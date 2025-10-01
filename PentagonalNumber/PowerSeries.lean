import PentagonalNumber.Generic

/-!

# Pentagonal number theorem for power series

This file proves the
[pentagonal number theorem](https://en.wikipedia.org/wiki/Pentagonal_number_theorem)
for power series.


-/

open PowerSeries Filter
open scoped PowerSeries.WithPiTopology

section HasProd


variable {ι α : Type*} [DecidableEq ι] [CommSemiring α] [TopologicalSpace α]

theorem hasProd_one_add_of_hasSum_prod {f : ι → α} {a : α} (h : HasSum (∏ i ∈ ·, f i) a) :
    HasProd (1 + f ·) a := by
  unfold HasProd
  unfold HasSum at h
  have : (fun s ↦ ∏ i ∈ s, (fun x ↦ 1 + f x) i) =
       (fun p ↦ ∑ s ∈ p, ∏ i ∈ s, f i ) ∘ Finset.powerset := by
    ext s
    exact Finset.prod_one_add s
  rw [this]
  apply h.comp
  rw [tendsto_atTop_atTop]
  intro t
  use t.sup id
  intro u hu v hv
  simp only [Finset.mem_powerset]
  refine le_trans ?_ hu
  exact Finset.le_sup_of_le hv fun _ a ↦ a

theorem multipliable_one_add_of_summable_prod {f : ι → α} (h : Summable (∏ i ∈ ·, f i)) :
    Multipliable (1 + f ·) := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, hasProd_one_add_of_hasSum_prod ha⟩

end HasProd

namespace PowerSeries

variable {R : Type*}

theorem le_order_prod [CommSemiring R] {ι : Type*} [DecidableEq ι]
    (f : ι → R⟦X⟧) (s : Finset ι) :
    ∑ i ∈ s, (f i).order ≤ (∏ i ∈ s, f i).order := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    refine le_trans ?_ (le_order_mul _ _)
    apply add_le_add_left ih

theorem inf_order_le_order_sum [Semiring R] {ι : Type*} [DecidableEq ι]
    (f : ι → R⟦X⟧) (s : Finset ι) :
    ⨅ i ∈ s, (f i).order ≤ (∑ i ∈ s, f i).order := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    rw [Finset.iInf_insert]
    exact le_trans (min_le_min_left _ ih) (PowerSeries.min_order_le_order_add _ _)

variable {R : Type*}
variable [TopologicalSpace R] [CommSemiring R]

theorem WithPiTopology.multipliable_one_add_of_order_tendsto_atTop_nhds_top
    {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι] {f : ι → R⟦X⟧}
    (h : Tendsto (fun i ↦ (f i).order) atTop (nhds ⊤)) :
    Multipliable (fun i ↦ 1 + f i) := by
  obtain hempty | hempty := isEmpty_or_nonempty ι
  · apply multipliable_empty
  apply multipliable_one_add_of_summable_prod
  rw [summable_iff_summable_coeff]
  intro n
  apply summable_of_finite_support
  simp_rw [ENat.tendsto_nhds_top_iff_natCast_lt, eventually_atTop] at h
  obtain ⟨i, hi⟩ := h n
  apply Set.Finite.subset (Finset.finite_toSet (Finset.Iio i).powerset)
  suffices ∀ (s : Finset ι), (coeff n) (∏ i ∈ s, f i) ≠ 0 → ↑s ⊆ Set.Iio i by simpa
  intro s hs
  contrapose! hs
  obtain ⟨x, hxs, hxi⟩ := Set.not_subset.mp hs
  rw [Set.mem_Iio, not_lt] at hxi
  refine coeff_of_lt_order _<| (hi x hxi).trans_le (le_trans ?_ (le_order_prod _ _))
  apply Finset.single_le_sum (by simp) hxs

end PowerSeries

variable (R : Type*) [CommRing R]


namespace Pentagonal

theorem summable_γ_powerSeries [TopologicalSpace R] (N : ℕ) :
    Summable (γ N · (X : R⟦X⟧)) := by
  rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
  refine fun n ↦ summable_of_finite_support <| Set.Finite.subset (Set.finite_Iic n) ?_
  simp_rw [Function.support_subset_iff, Set.mem_Iic]
  intro k h
  contrapose! h
  unfold γ
  have : ¬ (N + 1) * k ≤ n := by
    rw [not_le]
    exact h.trans_le <| Nat.le_mul_of_pos_left k (by simp)
  simp [PowerSeries.coeff_X_pow_mul', this]

theorem multipliable_pentagonalLhs_powerSeries' [Nontrivial R] [TopologicalSpace R] (N : ℕ) :
    Multipliable (fun n ↦ (1 : R⟦X⟧) - X ^ (n + N + 1)) := by
  simp_rw [sub_eq_add_neg]
  apply PowerSeries.WithPiTopology.multipliable_one_add_of_order_tendsto_atTop_nhds_top
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr (fun n ↦ eventually_atTop.mpr ⟨n, ?_⟩)
  intro m hm
  rw [PowerSeries.order_neg]
  refine lt_of_lt_of_le ?_ (PowerSeries.le_order_pow _ _)
  rw [PowerSeries.order_X, nsmul_one]
  norm_cast
  exact lt_of_le_of_lt hm (by rw[add_assoc]; simp)

end Pentagonal

open Pentagonal

theorem multipliable_pentagonalLhs_powerSeries [Nontrivial R] [TopologicalSpace R] :
    Multipliable (fun n ↦ (1 : R⟦X⟧) - X ^ (n + 1)) := by
  simpa using multipliable_pentagonalLhs_powerSeries' R 0

theorem summable_pentagonalRhs_powerSeries
    [Nontrivial R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    Summable (fun (k : ℕ) ↦
    ((-1) ^ k * (X ^ (k * (3 * k + 1) / 2) - X ^ ((k + 1) * (3 * k + 2) / 2)) : R⟦X⟧)) := by
  apply PowerSeries.WithPiTopology.summable_of_tendsto_order_atTop_nhds_top
  rw [ENat.tendsto_nhds_top_iff_natCast_lt]
  refine fun n ↦ eventually_atTop.mpr ⟨n + 1, fun k hk ↦ ?_⟩
  rw [sub_eq_add_neg]
  apply lt_of_lt_of_le (lt_add_of_nonneg_of_lt (by simp) ?_) (PowerSeries.le_order_mul _ _)
  apply lt_of_lt_of_le ?_ (PowerSeries.min_order_le_order_add _ _)
  simp_rw [order_neg, order_X_pow]
  rw [min_eq_left (by gcongr <;> simp)]
  rw [Nat.cast_lt, ← Nat.add_one_le_iff, Nat.le_div_iff_mul_le (by simp)]
  exact Nat.mul_le_mul hk (by linarith)

/-- **Pentagonal number theorem** for formal power series, summation over natural numbers.

$$ \prod_{n = 0}^{\infty} 1 - x^{n + 1} =
\sum_{k=0}^{\infty} (-1)^k \left(x^{k(3k+1)/2} + x^{(k+1)(3k+2)/2}\right) $$ -/
theorem pentagonalNumberTheorem_powerSeries
    [Nontrivial R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    ∏' n, (1 - X ^ (n + 1) : R⟦X⟧) =
    ∑' k, (-1) ^ k * (X ^ (k * (3 * k + 1) / 2) - X ^ ((k + 1) * (3 * k + 2) / 2)) := by
  refine pentagonalNumberTheorem_generic ?_ ?_ ?_ ?_ ?_
  · rw [IsTopologicallyNilpotent, PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
    refine fun d ↦ tendsto_atTop_of_eventually_const fun i (hi : i ≥ d + 1) ↦ ?_
    simp_rw [coeff_X_pow]
    aesop
  · apply summable_γ_powerSeries
  · apply multipliable_pentagonalLhs_powerSeries'
  · apply summable_pentagonalRhs_powerSeries
  · rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
    refine fun n ↦ tendsto_atTop_of_eventually_const fun k (hk : k ≥ n) ↦ ?_
    rw [map_zero]
    apply PowerSeries.coeff_of_lt_order
    refine lt_of_lt_of_le (lt_add_of_lt_of_nonneg ?_ (by simp)) (PowerSeries.le_order_mul _ _)
    refine lt_of_lt_of_le (lt_add_of_nonneg_of_lt (by simp) ?_) (PowerSeries.le_order_mul _ _)
    rw [order_X_pow, Nat.cast_lt, ← Nat.add_one_le_iff, Nat.le_div_iff_mul_le (by simp)]
    apply Nat.mul_le_mul <;> linarith

theorem summable_pentagonalRhs_intNeg_powerSeries
    [Nontrivial R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    Summable (fun (k : ℤ) ↦ (Int.negOnePow k : R⟦X⟧) * X ^ (k * (3 * k + 1) / 2).toNat) := by
  apply Summable.of_add_one_of_neg_add_one
  all_goals
  apply PowerSeries.WithPiTopology.summable_of_tendsto_order_atTop_nhds_top
  rw [ENat.tendsto_nhds_top_iff_natCast_lt]
  refine fun n ↦ eventually_atTop.mpr ⟨n, fun k hk ↦ ?_⟩
  refine lt_of_lt_of_le (lt_add_of_nonneg_of_lt (by simp) ?_) (PowerSeries.le_order_mul _ _)
  rw [order_X_pow, Nat.cast_lt, Int.lt_toNat, ← Int.add_one_le_iff]
  rw [Int.le_ediv_iff_mul_le (by simp)]
  nlinarith

/-- **Pentagonal number theorem** for formal power series, summation over integers, opposite order.

$$ \prod_{n = 0}^{\infty} 1 - x^{n + 1} = \sum_{k=-\infty}^{\infty} (-1)^k x^{k(3k + 1)/2} $$ -/
theorem pentagonalNumberTheorem_intNeg_powerSeries
    [Nontrivial R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    ∏' n, (1 - X ^ (n + 1)) =
    ∑' (k : ℤ), (Int.negOnePow k : R⟦X⟧) * X ^ (k * (3 * k + 1) / 2).toNat := by
  rw [← tsum_nat_add_neg_add_one (summable_pentagonalRhs_intNeg_powerSeries R),
    pentagonalNumberTheorem_powerSeries]
  refine tsum_congr fun k ↦ ?_
  rw [sub_eq_add_neg _ (X ^ _), mul_add, ← neg_mul_comm]
  congrm ($(by norm_cast) * X ^ $(by norm_cast) + ?_ * X ^ $(by norm_cast))
  trans (-1) ^ (k + 1)
  · ring
  · norm_cast

theorem summable_pentagonalRhs_intPos_powerSeries
    [Nontrivial R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    Summable (fun (k : ℤ) ↦ (Int.negOnePow k : R⟦X⟧) * X ^ (k * (3 * k - 1) / 2).toNat) := by
  rw [← neg_injective.summable_iff (by intro x hx; contrapose! hx; use -x; simp)]
  convert summable_pentagonalRhs_intNeg_powerSeries R
  rw [Function.comp_apply]
  exact congr($(by simp) * X ^ (Int.toNat ($(by ring_nf) / 2)))

/-- **Pentagonal number theorem** for formal power series, summation over integers, classic order.

$$ \prod_{n = 0}^{\infty} 1 - x^{n + 1} = \sum_{k=-\infty}^{\infty} (-1)^k x^{k(3k - 1)/2} $$ -/
theorem pentagonalNumberTheorem_intPos_powerSeries
    [Nontrivial R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    ∏' n, (1 - X ^ (n + 1)) =
    ∑' (k : ℤ), (Int.negOnePow k : R⟦X⟧) * X ^ (k * (3 * k - 1) / 2).toNat := by
  rw [pentagonalNumberTheorem_intNeg_powerSeries, ← neg_injective.tsum_eq (by simp)]
  exact tsum_congr fun k ↦ congr($(by simp) * X ^ (Int.toNat ($(by ring_nf) / 2)))

/-
namespace Nat.Partition

theorem le_of_mem_parts {n : ℕ} {p : Partition n} {m : ℕ} (h : m ∈ p.parts) :
    m ≤ n := by
  rw [← p.parts_sum]
  exact Multiset.le_sum_of_mem h

variable {R : Type*}

theorem multipliable_genFun [CommSemiring R] [TopologicalSpace R] (f : ℕ → ℕ → R) :
    Multipliable fun m ↦ (1 + ∑' n, f (m + 1) (n + 1) • X ^ ((m + 1) * (n + 1)) : R⟦X⟧) := by ...

noncomputable
def genFun [CommSemiring R] (f : ℕ → ℕ → R) :=
  PowerSeries.mk fun d ↦ ∑ p : d.Partition, ∏ m ∈ p.parts.toFinset, f m (p.parts.count m)


theorem coeff_genFun [CommSemiring R] [TopologicalSpace R] [T2Space R] (f : ℕ → ℕ → R) :
    genFun f =
    ∏' m, (1 + ∑' n, f (m + 1) (n + 1) • X ^ ((m + 1) * (n + 1)) : R⟦X⟧) := by
  apply (HasProd.tprod_eq ?_).symm
  rw [HasProd, PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro d
  apply tendsto_atTop_of_eventually_const
  show ∀ s ≥ Finset.range (d + 1), _
  intro s hs
  rw [PowerSeries.coeff_prod]
  rw [genFun, PowerSeries.coeff_mk]
  symm
  refine Finset.sum_of_injOn (fun p ↦ Finsupp.mk p.parts.toFinset
    (fun m ↦ p.parts.count m * m) (fun m ↦ ?_)) ?_ ?_ ?_ ?_
  · simpa using fun hm ↦ Nat.ne_zero_of_lt <| p.parts_pos hm
  · apply Function.Injective.injOn
    intro p q h
    rw [Finsupp.mk.injEq] at h
    obtain ⟨hfinset, hcount⟩ := h
    rw [Nat.Partition.ext_iff, Multiset.ext]
    intro m
    obtain rfl | h0 := Nat.eq_zero_or_pos m
    · trans 0
      · rw [Multiset.count_eq_zero]
        exact fun h ↦ (lt_self_iff_false _).mp <| p.parts_pos h
      · symm
        rw [Multiset.count_eq_zero]
        exact fun h ↦ (lt_self_iff_false _).mp <| q.parts_pos h
    · exact Nat.eq_of_mul_eq_mul_right h0 <| funext_iff.mp hcount m
  · suffices ∀ (p : d.Partition), ∑ m ∈ s, Multiset.count m p.parts * m = d ∧
        p.parts.toFinset ⊆ s by simpa
    intro p
    have hp : p.parts.toFinset ⊆ s := by
      refine le_trans ?_ hs
      intro m
      rw [Multiset.mem_toFinset, Finset.mem_range]
      exact fun h ↦ Nat.lt_add_one_of_le (le_of_mem_parts h)
    constructor
    · simp_rw [← p.parts_sum, Finset.sum_multiset_count, smul_eq_mul]
      symm
      apply Finset.sum_subset hp (by aesop)
    · exact hp
  · intro f hf hf'
    simp at hf'
    ...
  · intro p

    ...


end Nat.Partition
-/
