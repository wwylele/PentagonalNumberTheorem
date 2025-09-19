import Mathlib

/-!

# Pentagonal number theorem, second approach

This file proves the
[pentagonal number theorem](https://en.wikipedia.org/wiki/Pentagonal_number_theorem)
using another approach described in
https://math.stackexchange.com/questions/55738/how-to-prove-eulers-pentagonal-theorem-some-hints-will-help


-/

open PowerSeries
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
  rw [Filter.tendsto_atTop_atTop]
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

@[simp]
theorem order_neg [Ring R] (a : R⟦X⟧) : (-a).order = a.order := by
  simp_rw [PowerSeries.order_eq, map_neg, neg_eq_zero, neg_ne_zero]
  rw [← PowerSeries.order_eq]

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

theorem le_order_one_sub_prod_one_add [CommRing R] {ι : Type*} [DecidableEq ι]
    (f : ι → R⟦X⟧) (s : Finset ι) :
    ⨅ i ∈ s, (f i).order ≤ (1 - ∏ i ∈ s, (1 + f i)).order := by
  rw [Finset.prod_one_add]
  rw [Finset.sum_eq_add_sum_diff_singleton (show ∅ ∈ s.powerset by simp)]
  rw [Finset.prod_empty, ← sub_sub, sub_self, zero_sub, order_neg]
  refine le_trans ?_ (inf_order_le_order_sum _ _)
  apply le_iInf
  intro t
  apply le_iInf
  intro ht
  rw [Finset.mem_sdiff, Finset.mem_powerset, Finset.mem_singleton] at ht
  obtain ⟨hst, ht0⟩ := ht
  obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr ht0
  refine le_trans ?_ (le_order_prod _ _)
  trans ⨅ i ∈ t, (f i).order
  · exact iInf_le_iInf_of_subset hst
  · apply iInf_le_of_le a
    rw [iInf_pos ha]
    apply Finset.single_le_sum (by simp) ha

variable [TopologicalSpace R] [Semiring R]

theorem WithPiTopology.has_sum_iff {ι : Type*} (f : ι → R⟦X⟧) (a : R⟦X⟧) :
    HasSum f a ↔ ∀ n, HasSum (fun i ↦ coeff n (f i)) (coeff n a) := by
  unfold HasSum
  simp_rw [← map_sum]
  apply tendsto_iff_coeff_tendsto

theorem WithPiTopology.summable_iff {ι : Type*} (f : ι → R⟦X⟧) :
    Summable f ↔ ∀ n, Summable (fun i ↦ coeff n (f i)) := by
  unfold Summable
  simp_rw [has_sum_iff]
  constructor
  · rintro ⟨a, h⟩
    intro n
    exact ⟨coeff n a, h n⟩
  · intro h
    choose a h using h
    exact ⟨PowerSeries.mk a, by simpa using h⟩

theorem WithPiTopology.summable_of_order_tendsto_atTop_atTop
    {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι] {f : ι → R⟦X⟧}
    (h : Filter.Tendsto (fun i ↦ (f i).order) Filter.atTop (nhds ⊤)) :
    Summable f := by
  obtain hempty | hempty := isEmpty_or_nonempty ι
  · apply summable_empty
  simp_rw [ENat.tendsto_nhds_top_iff_natCast_lt, Filter.eventually_atTop] at h
  rw [WithPiTopology.summable_iff]
  intro n
  apply summable_of_finite_support
  obtain ⟨i, hi⟩ := h n
  apply Set.Finite.subset (Set.finite_Iic i)
  simp_rw [Function.support_subset_iff, Set.mem_Iic]
  intro k
  rw [← not_imp_not, not_le, ne_eq, not_not]
  intro hk
  apply PowerSeries.coeff_of_lt_order
  simpa using (hi k hk.le)

variable {R : Type*}
variable [TopologicalSpace R] [CommSemiring R]

theorem WithPiTopology.multipliable_one_add_of_order_tendsto_atTop_nhds_top
    {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι] {f : ι → R⟦X⟧}
    (h : Filter.Tendsto (fun i ↦ (f i).order) Filter.atTop (nhds ⊤)) :
    Multipliable (fun i ↦ 1 + f i) := by
  obtain hempty | hempty := isEmpty_or_nonempty ι
  · apply multipliable_empty
  apply multipliable_one_add_of_summable_prod
  rw [summable_iff]
  intro n
  apply summable_of_finite_support
  simp_rw [ENat.tendsto_nhds_top_iff_natCast_lt, Filter.eventually_atTop] at h
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

noncomputable
def φ (N n : ℕ) : PowerSeries R :=
  X ^ ((N + 1) * n) * ∏ i ∈ Finset.range (n + 1), (1 - X ^ (N + 1 + i))

theorem summable_φ [TopologicalSpace R] (N : ℕ) : Summable (φ R N) := by
  rw [WithPiTopology.summable_iff]
  intro n
  apply summable_of_finite_support
  apply Set.Finite.subset (Set.finite_Iic n)
  simp_rw [Function.support_subset_iff, Set.mem_Iic]
  intro k h
  contrapose! h
  unfold φ
  have : ¬ (N + 1) * k ≤ n := by
    rw [not_le]
    exact h.trans_le <| Nat.le_mul_of_pos_left k (by simp)
  simp [PowerSeries.coeff_X_pow_mul', this]

noncomputable
def ψ (N n : ℕ) : PowerSeries R :=
  X ^ ((N + 1) * n) * (X ^ (2 * N + n + 3) - 1) * ∏ i ∈ Finset.range n, (1 - X ^ (N + i + 2))

theorem coeff_ψ [Nontrivial R] {N n k : ℕ} (h : k < (N + 1) * n) : coeff k (ψ R N n) = 0 := by
  unfold ψ
  rw [mul_assoc]
  apply PowerSeries.coeff_of_lt_order
  apply lt_of_lt_of_le (lt_add_of_lt_of_nonneg ?_ (by simp)) (PowerSeries.le_order_mul _ _)
  rw [order_X_pow]
  norm_cast

theorem ψ_sub_ψ (N n : ℕ) :
    φ R N n + X ^ (3 * N + 5) * φ R (N + 1) n = ψ R N (n + 1) - ψ R N n := by
  unfold ψ
  rw [Finset.prod_range_succ]
  unfold φ
  rw [Finset.prod_range_succ']
  rw [Finset.prod_range_succ]
  ring_nf

theorem φ_rec [Nontrivial R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] (N : ℕ) :
    ∑' n, φ R N n = 1 - X ^ (2 * N + 3) - X ^ (3 * N + 5) * ∑' n, φ R (N + 1) n := by
  rw [eq_sub_iff_add_eq]
  rw [show 1 - X ^ (2 * N + 3) = 0 - ψ R N 0 by simp [ψ]]
  rw [← (summable_φ R _).tsum_mul_left]
  rw [← (summable_φ R _).tsum_add ((summable_φ R _).mul_left _)]
  apply HasSum.tsum_eq
  rw [((summable_φ R _).add ((summable_φ R _).mul_left _)).hasSum_iff_tendsto_nat]
  simp_rw [ψ_sub_ψ, Finset.sum_range_sub]
  apply Filter.Tendsto.sub_const
  rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro n
  apply tendsto_atTop_of_eventually_const (i₀ := n + 1)
  intro k hk
  rw [ge_iff_le, Nat.add_one_le_iff] at hk
  rw [map_zero]
  refine coeff_ψ R (hk.trans_le ?_)
  simp [add_one_mul]

theorem multipliable_pentagonalLhs [Nontrivial R] [TopologicalSpace R] :
    Multipliable (fun n ↦ (1 : R⟦X⟧) - X ^ (n + 1)) := by
  simp_rw [sub_eq_add_neg]
  apply PowerSeries.WithPiTopology.multipliable_one_add_of_order_tendsto_atTop_nhds_top
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr (fun n ↦ Filter.eventually_atTop.mpr ⟨n, ?_⟩)
  intro m hm
  rw [PowerSeries.order_neg]
  refine lt_of_lt_of_le ?_ (PowerSeries.le_order_pow _ _)
  rw [PowerSeries.order_X, nsmul_one]
  norm_cast
  exact lt_of_le_of_lt hm (by simp)

theorem pentagonalLhs_φ0 [Nontrivial R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    ∏' n, (1 - X ^ (n + 1)) = 1 - X - X ^ 2 * ∑' n, φ R 0 n := by
  rw [sub_sub, add_comm]
  apply HasProd.tprod_eq
  rw [(multipliable_pentagonalLhs R).hasProd_iff_tendsto_nat]
  conv in fun n ↦ _ =>
    ext n
    rw [Finset.prod_one_sub_ordered]
  apply Filter.Tendsto.const_sub
  rw [(Filter.map_add_atTop_eq_nat 1).symm]
  apply Filter.tendsto_map'
  change Filter.Tendsto ((fun k ↦ ∑ i ∈ Finset.range (k + 1), X ^ (i + 1) *
      ∏ j ∈ Finset.range (k + 1) with j < i, (1 - X ^ (j + 1))))
      Filter.atTop (nhds (X ^ 2 * ∑' (n : ℕ), φ R 0 n + X))
  simp_rw [Finset.sum_range_succ']
  refine Filter.Tendsto.add ?_ (by simp)
  have (k : ℕ) : (X ^ (k + 1 + 1) : R⟦X⟧) = X ^ 2 * X ^ k := by ring
  conv in fun k ↦ X ^ (k + 1 + 1) * _ =>
    ext k
    rw [this k]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  apply Filter.Tendsto.const_mul

  suffices Filter.Tendsto (fun k ↦ ∑ i ∈ Finset.range k,
      (X ^ i * ∏ j ∈ Finset.range (k + 1) with j < i + 1,
      (1 - X ^ (j + 1)) - (φ R 0 i))) Filter.atTop (nhds 0) by
    simpa using this.add (summable_φ R 0).tendsto_sum_tsum_nat
  unfold φ
  simp_rw [zero_add, one_mul, ← mul_sub]

  have hfilterswap (j k : ℕ) : (Finset.range (j + 1)).filter (· < k + 1) =
      (Finset.range (k + 1)).filter (· < j + 1) := by
    ext x
    grind
  have (j k : ℕ) : ∏ n ∈ Finset.range (k + 1), ((1 : R⟦X⟧) - X ^ (1 + n)) =
      (∏ n ∈ Finset.range (k + 1) with ¬ n < j + 1, ((1 : R⟦X⟧) - X ^ (n + 1))) *
      (∏ n ∈ Finset.range (j + 1) with n < k + 1, ((1 : R⟦X⟧) - X ^ (n + 1))) := by
    rw [hfilterswap]
    rw [Finset.prod_filter_not_mul_prod_filter]
    ring_nf

  conv in fun j ↦ _ =>
    ext j
    right
    conv in fun k ↦ _ =>
      ext k
      rw [this j k]
      rw [← one_sub_mul]
  rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro d
  apply tendsto_atTop_of_eventually_const (i₀ := d)
  intro i hi
  rw [map_zero, map_sum]
  apply Finset.sum_eq_zero
  intro j hj
  apply PowerSeries.coeff_of_lt_order
  refine lt_of_lt_of_le ?_ (PowerSeries.le_order_mul _ _)
  apply lt_add_of_nonneg_of_lt (by simp)
  refine lt_of_lt_of_le ?_ (PowerSeries.le_order_mul _ _)
  refine lt_add_of_lt_of_nonneg ?_ (by simp)
  apply lt_of_le_of_lt (Nat.cast_le.mpr hi.le)
  rw [← ENat.add_one_le_iff (by simp)]
  norm_cast
  simp_rw [sub_eq_add_neg _ (X ^ _)]
  refine le_trans ?_ (le_order_one_sub_prod_one_add _ _)
  apply le_iInf
  intro k
  apply le_iInf
  intro hk
  simp_rw [Finset.mem_filter, Finset.mem_range, not_lt] at hk
  suffices (i + 1 : ℕ∞) ≤ k + 1 by simpa
  norm_cast
  rw [add_le_add_iff_right]
  apply le_trans (by simp) hk.2

theorem pentagonalLhs_φ [Nontrivial R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    (N : ℕ) : ∏' n, (1 - X ^ (n + 1)) =
    ∑ k ∈ Finset.range (N + 1), (-1) ^ k *
      (X ^ (k * (3 * k + 1) / 2) - X ^ ((k + 1) * (3 * k + 2) / 2))
      + (-1) ^ (N + 1) * X ^ ((N + 1) * (3 * N + 4) / 2) * ∑' n, φ R N n := by
  induction N with
  | zero =>
    simp [pentagonalLhs_φ0, φ]
    ring_nf
  | succ n ih =>
    rw [ih]
    rw [φ_rec]
    rw [Finset.sum_range_succ _ (n + 1)]
    have h (n) : (n + 1 + 1) * (3 * (n + 1) + 2) / 2 =
        (n + 1) * (3 * n + 4) / 2 + (2 * n + 3) := by
      rw [← Nat.add_mul_div_left _ _ (by simp)]
      ring_nf
    simp_rw [h]
    have h (n) : (n + 1 + 1) * (3 * (n + 1) + 4) / 2 =
        (n + 1) * (3 * n + 4) / 2 + (3 * n + 5) := by
      rw [← Nat.add_mul_div_left _ _ (by simp)]
      ring_nf
    simp_rw [h]
    ring_nf

theorem summable_pentagonalRhs
    [Nontrivial R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    Summable (fun (k : ℕ) ↦
    ((-1) ^ k * (X ^ (k * (3 * k + 1) / 2) - X ^ ((k + 1) * (3 * k + 2) / 2)) : R⟦X⟧)) := by
  apply PowerSeries.WithPiTopology.summable_of_order_tendsto_atTop_atTop
  rw [ENat.tendsto_nhds_top_iff_natCast_lt]
  intro n
  rw [Filter.eventually_atTop]
  use n + 1
  intro k hk
  rw [sub_eq_add_neg]
  apply lt_of_lt_of_le (lt_add_of_nonneg_of_lt (by simp) ?_) (PowerSeries.le_order_mul _ _)
  apply lt_of_lt_of_le ?_ (PowerSeries.min_order_le_order_add _ _)
  simp_rw [order_neg, order_X_pow]
  rw [min_eq_left (by gcongr <;> simp)]
  rw [Nat.cast_lt, ← Nat.add_one_le_iff, Nat.le_div_iff_mul_le (by simp)]
  apply Nat.mul_le_mul hk
  linarith

theorem pentagonalNumberTheorem'
    [Nontrivial R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    ∏' n, (1 - X ^ (n + 1) : R⟦X⟧) =
    ∑' k, (-1) ^ k * (X ^ (k * (3 * k + 1) / 2) - X ^ ((k + 1) * (3 * k + 2) / 2)) := by
  symm
  apply HasSum.tsum_eq
  rw [(summable_pentagonalRhs R).hasSum_iff_tendsto_nat]
  rw [(Filter.map_add_atTop_eq_nat 1).symm]
  apply Filter.tendsto_map'
  change Filter.Tendsto
    (fun n ↦ ∑ i ∈ Finset.range (n + 1), (-1) ^ i *
        (X ^ (i * (3 * i + 1) / 2) - X ^ ((i + 1) * (3 * i + 2) / 2)))
    Filter.atTop (nhds (∏' (n : ℕ), (1 - X ^ (n + 1))))
  obtain h := pentagonalLhs_φ R
  simp_rw [← sub_eq_iff_eq_add] at h
  simp_rw [← h]
  rw [← tendsto_sub_nhds_zero_iff]
  simp_rw [sub_sub_cancel_left]
  rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro n
  apply tendsto_atTop_of_eventually_const (i₀ := n)
  intro k hk
  rw [map_zero]
  apply PowerSeries.coeff_of_lt_order
  rw [PowerSeries.order_neg]
  refine lt_of_lt_of_le (lt_add_of_lt_of_nonneg ?_ (by simp)) (PowerSeries.le_order_mul _ _)
  refine lt_of_lt_of_le (lt_add_of_nonneg_of_lt (by simp) ?_) (PowerSeries.le_order_mul _ _)
  rw [order_X_pow, Nat.cast_lt, ← Nat.add_one_le_iff, Nat.le_div_iff_mul_le (by simp)]
  apply Nat.mul_le_mul <;> linarith
