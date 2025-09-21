import Mathlib

/-!

# Pentagonal number theorem, second approach

This file proves the
[pentagonal number theorem](https://en.wikipedia.org/wiki/Pentagonal_number_theorem)
using another approach described in
https://math.stackexchange.com/questions/55738/how-to-prove-eulers-pentagonal-theorem-some-hints-will-help


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

noncomputable
def LocallyFiniteOrderBot.toOrderBot (α : Type*)
    [SemilatticeInf α] [LocallyFiniteOrderBot α] [h : Nonempty α] :
    OrderBot α where
  bot := (Finset.Iic h.some).inf' Finset.nonempty_Iic id
  bot_le a := by
    trans h.some ⊓ a
    · exact Finset.inf'_le _ (by simp)
    · exact inf_le_right

theorem tprod_one_sub_ordererd {ι α : Type*} [CommRing α] [TopologicalSpace α] [T2Space α]
    [LinearOrder ι] [LocallyFiniteOrderBot ι] [ContinuousSub α] [T2Space α]
    {f : ι → α} (hsum : Summable (fun i ↦ f i * ∏ j ∈ Finset.Iio i, (1 - f j)))
    (hmul : Multipliable (1 - f ·)) :
    ∏' i, (1 - f i) = 1 - ∑' i, f i * ∏ j ∈ Finset.Iio i, (1 - f j) := by
  obtain hempty | hempty := isEmpty_or_nonempty ι
  · simp
  obtain ⟨x, hx⟩ := hmul
  convert hx.tprod_eq
  unfold HasProd at hx
  obtain hx := hx.const_sub 1
  conv at hx in fun s ↦ _ =>
    ext s
    rw [Finset.prod_one_sub_ordered]
    rw [sub_sub_cancel]

  obtain ⟨a, ha⟩ := hsum
  have : Tendsto (fun i : ι ↦ Finset.Iic i) atTop atTop := by
    let : OrderBot ι := LocallyFiniteOrderBot.toOrderBot ι
    rw [Filter.tendsto_atTop_atTop]
    intro s
    use s.sup id
    intro i h
    intro b hb
    rw [Finset.sup_le_iff] at h
    simpa using h b hb
  obtain h' := ha.comp this
  obtain hx' := hx.comp this
  rw [ha.tsum_eq, sub_eq_iff_eq_add, ← sub_eq_iff_eq_add']
  apply tendsto_nhds_unique hx'
  convert h' using 1
  ext s
  apply Finset.sum_congr rfl
  intro i hi
  apply congr(_ * ∏ _ ∈ $_, _)
  ext j
  suffices j < i → j ≤ s by simpa
  intro hj
  exact (hj.trans_le (by simpa using hi)).le

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

/--
We define an auxiliary sequence

$$Γ_N = \sum_{n=0}^{\infty} γ_{N, n} =
\sum_{n=0}^{\infty} \left( x^{(N+1)n} \prod_{i=0}^{n} 1 - x^{N + i + 1} \right)$$
-/
noncomputable
def γ (N n : ℕ) : PowerSeries R :=
  X ^ ((N + 1) * n) * ∏ i ∈ Finset.range (n + 1), (1 - X ^ (N + i + 1))

theorem summable_γ [TopologicalSpace R] (N : ℕ) : Summable (γ R N) := by
  rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
  intro n
  apply summable_of_finite_support
  apply Set.Finite.subset (Set.finite_Iic n)
  simp_rw [Function.support_subset_iff, Set.mem_Iic]
  intro k h
  contrapose! h
  unfold γ
  have : ¬ (N + 1) * k ≤ n := by
    rw [not_le]
    exact h.trans_le <| Nat.le_mul_of_pos_left k (by simp)
  simp [PowerSeries.coeff_X_pow_mul', this]

/-- And a second auxiliary sequence

$$ ψ_{N, n} = x^{(N+1)n} (x^{2N + n + 3} - 1) \prod_{i=0}^{n-1} 1 - x^{N + i + 2} $$ -/
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

/-- $γ$ and $ψ$ have relation

$$ γ_{N,n} + x^{3N + 5}γ_{N + 1, n} = ψ_{N, n+1} - ψ_{N, n} $$ -/
theorem ψ_sub_ψ (N n : ℕ) :
    γ R N n + X ^ (3 * N + 5) * γ R (N + 1) n = ψ R N (n + 1) - ψ R N n := by
  unfold ψ
  rw [Finset.prod_range_succ]
  unfold γ
  rw [Finset.prod_range_succ']
  rw [Finset.prod_range_succ]
  ring_nf

/-- By summing with telescoping, we get a recurrence formlua for $Γ$

$$ Γ_{N} = 1 - x^{2N + 3} - x^{3N + 5}Γ_{N + 1} $$
-/
theorem γ_rec [Nontrivial R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] (N : ℕ) :
    ∑' n, γ R N n = 1 - X ^ (2 * N + 3) - X ^ (3 * N + 5) * ∑' n, γ R (N + 1) n := by
  rw [eq_sub_iff_add_eq]
  rw [show 1 - X ^ (2 * N + 3) = 0 - ψ R N 0 by simp [ψ]]
  rw [← (summable_γ R _).tsum_mul_left]
  rw [← (summable_γ R _).tsum_add ((summable_γ R _).mul_left _)]
  apply HasSum.tsum_eq
  rw [((summable_γ R _).add ((summable_γ R _).mul_left _)).hasSum_iff_tendsto_nat]
  simp_rw [ψ_sub_ψ, Finset.sum_range_sub]
  apply Tendsto.sub_const
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
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr (fun n ↦ eventually_atTop.mpr ⟨n, ?_⟩)
  intro m hm
  rw [PowerSeries.order_neg]
  refine lt_of_lt_of_le ?_ (PowerSeries.le_order_pow _ _)
  rw [PowerSeries.order_X, nsmul_one]
  norm_cast
  exact lt_of_le_of_lt hm (by simp)


/-- The Euler function is related to $Γ$ by

$$ \prod_{n = 0}^{\infty} 1 - x^{n + 1} = 1 - x - x^2 Γ_0 $$ -/
theorem pentagonalLhs_γ0 [Nontrivial R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    ∏' n, (1 - X ^ (n + 1)) = 1 - X - X ^ 2 * ∑' n, γ R 0 n := by
  obtain hsum := summable_γ R 0
  unfold γ at hsum
  simp_rw [zero_add, one_mul] at hsum
  have hsum' : Summable fun i ↦ X ^ (i + 1) * ∏ x ∈ Finset.range i, (1 - X ^ (x + 1) : R⟦X⟧) := by
    apply Summable.comp_nat_add (k := 1)
    conv in fun k ↦ _ =>
      ext k
      rw [pow_add, pow_add, mul_assoc (X ^ k), mul_comm (X ^ k), mul_assoc (X ^1 * X ^ 1)]
    apply Summable.mul_left _ hsum

  rw [tprod_one_sub_ordererd (by simpa [Nat.Iio_eq_range] using hsum')
    (multipliable_pentagonalLhs R)]
  simp_rw [Nat.Iio_eq_range, sub_sub, sub_right_inj, Summable.tsum_eq_zero_add hsum']
  conv in fun k ↦ X ^ (k + 1 + 1) * _ =>
    ext k
    rw [pow_add, pow_add, mul_assoc (X ^ k), mul_comm (X ^ k),
      ← pow_add X 1 1, one_add_one_eq_two, mul_assoc (X ^ 2)]
  rw [Summable.tsum_mul_left _ hsum]
  simp [γ]

/-- Applying the recurrence formula repeatedly, we get

$$ \prod_{n = 0}^{\infty} 1 - x^{n + 1} =
\left(\sum_{k=0}^{N} (-1)^k \left(x^{k(3k+1)/2} + x^{(k+1)(3k+2)/2}\right) \right) +
(-1)^{N+1}x^{(N+1)(3N + 4)/2}Γ_N $$ -/
theorem pentagonalLhs_γ [Nontrivial R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    (N : ℕ) : ∏' n, (1 - X ^ (n + 1)) =
    ∑ k ∈ Finset.range (N + 1), (-1) ^ k *
      (X ^ (k * (3 * k + 1) / 2) - X ^ ((k + 1) * (3 * k + 2) / 2))
      + (-1) ^ (N + 1) * X ^ ((N + 1) * (3 * N + 4) / 2) * ∑' n, γ R N n := by
  induction N with
  | zero =>
    simp [pentagonalLhs_γ0, γ]
    ring_nf
  | succ n ih =>
    rw [ih, γ_rec, Finset.sum_range_succ _ (n + 1)]
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
  apply PowerSeries.WithPiTopology.summable_of_tendsto_order_atTop_nhds_top
  rw [ENat.tendsto_nhds_top_iff_natCast_lt]
  intro n
  rw [eventually_atTop]
  refine ⟨n + 1, fun k hk ↦ ?_⟩
  rw [sub_eq_add_neg]
  apply lt_of_lt_of_le (lt_add_of_nonneg_of_lt (by simp) ?_) (PowerSeries.le_order_mul _ _)
  apply lt_of_lt_of_le ?_ (PowerSeries.min_order_le_order_add _ _)
  simp_rw [order_neg, order_X_pow]
  rw [min_eq_left (by gcongr <;> simp)]
  rw [Nat.cast_lt, ← Nat.add_one_le_iff, Nat.le_div_iff_mul_le (by simp)]
  exact Nat.mul_le_mul hk (by linarith)

/-- Taking $N \to \infty$, we get the pentagonal number theorem in the natural number form

$$ \prod_{n = 0}^{\infty} 1 - x^{n + 1} =
\sum_{k=0}^{\infty} (-1)^k \left(x^{k(3k+1)/2} + x^{(k+1)(3k+2)/2}\right) $$ -/

theorem pentagonalNumberTheorem'
    [Nontrivial R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    ∏' n, (1 - X ^ (n + 1) : R⟦X⟧) =
    ∑' k, (-1) ^ k * (X ^ (k * (3 * k + 1) / 2) - X ^ ((k + 1) * (3 * k + 2) / 2)) := by
  refine (HasSum.tsum_eq ?_).symm
  rw [(summable_pentagonalRhs R).hasSum_iff_tendsto_nat, (map_add_atTop_eq_nat 1).symm]
  apply tendsto_map'
  change Tendsto
    (fun n ↦ ∑ i ∈ Finset.range (n + 1), (-1) ^ i *
      (X ^ (i * (3 * i + 1) / 2) - X ^ ((i + 1) * (3 * i + 2) / 2)))
    atTop (nhds (∏' (n : ℕ), (1 - X ^ (n + 1))))
  obtain h := pentagonalLhs_γ R
  simp_rw [← sub_eq_iff_eq_add] at h
  simp_rw [← h]
  rw [← tendsto_sub_nhds_zero_iff]
  simp_rw [sub_sub_cancel_left]
  rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  refine fun n ↦ tendsto_atTop_of_eventually_const (i₀ := n) fun k hk ↦ ?_
  rw [map_zero]
  apply PowerSeries.coeff_of_lt_order
  rw [PowerSeries.order_neg]
  refine lt_of_lt_of_le (lt_add_of_lt_of_nonneg ?_ (by simp)) (PowerSeries.le_order_mul _ _)
  refine lt_of_lt_of_le (lt_add_of_nonneg_of_lt (by simp) ?_) (PowerSeries.le_order_mul _ _)
  rw [order_X_pow, Nat.cast_lt, ← Nat.add_one_le_iff, Nat.le_div_iff_mul_le (by simp)]
  apply Nat.mul_le_mul <;> linarith

theorem summable_pentagonalRhs_intNeg
    [Nontrivial R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    Summable (fun (k : ℤ) ↦ (Int.negOnePow k : R⟦X⟧) * X ^ (k * (3 * k + 1) / 2).toNat) := by
  apply Summable.of_add_one_of_neg_add_one
  <;> apply PowerSeries.WithPiTopology.summable_of_tendsto_order_atTop_nhds_top
  <;> rw [ENat.tendsto_nhds_top_iff_natCast_lt]
  <;> intro n
  <;> rw [eventually_atTop]
  <;> use n
  <;> intro k hk
  <;> refine lt_of_lt_of_le (lt_add_of_nonneg_of_lt (by simp) ?_) (PowerSeries.le_order_mul _ _)
  <;> rw [order_X_pow, Nat.cast_lt, Int.lt_toNat, ← Int.add_one_le_iff]
  <;> rw [Int.le_ediv_iff_mul_le (by simp)]
  · gcongr
    linarith
  · rw [neg_mul_comm]
    gcongr
    linarith

/-- Splitting the two terms in the sum, we get the integer form, though the
summing direction is the opposite to the classic formula

$$ \prod_{n = 0}^{\infty} 1 - x^{n + 1} = \sum_{k=-\infty}^{\infty} (-1)^k x^{k(3k + 1)/2} $$ -/
theorem pentagonalNumberTheorem_intNeg
    [Nontrivial R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    ∏' n, (1 - X ^ (n + 1)) =
    ∑' (k : ℤ), (Int.negOnePow k : R⟦X⟧) * X ^ (k * (3 * k + 1) / 2).toNat := by
  rw [← tsum_nat_add_neg_add_one (summable_pentagonalRhs_intNeg R), pentagonalNumberTheorem']
  apply tsum_congr
  intro k
  rw [sub_eq_add_neg _ (X ^ _), mul_add, ← neg_mul_comm]
  apply congr($_ * X ^ $_ + $_ * X ^ $_)
  · norm_cast
  · norm_cast
  · trans (-1) ^ (k + 1)
    · ring
    · norm_cast
  · norm_cast

theorem summable_pentagonalRhs_intPos
    [Nontrivial R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    Summable (fun (k : ℤ) ↦ (Int.negOnePow k : R⟦X⟧) * X ^ (k * (3 * k - 1) / 2).toNat) := by
  rw [← neg_injective.summable_iff (by intro x hx; contrapose! hx; use -x; simp)]
  convert summable_pentagonalRhs_intNeg R
  rw [Function.comp_apply]
  apply congr($_ * X ^ (Int.toNat ($_ / 2)))
  · simp
  · ring_nf

/-- Taking the opposite direction, we get the classic formula

$$ \prod_{n = 0}^{\infty} 1 - x^{n + 1} = \sum_{k=-\infty}^{\infty} (-1)^k x^{k(3k - 1)/2} $$ -/
theorem pentagonalNumberTheorem_intPos
    [Nontrivial R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    ∏' n, (1 - X ^ (n + 1)) =
    ∑' (k : ℤ), (Int.negOnePow k : R⟦X⟧) * X ^ (k * (3 * k - 1) / 2).toNat := by
  rw [pentagonalNumberTheorem_intNeg, ← neg_injective.tsum_eq (by simp)]
  apply tsum_congr
  intro k
  apply congr($_ * X ^ (Int.toNat ($_ / 2)))
  · simp
  · ring_nf
