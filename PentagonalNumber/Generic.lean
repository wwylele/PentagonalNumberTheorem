import Mathlib


/-!

# Generic framework for Pentagonal number theorem

This file partially proves the Pentagonal number theorem for arbitrary topological ring,
without concerning about summability, multipliability, or the existence of certain limits.

Complete proof is delegated to Complex.lean and PowerSeries.lean.

Reference:
https://math.stackexchange.com/questions/55738/how-to-prove-eulers-pentagonal-theorem-some-hints-will-help
-/

open Filter

theorem tprod_one_sub_ordererd {ι α : Type*} [CommRing α] [TopologicalSpace α] [T2Space α]
    [LinearOrder ι] [LocallyFiniteOrderBot ι] [IsTopologicalAddGroup α]
    {f : ι → α} (hsum : Summable fun i ↦ f i * ∏ j ∈ Finset.Iio i, (1 - f j))
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
    rw [Finset.prod_one_sub_ordered, sub_sub_cancel]
  obtain ⟨a, ha⟩ := hsum
  obtain h' := ha.comp Filter.tendsto_finset_Iic_atTop_atTop
  obtain hx' := hx.comp Filter.tendsto_finset_Iic_atTop_atTop
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

variable {R : Type*} [CommRing R]

namespace Pentagonal

/--
We define an auxiliary sequence

$$Γ_N = \sum_{n=0}^{\infty} γ_{N, n} =
\sum_{n=0}^{\infty} \left( x^{(N+1)n} \prod_{i=0}^{n} 1 - x^{N + i + 1} \right)$$
-/
def γ (N n : ℕ) (x : R) : R :=
  x ^ ((N + 1) * n) * ∏ i ∈ Finset.range (n + 1), (1 - x ^ (N + i + 1))

/-- And a second auxiliary sequence

$$ ψ_{N, n} = x^{(N+1)n} (x^{2N + n + 3} - 1) \prod_{i=0}^{n-1} 1 - x^{N + i + 2} $$ -/
def ψ (N n : ℕ) (x : R) : R :=
  x ^ ((N + 1) * n) * (x ^ (2 * N + n + 3) - 1) * ∏ i ∈ Finset.range n, (1 - x ^ (N + i + 2))


/-- $γ$ and $ψ$ have relation

$$ γ_{N,n} + x^{3N + 5}γ_{N + 1, n} = ψ_{N, n+1} - ψ_{N, n} $$ -/
theorem ψ_sub_ψ (N n : ℕ) (x : R) :
    γ N n x + x ^ (3 * N + 5) * γ (N + 1) n x = ψ N (n + 1) x - ψ N n x := by
  unfold ψ
  rw [Finset.prod_range_succ]
  unfold γ
  rw [Finset.prod_range_succ']
  rw [Finset.prod_range_succ]
  ring_nf

/-- By summing with telescoping, we get a recurrence formlua for $Γ$

$$ Γ_{N} = 1 - x^{2N + 3} - x^{3N + 5}Γ_{N + 1} $$
-/
theorem γ_rec [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    (N : ℕ) {x : R} (hx : IsTopologicallyNilpotent x) (hγ : ∀ N, Summable (γ N · x))
    (h : ∀ N, Multipliable (fun n ↦ 1 - x ^ (n + N + 1))) :
    ∑' n, γ N n x = 1 - x ^ (2 * N + 3) - x ^ (3 * N + 5) * ∑' n, γ (N + 1) n x := by
  rw [eq_sub_iff_add_eq]
  rw [show 1 - x ^ (2 * N + 3) = 0 - ψ N 0 x by simp [ψ]]
  rw [← (hγ _).tsum_mul_left]
  rw [← (hγ _).tsum_add ((hγ _).mul_left _)]
  apply HasSum.tsum_eq
  rw [((hγ _).add ((hγ _).mul_left _)).hasSum_iff_tendsto_nat]
  simp_rw [ψ_sub_ψ, Finset.sum_range_sub (ψ N · x)]
  apply Tendsto.sub_const
  unfold ψ
  rw [show nhds 0 = nhds (0 * (0 - 1) * ∏' i, (1 - x ^ (N + i + 2))) by simp]
  refine (Tendsto.mul ?_ ?_).mul ?_
  · exact hx.comp (strictMono_mul_left_of_pos (by simp)).tendsto_atTop
  · refine Tendsto.sub_const (hx.comp (StrictMono.tendsto_atTop ?_)) _
    exact add_right_strictMono.add_monotone monotone_const
  · apply Multipliable.tendsto_prod_tprod_nat
    convert h (N + 1) using 4
    ring

/-- The Euler function is related to $Γ$ by

$$ \prod_{n = 0}^{\infty} 1 - x^{n + 1} = 1 - x - x^2 Γ_0 $$ -/
theorem pentagonalLhs_γ0 [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] {x : R}
    (hγ : ∀ N, Summable (γ N · x)) (h : ∀ N, Multipliable fun n ↦ 1 - x ^ (n + N + 1)) :
    ∏' n, (1 - x ^ (n + 1)) = 1 - x - x ^ 2 * ∑' n, γ 0 n x := by
  obtain hsum := hγ 0
  unfold γ at hsum
  simp_rw [zero_add, one_mul] at hsum
  have hsum' : Summable fun i ↦ x ^ (i + 1) * ∏ n ∈ Finset.range i, (1 - x ^ (n + 1)) := by
    apply Summable.comp_nat_add (k := 1)
    conv in fun k ↦ _ =>
      ext k
      rw [pow_add, pow_add, mul_assoc (x ^ k), mul_comm (x ^ k), mul_assoc (x ^ 1 * x ^ 1)]
    apply Summable.mul_left _ hsum

  rw [tprod_one_sub_ordererd (by simpa [Nat.Iio_eq_range] using hsum') (by simpa using h 0)]
  simp_rw [Nat.Iio_eq_range, sub_sub, sub_right_inj, Summable.tsum_eq_zero_add hsum']
  conv in fun k ↦ x ^ (k + 1 + 1) * _ =>
    ext k
    rw [pow_add, pow_add, mul_assoc (x ^ k), mul_comm (x ^ k),
      ← pow_add x 1 1, one_add_one_eq_two, mul_assoc (x ^ 2)]
  rw [Summable.tsum_mul_left _ hsum]
  simp [γ]

/-- Applying the recurrence formula repeatedly, we get

$$ \prod_{n = 0}^{\infty} 1 - x^{n + 1} =
\left(\sum_{k=0}^{N} (-1)^k \left(x^{k(3k+1)/2} + x^{(k+1)(3k+2)/2}\right) \right) +
(-1)^{N+1}x^{(N+1)(3N + 4)/2}Γ_N $$ -/
theorem pentagonalLhs_γ [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] (N : ℕ) {x : R}
    (hx : IsTopologicallyNilpotent x)
    (hγ : ∀ N, Summable (γ N · x)) (h : ∀ N, Multipliable (fun n ↦ 1 - x ^ (n + N + 1)))
    : ∏' n, (1 - x ^ (n + 1)) =
    ∑ k ∈ Finset.range (N + 1), (-1) ^ k *
      (x ^ (k * (3 * k + 1) / 2) - x ^ ((k + 1) * (3 * k + 2) / 2))
      + (-1) ^ (N + 1) * x ^ ((N + 1) * (3 * N + 4) / 2) * ∑' n, γ N n x := by
  induction N with
  | zero => simp [pentagonalLhs_γ0 hγ h, γ, ← sub_eq_add_neg]
  | succ n ih =>
    rw [ih, γ_rec _ hx hγ h , Finset.sum_range_succ _ (n + 1)]
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

end Pentagonal

/-- Taking $N \to \infty$, we get the pentagonal number theorem in the generic form

$$ \prod_{n = 0}^{\infty} 1 - x^{n + 1} =
\sum_{k=0}^{\infty} (-1)^k \left(x^{k(3k+1)/2} + x^{(k+1)(3k+2)/2}\right) $$ -/
theorem pentagonalNumberTheorem_generic [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    {x : R} (hx : IsTopologicallyNilpotent x)
    (hγ : ∀ N, Summable (Pentagonal.γ N · x))
    (hlhs : ∀ N, Multipliable (fun n ↦ 1 - x ^ (n + N + 1)))
    (hrhs : Summable fun (k : ℕ) ↦
      (-1) ^ k * (x ^ (k * (3 * k + 1) / 2) - x ^ ((k + 1) * (3 * k + 2) / 2)))
    (htail : Tendsto (fun k ↦ (-1) ^ (k + 1) * x ^ ((k + 1) * (3 * k + 4) / 2) *
      ∑' (n : ℕ), Pentagonal.γ k n x) atTop (nhds 0)) :
    ∏' n, (1 - x ^ (n + 1)) =
    ∑' k, (-1) ^ k * (x ^ (k * (3 * k + 1) / 2) - x ^ ((k + 1) * (3 * k + 2) / 2)) := by
  refine (HasSum.tsum_eq ?_).symm
  rw [hrhs.hasSum_iff_tendsto_nat, (map_add_atTop_eq_nat 1).symm]
  apply tendsto_map'
  change Tendsto
    (fun n ↦ ∑ i ∈ Finset.range (n + 1), (-1) ^ i *
      (x ^ (i * (3 * i + 1) / 2) - x ^ ((i + 1) * (3 * i + 2) / 2)))
    atTop (nhds (∏' (n : ℕ), (1 - x ^ (n + 1))))
  obtain h := fun n ↦ Pentagonal.pentagonalLhs_γ n hx hγ hlhs
  simp_rw [← sub_eq_iff_eq_add] at h
  simp_rw [← h]
  rw [← tendsto_sub_nhds_zero_iff]
  simp_rw [sub_sub_cancel_left]
  rw [show (nhds (0 : R)) = (nhds (-0)) by simp]
  apply Filter.Tendsto.neg
  apply htail
