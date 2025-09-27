import PentagonalNumber.Approach2

/-!

# Pentagonal number theorem for complex series

This file proves the
[pentagonal number theorem](https://en.wikipedia.org/wiki/Pentagonal_number_theorem)
as complex series.

-/

open Filter

def γ' (N n : ℕ) (x : ℂ) : ℂ :=
  x ^ ((N + 1) * n) * ∏ i ∈ Finset.range (n + 1), (1 - x ^ (N + i + 1))

theorem γ'_bound (N n : ℕ) {x : ℂ} (hx : ‖x‖ < 1) :
    ‖γ' N n x‖ ≤ ‖x‖ ^ ((N + 1) * n) * ∏' i, (1 + ‖x‖ ^ i) := by
  unfold γ'
  rw [norm_mul, norm_prod, norm_pow]
  refine mul_le_mul_of_nonneg_left ?_ (by simp)
  trans ∏ i ∈ Finset.Ico (N + 1) (n + 1 + (N + 1)), (1 + ‖x‖ ^ i)
  · rw [Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel]
    apply Finset.prod_le_prod (by simp)
    intro _ _
    apply (norm_sub_le _ _).trans_eq
    rw [norm_one, norm_pow]
    ring
  have : Multipliable (1 + ‖x‖ ^ ·) := by
    apply multipliable_one_add_of_summable
    simpa using hx
  apply ge_of_tendsto (this.tendsto_prod_tprod_nat)
  rw [eventually_atTop]
  use n + 1 + (N + 1)
  intro a ha
  have : Finset.Ico (N + 1) (n + 1 + (N + 1)) ⊆ Finset.range a := by
    rw [Finset.range_eq_Ico]
    exact Finset.Ico_subset_Ico (by simp) ha
  rw [← Finset.prod_sdiff this]
  apply le_mul_of_one_le_left (Finset.prod_nonneg (by
    intro _ _
    trans 1 <;> simp))
  generalize Finset.range a \ Finset.Ico (N + 1) (n + 1 + (N + 1)) = s
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s h ih =>
    rw [Finset.prod_cons]
    exact one_le_mul_of_one_le_of_one_le (by simp) ih

theorem summable_γ' (N : ℕ) {x : ℂ} (hx : ‖x‖ < 1) : Summable (γ' N · x) := by
  rw [← summable_norm_iff]
  apply Summable.of_nonneg_of_le (by simp) (γ'_bound N · hx)
  apply Summable.mul_right
  simp_rw [pow_mul]
  apply summable_geometric_of_lt_one (by simp)
  exact (pow_lt_one_iff_of_nonneg (by simp) (by simp)).mpr hx

theorem tsum_γ'_bound (N : ℕ) {x : ℂ} (hx : ‖x‖ < 1) :
    ‖∑' n, γ' N n x‖ ≤ (1 - ‖x‖)⁻¹ * ∏' i, (1 + ‖x‖ ^ i) := by
  obtain hsum := (summable_γ' N hx).norm
  have hx' : ‖x‖ ^ (N + 1) < 1 := (pow_lt_one_iff_of_nonneg (by simp) (by simp)).mpr hx
  apply (norm_tsum_le_tsum_norm hsum).trans
  refine (Summable.tsum_le_tsum (γ'_bound N · hx) hsum ?_).trans ?_
  · simp_rw [pow_mul]
    apply Summable.mul_right
    exact summable_geometric_of_lt_one (by simp) hx'
  rw [tsum_mul_right]
  refine mul_le_mul_of_nonneg_right ?_ ?_
  · simp_rw [pow_mul]
    rw [tsum_geometric_of_lt_one (by simp) hx']
    rw [inv_le_inv₀ (by simpa using hx') (by simpa using hx)]
    rw [sub_le_sub_iff_left]
    apply pow_le_of_le_one (by simp) hx.le (by simp)
  -- hx : ‖x‖ < 1
  -- ⊢ 0 ≤ ∏' (i : ℕ), (1 + ‖x‖ ^ i)
  rw [← Real.rexp_tsum_eq_tprod (fun i ↦ (show (0 : ℝ) < 1 by simp).trans_le (by simp)) (by
    apply Real.summable_log_one_add_of_summable
    simpa using hx)]
  apply Real.exp_nonneg

def ψ' (N n : ℕ) (x : ℂ) : ℂ :=
  x ^ ((N + 1) * n) * (x ^ (2 * N + n + 3) - 1) * ∏ i ∈ Finset.range n, (1 - x ^ (N + i + 2))

theorem ψ_sub_ψ' (N n : ℕ) (x : ℂ) :
    γ' N n x + x ^ (3 * N + 5) * γ' (N + 1) n x = ψ' N (n + 1) x - ψ' N n x := by
  unfold ψ'
  rw [Finset.prod_range_succ]
  unfold γ'
  rw [Finset.prod_range_succ']
  rw [Finset.prod_range_succ]
  ring_nf

theorem γ_rec' (N : ℕ) {x : ℂ} (hx : ‖x‖ < 1) :
    ∑' n, γ' N n x = 1 - x ^ (2 * N + 3) - x ^ (3 * N + 5) * ∑' n, γ' (N + 1) n x := by
  rw [eq_sub_iff_add_eq]
  rw [show 1 - x ^ (2 * N + 3) = 0 - ψ' N 0 x by simp [ψ']]
  rw [← (summable_γ' _ hx).tsum_mul_left]
  rw [← (summable_γ' _ hx).tsum_add ((summable_γ' _ hx).mul_left _)]
  apply HasSum.tsum_eq
  rw [((summable_γ' _ hx).add ((summable_γ' _ hx).mul_left _)).hasSum_iff_tendsto_nat]
  simp_rw [ψ_sub_ψ', Finset.sum_range_sub (ψ' N · x)]
  apply Tendsto.sub_const
  unfold ψ'
  rw [show nhds 0 = nhds (0 * ∏' i, (1 - x ^ (N + i + 2))) by simp]
  refine Filter.Tendsto.mul ?_ ?_
  · refine Filter.Tendsto.zero_mul_isBoundedUnder_le ?_ ?_
    · simp_rw [pow_mul]
      apply tendsto_pow_atTop_nhds_zero_of_norm_lt_one
      rw [norm_pow]
      exact (pow_lt_one_iff_of_nonneg (by simp) (by simp)).mpr hx
    · use 2
      simp_rw [eventually_map, Function.comp_apply, eventually_atTop]
      use 0
      intro n hn
      apply (norm_sub_le _ _).trans
      apply add_le_of_le_sub_right
      norm_num
      exact pow_le_one₀ (by simp) hx.le
  · apply Multipliable.tendsto_prod_tprod_nat
    simp_rw [sub_eq_add_neg]
    apply multipliable_one_add_of_summable
    simp_rw [norm_neg, norm_pow, add_right_comm _ _ 2, pow_add _ (N + 2)]
    apply (summable_geometric_of_lt_one (by simp) hx).mul_left

theorem multipliable_pentagonalLhs' {x : ℂ} (hx : ‖x‖ < 1) :
    Multipliable (fun n ↦ 1 - x ^ (n + 1)) := by
  simp_rw [sub_eq_add_neg]
  apply multipliable_one_add_of_summable
  simp_rw [norm_neg, norm_pow, pow_add]
  apply (summable_geometric_of_lt_one (by simp) hx).mul_right

theorem pentagonalLhs_γ0' {x : ℂ} (hx : ‖x‖ < 1) :
    ∏' n, (1 - x ^ (n + 1)) = 1 - x - x ^ 2 * ∑' n, γ' 0 n x := by
  obtain hsum := summable_γ' 0 hx
  unfold γ' at hsum
  simp_rw [zero_add, one_mul] at hsum
  have hsum' : Summable fun i ↦ x ^ (i + 1) * ∏ n ∈ Finset.range i, (1 - x ^ (n + 1)) := by
    apply Summable.comp_nat_add (k := 1)
    conv in fun k ↦ _ =>
      ext k
      rw [pow_add, pow_add, mul_assoc (x ^ k), mul_comm (x ^ k), mul_assoc (x ^ 1 * x ^ 1)]
    apply Summable.mul_left _ hsum

  rw [tprod_one_sub_ordererd (by simpa [Nat.Iio_eq_range] using hsum')
    (multipliable_pentagonalLhs' hx)]
  simp_rw [Nat.Iio_eq_range, sub_sub, sub_right_inj, Summable.tsum_eq_zero_add hsum']
  conv in fun k ↦ x ^ (k + 1 + 1) * _ =>
    ext k
    rw [pow_add, pow_add, mul_assoc (x ^ k), mul_comm (x ^ k),
      ← pow_add x 1 1, one_add_one_eq_two, mul_assoc (x ^ 2)]
  rw [Summable.tsum_mul_left _ hsum]
  simp [γ']

theorem pentagonalLhs_γ' (N : ℕ) {x : ℂ} (hx : ‖x‖ < 1) : ∏' n, (1 - x ^ (n + 1)) =
    ∑ k ∈ Finset.range (N + 1), (-1) ^ k *
      (x ^ (k * (3 * k + 1) / 2) - x ^ ((k + 1) * (3 * k + 2) / 2))
      + (-1) ^ (N + 1) * x ^ ((N + 1) * (3 * N + 4) / 2) * ∑' n, γ' N n x := by
  induction N with
  | zero =>
    simp [pentagonalLhs_γ0' hx, γ']
    ring_nf
  | succ n ih =>
    rw [ih, γ_rec' _ hx, Finset.sum_range_succ _ (n + 1)]
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

theorem summable_pentagonalRhs' {x : ℂ} (hx : ‖x‖ < 1) :
    Summable (fun (k : ℕ) ↦
    ((-1) ^ k * (x ^ (k * (3 * k + 1) / 2) - x ^ ((k + 1) * (3 * k + 2) / 2)))) := by
  rw [← summable_norm_iff]
  simp_rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  rw [summable_norm_iff]
  apply Summable.sub
  · rw [← summable_norm_iff]
    refine Summable.of_nonneg_of_le (by simp) ?_ (summable_geometric_of_lt_one (by simp) hx)
    intro k
    rw [norm_pow]
    apply pow_le_pow_of_le_one (by simp) (hx.le)
    obtain rfl | h0 := Nat.eq_zero_or_pos k
    · simp
    rw [Nat.le_div_iff_mul_le (by simp)]
    exact Nat.mul_le_mul_left _ (by linarith)
  · rw [← summable_norm_iff]
    refine Summable.of_nonneg_of_le (by simp) ?_ (summable_geometric_of_lt_one (by simp) hx)
    intro k
    rw [norm_pow]
    apply pow_le_pow_of_le_one (by simp) (hx.le)
    rw [Nat.le_div_iff_mul_le (by simp)]
    exact Nat.mul_le_mul (by simp) (by simp)

theorem pentagonalNumberTheorem_complex {x : ℂ} (hx : ‖x‖ < 1) :
    ∏' n, (1 - x ^ (n + 1)) =
    ∑' k, (-1) ^ k * (x ^ (k * (3 * k + 1) / 2) - x ^ ((k + 1) * (3 * k + 2) / 2)) := by
  refine (HasSum.tsum_eq ?_).symm
  rw [(summable_pentagonalRhs' hx).hasSum_iff_tendsto_nat, (map_add_atTop_eq_nat 1).symm]
  apply tendsto_map'
  change Tendsto
    (fun n ↦ ∑ i ∈ Finset.range (n + 1), (-1) ^ i *
      (x ^ (i * (3 * i + 1) / 2) - x ^ ((i + 1) * (3 * i + 2) / 2)))
    atTop (nhds (∏' (n : ℕ), (1 - x ^ (n + 1))))
  obtain h := fun n ↦ pentagonalLhs_γ' n hx
  simp_rw [← sub_eq_iff_eq_add] at h
  simp_rw [← h]
  rw [← tendsto_sub_nhds_zero_iff]
  simp_rw [sub_sub_cancel_left]
  rw [show (nhds (0 : ℂ)) = (nhds (-0)) by simp]
  apply Filter.Tendsto.neg
  apply Filter.Tendsto.zero_mul_isBoundedUnder_le
  · apply Filter.isBoundedUnder_le_mul_tendsto_zero
    · exact ⟨1, by simp⟩
    · apply (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hx).comp
      rw [Filter.tendsto_atTop_atTop]
      refine fun k ↦ ⟨k, fun n hn ↦ hn.trans ?_⟩
      rw [Nat.le_div_iff_mul_le (by simp)]
      exact Nat.mul_le_mul (by simp) (by simp)
  · use (1 - ‖x‖)⁻¹ * ∏' i, (1 + ‖x‖ ^ i)
    simp_rw [eventually_map, Function.comp_apply, eventually_atTop]
    exact ⟨0, fun N _ ↦ tsum_γ'_bound N hx⟩

theorem summable_pentagonalRhs_intNeg_complex {x : ℂ} (hx : ‖x‖ < 1) :
    Summable (fun (k : ℤ) ↦ (-1) ^ k * x ^ (k * (3 * k + 1) / 2)) := by
  apply Summable.of_add_one_of_neg_add_one
  all_goals
  rw [← summable_norm_iff]
  simp_rw [norm_mul, norm_zpow, norm_neg, norm_one, one_zpow, one_mul]
  refine Summable.of_nonneg_of_le (fun k ↦ by apply zpow_nonneg (by simp)) (fun k ↦ ?_)
   (summable_geometric_of_lt_one (by simp) hx)
  rw [← zpow_natCast]
  obtain h0 | h0 := eq_or_lt_of_le (norm_nonneg x)
  · simp_rw [← h0]
    obtain rfl | hk0 := eq_or_ne k 0
    · norm_num
    rw [zero_zpow _ ?_, zero_zpow _ (by simpa using hk0)]
    grind
  apply zpow_le_zpow_right_of_le_one₀ h0 hx.le
  grind

theorem pentagonalNumberTheorem_intNeg_complex {x : ℂ} (hx : ‖x‖ < 1) :
    ∏' n, (1 - x ^ (n + 1)) =
    ∑' (k : ℤ), (-1) ^ k * x ^ (k * (3 * k + 1) / 2) := by
  rw [← tsum_nat_add_neg_add_one (summable_pentagonalRhs_intNeg_complex hx),
    pentagonalNumberTheorem_complex hx]
  apply tsum_congr
  intro k
  rw [sub_eq_add_neg _ (x ^ _), mul_add, ← neg_mul_comm]
  apply congr($(by norm_cast) * $(by norm_cast) + $_ * $(by norm_cast))
  trans (-1) ^ (k + 1)
  · ring
  · rw [zpow_neg, ← inv_zpow, inv_neg, inv_one]
    norm_cast

theorem summable_pentagonalRhs_intPos_complex {x : ℂ} (hx : ‖x‖ < 1) :
    Summable (fun (k : ℤ) ↦ (-1) ^ k * x ^ (k * (3 * k - 1) / 2)) := by
  rw [← neg_injective.summable_iff (by intro x hx; contrapose! hx; use -x; simp)]
  convert summable_pentagonalRhs_intNeg_complex hx
  rw [Function.comp_apply]
  apply congr($_ * x ^ ($(by ring_nf) / 2))
  rw [zpow_neg, ← inv_zpow, inv_neg, inv_one]

theorem pentagonalNumberTheorem_intPos_complex {x : ℂ} (hx : ‖x‖ < 1) :
    ∏' n, (1 - x ^ (n + 1)) =
    ∑' (k : ℤ), (-1) ^ k * x ^ (k * (3 * k - 1) / 2) := by
  rw [pentagonalNumberTheorem_intNeg_complex hx, ← neg_injective.tsum_eq (by simp)]
  apply tsum_congr
  intro k
  apply congr($_ * x ^ ($(by ring_nf) / 2))
  rw [zpow_neg, ← inv_zpow, inv_neg, inv_one]
