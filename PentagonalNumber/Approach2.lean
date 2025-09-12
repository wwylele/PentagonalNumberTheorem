import Mathlib

/-!

# Pentagonal number theorem, second approach

This file proves the
[pentagonal number theorem](https://en.wikipedia.org/wiki/Pentagonal_number_theorem)
using another approach described in
https://math.stackexchange.com/questions/55738/how-to-prove-eulers-pentagonal-theorem-some-hints-will-help


-/

open PowerSeries Finset
open scoped PowerSeries.WithPiTopology

namespace PowerSeries

variable {R : Type*}

theorem order_neg [Ring R] (a : R⟦X⟧) : (-a).order = a.order := by
  simp_rw [PowerSeries.order_eq, map_neg, neg_eq_zero, neg_ne_zero]
  rw [← PowerSeries.order_eq]

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

end PowerSeries

noncomputable
def AN_term (N n : ℕ) : PowerSeries ℤ := X ^ (N * n) * ∏ i ∈ Finset.range (n + 1), (1 - X ^ (N + i))

theorem AN_summable (N : ℕ) (hN : 0 < N) : Summable (AN_term N) := by
  rw [WithPiTopology.summable_iff]
  intro n
  apply summable_of_finite_support
  apply Set.Finite.subset (Set.finite_Iic n)
  simp_rw [Function.support_subset_iff, Set.mem_Iic]
  intro k h
  contrapose! h
  unfold AN_term
  have : ¬ N * k ≤ n := by
    rw [not_le]
    exact h.trans_le <| Nat.le_mul_of_pos_left k hN
  simp [PowerSeries.coeff_X_pow_mul', this]

noncomputable
def BN_term (N n : ℕ) : PowerSeries ℤ :=
  X ^ (N * n) * (1 - X ^ N + X ^ (3 * N + n + 2) - X ^ (4 * N + 2 * n + 3)) *
  ∏ i ∈ Finset.range n, (1 - X ^ (N + i + 1))

theorem AN_BN (N n : ℕ) : AN_term N n + X ^ (3 * N + 2) * AN_term (N + 1) n = BN_term N n := by
  unfold BN_term
  rw [add_sub_assoc]
  rw [mul_add, add_mul]
  congr 1
  · unfold AN_term
    rw [Finset.prod_range_eq_mul_Ico _ (show 0 < n + 1 by simp)]
    rw [Finset.prod_Ico_eq_prod_range]
    rw [add_tsub_cancel_right]
    ring_nf
  · unfold AN_term
    rw [Finset.prod_range_succ_comm]
    ring_nf

noncomputable
def CN (N n : ℕ) : PowerSeries ℤ :=
  X ^ (N * n) * (X ^ (2 * N + n + 1) - 1) * ∏ i ∈ Finset.range n, (1 - X ^ (N + i + 1))

theorem coeff_CN {N n k : ℕ} (h : k < N * n) : coeff k (CN N n) = 0 := by
  unfold CN
  rw [mul_assoc]
  apply PowerSeries.coeff_of_lt_order
  rw [PowerSeries.order_mul, order_X_pow]
  apply lt_add_of_lt_of_nonneg
  · norm_cast
  · simp

theorem BN_CN (N n : ℕ) : BN_term N n = CN N (n + 1) - CN N n := by
  unfold CN
  rw [Finset.prod_range_succ_comm]
  unfold BN_term
  ring_nf

theorem AN_rec (N : ℕ) (hN : 0 < N) (u : PowerSeries ℤ) (h : HasSum (AN_term (N + 1)) u) :
    HasSum (AN_term N) (1 - X ^ (2 * N + 1) - X ^ (3 * N + 2) * u) := by
  suffices HasSum (fun n ↦ AN_term N n + X ^ (3 * N + 2) * AN_term (N + 1) n)
      (1 - X ^ (2 * N + 1)) by
    simpa using this.sub (h.mul_left (X ^ (3 * N + 2)))
  simp_rw [AN_BN, BN_CN]
  unfold HasSum
  rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro n
  apply tendsto_atTop_of_eventually_const (i₀ := Finset.range (n + 1))
  intro s hs
  rw [← Finset.sum_sdiff hs]
  rw [Finset.sum_range_sub]
  rw [← add_sub_assoc]
  conv =>
    left
    simp only [Finset.sum_sub_distrib, map_sub, map_add, map_sum]
  apply sub_eq_of_eq_add
  trans 0
  · rw [coeff_CN ((Nat.lt_add_one n).trans_le (by simpa using hN))]
    rw [add_zero, sub_eq_zero]
    trans 0
    · apply Finset.sum_eq_zero
      simp_rw [Finset.mem_sdiff, Finset.mem_range, not_lt, and_imp, Nat.add_one_le_iff]
      intro k _ hk
      rw [coeff_CN (hk.trans ((Nat.lt_add_one k).trans_le (by simpa using hN)))]
    · symm
      apply Finset.sum_eq_zero
      simp_rw [Finset.mem_sdiff, Finset.mem_range, not_lt, and_imp, Nat.add_one_le_iff]
      intro k _ hk
      rw [coeff_CN (hk.trans_le (Nat.le_mul_of_pos_left _ (by simpa using hN)))]
  · rw [← map_add, CN]
    convert (map_zero (coeff n (R := ℤ))).symm
    ring_nf

theorem A1 (u : PowerSeries ℤ) (h : HasSum (AN_term 1) u) :
    HasProd (fun n ↦ 1 - X ^ (n + 1)) (1 - X - X ^ 2 * u) := by
  unfold HasProd
  rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro n
  apply tendsto_atTop_of_eventually_const (i₀ := Finset.range (n + 1))
  intro s hs
  rw [← Finset.prod_sdiff hs]
  rw [PowerSeries.coeff_mul]
  rw [Finset.sum_eq_single_of_mem (0, n) (by simp) ?_]
  · have : (coeff (0, n).1)
      (∏ n ∈ s \ Finset.range (n + 1), ((1 : ℤ⟦X⟧) - X ^ (n + 1))) = 1 := by simp
    rw [this, one_mul]
    rw [Finset.prod_one_sub_ordered]
    rw [Finset.sum_range_eq_add_Ico _ (by simp)]
    rw [← sub_sub]
    simp_rw [map_sub]
    apply congr(_ - $_ - $_)
    · simp
    rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    conv in fun (k : ℕ) ↦ X ^ (1 + k + 1) * _ =>
      ext k
      rw [add_right_comm, one_add_one_eq_two, pow_add, mul_assoc]
    rw [← Finset.mul_sum]
    cases n with
    | zero => simp
    | succ n => cases n with
      | zero => simp [PowerSeries.coeff_X_pow_mul']
      | succ n =>
    rw [show n + 1 + 1 = n + 2 by simp]
    simp_rw [PowerSeries.coeff_X_pow_mul]
    unfold HasSum at h
    rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto] at h
    specialize h n
    refine tendsto_nhds_unique ?_ h
    apply tendsto_atTop_of_eventually_const (i₀ := Finset.range (n + 2))
    intro t ht
    simp_rw [map_sum]
    rw [Finset.sum_subset ht ?_]
    · apply Finset.sum_congr rfl
      intro k _
      unfold AN_term
      rw [one_mul]
      by_cases hk : k ≤ n
      · apply congr((coeff n) (X ^ k * Finset.prod $_ $_))
        · rw [show k + 1 = 1 + k by ring]
          ext x
          suffices x < 1 + k → x < n + 2 + 1 by simpa
          intro h
          apply h.trans_le
          linarith
        ring_nf
      · simp [PowerSeries.coeff_X_pow_mul', hk]
    intro x hx hx2
    have : ¬ x ≤ n := by
      rw [not_le]
      exact (show n < n + 2 by simp).trans_le (by simpa using hx2)
    simp [PowerSeries.coeff_X_pow_mul', this]
  · intro b hb1 hb2
    rw [Finset.mem_antidiagonal] at hb1
    apply mul_eq_zero_of_left
    rw [PowerSeries.coeff_prod]
    apply Finset.sum_eq_zero
    intro x hx
    have hsupp : x.support.Nonempty := by
      contrapose! hb2 with h
      obtain rfl : x = 0 := by simpa using h
      obtain hb : 0 = b.1 := by simpa using hx
      rw [← hb] at hb1
      ext
      · exact hb.symm
      · simpa using hb1
    obtain ⟨y, hy⟩ := hsupp
    obtain ⟨hx1, hx2⟩ := Finset.mem_finsuppAntidiag.mp hx
    obtain hymem := (Finset.mem_of_subset hx2 hy)
    apply Finset.prod_eq_zero hymem
    have hxy0 : ¬ x y = 0 := by simpa using hy
    have hxyy : ¬ x y = y + 1 := by
      by_contra! h
      have : y ≤ x y := by simp [h]
      have : y ≤ b.1 := by
        rw [← hx1]
        exact le_trans this (Finset.single_le_sum (by simp) hymem)
      have : y ≤ n := by
        rw [← hb1]
        exact this.trans (Nat.le_add_right b.1 b.2)
      obtain ⟨_, hymem⟩ : y ∈ s ∧ n + 1 ≤ y := by simpa using hymem
      obtain h := hymem.trans this
      simp at h
    simp [coeff_X_pow, hxy0, hxyy]

theorem pentagonal_rec {n : ℕ} (hn : 0 < n) :
    ∀ {u : PowerSeries ℤ}, HasSum (AN_term n) u →
    HasProd (fun n ↦ 1 - X ^ (n + 1))
    (1 + ∑ k ∈ Finset.range n, ((-1) ^ (k + 1) *
      (X ^ ((k + 1) * (3 * k + 2) / 2) + X ^ ((k + 1) * (3 * k + 4) / 2))) +
      X ^ (n * (3 * n + 1) / 2) * (-1) ^ n * (u - 1)) := by
  induction n, hn using Nat.le_induction with
  | base =>
    intro u h
    convert A1 u h using 1
    simp
    ring_nf
  | succ n hn ih =>
    intro u h
    obtain h := ih <| AN_rec _ hn _ h
    convert h using 1
    rw [Finset.sum_range_succ]
    simp_rw [add_assoc]
    congr
    have : ((-1) ^ (n + 1)) = (-(-1) ^ n : ℤ⟦X⟧) := by
      rw [npow_add]
      simp
    simp_rw [this]
    have : 3 * (n + 1) + 1 = 3 * n + 4 := by ring
    simp_rw [this]
    conv =>
      right
      rw [mul_comm (X ^ (n * (3 * n + 1) / 2)), mul_assoc]
      rw [sub_right_comm _ _ 1, sub_right_comm _ _ 1, sub_self, zero_sub]
      rw [← neg_add', mul_neg, mul_neg, ← neg_mul, mul_add (X ^ (n * (3 * n + 1) / 2))]
      rw [← mul_assoc _ _ u]
      rw [← pow_add, ← pow_add]
      rw [← Nat.add_mul_div_left _ _ (by simp), ← Nat.add_mul_div_left _ _ (by simp)]
    conv =>
      left
      rw [mul_comm (X ^ ((n + 1) * (3 * n + 4) / 2)), mul_assoc]
      rw [← mul_add, mul_sub_one, add_add_sub_cancel]
    apply congr(_ * (X ^ ($_ / 2) + X ^ ($_ / 2) * u))
    · ring
    · ring

theorem pentagonal_const {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {u v : ℤ⟦X⟧}
    (hu : HasSum (AN_term m) u) (hv : HasSum (AN_term n) v) :
    (1 + ∑ k ∈ Finset.range m, ((-1) ^ (k + 1) *
      (X ^ ((k + 1) * (3 * k + 2) / 2) + X ^ ((k + 1) * (3 * k + 4) / 2))) +
      X ^ (m * (3 * m + 1) / 2) * ((-1) ^ m) * (u - 1)) =
    (1 + ∑ k ∈ Finset.range n, ((-1) ^ (k + 1) *
      (X ^ ((k + 1) * (3 * k + 2) / 2) + X ^ ((k + 1) * (3 * k + 4) / 2))) +
      X ^ (n * (3 * n + 1) / 2) * (-1) ^ n * (v - 1)) :=
  HasProd.unique (pentagonal_rec hm hu) (pentagonal_rec hn hv)

theorem term_order (k : ℕ) : ((-1 : ℤ⟦X⟧) ^ (k + 1) *
    (X ^ ((k + 1) * (3 * k + 2) / 2) + X ^ ((k + 1) * (3 * k + 4) / 2))).order =
    ↑((k + 1) * (3 * k + 2) / 2) := by
  simp_rw [PowerSeries.order_mul]
  have (k : ℕ) : ((-1) ^ (k + 1) : ℤ⟦X⟧).order = 0 := by
    simp [order_pow, order_neg]
  simp_rw [this, zero_add]
  have hdvd (k : ℕ) : 2 ∣ (k + 1) * (3 * k + 4) := by
    obtain heven | hodd := Nat.even_or_odd k
    · apply Nat.dvd_mul_left_of_dvd
      refine Nat.dvd_add ?_ (by simp)
      apply Nat.dvd_mul_left_of_dvd <| even_iff_two_dvd.mp heven
    · apply Nat.dvd_mul_right_of_dvd <| even_iff_two_dvd.mp <| Odd.add_one hodd
  have (k : ℕ) : (k + 1) * (3 * k + 2) / 2 < (k + 1) * (3 * k + 4) / 2 := by
    apply Nat.div_lt_div_of_lt_of_dvd (hdvd k)
    simp
  rw [PowerSeries.order_add_of_order_eq _ _ (by simpa using (this k).ne)]
  simpa using (this k).le

theorem pentagonal_lim (u : ℤ⟦X⟧) (v : ℕ → ℤ⟦X⟧)
    (hu : HasSum (fun (k : ℕ) ↦ ((-1) ^ (k + 1) *
      (X ^ ((k + 1) * (3 * k + 2) / 2) + X ^ ((k + 1) * (3 * k + 4) / 2)))) u) :
    Filter.Tendsto (fun n ↦ (1 + ∑ k ∈ Finset.range n, ((-1) ^ (k + 1) *
      (X ^ ((k + 1) * (3 * k + 2) / 2) + X ^ ((k + 1) * (3 * k + 4) / 2))) +
      X ^ (n * (3 * n + 1) / 2) * (-1) ^ n * (v n - 1)))
      Filter.atTop (nhds (1 + u)) := by
  rw [WithPiTopology.tendsto_iff_coeff_tendsto]
  intro n
  apply tendsto_atTop_of_eventually_const (i₀ := (n + 1))
  intro i hi
  simp_rw [map_add]
  rw [mul_assoc]
  have hni : n < i * (3 * i + 1) / 2 := by
    rw [ge_iff_le, Nat.add_one_le_iff] at hi
    apply hi.trans_le
    rw [Nat.le_div_iff_mul_le (by simp)]
    obtain rfl | h0 := Nat.eq_zero_or_pos i
    · simp
    apply Nat.mul_le_mul_left
    linarith
  simp only [PowerSeries.coeff_X_pow_mul', not_le.mpr hni, ↓reduceIte, add_zero]
  rw [add_left_cancel_iff, map_sum]

  rw [WithPiTopology.has_sum_iff] at hu
  specialize hu n
  refine tendsto_nhds_unique ?_ hu
  apply tendsto_atTop_of_eventually_const (i₀ := Finset.range i)
  intro s hs
  rw [← Finset.sum_sdiff hs, add_eq_right]
  apply Finset.sum_eq_zero
  intro x hx
  rw [Finset.mem_sdiff, Finset.mem_range, not_lt] at hx
  obtain hx := hx.2
  apply PowerSeries.coeff_of_lt_order
  rw [term_order, Nat.cast_lt]
  apply hni.trans_le
  apply Nat.div_le_div_right
  apply Nat.mul_le_mul <;> linarith

theorem pentagonal_lim_eq {u : ℤ⟦X⟧} {v : ℕ → ℤ⟦X⟧}
    (hu : HasSum (fun (k : ℕ) ↦ ((-1) ^ (k + 1) *
      (X ^ ((k + 1) * (3 * k + 2) / 2) + X ^ ((k + 1) * (3 * k + 4) / 2)))) u)
    {n : ℕ} (hn : 0 < n) (hv : ∀ n, 0 < n → HasSum (AN_term n) (v n)) :
    (1 + ∑ k ∈ Finset.range n, ((-1) ^ (k + 1) *
      (X ^ ((k + 1) * (3 * k + 2) / 2) + X ^ ((k + 1) * (3 * k + 4) / 2))) +
      X ^ (n * (3 * n + 1) / 2) * (-1) ^ n * (v n - 1)) =
    1 + u := by
  obtain hlim := pentagonal_lim u v hu

  have : (fun n ↦ 1 +
        ∑ k ∈ Finset.range n,
          (-1) ^ (k + 1) * (X ^ ((k + 1) * (3 * k + 2) / 2) +
          X ^ ((k + 1) * (3 * k + 4) / 2)) +
        X ^ (n * (3 * n + 1) / 2) * (-1) ^ n * (v n - 1)) =ᶠ[Filter.atTop]
      (fun _ ↦ 1 +
        ∑ k ∈ Finset.range n,
          (-1) ^ (k + 1) * (X ^ ((k + 1) * (3 * k + 2) / 2) +
          X ^ ((k + 1) * (3 * k + 4) / 2)) +
        X ^ (n * (3 * n + 1) / 2) * (-1) ^ n * (v n - 1)) := by
    unfold Filter.EventuallyEq
    rw [Filter.eventually_atTop]
    use 1
    intro m hm
    simp only
    apply pentagonal_const hm hn (hv m hm) (hv n hn)
  rw [Filter.tendsto_congr' this] at hlim
  exact tendsto_nhds_unique tendsto_const_nhds hlim

theorem pentagonal_inf (u : ℤ⟦X⟧) (hu : HasSum (fun (k : ℕ) ↦ (-1) ^ (k + 1) *
    (X ^ ((k + 1) * (3 * k + 2) / 2) + X ^ ((k + 1) * (3 * k + 4) / 2))) u) :
    HasProd (fun n ↦ 1 - X ^ (n + 1)) (1 + u) := by
  choose f hf using AN_summable
  let f' (n : ℕ) := if h : 0 < n then f n h else 0
  have hf' (n : ℕ) (hn : 0 < n) : HasSum (AN_term n) (f' n) := by
    simpa [f', hn] using hf n
  obtain h := pentagonal_rec (show 0 < 1 by simp) (hf' 1 (by simp))
  convert ← h using 1
  exact pentagonal_lim_eq hu (by simp) hf'

theorem summable_pentagonal :
    Summable (fun (k : ℕ) ↦ ((-1 : ℤ⟦X⟧) ^ (k + 1) *
    (X ^ ((k + 1) * (3 * k + 2) / 2) + X ^ ((k + 1) * (3 * k + 4) / 2)))) := by
  apply WithPiTopology.summable_of_order_tendsto_atTop_atTop
  simp_rw [term_order, ENat.tendsto_nhds_top_iff_natCast_lt, Filter.eventually_atTop]
  intro k
  use k
  intro a ha
  rw [Nat.cast_lt]
  apply ha.trans_lt
  rw [Nat.lt_div_iff_mul_lt (by simp)]
  norm_num
  apply Nat.lt_sub_of_add_lt
  apply lt_of_lt_of_le (show a * 2 + 1 < 1 * (3 * a + 2) by omega)
  apply Nat.mul_le_mul_right
  simp

theorem pentagonalNumberTheorem_hasProd :
    HasProd (fun n ↦ (1 - X ^ (n + 1)  : ℤ⟦X⟧))
    (1 + ∑' k : ℕ, (-1) ^ (k + 1) *
    (X ^ ((k + 1) * (3 * k + 2) / 2) + X ^ ((k + 1) * (3 * k + 4) / 2))) := by
  apply pentagonal_inf
  apply summable_pentagonal.hasSum

/-- Pentagonal number theorem -/
theorem pentagonalNumberTheorem_prod_eq :
    (∏' n, (1 - X ^ (n + 1)) : ℤ⟦X⟧) =
    1 + ∑' k : ℕ, (-1) ^ (k + 1) *
    (X ^ ((k + 1) * (3 * k + 2) / 2) + X ^ ((k + 1) * (3 * k + 4) / 2)) := by
  exact pentagonalNumberTheorem_hasProd.tprod_eq
