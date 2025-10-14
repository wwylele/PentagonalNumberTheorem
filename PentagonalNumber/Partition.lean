import PentagonalNumber.PowerSeries

theorem two_pentagonal (k : ℤ) : 2 * (k * (3 * k - 1) / 2) = k * (3 * k - 1) := by
  refine Int.two_mul_ediv_two_of_even ?_
  obtain h | h := Int.even_or_odd k
  · exact Even.mul_right h (3 * k - 1)
  · refine Even.mul_left ?_ _
    refine Int.even_sub_one.mpr ?_
    refine Int.not_even_iff_odd.mpr ?_
    refine Odd.mul ?_ h
    decide

theorem pentagonal_nonneg (k : ℤ) : 0 ≤ k * (3 * k - 1) / 2 := by
  suffices 0 ≤ 2 * (k * (3 * k - 1) / 2) by simpa
  rw [two_pentagonal]
  obtain h | h := lt_or_ge 0 k
  · exact mul_nonneg h.le (by linarith)
  · exact mul_nonneg_of_nonpos_of_nonpos h (by linarith)

theorem two_pentagonal_inj {x y : ℤ} (h : x * (3 * x - 1) = y * (3 * y - 1)) : x = y := by
  simp_rw [mul_sub_one] at h
  rw [sub_eq_sub_iff_sub_eq_sub] at h
  rw [mul_left_comm x, mul_left_comm y] at h
  rw [← mul_sub] at h
  rw [mul_self_sub_mul_self] at h
  rw [← mul_assoc] at h
  rw [← sub_eq_zero, ← sub_one_mul] at h
  rw [mul_eq_zero] at h
  obtain h | h := h
  · obtain h' := Int.eq_of_mul_eq_one <| eq_of_sub_eq_zero h
    simp [← h'] at h
  · exact eq_of_sub_eq_zero h

theorem pentagonal_injective : Function.Injective (fun (k : ℤ) ↦ k * (3 * k - 1) / 2) := by
  intro a b h
  have : a * (3 * a - 1) = b * (3 * b - 1) := by
    rw [← two_pentagonal a, ← two_pentagonal b]
    simp [h]
  apply two_pentagonal_inj this

theorem pentagonal_toNat_injective :
    Function.Injective (fun (k : ℤ) ↦ (k * (3 * k - 1) / 2).toNat) := by
  intro a b h
  apply pentagonal_injective
  zify at h
  simpa [pentagonal_nonneg] using h

theorem Finset.finsuppAntidiag_mono {ι : Type*} {μ : Type*}
    [DecidableEq ι] [AddCommMonoid μ] [HasAntidiagonal μ] [DecidableEq μ]
    {s t : Finset ι} (h : s ⊆ t) (n : μ) :
    finsuppAntidiag s n ⊆ finsuppAntidiag t n := by
  intro a
  simp_rw [Finset.mem_finsuppAntidiag']
  rintro ⟨hsum, hmem⟩
  exact ⟨hsum, hmem.trans h⟩

namespace Nat.Partition

open PowerSeries Finset
open scoped PowerSeries.WithPiTopology


theorem le_of_mem_parts {n : ℕ} {p : Partition n} {m : ℕ} (h : m ∈ p.parts) :
    m ≤ n := by
  rw [← p.parts_sum]
  exact Multiset.le_sum_of_mem h

variable {M : Type*} [CommSemiring M]

noncomputable
def genFun (f : ℕ → ℕ → M) : M⟦X⟧ :=
  PowerSeries.mk fun n ↦ ∑ p : n.Partition, ∏ i ∈ p.parts.toFinset, f i (p.parts.count i)

variable [TopologicalSpace M] [Nontrivial M]

theorem genFun_term_summable (f : ℕ → ℕ → M) (i : ℕ) :
    Summable fun j ↦ f (i + 1) (j + 1) • (X : M⟦X⟧) ^ ((i + 1) * (j + 1)) := by
  apply WithPiTopology.summable_of_tendsto_order_atTop_nhds_top
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr (fun n ↦ Filter.eventually_atTop.mpr ⟨n, ?_⟩)
  intro m hm
  rw [PowerSeries.smul_eq_C_mul]
  refine (lt_of_lt_of_le (lt_add_of_nonneg_of_lt (by simp) ?_) (le_order_mul _ _))
  rw [order_X_pow]
  norm_cast
  grind

variable [T2Space M]

theorem injOn_sub_one_parts {n : ℕ} (p : Partition n) :
    Set.InjOn (fun x ↦ x - 1) p.parts.toFinset := by
  intro a ha b hb
  exact tsub_inj_left (p.parts_pos (by simpa using ha)) (p.parts_pos (by simpa using hb))

theorem map_sub_one_parts_subset {n : ℕ} (p : Partition n) :
    (Multiset.map (fun x ↦ x - 1) p.parts).toFinset ⊆ Finset.range n := by
  intro m
  rw [Multiset.mem_toFinset, Finset.mem_range]
  suffices ∀ x ∈ p.parts, x - 1 = m → m < n by simpa
  rintro x h1 rfl
  exact Nat.sub_one_lt_of_le (p.parts_pos h1) (le_of_mem_parts h1)

theorem mapsTo_sub_one_parts {n : ℕ} (p : Partition n) :
    Set.MapsTo (fun x ↦ x - 1) p.parts.toFinset (Finset.range n) := by
  intro a ha
  apply Finset.mem_of_subset (map_sub_one_parts_subset p)
  rw [Multiset.mem_toFinset, Multiset.mem_map]
  exact ⟨a, by simpa using ha⟩

def toFinsuppAntidiag {n : ℕ} (p : Partition n) : ℕ →₀ ℕ where
  toFun m := p.parts.count (m + 1) * (m + 1)
  support := (p.parts.map (· - 1)).toFinset
  mem_support_toFun m := by
    suffices (∃ a ∈ p.parts, a - 1 = m) ↔ m + 1 ∈ p.parts by simpa
    trans (∃ a ∈ p.parts, a = m + 1)
    · refine ⟨fun ⟨a, h1, h2⟩ ↦ ⟨a, h1, ?_⟩, fun ⟨a, h1, h2⟩ ↦ ⟨a, h1, Nat.sub_eq_of_eq_add h2⟩⟩
      exact Nat.eq_add_of_sub_eq (Nat.one_le_of_lt (p.parts_pos h1)) h2
    · simp

theorem toFinsuppAntidiag_injective (n : ℕ) :
    Function.Injective (toFinsuppAntidiag (n := n)) := by
  unfold toFinsuppAntidiag
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
  · refine Nat.eq_of_mul_eq_mul_right h0 <| ?_
    convert funext_iff.mp hcount (m - 1) <;> exact (Nat.sub_eq_iff_eq_add h0).mp rfl

theorem range_toFinsuppAntidiag (n : ℕ) :
    Set.range (toFinsuppAntidiag (n := n)) ⊆ (Finset.range n).finsuppAntidiag n := by
  unfold toFinsuppAntidiag
  rw [Set.range_subset_iff]
  intro p
  suffices ∑ m ∈ Finset.range n, Multiset.count (m + 1) p.parts * (m + 1) = n by
    simpa [map_sub_one_parts_subset p]
  refine Eq.trans ?_ p.parts_sum
  simp_rw [Finset.sum_multiset_count, smul_eq_mul]
  refine (Finset.sum_of_injOn (· - 1) (injOn_sub_one_parts p) (mapsTo_sub_one_parts p) ?_ ?_).symm
  · suffices ∀ i ∈ Finset.range n, (∀ x ∈ p.parts, x - 1 ≠ i) → i + 1 ∉ p.parts by simpa
    intro i hi h
    contrapose! h
    exact ⟨i + 1, by simpa using h⟩
  · intro i hi
    suffices i - 1 + 1 = i by simp [this]
    rw [Nat.sub_add_cancel (Nat.one_le_of_lt (p.parts_pos (by simpa using hi)))]

theorem prod_coeff_eq_zero_of_notMem_range (f : ℕ → ℕ → M) {d : ℕ} {s : Finset ℕ}
    {g : ℕ →₀ ℕ} (hg : g ∈ s.finsuppAntidiag d) (hg' : g ∉ Set.range (toFinsuppAntidiag (n := d))) :
    ∏ i ∈ s, (coeff (g i)) (1 + ∑' (j : ℕ),
    f (i + 1) (j + 1) • X ^ ((i + 1) * (j + 1)) : M⟦X⟧) = 0 := by
  suffices ∃ i ∈ s, (coeff (g i)) ((1 : M⟦X⟧) +
      ∑' (j : ℕ), f (i + 1) (j + 1) • X ^ ((i + 1) * (j + 1))) = 0 by
    obtain ⟨i, hi, hi'⟩ := this
    apply Finset.prod_eq_zero hi hi'
  contrapose! hg' with hprod
  have hdvd (x : ℕ) : x + 1 ∣ g x := by
    by_cases hx : x ∈ s
    · specialize hprod x hx
      contrapose! hprod
      rw [map_add, (genFun_term_summable f x).map_tsum _ (WithPiTopology.continuous_coeff _ _)]
      rw [show (0 : M) = 0 + ∑' (i : ℕ), 0 by simp]
      congrm (?_ + ∑' (i : ℕ), ?_)
      · suffices g x ≠ 0 by simp [this]
        contrapose! hprod
        simp [hprod]
      · rw [map_smul, coeff_X_pow]
        apply smul_eq_zero_of_right
        suffices g x ≠ (x + 1) * (i + 1) by simp [this]
        contrapose! hprod
        simp [hprod]
    · suffices g x = 0 by simp [this]
      contrapose! hx
      apply Finset.mem_of_subset (Finset.mem_finsuppAntidiag.mp hg).2
      simpa using hx
  rw [Set.mem_range]
  refine ⟨Nat.Partition.mk (Finsupp.toMultiset
    (Finsupp.mk (g.support.map (Function.Embedding.mk (· + 1) (add_left_injective 1)))
    (fun i ↦ if i = 0 then 0 else g (i - 1) / i) ?_)) (by simp) ?_, ?_⟩
  · intro a
    suffices (∃ b, g b ≠ 0 ∧ b + 1 = a) ↔ a ≠ 0 ∧ a ≤ g (a - 1) by simpa
    constructor
    · rintro ⟨b, h1, rfl⟩
      suffices b + 1 ≤ g b by simpa
      exact Nat.le_of_dvd (Nat.pos_of_ne_zero h1) <| hdvd b
    · rintro ⟨h1, h2⟩
      use a - 1
      grind
  · obtain ⟨h1, h2⟩ := Finset.mem_finsuppAntidiag.mp hg
    rw [← h1]
    suffices ∑ x ∈ g.support, g x / (x + 1) * (x + 1) = ∑ x ∈ s, g x by simpa [Finsupp.sum]
    rw [Finset.sum_subset h2 (by
      intro x _
      suffices g x = 0 → g x < x + 1 by simpa;
      grind)]
    apply Finset.sum_congr rfl
    intro x _
    exact Nat.div_mul_cancel <| hdvd x
  · ext x
    simpa [toFinsuppAntidiag] using Nat.div_mul_cancel <| hdvd x

theorem prod_f_eq_prod_coeff
    (f : ℕ → ℕ → M) {n : ℕ} (p : Partition n) {s : Finset ℕ} (hs : range n ≤ s) :
    ∏ i ∈ p.parts.toFinset, f i (Multiset.count i p.parts) =
    ∏ i ∈ s, coeff (p.toFinsuppAntidiag i)
    (1 + ∑' (j : ℕ), f (i + 1) (j + 1) • X ^ ((i + 1) * (j + 1))) := by
  refine Finset.prod_of_injOn (· - 1) (injOn_sub_one_parts _)
    ((mapsTo_sub_one_parts p).mono_right hs) ?_ ?_
  · intro x hx
    suffices (∀ y ∈ p.parts, y - 1 ≠ x) →
        (if x + 1 ∈ p.parts then (0 : M) else 1) +
        (coeff (Multiset.count (x + 1) p.parts * (x + 1)))
        (∑' (j : ℕ), f (x + 1) (j + 1) • X ^ ((x + 1) * (j + 1))) = 1 + ∑' (j : ℕ), 0
      by simpa [toFinsuppAntidiag]
    intro h
    rw [(genFun_term_summable f x).map_tsum _ (WithPiTopology.continuous_coeff _ _)]
    have hx : x + 1 ∉ p.parts := by
      contrapose! h
      exact ⟨x + 1, by simpa using h⟩
    simp [hx]
  · suffices ∀ i ∈ p.parts,
      0 + (f i (Multiset.count i p.parts) • (1 : M)) =
      (if i - 1 + 1 ∈ p.parts then 0 else 1) +
      (coeff (Multiset.count (i - 1 + 1) p.parts * (i - 1 + 1)))
      (∑' (j : ℕ), f (i - 1 + 1) (j + 1) • X ^ ((i - 1 + 1) * (j + 1))) by simpa [toFinsuppAntidiag]
    intro i hi
    have hicancel : i - 1 + 1 = i := by
      rw [Nat.sub_add_cancel (Nat.one_le_of_lt (p.parts_pos hi))]
    have hpartcancel : Multiset.count i p.parts - 1 + 1 = Multiset.count i p.parts := by
      rw [Nat.sub_add_cancel (Multiset.one_le_count_iff_mem.mpr hi)]
    congrm $(by simp [hicancel, hi]) + ?_
    rw [(genFun_term_summable f _).map_tsum _ (WithPiTopology.continuous_coeff _ _)]
    simp_rw [coeff_smul, coeff_X_pow]
    rw [tsum_eq_single (Multiset.count i p.parts - 1) ?_]
    · rw [mul_comm]
      simp [hicancel, hpartcancel]
    · intro b hb
      suffices Multiset.count i p.parts * i ≠ i * (b + 1) by
        simp [this, hicancel]
      rw [mul_comm i, (mul_left_inj' (Nat.ne_zero_of_lt (p.parts_pos hi))).ne]
      grind

theorem hasProd_genFun (f : ℕ → ℕ → M) :
    HasProd (fun i ↦ (1 : M⟦X⟧) + ∑' j : ℕ, f (i + 1) (j + 1) • X ^ ((i + 1) * (j + 1)))
    (genFun f) := by
  rw [HasProd, WithPiTopology.tendsto_iff_coeff_tendsto]
  refine fun d ↦ tendsto_atTop_of_eventually_const (fun s (hs : s ≥ Finset.range d) ↦ ?_)
  rw [genFun, coeff_mk, coeff_prod]
  refine (Finset.sum_of_injOn toFinsuppAntidiag (toFinsuppAntidiag_injective d).injOn ?_ ?_ ?_).symm
  · refine Set.MapsTo.mono_right (Set.mapsTo_range _ _) ((range_toFinsuppAntidiag d).trans ?_)
    simpa using Finset.finsuppAntidiag_mono hs.le _
  · exact fun g hg hg' ↦ prod_coeff_eq_zero_of_notMem_range f hg (by simpa using hg')
  · exact fun p _ ↦ prod_f_eq_prod_coeff f p hs.le

def restricted (n : ℕ) (p : ℕ → Prop) [DecidablePred p] : Finset (n.Partition) :=
  Finset.univ.filter fun x ↦ ∀ i ∈ x.parts, p i

def countRestricted (n : ℕ) (m : ℕ) : Finset (n.Partition) :=
  Finset.univ.filter fun x ↦ ∀ i ∈ x.parts, x.parts.count i < m

variable (M)

omit [T2Space M] in
theorem summable_powerSeriesMk_restricted_term' (i : ℕ) (k : ℕ) :
    Summable (fun j ↦ (X ^ ((i + 1) * (j + k)) : M⟦X⟧)) := by
  apply WithPiTopology.summable_of_tendsto_order_atTop_nhds_top
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr (fun n ↦ Filter.eventually_atTop.mpr ⟨n + 1, ?_⟩)
  intro m hm
  rw [order_X_pow]
  norm_cast
  nlinarith

omit [T2Space M] in
theorem summable_powerSeriesMk_restricted_term (i : ℕ) :
    Summable (fun j ↦ (X ^ ((i + 1) * j) : M⟦X⟧)) :=
  summable_powerSeriesMk_restricted_term' M i 0

theorem hasProd_powerSeriesMk_restricted [IsTopologicalSemiring M]
    (p : ℕ → Prop) [DecidablePred p] :
    HasProd (fun i ↦ if p (i + 1) then ∑' j : ℕ, X ^ ((i + 1) * j) else 1)
    (PowerSeries.mk fun n ↦ (#(restricted n p) : M)) := by
  convert hasProd_genFun (fun i c ↦ if p i then (1 : M) else 0) using 1
  · ext1 i
    split_ifs
    · rw [tsum_eq_zero_add' ?_]
      · simp
      exact (summable_powerSeriesMk_restricted_term' M i 1)
    · simp
  · simp_rw [genFun, restricted, Finset.card_filter, Finset.prod_boole]
    simp


theorem hasProd_powerSeriesMk_partition [IsTopologicalSemiring M] :
    HasProd (fun i ↦ ∑' j : ℕ, X ^ ((i + 1) * j))
    (PowerSeries.mk fun n ↦ (Fintype.card n.Partition : M)) := by
  convert hasProd_powerSeriesMk_restricted M (fun _ ↦ True)
  simp [restricted]


theorem hasProd_powerSeriesMk_countRestricted [IsTopologicalSemiring M] {m : ℕ} (hm : 0 < m) :
    HasProd (fun i ↦ ∑ j ∈ Finset.range m, X ^ ((i + 1) * j))
    (PowerSeries.mk fun n ↦ (#(countRestricted n m) : M)) := by
  convert hasProd_genFun (fun i c ↦ if c < m then (1 : M) else 0) using 1
  · ext1 i
    rw [Finset.sum_range_eq_add_Ico _ hm, Finset.sum_Ico_eq_sum_range]
    congrm $(by simp) + ?_
    trans ∑ k ∈ range (m - 1), (if k + 1 < m then (1 : M) else 0) • X ^ ((i + 1) * (k + 1))
    · apply Finset.sum_congr rfl
      intro b hb
      rw [add_comm 1 b]
      have : b + 1 < m := by grind
      simp [this]
    · refine (tsum_eq_sum ?_).symm
      exact fun b hb ↦ smul_eq_zero_of_left (by simpa using hb) _
  · simp_rw [genFun, countRestricted, Finset.card_filter, Finset.prod_boole]
    simp

variable (M : Type*) [CommRing M]

variable {M} in
theorem geom_series_mul_neg' [TopologicalSpace M] [T2Space M]
    [IsTopologicalRing M] {x : M⟦X⟧} (hx : x.order ≠ 0) :
    (∑' (j : ℕ), x ^ j) * (1 - x) = 1 := by
  have horder (n : ℕ) : ∀ d ≥ n + 1, ↑n < (x ^ d).order := by
    intro d hd
    refine ((ENat.coe_lt_coe.mpr (Nat.add_one_le_iff.mp hd.le)).trans_le ?_).trans_le
      (le_order_pow _ _)
    rw [nsmul_eq_mul]
    exact ENat.self_le_mul_right _ hx
  have : Summable (x ^ ·) := by
    apply WithPiTopology.summable_of_tendsto_order_atTop_nhds_top
    exact ENat.tendsto_nhds_top_iff_natCast_lt.mpr
      (fun n ↦ Filter.eventually_atTop.mpr ⟨n + 1, horder n⟩)
  have := this.hasSum.mul_right (1 - x)
  refine tendsto_nhds_unique this.tendsto_sum_nat ?_
  simp_rw [← Finset.sum_mul, geom_sum_mul_neg]
  rw [show nhds (1 : M⟦X⟧) = nhds (1 - 0) by simp]
  apply Filter.Tendsto.const_sub
  rw [WithPiTopology.tendsto_iff_coeff_tendsto]
  intro d
  refine tendsto_atTop_of_eventually_const fun n (hn : n ≥ (d + 1)) ↦ ?_
  rw [map_zero]
  apply PowerSeries.coeff_of_lt_order
  apply horder d _ hn

theorem aux_mul_euler [TopologicalSpace M] [T2Space M] [Nontrivial M]
    [IsTopologicalRing M] [NoZeroDivisors M] {m : ℕ} (hm : 0 < m) :
    ((∏' (i : ℕ), if ¬m ∣ i + 1 then ∑' (j : ℕ), X ^ ((i + 1) * j) else 1) *
    ∏' (i : ℕ), (1 - X ^ (i + 1)) : M⟦X⟧) =
    ∏' (i : ℕ), (1 - X ^ ((i + 1) * m)) := by
  rw [← Multipliable.tprod_mul (hasProd_powerSeriesMk_restricted M (¬ m ∣ ·)).multipliable
    (multipliable_pentagonalLhs_powerSeries _)]
  simp_rw [ite_not, ite_mul, pow_mul]
  conv in fun b ↦ _ =>
    ext b
    rw [geom_series_mul_neg' (by simp)]
  apply tprod_eq_tprod_of_ne_one_bij (fun i ↦ (i.val + 1) * m - 1)
  · intro a b h
    rw [tsub_left_inj (by nlinarith) (by nlinarith)] at h
    rw [mul_left_inj' (hm.ne.symm), add_left_inj] at h
    exact SetCoe.ext h
  · suffices ∀ (i : ℕ), m ∣ i + 1 → ∃ a, (a + 1) * m - 1 = i by simpa
    intro i hi
    obtain ⟨j, hj⟩ := dvd_def.mp hi
    use j - 1
    apply Nat.sub_eq_of_eq_add
    rw [hj, mul_comm m j]
    rw [Nat.sub_add_cancel (by grind)]
  · intro i
    have : (i + 1) * m - 1 + 1 = (i + 1) * m := Nat.sub_add_cancel (by nlinarith)
    simp [this, pow_mul]

theorem powerSeries_eq [TopologicalSpace M] [T2Space M] [Nontrivial M]
    [IsTopologicalRing M] [NoZeroDivisors M] {m : ℕ} (hm : 0 < m) :
    (∏' i, if ¬ m ∣ i + 1 then ∑' j : ℕ, X ^ ((i + 1) * j) else 1 : M⟦X⟧) =
    ∏' i, ∑ j ∈ Finset.range m, X ^ ((i + 1) * j) := by
  have : ∏' i, (1 - X ^ (i + 1)) ≠ (0 : M⟦X⟧) := by
    by_contra! h
    obtain h := PowerSeries.ext_iff.mp h 0
    rw [coeff_zero_eq_constantCoeff] at h
    rw [Multipliable.map_tprod (multipliable_pentagonalLhs_powerSeries _) _
      (WithPiTopology.continuous_constantCoeff M)] at h
    simp at h
  apply mul_right_cancel₀ this
  apply (aux_mul_euler M hm).trans
  rw [← Multipliable.tprod_mul (hasProd_powerSeriesMk_countRestricted M hm).multipliable
    (multipliable_pentagonalLhs_powerSeries _)]
  refine tprod_congr (fun i ↦ ?_)
  simp_rw [pow_mul, geom_sum_mul_neg]

theorem aux_glaisher_theorem [Nontrivial M] [NoZeroDivisors M] {m : ℕ} (hm : 0 < m) :
    PowerSeries.mk (fun n ↦ (#(restricted n (¬ m ∣ ·)) : M)) =
    PowerSeries.mk (fun n ↦ (#(countRestricted n m) : M)) := by
  let _ : TopologicalSpace M := ⊥
  have _ : DiscreteTopology M := ⟨rfl⟩
  obtain h1 := (hasProd_powerSeriesMk_restricted M (¬ m ∣ ·)).tprod_eq
  obtain h2 := (hasProd_powerSeriesMk_countRestricted M hm).tprod_eq
  exact (h1.symm.trans (powerSeries_eq M hm)).trans h2

theorem glaisher_theorem (n : ℕ) {m : ℕ} (hm : 0 < m) :
    #(restricted n (¬ m ∣ ·)) = #(countRestricted n m) := by
  simpa using (PowerSeries.ext_iff.mp (aux_glaisher_theorem ℤ hm)) n

theorem aux_mul_euler_unrestricted [TopologicalSpace M] [T2Space M] [Nontrivial M]
    [IsTopologicalRing M] [NoZeroDivisors M] :
    (PowerSeries.mk fun n ↦ (Fintype.card n.Partition : M)) * ∏' i : ℕ, (1 - X ^ (i + 1)) = 1 := by
  rw [← (hasProd_powerSeriesMk_partition M).tprod_eq]
  rw [← Multipliable.tprod_mul (hasProd_powerSeriesMk_partition M).multipliable
    (multipliable_pentagonalLhs_powerSeries _)]
  simp [pow_mul, geom_series_mul_neg']

def kSet (n : ℤ) : Finset ℤ :=
  Finset.Icc (-(((1 + 24 * n).sqrt - 1) / 6)) (((1 + 24 * n).sqrt + 1) / 6)

theorem mem_kSet_iff {n k : ℤ} :
    k ∈ kSet n ↔ k * (3 * k - 1) / 2 ≤ n := by
  obtain hneg | hpos := lt_or_ge n 0
  · trans False
    · simp only [kSet, Finset.mem_Icc, iff_false]
      by_contra! h
      obtain h' := h.1.trans h.2
      have : (1 + 24 * n).toNat = 0 := by
        simp only [Int.toNat_eq_zero]
        linarith
      simp [Int.sqrt, this] at h'
    · simp only [false_iff, not_le]
      exact hneg.trans_le (pentagonal_nonneg k)
  symm
  calc
    k * (3 * k - 1) / 2 ≤ n ↔ 12 * (2 * (k * (3 * k - 1) / 2)) ≤ 24 * n := by
      rw [← mul_assoc]
      norm_num
    _ ↔ 36 * k ^ 2 - 12 * k ≤ 24 * n := by
      rw [two_pentagonal]
      ring_nf
    _ ↔ 36 * k ^ 2 - 12 * k + 1 ≤ 24 * n + 1 := (Int.add_le_add_iff_right 1).symm
    _ ↔ (6 * k - 1) ^ 2 ≤ 1 + 24 * n := by ring_nf
    _ ↔ |6 * k - 1| ≤ (1 + 24 * n).sqrt := (Int.abs_le_sqrt_iff_sq_le (by linarith)).symm
    _ ↔ -(1 + 24 * n).sqrt ≤ 6 * k - 1 ∧ 6 * k - 1 ≤ (1 + 24 * n).sqrt := abs_le
    _ ↔ (-k) * 6 ≤ (1 + 24 * n).sqrt - 1 ∧ k * 6 ≤ (1 + 24 * n).sqrt + 1 := by
      grind
    _ ↔ -k ≤ ((1 + 24 * n).sqrt - 1) / 6 ∧ k ≤ ((1 + 24 * n).sqrt + 1) / 6 := by
      rw [Int.le_ediv_iff_mul_le (by simp)]
      rw [Int.le_ediv_iff_mul_le (by simp)]
    _ ↔ - (((1 + 24 * n).sqrt - 1) / 6) ≤ k ∧ k ≤ ((1 + 24 * n).sqrt + 1) / 6 := by
      grind
    _ ↔ k ∈ kSet n := by
      simp [kSet]


/--
The recurrence relation of (non-distinct) partition function $p(n)$:

$$\sum_{k \in \mathbb{Z}} (-1)^k p(n - k(3k-1)/2) = 0 \quad (n > 0)$$

Note that this is a finite sum, as the term for $k$ outside $n - k(3k-1)/2 ≥ 0$ vanishes.
Here we explicitly restrict the set of $k$.
-/
theorem sum_partition (n : ℕ) (hn : n ≠ 0) :
    ∑ k ∈ kSet n, (Int.negOnePow k) *
    (Fintype.card (Nat.Partition (n - (k * (3 * k - 1) / 2).toNat)) : ℤ) = 0 := by
  convert PowerSeries.ext_iff.mp (aux_mul_euler_unrestricted ℤ) n
  · rw [coeff_mul, pentagonalNumberTheorem_intPos_powerSeries]
    conv in fun (_: ℕ × ℕ) ↦ _ =>
      ext _
      rw [(summable_pentagonalRhs_intPos_powerSeries _).map_tsum _
        (WithPiTopology.continuous_coeff _ _)]
    simp_rw [← zsmul_eq_mul, coeff_smul]
    refine Finset.sum_of_injOn (fun k ↦ (n - (k * (3 * k - 1) / 2).toNat,
      (k * (3 * k - 1) / 2).toNat)) ?_ ?_ ?_ ?_
    · intro k hk l hl h
      obtain h := (Prod.ext_iff.mp h).2
      simp only at h
      exact pentagonal_toNat_injective h
    · intro k hk
      simp only [mem_coe, mem_antidiagonal]
      rw [Nat.sub_add_cancel ?_]
      suffices k * (3 * k - 1) / 2 ≤ (n : ℤ) by simpa
      rw [← mem_kSet_iff]
      simpa using hk
    · intro i hi hmem
      rw [mem_antidiagonal] at hi
      apply mul_eq_zero_of_right
      convert tsum_zero with k
      suffices i.2 ≠ (k * (3 * k - 1) / 2).toNat by
        simp [coeff_X_pow, this]
      contrapose! hmem with hi2
      simp_rw [Set.mem_image, mem_coe]
      refine ⟨k, mem_kSet_iff.mpr ?_, ?_⟩
      · rw [← hi, hi2]
        simp [pentagonal_nonneg]
      · simp [← hi, ← hi2]
    · intro k hk
      rw [tsum_eq_single k ?_]
      · simp [mul_comm (k.negOnePow : ℤ)]
      intro i h
      simpa [coeff_X_pow] using pentagonal_toNat_injective.eq_iff.ne.mpr h.symm
  · simp [hn]

end Nat.Partition
