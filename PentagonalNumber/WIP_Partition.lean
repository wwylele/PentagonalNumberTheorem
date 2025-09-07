
import Mathlib

/-!

This is a WIP file where I attempt to build a better framework for partition functions.

-/

namespace Nat
namespace Partition

open PowerSeries Finset
open scoped PowerSeries.WithPiTopology

variable {M : Type*} [CommSemiring M]

-- Character function f : (part : ℕ+) → (count : ℕ) → (value : M)

noncomputable
def genFun (f : ℕ+ → ℕ → M) : M⟦X⟧ :=
  PowerSeries.mk fun n ↦ ∑ p : n.Partition, ∏ᶠ i : ℕ+, f i (p.parts.count i.val)

namespace Multiset
@[simp]
lemma mem_sum'' {α ι : Type*} {a : α} {s : Finset ι} {m : ι → Multiset α} :
    a ∈ ∑ i ∈ s, m i ↔ ∃ i ∈ s, a ∈ m i := by
  induction s using Finset.cons_induction <;> simp [*]

end Multiset

namespace PNat

def embedNat : ℕ+ ↪ ℕ := Function.Embedding.subtype _

@[simp]
theorem embedNat_apply (a : ℕ+) : embedNat a = ↑a := rfl

end PNat

theorem hasProd_genFun [TopologicalSpace M]
    {f : ℕ+ → ℕ → M} (h : (Function.mulSupport (f · 0)).Finite) :
    HasProd (fun (i : ℕ+) ↦ PowerSeries.mk fun n ↦
      if i.val ∣ n then f i (n / i) else 0) (genFun f) := by
  unfold HasProd
  rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro n
  apply tendsto_atTop_of_eventually_const
  show ∀ s ≥ Finset.Icc 1 n.toPNat' ∪ h.toFinset, _
  intro s hs
  rw [genFun]
  rw [PowerSeries.coeff_prod]
  simp_rw [coeff_mk]
  simp_rw [Finset.prod_ite_zero]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]

  let u (x : ℕ+ →₀ ℕ) (hx : x ∈ (s.finsuppAntidiag n).filter (fun x ↦ ∀ i ∈ s, i.val ∣ x i)) :
      n.Partition := {
    parts := x.sum (fun n s ↦ Multiset.replicate (s / n) n)
    parts_pos := by
      intro a ha
      unfold Finsupp.sum at ha
      simp only [Multiset.mem_sum'', Finsupp.mem_support_iff, ne_eq, Multiset.mem_replicate,
        Nat.div_eq_zero_iff, PNat.ne_zero, false_or, not_lt] at ha
      obtain ⟨b, hb0, hb, rfl⟩ := ha
      simp
    parts_sum := by
      unfold Finsupp.sum
      rw [Multiset.sum_sum]
      simp_rw [Multiset.sum_replicate, smul_eq_mul]
      simp only [Finset.mem_filter, Finset.mem_finsuppAntidiag] at hx
      obtain ⟨⟨hsum, hsupport⟩, hdvd⟩ := hx
      rw [Finset.sum_subset hsupport (by
        simp
        suffices ∀ a ∈ s, x a = 0 → x a < a by simpa
        intro a _ ha
        simp [ha]
      )]
      rw [← hsum]
      apply Finset.sum_congr rfl
      intro a ha
      exact Nat.div_mul_cancel (hdvd a ha)
  }

  let v (x : n.Partition) (_ : x ∈ Finset.univ) : ℕ+ →₀ ℕ := Finsupp.mk
    (x.parts.map Nat.toPNat').toFinset (fun n ↦ x.parts.count n.val * n) (by
      intro n
      suffices (∃ a ∈ x.parts, a.toPNat' = n) ↔ n.val ∈ x.parts by simpa
      constructor
      · rintro ⟨a, ha, rfl⟩
        simpa [x.parts_pos ha] using ha
      · intro hn
        use n.val
        simpa using hn
    )

  refine Finset.sum_bij' u v (by simp) ?_ ?_ ?_ ?_
  · intro x _
    suffices ∑ i ∈ s, x.parts.count i.val * i = n ∧ (x.parts.map toPNat').toFinset ⊆ s by simpa [v]
    constructor
    · simp_rw [← x.parts_sum]
      rw [Finset.sum_multiset_count]
      simp_rw [smul_eq_mul]
      have : ∑ i ∈ s, Multiset.count i.val x.parts * i
          = ∑ i ∈ s.map PNat.embedNat, Multiset.count i x.parts * i :=
        (Finset.sum_map s PNat.embedNat fun i ↦ Multiset.count i x.parts * i).symm
      rw [this]
      refine (Finset.sum_subset ?_ (by simp)).symm
      intro i hi
      rw [Multiset.mem_toFinset] at hi
      suffices ∃ i' ∈ s, i' = i by simpa
      use i.toPNat'
      constructor
      · apply Finset.mem_of_subset hs
        rw [Finset.mem_union]
        left
        suffices i.toPNat' ≤ n.toPNat' by simpa
        suffices i ≤ n by -- Extract this
          obtain rfl | hx0 := Nat.eq_zero_or_pos i
          · simp
          · apply (PNat.coe_le_coe _ _).mp
            simpa [hx0, hx0.trans_le this] using this
        rw [← x.parts_sum]
        exact Multiset.le_sum_of_mem hi
      · simp [x.parts_pos hi]
    · refine Finset.Subset.trans (Finset.Subset.trans ?_ Finset.subset_union_left) hs
      intro i
      suffices ∀ i' ∈ x.parts, i'.toPNat' = i → i ≤ n.toPNat' by simpa
      intro i' hi' hi
      rw [← hi]
      suffices i' ≤ n by -- Extract this
        obtain rfl | hx0 := Nat.eq_zero_or_pos i'
        · simp
        · apply (PNat.coe_le_coe _ _).mp
          simpa [hx0, hx0.trans_le this] using this
      rw [← x.parts_sum]
      exact Multiset.le_sum_of_mem hi'
  · intro x hx
    ext i
    suffices Multiset.count i.val (x.sum fun n s ↦ Multiset.replicate (s / n) n.val) * i = x i by
      simpa [u, v]
    unfold Finsupp.sum
    simp_rw [Multiset.count_sum', Multiset.count_replicate]
    simp_rw [PNat.coe_inj, Finset.sum_ite_eq', Finsupp.mem_support_iff]
    split_ifs with h
    · rw [Finset.mem_filter, Finset.mem_finsuppAntidiag] at hx
      obtain ⟨⟨hsum, hsupp⟩, hdvd⟩ := hx
      apply Nat.div_mul_cancel
      apply hdvd
      apply Finset.mem_of_subset hsupp
      simpa using h
    · rw [not_not] at h
      simp [h]
  · intro x hx
    ext i
    suffices Multiset.count i ((v x hx).sum fun n s ↦ Multiset.replicate (s / n) n) =
      Multiset.count i x.parts by simpa [u]
    unfold Finsupp.sum
    simp_rw [Multiset.count_sum', Multiset.count_replicate]
    obtain rfl | hi := Nat.eq_zero_or_pos i
    · symm
      suffices 0 ∉ x.parts by simpa
      obtain h := x.parts_pos
      contrapose! h
      exact ⟨h, le_refl _⟩
    rw [show i = i.toPNat' by simp [hi]]
    simp_rw [PNat.coe_inj, Finset.sum_ite_eq', Finsupp.mem_support_iff]
    suffices (i ∈ x.parts → i = 0) → 0 = Multiset.count i x.parts by simpa [v, hi]
    intro h
    refine (Multiset.count_eq_zero.mpr ?_).symm
    contrapose! h
    exact ⟨h, Nat.ne_zero_of_lt <| x.parts_pos h⟩
  · intro x hx
    simp [u]
    unfold Finsupp.sum
    simp_rw [Multiset.count_sum', Multiset.count_replicate]
    simp_rw [PNat.coe_inj, Finset.sum_ite_eq', Finsupp.mem_support_iff]
    have (i : ℕ+) : (if x i ≠ 0 then x i / i else 0) = x i / i.val := by
      suffices x i = 0 → 0 = x i / i by simpa
      intro h
      simp [h]
    simp_rw [this]
    refine (finprod_eq_finset_prod_of_mulSupport_subset _ ?_).symm
    rw [Finset.mem_filter, Finset.mem_finsuppAntidiag] at hx
    obtain ⟨⟨hsum, hsupp⟩, hdvd⟩ := hx
    intro a ha
    by_cases h : x a / a = 0
    · apply Set.mem_of_subset_of_mem (Finset.coe_subset.mpr hs)
      rw [Function.mem_mulSupport] at ha
      suffices a ≤ n.toPNat' ∨ f a 0 ≠ 1 by simpa
      rw [h] at ha
      exact Or.inr ha
    apply Set.mem_of_subset_of_mem (Finset.coe_subset.mpr hsupp)
    contrapose! h
    have : x a = 0 := by simpa using h
    simp [this]

theorem finite_mulSupport_mul {f g : ℕ+ → ℕ → M}
    (hf : (Function.mulSupport (f · 0)).Finite) (hg : (Function.mulSupport (g · 0)).Finite) :
    (Function.mulSupport (
      (fun i c ↦ ∑ j ∈ Finset.antidiagonal c, f i j.1 * g i j.2) · 0)).Finite := by
  simpa using Set.Finite.subset (hf.union hg) (Function.mulSupport_mul (f · 0) (g · 0))

theorem genFun_mul_genFun {f g : ℕ+ → ℕ → M}
    (hf : (Function.mulSupport (f · 0)).Finite) (hg : (Function.mulSupport (g · 0)).Finite) :
    genFun f * genFun g = genFun fun i c ↦ ∑ j ∈ Finset.antidiagonal c, f i j.1 * g i j.2 := by
  let _ : TopologicalSpace M := ⊥
  let _ : DiscreteTopology M := forall_open_iff_discrete.mp fun s ↦ trivial
  let fg := fun i c ↦ ∑ j ∈ Finset.antidiagonal c, f i j.1 * g i j.2
  have hfg : (Function.mulSupport (fg · 0)).Finite := finite_mulSupport_mul hf hg

  have hfgprod := (hasProd_genFun hfg).tprod_eq
  have hprod := ((hasProd_genFun hf).mul (hasProd_genFun hg)).tprod_eq
  refine (hprod.symm.trans ?_).trans hfgprod
  refine tprod_congr fun i ↦ ?_
  ext n
  suffices ∑ x ∈ antidiagonal n with ↑i ∣ x.2 ∧ ↑i ∣ x.1, f i (x.1 / i) * g i (x.2 / i) =
      if ↑i ∣ n then ∑ j ∈ antidiagonal (n / i), f i j.1 * g i j.2 else 0 by
    simpa [coeff_mul, fg, Finset.sum_ite, Finset.filter_filter]
  split_ifs with h
  · refine Finset.sum_nbij' (fun x ↦ x / (i.val, i.val)) (fun x ↦ x * (i.val, i.val)) ?_ ?_ ?_
      (by simp) (by simp)
    · suffices ∀ (a b : ℕ), a + b = n → ↑i ∣ b → ↑i ∣ a → a / ↑i + b / ↑i = n / ↑i by simpa
      intro a b h ha hb
      exact h.symm ▸ (Nat.add_div_of_dvd_left ha).symm
    · suffices ∀ (a b : ℕ), a + b = n / ↑i → a * ↑i + b * ↑i = n by simpa
      intro a b hab
      rw [← add_mul, hab]
      exact Nat.div_mul_cancel h
    · suffices ∀ (a b : ℕ), a + b = n → ↑i ∣ b → ↑i ∣ a → a / ↑i * ↑i = a ∧ b / ↑i * ↑i = b by simpa
      intro a b _ hb ha
      exact ⟨Nat.div_mul_cancel ha, Nat.div_mul_cancel hb⟩
  · apply Finset.sum_eq_zero
    intro x hx
    contrapose! hx
    contrapose! h
    obtain ⟨rfl, h1, h2⟩ : x.1 + x.2 = n ∧ ↑i ∣ x.2 ∧ ↑i ∣ x.1 := by simpa using h
    exact (Nat.dvd_add_iff_right h2).mp h1


theorem hasProd_genFun' [TopologicalSpace M] [T2Space M]
    {f : ℕ+ → ℕ → M} (h : (Function.mulSupport (f · 0)).Finite) :
    HasProd (fun i ↦ ∑' c : ℕ, f i c • X ^ (c * i)) (genFun f) := by
  convert hasProd_genFun h with i
  apply HasSum.tsum_eq
  unfold HasSum
  rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro n
  apply tendsto_atTop_of_eventually_const
  show ∀ s ≥ Finset.range (n + 1), _
  intro s hs
  suffices ∑ x ∈ s with n = x * i, f i x = if i.val ∣ n then f i (n / i) else 0 by
    simpa [PowerSeries.coeff_X_pow, Finset.sum_ite]
  split_ifs with h
  · convert Finset.sum_singleton _ _
    ext x
    suffices x ∈ s ∧ n = x * i ↔ x = n / i by simpa
    rw [Nat.eq_div_iff_mul_eq_left (by simp) h]
    suffices n = x * i → x ∈ s by simpa
    intro hxi
    refine Finset.mem_of_subset hs (Finset.mem_range.mpr ?_)
    apply Nat.lt_add_one_of_le
    rw [hxi]
    exact Nat.le_mul_of_pos_right x (by simp)
  · convert Finset.sum_empty
    rw [Finset.eq_empty_iff_forall_notMem]
    contrapose! h
    obtain ⟨x, hx⟩ := h
    rw [Finset.mem_filter, mul_comm] at hx
    exact ⟨x, hx.2⟩

theorem genFun_eq [TopologicalSpace M] [T2Space M]
    {f : ℕ+ → ℕ → M} (h : (Function.mulSupport (f · 0)).Finite) :
    genFun f = ∏' i : ℕ+, ∑' c : ℕ, f i c • X ^ (c * i) :=
  (hasProd_genFun' h).tprod_eq.symm

def restricted (n : ℕ) (p : ℕ → Prop) [DecidablePred p] : Finset (n.Partition) :=
  Finset.univ.filter fun x ↦ ∀ i ∈ x.parts, p i

def countRestricted (n : ℕ) (m : ℕ) : Finset (n.Partition) :=
  Finset.univ.filter fun x ↦ ∀ i ∈ x.parts, x.parts.count i < m


variable {M : Type*} [CommRing M]

theorem powerSeriesMk_card_restricted [Nontrivial M] (p : ℕ → Prop) [DecidablePred p] :
    PowerSeries.mk (fun n ↦ (#(restricted n p) : M)) =
    (genFun fun i c ↦ if c = 0 ∨ p i then 1 else 0) := by
  apply PowerSeries.ext
  intro n
  unfold genFun restricted
  simp_rw [coeff_mk]
  rw [← Finset.sum_boole]
  simp_rw [Multiset.count_eq_zero]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  split_ifs with h
  · have (i : ℕ+) : i.val ∉ x.parts ∨ p i := not_or_of_imp (by simpa using h i)
    simp [this]
  · simp only [not_forall] at h
    obtain ⟨i, hi, his⟩ := h
    have : i.toPNat' = i := by simp [x.parts_pos hi]
    have : ¬ (i.toPNat'.val ∉ x.parts ∨ p i.toPNat') := by
      rw [this]
      simpa using ⟨hi, his⟩
    refine (finprod_eq_zero _ i.toPNat' (by simp only [this, ↓reduceIte]) ?_).symm
    suffices ({i : ℕ+ | i.val ∈ x.parts} ∩ {i | ¬ p i}).Finite by simpa [Function.mulSupport]
    suffices {i : ℕ+ | i.val ∈ x.parts}.Finite by exact this.subset (by simp)
    suffices (((↑) : ℕ+ → ℕ) ⁻¹' x.parts.toFinset).Finite by
      convert this
      ext
      simp
    exact Set.Finite.preimage (by simp) (by simp)

theorem powerSeriesMk_card_countRestricted [Nontrivial M] {m : ℕ} (hm : 0 < m) :
    PowerSeries.mk (fun n ↦ (#(countRestricted n m) : M)) =
    (genFun fun _ c ↦ if c < m then 1 else 0) := by
  apply PowerSeries.ext
  intro n
  unfold genFun countRestricted
  simp_rw [coeff_mk]
  rw [← Finset.sum_boole]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  split_ifs with h
  · have (i : ℕ+) : Multiset.count (↑i) x.parts < m := by
      by_cases hi : i.val ∈ x.parts
      · exact h i hi
      · exact Multiset.count_eq_zero.mpr hi ▸ hm
    simp [this]
  · simp only [not_forall] at h
    obtain ⟨i, hi, his⟩ := h
    have : i.toPNat' = i := by simp [x.parts_pos hi]
    have : ¬ Multiset.count (↑i.toPNat') x.parts < m := by
      rw [this]
      simpa using his
    refine (finprod_eq_zero _ i.toPNat' (by simp only [this, ↓reduceIte]) ?_).symm
    suffices (((↑) : ℕ+ → ℕ) ⁻¹' {i : ℕ | m ≤ Multiset.count i x.parts}).Finite by
      convert this
      ext
      simp
    apply Set.Finite.preimage (by simp)
    suffices {i : ℕ | 0 < Multiset.count i x.parts}.Finite by
      apply this.subset
      intro i hi
      have hi : m ≤ Multiset.count i x.parts := by simpa using hi
      simpa using hm.trans_le hi
    suffices Set.Finite x.parts.toFinset.toSet by
      convert this
      ext
      simp [Nat.pos_iff_ne_zero]
    simp

variable (M) in
noncomputable
def eulerPhi : M⟦X⟧ := genFun fun _ c ↦ if c = 0 then 1 else if c = 1 then -1 else 0

theorem hasProd_eulerPhi [TopologicalSpace M] [T2Space M] :
    HasProd (fun (n : ℕ+) ↦ (1 - X ^ n.val)) (eulerPhi M) := by
  obtain h : HasProd _ (eulerPhi M) := hasProd_genFun' (by simp)
  convert h with n
  simp_rw [ite_smul]
  rw [tsum_eq_sum (show ∀ n ∉ {0, 1}, _ by
    intro n hn
    obtain ⟨h0, h1⟩ : n ≠ 0 ∧ n ≠ 1 := by simpa using hn
    simp [h0, h1]
  )]
  simp [← sub_eq_add_neg]

theorem powerSeriesMk_card_restricted_mul_eulerPhi [Nontrivial M] (p : ℕ → Prop) [DecidablePred p] :
    PowerSeries.mk (fun n ↦ (#(restricted n p) : M)) * eulerPhi M =
    genFun (fun i c ↦ if p i
      then if c = 0 then 1 else 0
      else if c = 0 then 1 else if c = 1 then -1 else 0) := by
  rw [powerSeriesMk_card_restricted, eulerPhi]
  rw [genFun_mul_genFun (by simp) (by simp)]
  apply congrArg
  ext i c
  split_ifs with hc hi hi hi2
  · simp [hi]
  · rw [← Finset.Nat.sum_antidiagonal_swap, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    have hc' : 0 < c := zero_lt_of_ne_zero hi
    simp [Finset.sum_ite, hc, hc']
  · simp [hi]
  · rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp [Finset.sum_ite, hc, hi2]
  · rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp [Finset.sum_ite, hc, hi, hi2]

theorem hasProd_powerSeriesMk_card_restricted_mul_eulerPhi [Nontrivial M] [TopologicalSpace M]
    (p : ℕ → Prop) [DecidablePred p] :
    HasProd (fun (i : {i : ℕ+ // ¬ p i}) ↦ 1 - X ^ i.val.val)
    (PowerSeries.mk (fun n ↦ (#(restricted n p) : M)) * eulerPhi M) := by
  rw [powerSeriesMk_card_restricted_mul_eulerPhi]
  let j := (fun (i : ℕ+) c ↦ if p i
      then if c = 0 then (1 : M) else 0
      else if c = 0 then 1 else if c = 1 then -1 else 0)
  obtain hprod := hasProd_genFun (show (Function.mulSupport (j · 0)).Finite by simp [j])

  let g := fun (i : {i : ℕ+ // ¬ p i}) ↦ i.val
  let f := (fun (i : ℕ+) ↦ if p i then (1 : M⟦X⟧) else 1 - X ^ i.val)
  have hf : ∀ x ∉ Set.range g, f x = 1 := by
    simp [f, g]
    grind
  have : (fun (i : {i : ℕ+ // ¬ p i}) ↦ (1 : M⟦X⟧) - X ^ i.val.val) = f ∘ g := by
    ext
    grind
  rw [this]
  rw [Function.Injective.hasProd_iff (by simp [g]) hf]
  convert hprod with i
  ext m
  by_cases hp : p i
  · by_cases hm : m = 0
    · simp [f, j, hp, hm]
    · suffices ↑i ∣ m → ↑i ≤ m by simpa [f, j, hp, hm]
      apply Nat.le_of_dvd <| zero_lt_of_ne_zero hm
  · by_cases hm : m = 0
    · simp [f, j, hp, hm]
    · by_cases hm' : m = i
      · simp [f, j, hp, hm']
      · suffices ↑i ∣ m → (0 : M) = if m < ↑i then 1 else if m / ↑i = 1 then -1 else 0 by
          simpa [f, j, hp, hm, PowerSeries.coeff_X_pow, hm']
        intro him
        have h1 : ¬ m < ↑i := by simpa using Nat.le_of_dvd (zero_lt_of_ne_zero hm) him
        have h2 : ¬ m / ↑i = 1 := by
          contrapose! hm'
          exact (Nat.eq_of_dvd_of_div_eq_one him hm').symm
        simp [h1, h2]


theorem powerSeriesMk_card_countRestricted_mul_eulerPhi [Nontrivial M] {m : ℕ} (hm : 0 < m) :
    PowerSeries.mk (fun n ↦ (#(countRestricted n m) : M)) * eulerPhi M =
    genFun (fun _ c ↦ if c = 0 then 1 else if c = m then -1 else 0) := by
  rw [powerSeriesMk_card_countRestricted hm, eulerPhi]
  rw [genFun_mul_genFun (by simp [hm]) (by simp)]
  apply congrArg
  ext i c
  split_ifs with hc hcm
  · simp [hc, hm]
  · rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    suffices (#({x ∈ {x ∈ range (m + 1) | m - x = 0} | x < m}) : M) +
        -#({x ∈ {x ∈ {x ∈ range (m + 1) | ¬m - x = 0} | m - x = 1} | x < m}) = -1 by
      simpa [hcm, Finset.sum_ite]
    have h1 : {x ∈ {x ∈ range (m + 1) | m - x = 0} | x < m} = {} := by grind
    have h2 : {x ∈ {x ∈ {x ∈ range (m + 1) | ¬m - x = 0} | m - x = 1} | x < m} = {m - 1} := by
      grind
    simp [h1, h2]
  · rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    suffices (#({x ∈ {x ∈ range (c + 1) | c - x = 0} | x < m}) : M) +
        -(#({x ∈ {x ∈ {x ∈ range (c + 1) | ¬c - x = 0} | c - x = 1} | x < m})) = 0 by
      simpa [Finset.sum_ite]
    obtain h | h := lt_or_gt_of_ne hcm
    · have h1 : {x ∈ {x ∈ range (c + 1) | c - x = 0} | x < m} = {c} := by grind
      have h2 : {x ∈ {x ∈ {x ∈ range (c + 1) | ¬c - x = 0} | c - x = 1} | x < m} = {c - 1} := by
        grind
      simp [h1, h2]
    · have h1 : {x ∈ {x ∈ range (c + 1) | c - x = 0} | x < m} = {} := by grind
      have h2 : {x ∈ {x ∈ {x ∈ range (c + 1) | ¬c - x = 0} | c - x = 1} | x < m} = {} := by grind
      simp [h1, h2]

theorem hasProd_powerSeriesMk_card_countRestricted_mul_eulerPhi [Nontrivial M] [TopologicalSpace M]
    {m : ℕ} (hm : 0 < m) :
    HasProd (fun (i : ℕ+) ↦ 1 - X ^ (m * i.val))
    (PowerSeries.mk (fun n ↦ (#(countRestricted n m) : M)) * eulerPhi M) := by
  rw [powerSeriesMk_card_countRestricted_mul_eulerPhi hm]
  let j := (fun (_ : ℕ+) c ↦ if c = 0 then (1 : M) else if c = m then -1 else 0)
  obtain hprod := hasProd_genFun (show (Function.mulSupport (j · 0)).Finite by simp [j])
  convert hprod with i
  ext n
  by_cases hn : n = 0
  · simpa [j, hn] using Nat.ne_zero_of_lt hm
  · by_cases hn' : n = m * i
    · have hm : m ≠ 0 := by
        contrapose! hn with hm
        simp [hn', hm]
      simp [j, hm, hn']
    · suffices ↑i ∣ n → 0 = j i (n / ↑i) by simpa [hn, coeff_X_pow, hn']
      intro hi
      have h1 : ¬ n < ↑i := by simpa using Nat.le_of_dvd (zero_lt_of_ne_zero hn) hi
      have h2 : ¬ n / ↑i = m := by
        contrapose! hn'
        exact Nat.eq_mul_of_div_eq_left hi hn'
      simp [j, h1, h2]

theorem aux_mul_eulerPhi_eq [TopologicalSpace M] [T2Space M] [Nontrivial M] {m : ℕ} (hm : 0 < m) :
    PowerSeries.mk (fun n ↦ (#(restricted n (¬ m ∣ ·)) : M)) * eulerPhi M =
    PowerSeries.mk (fun n ↦ (#(countRestricted n m) : M)) * eulerPhi M := by
  refine (hasProd_powerSeriesMk_card_restricted_mul_eulerPhi _).tprod_eq.symm.trans ?_
  refine Eq.trans ?_ (hasProd_powerSeriesMk_card_countRestricted_mul_eulerPhi hm).tprod_eq
  let g (i : { i : ℕ+ // ¬¬m ∣ ↑i }) := (1 : M⟦X⟧) - X ^ i.val.val
  let f (i : ℕ+) := (1 : M⟦X⟧) - X ^ (m * i.val)
  change ∏' i, g i = ∏' i, f i
  let e : { i : ℕ+ // ¬¬m ∣ ↑i } ≃ ℕ+ := {
    toFun i := ⟨i.val.val / m,
      Nat.div_pos_iff.mpr ⟨hm,  Nat.le_of_dvd i.val.prop <| not_not.mp i.prop⟩⟩
    invFun i := ⟨i * ⟨m, hm⟩, by simp⟩
    left_inv i := by
      ext
      rw [← PNat.coe_inj]
      simpa using Nat.div_mul_cancel <| not_not.mp i.prop
    right_inv i := by
      rw [← PNat.coe_inj]
      simpa using Nat.mul_div_cancel i.val hm
  }
  have (i : { i : ℕ+ // ¬¬m ∣ ↑i }) : g i = f (e i) := by
    suffices m * (i.val.val / m) = i.val.val by simp [f, g, e, this]
    exact Nat.mul_div_cancel' <| not_not.mp i.prop
  simp_rw [this]
  apply Equiv.tprod_eq

theorem aux_eq [TopologicalSpace M] [T2Space M] [Nontrivial M] [NoZeroDivisors M]
    {m : ℕ} (hm : 0 < m) :
    PowerSeries.mk (fun n ↦ (#(restricted n (¬ m ∣ ·)) : M)) =
    PowerSeries.mk (fun n ↦ (#(countRestricted n m) : M)) := by
  obtain h := aux_mul_eulerPhi_eq (M := M) hm
  have : eulerPhi M ≠ 0 := by
    by_contra! h
    obtain h := PowerSeries.ext_iff.mp h 0
    simp [eulerPhi, genFun] at h
  apply mul_right_cancel₀ this h


end Partition
end Nat
