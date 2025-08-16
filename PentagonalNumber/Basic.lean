import Mathlib

open scoped PowerSeries.WithPiTopology

--theorem phi_multipliable: Multipliable
--  fun k ↦ (PowerSeries.C ℤ 1 - PowerSeries.monomial ℤ (k + 1) 1) := by


--noncomputable
--def phi : PowerSeries ℤ := ∏' k, (PowerSeries.C ℤ 1 - PowerSeries.monomial ℤ (k + 1) 1)


def pentagonal (k : ℤ) := k * (3 * k - 1) / 2

theorem two_pentagonal (k : ℤ) : 2 * pentagonal k = k * (3 * k - 1) := by
  unfold pentagonal
  refine Int.two_mul_ediv_two_of_even ?_
  obtain h | h := Int.even_or_odd k
  · exact Even.mul_right h (3 * k - 1)
  · refine Even.mul_left ?_ _
    refine Int.even_sub_one.mpr ?_
    refine Int.not_even_iff_odd.mpr ?_
    refine Odd.mul ?_ h
    decide


theorem pentagonal_nonneg (k : ℤ) : 0 ≤ pentagonal k := by
  suffices 0 ≤ 2 * pentagonal k by simpa
  rw [two_pentagonal]
  obtain h | h := lt_or_ge 0 k
  · exact mul_nonneg h.le (by linarith)
  · exact mul_nonneg_of_nonpos_of_nonpos h (by linarith)

theorem pentagonal_injective : Function.Injective pentagonal := by
  intro a b h
  have : a * (3 * a - 1) - b * (3 * b - 1) = 0 := by
    simp [← two_pentagonal, h]
  have : (3 * (a + b) - 1) * (a - b) = 0 := by
    rw [← this]
    ring
  obtain h | h := mul_eq_zero.mp this
  · obtain h' := Int.eq_of_mul_eq_one <| eq_of_sub_eq_zero h
    simp [← h'] at h
  · exact eq_of_sub_eq_zero h

def Δ (n : ℤ) := 1 + 24 * n

theorem Δ_pentagonal (k : ℤ) : Δ (pentagonal k) = (6 * k - 1) ^ 2 := by
  unfold Δ
  rw [show 24 * pentagonal k = 12 * (2 * pentagonal k) by ring]
  rw [two_pentagonal]
  ring

def phiCoeff (n : ℤ) : ℤ :=
  if IsSquare (Δ n) then
    if 6 ∣ 1 + (Δ n).sqrt then
      ((1 + (Δ n).sqrt) / 6).negOnePow
    else if 6 ∣ 1 - (Δ n).sqrt then
      ((1 - (Δ n).sqrt) / 6).negOnePow
    else
      0
  else
    0

theorem phiCoeff_pentagonal (k : ℤ) : phiCoeff (pentagonal k) = k.negOnePow := by
  rw [phiCoeff, Δ_pentagonal]
  have hsquare : IsSquare ((6 * k - 1) ^ 2) := IsSquare.sq _
  simp only [hsquare, ↓reduceIte]
  simp_rw [sq, Int.sqrt_eq]
  by_cases hk : 1 ≤ k
  · have habs : (6 * k - 1).natAbs = 6 * k - 1 := Int.natAbs_of_nonneg (by linarith)
    simp [habs]
  · have habs : (6 * k - 1).natAbs = -(6 * k - 1) := Int.ofNat_natAbs_of_nonpos (by linarith)
    suffices ¬ 6 ∣ 1 + (1 - 6 * k) by simp [habs, this]
    rw [show 1 + (1 - 6 * k) = 2 + 6 * (-k) by ring]
    simp [-mul_neg]

theorem phiCoeff_eq_zero_iff (n : ℤ) : phiCoeff n = 0 ↔ n ∉ Set.range pentagonal := by
  rw [phiCoeff]
  constructor
  · split_ifs with hsq h1 h2
    · simp
    · simp
    · intro _
      by_contra! hmem
      obtain ⟨k, h⟩ := hmem
      rw [← h, Δ_pentagonal, sq, Int.sqrt_eq] at h1 h2
      obtain h | h := le_total 0 (6 * k - 1)
      · rw [Int.natAbs_of_nonneg h] at h1
        simp at h1
      · rw [Int.ofNat_natAbs_of_nonpos h] at h2
        rw [show 1 - -(6 * k - 1) = 6 * k by ring] at h2
        simp at h2
    · intro _
      contrapose! hsq with hmem
      obtain ⟨k, h⟩ := hmem
      rw [← h, Δ_pentagonal]
      exact IsSquare.sq _
  · split_ifs with hsq h1 h2
    · intro h
      contrapose! h
      obtain ⟨a, ha⟩ := hsq
      rw [ha, Int.sqrt_eq, dvd_iff_exists_eq_mul_right] at h1
      obtain ⟨k, hk⟩ := h1
      have hk' : a.natAbs = 6 * k - 1 := eq_sub_iff_add_eq'.mpr hk
      rw [Δ, ← Int.natAbs_mul_self' a, hk'] at ha
      use k
      apply Int.eq_of_mul_eq_mul_left (show 24 ≠ 0 by simp)
      refine (eq_iff_eq_of_add_eq_add ?_).mp (show 1 = 1 by rfl)
      rw [show 24 * pentagonal k = 12 * (2 * pentagonal k) by ring, two_pentagonal, ha]
      ring
    · intro h
      contrapose! h
      obtain ⟨a, ha⟩ := hsq
      rw [ha, Int.sqrt_eq, dvd_iff_exists_eq_mul_right] at h2
      obtain ⟨k, hk⟩ := h2
      have hk' : a.natAbs = 1 - 6 * k := by linarith
      rw [Δ, ← Int.natAbs_mul_self' a, hk'] at ha
      use k
      apply Int.eq_of_mul_eq_mul_left (show 24 ≠ 0 by simp)
      refine (eq_iff_eq_of_add_eq_add ?_).mp (show 1 = 1 by rfl)
      rw [show 24 * pentagonal k = 12 * (2 * pentagonal k) by ring, two_pentagonal, ha]
      ring
    · simp
    · simp

def phi : PowerSeries ℤ := PowerSeries.mk (phiCoeff ·)

theorem hasSum_phi :
    HasSum (fun k ↦ PowerSeries.monomial ℤ (pentagonal k).toNat k.negOnePow) phi := by
  obtain h := PowerSeries.hasSum_of_monomials_self phi
  nth_rw 1 [phi] at h
  simp_rw [PowerSeries.coeff_mk] at h
  conv in fun k ↦ _ =>
    ext k
    rw [← phiCoeff_pentagonal]
    rw [show (phiCoeff (pentagonal k)) = (phiCoeff (pentagonal k).toNat) by
      apply congrArg
      refine Int.eq_natCast_toNat.mpr (pentagonal_nonneg _)
    ]
  have hinj : Function.Injective fun k ↦ (pentagonal k).toNat := by
    intro a b h
    apply_fun ((↑) : ℕ → ℤ) at h
    simp only at h
    rw [← Int.eq_natCast_toNat.mpr (pentagonal_nonneg a)] at h
    rw [← Int.eq_natCast_toNat.mpr (pentagonal_nonneg b)] at h
    apply pentagonal_injective h
  have hrange (x : ℕ) (hx : x ∉ Set.range fun k ↦ (pentagonal k).toNat) :
      PowerSeries.monomial ℤ x (phiCoeff x) = 0 := by
    have hx: (x : ℤ) ∉ Set.range pentagonal := by
      contrapose! hx
      obtain ⟨y, hy⟩ := hx
      use y
      simp [hy]
    simp [(phiCoeff_eq_zero_iff _).mpr hx]
  exact (Function.Injective.hasSum_iff hinj hrange).mpr h


def partitions (n : ℕ) : Finset (Finset ℕ) :=
    (Finset.Icc 1 n).powerset.filter fun s ↦ s.sum id = n

def phiCoeff' (n : ℕ) := (partitions n).sum fun s ↦ (-1) ^ s.card

#eval (List.range 15).map phiCoeff
#eval (List.range 15).map phiCoeff'

def Nat.DistinctPartition (n : ℕ) : Type := Nat.Partition.distincts n

namespace Nat.DistinctPartition

variable {n : ℕ}

def parts (x : Nat.DistinctPartition n) := Finset.mk x.val.parts (Finset.mem_filter.mp x.prop).2

theorem parts_pos (x : Nat.DistinctPartition n) {i : ℕ} (h : i ∈ x.parts) : 0 < i := by
  apply x.val.parts_pos
  simpa using h

theorem parts_sum (x : Nat.DistinctPartition n) : x.parts.sum id = n := by
  rw [Finset.sum_eq_multiset_sum, Multiset.map_id x.parts.val]
  exact x.val.parts_sum

theorem ext {x y : Nat.DistinctPartition n} (parts : x.parts = y.parts) : x = y := by
  unfold Nat.DistinctPartition.parts at parts
  apply Subtype.ext_val
  apply Nat.Partition.ext
  simpa using parts

end Nat.DistinctPartition

theorem List.zipIdx_set {α : Type*} (l : List α) (nset : ℕ) (a : α) (nzip : ℕ) :
    (l.set nset a).zipIdx nzip = (l.zipIdx nzip).set nset (a, nset + nzip) := match l with
  | [] => by simp
  | x :: xs =>
    match nset with
    | 0 => by simp
    | nset + 1 => by simp [zipIdx_set xs, show nset + (nzip + 1) = nset + 1 + nzip by ring]

theorem List.zipIdx_take {α : Type*} (l : List α) (ntake : ℕ) (nzip : ℕ) :
    (l.take ntake).zipIdx nzip = (l.zipIdx nzip).take ntake := match l with
  | [] => by simp
  | x :: xs =>
    match ntake with
    | 0 => by simp
    | ntake + 1 => by
      simp [zipIdx_take xs _]

theorem List.zipIdx_drop {α : Type*} (l : List α) (ndrop : ℕ) (nzip : ℕ) :
    (l.drop ndrop).zipIdx (nzip + ndrop) = (l.zipIdx nzip).drop ndrop := match l with
  | [] => by simp
  | x :: xs =>
    match ndrop with
    | 0 => by simp
    | ndrop + 1 => by
      simp [show nzip + (ndrop + 1) = nzip + 1 + ndrop by ring, zipIdx_drop xs]

def List.lengthWhile {α : Type*} (p : α → Prop) [DecidablePred p] : List α →  ℕ
| [] => 0
| x :: xs => if p x then xs.lengthWhile p + 1 else 0



@[simp]
theorem List.lengthWhile_nil {α : Type*} (p : α → Prop) [DecidablePred p] :
    [].lengthWhile p = 0 := rfl

theorem List.lengthWhile_le_length {α : Type*} (p : α → Prop) [DecidablePred p] (l : List α) :
    l.lengthWhile p ≤ l.length := match l with
  | [] => by simp
  | x :: xs => by
    rw [lengthWhile]
    by_cases h : p x
    · simpa [h] using lengthWhile_le_length p xs
    · simp [h]

theorem List.lengthWhile_eq_length_iff {α : Type*} {p : α → Prop} [DecidablePred p] {l : List α} :
    l.lengthWhile p = l.length ↔ l.Forall p := match l with
| [] => by simp
| x :: xs => by
  rw [lengthWhile]
  by_cases h : p x
  · simpa [h] using lengthWhile_eq_length_iff
  · simp [h]

theorem List.pred_of_lt_lengthWhile {α : Type*} (p : α → Prop) [DecidablePred p] {l : List α}
    {i : ℕ} (h : i < l.lengthWhile p) : p (l[i]'(h.trans_le (l.lengthWhile_le_length p))) :=
  match l with
  | [] => by simp at h
  | x :: xs => by
    rw [lengthWhile] at h
    match i with
    | 0 =>
      suffices p x by simpa
      contrapose! h
      simp [h]
    | i + 1 =>
      have hp : p x := by
        contrapose! h
        simp [h]
      simp only [hp, ↓reduceIte, add_lt_add_iff_right] at h
      simp only [getElem_cons_succ]
      apply pred_of_lt_lengthWhile p h

theorem List.lengthWhile_eq_iff_of_lt_length {α : Type*}
    {p : α → Prop} [DecidablePred p] {l : List α} {a : ℕ} (ha : a < l.length) :
    l.lengthWhile p = a ↔ (∀ i, (h : i < a) → p (l[i])) ∧ (¬ p l[a]) := match l with
| [] => by simp at ha
| x :: xs => by
  rw [lengthWhile]
  by_cases h : p x <;> simp only [h, ↓reduceIte]
  · by_cases ha0 : a = 0
    · simp_rw [ha0]
      simpa using h
    · have hiff : lengthWhile p xs + 1 = a ↔ lengthWhile p xs = a - 1 := by
        grind
      rw [hiff, List.lengthWhile_eq_iff_of_lt_length (by grind)]
      constructor
      · grind
      · intro ⟨hi, hia⟩
        constructor
        · intro i hi'
          specialize hi (i + 1) (by grind)
          simpa using hi
        · grind
  · constructor
    · intro ha
      simp_rw [← ha]
      simpa using h
    · intro ⟨hi, hia⟩
      by_contra!
      specialize hi 0 (by grind)
      simp [h] at hi

theorem List.lengthWhile_mono {α : Type*}
    (p : α → Prop) [DecidablePred p] (l r : List α) :
    l.lengthWhile p ≤ (l ++ r).lengthWhile p := match l with
  | [] => by simp
  | x :: xs => by
    rw [cons_append]
    rw [lengthWhile, lengthWhile]
    split <;> simp [lengthWhile_mono]

theorem List.lengthWhile_set {α : Type*}
    (p : α → Prop) [DecidablePred p] (l : List α) {i : ℕ} (hi : i < l.length)
    (hp : ¬ p l[i]) (x : α) :
    l.lengthWhile p ≤ (l.set i x).lengthWhile p := match l with
  | [] => by simp
  | x :: xs => match i with
    | 0 => by
      replace hp : ¬p x := by simpa using hp
      simp [lengthWhile, set_cons_zero, hp]
    | i + 1 => by
      simp only [lengthWhile, set_cons_succ]
      split
      · simpa using lengthWhile_set p _ (by simpa using hi) (by simpa using hp) _
      · simp

def List.updateLast {α : Type*} (l : List α) (f : α → α) : List α :=
  match l with
  | [] => []
  | x :: xs => (x :: xs).set ((x :: xs).length - 1) (f ((x :: xs).getLast (by simp)))

@[simp]
theorem List.updateLast_id {α : Type*} (l : List α) : l.updateLast id = l :=
  match l with
  | [] => by simp [updateLast]
  | x :: xs => by
    simp [updateLast, List.getLast_eq_getElem]

theorem List.updateLast_eq_self {α : Type*} (l : List α) (f : α → α)
    (hl : l ≠ []) (h : f (l.getLast hl) = l.getLast hl) :
    l.updateLast f = l :=
  match l with
  | [] => by simp at hl
  | x :: xs => by
    unfold updateLast
    simp only [h]
    rw [getLast_eq_getElem]
    simp


@[simp]
theorem List.updateLast_nil {α : Type*} (f : α → α) : [].updateLast f = [] := rfl

@[simp]
theorem List.updateLast_eq {α : Type*} (l : List α) (f : α → α) (h : l ≠ []) :
    l.updateLast f = l.set (l.length - 1) (f (l.getLast h)) :=
  match l with
  | [] => by simp [updateLast]
  | x :: xs => by simp [updateLast]

@[simp]
theorem List.length_updateLast {α : Type*} (l : List α) (f : α → α) :
    (l.updateLast f).length = l.length :=
  match l with
  | [] => by simp
  | x :: xs => by simp

@[simp]
theorem List.updateLast_updateLast {α : Type*} (l : List α) (f g : α → α) :
    (l.updateLast f).updateLast g = l.updateLast (g ∘ f) :=
  match l with
  | [] => by simp
  | x :: xs => by
    rw [updateLast, updateLast]
    unfold updateLast
    split
    · case _ heq => simp at heq
    · case _ heq =>
      simp_rw [← heq]
      simp only [length_set, set_set, Function.comp_apply]
      congr
      simp_rw [List.getLast_eq_getElem]
      simp

theorem List.getElem_updateLast {α : Type*} (l : List α) (f : α → α)
    {i : ℕ} (h : i + 1 < l.length) :
    (l.updateLast f)[i]'(by simp; grind) = l[i] :=
  match l with
  | [] => by simp
  | x :: xs => by
    simp_rw [List.updateLast_eq (x :: xs) f (by simp)]
    rw [List.getElem_set_ne (by grind)]

@[ext]
structure FerrersDiagram (n : ℕ) where
  delta : List ℕ
  delta_pos : delta.Forall (0 < ·)
  delta_sum : ((delta.zipIdx 1).map fun p ↦ p.1 * p.2).sum = n

namespace FerrersDiagram
variable {n : ℕ}

theorem length_delta_le_n (x : FerrersDiagram n) : x.delta.length ≤ n := by
  conv =>
    right
    rw [← x.delta_sum]
  refine le_of_eq_of_le (by simp) (List.length_le_sum_of_one_le _ ?_)
  intro p hp
  rw [List.mem_map] at hp
  obtain ⟨a, ha, rfl⟩ := hp
  obtain ⟨ha2, _, ha1⟩ := List.mem_zipIdx ha
  refine one_le_mul ?_ ha2
  apply List.forall_iff_forall_mem.mp x.delta_pos
  simp [ha1]

theorem delta_ne_nil (hn : 0 < n) (x : FerrersDiagram n) : x.delta ≠ [] := by
  contrapose! hn
  simp [← x.delta_sum, hn]

theorem getLast_delta_le_n (hn : 0 < n) (x : FerrersDiagram n) :
    x.delta.getLast (x.delta_ne_nil hn) ≤ n := by
  conv => right; rw [← x.delta_sum]
  have hlengthpos : 0 < x.delta.length := List.length_pos_iff.mpr (x.delta_ne_nil hn)
  trans x.delta.getLast (x.delta_ne_nil hn) * x.delta.length
  · exact Nat.le_mul_of_pos_right _ hlengthpos
  · apply List.le_sum_of_mem
    simp only [List.mem_map, Prod.exists]
    have hlength : x.delta.length - 1 < x.delta.length := by simpa using hlengthpos
    use x.delta[x.delta.length - 1], x.delta.length
    constructor
    · rw [List.mem_iff_getElem]
      use x.delta.length - 1, (by simpa using hlength)
      suffices 1 + (x.delta.length - 1) = x.delta.length by simpa
      grind
    · grind

def IsPosPentagonal (hn : 0 < n) (x : FerrersDiagram n) :=
  x.delta.getLast (x.delta_ne_nil hn) = x.delta.length ∧
  ∀ i, (h : i < x.delta.length - 1) → x.delta[i] = 1

def IsNegPentagonal (hn : 0 < n) (x : FerrersDiagram n) :=
  x.delta.getLast (x.delta_ne_nil hn) = x.delta.length + 1 ∧
  ∀ i, (h : i < x.delta.length - 1) → x.delta[i] = 1

def diagSize (x : FerrersDiagram n) := x.delta.lengthWhile (· = 1) -- = s - 1

abbrev takeDiagFun (delta : List ℕ) (i : ℕ) (hi : i < delta.length) := delta.set i (delta[i] - 1)

def takeDiag (x : FerrersDiagram n) (i : ℕ) (hi : i < x.delta.length)
    (h : 1 < x.delta[i]) : FerrersDiagram (n - (i + 1)) where
  delta := takeDiagFun x.delta i hi
  delta_pos := by
    rw [List.forall_iff_forall_mem]
    intro a ha
    obtain ha | ha := List.mem_or_eq_of_mem_set ha
    · exact (List.forall_iff_forall_mem.mp x.delta_pos) a ha
    · simpa [ha] using h
  delta_sum := by
    rw [List.zipIdx_set, List.map_set]
    zify
    simp only [List.map_set, List.map_map, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    rw [List.sum_set']
    simp only [List.length_map, List.length_zipIdx, hi, ↓reduceDIte, List.getElem_map,
      List.getElem_zipIdx, Function.comp_apply, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hin : i + 1 ≤ n := by
      apply Nat.add_one_le_of_lt
      apply lt_of_lt_of_le hi
      apply x.length_delta_le_n
    push_cast [h, hin]
    rw [add_comm (1 : ℤ) i, ← neg_mul, ← add_mul, ← add_sub_assoc, Int.add_left_neg,
      zero_sub, neg_mul, one_mul, Int.add_neg_eq_sub, sub_left_inj]
    conv =>
      right
      rw [← x.delta_sum]
    simp

theorem takeDiag_ne_nil (x : FerrersDiagram n) (i : ℕ) (hi : i < x.delta.length)
    (h : 1 < x.delta[i]) : (x.takeDiag i hi h).delta ≠ [] := by
  unfold takeDiag
  simpa using List.length_pos_iff.mp (Nat.zero_lt_of_lt hi)

theorem getLast_takeDiag (x : FerrersDiagram n) (i : ℕ) (hi : i < x.delta.length - 1)
    (h : 1 < x.delta[i]) :
    (x.takeDiag i (Nat.lt_of_lt_of_le hi (by simp)) h).delta.getLast
      (x.takeDiag_ne_nil i (Nat.lt_of_lt_of_le hi (by simp)) h) =
    (x.delta.getLast (List.length_pos_iff.mp (Nat.zero_lt_of_lt
      (Nat.lt_of_lt_of_le hi (by simp))))) := by
  unfold takeDiag
  simp only
  rw [← List.getElem_length_sub_one_eq_getLast
    (by simpa using Nat.zero_lt_of_lt (Nat.lt_of_lt_of_le hi (by simp)))]
  rw [← List.getElem_length_sub_one_eq_getLast
    (by simpa using Nat.zero_lt_of_lt (Nat.lt_of_lt_of_le hi (by simp)))]
  rw [List.getElem_set]
  simp [hi.ne]

theorem getLast_takeDiag' (hn : 0 < n) (x : FerrersDiagram n) (i : ℕ) (hi : i = x.delta.length - 1)
    (h : 1 < x.delta[i]'(by simpa [hi] using List.length_pos_iff.mpr (x.delta_ne_nil hn))) :
    (x.takeDiag i (by simpa [hi] using List.length_pos_iff.mpr (x.delta_ne_nil hn)) h).delta.getLast
      (x.takeDiag_ne_nil i (by simpa [hi] using List.length_pos_iff.mpr (x.delta_ne_nil hn)) h) =
    (x.delta.getLast (by simpa using (x.delta_ne_nil hn))) - 1 := by
  unfold takeDiag
  simp only
  rw [← List.getElem_length_sub_one_eq_getLast
    (by simpa using List.length_pos_iff.mpr (x.delta_ne_nil hn))]
  rw [← List.getElem_length_sub_one_eq_getLast
    (by simpa using List.length_pos_iff.mpr (x.delta_ne_nil hn))]
  rw [List.getElem_set]
  simp [hi]

abbrev putLastFun (delta : List ℕ) (i : ℕ) := delta.updateLast (· - (i + 1)) ++ [i + 1]

def putLast (hn : 0 < n) (x : FerrersDiagram n) (i : ℕ)
    (hi : (i + 1) < x.delta.getLast (x.delta_ne_nil hn)) : FerrersDiagram (n + (i + 1)) where
  delta := putLastFun x.delta i
  delta_pos := by
    suffices (x.delta.set (x.delta.length - 1) (x.delta.getLast (x.delta_ne_nil hn) - (i + 1))
      ).Forall (0 < ·) by simpa [x.delta_ne_nil hn]
    rw [List.forall_iff_forall_mem]
    intro a ha
    obtain ha | ha := List.mem_or_eq_of_mem_set ha
    · exact (List.forall_iff_forall_mem.mp x.delta_pos) a ha
    · simpa [ha]
  delta_sum := by
    unfold putLastFun
    rw [x.delta.updateLast_eq _ (x.delta_ne_nil hn)]
    rw [List.zipIdx_append, List.map_append, List.sum_append, List.zipIdx_set, List.map_set]
    suffices ((List.map (fun p ↦ p.1 * p.2) (x.delta.zipIdx 1)).set (x.delta.length - 1)
        ((x.delta.getLast _ - (i + 1)) * (x.delta.length - 1 + 1))).sum +
        (i + 1) * (1 + x.delta.length) =
        n + (i + 1) by simpa
    zify
    simp only [List.map_set, List.map_map, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    rw [List.sum_set']
    have h0 : 0 < x.delta.length := List.length_pos_iff.mpr (x.delta_ne_nil hn)
    push_cast [hi]
    simp only [List.length_map, List.length_zipIdx, tsub_lt_self_iff, h0, zero_lt_one, and_self,
      ↓reduceDIte, List.getElem_map, List.getElem_zipIdx, List.getElem_length_sub_one_eq_getLast,
      Function.comp_apply, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pred, add_sub_cancel,
      sub_add_cancel]
    rw [add_assoc]
    congr 1
    · conv => right; rw [← x.delta_sum]
      simp
    · ring

theorem getLast_putLast (hn : 0 < n) (x : FerrersDiagram n) (i : ℕ)
    (hi : (i + 1) < x.delta.getLast (x.delta_ne_nil hn)) :
    (x.putLast hn i hi).delta.getLast (delta_ne_nil (by simp) _) = i + 1 := by
  simp [putLast]

theorem diagSize_putLast (hn : 0 < n) (x : FerrersDiagram n) (i : ℕ)
    (hi : (i + 1) < x.delta.getLast (x.delta_ne_nil hn))
    (hlast : 1 < x.delta.getLast (x.delta_ne_nil hn)) :
    x.diagSize ≤ (x.putLast hn i hi).diagSize := by
  unfold diagSize putLast
  refine le_trans ?_ (List.lengthWhile_mono _ _ _)
  rw [x.delta.updateLast_eq _ (x.delta_ne_nil hn)]
  refine List.lengthWhile_set _ _
    (by simpa using List.length_pos_iff.mpr (x.delta_ne_nil hn)) ?_ _
  rw [List.getLast_eq_getElem] at hlast
  exact hlast.ne.symm

def IsToDown (hn : 0 < n) (x : FerrersDiagram n) :=
  x.diagSize + 1 < x.delta.getLast (x.delta_ne_nil hn)

theorem pred_cast (p : (n : ℕ) → (0 < n) → (FerrersDiagram n) → Prop)
    (hn : 0 < n) {m : ℕ} (x : FerrersDiagram m)
    (h : m = n) :
    p n hn (cast (congrArg _ h) x) ↔ p m (h ▸ hn) x := by
  grind

theorem down_size' (hn : 0 < n) (x : FerrersDiagram n)
    (hdown : x.IsToDown hn) : x.diagSize + 1 < n := by
  apply lt_of_lt_of_le hdown
  apply x.getLast_delta_le_n hn

theorem down_size (hn : 0 < n) (x : FerrersDiagram n)
    (hdown : x.IsToDown hn) :
    n = n - (x.diagSize + 1) + (x.diagSize + 1) :=
  (Nat.sub_add_cancel (x.down_size' hn hdown).le).symm

theorem diagSize_lt (hn : 0 < n) (x : FerrersDiagram n)
    (hdown : x.IsToDown hn) : x.diagSize < x.delta.length := by
  unfold IsToDown at hdown
  by_contra!
  unfold diagSize at this
  have hthis' : x.delta.length = List.lengthWhile (· = 1) x.delta :=
    le_antisymm this (List.lengthWhile_le_length _ _)
  have hxall : x.delta.Forall (· = 1) := List.lengthWhile_eq_length_iff.mp hthis'.symm
  have hxlast : x.delta.getLast (x.delta_ne_nil hn) = 1 := by
    apply List.forall_iff_forall_mem.mp hxall
    apply List.getLast_mem
  simp [hxlast] at hdown

theorem delta_diagSize (hn : 0 < n) (x : FerrersDiagram n)
    (hdown : x.IsToDown hn) : 1 < x.delta[x.diagSize]'(x.diagSize_lt hn hdown) := by
  by_contra!
  have h1 : x.delta[x.diagSize]'(x.diagSize_lt hn hdown) = 1 :=
    le_antisymm this (Nat.one_le_of_lt (List.forall_iff_forall_mem.mp x.delta_pos _ (by simp)))
  obtain hdiagprop := (List.lengthWhile_eq_iff_of_lt_length (x.diagSize_lt hn hdown)).mp
    (show x.diagSize = x.diagSize by rfl)
  exact hdiagprop.2 h1

def down1 (hn : 0 < n) (x : FerrersDiagram n) (hdown : x.IsToDown hn) :
    FerrersDiagram (n - (x.diagSize + 1)) :=
  x.takeDiag x.diagSize (x.diagSize_lt hn hdown) (x.delta_diagSize hn hdown)

theorem diagSize_add_one_lt (hn : 0 < n) (x : FerrersDiagram n)
    (hdown : x.IsToDown hn)
    (hnegpen : ¬ x.IsNegPentagonal hn) :
    x.diagSize + 1 < (x.down1 hn hdown).delta.getLast
    (delta_ne_nil (Nat.zero_lt_sub_of_lt (x.down_size' hn hdown)) _) := by
  obtain hlt | heq := lt_or_eq_of_le (Nat.le_sub_one_of_lt (x.diagSize_lt hn hdown))
  · unfold IsToDown at hdown
    convert hdown using 1
    apply getLast_takeDiag
    exact hlt
  · obtain hh := x.getLast_takeDiag' hn _ heq (x.delta_diagSize hn hdown)
    unfold down1
    rw [hh, heq, Nat.sub_add_cancel (Nat.one_le_of_lt (x.diagSize_lt hn hdown))]
    contrapose! hnegpen with hthis
    obtain hGetLastLeLength := Nat.le_add_of_sub_le hthis
    have hLengthLeGetLast : x.delta.length + 1 ≤ x.delta.getLast (x.delta_ne_nil hn) := by
      obtain heq := (Nat.sub_eq_iff_eq_add (Nat.one_le_of_lt (x.diagSize_lt hn hdown))).mp heq.symm
      rw [heq]
      exact Nat.add_one_le_iff.mpr hdown
    obtain hLengthEqGetLast := le_antisymm hGetLastLeLength hLengthLeGetLast
    refine ⟨hLengthEqGetLast, ?_⟩
    obtain hdiagprop := (List.lengthWhile_eq_iff_of_lt_length
      (by simpa using Nat.zero_lt_of_lt (x.diagSize_lt hn hdown))).mp heq
    exact hdiagprop.1

def down (hn : 0 < n) (x : FerrersDiagram n)
    (hdown : x.IsToDown hn)
    (hnegpen : ¬ x.IsNegPentagonal hn) :
    FerrersDiagram n := by
  let lastPut := (x.down1 hn hdown).putLast (Nat.zero_lt_sub_of_lt (x.down_size' hn hdown))
    x.diagSize (x.diagSize_add_one_lt hn hdown hnegpen)
  rw [x.down_size hn hdown]
  exact lastPut

theorem delta_down (hn : 0 < n) (x : FerrersDiagram n)
    (hdown : x.IsToDown hn)
    (hnegpen : ¬ x.IsNegPentagonal hn) :
    (x.down hn hdown hnegpen).delta =
    putLastFun (takeDiagFun x.delta x.diagSize (x.diagSize_lt hn hdown)) x.diagSize := by
  unfold down
  simp only [eq_mpr_eq_cast]
  suffices ((x.down1 hn hdown).putLast (Nat.zero_lt_sub_of_lt (x.down_size' hn hdown))
      x.diagSize (x.diagSize_add_one_lt hn hdown hnegpen)).delta =
      putLastFun (takeDiagFun x.delta x.diagSize (x.diagSize_lt hn hdown)) x.diagSize by
    convert this
    · exact down_size hn x hdown
    · simp
  simp [putLast, down1, takeDiag]

theorem getLast_down (hn : 0 < n) (x : FerrersDiagram n)
    (hdown : x.IsToDown hn)
    (hnegpen : ¬ x.IsNegPentagonal hn) :
    (x.down hn hdown hnegpen).delta.getLast (delta_ne_nil hn _) = x.diagSize + 1 := by
  simp [x.delta_down hn hdown hnegpen]

theorem length_down (hn : 0 < n) (x : FerrersDiagram n)
    (hdown : x.IsToDown hn)
    (hnegpen : ¬ x.IsNegPentagonal hn) :
    (x.down hn hdown hnegpen).delta.length = x.delta.length + 1 := by
  simp [x.delta_down hn hdown hnegpen]

theorem down_notToDown (hn : 0 < n) (x : FerrersDiagram n)
    (hdown : x.IsToDown hn)
    (hnegpen : ¬ x.IsNegPentagonal hn) :
    ¬ (x.down hn hdown hnegpen).IsToDown hn := by
  unfold down
  simp only [eq_mpr_eq_cast]
  rw [pred_cast @IsToDown hn _ (x.down_size hn hdown).symm]
  unfold IsToDown
  rw [getLast_putLast]
  simp only [add_lt_add_iff_right, not_lt]
  refine le_trans ?_ (diagSize_putLast (Nat.zero_lt_sub_of_lt (x.down_size' hn hdown))
    _ _ ?_ ?_)
  · apply List.lengthWhile_set _ _ (x.diagSize_lt hn hdown)
    exact ((List.lengthWhile_eq_iff_of_lt_length (x.diagSize_lt hn hdown)).mp rfl).2
  · exact x.diagSize_add_one_lt hn hdown hnegpen
  · exact lt_of_le_of_lt (by simp) (x.diagSize_add_one_lt hn hdown hnegpen)

theorem down_notPosPentagonal (hn : 0 < n) (x : FerrersDiagram n)
    (hdown : x.IsToDown hn)
    (hnegpen : ¬ x.IsNegPentagonal hn) :
    ¬ (x.down hn hdown hnegpen).IsPosPentagonal hn := by
  unfold IsPosPentagonal
  rw [and_comm, not_and]
  intro h
  rw [getLast_down, length_down]
  by_contra!
  simp only [Nat.add_right_cancel_iff] at this
  obtain h1 := List.lengthWhile_eq_length_iff.mp this
  have hlast: x.delta.getLast (x.delta_ne_nil hn) = 1 :=
    (List.forall_iff_forall_mem.mp h1) _ (by simp)
  unfold IsToDown at hdown
  simp [hlast] at hdown

abbrev takeLastFun (delta : List ℕ) (h : delta ≠ []) :=
  (delta.take (delta.length - 1)).updateLast (· + delta.getLast h)

def takeLast (hn : 0 < n) (x : FerrersDiagram n) :
    FerrersDiagram (n - x.delta.getLast (x.delta_ne_nil hn)) where
  delta := takeLastFun x.delta (x.delta_ne_nil hn)
  delta_pos := by
    unfold takeLastFun
    by_cases hnil : x.delta.take (x.delta.length - 1) = []
    · simp [hnil]
    · rw [List.updateLast_eq _ _ hnil]
      rw [List.forall_iff_forall_mem]
      intro a ha
      obtain hmem | rfl := List.mem_or_eq_of_mem_set ha
      · exact List.forall_iff_forall_mem.mp x.delta_pos _ <| List.mem_of_mem_take hmem
      · have hlast : 0 < x.delta.getLast (x.delta_ne_nil hn) := by
          apply List.forall_iff_forall_mem.mp x.delta_pos _
          simp
        simp [hlast]
  delta_sum := by
    unfold takeLastFun
    by_cases hnil : x.delta.take (x.delta.length - 1) = []
    · rw [List.take_eq_nil_iff] at hnil
      simp only [x.delta_ne_nil hn, or_false] at hnil
      rw [Nat.sub_eq_iff_eq_add (Nat.one_le_of_lt (List.ne_nil_iff_length_pos.mp
        (x.delta_ne_nil hn))), zero_add, List.length_eq_one_iff] at hnil
      obtain ⟨a, ha⟩ := hnil
      simp [ha, ← x.delta_sum]
    have h1 : 1 < x.delta.length := by
      contrapose! hnil
      simp [hnil]
    rw [List.updateLast_eq _ _ hnil]
    rw [List.zipIdx_set, List.map_set]
    zify
    simp only [List.length_take, tsub_le_iff_right, le_add_iff_nonneg_right, zero_le,
      inf_of_le_left, List.map_set, List.map_map, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    rw [List.sum_set']
    simp only [List.length_map, List.length_zipIdx, List.length_take, tsub_le_iff_right,
      le_add_iff_nonneg_right, zero_le, inf_of_le_left, tsub_lt_self_iff, tsub_pos_iff_lt, h1,
      zero_lt_one, and_self, ↓reduceDIte, List.getElem_map, List.getElem_zipIdx, List.getElem_take,
      Function.comp_apply, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pred, add_sub_cancel,
      sub_add_cancel]
    have heq : (List.take (x.delta.length - 1) x.delta).getLast hnil =
        x.delta[x.delta.length - 1 - 1] := by
      grind
    rw [heq]
    rw [add_mul, ← add_assoc _ (↑x.delta[x.delta.length - 1 - 1] * ↑(x.delta.length - 1) : ℤ) _ ]
    rw [neg_add_cancel, zero_add]
    have hle : x.delta.getLast (x.delta_ne_nil hn) ≤ n := getLast_delta_le_n hn x
    push_cast [hle, h1]
    apply eq_sub_of_add_eq
    rw [add_assoc, ← mul_add_one, sub_add_cancel]
    conv => right; rw [← x.delta_sum]
    simp only [Nat.cast_list_sum, List.map_map]
    rw [List.zipIdx_take, List.map_take]
    have : ((x.delta.getLast (x.delta_ne_nil hn)) * x.delta.length : ℤ) =
        (List.drop (x.delta.length - 1)
        (List.map (Nat.cast ∘ fun p ↦ p.1 * p.2) (x.delta.zipIdx 1))).sum := by
      rw [← List.map_drop, ← List.zipIdx_drop]
      rw [List.drop_length_sub_one (x.delta_ne_nil hn)]
      suffices (x.delta.length : ℤ) = 1 + (x.delta.length - 1 : ℕ) by simp [this]
      push_cast [h1]
      simp
    rw [this]
    exact List.sum_take_add_sum_drop _ _

theorem length_takeLast (hn : 0 < n) (x : FerrersDiagram n) :
    (x.takeLast hn).delta.length = x.delta.length - 1 := by
  simp [takeLast]

abbrev putDiagFun (delta : List ℕ) (i : ℕ) (hi : i < delta.length) := delta.set i (delta[i] + 1)

def putDiag (x : FerrersDiagram n) (i : ℕ) (hi : i < x.delta.length)
    : FerrersDiagram (n + (i + 1)) where
  delta := putDiagFun x.delta i hi
  delta_pos := by
    rw [List.forall_iff_forall_mem]
    intro a ha
    obtain ha | ha := List.mem_or_eq_of_mem_set ha
    · exact (List.forall_iff_forall_mem.mp x.delta_pos) a ha
    · simp [ha]
  delta_sum := by
    rw [List.zipIdx_set, List.map_set]
    zify
    simp only [List.map_set, List.map_map, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    rw [List.sum_set']
    simp only [List.length_map, List.length_zipIdx, hi, ↓reduceDIte, List.getElem_map,
      List.getElem_zipIdx, Function.comp_apply, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    rw [add_comm (1 : ℤ) i, ← neg_mul, ← add_mul, ← add_assoc, Int.add_left_neg,
      zero_add, one_mul, add_left_inj]
    conv =>
      right
      rw [← x.delta_sum]
    simp

theorem up_size (hn : 0 < n) (x : FerrersDiagram n) :
    n - x.delta.getLast (x.delta_ne_nil hn) + (x.delta.getLast (x.delta_ne_nil hn) - 1 + 1) =
    n := by
  rw [Nat.sub_add_cancel (by
    apply Nat.one_le_of_lt
    apply (List.forall_iff_forall_mem.mp x.delta_pos)
    simp
  )]
  rw [Nat.sub_add_cancel (getLast_delta_le_n hn x)]

theorem up_getLast_lt (hn : 0 < n) (x : FerrersDiagram n)
    (hdown : ¬ x.IsToDown hn) (hpospen : ¬ x.IsPosPentagonal hn) :
    x.delta.getLast (x.delta_ne_nil hn) - 1 < (x.takeLast hn).delta.length := by
  apply Nat.sub_one_lt_of_le (List.forall_iff_forall_mem.mp x.delta_pos _ (by simp))
  rw [length_takeLast]
  apply Nat.le_sub_one_of_lt

  rw [IsToDown, not_lt] at hdown
  have hdiag : x.diagSize + 1 ≤ x.delta.length + 1 := by
    unfold diagSize
    simpa using List.lengthWhile_le_length _ x.delta
  obtain h := hdown.trans hdiag

  by_contra! hassump
  obtain heq | hlt := eq_or_lt_of_le hassump
  · contrapose! hpospen
    constructor
    · exact heq.symm
    · intro i hi
      apply List.pred_of_lt_lengthWhile (· = 1)
      refine hi.trans_le ?_
      rw [heq]
      apply Nat.sub_le_of_le_add
      exact hdown
  obtain heq | hlt := eq_or_lt_of_le (Nat.add_one_le_of_lt hlt)
  · rw [← heq] at hdown
    obtain hdiageq := le_antisymm hdiag hdown
    unfold diagSize at hdiageq
    obtain h1 := List.lengthWhile_eq_length_iff.mp (Nat.add_right_cancel_iff.mp hdiageq)
    obtain hgetLast : x.delta.getLast (x.delta_ne_nil hn) = 1 :=
      List.forall_iff_forall_mem.mp h1 _ (by simp)
    rw [hgetLast] at heq
    simp [x.delta_ne_nil hn] at heq
  obtain hwhat := h.trans_lt hlt
  simp at hwhat

def up (hn : 0 < n) (x : FerrersDiagram n)
    (hdown : ¬ x.IsToDown hn)
    (hpospen : ¬ x.IsPosPentagonal hn) : FerrersDiagram n := by
  let diagPut := (x.takeLast hn).putDiag (x.delta.getLast (x.delta_ne_nil hn) - 1)
    (x.up_getLast_lt hn hdown hpospen)
  rw [x.up_size hn] at diagPut
  exact diagPut

theorem delta_up (hn : 0 < n) (x : FerrersDiagram n)
    (hdown : ¬ x.IsToDown hn)
    (hpospen : ¬ x.IsPosPentagonal hn) :
    (x.up hn hdown hpospen).delta =
    putDiagFun (takeLastFun x.delta (x.delta_ne_nil hn))
    (x.delta.getLast (x.delta_ne_nil hn) - 1) (x.up_getLast_lt hn hdown hpospen) := by
  unfold up
  suffices ((x.takeLast hn).putDiag (x.delta.getLast (x.delta_ne_nil hn) - 1)
      (x.up_getLast_lt hn hdown hpospen)).delta =
      putDiagFun (takeLastFun x.delta (x.delta_ne_nil hn))
      (x.delta.getLast (x.delta_ne_nil hn) - 1) (x.up_getLast_lt hn hdown hpospen) by
    convert this
    · exact (up_size hn x).symm
    · simp
  simp [putDiag, takeLast]

theorem diagSize_up (hn : 0 < n) (x : FerrersDiagram n)
    (hdown : ¬ x.IsToDown hn)
    (hpospen : ¬ x.IsPosPentagonal hn) :
    (x.up hn hdown hpospen).diagSize = x.delta.getLast (x.delta_ne_nil hn) - 1 := by
  simp_rw [diagSize, delta_up]
  simp only [IsToDown, not_lt] at hdown
  have hdiagle : x.diagSize ≤ x.delta.length := by
    unfold diagSize
    exact List.lengthWhile_le_length _ x.delta
  rw [List.lengthWhile_eq_iff_of_lt_length (by
    suffices x.delta.getLast _ - 1 < x.delta.length - 1 by
      simpa [putDiagFun]
    apply Nat.sub_lt_sub_right (by
      apply List.forall_iff_forall_mem.mp x.delta_pos
      simp
    )
    obtain heq | hlt := eq_or_lt_of_le <| hdiagle
    · have h1 := List.lengthWhile_eq_length_iff.mp heq
      have h1' : x.delta.getLast (x.delta_ne_nil hn) = 1 := by
        apply List.forall_iff_forall_mem.mp h1
        simp
      rw [h1']
      suffices 1 < x.delta.length by simpa
      contrapose! hpospen with hthis
      have h1'' : x.delta.length = 1 := by
        apply le_antisymm hthis
        apply Nat.one_le_of_lt
        apply List.ne_nil_iff_length_pos.mp
        exact x.delta_ne_nil hn
      constructor
      · rw [h1', h1'']
      · intro i hi
        simp [h1''] at hi
    obtain heq | hlt := eq_or_lt_of_le <| Nat.lt_iff_add_one_le.mp hlt
    · apply lt_of_le_of_ne (heq ▸ hdown)
      contrapose! hpospen with heq'
      constructor
      · exact heq'
      · intro i hi
        apply List.pred_of_lt_lengthWhile (· = 1)
        apply hi.trans_le
        rw [← heq, Nat.add_sub_cancel]
        rfl
    apply hdown.trans_lt hlt
  )]
  constructor
  · intro i hi
    simp_rw [putDiagFun, List.getElem_set_ne (hi.ne.symm)]
    unfold takeLastFun
    rw [List.getElem_updateLast _ _ (by
      suffices i + 1 < x.delta.length - 1 by simpa
      obtain heq | hlt := eq_or_lt_of_le <| hdiagle
      · have h1 := List.lengthWhile_eq_length_iff.mp heq
        have hwhat : x.delta.getLast (x.delta_ne_nil hn) = 1 := by
          apply List.forall_iff_forall_mem.mp h1
          simp
        simp [hwhat] at hi
      obtain heq | hlt := eq_or_lt_of_le <| Nat.lt_iff_add_one_le.mp hlt
      · obtain heq' | hlt' := eq_or_lt_of_le hdown
        · contrapose! hpospen
          constructor
          · rw [heq', heq]
          · intro i hi
            apply List.pred_of_lt_lengthWhile (· = 1)
            apply hi.trans_le
            rw [← heq, Nat.add_sub_cancel]
            rfl
        · have hle1 : 1 ≤ x.delta.getLast (x.delta_ne_nil hn) := by
            apply Nat.one_le_of_lt
            apply List.forall_iff_forall_mem.mp x.delta_pos
            simp
          obtain hi' := (Nat.lt_iff_add_one_le.mp hi).trans_lt
            (Nat.sub_lt_right_of_lt_add hle1 hlt')
          exact hi'.trans_le <| Nat.le_sub_one_of_lt hlt
      obtain hi' := Nat.lt_iff_add_one_le.mp <| hi.trans_le (Nat.sub_le_of_le_add hdown)
      exact hi'.trans_lt <| Nat.lt_sub_of_add_lt hlt
    )]
    rw [List.getElem_take]
    apply List.pred_of_lt_lengthWhile (· = 1)
    apply hi.trans_le
    apply Nat.sub_le_of_le_add
    exact hdown
  · suffices (takeLastFun x.delta (x.delta_ne_nil hn))[x.delta.getLast _ - 1]'_ ≠ 0 by simpa
    apply Nat.ne_zero_iff_zero_lt.mpr
    apply List.forall_iff_forall_mem.mp (x.takeLast hn).delta_pos
    simp [takeLast]

theorem up_isToDown (hn : 0 < n) (x : FerrersDiagram n)
    (hdown : ¬ x.IsToDown hn)
    (hpospen : ¬ x.IsPosPentagonal hn) :
    (x.up hn hdown hpospen).IsToDown hn := by
  unfold IsToDown


  sorry

theorem takeLastFun_putLastFun (delta : List ℕ) (i : ℕ) (hdelta : delta ≠ [])
    (h : i + 1 ≤ delta.getLast hdelta) :
    takeLastFun (putLastFun delta i) (by simp [putLastFun]) = delta := by
  simp [takeLastFun, putLastFun]
  apply List.updateLast_eq_self _ _ hdelta
  simp [h]

theorem up_down (hn : 0 < n) (x : FerrersDiagram n)
    (hdown : x.IsToDown hn)
    (hnegpen : ¬ x.IsNegPentagonal hn) :
    (x.down hn hdown hnegpen).up hn (x.down_notToDown hn hdown hnegpen)
    (x.down_notPosPentagonal hn hdown hnegpen) = x := by
  ext1
  simp_rw [delta_up, delta_down]

  have h1 : takeDiagFun x.delta x.diagSize (x.diagSize_lt hn hdown) ≠ [] := by
    simpa using x.delta_ne_nil hn

  have h2 : x.diagSize + 1 ≤
      (takeDiagFun x.delta x.diagSize (x.diagSize_lt hn hdown)).getLast h1 := by
    obtain h := x.diagSize_add_one_lt hn hdown hnegpen
    unfold down1 takeDiag at h
    exact h.le

  conv in (takeLastFun _ _) =>
    rw [takeLastFun_putLastFun _ _ h1 h2]

  have h3 (h : x.diagSize < x.delta.length) :
      x.delta[x.diagSize] - 1 + 1 = x.delta[x.diagSize] := by
    rw [Nat.sub_add_cancel ?_]
    apply List.forall_iff_forall_mem.mp (x.delta_pos)
    simp

  simp [h3]

end FerrersDiagram
