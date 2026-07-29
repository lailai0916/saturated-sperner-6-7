import AiMathLab.P0054AdjacentSixChecks

/-!
# Sound compact encodings for the adjacent six-row certificate

The finite certificate uses base three for the 21 support multiplicities and
base 32 for the six accumulated degrees.  This file relates those machine
encodings to typed functions, independently of the exhaustive check.
-/

namespace AiMathLab.P0054.AdjacentSixFinite

open AiMathLab.P0054.G417
open scoped BigOperators

theorem adjacentSixOfDigits_digit (base : Nat) (hBase : 0 < base)
    (digits : List Nat) (hDigits : ∀ digit ∈ digits, digit < base) (i : Nat) :
    Nat.ofDigits base digits / base ^ i % base = digits.getD i 0 := by
  rw [Nat.ofDigits_div_pow_eq_ofDigits_drop i hBase digits hDigits]
  rw [Nat.ofDigits_mod_eq_head!]
  by_cases hi : i < digits.length
  · have hDrop := List.drop_eq_getElem_cons hi
    have hDigit : digits[i] < base := hDigits digits[i] (List.getElem_mem hi)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    rw [hDrop]
    simp only [List.head!_cons]
    exact Nat.mod_eq_of_lt hDigit
  · have hDrop : digits.drop i = [] := List.drop_eq_nil_of_le (Nat.le_of_not_gt hi)
    rw [hDrop]
    simp [List.getD_eq_getElem?_getD, hi]

def adjacentSixCompactEncode (m : Fin 21 → Fin 3) : Nat :=
  Nat.ofDigits 3 (List.ofFn fun s : Fin 21 ↦ (m s).val)

@[simp] theorem adjacentSixCompactMultiplicityDigit_encode
    (m : Fin 21 → Fin 3) (s : Fin 21) :
    adjacentSixCompactMultiplicityDigit (adjacentSixCompactEncode m) s.val = (m s).val := by
  unfold adjacentSixCompactMultiplicityDigit adjacentSixCompactEncode
  rw [adjacentSixOfDigits_digit 3 (by omega)]
  · have hs : s.val < (List.ofFn fun i : Fin 21 ↦ (m i).val).length := by simp
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs, Option.getD_some]
    rw [List.getElem_ofFn]
  · intro digit hDigit
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hDigit
    exact (m i).isLt

def adjacentSixMultiplicityOfFunction (m : Fin 21 → Fin 3) : SixMultiplicity :=
  Array.ofFn fun s : Fin 21 ↦ (m s).val

@[simp] theorem adjacentSixMultiplicityOfFunction_digit
    (m : Fin 21 → Fin 3) (s : Fin 21) :
    sixMultiplicityDigit (adjacentSixMultiplicityOfFunction m) s.val = (m s).val := by
  simp [sixMultiplicityDigit, adjacentSixMultiplicityOfFunction, Array.getD]

def adjacentSixFunctionDegree (m : Fin 21 → Fin 3) (v : Nat) : Nat :=
  ∑ s : Fin 21, if sixSupportContains s.val v then (m s).val else 0

theorem adjacentSixSupportDegree_function (m : Fin 21 → Fin 3) (v : Fin 6) :
    sixSupportDegree (adjacentSixMultiplicityOfFunction m) v =
      adjacentSixFunctionDegree m v := by
  unfold sixSupportDegree adjacentSixFunctionDegree
  apply Finset.sum_congr rfl
  intro s hs
  rw [adjacentSixMultiplicityOfFunction_digit]
  fin_cases s <;> fin_cases v <;>
    simp [sixSupport, sixSupportContains, sixSupportMask, Nat.testBit]

theorem adjacentSixFunctionDegree_lt_32 (m : Fin 21 → Fin 3) (v : Fin 6) :
    adjacentSixFunctionDegree m v.val < 32 := by
  have hBound : adjacentSixFunctionDegree m v.val ≤
      ∑ s : Fin 21, if sixSupportContains s.val v.val then 2 else 0 := by
    unfold adjacentSixFunctionDegree
    apply Finset.sum_le_sum
    intro s hs
    by_cases hContains : sixSupportContains s.val v.val = true
    · simp only [hContains, if_true]
      exact Nat.le_pred_of_lt (m s).isLt
    · simp [Bool.eq_false_of_not_eq_true hContains]
  have hSix : (∑ s : Fin 21, if sixSupportContains s.val v.val then 2 else 0) = 12 := by
    fin_cases v <;> decide
  omega

def adjacentSixCompactEncodeDegrees (m : Fin 21 → Fin 3) : Nat :=
  Nat.ofDigits 32 (List.ofFn fun v : Fin 6 ↦ adjacentSixFunctionDegree m v.val)

@[simp] theorem adjacentSixCompactDegreeDigit_encode
    (m : Fin 21 → Fin 3) (v : Fin 6) :
    adjacentSixCompactDegreeDigit (adjacentSixCompactEncodeDegrees m) v.val =
      adjacentSixFunctionDegree m v.val := by
  unfold adjacentSixCompactDegreeDigit adjacentSixCompactEncodeDegrees
  rw [adjacentSixOfDigits_digit 32 (by omega)]
  · have hv : v.val <
        (List.ofFn fun i : Fin 6 ↦ adjacentSixFunctionDegree m i.val).length := by simp
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hv, Option.getD_some]
    rw [List.getElem_ofFn]
  · intro digit hDigit
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hDigit
    exact adjacentSixFunctionDegree_lt_32 m i

theorem adjacentSixCompactDegreeDigit_encode_nat
    (m : Fin 21 → Fin 3) {v : Nat} (hv : v < 6) :
    adjacentSixCompactDegreeDigit (adjacentSixCompactEncodeDegrees m) v =
      adjacentSixFunctionDegree m v := by
  exact adjacentSixCompactDegreeDigit_encode m ⟨v, hv⟩

theorem adjacentSixCompactEncode_eq_sum (m : Fin 21 → Fin 3) :
    adjacentSixCompactEncode m = ∑ s : Fin 21, (m s).val * 3 ^ s.val := by
  rw [adjacentSixCompactEncode, Nat.ofDigits_eq_sum_mapIdx]
  simp only [List.mapIdx_eq_ofFn, List.get_ofFn, List.length_ofFn,
    Fin.val_cast, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i hi
  congr

theorem adjacentSixCompactEncodeDegrees_eq_sum (m : Fin 21 → Fin 3) :
    adjacentSixCompactEncodeDegrees m =
      ∑ v : Fin 6, adjacentSixFunctionDegree m v.val * 32 ^ v.val := by
  rw [adjacentSixCompactEncodeDegrees, Nat.ofDigits_eq_sum_mapIdx]
  simp only [List.mapIdx_eq_ofFn, List.get_ofFn, List.length_ofFn,
    Fin.val_cast, List.sum_ofFn]

theorem adjacentSixFunctionDegree_update
    (m : Fin 21 → Fin 3) (s : Fin 21) (k : Fin 3) (hZero : m s = 0) (v : Nat) :
    adjacentSixFunctionDegree (Function.update m s k) v =
      adjacentSixFunctionDegree m v +
        if sixSupportContains s.val v then k.val else 0 := by
  classical
  unfold adjacentSixFunctionDegree
  have hUpdate :
      (fun x : Fin 21 ↦ if sixSupportContains x.val v
        then (Function.update m s k x).val else 0) =
        Function.update (fun x : Fin 21 ↦ if sixSupportContains x.val v
          then (m x).val else 0) s
          (if sixSupportContains s.val v then k.val else 0) := by
    funext x
    by_cases hxs : x = s
    · subst x
      simp
    · simp [Function.update_of_ne hxs]
  rw [hUpdate, Finset.sum_update_of_mem (Finset.mem_univ s)]
  rw [Finset.sdiff_singleton_eq_erase]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ s)]
  simp [hZero, add_comm]

theorem adjacentSixCompactEncode_update
    (m : Fin 21 → Fin 3) (s : Fin 21) (k : Fin 3) (hZero : m s = 0) :
    adjacentSixCompactEncode m + k.val * 3 ^ s.val =
      adjacentSixCompactEncode (Function.update m s k) := by
  classical
  rw [adjacentSixCompactEncode_eq_sum, adjacentSixCompactEncode_eq_sum]
  have hUpdate :
      (fun x : Fin 21 ↦ (Function.update m s k x).val * 3 ^ x.val) =
        Function.update (fun x : Fin 21 ↦ (m x).val * 3 ^ x.val) s
          (k.val * 3 ^ s.val) := by
    funext x
    by_cases hxs : x = s
    · subst x
      simp
    · simp [Function.update_of_ne hxs]
  rw [hUpdate, Finset.sum_update_of_mem (Finset.mem_univ s)]
  rw [Finset.sdiff_singleton_eq_erase]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ s)]
  simp [hZero, add_comm]

theorem adjacentSixCompactSupportWeight_eq_sum (s : Fin 21) :
    adjacentSixCompactSupportWeight s.val =
      ∑ v : Fin 6, (if sixSupportContains s.val v.val then 32 ^ v.val else 0) := by
  fin_cases s <;> decide

theorem adjacentSixCompactEncodeDegrees_update
    (m : Fin 21 → Fin 3) (s : Fin 21) (k : Fin 3) (hZero : m s = 0) :
    adjacentSixCompactAddDegree (adjacentSixCompactEncodeDegrees m) s.val k.val =
      adjacentSixCompactEncodeDegrees (Function.update m s k) := by
  classical
  rw [adjacentSixCompactEncodeDegrees_eq_sum, adjacentSixCompactEncodeDegrees_eq_sum,
    adjacentSixCompactAddDegree, adjacentSixCompactSupportWeight_eq_sum]
  simp only [adjacentSixFunctionDegree_update m s k hZero]
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases hContains : sixSupportContains s.val v.val = true
  · simp [hContains]
    ring
  · simp [Bool.eq_false_of_not_eq_true hContains]

def adjacentSixRestrict
    (target : Fin 21 → Fin 3) (processed : Finset (Fin 21)) : Fin 21 → Fin 3 :=
  fun s ↦ if s ∈ processed then target s else 0

theorem adjacentSixRestrict_zero (target : Fin 21 → Fin 3)
    (processed : Finset (Fin 21)) {s : Fin 21} (hs : s ∉ processed) :
    adjacentSixRestrict target processed s = 0 := by
  simp [adjacentSixRestrict, hs]

theorem adjacentSixRestrict_le (target : Fin 21 → Fin 3)
    (processed : Finset (Fin 21)) (s : Fin 21) :
    (adjacentSixRestrict target processed s).val ≤ (target s).val := by
  by_cases hs : s ∈ processed
  · simp [adjacentSixRestrict, hs]
  · simp [adjacentSixRestrict, hs]

theorem adjacentSixRestrict_update (target : Fin 21 → Fin 3)
    (processed : Finset (Fin 21)) (s : Fin 21) :
    Function.update (adjacentSixRestrict target processed) s (target s) =
      adjacentSixRestrict target (insert s processed) := by
  funext t
  by_cases hts : t = s
  · subst t
    simp [adjacentSixRestrict]
  · rw [Function.update_of_ne hts]
    simp [adjacentSixRestrict, hts]

theorem adjacentSixCompactEncodeRestrict_update (target : Fin 21 → Fin 3)
    (processed : Finset (Fin 21)) {s : Fin 21} (hs : s ∉ processed) :
    adjacentSixCompactEncode (adjacentSixRestrict target processed) +
        (target s).val * 3 ^ s.val =
      adjacentSixCompactEncode (adjacentSixRestrict target (insert s processed)) := by
  rw [adjacentSixCompactEncode_update _ s (target s)
    (adjacentSixRestrict_zero target processed hs)]
  rw [adjacentSixRestrict_update target processed s]

theorem adjacentSixCompactDegreesRestrict_update (target : Fin 21 → Fin 3)
    (processed : Finset (Fin 21)) {s : Fin 21} (hs : s ∉ processed) :
    adjacentSixCompactAddDegree
        (adjacentSixCompactEncodeDegrees (adjacentSixRestrict target processed))
        s.val (target s).val =
      adjacentSixCompactEncodeDegrees (adjacentSixRestrict target (insert s processed)) := by
  rw [adjacentSixCompactEncodeDegrees_update _ s (target s)
    (adjacentSixRestrict_zero target processed hs)]
  rw [adjacentSixRestrict_update target processed s]

theorem adjacentSixFunctionDegree_mono {left right : Fin 21 → Fin 3}
    (hDigits : ∀ s, (left s).val ≤ (right s).val) (v : Nat) :
    adjacentSixFunctionDegree left v ≤ adjacentSixFunctionDegree right v := by
  unfold adjacentSixFunctionDegree
  apply Finset.sum_le_sum
  intro s hs
  by_cases hContains : sixSupportContains s.val v = true
  · simp [hContains, hDigits s]
  · simp [Bool.eq_false_of_not_eq_true hContains]

theorem adjacentSixCompactCoverWeight_encode (target : Fin 21 → Fin 3)
    (C : List SixSupportIndex) :
    adjacentSixCompactCoverWeight (adjacentSixCompactEncode target) C =
      (C.map fun s ↦ sixMultiplicityDigit
        (adjacentSixMultiplicityOfFunction target) s.val).prod := by
  unfold adjacentSixCompactCoverWeight
  apply congrArg List.prod
  apply List.map_congr_left
  intro s hs
  rw [adjacentSixCompactMultiplicityDigit_encode,
    adjacentSixMultiplicityOfFunction_digit]

theorem adjacentSixCompactWeightedCoverCount_encode (target : Fin 21 → Fin 3) :
    adjacentSixCompactWeightedCoverCount (adjacentSixCompactEncode target) =
      sixWeightedCoverCount (adjacentSixMultiplicityOfFunction target) := by
  unfold adjacentSixCompactWeightedCoverCount sixWeightedCoverCount
  apply congrArg List.sum
  apply List.map_congr_left
  intro C hC
  apply congrArg List.prod
  have hCoerce : (do let s ← C; pure (s : Nat)) = C.map fun s ↦ s.val := by
    simpa [Function.comp_def] using
      (List.flatMap_pure_eq_map (fun s : SixSupportIndex ↦ s.val) C)
  rw [hCoerce, List.map_map]
  apply List.map_congr_left
  intro s hs
  simp

theorem adjacentSixCompactWeightedCoverAtLeastAux_sound
    {minimum m total : Nat} {covers : List (List SixSupportIndex)}
    (hCheck : adjacentSixCompactWeightedCoverAtLeastAux minimum m total covers = true) :
    minimum ≤ total + (covers.map fun C ↦ adjacentSixCompactCoverWeight m C).sum := by
  induction covers generalizing total with
  | nil =>
      simpa [adjacentSixCompactWeightedCoverAtLeastAux, decide_eq_true_eq] using hCheck
  | cons C covers ih =>
      simp only [adjacentSixCompactWeightedCoverAtLeastAux] at hCheck
      split at hCheck <;> rename_i hEnough
      · have hMinimum : minimum ≤ total := decide_eq_true_eq.mp hEnough
        simp only [List.map_cons, List.sum_cons]
        omega
      · have hTail := ih hCheck
        simp only [List.map_cons, List.sum_cons]
        omega

theorem adjacentSixCompactWeightedCoverAtLeast_sound {minimum m : Nat}
    (hCheck : adjacentSixCompactWeightedCoverAtLeast minimum m = true) :
    minimum ≤ adjacentSixCompactWeightedCoverCount m := by
  unfold adjacentSixCompactWeightedCoverAtLeast at hCheck
  have h := adjacentSixCompactWeightedCoverAtLeastAux_sound hCheck
  simpa [adjacentSixCompactWeightedCoverCount,
    adjacentSixCompactCoverWeight] using h

end AiMathLab.P0054.AdjacentSixFinite
