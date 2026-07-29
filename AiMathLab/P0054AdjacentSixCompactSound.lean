import AiMathLab.P0054AdjacentSixCompactBridge

/-!
# Soundness of the adjacent six-row exhaustive check

Every typed multiplicity vector satisfying the adjacent degree conditions and
excluding a positive three-support cover follows one branch of the checked
search tree.  The resulting weighted minimal-cover count is at least six.
-/

namespace AiMathLab.P0054.AdjacentSixFinite

open AiMathLab.P0054.G417

theorem adjacentSixCompactDegreeValid_of_valid {lowCount : Nat}
    (target : Fin 21 → Fin 3)
    (hValid : AdjacentSixMultiplicityValid lowCount
      (adjacentSixMultiplicityOfFunction target)) :
    adjacentSixCompactDegreeValidBool lowCount
      (adjacentSixCompactEncodeDegrees target) = true := by
  simp only [adjacentSixCompactDegreeValidBool, List.all_eq_true, List.mem_range]
  intro v hvSix
  have hTarget := hValid.1 (⟨v, hvSix⟩ : SixVertex)
  rw [adjacentSixSupportDegree_function] at hTarget
  rw [adjacentSixCompactDegreeDigit_encode_nat target hvSix]
  simpa [decide_eq_true_eq] using hTarget

theorem adjacentSixCompactNoThree_of_noThree (target : Fin 21 → Fin 3)
    (hNoThree : AdjacentSixNoThreeCover
      (adjacentSixMultiplicityOfFunction target)) :
    AdjacentSixCompactNoThreeCover (adjacentSixCompactEncode target) := by
  intro C hC hLength
  obtain ⟨s, hsC, hsZero⟩ := hNoThree C hC hLength
  refine ⟨s, hsC, ?_⟩
  simpa using hsZero

set_option maxRecDepth 1000000 in
theorem adjacentSix_first_fifteen_cover_length_three :
    ∀ C ∈ sixMinimalSupportCovers.take 15, C.length = 3 := by
  decide

theorem adjacentSixCompactNoThreePossible_of_noThree
    {lowCount : Nat} (target : Fin 21 → Fin 3)
    (hNoThree : AdjacentSixNoThreeCover
      (adjacentSixMultiplicityOfFunction target))
    (processed : Finset (Fin 21)) (order : List (Fin 21)) :
    adjacentSixCompactNoThreePossibleBool lowCount
      (adjacentSixCompactEncode (adjacentSixRestrict target processed))
      (order.map Fin.val) = true := by
  unfold adjacentSixCompactNoThreePossibleBool
  split
  · rfl
  · simp only [List.all_eq_true]
    intro C hC
    have hCover : C ∈ sixMinimalSupportCovers :=
      List.mem_of_mem_take hC
    have hLength : C.length = 3 :=
      adjacentSix_first_fifteen_cover_length_three C hC
    obtain ⟨s, hsC, hsZero⟩ := hNoThree C hCover hLength
    apply Bool.or_eq_true_iff.mpr
    right
    apply List.any_eq_true.mpr
    refine ⟨s, hsC, ?_⟩
    simp only [decide_eq_true_eq]
    rw [adjacentSixCompactMultiplicityDigit_encode]
    have hTargetZero : target s = 0 := by
      apply Fin.ext
      simpa using hsZero
    simp [adjacentSixRestrict, hTargetZero]

theorem adjacentSixFunctionDegree_restrict_eq_of_sealed
    (target : Fin 21 → Fin 3) (processed : Finset (Fin 21))
    (order : List (Fin 21))
    (hCovered : ∀ s, target s ≠ 0 → s ∉ processed → s ∈ order)
    (v : Nat)
    (hSealed : (order.map Fin.val).any (fun s ↦ sixSupportContains s v) = false) :
    adjacentSixFunctionDegree (adjacentSixRestrict target processed) v =
      adjacentSixFunctionDegree target v := by
  unfold adjacentSixFunctionDegree
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hContains : sixSupportContains s.val v = true
  · simp only [hContains, if_true]
    by_cases hProcessed : s ∈ processed
    · simp [adjacentSixRestrict, hProcessed]
    · have hZero : target s = 0 := by
        by_contra hNonzero
        have hsOrder := hCovered s hNonzero hProcessed
        have hAny : (order.map Fin.val).any
            (fun t ↦ sixSupportContains t v) = true := by
          apply List.any_eq_true.mpr
          refine ⟨s.val, ?_, hContains⟩
          exact List.mem_map.mpr ⟨s, hsOrder, rfl⟩
        rw [hAny] at hSealed
        contradiction
      simp [adjacentSixRestrict, hProcessed, hZero]
  · simp [Bool.eq_false_of_not_eq_true hContains]

theorem adjacentSixCompactSealedValid_of_valid
    {lowCount : Nat} (hHigh : lowCount ≤ 6) (target : Fin 21 → Fin 3)
    (hValid : AdjacentSixMultiplicityValid lowCount
      (adjacentSixMultiplicityOfFunction target))
    (processed : Finset (Fin 21)) (order : List (Fin 21))
    (hCovered : ∀ s, target s ≠ 0 → s ∉ processed → s ∈ order) :
    adjacentSixCompactSealedValidBool lowCount
      (adjacentSixCompactEncodeDegrees (adjacentSixRestrict target processed))
      (order.map Fin.val) = true := by
  simp only [adjacentSixCompactSealedValidBool, List.all_eq_true, List.mem_range]
  intro v hvLow
  split <;> rename_i hAny
  · rfl
  · simp only [decide_eq_true_eq]
    have hvSix : v < 6 := lt_of_lt_of_le hvLow hHigh
    rw [adjacentSixCompactDegreeDigit_encode_nat _ hvSix]
    rw [adjacentSixFunctionDegree_restrict_eq_of_sealed target processed order
      hCovered v (Bool.eq_false_of_not_eq_true hAny)]
    have hTarget := hValid.1 (⟨v, hvSix⟩ : SixVertex)
    rw [if_pos hvLow, adjacentSixSupportDegree_function] at hTarget
    exact hTarget

theorem adjacentSixCompactChoice_of_valid
    {lowCount : Nat} (hHigh : lowCount ≤ 6) (target : Fin 21 → Fin 3)
    (hValid : AdjacentSixMultiplicityValid lowCount
      (adjacentSixMultiplicityOfFunction target))
    (processed : Finset (Fin 21)) (s : Fin 21) (hs : s ∉ processed) :
    (target s).val ∈ adjacentSixCompactChoices lowCount
      (adjacentSixCompactEncodeDegrees (adjacentSixRestrict target processed)) s.val := by
  simp only [adjacentSixCompactChoices, List.mem_filter, List.mem_range]
  refine ⟨(target s).isLt, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · by_cases hZero : target s = 0
    · simp [hZero]
    · have hPositive : 0 < sixMultiplicityDigit
          (adjacentSixMultiplicityOfFunction target) s.val := by
        rw [adjacentSixMultiplicityOfFunction_digit]
        exact Nat.pos_of_ne_zero (by simpa using hZero)
      have hTouch := AiMathLab.P0054.G417.sixSupportTouchesLowBool_true
        (hValid.2 s hPositive)
      simp [hTouch]
  · simp only [List.all_eq_true, List.mem_range]
    intro v hvLow
    by_cases hContains : sixSupportContains s.val v = true
    · simp only [hContains, Bool.not_true, Bool.false_or, decide_eq_true_eq]
      have hvSix : v < 6 := lt_of_lt_of_le hvLow hHigh
      have hTarget := hValid.1 (⟨v, hvSix⟩ : SixVertex)
      rw [if_pos hvLow, adjacentSixSupportDegree_function] at hTarget
      have hAfter := adjacentSixFunctionDegree_mono
        (adjacentSixRestrict_le target (insert s processed)) v
      rw [← adjacentSixRestrict_update target processed s] at hAfter
      rw [adjacentSixFunctionDegree_update _ s (target s)
        (adjacentSixRestrict_zero target processed hs) v,
        hContains, if_pos rfl] at hAfter
      rw [hTarget] at hAfter
      rw [adjacentSixCompactDegreeDigit_encode_nat _ hvSix]
      exact hAfter
    · simp [Bool.eq_false_of_not_eq_true hContains]

theorem adjacentSixCompactCheckAux_sound_target
    {lowCount minimum : Nat} (hHigh : lowCount ≤ 6)
    (target : Fin 21 → Fin 3)
    (hValid : AdjacentSixMultiplicityValid lowCount
      (adjacentSixMultiplicityOfFunction target))
    (hNoThree : AdjacentSixNoThreeCover
      (adjacentSixMultiplicityOfFunction target))
    (processed : Finset (Fin 21)) (order : List (Fin 21))
    (hNodup : order.Nodup)
    (hFresh : ∀ s ∈ order, s ∉ processed)
    (hCovered : ∀ s, target s ≠ 0 → s ∉ processed → s ∈ order)
    (hCheck : adjacentSixCompactCheckAux lowCount minimum (order.map Fin.val)
      (adjacentSixCompactEncode (adjacentSixRestrict target processed))
      (adjacentSixCompactEncodeDegrees
        (adjacentSixRestrict target processed)) = true) :
    minimum ≤ sixWeightedCoverCount (adjacentSixMultiplicityOfFunction target) := by
  induction order generalizing processed with
  | nil =>
      have hRestrict : adjacentSixRestrict target processed = target := by
        funext s
        by_cases hProcessed : s ∈ processed
        · simp [adjacentSixRestrict, hProcessed]
        · have hZero : target s = 0 := by
            by_contra hNonzero
            exact (by simpa using hCovered s hNonzero hProcessed)
          simp [adjacentSixRestrict, hProcessed, hZero]
      have hDegree := adjacentSixCompactDegreeValid_of_valid target hValid
      have hNoThreeCompact := adjacentSixCompactNoThree_of_noThree target hNoThree
      have hTerminal : adjacentSixCompactWeightedCoverAtLeast minimum
          (adjacentSixCompactEncode target) = true := by
        simpa [hRestrict, adjacentSixCompactCheckAux, hDegree,
          hNoThreeCompact, decide_eq_true_eq] using hCheck
      have hLower := adjacentSixCompactWeightedCoverAtLeast_sound hTerminal
      simpa [adjacentSixCompactWeightedCoverCount_encode] using hLower
  | cons s order ih =>
      have hParts := List.nodup_cons.mp hNodup
      have hs : s ∉ processed := hFresh s (by simp)
      have hFreshTail : ∀ t ∈ order, t ∉ insert s processed := by
        intro t ht
        simp only [Finset.mem_insert, not_or]
        refine ⟨?_, hFresh t (by simp [ht])⟩
        intro hts
        subst t
        exact hParts.1 ht
      have hCoveredTail :
          ∀ t, target t ≠ 0 → t ∉ insert s processed → t ∈ order := by
        intro t hNonzero hNot
        have hNotProcessed : t ∉ processed := by
          intro ht
          exact hNot (Finset.mem_insert_of_mem ht)
        have ht := hCovered t hNonzero hNotProcessed
        rcases List.mem_cons.mp ht with hts | ht
        · subst t
          exact False.elim (hNot (Finset.mem_insert_self s processed))
        · exact ht
      have hSealed := adjacentSixCompactSealedValid_of_valid hHigh target hValid
        processed (s :: order) hCovered
      have hPossible := adjacentSixCompactNoThreePossible_of_noThree
        (lowCount := lowCount) target hNoThree processed (s :: order)
      have hChoice := adjacentSixCompactChoice_of_valid hHigh target hValid processed s hs
      have hGuard :
          (adjacentSixCompactSealedValidBool lowCount
              (adjacentSixCompactEncodeDegrees
                (adjacentSixRestrict target processed))
              (s.val :: order.map Fin.val) &&
            adjacentSixCompactNoThreePossibleBool lowCount
              (adjacentSixCompactEncode (adjacentSixRestrict target processed))
              (s.val :: order.map Fin.val)) = true := by
        apply Bool.and_eq_true_iff.mpr
        exact ⟨by simpa using hSealed, by simpa using hPossible⟩
      have hAll :
          (adjacentSixCompactChoices lowCount
            (adjacentSixCompactEncodeDegrees
              (adjacentSixRestrict target processed)) s.val).all (fun k ↦
              adjacentSixCompactCheckAux lowCount minimum (order.map Fin.val)
                (adjacentSixCompactEncode (adjacentSixRestrict target processed) +
                  k * 3 ^ s.val)
                (adjacentSixCompactAddDegree
                  (adjacentSixCompactEncodeDegrees
                    (adjacentSixRestrict target processed)) s.val k)) = true := by
        simp only [List.map_cons, adjacentSixCompactCheckAux] at hCheck
        rw [hGuard] at hCheck
        exact hCheck
      have hBranch := (List.all_eq_true.mp hAll) (target s).val hChoice
      have hEncoded := adjacentSixCompactEncodeRestrict_update target processed hs
      have hDegrees := adjacentSixCompactDegreesRestrict_update target processed hs
      rw [hEncoded, hDegrees] at hBranch
      exact ih (insert s processed) hParts.2 hFreshTail hCoveredTail hBranch

def adjacentSixInitialProcessed : Finset (Fin 21) := {0, 1, 2, 3}

def adjacentSixTypedSupportOrder : List (Fin 21) :=
  [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 4, 20, 5]

theorem adjacentSixInitialEncode (target : Fin 21 → Fin 3) :
    adjacentSixCompactEncode (adjacentSixRestrict target adjacentSixInitialProcessed) =
      (target 0).val + 3 * (target 1).val + 9 * (target 2).val + 27 * (target 3).val := by
  rw [adjacentSixCompactEncode_eq_sum]
  simp [adjacentSixRestrict, adjacentSixInitialProcessed, Fin.sum_univ_succ]
  ring

theorem adjacentSixInitialDegrees (target : Fin 21 → Fin 3) :
    adjacentSixCompactEncodeDegrees
        (adjacentSixRestrict target adjacentSixInitialProcessed) =
      (target 0).val + 32 * (target 1).val + 32 ^ 2 * (target 2).val +
        32 ^ 3 * (target 3).val := by
  rw [adjacentSixCompactEncodeDegrees_eq_sum]
  simp [adjacentSixFunctionDegree, adjacentSixRestrict, adjacentSixInitialProcessed,
    Fin.sum_univ_succ, sixSupportContains, sixSupportMask, Nat.testBit]
  ring

set_option maxHeartbeats 2000000 in
-- Selecting the four leading digits and following the typed branch is symbolic.
theorem adjacent_six_compact_check_sound {lowCount : Nat}
    (hLow : 1 ≤ lowCount) (hHigh : lowCount ≤ 6)
    (target : Fin 21 → Fin 3)
    (hValid : AdjacentSixMultiplicityValid lowCount
      (adjacentSixMultiplicityOfFunction target))
    (hNoThree : AdjacentSixNoThreeCover
      (adjacentSixMultiplicityOfFunction target)) :
    6 ≤ sixWeightedCoverCount (adjacentSixMultiplicityOfFunction target) := by
  have hCheck := adjacent_six_check_true hLow hHigh
  have hA : adjacentSixCompactCheckA lowCount (target 0).val = true :=
    (List.all_eq_true.mp hCheck) (target 0).val (List.mem_range.mpr (target 0).isLt)
  have hB : adjacentSixCompactCheckAB lowCount (target 0).val (target 1).val = true :=
    (List.all_eq_true.mp hA) (target 1).val (List.mem_range.mpr (target 1).isLt)
  have hC : (List.range 3).all (fun d ↦
      adjacentSixCompactSubcheck lowCount (target 0).val (target 1).val
        (target 2).val d) = true :=
    (List.all_eq_true.mp hB) (target 2).val (List.mem_range.mpr (target 2).isLt)
  have hSubcheck : adjacentSixCompactSubcheck lowCount
      (target 0).val (target 1).val (target 2).val (target 3).val = true :=
    (List.all_eq_true.mp hC) (target 3).val (List.mem_range.mpr (target 3).isLt)
  have hOrder : adjacentSixTypedSupportOrder.map Fin.val =
      adjacentSixCompactSupportOrder := by rfl
  have hNodup : adjacentSixTypedSupportOrder.Nodup := by decide
  have hFresh : ∀ s ∈ adjacentSixTypedSupportOrder,
      s ∉ adjacentSixInitialProcessed := by decide
  have hCovered : ∀ s, target s ≠ 0 → s ∉ adjacentSixInitialProcessed →
      s ∈ adjacentSixTypedSupportOrder := by
    intro s hNonzero hs
    fin_cases s <;> simp_all [adjacentSixInitialProcessed, adjacentSixTypedSupportOrder]
  have hPathCheck : adjacentSixCompactCheckAux lowCount 6
      (adjacentSixTypedSupportOrder.map Fin.val)
      (adjacentSixCompactEncode
        (adjacentSixRestrict target adjacentSixInitialProcessed))
      (adjacentSixCompactEncodeDegrees
        (adjacentSixRestrict target adjacentSixInitialProcessed)) = true := by
    rw [hOrder, adjacentSixInitialEncode, adjacentSixInitialDegrees]
    simpa [adjacentSixCompactSubcheck] using hSubcheck
  exact adjacentSixCompactCheckAux_sound_target hHigh target hValid hNoThree
    adjacentSixInitialProcessed adjacentSixTypedSupportOrder hNodup hFresh hCovered hPathCheck

end AiMathLab.P0054.AdjacentSixFinite
