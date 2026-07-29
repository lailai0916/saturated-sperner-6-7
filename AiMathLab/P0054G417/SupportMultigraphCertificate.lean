import AiMathLab.P0054G417.SixSupportMultigraphChecks
import AiMathLab.P0054G417.SupportMultigraphEarlyPath

namespace AiMathLab.P0054.G417

set_option maxHeartbeats 8000000 in
-- The early checker is transferred through the dominated target path.
theorem six_support_multigraph_weighted_cover_count_ge_fifteen
    (lowCount : Nat)
    (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20 :
      Nat)
    (hLow : 4 ≤ lowCount) (hHigh : lowCount ≤ 6)
    (hValid : SixMultiplicityValid lowCount
      (sixMultiplicityOfValues m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14
        m15 m16 m17 m18 m19 m20)) :
    15 ≤ sixWeightedCoverCount
      (sixMultiplicityOfValues m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14
        m15 m16 m17 m18 m19 m20) := by
  let multiplicity := sixMultiplicityOfValues m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10
    m11 m12 m13 m14 m15 m16 m17 m18 m19 m20
  change 15 ≤ sixWeightedCoverCount multiplicity
  change SixMultiplicityValid lowCount multiplicity at hValid
  let target : Fin 21 → Fin 4 := fun s ↦
    ⟨sixMultiplicityDigit multiplicity s.val,
      sixMultiplicityDigit_lt_four_of_valid hValid s⟩
  have hTargetMultiplicity : sixMultiplicityOfFunction target = multiplicity := by
    apply Array.ext
    · simp [sixMultiplicityOfFunction, multiplicity, sixMultiplicityOfValues]
    · intro i hiLeft hiRight
      have hi : i < 21 := by
        simpa [multiplicity, sixMultiplicityOfValues] using hiRight
      interval_cases i <;>
        simp [sixMultiplicityOfFunction, target, multiplicity, sixMultiplicityDigit,
          sixMultiplicityOfValues, Array.getD]
  have hTargetValid :
      SixMultiplicityValid lowCount (sixMultiplicityOfFunction target) := by
    rw [hTargetMultiplicity]
    exact hValid
  have hTargetBound :
      15 ≤ sixWeightedCoverCount (sixMultiplicityOfFunction target) := by
    have hLowCount : lowCount = 4 ∨ lowCount = 5 ∨ lowCount = 6 := by omega
    rcases hLowCount with hLowCount | hLowCount | hLowCount
    · subst lowCount
      obtain ⟨finalCount, hGenerated⟩ :=
        sixEarlyGeneratedDominated_four target hTargetValid
      have hCount := sixSupportMultigraphEarlyCheckAux_sound hGenerated.generated
        six_support_multigraph_early_check_4
        (sixCompactStateValid_of_valid target hTargetValid)
      have hCountLe : finalCount ≤
          sixCompletionGroupsValue (sixCompactEncodeMultiplicity target)
            sixCompletionGroups4 := by
        simpa using hGenerated.count_le
      exact hCount.trans
        (hCountLe.trans (sixCompletionGroups4_value_le_weightedCoverCount target))
    · subst lowCount
      obtain ⟨finalCount, hGenerated⟩ :=
        sixEarlyGeneratedDominated_five target hTargetValid
      have hCount := sixSupportMultigraphEarlyCheckAux_sound hGenerated.generated
        six_support_multigraph_early_check_5
        (sixCompactStateValid_of_valid target hTargetValid)
      have hCountLe : finalCount ≤
          sixCompletionGroupsValue (sixCompactEncodeMultiplicity target)
            sixCompletionGroups5 := by
        simpa using hGenerated.count_le
      exact hCount.trans
        (hCountLe.trans (sixCompletionGroups5_value_le_weightedCoverCount target))
    · subst lowCount
      obtain ⟨finalCount, hGenerated⟩ :=
        sixEarlyGeneratedDominated_six target hTargetValid
      have hCount := sixSupportMultigraphEarlyCheckAux_sound hGenerated.generated
        six_support_multigraph_early_check_6
        (sixCompactStateValid_of_valid target hTargetValid)
      have hCountLe : finalCount ≤
          sixCompletionGroupsValue (sixCompactEncodeMultiplicity target)
            sixCompletionGroups6 := by
        simpa using hGenerated.count_le
      exact hCount.trans
        (hCountLe.trans (sixCompletionGroups6_value_le_weightedCoverCount target))
  rwa [hTargetMultiplicity] at hTargetBound

end AiMathLab.P0054.G417
