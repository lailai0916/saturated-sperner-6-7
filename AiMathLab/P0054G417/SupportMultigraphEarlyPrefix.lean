import AiMathLab.P0054G417.SixSupportMultigraphEarly

namespace AiMathLab.P0054.G417

def sixSupportMultigraphEarlyCheckValues
    (lowCount minimum : Nat) : List Nat → List Nat → List (List Nat) →
      Nat → SixCompactDegrees → Nat → Bool
  | [], supports, groups, m, degrees, count =>
      sixSupportMultigraphEarlyCheckAux lowCount minimum supports groups m degrees count
  | k :: values, s :: supports, group :: groups, m, degrees, count =>
      let nextM := sixCompactSetMultiplicity m s k
      let nextDegrees := sixCompactAddSupportDegree degrees s k
      let nextCount := count + sixCompactCoverGroupValue nextM group
      decide (minimum ≤ nextCount) ||
        !sixCompactDegreeCompletionPossibleBool lowCount supports nextDegrees ||
        sixSupportMultigraphEarlyCheckValues lowCount minimum values supports groups
          nextM nextDegrees nextCount
  | _, _, _, _, _, _ => false

def sixSupportMultigraphEarlyValuesAdmissible
    (lowCount minimum : Nat) : List Nat → List Nat → List (List Nat) →
      Nat → SixCompactDegrees → Nat → Bool
  | [], _, _, _, _, _ => true
  | k :: values, s :: supports, group :: groups, m, degrees, count =>
      let nextM := sixCompactSetMultiplicity m s k
      let nextDegrees := sixCompactAddSupportDegree degrees s k
      let nextCount := count + sixCompactCoverGroupValue nextM group
      decide (k ∈ sixCompactMultiplicityChoices lowCount degrees s) &&
        !decide (minimum ≤ nextCount) &&
        sixCompactDegreeCompletionPossibleBool lowCount supports nextDegrees &&
        sixSupportMultigraphEarlyValuesAdmissible lowCount minimum values supports groups
          nextM nextDegrees nextCount
  | _, _, _, _, _, _ => false

theorem sixSupportMultigraphEarlyCheckAux_of_prefix
    (depth lowCount minimum : Nat) (supports : List Nat) (groups : List (List Nat))
    (m : Nat) (degrees : SixCompactDegrees) (count : Nat)
    (hDepth : depth ≤ supports.length) (hLength : supports.length = groups.length)
    (hPrefixes : ∀ values : List Nat, values.length = depth →
      (∀ k ∈ values, k < 4) →
      sixSupportMultigraphEarlyValuesAdmissible lowCount minimum values supports groups
        m degrees count = true →
      sixSupportMultigraphEarlyCheckValues lowCount minimum values supports groups
        m degrees count = true) :
    sixSupportMultigraphEarlyCheckAux lowCount minimum supports groups m degrees count = true := by
  induction depth generalizing supports groups m degrees count with
  | zero =>
      simpa [sixSupportMultigraphEarlyCheckValues] using
        hPrefixes [] (by rfl) (by simp) (by rfl)
  | succ depth ih =>
      cases supports with
      | nil => simp at hDepth
      | cons s supports =>
          cases groups with
          | nil => simp at hLength
          | cons group groups =>
              simp only [sixSupportMultigraphEarlyCheckAux, List.all_eq_true]
              intro k hChoice
              have hk : k < 4 := by
                simpa [sixCompactMultiplicityChoices] using (List.mem_of_mem_filter hChoice)
              let nextM := sixCompactSetMultiplicity m s k
              let nextDegrees := sixCompactAddSupportDegree degrees s k
              let nextCount := count + sixCompactCoverGroupValue nextM group
              by_cases hReached : minimum ≤ nextCount
              · simp [nextM, nextCount, hReached]
              · by_cases hCompletion :
                    sixCompactDegreeCompletionPossibleBool lowCount supports nextDegrees = true
                · simp only [nextM, nextDegrees, nextCount, hReached, decide_false,
                    Bool.false_or, hCompletion, Bool.not_true]
                  apply ih supports groups nextM nextDegrees nextCount
                  · simp at hDepth
                    omega
                  · simpa using hLength
                  · intro values hValuesLength hValues hAdmissible
                    have hChoiceTrue :
                        decide (k ∈ sixCompactMultiplicityChoices lowCount degrees s) = true :=
                      decide_eq_true hChoice
                    have hAdmissibleCombined :
                        sixSupportMultigraphEarlyValuesAdmissible lowCount minimum
                          (k :: values) (s :: supports) (group :: groups)
                          m degrees count = true := by
                      simp only [sixSupportMultigraphEarlyValuesAdmissible, nextM,
                        nextDegrees, nextCount, hChoiceTrue, Bool.true_and, hReached,
                        decide_false, Bool.not_false, hCompletion]
                      exact hAdmissible
                    have hCombined := hPrefixes (k :: values) (by simp [hValuesLength])
                      (by
                        intro value hValue
                        rcases List.mem_cons.mp hValue with rfl | hValue
                        · exact hk
                        · exact hValues value hValue)
                      hAdmissibleCombined
                    simpa [sixSupportMultigraphEarlyCheckValues, nextM, nextDegrees,
                      nextCount, hReached, hCompletion] using hCombined
                · have hCompletionFalse :
                      sixCompactDegreeCompletionPossibleBool lowCount supports nextDegrees =
                        false := Bool.eq_false_of_not_eq_true hCompletion
                  simp [nextM, nextDegrees, nextCount, hReached, hCompletionFalse]

end AiMathLab.P0054.G417
