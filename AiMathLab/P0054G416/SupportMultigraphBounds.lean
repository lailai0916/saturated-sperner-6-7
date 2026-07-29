import AiMathLab.P0054G416.SupportMultigraphBridge

namespace AiMathLab.P0054.G416

theorem fiveMultiplicityChoice_of_bounds {lowCount s k : Nat} {degrees : FiveDegreeState}
    (hk : k < 4)
    (hTouch : k = 0 ∨ fiveSupportTouchesLowBool lowCount s = true)
    (hCap : ∀ v < lowCount, fiveSupportContains s v = true →
      degrees.getD v 0 + k ≤ 3) :
    k ∈ fiveMultiplicityChoices lowCount degrees s := by
  simp only [fiveMultiplicityChoices, List.mem_filter, List.mem_range]
  refine ⟨hk, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · rcases hTouch with rfl | hTouch
    · simp
    · simp [hTouch]
  · simp only [List.all_eq_true, List.mem_range]
    intro v hv
    by_cases hContains : fiveSupportContains s v = true
    · simp only [hContains, Bool.not_true, Bool.false_or, decide_eq_true_eq]
      exact hCap v hv hContains
    · have hFalse : fiveSupportContains s v = false := Bool.eq_false_of_not_eq_true hContains
      simp [hFalse]

theorem fiveGenerated_lowThree_of_values
    (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 : Nat)
    (h0 : m0 + m5 + m6 + m7 + m8 = 3)
    (h1 : m1 + m5 + m9 + m10 + m11 = 3)
    (h2 : m2 + m6 + m9 + m12 + m13 = 3)
    (hm3 : m3 = 0) (hm4 : m4 = 0) (hm14 : m14 = 0) :
    FiveGenerated 3 ((List.range 15).drop 3)
      (fiveMultiplicityAfterThree m0 m1 m2) (fiveDegreeStateAfterThree m0 m1 m2)
      (fiveMultiplicityOfValues m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14)
      (fiveDegreeStateOfValues m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14) := by
  norm_num [List.range, List.drop]
  apply FiveGenerated.cons (k := m3)
  · apply fiveMultiplicityChoice_of_bounds
    · omega
    · exact Or.inl hm3
    · intro v hv hContains
      interval_cases v <;>
        simp [fiveDegreeStateAfterThree, fiveSupportContains, fiveSupportMask,
          Array.getD, Nat.testBit] at * <;>
        omega
  apply FiveGenerated.cons (k := m4)
  · apply fiveMultiplicityChoice_of_bounds
    · omega
    · exact Or.inl hm4
    · intro v hv hContains
      interval_cases v <;>
        simp [fiveDegreeStateAfterThree, addFiveSupportDegree, fiveSupportContains,
          fiveSupportMask, Array.getD, Nat.testBit] at * <;>
        omega
  apply FiveGenerated.cons (k := m5)
  · apply fiveMultiplicityChoice_of_bounds
    · omega
    · exact Or.inr rfl
    · intro v hv hContains
      interval_cases v <;>
        simp [fiveDegreeStateAfterThree, addFiveSupportDegree, fiveSupportContains,
          fiveSupportMask, Array.getD, Nat.testBit] at * <;>
        omega
  apply FiveGenerated.cons (k := m6)
  · apply fiveMultiplicityChoice_of_bounds
    · omega
    · exact Or.inr rfl
    · intro v hv hContains
      interval_cases v <;>
        simp [fiveDegreeStateAfterThree, addFiveSupportDegree, fiveSupportContains,
          fiveSupportMask, Array.getD, Nat.testBit] at * <;>
        omega
  apply FiveGenerated.cons (k := m7)
  · apply fiveMultiplicityChoice_of_bounds
    · omega
    · exact Or.inr rfl
    · intro v hv hContains
      interval_cases v <;>
        simp [fiveDegreeStateAfterThree, addFiveSupportDegree, fiveSupportContains,
          fiveSupportMask, Array.getD, Nat.testBit] at * <;>
        omega
  apply FiveGenerated.cons (k := m8)
  · apply fiveMultiplicityChoice_of_bounds
    · omega
    · exact Or.inr rfl
    · intro v hv hContains
      interval_cases v <;>
        simp [fiveDegreeStateAfterThree, addFiveSupportDegree, fiveSupportContains,
          fiveSupportMask, Array.getD, Nat.testBit] at * <;>
        omega
  apply FiveGenerated.cons (k := m9)
  · apply fiveMultiplicityChoice_of_bounds
    · omega
    · exact Or.inr rfl
    · intro v hv hContains
      interval_cases v <;>
        simp [fiveDegreeStateAfterThree, addFiveSupportDegree, fiveSupportContains,
          fiveSupportMask, Array.getD, Nat.testBit] at * <;>
        omega
  apply FiveGenerated.cons (k := m10)
  · apply fiveMultiplicityChoice_of_bounds
    · omega
    · exact Or.inr rfl
    · intro v hv hContains
      interval_cases v <;>
        simp [fiveDegreeStateAfterThree, addFiveSupportDegree, fiveSupportContains,
          fiveSupportMask, Array.getD, Nat.testBit] at * <;>
        omega
  apply FiveGenerated.cons (k := m11)
  · apply fiveMultiplicityChoice_of_bounds
    · omega
    · exact Or.inr rfl
    · intro v hv hContains
      interval_cases v <;>
        simp [fiveDegreeStateAfterThree, addFiveSupportDegree, fiveSupportContains,
          fiveSupportMask, Array.getD, Nat.testBit] at * <;>
        omega
  apply FiveGenerated.cons (k := m12)
  · apply fiveMultiplicityChoice_of_bounds
    · omega
    · exact Or.inr rfl
    · intro v hv hContains
      interval_cases v <;>
        simp [fiveDegreeStateAfterThree, addFiveSupportDegree, fiveSupportContains,
          fiveSupportMask, Array.getD, Nat.testBit] at * <;>
        omega
  apply FiveGenerated.cons (k := m13)
  · apply fiveMultiplicityChoice_of_bounds
    · omega
    · exact Or.inr rfl
    · intro v hv hContains
      interval_cases v <;>
        simp [fiveDegreeStateAfterThree, addFiveSupportDegree, fiveSupportContains,
          fiveSupportMask, Array.getD, Nat.testBit] at * <;>
        omega
  apply FiveGenerated.cons (k := m14)
  · apply fiveMultiplicityChoice_of_bounds
    · omega
    · exact Or.inl hm14
    · intro v hv hContains
      interval_cases v <;>
        simp [fiveDegreeStateAfterThree, addFiveSupportDegree, fiveSupportContains,
          fiveSupportMask, Array.getD, Nat.testBit] at * <;>
        omega
  rw [fiveMultiplicityAfterThree_set_remaining, fiveDegreeStateAfterThree_add_remaining]
  exact FiveGenerated.nil _ _

theorem five_support_multigraph_low_three_of_values
    (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 : Nat)
    (hValid : FiveMultiplicityValid 3
      (fiveMultiplicityOfValues m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14)) :
    19 ≤ fiveWeightedCoverCount
      (fiveMultiplicityOfValues m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14) := by
  have h0 := hValid.1 (0 : FiveVertex)
  have h1 := hValid.1 (1 : FiveVertex)
  have h2 := hValid.1 (2 : FiveVertex)
  have h3 := hValid.1 (3 : FiveVertex)
  have h4 := hValid.1 (4 : FiveVertex)
  simp [fiveSupportDegree, fiveMultiplicityDigit, fiveMultiplicityOfValues, fiveSupport,
    Fin.sum_univ_succ, Nat.add_assoc] at h0 h1 h2 h3 h4
  have hm3 : m3 = 0 := by
    have h := hValid.2 (3 : FiveSupportIndex)
    simp [fiveMultiplicityDigit, fiveMultiplicityOfValues, fiveSupportTouchesLow,
      fiveSupport] at h
    omega
  have hm4 : m4 = 0 := by
    have h := hValid.2 (4 : FiveSupportIndex)
    simp [fiveMultiplicityDigit, fiveMultiplicityOfValues, fiveSupportTouchesLow,
      fiveSupport] at h
    omega
  have hm14 : m14 = 0 := by
    have h := hValid.2 (14 : FiveSupportIndex)
    simp [fiveMultiplicityDigit, fiveMultiplicityOfValues, fiveSupportTouchesLow,
      fiveSupport] at h
    omega
  have hm0 : m0 < 4 := by omega
  have hm1 : m1 < 4 := by omega
  have hm2 : m2 < 4 := by omega
  have h0' : m0 + m5 + m6 + m7 + m8 = 3 := by omega
  have h1' : m1 + m5 + m9 + m10 + m11 = 3 := by omega
  have h2' : m2 + m6 + m9 + m12 + m13 = 3 := by omega
  have hGenerated := fiveGenerated_lowThree_of_values
    m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14
    h0' h1' h2' hm3 hm4 hm14
  have hCheck := five_support_multigraph_low_three_subcheck_all
    ⟨m0, hm0⟩ ⟨m1, hm1⟩ ⟨m2, hm2⟩
  have hFinal : fiveDegreeStateValidBool 3
      (fiveDegreeStateOfValues m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14) =
      true := by
    simp only [fiveDegreeStateValidBool, List.all_eq_true, List.mem_range]
    intro v hv
    interval_cases v <;>
      simp [fiveDegreeStateOfValues, Array.getD] <;>
      omega
  exact fiveSupportMultigraphCheckAux_sound hGenerated hCheck hFinal

theorem fiveMultiplicityAfterFour_set_remaining
    (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 : Nat) :
    (((((((((((fiveMultiplicityAfterFour m0 m1 m2 m3).set! 4 m4).set! 5 m5).set! 6 m6).set! 7 m7).set! 8 m8).set! 9 m9).set! 10 m10).set! 11 m11).set! 12 m12).set! 13 m13).set! 14 m14 =
      fiveMultiplicityOfValues m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 := by
  simpa [fiveMultiplicityAfterFour, fiveMultiplicityAfterThree] using
    fiveMultiplicityAfterThree_set_remaining
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14

set_option maxHeartbeats 2000000 in
-- The alias reduction expands the fixed fourth-loop degree update.
theorem fiveDegreeStateAfterFour_add_remaining
    (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 : Nat) :
    addFiveSupportDegree
      (addFiveSupportDegree
        (addFiveSupportDegree
          (addFiveSupportDegree
            (addFiveSupportDegree
              (addFiveSupportDegree
                (addFiveSupportDegree
                  (addFiveSupportDegree
                    (addFiveSupportDegree
                      (addFiveSupportDegree
                        (addFiveSupportDegree (fiveDegreeStateAfterFour m0 m1 m2 m3) 4 m4)
                          5 m5) 6 m6) 7 m7) 8 m8) 9 m9) 10 m10) 11 m11) 12 m12) 13 m13)
      14 m14 =
      fiveDegreeStateOfValues m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 := by
  apply Array.ext
  · simp [fiveDegreeStateAfterFour, addFiveSupportDegree, fiveDegreeStateOfValues]
  · intro i hiLeft hiRight
    have hi : i < 5 := by
      simpa [fiveDegreeStateOfValues] using hiRight
    interval_cases i <;>
      simp [fiveDegreeStateAfterFour, addFiveSupportDegree, fiveSupportContains,
        fiveSupportMask, fiveDegreeStateOfValues, Array.getD, Nat.testBit]

theorem fiveGenerated_lowFour_of_values
    (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 : Nat)
    (h0 : m0 + m5 + m6 + m7 + m8 = 3)
    (h1 : m1 + m5 + m9 + m10 + m11 = 3)
    (h2 : m2 + m6 + m9 + m12 + m13 = 3)
    (h3 : m3 + m7 + m10 + m12 + m14 = 3)
    (hm4 : m4 = 0) :
    FiveGenerated 4 ((List.range 15).drop 4)
      (fiveMultiplicityAfterFour m0 m1 m2 m3) (fiveDegreeStateAfterFour m0 m1 m2 m3)
      (fiveMultiplicityOfValues m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14)
      (fiveDegreeStateOfValues m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14) := by
  norm_num [List.range, List.drop]
  apply FiveGenerated.cons (k := m4)
  · apply fiveMultiplicityChoice_of_bounds
    · omega
    · exact Or.inl hm4
    · intro v hv hContains
      interval_cases v <;>
        simp [fiveDegreeStateAfterFour, fiveSupportContains, fiveSupportMask,
          Array.getD, Nat.testBit] at * <;>
        omega
  apply FiveGenerated.cons (k := m5)
  · apply fiveMultiplicityChoice_of_bounds
    · omega
    · exact Or.inr rfl
    · intro v hv hContains
      interval_cases v <;>
        simp [fiveDegreeStateAfterFour, addFiveSupportDegree, fiveSupportContains,
          fiveSupportMask, Array.getD, Nat.testBit] at * <;>
        omega
  apply FiveGenerated.cons (k := m6)
  · apply fiveMultiplicityChoice_of_bounds
    · omega
    · exact Or.inr rfl
    · intro v hv hContains
      interval_cases v <;>
        simp [fiveDegreeStateAfterFour, addFiveSupportDegree, fiveSupportContains,
          fiveSupportMask, Array.getD, Nat.testBit] at * <;>
        omega
  apply FiveGenerated.cons (k := m7)
  · apply fiveMultiplicityChoice_of_bounds
    · omega
    · exact Or.inr rfl
    · intro v hv hContains
      interval_cases v <;>
        simp [fiveDegreeStateAfterFour, addFiveSupportDegree, fiveSupportContains,
          fiveSupportMask, Array.getD, Nat.testBit] at * <;>
        omega
  apply FiveGenerated.cons (k := m8)
  · apply fiveMultiplicityChoice_of_bounds
    · omega
    · exact Or.inr rfl
    · intro v hv hContains
      interval_cases v <;>
        simp [fiveDegreeStateAfterFour, addFiveSupportDegree, fiveSupportContains,
          fiveSupportMask, Array.getD, Nat.testBit] at * <;>
        omega
  apply FiveGenerated.cons (k := m9)
  · apply fiveMultiplicityChoice_of_bounds
    · omega
    · exact Or.inr rfl
    · intro v hv hContains
      interval_cases v <;>
        simp [fiveDegreeStateAfterFour, addFiveSupportDegree, fiveSupportContains,
          fiveSupportMask, Array.getD, Nat.testBit] at * <;>
        omega
  apply FiveGenerated.cons (k := m10)
  · apply fiveMultiplicityChoice_of_bounds
    · omega
    · exact Or.inr rfl
    · intro v hv hContains
      interval_cases v <;>
        simp [fiveDegreeStateAfterFour, addFiveSupportDegree, fiveSupportContains,
          fiveSupportMask, Array.getD, Nat.testBit] at * <;>
        omega
  apply FiveGenerated.cons (k := m11)
  · apply fiveMultiplicityChoice_of_bounds
    · omega
    · exact Or.inr rfl
    · intro v hv hContains
      interval_cases v <;>
        simp [fiveDegreeStateAfterFour, addFiveSupportDegree, fiveSupportContains,
          fiveSupportMask, Array.getD, Nat.testBit] at * <;>
        omega
  apply FiveGenerated.cons (k := m12)
  · apply fiveMultiplicityChoice_of_bounds
    · omega
    · exact Or.inr rfl
    · intro v hv hContains
      interval_cases v <;>
        simp [fiveDegreeStateAfterFour, addFiveSupportDegree, fiveSupportContains,
          fiveSupportMask, Array.getD, Nat.testBit] at * <;>
        omega
  apply FiveGenerated.cons (k := m13)
  · apply fiveMultiplicityChoice_of_bounds
    · omega
    · exact Or.inr rfl
    · intro v hv hContains
      interval_cases v <;>
        simp [fiveDegreeStateAfterFour, addFiveSupportDegree, fiveSupportContains,
          fiveSupportMask, Array.getD, Nat.testBit] at * <;>
        omega
  apply FiveGenerated.cons (k := m14)
  · apply fiveMultiplicityChoice_of_bounds
    · omega
    · exact Or.inr rfl
    · intro v hv hContains
      interval_cases v <;>
        simp [fiveDegreeStateAfterFour, addFiveSupportDegree, fiveSupportContains,
          fiveSupportMask, Array.getD, Nat.testBit] at * <;>
        omega
  rw [fiveMultiplicityAfterFour_set_remaining, fiveDegreeStateAfterFour_add_remaining]
  exact FiveGenerated.nil _ _

theorem five_support_multigraph_low_four_of_values
    (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 : Nat)
    (hValid : FiveMultiplicityValid 4
      (fiveMultiplicityOfValues m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14)) :
    16 ≤ fiveWeightedCoverCount
      (fiveMultiplicityOfValues m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14) := by
  have h0 := hValid.1 (0 : FiveVertex)
  have h1 := hValid.1 (1 : FiveVertex)
  have h2 := hValid.1 (2 : FiveVertex)
  have h3 := hValid.1 (3 : FiveVertex)
  have h4 := hValid.1 (4 : FiveVertex)
  simp [fiveSupportDegree, fiveMultiplicityDigit, fiveMultiplicityOfValues, fiveSupport,
    Fin.sum_univ_succ] at h0 h1 h2 h3 h4
  have hm4 : m4 = 0 := by
    have h := hValid.2 (4 : FiveSupportIndex)
    simp [fiveMultiplicityDigit, fiveMultiplicityOfValues, fiveSupportTouchesLow,
      fiveSupport] at h
    omega
  have hm0 : m0 < 4 := by omega
  have hm1 : m1 < 4 := by omega
  have hm2 : m2 < 4 := by omega
  have hm3 : m3 < 4 := by omega
  have h0' : m0 + m5 + m6 + m7 + m8 = 3 := by omega
  have h1' : m1 + m5 + m9 + m10 + m11 = 3 := by omega
  have h2' : m2 + m6 + m9 + m12 + m13 = 3 := by omega
  have h3' : m3 + m7 + m10 + m12 + m14 = 3 := by omega
  have hGenerated := fiveGenerated_lowFour_of_values
    m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14
    h0' h1' h2' h3' hm4
  have hCheck := five_support_multigraph_low_four_subcheck_all
    ⟨m0, hm0⟩ ⟨m1, hm1⟩ ⟨m2, hm2⟩ ⟨m3, hm3⟩
  have hFinal : fiveDegreeStateValidBool 4
      (fiveDegreeStateOfValues m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14) =
      true := by
    simp only [fiveDegreeStateValidBool, List.all_eq_true, List.mem_range]
    intro v hv
    interval_cases v <;>
      simp [fiveDegreeStateOfValues, Array.getD] <;>
      omega
  exact fiveSupportMultigraphCheckAux_sound hGenerated hCheck hFinal

set_option maxHeartbeats 2000000 in
-- The fifth low vertex adds one interval branch to every fixed support step.
theorem fiveGenerated_lowFive_of_values
    (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 : Nat)
    (h0 : m0 + m5 + m6 + m7 + m8 = 3)
    (h1 : m1 + m5 + m9 + m10 + m11 = 3)
    (h2 : m2 + m6 + m9 + m12 + m13 = 3)
    (h3 : m3 + m7 + m10 + m12 + m14 = 3)
    (h4 : m4 + m8 + m11 + m13 + m14 = 3) :
    FiveGenerated 5 ((List.range 15).drop 4)
      (fiveMultiplicityAfterFour m0 m1 m2 m3) (fiveDegreeStateAfterFour m0 m1 m2 m3)
      (fiveMultiplicityOfValues m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14)
      (fiveDegreeStateOfValues m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14) := by
  norm_num [List.range, List.drop]
  apply FiveGenerated.cons (k := m4)
  · apply fiveMultiplicityChoice_of_bounds
    · omega
    · exact Or.inr rfl
    · intro v hv hContains
      interval_cases v <;>
        simp [fiveDegreeStateAfterFour, fiveSupportContains, fiveSupportMask,
          Array.getD, Nat.testBit] at * <;>
        omega
  apply FiveGenerated.cons (k := m5)
  · apply fiveMultiplicityChoice_of_bounds
    · omega
    · exact Or.inr rfl
    · intro v hv hContains
      interval_cases v <;>
        simp [fiveDegreeStateAfterFour, addFiveSupportDegree, fiveSupportContains,
          fiveSupportMask, Array.getD, Nat.testBit] at * <;>
        omega
  apply FiveGenerated.cons (k := m6)
  · apply fiveMultiplicityChoice_of_bounds
    · omega
    · exact Or.inr rfl
    · intro v hv hContains
      interval_cases v <;>
        simp [fiveDegreeStateAfterFour, addFiveSupportDegree, fiveSupportContains,
          fiveSupportMask, Array.getD, Nat.testBit] at * <;>
        omega
  apply FiveGenerated.cons (k := m7)
  · apply fiveMultiplicityChoice_of_bounds
    · omega
    · exact Or.inr rfl
    · intro v hv hContains
      interval_cases v <;>
        simp [fiveDegreeStateAfterFour, addFiveSupportDegree, fiveSupportContains,
          fiveSupportMask, Array.getD, Nat.testBit] at * <;>
        omega
  apply FiveGenerated.cons (k := m8)
  · apply fiveMultiplicityChoice_of_bounds
    · omega
    · exact Or.inr rfl
    · intro v hv hContains
      interval_cases v <;>
        simp [fiveDegreeStateAfterFour, addFiveSupportDegree, fiveSupportContains,
          fiveSupportMask, Array.getD, Nat.testBit] at * <;>
        omega
  apply FiveGenerated.cons (k := m9)
  · apply fiveMultiplicityChoice_of_bounds
    · omega
    · exact Or.inr rfl
    · intro v hv hContains
      interval_cases v <;>
        simp [fiveDegreeStateAfterFour, addFiveSupportDegree, fiveSupportContains,
          fiveSupportMask, Array.getD, Nat.testBit] at * <;>
        omega
  apply FiveGenerated.cons (k := m10)
  · apply fiveMultiplicityChoice_of_bounds
    · omega
    · exact Or.inr rfl
    · intro v hv hContains
      interval_cases v <;>
        simp [fiveDegreeStateAfterFour, addFiveSupportDegree, fiveSupportContains,
          fiveSupportMask, Array.getD, Nat.testBit] at * <;>
        omega
  apply FiveGenerated.cons (k := m11)
  · apply fiveMultiplicityChoice_of_bounds
    · omega
    · exact Or.inr rfl
    · intro v hv hContains
      interval_cases v <;>
        simp [fiveDegreeStateAfterFour, addFiveSupportDegree, fiveSupportContains,
          fiveSupportMask, Array.getD, Nat.testBit] at * <;>
        omega
  apply FiveGenerated.cons (k := m12)
  · apply fiveMultiplicityChoice_of_bounds
    · omega
    · exact Or.inr rfl
    · intro v hv hContains
      interval_cases v <;>
        simp [fiveDegreeStateAfterFour, addFiveSupportDegree, fiveSupportContains,
          fiveSupportMask, Array.getD, Nat.testBit] at * <;>
        omega
  apply FiveGenerated.cons (k := m13)
  · apply fiveMultiplicityChoice_of_bounds
    · omega
    · exact Or.inr rfl
    · intro v hv hContains
      interval_cases v <;>
        simp [fiveDegreeStateAfterFour, addFiveSupportDegree, fiveSupportContains,
          fiveSupportMask, Array.getD, Nat.testBit] at * <;>
        omega
  apply FiveGenerated.cons (k := m14)
  · apply fiveMultiplicityChoice_of_bounds
    · omega
    · exact Or.inr rfl
    · intro v hv hContains
      interval_cases v <;>
        simp [fiveDegreeStateAfterFour, addFiveSupportDegree, fiveSupportContains,
          fiveSupportMask, Array.getD, Nat.testBit] at * <;>
        omega
  rw [fiveMultiplicityAfterFour_set_remaining, fiveDegreeStateAfterFour_add_remaining]
  exact FiveGenerated.nil _ _

theorem five_support_multigraph_low_five_of_values
    (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 : Nat)
    (hValid : FiveMultiplicityValid 5
      (fiveMultiplicityOfValues m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14)) :
    15 ≤ fiveWeightedCoverCount
      (fiveMultiplicityOfValues m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14) := by
  have h0 := hValid.1 (0 : FiveVertex)
  have h1 := hValid.1 (1 : FiveVertex)
  have h2 := hValid.1 (2 : FiveVertex)
  have h3 := hValid.1 (3 : FiveVertex)
  have h4 := hValid.1 (4 : FiveVertex)
  simp [fiveSupportDegree, fiveMultiplicityDigit, fiveMultiplicityOfValues, fiveSupport,
    Fin.sum_univ_succ] at h0 h1 h2 h3 h4
  have hm0 : m0 < 4 := by omega
  have hm1 : m1 < 4 := by omega
  have hm2 : m2 < 4 := by omega
  have hm3 : m3 < 4 := by omega
  have h0' : m0 + m5 + m6 + m7 + m8 = 3 := by omega
  have h1' : m1 + m5 + m9 + m10 + m11 = 3 := by omega
  have h2' : m2 + m6 + m9 + m12 + m13 = 3 := by omega
  have h3' : m3 + m7 + m10 + m12 + m14 = 3 := by omega
  have h4' : m4 + m8 + m11 + m13 + m14 = 3 := by omega
  have hGenerated := fiveGenerated_lowFive_of_values
    m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14
    h0' h1' h2' h3' h4'
  have hCheck := five_support_multigraph_low_five_subcheck_all
    ⟨m0, hm0⟩ ⟨m1, hm1⟩ ⟨m2, hm2⟩ ⟨m3, hm3⟩
  have hFinal : fiveDegreeStateValidBool 5
      (fiveDegreeStateOfValues m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14) =
      true := by
    simp only [fiveDegreeStateValidBool, List.all_eq_true, List.mem_range]
    intro v hv
    interval_cases v <;>
      simp [fiveDegreeStateOfValues, Array.getD] <;>
      omega
  exact fiveSupportMultigraphCheckAux_sound hGenerated hCheck hFinal

theorem five_support_multigraph_weighted_cover_count_ge_fifteen
    (lowCount : Nat)
    (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 : Nat)
    (hLow : 3 ≤ lowCount) (hHigh : lowCount ≤ 5)
    (hValid : FiveMultiplicityValid lowCount
      (fiveMultiplicityOfValues m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14)) :
    15 ≤ fiveWeightedCoverCount
      (fiveMultiplicityOfValues m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14) := by
  interval_cases lowCount
  · exact (by omega : 15 ≤ 19).trans
      (five_support_multigraph_low_three_of_values
        m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 hValid)
  · exact (by omega : 15 ≤ 16).trans
      (five_support_multigraph_low_four_of_values
        m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 hValid)
  · exact five_support_multigraph_low_five_of_values
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 hValid

end AiMathLab.P0054.G416
