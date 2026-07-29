import AiMathLab.P0054G417.SupportMultigraphBridge

namespace AiMathLab.P0054.G417

theorem sixMultiplicityChoice_of_bounds {lowCount s k : Nat} {degrees : SixDegreeState}
    (hk : k < 4)
    (hTouch : k = 0 ∨ sixSupportTouchesLowBool lowCount s = true)
    (hCap : ∀ v < lowCount, sixSupportContains s v = true →
      degrees.getD v 0 + k ≤ 3) :
    k ∈ sixMultiplicityChoices lowCount degrees s := by
  simp only [sixMultiplicityChoices, List.mem_filter, List.mem_range]
  refine ⟨hk, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · rcases hTouch with rfl | hTouch
    · simp
    · simp [hTouch]
  · simp only [List.all_eq_true, List.mem_range]
    intro v hv
    by_cases hContains : sixSupportContains s v = true
    · simp only [hContains, Bool.not_true, Bool.false_or, decide_eq_true_eq]
      exact hCap v hv hContains
    · have hFalse : sixSupportContains s v = false := Bool.eq_false_of_not_eq_true hContains
      simp [hFalse]

theorem sixSupportTouchesLowBool_true {lowCount : Nat} {s : SixSupportIndex}
    (hTouch : sixSupportTouchesLow lowCount s) :
    sixSupportTouchesLowBool lowCount s.val = true := by
  obtain ⟨v, hvs, hvLow⟩ := hTouch
  apply List.any_eq_true.mpr
  refine ⟨v.val, List.mem_range.mpr hvLow, ?_⟩
  fin_cases s <;> fin_cases v <;>
    simp_all [sixSupport, sixSupportContains, sixSupportMask, Nat.testBit]

theorem sixMultiplicityDigit_lt_four_of_valid
    {lowCount : Nat} {m : SixMultiplicity}
    (hValid : SixMultiplicityValid lowCount m) (s : SixSupportIndex) :
    sixMultiplicityDigit m s.val < 4 := by
  by_cases hZero : sixMultiplicityDigit m s.val = 0
  · omega
  have hPositive : 0 < sixMultiplicityDigit m s.val := Nat.pos_of_ne_zero hZero
  obtain ⟨v, hvs, hvLow⟩ := hValid.2 s hPositive
  have hDegree := hValid.1 v
  rw [if_pos hvLow] at hDegree
  have hTerm : sixMultiplicityDigit m s.val ≤ sixSupportDegree m v := by
    unfold sixSupportDegree
    have hSingle := Finset.single_le_sum
      (s := (Finset.univ : Finset SixSupportIndex))
      (f := fun t : SixSupportIndex ↦
        if v ∈ sixSupport t then sixMultiplicityDigit m t.val else 0)
      (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ s)
    simpa [hvs] using hSingle
  omega

theorem sixChoiceData_of_valid {lowCount : Nat} {m : SixMultiplicity}
    (hValid : SixMultiplicityValid lowCount m) (s : SixSupportIndex) :
    sixMultiplicityDigit m s.val < 4 ∧
      (sixMultiplicityDigit m s.val = 0 ∨
        sixSupportTouchesLowBool lowCount s.val = true) := by
  refine ⟨sixMultiplicityDigit_lt_four_of_valid hValid s, ?_⟩
  by_cases hZero : sixMultiplicityDigit m s.val = 0
  · exact Or.inl hZero
  · exact Or.inr (sixSupportTouchesLowBool_true
      (hValid.2 s (Nat.pos_of_ne_zero hZero)))

theorem SixGenerated.append {lowCount : Nat}
    {left right : List Nat}
    {m middleM finalM : SixMultiplicity}
    {degrees middleDegrees finalDegrees : SixDegreeState}
    (hLeft : SixGenerated lowCount left m degrees middleM middleDegrees)
    (hRight : SixGenerated lowCount right middleM middleDegrees finalM finalDegrees) :
    SixGenerated lowCount (left ++ right) m degrees finalM finalDegrees := by
  induction hLeft with
  | nil => simpa using hRight
  | cons hChoice hGenerated ih =>
      exact SixGenerated.cons hChoice (ih hRight)

set_option maxHeartbeats 4000000 in
-- This chunk expands only the first seven support updates.
theorem sixGenerated_four_through_ten
    (lowCount : Nat)
    (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20 :
      Nat)
    (hHigh : lowCount ≤ 6)
    (hValid : SixMultiplicityValid lowCount
      (sixMultiplicityOfValues m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14
        m15 m16 m17 m18 m19 m20)) :
    SixGenerated lowCount [4, 5, 6, 7, 8, 9, 10]
      (sixMultiplicityAfterFour m0 m1 m2 m3) (sixDegreeStateAfterFour m0 m1 m2 m3)
      (sixMultiplicityThroughTen m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10)
      (sixDegreeStateThroughTen m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10) := by
  have hData := sixChoiceData_of_valid hValid
  apply SixGenerated.cons (k := m4)
  · apply sixMultiplicityChoice_of_bounds
    · simpa [sixMultiplicityDigit, sixMultiplicityOfValues] using
        (hData (4 : SixSupportIndex)).1
    · simpa [sixMultiplicityDigit, sixMultiplicityOfValues] using
        (hData (4 : SixSupportIndex)).2
    · intro v hv hContains
      have hvSix : v < 6 := by omega
      have hDegree := hValid.1 (⟨v, hvSix⟩ : SixVertex)
      rw [if_pos hv] at hDegree
      interval_cases v <;>
        simp [sixSupportDegree, sixMultiplicityDigit, sixMultiplicityOfValues, sixSupport,
          Fin.sum_univ_succ, sixDegreeStateAfterFour, addSixSupportDegree,
          sixSupportContains, sixSupportMask, Array.getD, Nat.testBit]
          at hDegree hContains ⊢ <;>
        omega
  apply SixGenerated.cons (k := m5)
  · apply sixMultiplicityChoice_of_bounds
    · simpa [sixMultiplicityDigit, sixMultiplicityOfValues] using
        (hData (5 : SixSupportIndex)).1
    · simpa [sixMultiplicityDigit, sixMultiplicityOfValues] using
        (hData (5 : SixSupportIndex)).2
    · intro v hv hContains
      have hvSix : v < 6 := by omega
      have hDegree := hValid.1 (⟨v, hvSix⟩ : SixVertex)
      rw [if_pos hv] at hDegree
      interval_cases v <;>
        simp [sixSupportDegree, sixMultiplicityDigit, sixMultiplicityOfValues, sixSupport,
          Fin.sum_univ_succ, sixDegreeStateAfterFour, addSixSupportDegree,
          sixSupportContains, sixSupportMask, Array.getD, Nat.testBit]
          at hDegree hContains ⊢ <;>
        omega
  apply SixGenerated.cons (k := m6)
  · apply sixMultiplicityChoice_of_bounds
    · simpa [sixMultiplicityDigit, sixMultiplicityOfValues] using
        (hData (6 : SixSupportIndex)).1
    · simpa [sixMultiplicityDigit, sixMultiplicityOfValues] using
        (hData (6 : SixSupportIndex)).2
    · intro v hv hContains
      have hvSix : v < 6 := by omega
      have hDegree := hValid.1 (⟨v, hvSix⟩ : SixVertex)
      rw [if_pos hv] at hDegree
      interval_cases v <;>
        simp [sixSupportDegree, sixMultiplicityDigit, sixMultiplicityOfValues, sixSupport,
          Fin.sum_univ_succ, sixDegreeStateAfterFour, addSixSupportDegree,
          sixSupportContains, sixSupportMask, Array.getD, Nat.testBit]
          at hDegree hContains ⊢ <;>
        omega
  apply SixGenerated.cons (k := m7)
  · apply sixMultiplicityChoice_of_bounds
    · simpa [sixMultiplicityDigit, sixMultiplicityOfValues] using
        (hData (7 : SixSupportIndex)).1
    · simpa [sixMultiplicityDigit, sixMultiplicityOfValues] using
        (hData (7 : SixSupportIndex)).2
    · intro v hv hContains
      have hvSix : v < 6 := by omega
      have hDegree := hValid.1 (⟨v, hvSix⟩ : SixVertex)
      rw [if_pos hv] at hDegree
      interval_cases v <;>
        simp [sixSupportDegree, sixMultiplicityDigit, sixMultiplicityOfValues, sixSupport,
          Fin.sum_univ_succ, sixDegreeStateAfterFour, addSixSupportDegree,
          sixSupportContains, sixSupportMask, Array.getD, Nat.testBit]
          at hDegree hContains ⊢ <;>
        omega
  apply SixGenerated.cons (k := m8)
  · apply sixMultiplicityChoice_of_bounds
    · simpa [sixMultiplicityDigit, sixMultiplicityOfValues] using
        (hData (8 : SixSupportIndex)).1
    · simpa [sixMultiplicityDigit, sixMultiplicityOfValues] using
        (hData (8 : SixSupportIndex)).2
    · intro v hv hContains
      have hvSix : v < 6 := by omega
      have hDegree := hValid.1 (⟨v, hvSix⟩ : SixVertex)
      rw [if_pos hv] at hDegree
      interval_cases v <;>
        simp [sixSupportDegree, sixMultiplicityDigit, sixMultiplicityOfValues, sixSupport,
          Fin.sum_univ_succ, sixDegreeStateAfterFour, addSixSupportDegree,
          sixSupportContains, sixSupportMask, Array.getD, Nat.testBit]
          at hDegree hContains ⊢ <;>
        omega
  apply SixGenerated.cons (k := m9)
  · apply sixMultiplicityChoice_of_bounds
    · simpa [sixMultiplicityDigit, sixMultiplicityOfValues] using
        (hData (9 : SixSupportIndex)).1
    · simpa [sixMultiplicityDigit, sixMultiplicityOfValues] using
        (hData (9 : SixSupportIndex)).2
    · intro v hv hContains
      have hvSix : v < 6 := by omega
      have hDegree := hValid.1 (⟨v, hvSix⟩ : SixVertex)
      rw [if_pos hv] at hDegree
      interval_cases v <;>
        simp [sixSupportDegree, sixMultiplicityDigit, sixMultiplicityOfValues, sixSupport,
          Fin.sum_univ_succ, sixDegreeStateAfterFour, addSixSupportDegree,
          sixSupportContains, sixSupportMask, Array.getD, Nat.testBit]
          at hDegree hContains ⊢ <;>
        omega
  apply SixGenerated.cons (k := m10)
  · apply sixMultiplicityChoice_of_bounds
    · simpa [sixMultiplicityDigit, sixMultiplicityOfValues] using
        (hData (10 : SixSupportIndex)).1
    · simpa [sixMultiplicityDigit, sixMultiplicityOfValues] using
        (hData (10 : SixSupportIndex)).2
    · intro v hv hContains
      have hvSix : v < 6 := by omega
      have hDegree := hValid.1 (⟨v, hvSix⟩ : SixVertex)
      rw [if_pos hv] at hDegree
      interval_cases v <;>
        simp [sixSupportDegree, sixMultiplicityDigit, sixMultiplicityOfValues, sixSupport,
          Fin.sum_univ_succ, sixDegreeStateAfterFour, addSixSupportDegree,
          sixSupportContains, sixSupportMask, Array.getD, Nat.testBit]
          at hDegree hContains ⊢ <;>
        omega
  rw [sixMultiplicityAfterFour_set_throughTen, sixDegreeStateAfterFour_add_throughTen]
  exact SixGenerated.nil _ _

set_option maxHeartbeats 4000000 in
-- This chunk expands the five middle support updates.
theorem sixGenerated_eleven_through_fifteen
    (lowCount : Nat)
    (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20 :
      Nat)
    (hHigh : lowCount ≤ 6)
    (hValid : SixMultiplicityValid lowCount
      (sixMultiplicityOfValues m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14
        m15 m16 m17 m18 m19 m20)) :
    SixGenerated lowCount [11, 12, 13, 14, 15]
      (sixMultiplicityThroughTen m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10)
      (sixDegreeStateThroughTen m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10)
      (sixMultiplicityThroughFifteen m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10
        m11 m12 m13 m14 m15)
      (sixDegreeStateThroughFifteen m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10
        m11 m12 m13 m14 m15) := by
  have hData := sixChoiceData_of_valid hValid
  apply SixGenerated.cons (k := m11)
  · apply sixMultiplicityChoice_of_bounds
    · simpa [sixMultiplicityDigit, sixMultiplicityOfValues] using
        (hData (11 : SixSupportIndex)).1
    · simpa [sixMultiplicityDigit, sixMultiplicityOfValues] using
        (hData (11 : SixSupportIndex)).2
    · intro v hv hContains
      have hvSix : v < 6 := by omega
      have hDegree := hValid.1 (⟨v, hvSix⟩ : SixVertex)
      rw [if_pos hv] at hDegree
      interval_cases v <;>
        simp [sixSupportDegree, sixMultiplicityDigit, sixMultiplicityOfValues, sixSupport,
          Fin.sum_univ_succ, sixDegreeStateThroughTen, addSixSupportDegree,
          sixSupportContains, sixSupportMask, Array.getD, Nat.testBit]
          at hDegree hContains ⊢ <;>
        omega
  apply SixGenerated.cons (k := m12)
  · apply sixMultiplicityChoice_of_bounds
    · simpa [sixMultiplicityDigit, sixMultiplicityOfValues] using
        (hData (12 : SixSupportIndex)).1
    · simpa [sixMultiplicityDigit, sixMultiplicityOfValues] using
        (hData (12 : SixSupportIndex)).2
    · intro v hv hContains
      have hvSix : v < 6 := by omega
      have hDegree := hValid.1 (⟨v, hvSix⟩ : SixVertex)
      rw [if_pos hv] at hDegree
      interval_cases v <;>
        simp [sixSupportDegree, sixMultiplicityDigit, sixMultiplicityOfValues, sixSupport,
          Fin.sum_univ_succ, sixDegreeStateThroughTen, addSixSupportDegree,
          sixSupportContains, sixSupportMask, Array.getD, Nat.testBit]
          at hDegree hContains ⊢ <;>
        omega
  apply SixGenerated.cons (k := m13)
  · apply sixMultiplicityChoice_of_bounds
    · simpa [sixMultiplicityDigit, sixMultiplicityOfValues] using
        (hData (13 : SixSupportIndex)).1
    · simpa [sixMultiplicityDigit, sixMultiplicityOfValues] using
        (hData (13 : SixSupportIndex)).2
    · intro v hv hContains
      have hvSix : v < 6 := by omega
      have hDegree := hValid.1 (⟨v, hvSix⟩ : SixVertex)
      rw [if_pos hv] at hDegree
      interval_cases v <;>
        simp [sixSupportDegree, sixMultiplicityDigit, sixMultiplicityOfValues, sixSupport,
          Fin.sum_univ_succ, sixDegreeStateThroughTen, addSixSupportDegree,
          sixSupportContains, sixSupportMask, Array.getD, Nat.testBit]
          at hDegree hContains ⊢ <;>
        omega
  apply SixGenerated.cons (k := m14)
  · apply sixMultiplicityChoice_of_bounds
    · simpa [sixMultiplicityDigit, sixMultiplicityOfValues] using
        (hData (14 : SixSupportIndex)).1
    · simpa [sixMultiplicityDigit, sixMultiplicityOfValues] using
        (hData (14 : SixSupportIndex)).2
    · intro v hv hContains
      have hvSix : v < 6 := by omega
      have hDegree := hValid.1 (⟨v, hvSix⟩ : SixVertex)
      rw [if_pos hv] at hDegree
      interval_cases v <;>
        simp [sixSupportDegree, sixMultiplicityDigit, sixMultiplicityOfValues, sixSupport,
          Fin.sum_univ_succ, sixDegreeStateThroughTen, addSixSupportDegree,
          sixSupportContains, sixSupportMask, Array.getD, Nat.testBit]
          at hDegree hContains ⊢ <;>
        omega
  apply SixGenerated.cons (k := m15)
  · apply sixMultiplicityChoice_of_bounds
    · simpa [sixMultiplicityDigit, sixMultiplicityOfValues] using
        (hData (15 : SixSupportIndex)).1
    · simpa [sixMultiplicityDigit, sixMultiplicityOfValues] using
        (hData (15 : SixSupportIndex)).2
    · intro v hv hContains
      have hvSix : v < 6 := by omega
      have hDegree := hValid.1 (⟨v, hvSix⟩ : SixVertex)
      rw [if_pos hv] at hDegree
      interval_cases v <;>
        simp [sixSupportDegree, sixMultiplicityDigit, sixMultiplicityOfValues, sixSupport,
          Fin.sum_univ_succ, sixDegreeStateThroughTen, addSixSupportDegree,
          sixSupportContains, sixSupportMask, Array.getD, Nat.testBit]
          at hDegree hContains ⊢ <;>
        omega
  rw [sixMultiplicityThroughTen_set_throughFifteen,
    sixDegreeStateThroughTen_add_throughFifteen]
  exact SixGenerated.nil _ _

set_option maxHeartbeats 4000000 in
-- This chunk expands the final five support updates.
theorem sixGenerated_sixteen_through_twenty
    (lowCount : Nat)
    (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20 :
      Nat)
    (hHigh : lowCount ≤ 6)
    (hValid : SixMultiplicityValid lowCount
      (sixMultiplicityOfValues m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14
        m15 m16 m17 m18 m19 m20)) :
    SixGenerated lowCount [16, 17, 18, 19, 20]
      (sixMultiplicityThroughFifteen m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10
        m11 m12 m13 m14 m15)
      (sixDegreeStateThroughFifteen m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10
        m11 m12 m13 m14 m15)
      (sixMultiplicityOfValues m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14
        m15 m16 m17 m18 m19 m20)
      (sixDegreeStateOfValues m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14
        m15 m16 m17 m18 m19 m20) := by
  have hData := sixChoiceData_of_valid hValid
  apply SixGenerated.cons (k := m16)
  · apply sixMultiplicityChoice_of_bounds
    · simpa [sixMultiplicityDigit, sixMultiplicityOfValues] using
        (hData (16 : SixSupportIndex)).1
    · simpa [sixMultiplicityDigit, sixMultiplicityOfValues] using
        (hData (16 : SixSupportIndex)).2
    · intro v hv hContains
      have hvSix : v < 6 := by omega
      have hDegree := hValid.1 (⟨v, hvSix⟩ : SixVertex)
      rw [if_pos hv] at hDegree
      interval_cases v <;>
        simp [sixSupportDegree, sixMultiplicityDigit, sixMultiplicityOfValues, sixSupport,
          Fin.sum_univ_succ, sixDegreeStateThroughFifteen, addSixSupportDegree,
          sixSupportContains, sixSupportMask, Array.getD, Nat.testBit]
          at hDegree hContains ⊢ <;>
        omega
  apply SixGenerated.cons (k := m17)
  · apply sixMultiplicityChoice_of_bounds
    · simpa [sixMultiplicityDigit, sixMultiplicityOfValues] using
        (hData (17 : SixSupportIndex)).1
    · simpa [sixMultiplicityDigit, sixMultiplicityOfValues] using
        (hData (17 : SixSupportIndex)).2
    · intro v hv hContains
      have hvSix : v < 6 := by omega
      have hDegree := hValid.1 (⟨v, hvSix⟩ : SixVertex)
      rw [if_pos hv] at hDegree
      interval_cases v <;>
        simp [sixSupportDegree, sixMultiplicityDigit, sixMultiplicityOfValues, sixSupport,
          Fin.sum_univ_succ, sixDegreeStateThroughFifteen, addSixSupportDegree,
          sixSupportContains, sixSupportMask, Array.getD, Nat.testBit]
          at hDegree hContains ⊢ <;>
        omega
  apply SixGenerated.cons (k := m18)
  · apply sixMultiplicityChoice_of_bounds
    · simpa [sixMultiplicityDigit, sixMultiplicityOfValues] using
        (hData (18 : SixSupportIndex)).1
    · simpa [sixMultiplicityDigit, sixMultiplicityOfValues] using
        (hData (18 : SixSupportIndex)).2
    · intro v hv hContains
      have hvSix : v < 6 := by omega
      have hDegree := hValid.1 (⟨v, hvSix⟩ : SixVertex)
      rw [if_pos hv] at hDegree
      interval_cases v <;>
        simp [sixSupportDegree, sixMultiplicityDigit, sixMultiplicityOfValues, sixSupport,
          Fin.sum_univ_succ, sixDegreeStateThroughFifteen, addSixSupportDegree,
          sixSupportContains, sixSupportMask, Array.getD, Nat.testBit]
          at hDegree hContains ⊢ <;>
        omega
  apply SixGenerated.cons (k := m19)
  · apply sixMultiplicityChoice_of_bounds
    · simpa [sixMultiplicityDigit, sixMultiplicityOfValues] using
        (hData (19 : SixSupportIndex)).1
    · simpa [sixMultiplicityDigit, sixMultiplicityOfValues] using
        (hData (19 : SixSupportIndex)).2
    · intro v hv hContains
      have hvSix : v < 6 := by omega
      have hDegree := hValid.1 (⟨v, hvSix⟩ : SixVertex)
      rw [if_pos hv] at hDegree
      interval_cases v <;>
        simp [sixSupportDegree, sixMultiplicityDigit, sixMultiplicityOfValues, sixSupport,
          Fin.sum_univ_succ, sixDegreeStateThroughFifteen, addSixSupportDegree,
          sixSupportContains, sixSupportMask, Array.getD, Nat.testBit]
          at hDegree hContains ⊢ <;>
        omega
  apply SixGenerated.cons (k := m20)
  · apply sixMultiplicityChoice_of_bounds
    · simpa [sixMultiplicityDigit, sixMultiplicityOfValues] using
        (hData (20 : SixSupportIndex)).1
    · simpa [sixMultiplicityDigit, sixMultiplicityOfValues] using
        (hData (20 : SixSupportIndex)).2
    · intro v hv hContains
      have hvSix : v < 6 := by omega
      have hDegree := hValid.1 (⟨v, hvSix⟩ : SixVertex)
      rw [if_pos hv] at hDegree
      interval_cases v <;>
        simp [sixSupportDegree, sixMultiplicityDigit, sixMultiplicityOfValues, sixSupport,
          Fin.sum_univ_succ, sixDegreeStateThroughFifteen, addSixSupportDegree,
          sixSupportContains, sixSupportMask, Array.getD, Nat.testBit]
          at hDegree hContains ⊢ <;>
        omega
  rw [sixMultiplicityThroughFifteen_set_remaining,
    sixDegreeStateThroughFifteen_add_remaining]
  exact SixGenerated.nil _ _

theorem sixGenerated_of_values
    (lowCount : Nat)
    (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20 :
      Nat)
    (hHigh : lowCount ≤ 6)
    (hValid : SixMultiplicityValid lowCount
      (sixMultiplicityOfValues m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14
        m15 m16 m17 m18 m19 m20)) :
    SixGenerated lowCount ((List.range 21).drop 4)
      (sixMultiplicityAfterFour m0 m1 m2 m3) (sixDegreeStateAfterFour m0 m1 m2 m3)
      (sixMultiplicityOfValues m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14
        m15 m16 m17 m18 m19 m20)
      (sixDegreeStateOfValues m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14
        m15 m16 m17 m18 m19 m20) := by
  have hFirst := sixGenerated_four_through_ten lowCount
    m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20
    hHigh hValid
  have hMiddle := sixGenerated_eleven_through_fifteen lowCount
    m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20
    hHigh hValid
  have hLast := sixGenerated_sixteen_through_twenty lowCount
    m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20
    hHigh hValid
  norm_num [List.range, List.drop]
  exact hFirst.append (hMiddle.append hLast)

theorem sixMultiplicityValid_low_three_impossible
    (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20 :
      Nat)
    (hValid : SixMultiplicityValid 3
      (sixMultiplicityOfValues m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14
        m15 m16 m17 m18 m19 m20)) : False := by
  have h0 := hValid.1 (0 : SixVertex)
  have h1 := hValid.1 (1 : SixVertex)
  have h2 := hValid.1 (2 : SixVertex)
  have h3 := hValid.1 (3 : SixVertex)
  have h4 := hValid.1 (4 : SixVertex)
  have h5 := hValid.1 (5 : SixVertex)
  simp [sixSupportDegree, sixMultiplicityDigit, sixMultiplicityOfValues, sixSupport,
    Fin.sum_univ_succ] at h0 h1 h2 h3 h4 h5
  have hm3 : m3 = 0 := by
    have h := hValid.2 (3 : SixSupportIndex)
    simp [sixMultiplicityDigit, sixMultiplicityOfValues, sixSupportTouchesLow,
      sixSupport] at h
    omega
  have hm4 : m4 = 0 := by
    have h := hValid.2 (4 : SixSupportIndex)
    simp [sixMultiplicityDigit, sixMultiplicityOfValues, sixSupportTouchesLow,
      sixSupport] at h
    omega
  have hm5 : m5 = 0 := by
    have h := hValid.2 (5 : SixSupportIndex)
    simp [sixMultiplicityDigit, sixMultiplicityOfValues, sixSupportTouchesLow,
      sixSupport] at h
    omega
  have hm18 : m18 = 0 := by
    have h := hValid.2 (18 : SixSupportIndex)
    simp [sixMultiplicityDigit, sixMultiplicityOfValues, sixSupportTouchesLow,
      sixSupport] at h
    omega
  have hm19 : m19 = 0 := by
    have h := hValid.2 (19 : SixSupportIndex)
    simp [sixMultiplicityDigit, sixMultiplicityOfValues, sixSupportTouchesLow,
      sixSupport] at h
    omega
  have hm20 : m20 = 0 := by
    have h := hValid.2 (20 : SixSupportIndex)
    simp [sixMultiplicityDigit, sixMultiplicityOfValues, sixSupportTouchesLow,
      sixSupport] at h
    omega
  omega

end AiMathLab.P0054.G417
