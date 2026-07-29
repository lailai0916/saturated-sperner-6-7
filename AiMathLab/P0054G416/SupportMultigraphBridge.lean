import AiMathLab.P0054G416.SupportMultigraphSound

namespace AiMathLab.P0054.G416

def fiveMultiplicityOfValues
    (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 : Nat) :
    FiveMultiplicity :=
  #[m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14]

def fiveDegreeStateOfValues
    (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 : Nat) :
    FiveDegreeState :=
  #[m0 + m5 + m6 + m7 + m8,
    m1 + m5 + m9 + m10 + m11,
    m2 + m6 + m9 + m12 + m13,
    m3 + m7 + m10 + m12 + m14,
    m4 + m8 + m11 + m13 + m14]

set_option maxHeartbeats 2000000 in
-- The fixed 15-coordinate normalization expands a nested sequence of array updates.
theorem fiveMultiplicityAfterThree_set_remaining
    (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 : Nat) :
    ((((((((((((fiveMultiplicityAfterThree m0 m1 m2).set! 3 m3).set! 4 m4).set! 5 m5).set!
      6 m6).set! 7 m7).set! 8 m8).set! 9 m9).set! 10 m10).set! 11 m11).set! 12 m12).set!
      13 m13).set! 14 m14 =
      fiveMultiplicityOfValues m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 := by
  apply Array.ext
  · simp [fiveMultiplicityAfterThree, fiveMultiplicityZero, fiveMultiplicityOfValues]
  · intro i hiLeft hiRight
    have hi : i < 15 := by
      simpa [fiveMultiplicityOfValues] using hiRight
    interval_cases i <;>
      simp [fiveMultiplicityAfterThree, fiveMultiplicityZero, fiveMultiplicityOfValues]

set_option maxHeartbeats 2000000 in
-- The fixed five-coordinate normalization expands all 15 support incidences.
theorem fiveDegreeStateAfterThree_add_remaining
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
                        (addFiveSupportDegree
                          (addFiveSupportDegree (fiveDegreeStateAfterThree m0 m1 m2) 3 m3)
                          4 m4) 5 m5) 6 m6) 7 m7) 8 m8) 9 m9) 10 m10) 11 m11) 12 m12) 13 m13)
      14 m14 =
      fiveDegreeStateOfValues m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 := by
  apply Array.ext
  · simp [fiveDegreeStateAfterThree, addFiveSupportDegree, fiveDegreeStateOfValues]
  · intro i hiLeft hiRight
    have hi : i < 5 := by
      simpa [fiveDegreeStateOfValues] using hiRight
    interval_cases i <;>
      simp [fiveDegreeStateAfterThree, addFiveSupportDegree, fiveSupportContains,
        fiveSupportMask, fiveDegreeStateOfValues, Array.getD, Nat.testBit]

end AiMathLab.P0054.G416
