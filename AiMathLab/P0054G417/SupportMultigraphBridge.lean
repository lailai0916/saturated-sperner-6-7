import AiMathLab.P0054G417.SupportMultigraphSound

namespace AiMathLab.P0054.G417

def sixMultiplicityOfValues
    (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20 :
      Nat) : SixMultiplicity :=
  #[m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14,
    m15, m16, m17, m18, m19, m20]

def sixDegreeStateOfValues
    (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20 :
      Nat) : SixDegreeState :=
  #[m0 + m6 + m7 + m8 + m9 + m10,
    m1 + m6 + m11 + m12 + m13 + m14,
    m2 + m7 + m11 + m15 + m16 + m17,
    m3 + m8 + m12 + m15 + m18 + m19,
    m4 + m9 + m13 + m16 + m18 + m20,
    m5 + m10 + m14 + m17 + m19 + m20]

def sixMultiplicityThroughTen
    (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 : Nat) : SixMultiplicity :=
  #[m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def sixMultiplicityThroughFifteen
    (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 : Nat) :
    SixMultiplicity :=
  #[m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10,
    m11, m12, m13, m14, m15, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000 in
theorem sixMultiplicityAfterFour_set_throughTen
    (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 : Nat) :
    (((((((sixMultiplicityAfterFour m0 m1 m2 m3).set! 4 m4).set! 5 m5).set!
      6 m6).set! 7 m7).set! 8 m8).set! 9 m9).set! 10 m10 =
      sixMultiplicityThroughTen m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 := by
  apply Array.ext
  · simp [sixMultiplicityAfterFour, sixMultiplicityZero, sixMultiplicityThroughTen]
  · intro i hiLeft hiRight
    have hi : i < 21 := by simpa [sixMultiplicityThroughTen] using hiRight
    interval_cases i <;>
      simp [sixMultiplicityAfterFour, sixMultiplicityZero, sixMultiplicityThroughTen]

set_option maxHeartbeats 2000000 in
theorem sixMultiplicityThroughTen_set_throughFifteen
    (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 : Nat) :
    (((((sixMultiplicityThroughTen m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10).set!
      11 m11).set! 12 m12).set! 13 m13).set! 14 m14).set! 15 m15 =
      sixMultiplicityThroughFifteen m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10
        m11 m12 m13 m14 m15 := by
  apply Array.ext
  · simp [sixMultiplicityThroughTen, sixMultiplicityThroughFifteen]
  · intro i hiLeft hiRight
    have hi : i < 21 := by simpa [sixMultiplicityThroughFifteen] using hiRight
    interval_cases i <;>
      simp [sixMultiplicityThroughTen, sixMultiplicityThroughFifteen]

set_option maxHeartbeats 2000000 in
theorem sixMultiplicityThroughFifteen_set_remaining
    (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20 :
      Nat) :
    (((((sixMultiplicityThroughFifteen m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10
      m11 m12 m13 m14 m15).set! 16 m16).set! 17 m17).set! 18 m18).set!
      19 m19).set! 20 m20 =
      sixMultiplicityOfValues m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14
        m15 m16 m17 m18 m19 m20 := by
  apply Array.ext
  · simp [sixMultiplicityThroughFifteen, sixMultiplicityOfValues]
  · intro i hiLeft hiRight
    have hi : i < 21 := by simpa [sixMultiplicityOfValues] using hiRight
    interval_cases i <;>
      simp [sixMultiplicityThroughFifteen, sixMultiplicityOfValues]

theorem sixMultiplicityAfterFour_set_remaining
    (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20 :
      Nat) :
    (((((((((((((((((sixMultiplicityAfterFour m0 m1 m2 m3).set! 4 m4).set! 5 m5).set!
      6 m6).set! 7 m7).set! 8 m8).set! 9 m9).set! 10 m10).set! 11 m11).set! 12 m12).set!
      13 m13).set! 14 m14).set! 15 m15).set! 16 m16).set! 17 m17).set! 18 m18).set!
      19 m19).set! 20 m20 =
      sixMultiplicityOfValues m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14
        m15 m16 m17 m18 m19 m20 := by
  rw [sixMultiplicityAfterFour_set_throughTen,
    sixMultiplicityThroughTen_set_throughFifteen,
    sixMultiplicityThroughFifteen_set_remaining]

def sixDegreeStateThroughTen
    (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 : Nat) : SixDegreeState :=
  #[m0 + m6 + m7 + m8 + m9 + m10,
    m1 + m6, m2 + m7, m3 + m8, m4 + m9, m5 + m10]

def sixDegreeStateThroughFifteen
    (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 : Nat) :
    SixDegreeState :=
  #[m0 + m6 + m7 + m8 + m9 + m10,
    m1 + m6 + m11 + m12 + m13 + m14,
    m2 + m7 + m11 + m15,
    m3 + m8 + m12 + m15,
    m4 + m9 + m13,
    m5 + m10 + m14]

set_option maxHeartbeats 2000000 in
theorem sixDegreeStateAfterFour_add_throughTen
    (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 : Nat) :
    addSixSupportDegree
      (addSixSupportDegree
        (addSixSupportDegree
          (addSixSupportDegree
            (addSixSupportDegree
              (addSixSupportDegree
                (addSixSupportDegree (sixDegreeStateAfterFour m0 m1 m2 m3) 4 m4) 5 m5)
              6 m6) 7 m7) 8 m8) 9 m9) 10 m10 =
      sixDegreeStateThroughTen m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 := by
  apply Array.ext
  · simp [sixDegreeStateAfterFour, addSixSupportDegree, sixDegreeStateThroughTen]
  · intro i hiLeft hiRight
    have hi : i < 6 := by simpa [sixDegreeStateThroughTen] using hiRight
    interval_cases i <;>
      simp [sixDegreeStateAfterFour, addSixSupportDegree, sixSupportContains,
        sixSupportMask, sixDegreeStateThroughTen, Array.getD, Nat.testBit]

set_option maxHeartbeats 2000000 in
theorem sixDegreeStateThroughTen_add_throughFifteen
    (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 : Nat) :
    addSixSupportDegree
      (addSixSupportDegree
        (addSixSupportDegree
          (addSixSupportDegree
            (addSixSupportDegree
              (sixDegreeStateThroughTen m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10)
              11 m11) 12 m12) 13 m13) 14 m14) 15 m15 =
      sixDegreeStateThroughFifteen m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10
        m11 m12 m13 m14 m15 := by
  apply Array.ext
  · simp [sixDegreeStateThroughTen, addSixSupportDegree, sixDegreeStateThroughFifteen]
  · intro i hiLeft hiRight
    have hi : i < 6 := by simpa [sixDegreeStateThroughFifteen] using hiRight
    interval_cases i <;>
      simp [sixDegreeStateThroughTen, addSixSupportDegree, sixSupportContains,
        sixSupportMask, sixDegreeStateThroughFifteen, Array.getD, Nat.testBit]

set_option maxHeartbeats 2000000 in
theorem sixDegreeStateThroughFifteen_add_remaining
    (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20 :
      Nat) :
    addSixSupportDegree
      (addSixSupportDegree
        (addSixSupportDegree
          (addSixSupportDegree
            (addSixSupportDegree
              (sixDegreeStateThroughFifteen m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10
                m11 m12 m13 m14 m15) 16 m16) 17 m17) 18 m18) 19 m19) 20 m20 =
      sixDegreeStateOfValues m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14
        m15 m16 m17 m18 m19 m20 := by
  apply Array.ext
  · simp [sixDegreeStateThroughFifteen, addSixSupportDegree, sixDegreeStateOfValues]
  · intro i hiLeft hiRight
    have hi : i < 6 := by simpa [sixDegreeStateOfValues] using hiRight
    interval_cases i <;>
      simp [sixDegreeStateThroughFifteen, addSixSupportDegree, sixSupportContains,
        sixSupportMask, sixDegreeStateOfValues, Array.getD, Nat.testBit]

theorem sixDegreeStateAfterFour_add_remaining
    (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20 :
      Nat) :
    addSixSupportDegree
      (addSixSupportDegree
        (addSixSupportDegree
          (addSixSupportDegree
            (addSixSupportDegree
              (addSixSupportDegree
                (addSixSupportDegree
                  (addSixSupportDegree
                    (addSixSupportDegree
                      (addSixSupportDegree
                        (addSixSupportDegree
                          (addSixSupportDegree
                            (addSixSupportDegree
                              (addSixSupportDegree
                                (addSixSupportDegree
                                  (addSixSupportDegree
                                    (addSixSupportDegree
                                      (sixDegreeStateAfterFour m0 m1 m2 m3) 4 m4) 5 m5) 6 m6)
                                  7 m7) 8 m8) 9 m9) 10 m10) 11 m11) 12 m12) 13 m13) 14 m14)
                      15 m15) 16 m16) 17 m17) 18 m18) 19 m19) 20 m20 =
      sixDegreeStateOfValues m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14
        m15 m16 m17 m18 m19 m20 := by
  rw [sixDegreeStateAfterFour_add_throughTen,
    sixDegreeStateThroughTen_add_throughFifteen,
    sixDegreeStateThroughFifteen_add_remaining]

end AiMathLab.P0054.G417
