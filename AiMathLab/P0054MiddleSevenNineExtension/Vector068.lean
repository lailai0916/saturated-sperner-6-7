import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector066

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector068 : List Nat :=
  [1, 0, 1, 1, 1, 0, 0, 0, 0, 2, 0, 1, 0, 0]

theorem sevenNineExtensionVector068_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 68 [] =
      sevenNineExtensionVector068 := by
  decide

def sevenNineExtensionVector068BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5}, {3, 4}, {1, 6}, {1, 2, 5}, {1, 2, 4}, {0, 5, 6}, {0, 4, 6}, {0, 2, 5}, {0, 2, 4}]

def sevenNineExtensionVector068Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector068Selected1 :
    List (G413.Row MiddleFourModelPoint) :=
  [{0, 2, 4}]

def sevenNineExtensionVector068Selected2 :
    List (G413.Row MiddleFourModelPoint) :=
  [{0, 2, 5}]

def sevenNineExtensionVector068Selected3 :
    List (G413.Row MiddleFourModelPoint) :=
  [{0, 4, 6}]

def sevenNineExtensionVector068Selected4 :
    List (G413.Row MiddleFourModelPoint) :=
  [{0, 5, 6}]

def sevenNineExtensionVector068Selected5 :
    List (G413.Row MiddleFourModelPoint) :=
  [{1, 2, 4}]

def sevenNineExtensionVector068Selected6 :
    List (G413.Row MiddleFourModelPoint) :=
  [{1, 2, 5}]

def sevenNineExtensionVector068Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector068Selected0, sevenNineExtensionVector068Selected1, sevenNineExtensionVector068Selected2, sevenNineExtensionVector068Selected3, sevenNineExtensionVector068Selected4, sevenNineExtensionVector068Selected5, sevenNineExtensionVector068Selected6]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector068_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector068 =
      sevenNineExtensionVector068BlockerRows := by
  decide

theorem sevenNineExtensionVector068_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector068 =
      sevenNineExtensionVector068Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector068_blocker_rows]
  decide

def sevenNineExtensionVector068Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {3, 4, 7}, {1, 6, 7}, {1, 2, 5}, {1, 2, 4}, {0, 5, 6}, {0, 4, 6}, {0, 2, 5}, {0, 2, 4}]

theorem sevenNineExtensionVector068_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector068
        sevenNineExtensionVector068Selected0 =
      sevenNineExtensionVector068Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector068_blocker_rows]
  decide

theorem sevenNineExtensionVector068_final_card0 :
    (fastBlocker sevenNineExtensionVector068Base0).card =
      8 := by
  decide

theorem sevenNineExtensionVector068_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector068
      sevenNineExtensionVector068Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector068_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector068Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector068Base0 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector068_final_card0]
  decide
def sevenNineExtensionVector068Base1 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {3, 4, 7}, {1, 6, 7}, {1, 2, 5}, {1, 2, 4}, {0, 5, 6}, {0, 4, 6}, {0, 2, 5}, {0, 2, 4, 7}]

theorem sevenNineExtensionVector068_base1 :
    middleFourModelLiftBaseRows sevenNineExtensionVector068
        sevenNineExtensionVector068Selected1 =
      sevenNineExtensionVector068Base1 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector068_blocker_rows]
  decide

theorem sevenNineExtensionVector068_final_card1 :
    (fastBlocker sevenNineExtensionVector068Base1).card =
      9 := by
  decide

theorem sevenNineExtensionVector068_selection1_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector068
      sevenNineExtensionVector068Selected1 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector068_base1, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector068Base1 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector068Base1 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector068_final_card1]
  decide
def sevenNineExtensionVector068Base2 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {3, 4, 7}, {1, 6, 7}, {1, 2, 5}, {1, 2, 4}, {0, 5, 6}, {0, 4, 6}, {0, 2, 5, 7}, {0, 2, 4}]

theorem sevenNineExtensionVector068_base2 :
    middleFourModelLiftBaseRows sevenNineExtensionVector068
        sevenNineExtensionVector068Selected2 =
      sevenNineExtensionVector068Base2 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector068_blocker_rows]
  decide

theorem sevenNineExtensionVector068_final_card2 :
    (fastBlocker sevenNineExtensionVector068Base2).card =
      9 := by
  decide

theorem sevenNineExtensionVector068_selection2_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector068
      sevenNineExtensionVector068Selected2 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector068_base2, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector068Base2 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector068Base2 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector068_final_card2]
  decide
def sevenNineExtensionVector068Base3 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {3, 4, 7}, {1, 6, 7}, {1, 2, 5}, {1, 2, 4}, {0, 5, 6}, {0, 4, 6, 7}, {0, 2, 5}, {0, 2, 4}]

theorem sevenNineExtensionVector068_base3 :
    middleFourModelLiftBaseRows sevenNineExtensionVector068
        sevenNineExtensionVector068Selected3 =
      sevenNineExtensionVector068Base3 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector068_blocker_rows]
  decide

theorem sevenNineExtensionVector068_final_card3 :
    (fastBlocker sevenNineExtensionVector068Base3).card =
      9 := by
  decide

theorem sevenNineExtensionVector068_selection3_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector068
      sevenNineExtensionVector068Selected3 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector068_base3, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector068Base3 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector068Base3 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector068_final_card3]
  decide
def sevenNineExtensionVector068Base4 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {3, 4, 7}, {1, 6, 7}, {1, 2, 5}, {1, 2, 4}, {0, 5, 6, 7}, {0, 4, 6}, {0, 2, 5}, {0, 2, 4}]

theorem sevenNineExtensionVector068_base4 :
    middleFourModelLiftBaseRows sevenNineExtensionVector068
        sevenNineExtensionVector068Selected4 =
      sevenNineExtensionVector068Base4 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector068_blocker_rows]
  decide

theorem sevenNineExtensionVector068_final_card4 :
    (fastBlocker sevenNineExtensionVector068Base4).card =
      9 := by
  decide

theorem sevenNineExtensionVector068_selection4_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector068
      sevenNineExtensionVector068Selected4 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector068_base4, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector068Base4 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector068Base4 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector068_final_card4]
  decide
def sevenNineExtensionVector068Base5 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {3, 4, 7}, {1, 6, 7}, {1, 2, 5}, {1, 2, 4, 7}, {0, 5, 6}, {0, 4, 6}, {0, 2, 5}, {0, 2, 4}]

theorem sevenNineExtensionVector068_base5 :
    middleFourModelLiftBaseRows sevenNineExtensionVector068
        sevenNineExtensionVector068Selected5 =
      sevenNineExtensionVector068Base5 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector068_blocker_rows]
  decide

theorem sevenNineExtensionVector068_final_card5 :
    (fastBlocker sevenNineExtensionVector068Base5).card =
      9 := by
  decide

theorem sevenNineExtensionVector068_selection5_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector068
      sevenNineExtensionVector068Selected5 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector068_base5, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector068Base5 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector068Base5 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector068_final_card5]
  decide
def sevenNineExtensionVector068Base6 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {3, 4, 7}, {1, 6, 7}, {1, 2, 5, 7}, {1, 2, 4}, {0, 5, 6}, {0, 4, 6}, {0, 2, 5}, {0, 2, 4}]

theorem sevenNineExtensionVector068_base6 :
    middleFourModelLiftBaseRows sevenNineExtensionVector068
        sevenNineExtensionVector068Selected6 =
      sevenNineExtensionVector068Base6 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector068_blocker_rows]
  decide

theorem sevenNineExtensionVector068_final_card6 :
    (fastBlocker sevenNineExtensionVector068Base6).card =
      9 := by
  decide

theorem sevenNineExtensionVector068_selection6_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector068
      sevenNineExtensionVector068Selected6 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector068_base6, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector068Base6 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector068Base6 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector068_final_card6]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
