import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector075

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector077 : List Nat :=
  [0, 0, 2, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0]

theorem sevenNineExtensionVector077_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 77 [] =
      sevenNineExtensionVector077 := by
  decide

def sevenNineExtensionVector077BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5}, {1, 6}, {1, 3, 4}, {1, 2, 5}, {1, 2, 4}, {0, 6}, {0, 3, 4}, {0, 2, 5}, {0, 2, 4}]

def sevenNineExtensionVector077Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector077Selected1 :
    List (G413.Row MiddleFourModelPoint) :=
  [{0, 2, 4}]

def sevenNineExtensionVector077Selected2 :
    List (G413.Row MiddleFourModelPoint) :=
  [{0, 2, 5}]

def sevenNineExtensionVector077Selected3 :
    List (G413.Row MiddleFourModelPoint) :=
  [{0, 3, 4}]

def sevenNineExtensionVector077Selected4 :
    List (G413.Row MiddleFourModelPoint) :=
  [{1, 2, 4}]

def sevenNineExtensionVector077Selected5 :
    List (G413.Row MiddleFourModelPoint) :=
  [{1, 2, 5}]

def sevenNineExtensionVector077Selected6 :
    List (G413.Row MiddleFourModelPoint) :=
  [{1, 3, 4}]

def sevenNineExtensionVector077Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector077Selected0, sevenNineExtensionVector077Selected1, sevenNineExtensionVector077Selected2, sevenNineExtensionVector077Selected3, sevenNineExtensionVector077Selected4, sevenNineExtensionVector077Selected5, sevenNineExtensionVector077Selected6]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector077_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector077 =
      sevenNineExtensionVector077BlockerRows := by
  decide

theorem sevenNineExtensionVector077_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector077 =
      sevenNineExtensionVector077Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector077_blocker_rows]
  decide

def sevenNineExtensionVector077Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {1, 6, 7}, {1, 3, 4}, {1, 2, 5}, {1, 2, 4}, {0, 6, 7}, {0, 3, 4}, {0, 2, 5}, {0, 2, 4}]

theorem sevenNineExtensionVector077_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector077
        sevenNineExtensionVector077Selected0 =
      sevenNineExtensionVector077Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector077_blocker_rows]
  decide

theorem sevenNineExtensionVector077_final_card0 :
    (fastBlocker sevenNineExtensionVector077Base0).card =
      8 := by
  decide

theorem sevenNineExtensionVector077_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector077
      sevenNineExtensionVector077Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector077_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector077Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector077Base0 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector077_final_card0]
  decide
def sevenNineExtensionVector077Base1 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {1, 6, 7}, {1, 3, 4}, {1, 2, 5}, {1, 2, 4}, {0, 6, 7}, {0, 3, 4}, {0, 2, 5}, {0, 2, 4, 7}]

theorem sevenNineExtensionVector077_base1 :
    middleFourModelLiftBaseRows sevenNineExtensionVector077
        sevenNineExtensionVector077Selected1 =
      sevenNineExtensionVector077Base1 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector077_blocker_rows]
  decide

theorem sevenNineExtensionVector077_final_card1 :
    (fastBlocker sevenNineExtensionVector077Base1).card =
      9 := by
  decide

theorem sevenNineExtensionVector077_selection1_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector077
      sevenNineExtensionVector077Selected1 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector077_base1, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector077Base1 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector077Base1 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector077_final_card1]
  decide
def sevenNineExtensionVector077Base2 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {1, 6, 7}, {1, 3, 4}, {1, 2, 5}, {1, 2, 4}, {0, 6, 7}, {0, 3, 4}, {0, 2, 5, 7}, {0, 2, 4}]

theorem sevenNineExtensionVector077_base2 :
    middleFourModelLiftBaseRows sevenNineExtensionVector077
        sevenNineExtensionVector077Selected2 =
      sevenNineExtensionVector077Base2 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector077_blocker_rows]
  decide

theorem sevenNineExtensionVector077_final_card2 :
    (fastBlocker sevenNineExtensionVector077Base2).card =
      9 := by
  decide

theorem sevenNineExtensionVector077_selection2_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector077
      sevenNineExtensionVector077Selected2 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector077_base2, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector077Base2 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector077Base2 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector077_final_card2]
  decide
def sevenNineExtensionVector077Base3 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {1, 6, 7}, {1, 3, 4}, {1, 2, 5}, {1, 2, 4}, {0, 6, 7}, {0, 3, 4, 7}, {0, 2, 5}, {0, 2, 4}]

theorem sevenNineExtensionVector077_base3 :
    middleFourModelLiftBaseRows sevenNineExtensionVector077
        sevenNineExtensionVector077Selected3 =
      sevenNineExtensionVector077Base3 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector077_blocker_rows]
  decide

theorem sevenNineExtensionVector077_final_card3 :
    (fastBlocker sevenNineExtensionVector077Base3).card =
      9 := by
  decide

theorem sevenNineExtensionVector077_selection3_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector077
      sevenNineExtensionVector077Selected3 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector077_base3, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector077Base3 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector077Base3 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector077_final_card3]
  decide
def sevenNineExtensionVector077Base4 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {1, 6, 7}, {1, 3, 4}, {1, 2, 5}, {1, 2, 4, 7}, {0, 6, 7}, {0, 3, 4}, {0, 2, 5}, {0, 2, 4}]

theorem sevenNineExtensionVector077_base4 :
    middleFourModelLiftBaseRows sevenNineExtensionVector077
        sevenNineExtensionVector077Selected4 =
      sevenNineExtensionVector077Base4 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector077_blocker_rows]
  decide

theorem sevenNineExtensionVector077_final_card4 :
    (fastBlocker sevenNineExtensionVector077Base4).card =
      9 := by
  decide

theorem sevenNineExtensionVector077_selection4_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector077
      sevenNineExtensionVector077Selected4 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector077_base4, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector077Base4 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector077Base4 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector077_final_card4]
  decide
def sevenNineExtensionVector077Base5 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {1, 6, 7}, {1, 3, 4}, {1, 2, 5, 7}, {1, 2, 4}, {0, 6, 7}, {0, 3, 4}, {0, 2, 5}, {0, 2, 4}]

theorem sevenNineExtensionVector077_base5 :
    middleFourModelLiftBaseRows sevenNineExtensionVector077
        sevenNineExtensionVector077Selected5 =
      sevenNineExtensionVector077Base5 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector077_blocker_rows]
  decide

theorem sevenNineExtensionVector077_final_card5 :
    (fastBlocker sevenNineExtensionVector077Base5).card =
      9 := by
  decide

theorem sevenNineExtensionVector077_selection5_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector077
      sevenNineExtensionVector077Selected5 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector077_base5, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector077Base5 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector077Base5 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector077_final_card5]
  decide
def sevenNineExtensionVector077Base6 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {1, 6, 7}, {1, 3, 4, 7}, {1, 2, 5}, {1, 2, 4}, {0, 6, 7}, {0, 3, 4}, {0, 2, 5}, {0, 2, 4}]

theorem sevenNineExtensionVector077_base6 :
    middleFourModelLiftBaseRows sevenNineExtensionVector077
        sevenNineExtensionVector077Selected6 =
      sevenNineExtensionVector077Base6 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector077_blocker_rows]
  decide

theorem sevenNineExtensionVector077_final_card6 :
    (fastBlocker sevenNineExtensionVector077Base6).card =
      9 := by
  decide

theorem sevenNineExtensionVector077_selection6_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector077
      sevenNineExtensionVector077Selected6 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector077_base6, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector077Base6 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector077Base6 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector077_final_card6]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
