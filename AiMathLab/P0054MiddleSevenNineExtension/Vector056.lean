import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector054

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector056 : List Nat :=
  [1, 0, 1, 0, 0, 2, 0, 1, 1, 0, 0, 1, 0, 0]

theorem sevenNineExtensionVector056_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 56 [] =
      sevenNineExtensionVector056 := by
  decide

def sevenNineExtensionVector056BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5}, {2, 5}, {1, 6}, {1, 3, 4}, {1, 2, 4}, {0, 3, 6}, {0, 3, 4}, {0, 2, 6}, {0, 2, 4}]

def sevenNineExtensionVector056Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector056Selected1 :
    List (G413.Row MiddleFourModelPoint) :=
  [{0, 2, 4}]

def sevenNineExtensionVector056Selected2 :
    List (G413.Row MiddleFourModelPoint) :=
  [{0, 2, 6}]

def sevenNineExtensionVector056Selected3 :
    List (G413.Row MiddleFourModelPoint) :=
  [{0, 3, 4}]

def sevenNineExtensionVector056Selected4 :
    List (G413.Row MiddleFourModelPoint) :=
  [{0, 3, 6}]

def sevenNineExtensionVector056Selected5 :
    List (G413.Row MiddleFourModelPoint) :=
  [{1, 2, 4}]

def sevenNineExtensionVector056Selected6 :
    List (G413.Row MiddleFourModelPoint) :=
  [{1, 3, 4}]

def sevenNineExtensionVector056Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector056Selected0, sevenNineExtensionVector056Selected1, sevenNineExtensionVector056Selected2, sevenNineExtensionVector056Selected3, sevenNineExtensionVector056Selected4, sevenNineExtensionVector056Selected5, sevenNineExtensionVector056Selected6]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector056_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector056 =
      sevenNineExtensionVector056BlockerRows := by
  decide

theorem sevenNineExtensionVector056_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector056 =
      sevenNineExtensionVector056Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector056_blocker_rows]
  decide

def sevenNineExtensionVector056Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {2, 5, 7}, {1, 6, 7}, {1, 3, 4}, {1, 2, 4}, {0, 3, 6}, {0, 3, 4}, {0, 2, 6}, {0, 2, 4}]

theorem sevenNineExtensionVector056_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector056
        sevenNineExtensionVector056Selected0 =
      sevenNineExtensionVector056Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector056_blocker_rows]
  decide

theorem sevenNineExtensionVector056_final_card0 :
    (fastBlocker sevenNineExtensionVector056Base0).card =
      8 := by
  decide

theorem sevenNineExtensionVector056_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector056
      sevenNineExtensionVector056Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector056_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector056Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector056Base0 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector056_final_card0]
  decide
def sevenNineExtensionVector056Base1 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {2, 5, 7}, {1, 6, 7}, {1, 3, 4}, {1, 2, 4}, {0, 3, 6}, {0, 3, 4}, {0, 2, 6}, {0, 2, 4, 7}]

theorem sevenNineExtensionVector056_base1 :
    middleFourModelLiftBaseRows sevenNineExtensionVector056
        sevenNineExtensionVector056Selected1 =
      sevenNineExtensionVector056Base1 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector056_blocker_rows]
  decide

theorem sevenNineExtensionVector056_final_card1 :
    (fastBlocker sevenNineExtensionVector056Base1).card =
      9 := by
  decide

theorem sevenNineExtensionVector056_selection1_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector056
      sevenNineExtensionVector056Selected1 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector056_base1, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector056Base1 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector056Base1 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector056_final_card1]
  decide
def sevenNineExtensionVector056Base2 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {2, 5, 7}, {1, 6, 7}, {1, 3, 4}, {1, 2, 4}, {0, 3, 6}, {0, 3, 4}, {0, 2, 6, 7}, {0, 2, 4}]

theorem sevenNineExtensionVector056_base2 :
    middleFourModelLiftBaseRows sevenNineExtensionVector056
        sevenNineExtensionVector056Selected2 =
      sevenNineExtensionVector056Base2 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector056_blocker_rows]
  decide

theorem sevenNineExtensionVector056_final_card2 :
    (fastBlocker sevenNineExtensionVector056Base2).card =
      9 := by
  decide

theorem sevenNineExtensionVector056_selection2_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector056
      sevenNineExtensionVector056Selected2 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector056_base2, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector056Base2 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector056Base2 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector056_final_card2]
  decide
def sevenNineExtensionVector056Base3 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {2, 5, 7}, {1, 6, 7}, {1, 3, 4}, {1, 2, 4}, {0, 3, 6}, {0, 3, 4, 7}, {0, 2, 6}, {0, 2, 4}]

theorem sevenNineExtensionVector056_base3 :
    middleFourModelLiftBaseRows sevenNineExtensionVector056
        sevenNineExtensionVector056Selected3 =
      sevenNineExtensionVector056Base3 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector056_blocker_rows]
  decide

theorem sevenNineExtensionVector056_final_card3 :
    (fastBlocker sevenNineExtensionVector056Base3).card =
      9 := by
  decide

theorem sevenNineExtensionVector056_selection3_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector056
      sevenNineExtensionVector056Selected3 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector056_base3, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector056Base3 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector056Base3 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector056_final_card3]
  decide
def sevenNineExtensionVector056Base4 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {2, 5, 7}, {1, 6, 7}, {1, 3, 4}, {1, 2, 4}, {0, 3, 6, 7}, {0, 3, 4}, {0, 2, 6}, {0, 2, 4}]

theorem sevenNineExtensionVector056_base4 :
    middleFourModelLiftBaseRows sevenNineExtensionVector056
        sevenNineExtensionVector056Selected4 =
      sevenNineExtensionVector056Base4 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector056_blocker_rows]
  decide

theorem sevenNineExtensionVector056_final_card4 :
    (fastBlocker sevenNineExtensionVector056Base4).card =
      9 := by
  decide

theorem sevenNineExtensionVector056_selection4_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector056
      sevenNineExtensionVector056Selected4 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector056_base4, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector056Base4 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector056Base4 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector056_final_card4]
  decide
def sevenNineExtensionVector056Base5 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {2, 5, 7}, {1, 6, 7}, {1, 3, 4}, {1, 2, 4, 7}, {0, 3, 6}, {0, 3, 4}, {0, 2, 6}, {0, 2, 4}]

theorem sevenNineExtensionVector056_base5 :
    middleFourModelLiftBaseRows sevenNineExtensionVector056
        sevenNineExtensionVector056Selected5 =
      sevenNineExtensionVector056Base5 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector056_blocker_rows]
  decide

theorem sevenNineExtensionVector056_final_card5 :
    (fastBlocker sevenNineExtensionVector056Base5).card =
      9 := by
  decide

theorem sevenNineExtensionVector056_selection5_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector056
      sevenNineExtensionVector056Selected5 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector056_base5, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector056Base5 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector056Base5 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector056_final_card5]
  decide
def sevenNineExtensionVector056Base6 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {2, 5, 7}, {1, 6, 7}, {1, 3, 4, 7}, {1, 2, 4}, {0, 3, 6}, {0, 3, 4}, {0, 2, 6}, {0, 2, 4}]

theorem sevenNineExtensionVector056_base6 :
    middleFourModelLiftBaseRows sevenNineExtensionVector056
        sevenNineExtensionVector056Selected6 =
      sevenNineExtensionVector056Base6 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector056_blocker_rows]
  decide

theorem sevenNineExtensionVector056_final_card6 :
    (fastBlocker sevenNineExtensionVector056Base6).card =
      9 := by
  decide

theorem sevenNineExtensionVector056_selection6_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector056
      sevenNineExtensionVector056Selected6 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector056_base6, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector056Base6 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector056Base6 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector056_final_card6]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
