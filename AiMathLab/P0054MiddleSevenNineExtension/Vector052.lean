import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector050

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector052 : List Nat :=
  [0, 1, 1, 1, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0]

theorem sevenNineExtensionVector052_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 52 [] =
      sevenNineExtensionVector052 := by
  decide

def sevenNineExtensionVector052BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5}, {3, 4}, {1, 6}, {1, 2, 5}, {1, 2, 4}, {0, 5, 6}, {0, 4, 6}, {0, 2, 5}, {0, 2, 4}]

def sevenNineExtensionVector052Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector052Selected1 :
    List (G413.Row MiddleFourModelPoint) :=
  [{0, 2, 4}]

def sevenNineExtensionVector052Selected2 :
    List (G413.Row MiddleFourModelPoint) :=
  [{0, 2, 5}]

def sevenNineExtensionVector052Selected3 :
    List (G413.Row MiddleFourModelPoint) :=
  [{0, 4, 6}]

def sevenNineExtensionVector052Selected4 :
    List (G413.Row MiddleFourModelPoint) :=
  [{0, 5, 6}]

def sevenNineExtensionVector052Selected5 :
    List (G413.Row MiddleFourModelPoint) :=
  [{1, 2, 4}]

def sevenNineExtensionVector052Selected6 :
    List (G413.Row MiddleFourModelPoint) :=
  [{1, 2, 5}]

def sevenNineExtensionVector052Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector052Selected0, sevenNineExtensionVector052Selected1, sevenNineExtensionVector052Selected2, sevenNineExtensionVector052Selected3, sevenNineExtensionVector052Selected4, sevenNineExtensionVector052Selected5, sevenNineExtensionVector052Selected6]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector052_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector052 =
      sevenNineExtensionVector052BlockerRows := by
  decide

theorem sevenNineExtensionVector052_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector052 =
      sevenNineExtensionVector052Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector052_blocker_rows]
  decide

def sevenNineExtensionVector052Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {3, 4, 7}, {1, 6, 7}, {1, 2, 5}, {1, 2, 4}, {0, 5, 6}, {0, 4, 6}, {0, 2, 5}, {0, 2, 4}]

theorem sevenNineExtensionVector052_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector052
        sevenNineExtensionVector052Selected0 =
      sevenNineExtensionVector052Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector052_blocker_rows]
  decide

theorem sevenNineExtensionVector052_final_card0 :
    (fastBlocker sevenNineExtensionVector052Base0).card =
      8 := by
  decide

theorem sevenNineExtensionVector052_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector052
      sevenNineExtensionVector052Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector052_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector052Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector052Base0 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector052_final_card0]
  decide
def sevenNineExtensionVector052Base1 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {3, 4, 7}, {1, 6, 7}, {1, 2, 5}, {1, 2, 4}, {0, 5, 6}, {0, 4, 6}, {0, 2, 5}, {0, 2, 4, 7}]

theorem sevenNineExtensionVector052_base1 :
    middleFourModelLiftBaseRows sevenNineExtensionVector052
        sevenNineExtensionVector052Selected1 =
      sevenNineExtensionVector052Base1 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector052_blocker_rows]
  decide

theorem sevenNineExtensionVector052_final_card1 :
    (fastBlocker sevenNineExtensionVector052Base1).card =
      9 := by
  decide

theorem sevenNineExtensionVector052_selection1_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector052
      sevenNineExtensionVector052Selected1 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector052_base1, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector052Base1 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector052Base1 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector052_final_card1]
  decide
def sevenNineExtensionVector052Base2 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {3, 4, 7}, {1, 6, 7}, {1, 2, 5}, {1, 2, 4}, {0, 5, 6}, {0, 4, 6}, {0, 2, 5, 7}, {0, 2, 4}]

theorem sevenNineExtensionVector052_base2 :
    middleFourModelLiftBaseRows sevenNineExtensionVector052
        sevenNineExtensionVector052Selected2 =
      sevenNineExtensionVector052Base2 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector052_blocker_rows]
  decide

theorem sevenNineExtensionVector052_final_card2 :
    (fastBlocker sevenNineExtensionVector052Base2).card =
      9 := by
  decide

theorem sevenNineExtensionVector052_selection2_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector052
      sevenNineExtensionVector052Selected2 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector052_base2, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector052Base2 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector052Base2 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector052_final_card2]
  decide
def sevenNineExtensionVector052Base3 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {3, 4, 7}, {1, 6, 7}, {1, 2, 5}, {1, 2, 4}, {0, 5, 6}, {0, 4, 6, 7}, {0, 2, 5}, {0, 2, 4}]

theorem sevenNineExtensionVector052_base3 :
    middleFourModelLiftBaseRows sevenNineExtensionVector052
        sevenNineExtensionVector052Selected3 =
      sevenNineExtensionVector052Base3 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector052_blocker_rows]
  decide

theorem sevenNineExtensionVector052_final_card3 :
    (fastBlocker sevenNineExtensionVector052Base3).card =
      9 := by
  decide

theorem sevenNineExtensionVector052_selection3_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector052
      sevenNineExtensionVector052Selected3 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector052_base3, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector052Base3 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector052Base3 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector052_final_card3]
  decide
def sevenNineExtensionVector052Base4 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {3, 4, 7}, {1, 6, 7}, {1, 2, 5}, {1, 2, 4}, {0, 5, 6, 7}, {0, 4, 6}, {0, 2, 5}, {0, 2, 4}]

theorem sevenNineExtensionVector052_base4 :
    middleFourModelLiftBaseRows sevenNineExtensionVector052
        sevenNineExtensionVector052Selected4 =
      sevenNineExtensionVector052Base4 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector052_blocker_rows]
  decide

theorem sevenNineExtensionVector052_final_card4 :
    (fastBlocker sevenNineExtensionVector052Base4).card =
      9 := by
  decide

theorem sevenNineExtensionVector052_selection4_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector052
      sevenNineExtensionVector052Selected4 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector052_base4, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector052Base4 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector052Base4 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector052_final_card4]
  decide
def sevenNineExtensionVector052Base5 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {3, 4, 7}, {1, 6, 7}, {1, 2, 5}, {1, 2, 4, 7}, {0, 5, 6}, {0, 4, 6}, {0, 2, 5}, {0, 2, 4}]

theorem sevenNineExtensionVector052_base5 :
    middleFourModelLiftBaseRows sevenNineExtensionVector052
        sevenNineExtensionVector052Selected5 =
      sevenNineExtensionVector052Base5 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector052_blocker_rows]
  decide

theorem sevenNineExtensionVector052_final_card5 :
    (fastBlocker sevenNineExtensionVector052Base5).card =
      9 := by
  decide

theorem sevenNineExtensionVector052_selection5_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector052
      sevenNineExtensionVector052Selected5 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector052_base5, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector052Base5 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector052Base5 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector052_final_card5]
  decide
def sevenNineExtensionVector052Base6 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {3, 4, 7}, {1, 6, 7}, {1, 2, 5, 7}, {1, 2, 4}, {0, 5, 6}, {0, 4, 6}, {0, 2, 5}, {0, 2, 4}]

theorem sevenNineExtensionVector052_base6 :
    middleFourModelLiftBaseRows sevenNineExtensionVector052
        sevenNineExtensionVector052Selected6 =
      sevenNineExtensionVector052Base6 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector052_blocker_rows]
  decide

theorem sevenNineExtensionVector052_final_card6 :
    (fastBlocker sevenNineExtensionVector052Base6).card =
      9 := by
  decide

theorem sevenNineExtensionVector052_selection6_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector052
      sevenNineExtensionVector052Selected6 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector052_base6, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector052Base6 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector052Base6 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector052_final_card6]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
