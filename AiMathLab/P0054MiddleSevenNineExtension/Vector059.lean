import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector057

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector059 : List Nat :=
  [0, 0, 2, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0]

theorem sevenNineExtensionVector059_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 59 [] =
      sevenNineExtensionVector059 := by
  decide

def sevenNineExtensionVector059BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5}, {1, 6}, {1, 3, 4}, {1, 2, 5}, {1, 2, 4}, {0, 6}, {0, 3, 4}, {0, 2, 5}, {0, 2, 4}]

def sevenNineExtensionVector059Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector059Selected1 :
    List (G413.Row MiddleFourModelPoint) :=
  [{0, 2, 4}]

def sevenNineExtensionVector059Selected2 :
    List (G413.Row MiddleFourModelPoint) :=
  [{0, 2, 5}]

def sevenNineExtensionVector059Selected3 :
    List (G413.Row MiddleFourModelPoint) :=
  [{0, 3, 4}]

def sevenNineExtensionVector059Selected4 :
    List (G413.Row MiddleFourModelPoint) :=
  [{1, 2, 4}]

def sevenNineExtensionVector059Selected5 :
    List (G413.Row MiddleFourModelPoint) :=
  [{1, 2, 5}]

def sevenNineExtensionVector059Selected6 :
    List (G413.Row MiddleFourModelPoint) :=
  [{1, 3, 4}]

def sevenNineExtensionVector059Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector059Selected0, sevenNineExtensionVector059Selected1, sevenNineExtensionVector059Selected2, sevenNineExtensionVector059Selected3, sevenNineExtensionVector059Selected4, sevenNineExtensionVector059Selected5, sevenNineExtensionVector059Selected6]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector059_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector059 =
      sevenNineExtensionVector059BlockerRows := by
  decide

theorem sevenNineExtensionVector059_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector059 =
      sevenNineExtensionVector059Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector059_blocker_rows]
  decide

def sevenNineExtensionVector059Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {1, 6, 7}, {1, 3, 4}, {1, 2, 5}, {1, 2, 4}, {0, 6, 7}, {0, 3, 4}, {0, 2, 5}, {0, 2, 4}]

theorem sevenNineExtensionVector059_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector059
        sevenNineExtensionVector059Selected0 =
      sevenNineExtensionVector059Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector059_blocker_rows]
  decide

theorem sevenNineExtensionVector059_final_card0 :
    (fastBlocker sevenNineExtensionVector059Base0).card =
      8 := by
  decide

theorem sevenNineExtensionVector059_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector059
      sevenNineExtensionVector059Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector059_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector059Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector059Base0 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector059_final_card0]
  decide
def sevenNineExtensionVector059Base1 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {1, 6, 7}, {1, 3, 4}, {1, 2, 5}, {1, 2, 4}, {0, 6, 7}, {0, 3, 4}, {0, 2, 5}, {0, 2, 4, 7}]

theorem sevenNineExtensionVector059_base1 :
    middleFourModelLiftBaseRows sevenNineExtensionVector059
        sevenNineExtensionVector059Selected1 =
      sevenNineExtensionVector059Base1 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector059_blocker_rows]
  decide

theorem sevenNineExtensionVector059_final_card1 :
    (fastBlocker sevenNineExtensionVector059Base1).card =
      9 := by
  decide

theorem sevenNineExtensionVector059_selection1_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector059
      sevenNineExtensionVector059Selected1 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector059_base1, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector059Base1 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector059Base1 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector059_final_card1]
  decide
def sevenNineExtensionVector059Base2 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {1, 6, 7}, {1, 3, 4}, {1, 2, 5}, {1, 2, 4}, {0, 6, 7}, {0, 3, 4}, {0, 2, 5, 7}, {0, 2, 4}]

theorem sevenNineExtensionVector059_base2 :
    middleFourModelLiftBaseRows sevenNineExtensionVector059
        sevenNineExtensionVector059Selected2 =
      sevenNineExtensionVector059Base2 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector059_blocker_rows]
  decide

theorem sevenNineExtensionVector059_final_card2 :
    (fastBlocker sevenNineExtensionVector059Base2).card =
      9 := by
  decide

theorem sevenNineExtensionVector059_selection2_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector059
      sevenNineExtensionVector059Selected2 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector059_base2, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector059Base2 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector059Base2 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector059_final_card2]
  decide
def sevenNineExtensionVector059Base3 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {1, 6, 7}, {1, 3, 4}, {1, 2, 5}, {1, 2, 4}, {0, 6, 7}, {0, 3, 4, 7}, {0, 2, 5}, {0, 2, 4}]

theorem sevenNineExtensionVector059_base3 :
    middleFourModelLiftBaseRows sevenNineExtensionVector059
        sevenNineExtensionVector059Selected3 =
      sevenNineExtensionVector059Base3 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector059_blocker_rows]
  decide

theorem sevenNineExtensionVector059_final_card3 :
    (fastBlocker sevenNineExtensionVector059Base3).card =
      9 := by
  decide

theorem sevenNineExtensionVector059_selection3_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector059
      sevenNineExtensionVector059Selected3 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector059_base3, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector059Base3 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector059Base3 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector059_final_card3]
  decide
def sevenNineExtensionVector059Base4 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {1, 6, 7}, {1, 3, 4}, {1, 2, 5}, {1, 2, 4, 7}, {0, 6, 7}, {0, 3, 4}, {0, 2, 5}, {0, 2, 4}]

theorem sevenNineExtensionVector059_base4 :
    middleFourModelLiftBaseRows sevenNineExtensionVector059
        sevenNineExtensionVector059Selected4 =
      sevenNineExtensionVector059Base4 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector059_blocker_rows]
  decide

theorem sevenNineExtensionVector059_final_card4 :
    (fastBlocker sevenNineExtensionVector059Base4).card =
      9 := by
  decide

theorem sevenNineExtensionVector059_selection4_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector059
      sevenNineExtensionVector059Selected4 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector059_base4, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector059Base4 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector059Base4 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector059_final_card4]
  decide
def sevenNineExtensionVector059Base5 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {1, 6, 7}, {1, 3, 4}, {1, 2, 5, 7}, {1, 2, 4}, {0, 6, 7}, {0, 3, 4}, {0, 2, 5}, {0, 2, 4}]

theorem sevenNineExtensionVector059_base5 :
    middleFourModelLiftBaseRows sevenNineExtensionVector059
        sevenNineExtensionVector059Selected5 =
      sevenNineExtensionVector059Base5 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector059_blocker_rows]
  decide

theorem sevenNineExtensionVector059_final_card5 :
    (fastBlocker sevenNineExtensionVector059Base5).card =
      9 := by
  decide

theorem sevenNineExtensionVector059_selection5_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector059
      sevenNineExtensionVector059Selected5 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector059_base5, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector059Base5 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector059Base5 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector059_final_card5]
  decide
def sevenNineExtensionVector059Base6 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {1, 6, 7}, {1, 3, 4, 7}, {1, 2, 5}, {1, 2, 4}, {0, 6, 7}, {0, 3, 4}, {0, 2, 5}, {0, 2, 4}]

theorem sevenNineExtensionVector059_base6 :
    middleFourModelLiftBaseRows sevenNineExtensionVector059
        sevenNineExtensionVector059Selected6 =
      sevenNineExtensionVector059Base6 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector059_blocker_rows]
  decide

theorem sevenNineExtensionVector059_final_card6 :
    (fastBlocker sevenNineExtensionVector059Base6).card =
      9 := by
  decide

theorem sevenNineExtensionVector059_selection6_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector059
      sevenNineExtensionVector059Selected6 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector059_base6, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector059Base6 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector059Base6 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector059_final_card6]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
