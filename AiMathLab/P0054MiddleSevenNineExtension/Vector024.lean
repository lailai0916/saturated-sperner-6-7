import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector022

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector024 : List Nat :=
  [1, 0, 0, 0, 1, 2, 0, 1, 1, 1, 0, 0, 0, 0]

theorem sevenNineExtensionVector024_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 24 [] =
      sevenNineExtensionVector024 := by
  decide

def sevenNineExtensionVector024BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5}, {2, 5}, {1, 6}, {1, 3, 4}, {1, 2, 4}, {0, 3, 6}, {0, 3, 4}, {0, 2, 6}, {0, 2, 4}]

def sevenNineExtensionVector024Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector024Selected1 :
    List (G413.Row MiddleFourModelPoint) :=
  [{0, 2, 4}]

def sevenNineExtensionVector024Selected2 :
    List (G413.Row MiddleFourModelPoint) :=
  [{0, 2, 6}]

def sevenNineExtensionVector024Selected3 :
    List (G413.Row MiddleFourModelPoint) :=
  [{0, 3, 4}]

def sevenNineExtensionVector024Selected4 :
    List (G413.Row MiddleFourModelPoint) :=
  [{0, 3, 6}]

def sevenNineExtensionVector024Selected5 :
    List (G413.Row MiddleFourModelPoint) :=
  [{1, 2, 4}]

def sevenNineExtensionVector024Selected6 :
    List (G413.Row MiddleFourModelPoint) :=
  [{1, 3, 4}]

def sevenNineExtensionVector024Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector024Selected0, sevenNineExtensionVector024Selected1, sevenNineExtensionVector024Selected2, sevenNineExtensionVector024Selected3, sevenNineExtensionVector024Selected4, sevenNineExtensionVector024Selected5, sevenNineExtensionVector024Selected6]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector024_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector024 =
      sevenNineExtensionVector024BlockerRows := by
  decide

theorem sevenNineExtensionVector024_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector024 =
      sevenNineExtensionVector024Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector024_blocker_rows]
  decide

def sevenNineExtensionVector024Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {2, 5, 7}, {1, 6, 7}, {1, 3, 4}, {1, 2, 4}, {0, 3, 6}, {0, 3, 4}, {0, 2, 6}, {0, 2, 4}]

theorem sevenNineExtensionVector024_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector024
        sevenNineExtensionVector024Selected0 =
      sevenNineExtensionVector024Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector024_blocker_rows]
  decide

theorem sevenNineExtensionVector024_final_card0 :
    (fastBlocker sevenNineExtensionVector024Base0).card =
      8 := by
  decide

theorem sevenNineExtensionVector024_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector024
      sevenNineExtensionVector024Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector024_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector024Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector024Base0 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector024_final_card0]
  decide
def sevenNineExtensionVector024Base1 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {2, 5, 7}, {1, 6, 7}, {1, 3, 4}, {1, 2, 4}, {0, 3, 6}, {0, 3, 4}, {0, 2, 6}, {0, 2, 4, 7}]

theorem sevenNineExtensionVector024_base1 :
    middleFourModelLiftBaseRows sevenNineExtensionVector024
        sevenNineExtensionVector024Selected1 =
      sevenNineExtensionVector024Base1 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector024_blocker_rows]
  decide

theorem sevenNineExtensionVector024_final_card1 :
    (fastBlocker sevenNineExtensionVector024Base1).card =
      9 := by
  decide

theorem sevenNineExtensionVector024_selection1_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector024
      sevenNineExtensionVector024Selected1 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector024_base1, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector024Base1 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector024Base1 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector024_final_card1]
  decide
def sevenNineExtensionVector024Base2 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {2, 5, 7}, {1, 6, 7}, {1, 3, 4}, {1, 2, 4}, {0, 3, 6}, {0, 3, 4}, {0, 2, 6, 7}, {0, 2, 4}]

theorem sevenNineExtensionVector024_base2 :
    middleFourModelLiftBaseRows sevenNineExtensionVector024
        sevenNineExtensionVector024Selected2 =
      sevenNineExtensionVector024Base2 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector024_blocker_rows]
  decide

theorem sevenNineExtensionVector024_final_card2 :
    (fastBlocker sevenNineExtensionVector024Base2).card =
      9 := by
  decide

theorem sevenNineExtensionVector024_selection2_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector024
      sevenNineExtensionVector024Selected2 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector024_base2, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector024Base2 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector024Base2 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector024_final_card2]
  decide
def sevenNineExtensionVector024Base3 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {2, 5, 7}, {1, 6, 7}, {1, 3, 4}, {1, 2, 4}, {0, 3, 6}, {0, 3, 4, 7}, {0, 2, 6}, {0, 2, 4}]

theorem sevenNineExtensionVector024_base3 :
    middleFourModelLiftBaseRows sevenNineExtensionVector024
        sevenNineExtensionVector024Selected3 =
      sevenNineExtensionVector024Base3 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector024_blocker_rows]
  decide

theorem sevenNineExtensionVector024_final_card3 :
    (fastBlocker sevenNineExtensionVector024Base3).card =
      9 := by
  decide

theorem sevenNineExtensionVector024_selection3_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector024
      sevenNineExtensionVector024Selected3 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector024_base3, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector024Base3 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector024Base3 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector024_final_card3]
  decide
def sevenNineExtensionVector024Base4 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {2, 5, 7}, {1, 6, 7}, {1, 3, 4}, {1, 2, 4}, {0, 3, 6, 7}, {0, 3, 4}, {0, 2, 6}, {0, 2, 4}]

theorem sevenNineExtensionVector024_base4 :
    middleFourModelLiftBaseRows sevenNineExtensionVector024
        sevenNineExtensionVector024Selected4 =
      sevenNineExtensionVector024Base4 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector024_blocker_rows]
  decide

theorem sevenNineExtensionVector024_final_card4 :
    (fastBlocker sevenNineExtensionVector024Base4).card =
      9 := by
  decide

theorem sevenNineExtensionVector024_selection4_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector024
      sevenNineExtensionVector024Selected4 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector024_base4, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector024Base4 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector024Base4 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector024_final_card4]
  decide
def sevenNineExtensionVector024Base5 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {2, 5, 7}, {1, 6, 7}, {1, 3, 4}, {1, 2, 4, 7}, {0, 3, 6}, {0, 3, 4}, {0, 2, 6}, {0, 2, 4}]

theorem sevenNineExtensionVector024_base5 :
    middleFourModelLiftBaseRows sevenNineExtensionVector024
        sevenNineExtensionVector024Selected5 =
      sevenNineExtensionVector024Base5 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector024_blocker_rows]
  decide

theorem sevenNineExtensionVector024_final_card5 :
    (fastBlocker sevenNineExtensionVector024Base5).card =
      9 := by
  decide

theorem sevenNineExtensionVector024_selection5_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector024
      sevenNineExtensionVector024Selected5 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector024_base5, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector024Base5 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector024Base5 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector024_final_card5]
  decide
def sevenNineExtensionVector024Base6 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {2, 5, 7}, {1, 6, 7}, {1, 3, 4, 7}, {1, 2, 4}, {0, 3, 6}, {0, 3, 4}, {0, 2, 6}, {0, 2, 4}]

theorem sevenNineExtensionVector024_base6 :
    middleFourModelLiftBaseRows sevenNineExtensionVector024
        sevenNineExtensionVector024Selected6 =
      sevenNineExtensionVector024Base6 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector024_blocker_rows]
  decide

theorem sevenNineExtensionVector024_final_card6 :
    (fastBlocker sevenNineExtensionVector024Base6).card =
      9 := by
  decide

theorem sevenNineExtensionVector024_selection6_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector024
      sevenNineExtensionVector024Selected6 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector024_base6, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector024Base6 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector024Base6 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector024_final_card6]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
