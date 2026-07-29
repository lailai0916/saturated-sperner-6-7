import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector046

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector048 : List Nat :=
  [1, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0]

theorem sevenNineExtensionVector048_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 48 [] =
      sevenNineExtensionVector048 := by
  decide

def sevenNineExtensionVector048BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4}, {2, 6}, {2, 5}, {1, 4, 6}, {1, 4, 5}, {0, 3, 6}, {0, 3, 5}, {0, 1, 6}, {0, 1, 5}]

def sevenNineExtensionVector048Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector048Selected1 :
    List (G413.Row MiddleFourModelPoint) :=
  [{0, 1, 5}]

def sevenNineExtensionVector048Selected2 :
    List (G413.Row MiddleFourModelPoint) :=
  [{0, 1, 6}]

def sevenNineExtensionVector048Selected3 :
    List (G413.Row MiddleFourModelPoint) :=
  [{0, 3, 5}]

def sevenNineExtensionVector048Selected4 :
    List (G413.Row MiddleFourModelPoint) :=
  [{0, 3, 6}]

def sevenNineExtensionVector048Selected5 :
    List (G413.Row MiddleFourModelPoint) :=
  [{1, 4, 5}]

def sevenNineExtensionVector048Selected6 :
    List (G413.Row MiddleFourModelPoint) :=
  [{1, 4, 6}]

def sevenNineExtensionVector048Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector048Selected0, sevenNineExtensionVector048Selected1, sevenNineExtensionVector048Selected2, sevenNineExtensionVector048Selected3, sevenNineExtensionVector048Selected4, sevenNineExtensionVector048Selected5, sevenNineExtensionVector048Selected6]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector048_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector048 =
      sevenNineExtensionVector048BlockerRows := by
  decide

theorem sevenNineExtensionVector048_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector048 =
      sevenNineExtensionVector048Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector048_blocker_rows]
  decide

def sevenNineExtensionVector048Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 7}, {2, 6, 7}, {2, 5, 7}, {1, 4, 6}, {1, 4, 5}, {0, 3, 6}, {0, 3, 5}, {0, 1, 6}, {0, 1, 5}]

theorem sevenNineExtensionVector048_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector048
        sevenNineExtensionVector048Selected0 =
      sevenNineExtensionVector048Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector048_blocker_rows]
  decide

theorem sevenNineExtensionVector048_final_card0 :
    (fastBlocker sevenNineExtensionVector048Base0).card =
      8 := by
  decide

theorem sevenNineExtensionVector048_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector048
      sevenNineExtensionVector048Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector048_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector048Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector048Base0 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector048_final_card0]
  decide
def sevenNineExtensionVector048Base1 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 7}, {2, 6, 7}, {2, 5, 7}, {1, 4, 6}, {1, 4, 5}, {0, 3, 6}, {0, 3, 5}, {0, 1, 6}, {0, 1, 5, 7}]

theorem sevenNineExtensionVector048_base1 :
    middleFourModelLiftBaseRows sevenNineExtensionVector048
        sevenNineExtensionVector048Selected1 =
      sevenNineExtensionVector048Base1 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector048_blocker_rows]
  decide

theorem sevenNineExtensionVector048_final_card1 :
    (fastBlocker sevenNineExtensionVector048Base1).card =
      9 := by
  decide

theorem sevenNineExtensionVector048_selection1_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector048
      sevenNineExtensionVector048Selected1 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector048_base1, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector048Base1 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector048Base1 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector048_final_card1]
  decide
def sevenNineExtensionVector048Base2 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 7}, {2, 6, 7}, {2, 5, 7}, {1, 4, 6}, {1, 4, 5}, {0, 3, 6}, {0, 3, 5}, {0, 1, 6, 7}, {0, 1, 5}]

theorem sevenNineExtensionVector048_base2 :
    middleFourModelLiftBaseRows sevenNineExtensionVector048
        sevenNineExtensionVector048Selected2 =
      sevenNineExtensionVector048Base2 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector048_blocker_rows]
  decide

theorem sevenNineExtensionVector048_final_card2 :
    (fastBlocker sevenNineExtensionVector048Base2).card =
      9 := by
  decide

theorem sevenNineExtensionVector048_selection2_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector048
      sevenNineExtensionVector048Selected2 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector048_base2, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector048Base2 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector048Base2 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector048_final_card2]
  decide
def sevenNineExtensionVector048Base3 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 7}, {2, 6, 7}, {2, 5, 7}, {1, 4, 6}, {1, 4, 5}, {0, 3, 6}, {0, 3, 5, 7}, {0, 1, 6}, {0, 1, 5}]

theorem sevenNineExtensionVector048_base3 :
    middleFourModelLiftBaseRows sevenNineExtensionVector048
        sevenNineExtensionVector048Selected3 =
      sevenNineExtensionVector048Base3 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector048_blocker_rows]
  decide

theorem sevenNineExtensionVector048_final_card3 :
    (fastBlocker sevenNineExtensionVector048Base3).card =
      9 := by
  decide

theorem sevenNineExtensionVector048_selection3_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector048
      sevenNineExtensionVector048Selected3 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector048_base3, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector048Base3 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector048Base3 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector048_final_card3]
  decide
def sevenNineExtensionVector048Base4 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 7}, {2, 6, 7}, {2, 5, 7}, {1, 4, 6}, {1, 4, 5}, {0, 3, 6, 7}, {0, 3, 5}, {0, 1, 6}, {0, 1, 5}]

theorem sevenNineExtensionVector048_base4 :
    middleFourModelLiftBaseRows sevenNineExtensionVector048
        sevenNineExtensionVector048Selected4 =
      sevenNineExtensionVector048Base4 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector048_blocker_rows]
  decide

theorem sevenNineExtensionVector048_final_card4 :
    (fastBlocker sevenNineExtensionVector048Base4).card =
      9 := by
  decide

theorem sevenNineExtensionVector048_selection4_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector048
      sevenNineExtensionVector048Selected4 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector048_base4, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector048Base4 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector048Base4 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector048_final_card4]
  decide
def sevenNineExtensionVector048Base5 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 7}, {2, 6, 7}, {2, 5, 7}, {1, 4, 6}, {1, 4, 5, 7}, {0, 3, 6}, {0, 3, 5}, {0, 1, 6}, {0, 1, 5}]

theorem sevenNineExtensionVector048_base5 :
    middleFourModelLiftBaseRows sevenNineExtensionVector048
        sevenNineExtensionVector048Selected5 =
      sevenNineExtensionVector048Base5 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector048_blocker_rows]
  decide

theorem sevenNineExtensionVector048_final_card5 :
    (fastBlocker sevenNineExtensionVector048Base5).card =
      9 := by
  decide

theorem sevenNineExtensionVector048_selection5_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector048
      sevenNineExtensionVector048Selected5 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector048_base5, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector048Base5 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector048Base5 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector048_final_card5]
  decide
def sevenNineExtensionVector048Base6 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 7}, {2, 6, 7}, {2, 5, 7}, {1, 4, 6, 7}, {1, 4, 5}, {0, 3, 6}, {0, 3, 5}, {0, 1, 6}, {0, 1, 5}]

theorem sevenNineExtensionVector048_base6 :
    middleFourModelLiftBaseRows sevenNineExtensionVector048
        sevenNineExtensionVector048Selected6 =
      sevenNineExtensionVector048Base6 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector048_blocker_rows]
  decide

theorem sevenNineExtensionVector048_final_card6 :
    (fastBlocker sevenNineExtensionVector048Base6).card =
      9 := by
  decide

theorem sevenNineExtensionVector048_selection6_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector048
      sevenNineExtensionVector048Selected6 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector048_base6, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector048Base6 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector048Base6 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector048_final_card6]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
