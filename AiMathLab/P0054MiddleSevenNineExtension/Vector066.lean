import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector064

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector066 : List Nat :=
  [1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 2, 0, 0]

theorem sevenNineExtensionVector066_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 66 [] =
      sevenNineExtensionVector066 := by
  decide

def sevenNineExtensionVector066BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4}, {2, 6}, {2, 5}, {1, 3, 6}, {1, 3, 5}, {0, 4, 6}, {0, 4, 5}, {0, 1, 6}, {0, 1, 5}]

def sevenNineExtensionVector066Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector066Selected1 :
    List (G413.Row MiddleFourModelPoint) :=
  [{0, 1, 5}]

def sevenNineExtensionVector066Selected2 :
    List (G413.Row MiddleFourModelPoint) :=
  [{0, 1, 6}]

def sevenNineExtensionVector066Selected3 :
    List (G413.Row MiddleFourModelPoint) :=
  [{0, 4, 5}]

def sevenNineExtensionVector066Selected4 :
    List (G413.Row MiddleFourModelPoint) :=
  [{0, 4, 6}]

def sevenNineExtensionVector066Selected5 :
    List (G413.Row MiddleFourModelPoint) :=
  [{1, 3, 5}]

def sevenNineExtensionVector066Selected6 :
    List (G413.Row MiddleFourModelPoint) :=
  [{1, 3, 6}]

def sevenNineExtensionVector066Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector066Selected0, sevenNineExtensionVector066Selected1, sevenNineExtensionVector066Selected2, sevenNineExtensionVector066Selected3, sevenNineExtensionVector066Selected4, sevenNineExtensionVector066Selected5, sevenNineExtensionVector066Selected6]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector066_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector066 =
      sevenNineExtensionVector066BlockerRows := by
  decide

theorem sevenNineExtensionVector066_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector066 =
      sevenNineExtensionVector066Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector066_blocker_rows]
  decide

def sevenNineExtensionVector066Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 7}, {2, 6, 7}, {2, 5, 7}, {1, 3, 6}, {1, 3, 5}, {0, 4, 6}, {0, 4, 5}, {0, 1, 6}, {0, 1, 5}]

theorem sevenNineExtensionVector066_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector066
        sevenNineExtensionVector066Selected0 =
      sevenNineExtensionVector066Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector066_blocker_rows]
  decide

theorem sevenNineExtensionVector066_final_card0 :
    (fastBlocker sevenNineExtensionVector066Base0).card =
      8 := by
  decide

theorem sevenNineExtensionVector066_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector066
      sevenNineExtensionVector066Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector066_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector066Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector066Base0 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector066_final_card0]
  decide
def sevenNineExtensionVector066Base1 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 7}, {2, 6, 7}, {2, 5, 7}, {1, 3, 6}, {1, 3, 5}, {0, 4, 6}, {0, 4, 5}, {0, 1, 6}, {0, 1, 5, 7}]

theorem sevenNineExtensionVector066_base1 :
    middleFourModelLiftBaseRows sevenNineExtensionVector066
        sevenNineExtensionVector066Selected1 =
      sevenNineExtensionVector066Base1 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector066_blocker_rows]
  decide

theorem sevenNineExtensionVector066_final_card1 :
    (fastBlocker sevenNineExtensionVector066Base1).card =
      9 := by
  decide

theorem sevenNineExtensionVector066_selection1_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector066
      sevenNineExtensionVector066Selected1 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector066_base1, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector066Base1 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector066Base1 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector066_final_card1]
  decide
def sevenNineExtensionVector066Base2 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 7}, {2, 6, 7}, {2, 5, 7}, {1, 3, 6}, {1, 3, 5}, {0, 4, 6}, {0, 4, 5}, {0, 1, 6, 7}, {0, 1, 5}]

theorem sevenNineExtensionVector066_base2 :
    middleFourModelLiftBaseRows sevenNineExtensionVector066
        sevenNineExtensionVector066Selected2 =
      sevenNineExtensionVector066Base2 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector066_blocker_rows]
  decide

theorem sevenNineExtensionVector066_final_card2 :
    (fastBlocker sevenNineExtensionVector066Base2).card =
      9 := by
  decide

theorem sevenNineExtensionVector066_selection2_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector066
      sevenNineExtensionVector066Selected2 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector066_base2, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector066Base2 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector066Base2 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector066_final_card2]
  decide
def sevenNineExtensionVector066Base3 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 7}, {2, 6, 7}, {2, 5, 7}, {1, 3, 6}, {1, 3, 5}, {0, 4, 6}, {0, 4, 5, 7}, {0, 1, 6}, {0, 1, 5}]

theorem sevenNineExtensionVector066_base3 :
    middleFourModelLiftBaseRows sevenNineExtensionVector066
        sevenNineExtensionVector066Selected3 =
      sevenNineExtensionVector066Base3 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector066_blocker_rows]
  decide

theorem sevenNineExtensionVector066_final_card3 :
    (fastBlocker sevenNineExtensionVector066Base3).card =
      9 := by
  decide

theorem sevenNineExtensionVector066_selection3_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector066
      sevenNineExtensionVector066Selected3 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector066_base3, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector066Base3 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector066Base3 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector066_final_card3]
  decide
def sevenNineExtensionVector066Base4 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 7}, {2, 6, 7}, {2, 5, 7}, {1, 3, 6}, {1, 3, 5}, {0, 4, 6, 7}, {0, 4, 5}, {0, 1, 6}, {0, 1, 5}]

theorem sevenNineExtensionVector066_base4 :
    middleFourModelLiftBaseRows sevenNineExtensionVector066
        sevenNineExtensionVector066Selected4 =
      sevenNineExtensionVector066Base4 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector066_blocker_rows]
  decide

theorem sevenNineExtensionVector066_final_card4 :
    (fastBlocker sevenNineExtensionVector066Base4).card =
      9 := by
  decide

theorem sevenNineExtensionVector066_selection4_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector066
      sevenNineExtensionVector066Selected4 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector066_base4, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector066Base4 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector066Base4 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector066_final_card4]
  decide
def sevenNineExtensionVector066Base5 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 7}, {2, 6, 7}, {2, 5, 7}, {1, 3, 6}, {1, 3, 5, 7}, {0, 4, 6}, {0, 4, 5}, {0, 1, 6}, {0, 1, 5}]

theorem sevenNineExtensionVector066_base5 :
    middleFourModelLiftBaseRows sevenNineExtensionVector066
        sevenNineExtensionVector066Selected5 =
      sevenNineExtensionVector066Base5 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector066_blocker_rows]
  decide

theorem sevenNineExtensionVector066_final_card5 :
    (fastBlocker sevenNineExtensionVector066Base5).card =
      9 := by
  decide

theorem sevenNineExtensionVector066_selection5_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector066
      sevenNineExtensionVector066Selected5 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector066_base5, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector066Base5 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector066Base5 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector066_final_card5]
  decide
def sevenNineExtensionVector066Base6 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 7}, {2, 6, 7}, {2, 5, 7}, {1, 3, 6, 7}, {1, 3, 5}, {0, 4, 6}, {0, 4, 5}, {0, 1, 6}, {0, 1, 5}]

theorem sevenNineExtensionVector066_base6 :
    middleFourModelLiftBaseRows sevenNineExtensionVector066
        sevenNineExtensionVector066Selected6 =
      sevenNineExtensionVector066Base6 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector066_blocker_rows]
  decide

theorem sevenNineExtensionVector066_final_card6 :
    (fastBlocker sevenNineExtensionVector066Base6).card =
      9 := by
  decide

theorem sevenNineExtensionVector066_selection6_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector066
      sevenNineExtensionVector066Selected6 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector066_base6, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector066Base6 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector066Base6 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector066_final_card6]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
