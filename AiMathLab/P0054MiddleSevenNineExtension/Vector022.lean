import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector020

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector022 : List Nat :=
  [0, 1, 0, 1, 1, 1, 0, 0, 2, 1, 0, 0, 0, 0]

theorem sevenNineExtensionVector022_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 22 [] =
      sevenNineExtensionVector022 := by
  decide

def sevenNineExtensionVector022BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5}, {3, 4}, {2, 6}, {1, 5, 6}, {1, 4, 6}, {0, 2, 5}, {0, 2, 4}, {0, 1, 5}, {0, 1, 4}]

def sevenNineExtensionVector022Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector022Selected1 :
    List (G413.Row MiddleFourModelPoint) :=
  [{0, 1, 4}]

def sevenNineExtensionVector022Selected2 :
    List (G413.Row MiddleFourModelPoint) :=
  [{0, 1, 5}]

def sevenNineExtensionVector022Selected3 :
    List (G413.Row MiddleFourModelPoint) :=
  [{0, 2, 4}]

def sevenNineExtensionVector022Selected4 :
    List (G413.Row MiddleFourModelPoint) :=
  [{0, 2, 5}]

def sevenNineExtensionVector022Selected5 :
    List (G413.Row MiddleFourModelPoint) :=
  [{1, 4, 6}]

def sevenNineExtensionVector022Selected6 :
    List (G413.Row MiddleFourModelPoint) :=
  [{1, 5, 6}]

def sevenNineExtensionVector022Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector022Selected0, sevenNineExtensionVector022Selected1, sevenNineExtensionVector022Selected2, sevenNineExtensionVector022Selected3, sevenNineExtensionVector022Selected4, sevenNineExtensionVector022Selected5, sevenNineExtensionVector022Selected6]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector022_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector022 =
      sevenNineExtensionVector022BlockerRows := by
  decide

theorem sevenNineExtensionVector022_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector022 =
      sevenNineExtensionVector022Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector022_blocker_rows]
  decide

def sevenNineExtensionVector022Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {3, 4, 7}, {2, 6, 7}, {1, 5, 6}, {1, 4, 6}, {0, 2, 5}, {0, 2, 4}, {0, 1, 5}, {0, 1, 4}]

theorem sevenNineExtensionVector022_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector022
        sevenNineExtensionVector022Selected0 =
      sevenNineExtensionVector022Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector022_blocker_rows]
  decide

theorem sevenNineExtensionVector022_final_card0 :
    (fastBlocker sevenNineExtensionVector022Base0).card =
      8 := by
  decide

theorem sevenNineExtensionVector022_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector022
      sevenNineExtensionVector022Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector022_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector022Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector022Base0 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector022_final_card0]
  decide
def sevenNineExtensionVector022Base1 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {3, 4, 7}, {2, 6, 7}, {1, 5, 6}, {1, 4, 6}, {0, 2, 5}, {0, 2, 4}, {0, 1, 5}, {0, 1, 4, 7}]

theorem sevenNineExtensionVector022_base1 :
    middleFourModelLiftBaseRows sevenNineExtensionVector022
        sevenNineExtensionVector022Selected1 =
      sevenNineExtensionVector022Base1 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector022_blocker_rows]
  decide

theorem sevenNineExtensionVector022_final_card1 :
    (fastBlocker sevenNineExtensionVector022Base1).card =
      9 := by
  decide

theorem sevenNineExtensionVector022_selection1_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector022
      sevenNineExtensionVector022Selected1 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector022_base1, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector022Base1 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector022Base1 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector022_final_card1]
  decide
def sevenNineExtensionVector022Base2 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {3, 4, 7}, {2, 6, 7}, {1, 5, 6}, {1, 4, 6}, {0, 2, 5}, {0, 2, 4}, {0, 1, 5, 7}, {0, 1, 4}]

theorem sevenNineExtensionVector022_base2 :
    middleFourModelLiftBaseRows sevenNineExtensionVector022
        sevenNineExtensionVector022Selected2 =
      sevenNineExtensionVector022Base2 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector022_blocker_rows]
  decide

theorem sevenNineExtensionVector022_final_card2 :
    (fastBlocker sevenNineExtensionVector022Base2).card =
      9 := by
  decide

theorem sevenNineExtensionVector022_selection2_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector022
      sevenNineExtensionVector022Selected2 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector022_base2, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector022Base2 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector022Base2 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector022_final_card2]
  decide
def sevenNineExtensionVector022Base3 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {3, 4, 7}, {2, 6, 7}, {1, 5, 6}, {1, 4, 6}, {0, 2, 5}, {0, 2, 4, 7}, {0, 1, 5}, {0, 1, 4}]

theorem sevenNineExtensionVector022_base3 :
    middleFourModelLiftBaseRows sevenNineExtensionVector022
        sevenNineExtensionVector022Selected3 =
      sevenNineExtensionVector022Base3 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector022_blocker_rows]
  decide

theorem sevenNineExtensionVector022_final_card3 :
    (fastBlocker sevenNineExtensionVector022Base3).card =
      9 := by
  decide

theorem sevenNineExtensionVector022_selection3_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector022
      sevenNineExtensionVector022Selected3 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector022_base3, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector022Base3 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector022Base3 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector022_final_card3]
  decide
def sevenNineExtensionVector022Base4 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {3, 4, 7}, {2, 6, 7}, {1, 5, 6}, {1, 4, 6}, {0, 2, 5, 7}, {0, 2, 4}, {0, 1, 5}, {0, 1, 4}]

theorem sevenNineExtensionVector022_base4 :
    middleFourModelLiftBaseRows sevenNineExtensionVector022
        sevenNineExtensionVector022Selected4 =
      sevenNineExtensionVector022Base4 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector022_blocker_rows]
  decide

theorem sevenNineExtensionVector022_final_card4 :
    (fastBlocker sevenNineExtensionVector022Base4).card =
      9 := by
  decide

theorem sevenNineExtensionVector022_selection4_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector022
      sevenNineExtensionVector022Selected4 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector022_base4, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector022Base4 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector022Base4 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector022_final_card4]
  decide
def sevenNineExtensionVector022Base5 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {3, 4, 7}, {2, 6, 7}, {1, 5, 6}, {1, 4, 6, 7}, {0, 2, 5}, {0, 2, 4}, {0, 1, 5}, {0, 1, 4}]

theorem sevenNineExtensionVector022_base5 :
    middleFourModelLiftBaseRows sevenNineExtensionVector022
        sevenNineExtensionVector022Selected5 =
      sevenNineExtensionVector022Base5 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector022_blocker_rows]
  decide

theorem sevenNineExtensionVector022_final_card5 :
    (fastBlocker sevenNineExtensionVector022Base5).card =
      9 := by
  decide

theorem sevenNineExtensionVector022_selection5_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector022
      sevenNineExtensionVector022Selected5 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector022_base5, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector022Base5 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector022Base5 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector022_final_card5]
  decide
def sevenNineExtensionVector022Base6 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {3, 4, 7}, {2, 6, 7}, {1, 5, 6, 7}, {1, 4, 6}, {0, 2, 5}, {0, 2, 4}, {0, 1, 5}, {0, 1, 4}]

theorem sevenNineExtensionVector022_base6 :
    middleFourModelLiftBaseRows sevenNineExtensionVector022
        sevenNineExtensionVector022Selected6 =
      sevenNineExtensionVector022Base6 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector022_blocker_rows]
  decide

theorem sevenNineExtensionVector022_final_card6 :
    (fastBlocker sevenNineExtensionVector022Base6).card =
      9 := by
  decide

theorem sevenNineExtensionVector022_selection6_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector022
      sevenNineExtensionVector022Selected6 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector022_base6, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector022Base6 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector022Base6 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector022_final_card6]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
