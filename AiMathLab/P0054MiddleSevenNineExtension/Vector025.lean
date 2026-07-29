import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector023

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector025 : List Nat :=
  [0, 1, 0, 0, 2, 1, 0, 1, 1, 1, 0, 0, 0, 0]

theorem sevenNineExtensionVector025_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 25 [] =
      sevenNineExtensionVector025 := by
  decide

def sevenNineExtensionVector025BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5}, {2, 6}, {2, 3, 4}, {1, 6}, {1, 3, 4}, {0, 2, 5}, {0, 2, 4}, {0, 1, 5}, {0, 1, 4}]

def sevenNineExtensionVector025Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector025Selected1 :
    List (G413.Row MiddleFourModelPoint) :=
  [{0, 1, 4}]

def sevenNineExtensionVector025Selected2 :
    List (G413.Row MiddleFourModelPoint) :=
  [{0, 1, 5}]

def sevenNineExtensionVector025Selected3 :
    List (G413.Row MiddleFourModelPoint) :=
  [{0, 2, 4}]

def sevenNineExtensionVector025Selected4 :
    List (G413.Row MiddleFourModelPoint) :=
  [{0, 2, 5}]

def sevenNineExtensionVector025Selected5 :
    List (G413.Row MiddleFourModelPoint) :=
  [{1, 3, 4}]

def sevenNineExtensionVector025Selected6 :
    List (G413.Row MiddleFourModelPoint) :=
  [{2, 3, 4}]

def sevenNineExtensionVector025Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector025Selected0, sevenNineExtensionVector025Selected1, sevenNineExtensionVector025Selected2, sevenNineExtensionVector025Selected3, sevenNineExtensionVector025Selected4, sevenNineExtensionVector025Selected5, sevenNineExtensionVector025Selected6]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector025_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector025 =
      sevenNineExtensionVector025BlockerRows := by
  decide

theorem sevenNineExtensionVector025_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector025 =
      sevenNineExtensionVector025Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector025_blocker_rows]
  decide

def sevenNineExtensionVector025Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {2, 6, 7}, {2, 3, 4}, {1, 6, 7}, {1, 3, 4}, {0, 2, 5}, {0, 2, 4}, {0, 1, 5}, {0, 1, 4}]

theorem sevenNineExtensionVector025_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector025
        sevenNineExtensionVector025Selected0 =
      sevenNineExtensionVector025Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector025_blocker_rows]
  decide

theorem sevenNineExtensionVector025_final_card0 :
    (fastBlocker sevenNineExtensionVector025Base0).card =
      8 := by
  decide

theorem sevenNineExtensionVector025_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector025
      sevenNineExtensionVector025Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector025_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector025Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector025Base0 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector025_final_card0]
  decide
def sevenNineExtensionVector025Base1 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {2, 6, 7}, {2, 3, 4}, {1, 6, 7}, {1, 3, 4}, {0, 2, 5}, {0, 2, 4}, {0, 1, 5}, {0, 1, 4, 7}]

theorem sevenNineExtensionVector025_base1 :
    middleFourModelLiftBaseRows sevenNineExtensionVector025
        sevenNineExtensionVector025Selected1 =
      sevenNineExtensionVector025Base1 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector025_blocker_rows]
  decide

theorem sevenNineExtensionVector025_final_card1 :
    (fastBlocker sevenNineExtensionVector025Base1).card =
      9 := by
  decide

theorem sevenNineExtensionVector025_selection1_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector025
      sevenNineExtensionVector025Selected1 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector025_base1, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector025Base1 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector025Base1 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector025_final_card1]
  decide
def sevenNineExtensionVector025Base2 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {2, 6, 7}, {2, 3, 4}, {1, 6, 7}, {1, 3, 4}, {0, 2, 5}, {0, 2, 4}, {0, 1, 5, 7}, {0, 1, 4}]

theorem sevenNineExtensionVector025_base2 :
    middleFourModelLiftBaseRows sevenNineExtensionVector025
        sevenNineExtensionVector025Selected2 =
      sevenNineExtensionVector025Base2 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector025_blocker_rows]
  decide

theorem sevenNineExtensionVector025_final_card2 :
    (fastBlocker sevenNineExtensionVector025Base2).card =
      9 := by
  decide

theorem sevenNineExtensionVector025_selection2_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector025
      sevenNineExtensionVector025Selected2 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector025_base2, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector025Base2 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector025Base2 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector025_final_card2]
  decide
def sevenNineExtensionVector025Base3 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {2, 6, 7}, {2, 3, 4}, {1, 6, 7}, {1, 3, 4}, {0, 2, 5}, {0, 2, 4, 7}, {0, 1, 5}, {0, 1, 4}]

theorem sevenNineExtensionVector025_base3 :
    middleFourModelLiftBaseRows sevenNineExtensionVector025
        sevenNineExtensionVector025Selected3 =
      sevenNineExtensionVector025Base3 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector025_blocker_rows]
  decide

theorem sevenNineExtensionVector025_final_card3 :
    (fastBlocker sevenNineExtensionVector025Base3).card =
      9 := by
  decide

theorem sevenNineExtensionVector025_selection3_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector025
      sevenNineExtensionVector025Selected3 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector025_base3, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector025Base3 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector025Base3 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector025_final_card3]
  decide
def sevenNineExtensionVector025Base4 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {2, 6, 7}, {2, 3, 4}, {1, 6, 7}, {1, 3, 4}, {0, 2, 5, 7}, {0, 2, 4}, {0, 1, 5}, {0, 1, 4}]

theorem sevenNineExtensionVector025_base4 :
    middleFourModelLiftBaseRows sevenNineExtensionVector025
        sevenNineExtensionVector025Selected4 =
      sevenNineExtensionVector025Base4 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector025_blocker_rows]
  decide

theorem sevenNineExtensionVector025_final_card4 :
    (fastBlocker sevenNineExtensionVector025Base4).card =
      9 := by
  decide

theorem sevenNineExtensionVector025_selection4_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector025
      sevenNineExtensionVector025Selected4 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector025_base4, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector025Base4 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector025Base4 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector025_final_card4]
  decide
def sevenNineExtensionVector025Base5 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {2, 6, 7}, {2, 3, 4}, {1, 6, 7}, {1, 3, 4, 7}, {0, 2, 5}, {0, 2, 4}, {0, 1, 5}, {0, 1, 4}]

theorem sevenNineExtensionVector025_base5 :
    middleFourModelLiftBaseRows sevenNineExtensionVector025
        sevenNineExtensionVector025Selected5 =
      sevenNineExtensionVector025Base5 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector025_blocker_rows]
  decide

theorem sevenNineExtensionVector025_final_card5 :
    (fastBlocker sevenNineExtensionVector025Base5).card =
      9 := by
  decide

theorem sevenNineExtensionVector025_selection5_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector025
      sevenNineExtensionVector025Selected5 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector025_base5, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector025Base5 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector025Base5 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector025_final_card5]
  decide
def sevenNineExtensionVector025Base6 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {2, 6, 7}, {2, 3, 4, 7}, {1, 6, 7}, {1, 3, 4}, {0, 2, 5}, {0, 2, 4}, {0, 1, 5}, {0, 1, 4}]

theorem sevenNineExtensionVector025_base6 :
    middleFourModelLiftBaseRows sevenNineExtensionVector025
        sevenNineExtensionVector025Selected6 =
      sevenNineExtensionVector025Base6 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector025_blocker_rows]
  decide

theorem sevenNineExtensionVector025_final_card6 :
    (fastBlocker sevenNineExtensionVector025Base6).card =
      9 := by
  decide

theorem sevenNineExtensionVector025_selection6_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector025
      sevenNineExtensionVector025Selected6 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector025_base6, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector025Base6 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector025Base6 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector025_final_card6]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
