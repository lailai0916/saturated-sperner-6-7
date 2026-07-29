import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector019

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector021 : List Nat :=
  [1, 0, 0, 1, 1, 1, 0, 0, 1, 2, 0, 0, 0, 0]

theorem sevenNineExtensionVector021_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 21 [] =
      sevenNineExtensionVector021 := by
  decide

def sevenNineExtensionVector021BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4}, {2, 6}, {2, 5}, {1, 4, 6}, {1, 4, 5}, {0, 3, 6}, {0, 3, 5}, {0, 1, 6}, {0, 1, 5}]

def sevenNineExtensionVector021Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector021Selected1 :
    List (G413.Row MiddleFourModelPoint) :=
  [{0, 1, 5}]

def sevenNineExtensionVector021Selected2 :
    List (G413.Row MiddleFourModelPoint) :=
  [{0, 1, 6}]

def sevenNineExtensionVector021Selected3 :
    List (G413.Row MiddleFourModelPoint) :=
  [{0, 3, 5}]

def sevenNineExtensionVector021Selected4 :
    List (G413.Row MiddleFourModelPoint) :=
  [{0, 3, 6}]

def sevenNineExtensionVector021Selected5 :
    List (G413.Row MiddleFourModelPoint) :=
  [{1, 4, 5}]

def sevenNineExtensionVector021Selected6 :
    List (G413.Row MiddleFourModelPoint) :=
  [{1, 4, 6}]

def sevenNineExtensionVector021Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector021Selected0, sevenNineExtensionVector021Selected1, sevenNineExtensionVector021Selected2, sevenNineExtensionVector021Selected3, sevenNineExtensionVector021Selected4, sevenNineExtensionVector021Selected5, sevenNineExtensionVector021Selected6]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector021_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector021 =
      sevenNineExtensionVector021BlockerRows := by
  decide

theorem sevenNineExtensionVector021_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector021 =
      sevenNineExtensionVector021Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector021_blocker_rows]
  decide

def sevenNineExtensionVector021Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 7}, {2, 6, 7}, {2, 5, 7}, {1, 4, 6}, {1, 4, 5}, {0, 3, 6}, {0, 3, 5}, {0, 1, 6}, {0, 1, 5}]

theorem sevenNineExtensionVector021_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector021
        sevenNineExtensionVector021Selected0 =
      sevenNineExtensionVector021Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector021_blocker_rows]
  decide

theorem sevenNineExtensionVector021_final_card0 :
    (fastBlocker sevenNineExtensionVector021Base0).card =
      8 := by
  decide

theorem sevenNineExtensionVector021_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector021
      sevenNineExtensionVector021Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector021_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector021Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector021Base0 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector021_final_card0]
  decide
def sevenNineExtensionVector021Base1 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 7}, {2, 6, 7}, {2, 5, 7}, {1, 4, 6}, {1, 4, 5}, {0, 3, 6}, {0, 3, 5}, {0, 1, 6}, {0, 1, 5, 7}]

theorem sevenNineExtensionVector021_base1 :
    middleFourModelLiftBaseRows sevenNineExtensionVector021
        sevenNineExtensionVector021Selected1 =
      sevenNineExtensionVector021Base1 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector021_blocker_rows]
  decide

theorem sevenNineExtensionVector021_final_card1 :
    (fastBlocker sevenNineExtensionVector021Base1).card =
      9 := by
  decide

theorem sevenNineExtensionVector021_selection1_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector021
      sevenNineExtensionVector021Selected1 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector021_base1, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector021Base1 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector021Base1 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector021_final_card1]
  decide
def sevenNineExtensionVector021Base2 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 7}, {2, 6, 7}, {2, 5, 7}, {1, 4, 6}, {1, 4, 5}, {0, 3, 6}, {0, 3, 5}, {0, 1, 6, 7}, {0, 1, 5}]

theorem sevenNineExtensionVector021_base2 :
    middleFourModelLiftBaseRows sevenNineExtensionVector021
        sevenNineExtensionVector021Selected2 =
      sevenNineExtensionVector021Base2 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector021_blocker_rows]
  decide

theorem sevenNineExtensionVector021_final_card2 :
    (fastBlocker sevenNineExtensionVector021Base2).card =
      9 := by
  decide

theorem sevenNineExtensionVector021_selection2_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector021
      sevenNineExtensionVector021Selected2 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector021_base2, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector021Base2 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector021Base2 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector021_final_card2]
  decide
def sevenNineExtensionVector021Base3 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 7}, {2, 6, 7}, {2, 5, 7}, {1, 4, 6}, {1, 4, 5}, {0, 3, 6}, {0, 3, 5, 7}, {0, 1, 6}, {0, 1, 5}]

theorem sevenNineExtensionVector021_base3 :
    middleFourModelLiftBaseRows sevenNineExtensionVector021
        sevenNineExtensionVector021Selected3 =
      sevenNineExtensionVector021Base3 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector021_blocker_rows]
  decide

theorem sevenNineExtensionVector021_final_card3 :
    (fastBlocker sevenNineExtensionVector021Base3).card =
      9 := by
  decide

theorem sevenNineExtensionVector021_selection3_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector021
      sevenNineExtensionVector021Selected3 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector021_base3, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector021Base3 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector021Base3 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector021_final_card3]
  decide
def sevenNineExtensionVector021Base4 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 7}, {2, 6, 7}, {2, 5, 7}, {1, 4, 6}, {1, 4, 5}, {0, 3, 6, 7}, {0, 3, 5}, {0, 1, 6}, {0, 1, 5}]

theorem sevenNineExtensionVector021_base4 :
    middleFourModelLiftBaseRows sevenNineExtensionVector021
        sevenNineExtensionVector021Selected4 =
      sevenNineExtensionVector021Base4 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector021_blocker_rows]
  decide

theorem sevenNineExtensionVector021_final_card4 :
    (fastBlocker sevenNineExtensionVector021Base4).card =
      9 := by
  decide

theorem sevenNineExtensionVector021_selection4_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector021
      sevenNineExtensionVector021Selected4 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector021_base4, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector021Base4 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector021Base4 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector021_final_card4]
  decide
def sevenNineExtensionVector021Base5 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 7}, {2, 6, 7}, {2, 5, 7}, {1, 4, 6}, {1, 4, 5, 7}, {0, 3, 6}, {0, 3, 5}, {0, 1, 6}, {0, 1, 5}]

theorem sevenNineExtensionVector021_base5 :
    middleFourModelLiftBaseRows sevenNineExtensionVector021
        sevenNineExtensionVector021Selected5 =
      sevenNineExtensionVector021Base5 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector021_blocker_rows]
  decide

theorem sevenNineExtensionVector021_final_card5 :
    (fastBlocker sevenNineExtensionVector021Base5).card =
      9 := by
  decide

theorem sevenNineExtensionVector021_selection5_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector021
      sevenNineExtensionVector021Selected5 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector021_base5, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector021Base5 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector021Base5 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector021_final_card5]
  decide
def sevenNineExtensionVector021Base6 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 7}, {2, 6, 7}, {2, 5, 7}, {1, 4, 6, 7}, {1, 4, 5}, {0, 3, 6}, {0, 3, 5}, {0, 1, 6}, {0, 1, 5}]

theorem sevenNineExtensionVector021_base6 :
    middleFourModelLiftBaseRows sevenNineExtensionVector021
        sevenNineExtensionVector021Selected6 =
      sevenNineExtensionVector021Base6 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector021_blocker_rows]
  decide

theorem sevenNineExtensionVector021_final_card6 :
    (fastBlocker sevenNineExtensionVector021Base6).card =
      9 := by
  decide

theorem sevenNineExtensionVector021_selection6_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector021
      sevenNineExtensionVector021Selected6 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector021_base6, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector021Base6 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector021Base6 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector021_final_card6]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
