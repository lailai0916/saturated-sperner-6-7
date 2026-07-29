import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector032

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector034 : List Nat :=
  [0, 0, 1, 2, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0]

theorem sevenNineExtensionVector034_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 34 [] =
      sevenNineExtensionVector034 := by
  decide

def sevenNineExtensionVector034BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6}, {3, 5}, {2, 6}, {1, 6}, {0, 3, 4}, {0, 2, 5}, {0, 2, 4}, {0, 1, 5}, {0, 1, 4}]

def sevenNineExtensionVector034Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector034Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector034Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector034_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector034 =
      sevenNineExtensionVector034BlockerRows := by
  decide

theorem sevenNineExtensionVector034_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector034 =
      sevenNineExtensionVector034Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector034_blocker_rows]
  decide

def sevenNineExtensionVector034Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6, 7}, {3, 5, 7}, {2, 6, 7}, {1, 6, 7}, {0, 3, 4}, {0, 2, 5}, {0, 2, 4}, {0, 1, 5}, {0, 1, 4}]

theorem sevenNineExtensionVector034_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector034
        sevenNineExtensionVector034Selected0 =
      sevenNineExtensionVector034Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector034_blocker_rows]
  decide

theorem sevenNineExtensionVector034_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector034
      sevenNineExtensionVector034Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector034_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector034Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector034Base0 = false := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
