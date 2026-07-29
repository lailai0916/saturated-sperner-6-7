import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector003

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector005 : List Nat :=
  [0, 1, 0, 0, 1, 1, 1, 2, 1, 0, 0, 0, 0, 0]

theorem sevenNineExtensionVector005_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 5 [] =
      sevenNineExtensionVector005 := by
  decide

def sevenNineExtensionVector005BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6}, {3, 5}, {3, 4}, {2, 6}, {1, 2, 5}, {1, 2, 4}, {0, 1, 6}, {0, 1, 5}, {0, 1, 4}]

def sevenNineExtensionVector005Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector005Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector005Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector005_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector005 =
      sevenNineExtensionVector005BlockerRows := by
  decide

theorem sevenNineExtensionVector005_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector005 =
      sevenNineExtensionVector005Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector005_blocker_rows]
  decide

def sevenNineExtensionVector005Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6, 7}, {3, 5, 7}, {3, 4, 7}, {2, 6, 7}, {1, 2, 5}, {1, 2, 4}, {0, 1, 6}, {0, 1, 5}, {0, 1, 4}]

theorem sevenNineExtensionVector005_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector005
        sevenNineExtensionVector005Selected0 =
      sevenNineExtensionVector005Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector005_blocker_rows]
  decide

theorem sevenNineExtensionVector005_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector005
      sevenNineExtensionVector005Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector005_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector005Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector005Base0 = false := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
