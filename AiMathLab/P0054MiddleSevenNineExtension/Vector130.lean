import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector128

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector130 : List Nat :=
  [2, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1]

theorem sevenNineExtensionVector130_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 130 [] =
      sevenNineExtensionVector130 := by
  decide

def sevenNineExtensionVector130BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{2, 6}, {2, 5}, {2, 3, 4}, {1, 6}, {1, 3, 5}, {1, 3, 4}, {0, 6}, {0, 3, 5}, {0, 3, 4}]

def sevenNineExtensionVector130Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector130Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector130Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector130_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector130 =
      sevenNineExtensionVector130BlockerRows := by
  decide

theorem sevenNineExtensionVector130_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector130 =
      sevenNineExtensionVector130Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector130_blocker_rows]
  decide

def sevenNineExtensionVector130Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{2, 6, 7}, {2, 5, 7}, {2, 3, 4}, {1, 6, 7}, {1, 3, 5}, {1, 3, 4}, {0, 6, 7}, {0, 3, 5}, {0, 3, 4}]

theorem sevenNineExtensionVector130_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector130
        sevenNineExtensionVector130Selected0 =
      sevenNineExtensionVector130Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector130_blocker_rows]
  decide

theorem sevenNineExtensionVector130_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector130
      sevenNineExtensionVector130Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector130_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector130Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector130Base0 = false := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
