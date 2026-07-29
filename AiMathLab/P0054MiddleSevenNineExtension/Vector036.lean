import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector034

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector036 : List Nat :=
  [0, 1, 0, 2, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0]

theorem sevenNineExtensionVector036_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 36 [] =
      sevenNineExtensionVector036 := by
  decide

def sevenNineExtensionVector036BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6}, {3, 5}, {2, 6}, {2, 4, 5}, {1, 6}, {1, 4, 5}, {0, 3, 4}, {0, 2, 4}, {0, 1, 4}]

def sevenNineExtensionVector036Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector036Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector036Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector036_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector036 =
      sevenNineExtensionVector036BlockerRows := by
  decide

theorem sevenNineExtensionVector036_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector036 =
      sevenNineExtensionVector036Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector036_blocker_rows]
  decide

def sevenNineExtensionVector036Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6, 7}, {3, 5, 7}, {2, 6, 7}, {2, 4, 5}, {1, 6, 7}, {1, 4, 5}, {0, 3, 4}, {0, 2, 4}, {0, 1, 4}]

theorem sevenNineExtensionVector036_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector036
        sevenNineExtensionVector036Selected0 =
      sevenNineExtensionVector036Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector036_blocker_rows]
  decide

theorem sevenNineExtensionVector036_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector036
      sevenNineExtensionVector036Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector036_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector036Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector036Base0 = false := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
