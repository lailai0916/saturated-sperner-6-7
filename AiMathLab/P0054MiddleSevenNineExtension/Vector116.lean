import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector114

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector116 : List Nat :=
  [1, 2, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0]

theorem sevenNineExtensionVector116_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 116 [] =
      sevenNineExtensionVector116 := by
  decide

def sevenNineExtensionVector116BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 6}, {3, 4}, {2, 6}, {2, 3, 5}, {1, 6}, {1, 3, 5}, {0, 4, 5}, {0, 2, 5}, {0, 1, 5}]

def sevenNineExtensionVector116Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector116Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector116Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector116_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector116 =
      sevenNineExtensionVector116BlockerRows := by
  decide

theorem sevenNineExtensionVector116_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector116 =
      sevenNineExtensionVector116Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector116_blocker_rows]
  decide

def sevenNineExtensionVector116Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 6, 7}, {3, 4, 7}, {2, 6, 7}, {2, 3, 5}, {1, 6, 7}, {1, 3, 5}, {0, 4, 5}, {0, 2, 5}, {0, 1, 5}]

theorem sevenNineExtensionVector116_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector116
        sevenNineExtensionVector116Selected0 =
      sevenNineExtensionVector116Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector116_blocker_rows]
  decide

theorem sevenNineExtensionVector116_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector116
      sevenNineExtensionVector116Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector116_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector116Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector116Base0 = false := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
