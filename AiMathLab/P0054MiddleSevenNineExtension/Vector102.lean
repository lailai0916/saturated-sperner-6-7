import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector100

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector102 : List Nat :=
  [0, 2, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 1, 0]

theorem sevenNineExtensionVector102_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 102 [] =
      sevenNineExtensionVector102 := by
  decide

def sevenNineExtensionVector102BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6}, {3, 5}, {2, 3, 4}, {1, 6}, {1, 2, 5}, {1, 2, 4}, {0, 6}, {0, 2, 5}, {0, 2, 4}]

def sevenNineExtensionVector102Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector102Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector102Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector102_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector102 =
      sevenNineExtensionVector102BlockerRows := by
  decide

theorem sevenNineExtensionVector102_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector102 =
      sevenNineExtensionVector102Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector102_blocker_rows]
  decide

def sevenNineExtensionVector102Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6, 7}, {3, 5, 7}, {2, 3, 4}, {1, 6, 7}, {1, 2, 5}, {1, 2, 4}, {0, 6, 7}, {0, 2, 5}, {0, 2, 4}]

theorem sevenNineExtensionVector102_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector102
        sevenNineExtensionVector102Selected0 =
      sevenNineExtensionVector102Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector102_blocker_rows]
  decide

theorem sevenNineExtensionVector102_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector102
      sevenNineExtensionVector102Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector102_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector102Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector102Base0 = false := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
