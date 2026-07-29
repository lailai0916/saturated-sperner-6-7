import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector112

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector114 : List Nat :=
  [1, 2, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 0]

theorem sevenNineExtensionVector114_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 114 [] =
      sevenNineExtensionVector114 := by
  decide

def sevenNineExtensionVector114BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6}, {3, 4}, {2, 6}, {2, 4, 5}, {1, 6}, {1, 4, 5}, {0, 3, 5}, {0, 2, 5}, {0, 1, 5}]

def sevenNineExtensionVector114Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector114Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector114Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector114_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector114 =
      sevenNineExtensionVector114BlockerRows := by
  decide

theorem sevenNineExtensionVector114_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector114 =
      sevenNineExtensionVector114Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector114_blocker_rows]
  decide

def sevenNineExtensionVector114Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6, 7}, {3, 4, 7}, {2, 6, 7}, {2, 4, 5}, {1, 6, 7}, {1, 4, 5}, {0, 3, 5}, {0, 2, 5}, {0, 1, 5}]

theorem sevenNineExtensionVector114_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector114
        sevenNineExtensionVector114Selected0 =
      sevenNineExtensionVector114Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector114_blocker_rows]
  decide

theorem sevenNineExtensionVector114_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector114
      sevenNineExtensionVector114Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector114_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector114Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector114Base0 = false := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
