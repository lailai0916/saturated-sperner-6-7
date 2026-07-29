import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector061

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector063 : List Nat :=
  [1, 1, 0, 0, 2, 0, 0, 0, 0, 2, 0, 1, 0, 0]

theorem sevenNineExtensionVector063_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 63 [] =
      sevenNineExtensionVector063 := by
  decide

def sevenNineExtensionVector063BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5}, {3, 4}, {2, 5}, {2, 4}, {1, 3, 6}, {1, 2, 6}, {0, 5, 6}, {0, 4, 6}, {0, 1, 6}]

def sevenNineExtensionVector063Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector063Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector063Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector063_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector063 =
      sevenNineExtensionVector063BlockerRows := by
  decide

theorem sevenNineExtensionVector063_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector063 =
      sevenNineExtensionVector063Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector063_blocker_rows]
  decide

def sevenNineExtensionVector063Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {3, 4, 7}, {2, 5, 7}, {2, 4, 7}, {1, 3, 6}, {1, 2, 6}, {0, 5, 6}, {0, 4, 6}, {0, 1, 6}]

theorem sevenNineExtensionVector063_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector063
        sevenNineExtensionVector063Selected0 =
      sevenNineExtensionVector063Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector063_blocker_rows]
  decide

theorem sevenNineExtensionVector063_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector063
      sevenNineExtensionVector063Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector063_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector063Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector063Base0 = false := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
