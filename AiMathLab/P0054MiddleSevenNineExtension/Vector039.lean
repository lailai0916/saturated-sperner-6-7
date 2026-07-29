import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector037

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector039 : List Nat :=
  [0, 1, 2, 0, 1, 0, 0, 1, 0, 0, 0, 2, 0, 0]

theorem sevenNineExtensionVector039_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 39 [] =
      sevenNineExtensionVector039 := by
  decide

def sevenNineExtensionVector039BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{2, 6}, {2, 5}, {2, 3, 4}, {1, 6}, {1, 5}, {1, 3, 4}, {0, 3, 6}, {0, 3, 5}, {0, 3, 4}]

def sevenNineExtensionVector039Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector039Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector039Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector039_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector039 =
      sevenNineExtensionVector039BlockerRows := by
  decide

theorem sevenNineExtensionVector039_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector039 =
      sevenNineExtensionVector039Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector039_blocker_rows]
  decide

def sevenNineExtensionVector039Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{2, 6, 7}, {2, 5, 7}, {2, 3, 4}, {1, 6, 7}, {1, 5, 7}, {1, 3, 4}, {0, 3, 6}, {0, 3, 5}, {0, 3, 4}]

theorem sevenNineExtensionVector039_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector039
        sevenNineExtensionVector039Selected0 =
      sevenNineExtensionVector039Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector039_blocker_rows]
  decide

theorem sevenNineExtensionVector039_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector039
      sevenNineExtensionVector039Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector039_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector039Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector039Base0 = false := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
