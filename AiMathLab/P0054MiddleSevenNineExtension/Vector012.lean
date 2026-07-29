import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector010

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector012 : List Nat :=
  [0, 1, 0, 1, 2, 0, 0, 0, 1, 2, 0, 0, 0, 0]

theorem sevenNineExtensionVector012_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 12 [] =
      sevenNineExtensionVector012 := by
  decide

def sevenNineExtensionVector012BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6}, {3, 5}, {2, 6}, {2, 5}, {1, 4, 6}, {1, 4, 5}, {0, 3, 4}, {0, 2, 4}, {0, 1, 4}]

def sevenNineExtensionVector012Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector012Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector012Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector012_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector012 =
      sevenNineExtensionVector012BlockerRows := by
  decide

theorem sevenNineExtensionVector012_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector012 =
      sevenNineExtensionVector012Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector012_blocker_rows]
  decide

def sevenNineExtensionVector012Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6, 7}, {3, 5, 7}, {2, 6, 7}, {2, 5, 7}, {1, 4, 6}, {1, 4, 5}, {0, 3, 4}, {0, 2, 4}, {0, 1, 4}]

theorem sevenNineExtensionVector012_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector012
        sevenNineExtensionVector012Selected0 =
      sevenNineExtensionVector012Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector012_blocker_rows]
  decide

theorem sevenNineExtensionVector012_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector012
      sevenNineExtensionVector012Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector012_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector012Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector012Base0 = false := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
