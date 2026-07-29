import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector132

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector134 : List Nat :=
  [2, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1]

theorem sevenNineExtensionVector134_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 134 [] =
      sevenNineExtensionVector134 := by
  decide

def sevenNineExtensionVector134BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{2, 6}, {2, 5}, {2, 3, 4}, {1, 6}, {1, 4, 5}, {1, 3, 4}, {0, 6}, {0, 4, 5}, {0, 3, 4}]

def sevenNineExtensionVector134Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector134Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector134Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector134_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector134 =
      sevenNineExtensionVector134BlockerRows := by
  decide

theorem sevenNineExtensionVector134_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector134 =
      sevenNineExtensionVector134Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector134_blocker_rows]
  decide

def sevenNineExtensionVector134Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{2, 6, 7}, {2, 5, 7}, {2, 3, 4}, {1, 6, 7}, {1, 4, 5}, {1, 3, 4}, {0, 6, 7}, {0, 4, 5}, {0, 3, 4}]

theorem sevenNineExtensionVector134_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector134
        sevenNineExtensionVector134Selected0 =
      sevenNineExtensionVector134Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector134_blocker_rows]
  decide

theorem sevenNineExtensionVector134_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector134
      sevenNineExtensionVector134Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector134_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector134Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector134Base0 = false := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
