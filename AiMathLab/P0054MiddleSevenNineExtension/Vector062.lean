import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector060

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector062 : List Nat :=
  [1, 0, 2, 1, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0]

theorem sevenNineExtensionVector062_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 62 [] =
      sevenNineExtensionVector062 := by
  decide

def sevenNineExtensionVector062BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{2, 6}, {2, 5}, {2, 3, 4}, {1, 6}, {1, 5}, {1, 3, 4}, {0, 4, 6}, {0, 4, 5}, {0, 3, 4}]

def sevenNineExtensionVector062Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector062Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector062Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector062_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector062 =
      sevenNineExtensionVector062BlockerRows := by
  decide

theorem sevenNineExtensionVector062_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector062 =
      sevenNineExtensionVector062Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector062_blocker_rows]
  decide

def sevenNineExtensionVector062Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{2, 6, 7}, {2, 5, 7}, {2, 3, 4}, {1, 6, 7}, {1, 5, 7}, {1, 3, 4}, {0, 4, 6}, {0, 4, 5}, {0, 3, 4}]

theorem sevenNineExtensionVector062_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector062
        sevenNineExtensionVector062Selected0 =
      sevenNineExtensionVector062Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector062_blocker_rows]
  decide

theorem sevenNineExtensionVector062_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector062
      sevenNineExtensionVector062Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector062_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector062Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector062Base0 = false := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
