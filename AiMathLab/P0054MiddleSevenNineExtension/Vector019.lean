import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector017

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector019 : List Nat :=
  [0, 0, 1, 0, 2, 1, 0, 0, 2, 1, 0, 0, 0, 0]

theorem sevenNineExtensionVector019_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 19 [] =
      sevenNineExtensionVector019 := by
  decide

def sevenNineExtensionVector019BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5}, {3, 4}, {2, 6}, {1, 6}, {0, 3, 6}, {0, 2, 5}, {0, 2, 4}, {0, 1, 5}, {0, 1, 4}]

def sevenNineExtensionVector019Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector019Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector019Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector019_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector019 =
      sevenNineExtensionVector019BlockerRows := by
  decide

theorem sevenNineExtensionVector019_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector019 =
      sevenNineExtensionVector019Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector019_blocker_rows]
  decide

def sevenNineExtensionVector019Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {3, 4, 7}, {2, 6, 7}, {1, 6, 7}, {0, 3, 6}, {0, 2, 5}, {0, 2, 4}, {0, 1, 5}, {0, 1, 4}]

theorem sevenNineExtensionVector019_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector019
        sevenNineExtensionVector019Selected0 =
      sevenNineExtensionVector019Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector019_blocker_rows]
  decide

theorem sevenNineExtensionVector019_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector019
      sevenNineExtensionVector019Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector019_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector019Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector019Base0 = false := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
