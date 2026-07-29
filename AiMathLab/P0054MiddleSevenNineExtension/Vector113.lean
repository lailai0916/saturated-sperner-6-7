import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector111

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector113 : List Nat :=
  [0, 2, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0]

theorem sevenNineExtensionVector113_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 113 [] =
      sevenNineExtensionVector113 := by
  decide

def sevenNineExtensionVector113BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{2, 6}, {2, 5}, {2, 3, 4}, {1, 6}, {1, 4, 5}, {1, 3, 4}, {0, 6}, {0, 4, 5}, {0, 3, 4}]

def sevenNineExtensionVector113Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector113Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector113Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector113_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector113 =
      sevenNineExtensionVector113BlockerRows := by
  decide

theorem sevenNineExtensionVector113_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector113 =
      sevenNineExtensionVector113Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector113_blocker_rows]
  decide

def sevenNineExtensionVector113Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{2, 6, 7}, {2, 5, 7}, {2, 3, 4}, {1, 6, 7}, {1, 4, 5}, {1, 3, 4}, {0, 6, 7}, {0, 4, 5}, {0, 3, 4}]

theorem sevenNineExtensionVector113_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector113
        sevenNineExtensionVector113Selected0 =
      sevenNineExtensionVector113Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector113_blocker_rows]
  decide

theorem sevenNineExtensionVector113_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector113
      sevenNineExtensionVector113Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector113_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector113Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector113Base0 = false := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
