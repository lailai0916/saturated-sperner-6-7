import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector011

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector013 : List Nat :=
  [1, 0, 0, 1, 0, 2, 0, 0, 2, 1, 0, 0, 0, 0]

theorem sevenNineExtensionVector013_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 13 [] =
      sevenNineExtensionVector013 := by
  decide

def sevenNineExtensionVector013BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5}, {3, 4}, {2, 5}, {2, 4}, {1, 5, 6}, {1, 4, 6}, {0, 3, 6}, {0, 2, 6}, {0, 1, 6}]

def sevenNineExtensionVector013Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector013Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector013Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector013_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector013 =
      sevenNineExtensionVector013BlockerRows := by
  decide

theorem sevenNineExtensionVector013_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector013 =
      sevenNineExtensionVector013Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector013_blocker_rows]
  decide

def sevenNineExtensionVector013Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {3, 4, 7}, {2, 5, 7}, {2, 4, 7}, {1, 5, 6}, {1, 4, 6}, {0, 3, 6}, {0, 2, 6}, {0, 1, 6}]

theorem sevenNineExtensionVector013_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector013
        sevenNineExtensionVector013Selected0 =
      sevenNineExtensionVector013Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector013_blocker_rows]
  decide

theorem sevenNineExtensionVector013_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector013
      sevenNineExtensionVector013Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector013_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector013Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector013Base0 = false := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
