import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector006

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector008 : List Nat :=
  [1, 0, 0, 0, 2, 1, 0, 1, 0, 2, 0, 0, 0, 0]

theorem sevenNineExtensionVector008_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 8 [] =
      sevenNineExtensionVector008 := by
  decide

def sevenNineExtensionVector008BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{2, 6}, {2, 5}, {2, 3, 4}, {1, 6}, {1, 5}, {1, 3, 4}, {0, 3, 6}, {0, 3, 5}, {0, 3, 4}]

def sevenNineExtensionVector008Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector008Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector008Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector008_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector008 =
      sevenNineExtensionVector008BlockerRows := by
  decide

theorem sevenNineExtensionVector008_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector008 =
      sevenNineExtensionVector008Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector008_blocker_rows]
  decide

def sevenNineExtensionVector008Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{2, 6, 7}, {2, 5, 7}, {2, 3, 4}, {1, 6, 7}, {1, 5, 7}, {1, 3, 4}, {0, 3, 6}, {0, 3, 5}, {0, 3, 4}]

theorem sevenNineExtensionVector008_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector008
        sevenNineExtensionVector008Selected0 =
      sevenNineExtensionVector008Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector008_blocker_rows]
  decide

theorem sevenNineExtensionVector008_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector008
      sevenNineExtensionVector008Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector008_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector008Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector008Base0 = false := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
