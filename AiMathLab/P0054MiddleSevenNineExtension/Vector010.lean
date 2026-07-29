import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector008

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector010 : List Nat :=
  [0, 0, 1, 1, 1, 0, 1, 2, 0, 1, 0, 0, 0, 0]

theorem sevenNineExtensionVector010_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 10 [] =
      sevenNineExtensionVector010 := by
  decide

def sevenNineExtensionVector010BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6}, {3, 5}, {3, 4}, {2, 6}, {0, 2, 5}, {0, 2, 4}, {0, 1, 6}, {0, 1, 5}, {0, 1, 4}]

def sevenNineExtensionVector010Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector010Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector010Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector010_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector010 =
      sevenNineExtensionVector010BlockerRows := by
  decide

theorem sevenNineExtensionVector010_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector010 =
      sevenNineExtensionVector010Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector010_blocker_rows]
  decide

def sevenNineExtensionVector010Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6, 7}, {3, 5, 7}, {3, 4, 7}, {2, 6, 7}, {0, 2, 5}, {0, 2, 4}, {0, 1, 6}, {0, 1, 5}, {0, 1, 4}]

theorem sevenNineExtensionVector010_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector010
        sevenNineExtensionVector010Selected0 =
      sevenNineExtensionVector010Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector010_blocker_rows]
  decide

theorem sevenNineExtensionVector010_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector010
      sevenNineExtensionVector010Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector010_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector010Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector010Base0 = false := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
