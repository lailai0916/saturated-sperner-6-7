import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector080

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector082 : List Nat :=
  [0, 0, 1, 0, 0, 1, 0, 0, 2, 1, 0, 2, 0, 0]

theorem sevenNineExtensionVector082_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 82 [] =
      sevenNineExtensionVector082 := by
  decide

def sevenNineExtensionVector082BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 6}, {3, 4, 5}, {2, 4, 6}, {2, 4, 5}, {1, 3}, {1, 2}, {0, 6}, {0, 5}, {0, 1, 4}]

def sevenNineExtensionVector082Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector082Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector082Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector082_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector082 =
      sevenNineExtensionVector082BlockerRows := by
  decide

theorem sevenNineExtensionVector082_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector082 =
      sevenNineExtensionVector082Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector082_blocker_rows]
  decide

def sevenNineExtensionVector082Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 6}, {3, 4, 5}, {2, 4, 6}, {2, 4, 5}, {1, 3, 7}, {1, 2, 7}, {0, 6, 7}, {0, 5, 7}, {0, 1, 4}]

theorem sevenNineExtensionVector082_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector082
        sevenNineExtensionVector082Selected0 =
      sevenNineExtensionVector082Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector082_blocker_rows]
  decide

theorem sevenNineExtensionVector082_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector082
      sevenNineExtensionVector082Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector082_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector082Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector082Base0 = false := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
