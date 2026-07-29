import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector055

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector057 : List Nat :=
  [0, 1, 1, 0, 0, 1, 0, 1, 2, 0, 0, 2, 0, 0]

theorem sevenNineExtensionVector057_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 57 [] =
      sevenNineExtensionVector057 := by
  decide

def sevenNineExtensionVector057BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{2, 5}, {2, 4}, {1, 7}, {1, 6}, {1, 2, 3}, {0, 5, 7}, {0, 5, 6}, {0, 4, 7}, {0, 4, 6}]

def sevenNineExtensionVector057Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector057Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector057Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector057_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector057 =
      sevenNineExtensionVector057BlockerRows := by
  decide

theorem sevenNineExtensionVector057_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector057 =
      sevenNineExtensionVector057Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector057_blocker_rows]
  decide

def sevenNineExtensionVector057Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{2, 5, 8}, {2, 4, 8}, {1, 7, 8}, {1, 6, 8}, {1, 2, 3}, {0, 5, 7}, {0, 5, 6}, {0, 4, 7}, {0, 4, 6}]

theorem sevenNineExtensionVector057_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector057
        sevenNineExtensionVector057Selected0 =
      sevenNineExtensionVector057Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector057_blocker_rows]
  decide

theorem sevenNineExtensionVector057_final_card0 :
    (fastBlocker sevenNineExtensionVector057Base0).card =
      11 := by
  decide

theorem sevenNineExtensionVector057_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector057
      sevenNineExtensionVector057Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector057_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector057Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector057Base0 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector057_final_card0]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
