import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector007

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector009 : List Nat :=
  [1, 1, 0, 1, 1, 0, 1, 2, 0, 1, 0, 0, 0, 0]

theorem sevenNineExtensionVector009_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 9 [] =
      sevenNineExtensionVector009 := by
  decide

def sevenNineExtensionVector009BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 7}, {4, 6}, {4, 5}, {3, 7}, {1, 3, 6}, {1, 3, 5}, {0, 2, 7}, {0, 1, 2, 6}, {0, 1, 2, 5}]

def sevenNineExtensionVector009Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector009Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector009Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector009_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector009 =
      sevenNineExtensionVector009BlockerRows := by
  decide

theorem sevenNineExtensionVector009_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector009 =
      sevenNineExtensionVector009Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector009_blocker_rows]
  decide

def sevenNineExtensionVector009Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 7, 8}, {4, 6, 8}, {4, 5, 8}, {3, 7, 8}, {1, 3, 6}, {1, 3, 5}, {0, 2, 7}, {0, 1, 2, 6}, {0, 1, 2, 5}]

theorem sevenNineExtensionVector009_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector009
        sevenNineExtensionVector009Selected0 =
      sevenNineExtensionVector009Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector009_blocker_rows]
  decide

theorem sevenNineExtensionVector009_final_card0 :
    (fastBlocker sevenNineExtensionVector009Base0).card =
      11 := by
  decide

theorem sevenNineExtensionVector009_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector009
      sevenNineExtensionVector009Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector009_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector009Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector009Base0 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector009_final_card0]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
