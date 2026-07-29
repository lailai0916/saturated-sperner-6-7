import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector098

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector100 : List Nat :=
  [1, 2, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0]

theorem sevenNineExtensionVector100_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 100 [] =
      sevenNineExtensionVector100 := by
  decide

def sevenNineExtensionVector100BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 7}, {4, 6}, {2, 7}, {2, 3, 6}, {1, 7}, {1, 3, 6}, {0, 4, 5}, {0, 2, 3, 5}, {0, 1, 3, 5}]

def sevenNineExtensionVector100Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector100Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector100Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector100_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector100 =
      sevenNineExtensionVector100BlockerRows := by
  decide

theorem sevenNineExtensionVector100_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector100 =
      sevenNineExtensionVector100Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector100_blocker_rows]
  decide

def sevenNineExtensionVector100Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 7, 8}, {4, 6, 8}, {2, 7, 8}, {2, 3, 6}, {1, 7, 8}, {1, 3, 6}, {0, 4, 5}, {0, 2, 3, 5}, {0, 1, 3, 5}]

theorem sevenNineExtensionVector100_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector100
        sevenNineExtensionVector100Selected0 =
      sevenNineExtensionVector100Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector100_blocker_rows]
  decide

theorem sevenNineExtensionVector100_final_card0 :
    (fastBlocker sevenNineExtensionVector100Base0).card =
      11 := by
  decide

theorem sevenNineExtensionVector100_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector100
      sevenNineExtensionVector100Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector100_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector100Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector100Base0 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector100_final_card0]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
