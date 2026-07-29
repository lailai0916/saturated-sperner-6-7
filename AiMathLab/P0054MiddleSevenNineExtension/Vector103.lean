import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector101

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector103 : List Nat :=
  [1, 2, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0]

theorem sevenNineExtensionVector103_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 103 [] =
      sevenNineExtensionVector103 := by
  decide

def sevenNineExtensionVector103BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{6, 7}, {4, 6}, {2, 7}, {2, 4, 5}, {1, 7}, {1, 4, 5}, {0, 3, 6}, {0, 2, 3, 5}, {0, 1, 3, 5}]

def sevenNineExtensionVector103Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector103Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector103Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector103_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector103 =
      sevenNineExtensionVector103BlockerRows := by
  decide

theorem sevenNineExtensionVector103_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector103 =
      sevenNineExtensionVector103Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector103_blocker_rows]
  decide

def sevenNineExtensionVector103Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{6, 7, 8}, {4, 6, 8}, {2, 7, 8}, {2, 4, 5}, {1, 7, 8}, {1, 4, 5}, {0, 3, 6}, {0, 2, 3, 5}, {0, 1, 3, 5}]

theorem sevenNineExtensionVector103_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector103
        sevenNineExtensionVector103Selected0 =
      sevenNineExtensionVector103Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector103_blocker_rows]
  decide

theorem sevenNineExtensionVector103_final_card0 :
    (fastBlocker sevenNineExtensionVector103Base0).card =
      11 := by
  decide

theorem sevenNineExtensionVector103_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector103
      sevenNineExtensionVector103Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector103_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector103Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector103Base0 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector103_final_card0]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
