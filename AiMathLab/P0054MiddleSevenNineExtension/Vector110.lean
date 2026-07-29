import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector108

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector110 : List Nat :=
  [1, 2, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0]

theorem sevenNineExtensionVector110_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 110 [] =
      sevenNineExtensionVector110 := by
  decide

def sevenNineExtensionVector110BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 7}, {3, 6}, {3, 4, 5}, {2, 7}, {1, 7}, {0, 2, 6}, {0, 2, 4, 5}, {0, 1, 6}, {0, 1, 4, 5}]

def sevenNineExtensionVector110Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector110Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector110Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector110_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector110 =
      sevenNineExtensionVector110BlockerRows := by
  decide

theorem sevenNineExtensionVector110_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector110 =
      sevenNineExtensionVector110Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector110_blocker_rows]
  decide

def sevenNineExtensionVector110Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 7, 8}, {3, 6, 8}, {3, 4, 5}, {2, 7, 8}, {1, 7, 8}, {0, 2, 6}, {0, 2, 4, 5}, {0, 1, 6}, {0, 1, 4, 5}]

theorem sevenNineExtensionVector110_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector110
        sevenNineExtensionVector110Selected0 =
      sevenNineExtensionVector110Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector110_blocker_rows]
  decide

theorem sevenNineExtensionVector110_final_card0 :
    (fastBlocker sevenNineExtensionVector110Base0).card =
      11 := by
  decide

theorem sevenNineExtensionVector110_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector110
      sevenNineExtensionVector110Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector110_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector110Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector110Base0 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector110_final_card0]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
