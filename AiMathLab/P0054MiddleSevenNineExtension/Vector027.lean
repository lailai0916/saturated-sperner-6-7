import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector025

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector027 : List Nat :=
  [0, 0, 0, 1, 2, 2, 0, 1, 1, 1, 0, 0, 0, 0]

theorem sevenNineExtensionVector027_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 27 [] =
      sevenNineExtensionVector027 := by
  decide

def sevenNineExtensionVector027BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 6}, {3, 6}, {2, 7}, {2, 4, 5}, {2, 3, 5}, {1, 7}, {1, 4, 5}, {1, 3, 5}, {0, 6, 7}]

def sevenNineExtensionVector027Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector027Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector027Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector027_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector027 =
      sevenNineExtensionVector027BlockerRows := by
  decide

theorem sevenNineExtensionVector027_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector027 =
      sevenNineExtensionVector027Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector027_blocker_rows]
  decide

def sevenNineExtensionVector027Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 6, 8}, {3, 6, 8}, {2, 7, 8}, {2, 4, 5}, {2, 3, 5}, {1, 7, 8}, {1, 4, 5}, {1, 3, 5}, {0, 6, 7}]

theorem sevenNineExtensionVector027_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector027
        sevenNineExtensionVector027Selected0 =
      sevenNineExtensionVector027Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector027_blocker_rows]
  decide

theorem sevenNineExtensionVector027_final_card0 :
    (fastBlocker sevenNineExtensionVector027Base0).card =
      11 := by
  decide

theorem sevenNineExtensionVector027_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector027
      sevenNineExtensionVector027Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector027_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector027Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector027Base0 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector027_final_card0]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
