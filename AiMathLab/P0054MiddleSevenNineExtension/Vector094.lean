import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector092

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector094 : List Nat :=
  [0, 1, 1, 2, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0]

theorem sevenNineExtensionVector094_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 94 [] =
      sevenNineExtensionVector094 := by
  decide

def sevenNineExtensionVector094BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{5, 6}, {3, 5}, {2, 5}, {1, 6}, {1, 3, 4}, {1, 2, 4}, {0, 4, 6}, {0, 3, 4}, {0, 2, 4}]

def sevenNineExtensionVector094Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector094Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector094Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector094_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector094 =
      sevenNineExtensionVector094BlockerRows := by
  decide

theorem sevenNineExtensionVector094_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector094 =
      sevenNineExtensionVector094Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector094_blocker_rows]
  decide

def sevenNineExtensionVector094Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{5, 6, 7}, {3, 5, 7}, {2, 5, 7}, {1, 6, 7}, {1, 3, 4}, {1, 2, 4}, {0, 4, 6}, {0, 3, 4}, {0, 2, 4}]

theorem sevenNineExtensionVector094_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector094
        sevenNineExtensionVector094Selected0 =
      sevenNineExtensionVector094Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector094_blocker_rows]
  decide

theorem sevenNineExtensionVector094_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector094
      sevenNineExtensionVector094Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector094_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector094Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector094Base0 = false := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
