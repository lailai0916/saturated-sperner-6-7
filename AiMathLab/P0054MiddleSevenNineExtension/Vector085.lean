import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector083

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector085 : List Nat :=
  [0, 0, 0, 0, 2, 2, 0, 0, 1, 1, 0, 1, 0, 0]

theorem sevenNineExtensionVector085_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 85 [] =
      sevenNineExtensionVector085 := by
  decide

def sevenNineExtensionVector085BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 5, 6}, {3, 4}, {2, 4}, {1, 5}, {1, 3, 6}, {1, 2, 6}, {0, 5}, {0, 3, 6}, {0, 2, 6}]

def sevenNineExtensionVector085Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector085Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector085Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector085_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector085 =
      sevenNineExtensionVector085BlockerRows := by
  decide

theorem sevenNineExtensionVector085_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector085 =
      sevenNineExtensionVector085Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector085_blocker_rows]
  decide

def sevenNineExtensionVector085Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 5, 6}, {3, 4, 7}, {2, 4, 7}, {1, 5, 7}, {1, 3, 6}, {1, 2, 6}, {0, 5, 7}, {0, 3, 6}, {0, 2, 6}]

theorem sevenNineExtensionVector085_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector085
        sevenNineExtensionVector085Selected0 =
      sevenNineExtensionVector085Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector085_blocker_rows]
  decide

theorem sevenNineExtensionVector085_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector085
      sevenNineExtensionVector085Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector085_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector085Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector085Base0 = false := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
