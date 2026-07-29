import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector041

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector043 : List Nat :=
  [1, 0, 1, 0, 0, 1, 1, 2, 0, 0, 0, 1, 0, 0]

theorem sevenNineExtensionVector043_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 43 [] =
      sevenNineExtensionVector043 := by
  decide

def sevenNineExtensionVector043BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6}, {3, 5}, {3, 4}, {1, 6}, {1, 2, 5}, {1, 2, 4}, {0, 2, 6}, {0, 2, 5}, {0, 2, 4}]

def sevenNineExtensionVector043Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector043Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector043Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector043_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector043 =
      sevenNineExtensionVector043BlockerRows := by
  decide

theorem sevenNineExtensionVector043_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector043 =
      sevenNineExtensionVector043Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector043_blocker_rows]
  decide

def sevenNineExtensionVector043Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6, 7}, {3, 5, 7}, {3, 4, 7}, {1, 6, 7}, {1, 2, 5}, {1, 2, 4}, {0, 2, 6}, {0, 2, 5}, {0, 2, 4}]

theorem sevenNineExtensionVector043_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector043
        sevenNineExtensionVector043Selected0 =
      sevenNineExtensionVector043Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector043_blocker_rows]
  decide

theorem sevenNineExtensionVector043_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector043
      sevenNineExtensionVector043Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector043_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector043Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector043Base0 = false := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
