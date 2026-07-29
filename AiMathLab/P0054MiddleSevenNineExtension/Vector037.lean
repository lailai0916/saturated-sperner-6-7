import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector035

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector037 : List Nat :=
  [1, 0, 0, 2, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0]

theorem sevenNineExtensionVector037_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 37 [] =
      sevenNineExtensionVector037 := by
  decide

def sevenNineExtensionVector037BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6}, {3, 4}, {2, 6}, {2, 4, 5}, {1, 6}, {1, 4, 5}, {0, 3, 5}, {0, 2, 5}, {0, 1, 5}]

def sevenNineExtensionVector037Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector037Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector037Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector037_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector037 =
      sevenNineExtensionVector037BlockerRows := by
  decide

theorem sevenNineExtensionVector037_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector037 =
      sevenNineExtensionVector037Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector037_blocker_rows]
  decide

def sevenNineExtensionVector037Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6, 7}, {3, 4, 7}, {2, 6, 7}, {2, 4, 5}, {1, 6, 7}, {1, 4, 5}, {0, 3, 5}, {0, 2, 5}, {0, 1, 5}]

theorem sevenNineExtensionVector037_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector037
        sevenNineExtensionVector037Selected0 =
      sevenNineExtensionVector037Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector037_blocker_rows]
  decide

theorem sevenNineExtensionVector037_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector037
      sevenNineExtensionVector037Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector037_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector037Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector037Base0 = false := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
