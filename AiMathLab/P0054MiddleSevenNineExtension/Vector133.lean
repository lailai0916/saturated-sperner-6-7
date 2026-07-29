import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector131

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector133 : List Nat :=
  [2, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1]

theorem sevenNineExtensionVector133_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 133 [] =
      sevenNineExtensionVector133 := by
  decide

def sevenNineExtensionVector133BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 6}, {3, 4}, {2, 4, 5}, {1, 6}, {1, 3, 5}, {1, 2, 5}, {0, 6}, {0, 3, 5}, {0, 2, 5}]

def sevenNineExtensionVector133Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector133Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector133Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector133_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector133 =
      sevenNineExtensionVector133BlockerRows := by
  decide

theorem sevenNineExtensionVector133_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector133 =
      sevenNineExtensionVector133Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector133_blocker_rows]
  decide

def sevenNineExtensionVector133Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 6, 7}, {3, 4, 7}, {2, 4, 5}, {1, 6, 7}, {1, 3, 5}, {1, 2, 5}, {0, 6, 7}, {0, 3, 5}, {0, 2, 5}]

theorem sevenNineExtensionVector133_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector133
        sevenNineExtensionVector133Selected0 =
      sevenNineExtensionVector133Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector133_blocker_rows]
  decide

theorem sevenNineExtensionVector133_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector133
      sevenNineExtensionVector133Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector133_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector133Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector133Base0 = false := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
