import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector069

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector071 : List Nat :=
  [0, 0, 1, 0, 2, 1, 0, 0, 0, 1, 0, 2, 0, 0]

theorem sevenNineExtensionVector071_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 71 [] =
      sevenNineExtensionVector071 := by
  decide

def sevenNineExtensionVector071BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{2, 4}, {2, 3, 6}, {2, 3, 5}, {1, 4}, {1, 3, 6}, {1, 3, 5}, {0, 6}, {0, 5}, {0, 3, 4}]

def sevenNineExtensionVector071Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector071Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector071Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector071_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector071 =
      sevenNineExtensionVector071BlockerRows := by
  decide

theorem sevenNineExtensionVector071_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector071 =
      sevenNineExtensionVector071Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector071_blocker_rows]
  decide

def sevenNineExtensionVector071Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{2, 4, 7}, {2, 3, 6}, {2, 3, 5}, {1, 4, 7}, {1, 3, 6}, {1, 3, 5}, {0, 6, 7}, {0, 5, 7}, {0, 3, 4}]

theorem sevenNineExtensionVector071_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector071
        sevenNineExtensionVector071Selected0 =
      sevenNineExtensionVector071Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector071_blocker_rows]
  decide

theorem sevenNineExtensionVector071_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector071
      sevenNineExtensionVector071Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector071_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector071Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector071Base0 = false := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
