import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector038

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector040 : List Nat :=
  [1, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 2, 0, 0]

theorem sevenNineExtensionVector040_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 40 [] =
      sevenNineExtensionVector040 := by
  decide

def sevenNineExtensionVector040BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{2, 6}, {2, 5}, {2, 3, 4}, {1, 6}, {1, 5}, {1, 3, 4}, {0, 3, 6}, {0, 3, 5}, {0, 3, 4}]

def sevenNineExtensionVector040Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector040Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector040Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector040_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector040 =
      sevenNineExtensionVector040BlockerRows := by
  decide

theorem sevenNineExtensionVector040_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector040 =
      sevenNineExtensionVector040Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector040_blocker_rows]
  decide

def sevenNineExtensionVector040Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{2, 6, 7}, {2, 5, 7}, {2, 3, 4}, {1, 6, 7}, {1, 5, 7}, {1, 3, 4}, {0, 3, 6}, {0, 3, 5}, {0, 3, 4}]

theorem sevenNineExtensionVector040_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector040
        sevenNineExtensionVector040Selected0 =
      sevenNineExtensionVector040Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector040_blocker_rows]
  decide

theorem sevenNineExtensionVector040_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector040
      sevenNineExtensionVector040Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector040_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector040Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector040Base0 = false := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
