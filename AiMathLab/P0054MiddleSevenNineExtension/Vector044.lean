import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector042

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector044 : List Nat :=
  [0, 1, 2, 1, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0]

theorem sevenNineExtensionVector044_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 44 [] =
      sevenNineExtensionVector044 := by
  decide

def sevenNineExtensionVector044BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{2, 6}, {2, 5}, {2, 3, 4}, {1, 6}, {1, 5}, {1, 3, 4}, {0, 4, 6}, {0, 4, 5}, {0, 3, 4}]

def sevenNineExtensionVector044Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector044Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector044Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector044_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector044 =
      sevenNineExtensionVector044BlockerRows := by
  decide

theorem sevenNineExtensionVector044_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector044 =
      sevenNineExtensionVector044Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector044_blocker_rows]
  decide

def sevenNineExtensionVector044Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{2, 6, 7}, {2, 5, 7}, {2, 3, 4}, {1, 6, 7}, {1, 5, 7}, {1, 3, 4}, {0, 4, 6}, {0, 4, 5}, {0, 3, 4}]

theorem sevenNineExtensionVector044_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector044
        sevenNineExtensionVector044Selected0 =
      sevenNineExtensionVector044Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector044_blocker_rows]
  decide

theorem sevenNineExtensionVector044_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector044
      sevenNineExtensionVector044Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector044_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector044Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector044Base0 = false := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
