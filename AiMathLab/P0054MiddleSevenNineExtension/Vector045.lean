import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector043

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector045 : List Nat :=
  [1, 1, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0]

theorem sevenNineExtensionVector045_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 45 [] =
      sevenNineExtensionVector045 := by
  decide

def sevenNineExtensionVector045BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5}, {3, 4}, {2, 5}, {2, 4}, {1, 5, 6}, {1, 4, 6}, {0, 3, 6}, {0, 2, 6}, {0, 1, 6}]

def sevenNineExtensionVector045Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector045Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector045Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector045_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector045 =
      sevenNineExtensionVector045BlockerRows := by
  decide

theorem sevenNineExtensionVector045_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector045 =
      sevenNineExtensionVector045Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector045_blocker_rows]
  decide

def sevenNineExtensionVector045Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {3, 4, 7}, {2, 5, 7}, {2, 4, 7}, {1, 5, 6}, {1, 4, 6}, {0, 3, 6}, {0, 2, 6}, {0, 1, 6}]

theorem sevenNineExtensionVector045_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector045
        sevenNineExtensionVector045Selected0 =
      sevenNineExtensionVector045Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector045_blocker_rows]
  decide

theorem sevenNineExtensionVector045_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector045
      sevenNineExtensionVector045Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector045_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector045Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector045Base0 = false := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
