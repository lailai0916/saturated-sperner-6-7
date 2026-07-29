import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector005

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector007 : List Nat :=
  [0, 0, 1, 1, 2, 0, 0, 1, 0, 2, 0, 0, 0, 0]

theorem sevenNineExtensionVector007_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 7 [] =
      sevenNineExtensionVector007 := by
  decide

def sevenNineExtensionVector007BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6}, {3, 5}, {2, 6}, {2, 5}, {0, 3, 4}, {0, 2, 4}, {0, 1, 6}, {0, 1, 5}, {0, 1, 4}]

def sevenNineExtensionVector007Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector007Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector007Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector007_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector007 =
      sevenNineExtensionVector007BlockerRows := by
  decide

theorem sevenNineExtensionVector007_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector007 =
      sevenNineExtensionVector007Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector007_blocker_rows]
  decide

def sevenNineExtensionVector007Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6, 7}, {3, 5, 7}, {2, 6, 7}, {2, 5, 7}, {0, 3, 4}, {0, 2, 4}, {0, 1, 6}, {0, 1, 5}, {0, 1, 4}]

theorem sevenNineExtensionVector007_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector007
        sevenNineExtensionVector007Selected0 =
      sevenNineExtensionVector007Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector007_blocker_rows]
  decide

theorem sevenNineExtensionVector007_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector007
      sevenNineExtensionVector007Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector007_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector007Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector007Base0 = false := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
