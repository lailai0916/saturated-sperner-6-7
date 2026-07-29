import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector040

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector042 : List Nat :=
  [0, 1, 1, 0, 1, 0, 1, 2, 0, 0, 0, 1, 0, 0]

theorem sevenNineExtensionVector042_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 42 [] =
      sevenNineExtensionVector042 := by
  decide

def sevenNineExtensionVector042BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6}, {3, 5}, {3, 4}, {1, 6}, {1, 2, 5}, {1, 2, 4}, {0, 2, 6}, {0, 2, 5}, {0, 2, 4}]

def sevenNineExtensionVector042Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector042Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector042Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector042_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector042 =
      sevenNineExtensionVector042BlockerRows := by
  decide

theorem sevenNineExtensionVector042_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector042 =
      sevenNineExtensionVector042Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector042_blocker_rows]
  decide

def sevenNineExtensionVector042Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6, 7}, {3, 5, 7}, {3, 4, 7}, {1, 6, 7}, {1, 2, 5}, {1, 2, 4}, {0, 2, 6}, {0, 2, 5}, {0, 2, 4}]

theorem sevenNineExtensionVector042_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector042
        sevenNineExtensionVector042Selected0 =
      sevenNineExtensionVector042Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector042_blocker_rows]
  decide

theorem sevenNineExtensionVector042_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector042
      sevenNineExtensionVector042Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector042_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector042Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector042Base0 = false := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
