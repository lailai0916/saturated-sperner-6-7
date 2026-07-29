import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector009

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector011 : List Nat :=
  [1, 0, 0, 0, 1, 1, 1, 2, 0, 1, 0, 0, 0, 0]

theorem sevenNineExtensionVector011_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 11 [] =
      sevenNineExtensionVector011 := by
  decide

def sevenNineExtensionVector011BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6}, {3, 5}, {3, 4}, {1, 6}, {1, 2, 5}, {1, 2, 4}, {0, 2, 6}, {0, 2, 5}, {0, 2, 4}]

def sevenNineExtensionVector011Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector011Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector011Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector011_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector011 =
      sevenNineExtensionVector011BlockerRows := by
  decide

theorem sevenNineExtensionVector011_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector011 =
      sevenNineExtensionVector011Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector011_blocker_rows]
  decide

def sevenNineExtensionVector011Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6, 7}, {3, 5, 7}, {3, 4, 7}, {1, 6, 7}, {1, 2, 5}, {1, 2, 4}, {0, 2, 6}, {0, 2, 5}, {0, 2, 4}]

theorem sevenNineExtensionVector011_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector011
        sevenNineExtensionVector011Selected0 =
      sevenNineExtensionVector011Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector011_blocker_rows]
  decide

theorem sevenNineExtensionVector011_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector011
      sevenNineExtensionVector011Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector011_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector011Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector011Base0 = false := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
