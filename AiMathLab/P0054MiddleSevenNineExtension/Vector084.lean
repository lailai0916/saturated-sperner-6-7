import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector082

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector084 : List Nat :=
  [0, 0, 0, 0, 1, 1, 0, 0, 2, 2, 0, 1, 0, 0]

theorem sevenNineExtensionVector084_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 84 [] =
      sevenNineExtensionVector084 := by
  decide

def sevenNineExtensionVector084BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 6}, {3, 4, 6}, {2, 5, 6}, {2, 4, 6}, {1, 3}, {1, 2}, {0, 5}, {0, 4}, {0, 1, 6}]

def sevenNineExtensionVector084Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector084Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector084Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector084_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector084 =
      sevenNineExtensionVector084BlockerRows := by
  decide

theorem sevenNineExtensionVector084_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector084 =
      sevenNineExtensionVector084Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector084_blocker_rows]
  decide

def sevenNineExtensionVector084Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 6}, {3, 4, 6}, {2, 5, 6}, {2, 4, 6}, {1, 3, 7}, {1, 2, 7}, {0, 5, 7}, {0, 4, 7}, {0, 1, 6}]

theorem sevenNineExtensionVector084_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector084
        sevenNineExtensionVector084Selected0 =
      sevenNineExtensionVector084Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector084_blocker_rows]
  decide

theorem sevenNineExtensionVector084_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector084
      sevenNineExtensionVector084Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector084_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector084Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector084Base0 = false := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
