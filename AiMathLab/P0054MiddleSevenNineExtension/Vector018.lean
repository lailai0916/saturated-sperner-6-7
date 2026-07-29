import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector016

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector018 : List Nat :=
  [0, 0, 1, 0, 1, 2, 0, 0, 1, 2, 0, 0, 0, 0]

theorem sevenNineExtensionVector018_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 18 [] =
      sevenNineExtensionVector018 := by
  decide

def sevenNineExtensionVector018BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4}, {2, 4}, {1, 6}, {1, 5}, {0, 3, 6}, {0, 3, 5}, {0, 2, 6}, {0, 2, 5}, {0, 1, 4}]

def sevenNineExtensionVector018Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector018Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector018Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector018_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector018 =
      sevenNineExtensionVector018BlockerRows := by
  decide

theorem sevenNineExtensionVector018_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector018 =
      sevenNineExtensionVector018Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector018_blocker_rows]
  decide

def sevenNineExtensionVector018Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 7}, {2, 4, 7}, {1, 6, 7}, {1, 5, 7}, {0, 3, 6}, {0, 3, 5}, {0, 2, 6}, {0, 2, 5}, {0, 1, 4}]

theorem sevenNineExtensionVector018_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector018
        sevenNineExtensionVector018Selected0 =
      sevenNineExtensionVector018Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector018_blocker_rows]
  decide

theorem sevenNineExtensionVector018_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector018
      sevenNineExtensionVector018Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector018_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector018Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector018Base0 = false := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
