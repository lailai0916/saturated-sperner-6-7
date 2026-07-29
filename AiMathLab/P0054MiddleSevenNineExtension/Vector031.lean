import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector029

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector031 : List Nat :=
  [0, 0, 1, 2, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0]

theorem sevenNineExtensionVector031_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 31 [] =
      sevenNineExtensionVector031 := by
  decide

def sevenNineExtensionVector031BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6}, {3, 5}, {2, 6}, {1, 6}, {0, 3, 4}, {0, 2, 5}, {0, 2, 4}, {0, 1, 5}, {0, 1, 4}]

def sevenNineExtensionVector031Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector031Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector031Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector031_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector031 =
      sevenNineExtensionVector031BlockerRows := by
  decide

theorem sevenNineExtensionVector031_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector031 =
      sevenNineExtensionVector031Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector031_blocker_rows]
  decide

def sevenNineExtensionVector031Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6, 7}, {3, 5, 7}, {2, 6, 7}, {1, 6, 7}, {0, 3, 4}, {0, 2, 5}, {0, 2, 4}, {0, 1, 5}, {0, 1, 4}]

theorem sevenNineExtensionVector031_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector031
        sevenNineExtensionVector031Selected0 =
      sevenNineExtensionVector031Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector031_blocker_rows]
  decide

theorem sevenNineExtensionVector031_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector031
      sevenNineExtensionVector031Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector031_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector031Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector031Base0 = false := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
