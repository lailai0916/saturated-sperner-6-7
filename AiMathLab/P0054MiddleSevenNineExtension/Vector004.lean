import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector002

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector004 : List Nat :=
  [0, 0, 1, 1, 0, 1, 1, 2, 1, 0, 0, 0, 0, 0]

theorem sevenNineExtensionVector004_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 4 [] =
      sevenNineExtensionVector004 := by
  decide

def sevenNineExtensionVector004BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6}, {3, 5}, {3, 4}, {2, 6}, {0, 2, 5}, {0, 2, 4}, {0, 1, 6}, {0, 1, 5}, {0, 1, 4}]

def sevenNineExtensionVector004Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector004Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector004Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector004_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector004 =
      sevenNineExtensionVector004BlockerRows := by
  decide

theorem sevenNineExtensionVector004_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector004 =
      sevenNineExtensionVector004Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector004_blocker_rows]
  decide

def sevenNineExtensionVector004Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6, 7}, {3, 5, 7}, {3, 4, 7}, {2, 6, 7}, {0, 2, 5}, {0, 2, 4}, {0, 1, 6}, {0, 1, 5}, {0, 1, 4}]

theorem sevenNineExtensionVector004_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector004
        sevenNineExtensionVector004Selected0 =
      sevenNineExtensionVector004Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector004_blocker_rows]
  decide

theorem sevenNineExtensionVector004_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector004
      sevenNineExtensionVector004Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector004_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector004Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector004Base0 = false := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
