import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector125

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector127 : List Nat :=
  [2, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 1]

theorem sevenNineExtensionVector127_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 127 [] =
      sevenNineExtensionVector127 := by
  decide

def sevenNineExtensionVector127BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 6}, {3, 4}, {2, 4, 5}, {1, 6}, {1, 3, 5}, {1, 2, 5}, {0, 6}, {0, 3, 5}, {0, 2, 5}]

def sevenNineExtensionVector127Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector127Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector127Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector127_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector127 =
      sevenNineExtensionVector127BlockerRows := by
  decide

theorem sevenNineExtensionVector127_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector127 =
      sevenNineExtensionVector127Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector127_blocker_rows]
  decide

def sevenNineExtensionVector127Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 6, 7}, {3, 4, 7}, {2, 4, 5}, {1, 6, 7}, {1, 3, 5}, {1, 2, 5}, {0, 6, 7}, {0, 3, 5}, {0, 2, 5}]

theorem sevenNineExtensionVector127_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector127
        sevenNineExtensionVector127Selected0 =
      sevenNineExtensionVector127Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector127_blocker_rows]
  decide

theorem sevenNineExtensionVector127_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector127
      sevenNineExtensionVector127Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector127_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector127Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector127Base0 = false := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
