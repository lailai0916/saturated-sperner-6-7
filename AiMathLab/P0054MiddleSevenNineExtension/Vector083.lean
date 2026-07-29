import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector081

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector083 : List Nat :=
  [0, 0, 2, 0, 0, 2, 0, 0, 1, 1, 0, 1, 0, 0]

theorem sevenNineExtensionVector083_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 83 [] =
      sevenNineExtensionVector083 := by
  decide

def sevenNineExtensionVector083BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 5, 6}, {3, 4}, {2, 4}, {1, 6}, {1, 3, 5}, {1, 2, 5}, {0, 6}, {0, 3, 5}, {0, 2, 5}]

def sevenNineExtensionVector083Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector083Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector083Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector083_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector083 =
      sevenNineExtensionVector083BlockerRows := by
  decide

theorem sevenNineExtensionVector083_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector083 =
      sevenNineExtensionVector083Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector083_blocker_rows]
  decide

def sevenNineExtensionVector083Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 5, 6}, {3, 4, 7}, {2, 4, 7}, {1, 6, 7}, {1, 3, 5}, {1, 2, 5}, {0, 6, 7}, {0, 3, 5}, {0, 2, 5}]

theorem sevenNineExtensionVector083_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector083
        sevenNineExtensionVector083Selected0 =
      sevenNineExtensionVector083Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector083_blocker_rows]
  decide

theorem sevenNineExtensionVector083_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector083
      sevenNineExtensionVector083Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector083_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector083Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector083Base0 = false := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
