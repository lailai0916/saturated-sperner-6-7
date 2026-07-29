import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector000

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector002 : List Nat :=
  [0, 1, 0, 0, 1, 2, 0, 1, 2, 0, 0, 0, 0, 0]

theorem sevenNineExtensionVector002_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 2 [] =
      sevenNineExtensionVector002 := by
  decide

def sevenNineExtensionVector002BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6}, {3, 5}, {2, 6}, {2, 5}, {1, 3, 4}, {1, 2, 4}, {0, 1, 6}, {0, 1, 5}, {0, 1, 4}]

def sevenNineExtensionVector002Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector002Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector002Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector002_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector002 =
      sevenNineExtensionVector002BlockerRows := by
  decide

theorem sevenNineExtensionVector002_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector002 =
      sevenNineExtensionVector002Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector002_blocker_rows]
  decide

def sevenNineExtensionVector002Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6, 7}, {3, 5, 7}, {2, 6, 7}, {2, 5, 7}, {1, 3, 4}, {1, 2, 4}, {0, 1, 6}, {0, 1, 5}, {0, 1, 4}]

theorem sevenNineExtensionVector002_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector002
        sevenNineExtensionVector002Selected0 =
      sevenNineExtensionVector002Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector002_blocker_rows]
  decide

theorem sevenNineExtensionVector002_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector002
      sevenNineExtensionVector002Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector002_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector002Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector002Base0 = false := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
