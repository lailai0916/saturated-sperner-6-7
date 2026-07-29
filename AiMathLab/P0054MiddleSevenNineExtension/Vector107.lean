import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector105

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector107 : List Nat :=
  [0, 2, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 0]

theorem sevenNineExtensionVector107_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 107 [] =
      sevenNineExtensionVector107 := by
  decide

def sevenNineExtensionVector107BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{5, 6}, {3, 5}, {2, 4, 5}, {1, 6}, {1, 3, 4}, {1, 2, 4}, {0, 6}, {0, 3, 4}, {0, 2, 4}]

def sevenNineExtensionVector107Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector107Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector107Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector107_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector107 =
      sevenNineExtensionVector107BlockerRows := by
  decide

theorem sevenNineExtensionVector107_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector107 =
      sevenNineExtensionVector107Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector107_blocker_rows]
  decide

def sevenNineExtensionVector107Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{5, 6, 7}, {3, 5, 7}, {2, 4, 5}, {1, 6, 7}, {1, 3, 4}, {1, 2, 4}, {0, 6, 7}, {0, 3, 4}, {0, 2, 4}]

theorem sevenNineExtensionVector107_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector107
        sevenNineExtensionVector107Selected0 =
      sevenNineExtensionVector107Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector107_blocker_rows]
  decide

theorem sevenNineExtensionVector107_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector107
      sevenNineExtensionVector107Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector107_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector107Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector107Base0 = false := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
