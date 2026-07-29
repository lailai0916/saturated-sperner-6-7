import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector026

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector028 : List Nat :=
  [0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0]

theorem sevenNineExtensionVector028_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 28 [] =
      sevenNineExtensionVector028 := by
  decide

def sevenNineExtensionVector028BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6}, {3, 5}, {3, 4}, {2, 6}, {1, 5, 6}, {0, 2, 5}, {0, 2, 4}, {0, 1, 5}]

def sevenNineExtensionVector028Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector028Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector028Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector028_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector028 =
      sevenNineExtensionVector028BlockerRows := by
  decide

theorem sevenNineExtensionVector028_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector028 =
      sevenNineExtensionVector028Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector028_blocker_rows]
  decide

def sevenNineExtensionVector028Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6, 7}, {3, 5, 7}, {3, 4, 7}, {2, 6, 7}, {1, 5, 6}, {0, 2, 5}, {0, 2, 4}, {0, 1, 5}]

theorem sevenNineExtensionVector028_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector028
        sevenNineExtensionVector028Selected0 =
      sevenNineExtensionVector028Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector028_blocker_rows]
  decide

def sevenNineExtensionVector028Eligible0 :
    List MiddleFourModelPoint :=
  [0, 1, 2, 3, 4, 6]

def sevenNineExtensionVector028BaseBlocker0 :
    G413.Hypergraph MiddleFourModelPoint :=
  ([{0, 1, 7}, {0, 3, 6}, {0, 5, 7}, {0, 6, 7}, {1, 2, 3}, {1, 2, 7}, {2, 3, 5}, {2, 5, 7}, {4, 5, 6}, {4, 5, 7}]).toFinset

theorem sevenNineExtensionVector028_eligible0 :
    middleFourModelEligibleOldPointList sevenNineExtensionVector028
        sevenNineExtensionVector028Base0 =
      sevenNineExtensionVector028Eligible0 := by
  decide

theorem sevenNineExtensionVector028_base_blocker0 :
    fastBlocker sevenNineExtensionVector028Base0 =
      sevenNineExtensionVector028BaseBlocker0 := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
