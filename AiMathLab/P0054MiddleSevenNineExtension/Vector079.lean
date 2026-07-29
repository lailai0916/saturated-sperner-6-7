import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector077

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector079 : List Nat :=
  [1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0]

theorem sevenNineExtensionVector079_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 79 [] =
      sevenNineExtensionVector079 := by
  decide

def sevenNineExtensionVector079BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6}, {3, 5}, {3, 4}, {2, 5}, {1, 2, 6}, {1, 2, 4}, {0, 5, 6}, {0, 1, 6}]

def sevenNineExtensionVector079Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector079Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector079Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector079_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector079 =
      sevenNineExtensionVector079BlockerRows := by
  decide

theorem sevenNineExtensionVector079_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector079 =
      sevenNineExtensionVector079Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector079_blocker_rows]
  decide

def sevenNineExtensionVector079Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6, 7}, {3, 5, 7}, {3, 4, 7}, {2, 5, 7}, {1, 2, 6}, {1, 2, 4}, {0, 5, 6}, {0, 1, 6}]

theorem sevenNineExtensionVector079_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector079
        sevenNineExtensionVector079Selected0 =
      sevenNineExtensionVector079Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector079_blocker_rows]
  decide

def sevenNineExtensionVector079Eligible0 :
    List MiddleFourModelPoint :=
  [0, 1, 2, 3, 4, 5]

def sevenNineExtensionVector079BaseBlocker0 :
    G413.Hypergraph MiddleFourModelPoint :=
  ([{0, 1, 7}, {0, 2, 3}, {0, 2, 7}, {1, 3, 5}, {1, 5, 7}, {1, 6, 7}, {2, 3, 6}, {2, 6, 7}, {4, 5, 6}, {4, 6, 7}]).toFinset

theorem sevenNineExtensionVector079_eligible0 :
    middleFourModelEligibleOldPointList sevenNineExtensionVector079
        sevenNineExtensionVector079Base0 =
      sevenNineExtensionVector079Eligible0 := by
  decide

theorem sevenNineExtensionVector079_base_blocker0 :
    fastBlocker sevenNineExtensionVector079Base0 =
      sevenNineExtensionVector079BaseBlocker0 := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
