import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector124

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector126 : List Nat :=
  [0, 0, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1]

theorem sevenNineExtensionVector126_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 126 [] =
      sevenNineExtensionVector126 := by
  decide

def sevenNineExtensionVector126BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5}, {2, 5}, {2, 4}, {1, 3, 4}, {0, 5}, {0, 2, 3}, {0, 1, 4}, {0, 1, 3}]

def sevenNineExtensionVector126Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector126Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector126Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector126_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector126 =
      sevenNineExtensionVector126BlockerRows := by
  decide

theorem sevenNineExtensionVector126_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector126 =
      sevenNineExtensionVector126Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector126_blocker_rows]
  decide

def sevenNineExtensionVector126Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 6}, {2, 5, 6}, {2, 4, 6}, {1, 3, 4}, {0, 5, 6}, {0, 2, 3}, {0, 1, 4}, {0, 1, 3}]

theorem sevenNineExtensionVector126_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector126
        sevenNineExtensionVector126Selected0 =
      sevenNineExtensionVector126Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector126_blocker_rows]
  decide

def sevenNineExtensionVector126Eligible0 :
    List MiddleFourModelPoint :=
  [1, 2, 4, 5]

def sevenNineExtensionVector126BaseBlocker0 :
    G413.Hypergraph MiddleFourModelPoint :=
  ([{0, 1, 6}, {0, 2, 3}, {0, 3, 6}, {0, 4, 5}, {0, 4, 6}, {1, 2, 5}, {1, 2, 6}, {1, 3, 6}, {3, 4, 5}, {3, 4, 6}]).toFinset

theorem sevenNineExtensionVector126_eligible0 :
    middleFourModelEligibleOldPointList sevenNineExtensionVector126
        sevenNineExtensionVector126Base0 =
      sevenNineExtensionVector126Eligible0 := by
  decide

theorem sevenNineExtensionVector126_base_blocker0 :
    fastBlocker sevenNineExtensionVector126Base0 =
      sevenNineExtensionVector126BaseBlocker0 := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
