import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector115

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector117 : List Nat :=
  [1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 0]

theorem sevenNineExtensionVector117_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 117 [] =
      sevenNineExtensionVector117 := by
  decide

def sevenNineExtensionVector117BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5}, {2, 5}, {1, 5}, {1, 4}, {1, 2, 3}, {0, 3, 4}, {0, 2, 4}, {0, 2, 3}]

def sevenNineExtensionVector117Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector117Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector117Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector117_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector117 =
      sevenNineExtensionVector117BlockerRows := by
  decide

theorem sevenNineExtensionVector117_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector117 =
      sevenNineExtensionVector117Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector117_blocker_rows]
  decide

def sevenNineExtensionVector117Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 6}, {2, 5, 6}, {1, 5, 6}, {1, 4, 6}, {1, 2, 3}, {0, 3, 4}, {0, 2, 4}, {0, 2, 3}]

theorem sevenNineExtensionVector117_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector117
        sevenNineExtensionVector117Selected0 =
      sevenNineExtensionVector117Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector117_blocker_rows]
  decide

def sevenNineExtensionVector117Eligible0 :
    List MiddleFourModelPoint :=
  [0, 1, 4, 5]

def sevenNineExtensionVector117BaseBlocker0 :
    G413.Hypergraph MiddleFourModelPoint :=
  ([{0, 1, 5}, {0, 1, 6}, {0, 2, 6}, {0, 3, 6}, {1, 2, 3}, {2, 3, 6}, {2, 4, 5}, {2, 4, 6}, {3, 4, 5}, {3, 4, 6}]).toFinset

theorem sevenNineExtensionVector117_eligible0 :
    middleFourModelEligibleOldPointList sevenNineExtensionVector117
        sevenNineExtensionVector117Base0 =
      sevenNineExtensionVector117Eligible0 := by
  decide

theorem sevenNineExtensionVector117_base_blocker0 :
    fastBlocker sevenNineExtensionVector117Base0 =
      sevenNineExtensionVector117BaseBlocker0 := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
