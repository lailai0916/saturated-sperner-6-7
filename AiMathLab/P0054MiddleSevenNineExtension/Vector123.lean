import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector121

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector123 : List Nat :=
  [1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1]

theorem sevenNineExtensionVector123_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 123 [] =
      sevenNineExtensionVector123 := by
  decide

def sevenNineExtensionVector123BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6}, {3, 5}, {1, 6}, {1, 3, 4}, {1, 2, 5}, {1, 2, 4}, {0, 6}, {0, 2, 5}]

def sevenNineExtensionVector123Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector123Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector123Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector123_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector123 =
      sevenNineExtensionVector123BlockerRows := by
  decide

theorem sevenNineExtensionVector123_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector123 =
      sevenNineExtensionVector123Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector123_blocker_rows]
  decide

def sevenNineExtensionVector123Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6, 7}, {3, 5, 7}, {1, 6, 7}, {1, 3, 4}, {1, 2, 5}, {1, 2, 4}, {0, 6, 7}, {0, 2, 5}]

theorem sevenNineExtensionVector123_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector123
        sevenNineExtensionVector123Selected0 =
      sevenNineExtensionVector123Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector123_blocker_rows]
  decide

def sevenNineExtensionVector123Eligible0 :
    List MiddleFourModelPoint :=
  [0, 2, 3, 4, 5, 6]

def sevenNineExtensionVector123BaseBlocker0 :
    G413.Hypergraph MiddleFourModelPoint :=
  ([{0, 1, 3}, {0, 1, 7}, {1, 2, 7}, {1, 5, 6}, {1, 5, 7}, {2, 3, 6}, {2, 3, 7}, {2, 4, 7}, {4, 5, 6}, {4, 5, 7}]).toFinset

theorem sevenNineExtensionVector123_eligible0 :
    middleFourModelEligibleOldPointList sevenNineExtensionVector123
        sevenNineExtensionVector123Base0 =
      sevenNineExtensionVector123Eligible0 := by
  decide

theorem sevenNineExtensionVector123_base_blocker0 :
    fastBlocker sevenNineExtensionVector123Base0 =
      sevenNineExtensionVector123BaseBlocker0 := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
