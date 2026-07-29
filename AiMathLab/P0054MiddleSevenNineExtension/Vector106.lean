import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector104

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector106 : List Nat :=
  [0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0]

theorem sevenNineExtensionVector106_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 106 [] =
      sevenNineExtensionVector106 := by
  decide

def sevenNineExtensionVector106BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 5}, {2, 5}, {1, 4}, {1, 2, 3}, {0, 5}, {0, 2, 4}, {0, 2, 3}, {0, 1, 3}]

def sevenNineExtensionVector106Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector106Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector106Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector106_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector106 =
      sevenNineExtensionVector106BlockerRows := by
  decide

theorem sevenNineExtensionVector106_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector106 =
      sevenNineExtensionVector106Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector106_blocker_rows]
  decide

def sevenNineExtensionVector106Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 5, 6}, {2, 5, 6}, {1, 4, 6}, {1, 2, 3}, {0, 5, 6}, {0, 2, 4}, {0, 2, 3}, {0, 1, 3}]

theorem sevenNineExtensionVector106_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector106
        sevenNineExtensionVector106Selected0 =
      sevenNineExtensionVector106Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector106_blocker_rows]
  decide

def sevenNineExtensionVector106Eligible0 :
    List MiddleFourModelPoint :=
  [1, 3, 4, 5]

def sevenNineExtensionVector106BaseBlocker0 :
    G413.Hypergraph MiddleFourModelPoint :=
  ([{0, 1, 5}, {0, 1, 6}, {0, 2, 4}, {0, 2, 6}, {0, 3, 6}, {1, 2, 5}, {1, 2, 6}, {2, 3, 6}, {3, 4, 5}, {3, 4, 6}]).toFinset

theorem sevenNineExtensionVector106_eligible0 :
    middleFourModelEligibleOldPointList sevenNineExtensionVector106
        sevenNineExtensionVector106Base0 =
      sevenNineExtensionVector106Eligible0 := by
  decide

theorem sevenNineExtensionVector106_base_blocker0 :
    fastBlocker sevenNineExtensionVector106Base0 =
      sevenNineExtensionVector106BaseBlocker0 := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
