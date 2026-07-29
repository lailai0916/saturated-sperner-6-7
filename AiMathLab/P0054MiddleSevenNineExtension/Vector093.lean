import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector091

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector093 : List Nat :=
  [0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0]

theorem sevenNineExtensionVector093_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 93 [] =
      sevenNineExtensionVector093 := by
  decide

def sevenNineExtensionVector093BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 5}, {2, 4}, {1, 4}, {1, 2, 5}, {1, 2, 3}, {0, 5}, {0, 2, 3}, {0, 1, 3}]

def sevenNineExtensionVector093Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector093Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector093Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector093_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector093 =
      sevenNineExtensionVector093BlockerRows := by
  decide

theorem sevenNineExtensionVector093_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector093 =
      sevenNineExtensionVector093Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector093_blocker_rows]
  decide

def sevenNineExtensionVector093Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 5, 6}, {2, 4, 6}, {1, 4, 6}, {1, 2, 5}, {1, 2, 3}, {0, 5, 6}, {0, 2, 3}, {0, 1, 3}]

theorem sevenNineExtensionVector093_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector093
        sevenNineExtensionVector093Selected0 =
      sevenNineExtensionVector093Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector093_blocker_rows]
  decide

def sevenNineExtensionVector093Eligible0 :
    List MiddleFourModelPoint :=
  [0, 3, 4, 5]

def sevenNineExtensionVector093BaseBlocker0 :
    G413.Hypergraph MiddleFourModelPoint :=
  ([{0, 1, 4}, {0, 1, 6}, {0, 2, 4}, {0, 2, 6}, {1, 2, 5}, {1, 2, 6}, {1, 3, 6}, {2, 3, 6}, {3, 4, 5}, {3, 5, 6}]).toFinset

theorem sevenNineExtensionVector093_eligible0 :
    middleFourModelEligibleOldPointList sevenNineExtensionVector093
        sevenNineExtensionVector093Base0 =
      sevenNineExtensionVector093Eligible0 := by
  decide

theorem sevenNineExtensionVector093_base_blocker0 :
    fastBlocker sevenNineExtensionVector093Base0 =
      sevenNineExtensionVector093BaseBlocker0 := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
