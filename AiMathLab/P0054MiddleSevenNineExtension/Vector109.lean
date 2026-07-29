import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector107

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector109 : List Nat :=
  [0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0]

theorem sevenNineExtensionVector109_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 109 [] =
      sevenNineExtensionVector109 := by
  decide

def sevenNineExtensionVector109BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 5}, {2, 5}, {2, 3}, {1, 3, 4}, {0, 5}, {0, 2, 4}, {0, 1, 4}, {0, 1, 3}]

def sevenNineExtensionVector109Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector109Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector109Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector109_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector109 =
      sevenNineExtensionVector109BlockerRows := by
  decide

theorem sevenNineExtensionVector109_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector109 =
      sevenNineExtensionVector109Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector109_blocker_rows]
  decide

def sevenNineExtensionVector109Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 5, 6}, {2, 5, 6}, {2, 3, 6}, {1, 3, 4}, {0, 5, 6}, {0, 2, 4}, {0, 1, 4}, {0, 1, 3}]

theorem sevenNineExtensionVector109_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector109
        sevenNineExtensionVector109Selected0 =
      sevenNineExtensionVector109Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector109_blocker_rows]
  decide

def sevenNineExtensionVector109Eligible0 :
    List MiddleFourModelPoint :=
  [1, 2, 3, 5]

def sevenNineExtensionVector109BaseBlocker0 :
    G413.Hypergraph MiddleFourModelPoint :=
  ([{0, 1, 6}, {0, 2, 4}, {0, 3, 5}, {0, 3, 6}, {0, 4, 6}, {1, 2, 5}, {1, 2, 6}, {1, 4, 6}, {3, 4, 5}, {3, 4, 6}]).toFinset

theorem sevenNineExtensionVector109_eligible0 :
    middleFourModelEligibleOldPointList sevenNineExtensionVector109
        sevenNineExtensionVector109Base0 =
      sevenNineExtensionVector109Eligible0 := by
  decide

theorem sevenNineExtensionVector109_base_blocker0 :
    fastBlocker sevenNineExtensionVector109Base0 =
      sevenNineExtensionVector109BaseBlocker0 := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
