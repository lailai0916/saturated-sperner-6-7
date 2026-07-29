import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector097

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector099 : List Nat :=
  [1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 0]

theorem sevenNineExtensionVector099_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 99 [] =
      sevenNineExtensionVector099 := by
  decide

def sevenNineExtensionVector099BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 5}, {2, 4}, {1, 4}, {1, 3}, {1, 2, 5}, {0, 3, 5}, {0, 2, 5}, {0, 2, 3}]

def sevenNineExtensionVector099Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector099Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector099Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector099_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector099 =
      sevenNineExtensionVector099BlockerRows := by
  decide

theorem sevenNineExtensionVector099_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector099 =
      sevenNineExtensionVector099Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector099_blocker_rows]
  decide

def sevenNineExtensionVector099Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 5, 6}, {2, 4, 6}, {1, 4, 6}, {1, 3, 6}, {1, 2, 5}, {0, 3, 5}, {0, 2, 5}, {0, 2, 3}]

theorem sevenNineExtensionVector099_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector099
        sevenNineExtensionVector099Selected0 =
      sevenNineExtensionVector099Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector099_blocker_rows]
  decide

def sevenNineExtensionVector099Eligible0 :
    List MiddleFourModelPoint :=
  [0, 1, 3, 4]

def sevenNineExtensionVector099BaseBlocker0 :
    G413.Hypergraph MiddleFourModelPoint :=
  ([{0, 1, 4}, {0, 1, 6}, {0, 2, 6}, {0, 5, 6}, {1, 2, 5}, {2, 3, 4}, {2, 3, 6}, {2, 5, 6}, {3, 4, 5}, {3, 5, 6}]).toFinset

theorem sevenNineExtensionVector099_eligible0 :
    middleFourModelEligibleOldPointList sevenNineExtensionVector099
        sevenNineExtensionVector099Base0 =
      sevenNineExtensionVector099Eligible0 := by
  decide

theorem sevenNineExtensionVector099_base_blocker0 :
    fastBlocker sevenNineExtensionVector099Base0 =
      sevenNineExtensionVector099BaseBlocker0 := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
