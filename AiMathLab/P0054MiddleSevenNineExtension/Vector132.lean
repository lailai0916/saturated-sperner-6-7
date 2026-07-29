import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector130

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector132 : List Nat :=
  [0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1]

theorem sevenNineExtensionVector132_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 132 [] =
      sevenNineExtensionVector132 := by
  decide

def sevenNineExtensionVector132BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5}, {2, 5}, {1, 5}, {1, 4}, {1, 2, 3}, {0, 3, 4}, {0, 2, 4}, {0, 2, 3}]

def sevenNineExtensionVector132Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector132Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector132Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector132_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector132 =
      sevenNineExtensionVector132BlockerRows := by
  decide

theorem sevenNineExtensionVector132_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector132 =
      sevenNineExtensionVector132Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector132_blocker_rows]
  decide

def sevenNineExtensionVector132Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 6}, {2, 5, 6}, {1, 5, 6}, {1, 4, 6}, {1, 2, 3}, {0, 3, 4}, {0, 2, 4}, {0, 2, 3}]

theorem sevenNineExtensionVector132_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector132
        sevenNineExtensionVector132Selected0 =
      sevenNineExtensionVector132Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector132_blocker_rows]
  decide

def sevenNineExtensionVector132Eligible0 :
    List MiddleFourModelPoint :=
  [0, 1, 4, 5]

def sevenNineExtensionVector132BaseBlocker0 :
    G413.Hypergraph MiddleFourModelPoint :=
  ([{0, 1, 5}, {0, 1, 6}, {0, 2, 6}, {0, 3, 6}, {1, 2, 3}, {2, 3, 6}, {2, 4, 5}, {2, 4, 6}, {3, 4, 5}, {3, 4, 6}]).toFinset

theorem sevenNineExtensionVector132_eligible0 :
    middleFourModelEligibleOldPointList sevenNineExtensionVector132
        sevenNineExtensionVector132Base0 =
      sevenNineExtensionVector132Eligible0 := by
  decide

theorem sevenNineExtensionVector132_base_blocker0 :
    fastBlocker sevenNineExtensionVector132Base0 =
      sevenNineExtensionVector132BaseBlocker0 := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
