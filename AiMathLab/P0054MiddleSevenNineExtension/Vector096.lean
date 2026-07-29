import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector094

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector096 : List Nat :=
  [0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0]

theorem sevenNineExtensionVector096_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 96 [] =
      sevenNineExtensionVector096 := by
  decide

def sevenNineExtensionVector096BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 5}, {2, 4}, {2, 3}, {1, 4}, {1, 2, 5}, {0, 3, 5}, {0, 1, 5}, {0, 1, 3}]

def sevenNineExtensionVector096Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector096Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector096Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector096_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector096 =
      sevenNineExtensionVector096BlockerRows := by
  decide

theorem sevenNineExtensionVector096_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector096 =
      sevenNineExtensionVector096Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector096_blocker_rows]
  decide

def sevenNineExtensionVector096Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 5, 6}, {2, 4, 6}, {2, 3, 6}, {1, 4, 6}, {1, 2, 5}, {0, 3, 5}, {0, 1, 5}, {0, 1, 3}]

theorem sevenNineExtensionVector096_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector096
        sevenNineExtensionVector096Selected0 =
      sevenNineExtensionVector096Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector096_blocker_rows]
  decide

def sevenNineExtensionVector096Eligible0 :
    List MiddleFourModelPoint :=
  [0, 2, 3, 4]

def sevenNineExtensionVector096BaseBlocker0 :
    G413.Hypergraph MiddleFourModelPoint :=
  ([{0, 1, 6}, {0, 2, 4}, {0, 2, 6}, {0, 5, 6}, {1, 2, 5}, {1, 3, 4}, {1, 3, 6}, {1, 5, 6}, {3, 4, 5}, {3, 5, 6}]).toFinset

theorem sevenNineExtensionVector096_eligible0 :
    middleFourModelEligibleOldPointList sevenNineExtensionVector096
        sevenNineExtensionVector096Base0 =
      sevenNineExtensionVector096Eligible0 := by
  decide

theorem sevenNineExtensionVector096_base_blocker0 :
    fastBlocker sevenNineExtensionVector096Base0 =
      sevenNineExtensionVector096BaseBlocker0 := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
