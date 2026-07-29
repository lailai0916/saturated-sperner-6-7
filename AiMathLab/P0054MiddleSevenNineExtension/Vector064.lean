import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector062

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector064 : List Nat :=
  [1, 0, 1, 0, 1, 0, 0, 0, 0, 2, 0, 2, 0, 0]

theorem sevenNineExtensionVector064_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 64 [] =
      sevenNineExtensionVector064 := by
  decide

def sevenNineExtensionVector064BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{2, 4}, {2, 3}, {1, 6}, {1, 5}, {0, 4, 6}, {0, 4, 5}, {0, 3, 6}, {0, 3, 5}]

def sevenNineExtensionVector064Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector064Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector064Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector064_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector064 =
      sevenNineExtensionVector064BlockerRows := by
  decide

theorem sevenNineExtensionVector064_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector064 =
      sevenNineExtensionVector064Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector064_blocker_rows]
  decide

def sevenNineExtensionVector064Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{2, 4, 7}, {2, 3, 7}, {1, 6, 7}, {1, 5, 7}, {0, 4, 6}, {0, 4, 5}, {0, 3, 6}, {0, 3, 5}]

theorem sevenNineExtensionVector064_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector064
        sevenNineExtensionVector064Selected0 =
      sevenNineExtensionVector064Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector064_blocker_rows]
  decide

def sevenNineExtensionVector064Eligible0 :
    List MiddleFourModelPoint :=
  [1, 2, 3, 4, 5, 6]

def sevenNineExtensionVector064BaseBlocker0 :
    G413.Hypergraph MiddleFourModelPoint :=
  ([{0, 7}, {0, 1, 2}, {1, 3, 4}, {2, 5, 6}, {3, 4, 7}, {5, 6, 7}, {3, 4, 5, 6}]).toFinset

theorem sevenNineExtensionVector064_eligible0 :
    middleFourModelEligibleOldPointList sevenNineExtensionVector064
        sevenNineExtensionVector064Base0 =
      sevenNineExtensionVector064Eligible0 := by
  decide

theorem sevenNineExtensionVector064_base_blocker0 :
    fastBlocker sevenNineExtensionVector064Base0 =
      sevenNineExtensionVector064BaseBlocker0 := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
