import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector129

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector131 : List Nat :=
  [1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1]

theorem sevenNineExtensionVector131_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 131 [] =
      sevenNineExtensionVector131 := by
  decide

def sevenNineExtensionVector131BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 6}, {2, 6}, {2, 5}, {2, 3, 4}, {1, 4, 5}, {1, 3, 4}, {0, 6}, {0, 1, 5}]

def sevenNineExtensionVector131Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector131Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector131Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector131_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector131 =
      sevenNineExtensionVector131BlockerRows := by
  decide

theorem sevenNineExtensionVector131_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector131 =
      sevenNineExtensionVector131Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector131_blocker_rows]
  decide

def sevenNineExtensionVector131Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 6, 7}, {2, 6, 7}, {2, 5, 7}, {2, 3, 4}, {1, 4, 5}, {1, 3, 4}, {0, 6, 7}, {0, 1, 5}]

theorem sevenNineExtensionVector131_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector131
        sevenNineExtensionVector131Selected0 =
      sevenNineExtensionVector131Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector131_blocker_rows]
  decide

def sevenNineExtensionVector131Eligible0 :
    List MiddleFourModelPoint :=
  [0, 1, 2, 3, 5, 6]

def sevenNineExtensionVector131BaseBlocker0 :
    G413.Hypergraph MiddleFourModelPoint :=
  ([{0, 2, 4}, {0, 4, 7}, {1, 2, 6}, {1, 2, 7}, {1, 3, 7}, {1, 4, 7}, {3, 5, 6}, {3, 5, 7}, {4, 5, 6}, {4, 5, 7}]).toFinset

theorem sevenNineExtensionVector131_eligible0 :
    middleFourModelEligibleOldPointList sevenNineExtensionVector131
        sevenNineExtensionVector131Base0 =
      sevenNineExtensionVector131Eligible0 := by
  decide

theorem sevenNineExtensionVector131_base_blocker0 :
    fastBlocker sevenNineExtensionVector131Base0 =
      sevenNineExtensionVector131BaseBlocker0 := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
