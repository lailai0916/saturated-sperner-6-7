import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector102

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector104 : List Nat :=
  [0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0]

theorem sevenNineExtensionVector104_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 104 [] =
      sevenNineExtensionVector104 := by
  decide

def sevenNineExtensionVector104BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{5, 6}, {3, 5}, {1, 6}, {1, 3, 4}, {1, 2, 5}, {1, 2, 4}, {0, 6}, {0, 3, 4}]

def sevenNineExtensionVector104Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector104Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector104Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector104_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector104 =
      sevenNineExtensionVector104BlockerRows := by
  decide

theorem sevenNineExtensionVector104_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector104 =
      sevenNineExtensionVector104Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector104_blocker_rows]
  decide

def sevenNineExtensionVector104Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{5, 6, 7}, {3, 5, 7}, {1, 6, 7}, {1, 3, 4}, {1, 2, 5}, {1, 2, 4}, {0, 6, 7}, {0, 3, 4}]

theorem sevenNineExtensionVector104_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector104
        sevenNineExtensionVector104Selected0 =
      sevenNineExtensionVector104Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector104_blocker_rows]
  decide

def sevenNineExtensionVector104Eligible0 :
    List MiddleFourModelPoint :=
  [0, 2, 3, 4, 5, 6]

def sevenNineExtensionVector104BaseBlocker0 :
    G413.Hypergraph MiddleFourModelPoint :=
  ([{0, 1, 5}, {0, 1, 7}, {1, 3, 6}, {1, 3, 7}, {1, 4, 7}, {2, 3, 6}, {2, 3, 7}, {2, 4, 7}, {4, 5, 6}, {4, 5, 7}]).toFinset

theorem sevenNineExtensionVector104_eligible0 :
    middleFourModelEligibleOldPointList sevenNineExtensionVector104
        sevenNineExtensionVector104Base0 =
      sevenNineExtensionVector104Eligible0 := by
  decide

theorem sevenNineExtensionVector104_base_blocker0 :
    fastBlocker sevenNineExtensionVector104Base0 =
      sevenNineExtensionVector104BaseBlocker0 := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
