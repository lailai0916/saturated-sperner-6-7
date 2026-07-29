import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector127

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector129 : List Nat :=
  [1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1]

theorem sevenNineExtensionVector129_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 129 [] =
      sevenNineExtensionVector129 := by
  decide

def sevenNineExtensionVector129BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6}, {2, 6}, {2, 5}, {2, 3, 4}, {1, 3, 5}, {1, 3, 4}, {0, 6}, {0, 1, 5}]

def sevenNineExtensionVector129Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector129Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector129Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector129_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector129 =
      sevenNineExtensionVector129BlockerRows := by
  decide

theorem sevenNineExtensionVector129_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector129 =
      sevenNineExtensionVector129Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector129_blocker_rows]
  decide

def sevenNineExtensionVector129Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6, 7}, {2, 6, 7}, {2, 5, 7}, {2, 3, 4}, {1, 3, 5}, {1, 3, 4}, {0, 6, 7}, {0, 1, 5}]

theorem sevenNineExtensionVector129_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector129
        sevenNineExtensionVector129Selected0 =
      sevenNineExtensionVector129Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector129_blocker_rows]
  decide

def sevenNineExtensionVector129Eligible0 :
    List MiddleFourModelPoint :=
  [0, 1, 2, 4, 5, 6]

def sevenNineExtensionVector129BaseBlocker0 :
    G413.Hypergraph MiddleFourModelPoint :=
  ([{0, 2, 3}, {0, 3, 7}, {1, 2, 6}, {1, 2, 7}, {1, 3, 7}, {1, 4, 7}, {3, 5, 6}, {3, 5, 7}, {4, 5, 6}, {4, 5, 7}]).toFinset

theorem sevenNineExtensionVector129_eligible0 :
    middleFourModelEligibleOldPointList sevenNineExtensionVector129
        sevenNineExtensionVector129Base0 =
      sevenNineExtensionVector129Eligible0 := by
  decide

theorem sevenNineExtensionVector129_base_blocker0 :
    fastBlocker sevenNineExtensionVector129Base0 =
      sevenNineExtensionVector129BaseBlocker0 := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
