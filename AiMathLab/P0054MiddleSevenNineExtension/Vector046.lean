import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector044

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector046 : List Nat :=
  [1, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0]

theorem sevenNineExtensionVector046_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 46 [] =
      sevenNineExtensionVector046 := by
  decide

def sevenNineExtensionVector046BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4}, {2, 4}, {1, 6}, {1, 5}, {0, 3, 6}, {0, 3, 5}, {0, 2, 6}, {0, 2, 5}]

def sevenNineExtensionVector046Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector046Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector046Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector046_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector046 =
      sevenNineExtensionVector046BlockerRows := by
  decide

theorem sevenNineExtensionVector046_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector046 =
      sevenNineExtensionVector046Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector046_blocker_rows]
  decide

def sevenNineExtensionVector046Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 7}, {2, 4, 7}, {1, 6, 7}, {1, 5, 7}, {0, 3, 6}, {0, 3, 5}, {0, 2, 6}, {0, 2, 5}]

theorem sevenNineExtensionVector046_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector046
        sevenNineExtensionVector046Selected0 =
      sevenNineExtensionVector046Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector046_blocker_rows]
  decide

def sevenNineExtensionVector046Eligible0 :
    List MiddleFourModelPoint :=
  [1, 2, 3, 4, 5, 6]

def sevenNineExtensionVector046BaseBlocker0 :
    G413.Hypergraph MiddleFourModelPoint :=
  ([{0, 7}, {0, 1, 4}, {1, 2, 3}, {2, 3, 7}, {4, 5, 6}, {5, 6, 7}, {2, 3, 5, 6}]).toFinset

theorem sevenNineExtensionVector046_eligible0 :
    middleFourModelEligibleOldPointList sevenNineExtensionVector046
        sevenNineExtensionVector046Base0 =
      sevenNineExtensionVector046Eligible0 := by
  decide

theorem sevenNineExtensionVector046_base_blocker0 :
    fastBlocker sevenNineExtensionVector046Base0 =
      sevenNineExtensionVector046BaseBlocker0 := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
