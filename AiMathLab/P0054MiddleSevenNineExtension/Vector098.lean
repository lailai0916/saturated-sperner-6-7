import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector096

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector098 : List Nat :=
  [1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0]

theorem sevenNineExtensionVector098_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 98 [] =
      sevenNineExtensionVector098 := by
  decide

def sevenNineExtensionVector098BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{5, 6}, {3, 5}, {3, 4}, {2, 5}, {1, 3, 6}, {0, 4, 6}, {0, 2, 4}, {0, 1, 6}]

def sevenNineExtensionVector098Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector098Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector098Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector098_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector098 =
      sevenNineExtensionVector098BlockerRows := by
  decide

theorem sevenNineExtensionVector098_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector098 =
      sevenNineExtensionVector098Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector098_blocker_rows]
  decide

def sevenNineExtensionVector098Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{5, 6, 7}, {3, 5, 7}, {3, 4, 7}, {2, 5, 7}, {1, 3, 6}, {0, 4, 6}, {0, 2, 4}, {0, 1, 6}]

theorem sevenNineExtensionVector098_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector098
        sevenNineExtensionVector098Selected0 =
      sevenNineExtensionVector098Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector098_blocker_rows]
  decide

def sevenNineExtensionVector098Eligible0 :
    List MiddleFourModelPoint :=
  [0, 1, 2, 3, 4, 5]

def sevenNineExtensionVector098BaseBlocker0 :
    G413.Hypergraph MiddleFourModelPoint :=
  ([{0, 1, 7}, {0, 3, 5}, {0, 3, 7}, {0, 6, 7}, {1, 4, 5}, {1, 4, 7}, {2, 3, 6}, {2, 6, 7}, {4, 5, 6}, {4, 6, 7}]).toFinset

theorem sevenNineExtensionVector098_eligible0 :
    middleFourModelEligibleOldPointList sevenNineExtensionVector098
        sevenNineExtensionVector098Base0 =
      sevenNineExtensionVector098Eligible0 := by
  decide

theorem sevenNineExtensionVector098_base_blocker0 :
    fastBlocker sevenNineExtensionVector098Base0 =
      sevenNineExtensionVector098BaseBlocker0 := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
