import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector021

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector023 : List Nat :=
  [0, 0, 0, 0, 2, 2, 0, 1, 1, 1, 0, 0, 0, 0]

theorem sevenNineExtensionVector023_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 23 [] =
      sevenNineExtensionVector023 := by
  decide

def sevenNineExtensionVector023BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5}, {2, 5}, {1, 6}, {1, 3, 4}, {1, 2, 4}, {0, 6}, {0, 3, 4}, {0, 2, 4}]

def sevenNineExtensionVector023Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector023Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector023Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector023_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector023 =
      sevenNineExtensionVector023BlockerRows := by
  decide

theorem sevenNineExtensionVector023_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector023 =
      sevenNineExtensionVector023Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector023_blocker_rows]
  decide

def sevenNineExtensionVector023Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {2, 5, 7}, {1, 6, 7}, {1, 3, 4}, {1, 2, 4}, {0, 6, 7}, {0, 3, 4}, {0, 2, 4}]

theorem sevenNineExtensionVector023_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector023
        sevenNineExtensionVector023Selected0 =
      sevenNineExtensionVector023Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector023_blocker_rows]
  decide

def sevenNineExtensionVector023Eligible0 :
    List MiddleFourModelPoint :=
  [0, 1, 2, 3, 5, 6]

def sevenNineExtensionVector023BaseBlocker0 :
    G413.Hypergraph MiddleFourModelPoint :=
  ([{4, 7}, {0, 1, 5}, {0, 1, 7}, {2, 3, 6}, {2, 3, 7}, {4, 5, 6}, {0, 1, 2, 3}]).toFinset

theorem sevenNineExtensionVector023_eligible0 :
    middleFourModelEligibleOldPointList sevenNineExtensionVector023
        sevenNineExtensionVector023Base0 =
      sevenNineExtensionVector023Eligible0 := by
  decide

theorem sevenNineExtensionVector023_base_blocker0 :
    fastBlocker sevenNineExtensionVector023Base0 =
      sevenNineExtensionVector023BaseBlocker0 := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
