import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector119

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector121 : List Nat :=
  [0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1]

theorem sevenNineExtensionVector121_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 121 [] =
      sevenNineExtensionVector121 := by
  decide

def sevenNineExtensionVector121BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 5}, {2, 4}, {1, 5}, {1, 2, 3}, {0, 5}, {0, 2, 3}, {0, 1, 4}, {0, 1, 3}]

def sevenNineExtensionVector121Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector121Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector121Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector121_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector121 =
      sevenNineExtensionVector121BlockerRows := by
  decide

theorem sevenNineExtensionVector121_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector121 =
      sevenNineExtensionVector121Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector121_blocker_rows]
  decide

def sevenNineExtensionVector121Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 5, 6}, {2, 4, 6}, {1, 5, 6}, {1, 2, 3}, {0, 5, 6}, {0, 2, 3}, {0, 1, 4}, {0, 1, 3}]

theorem sevenNineExtensionVector121_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector121
        sevenNineExtensionVector121Selected0 =
      sevenNineExtensionVector121Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector121_blocker_rows]
  decide

def sevenNineExtensionVector121Eligible0 :
    List MiddleFourModelPoint :=
  [2, 3, 4, 5]

def sevenNineExtensionVector121BaseBlocker0 :
    G413.Hypergraph MiddleFourModelPoint :=
  ([{0, 1, 4}, {0, 1, 6}, {0, 2, 5}, {0, 2, 6}, {0, 3, 6}, {1, 2, 5}, {1, 2, 6}, {1, 3, 6}, {3, 4, 5}, {3, 4, 6}]).toFinset

theorem sevenNineExtensionVector121_eligible0 :
    middleFourModelEligibleOldPointList sevenNineExtensionVector121
        sevenNineExtensionVector121Base0 =
      sevenNineExtensionVector121Eligible0 := by
  decide

theorem sevenNineExtensionVector121_base_blocker0 :
    fastBlocker sevenNineExtensionVector121Base0 =
      sevenNineExtensionVector121BaseBlocker0 := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
