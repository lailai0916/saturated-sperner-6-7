import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector085

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector087 : List Nat :=
  [0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0]

theorem sevenNineExtensionVector087_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 87 [] =
      sevenNineExtensionVector087 := by
  decide

def sevenNineExtensionVector087BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 5}, {2, 5}, {2, 4}, {2, 3}, {1, 3, 4}, {0, 5}, {0, 1, 4}, {0, 1, 3}]

def sevenNineExtensionVector087Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector087Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector087Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector087_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector087 =
      sevenNineExtensionVector087BlockerRows := by
  decide

theorem sevenNineExtensionVector087_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector087 =
      sevenNineExtensionVector087Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector087_blocker_rows]
  decide

def sevenNineExtensionVector087Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 5}, {2, 5, 6}, {2, 4, 6}, {2, 3, 6}, {1, 3, 4}, {0, 5, 6}, {0, 1, 4}, {0, 1, 3}]

theorem sevenNineExtensionVector087_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector087
        sevenNineExtensionVector087Selected0 =
      sevenNineExtensionVector087Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector087_blocker_rows]
  decide

def sevenNineExtensionVector087Eligible0 :
    List MiddleFourModelPoint :=
  [0, 1, 2, 5]

def sevenNineExtensionVector087BaseBlocker0 :
    G413.Hypergraph MiddleFourModelPoint :=
  ([{0, 2, 3}, {0, 2, 4}, {0, 3, 6}, {0, 4, 6}, {1, 2, 5}, {1, 3, 6}, {1, 4, 6}, {1, 5, 6}, {3, 4, 5}, {3, 4, 6}]).toFinset

theorem sevenNineExtensionVector087_eligible0 :
    middleFourModelEligibleOldPointList sevenNineExtensionVector087
        sevenNineExtensionVector087Base0 =
      sevenNineExtensionVector087Eligible0 := by
  decide

theorem sevenNineExtensionVector087_base_blocker0 :
    fastBlocker sevenNineExtensionVector087Base0 =
      sevenNineExtensionVector087BaseBlocker0 := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
