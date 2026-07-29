import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector110

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector112 : List Nat :=
  [1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0]

theorem sevenNineExtensionVector112_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 112 [] =
      sevenNineExtensionVector112 := by
  decide

def sevenNineExtensionVector112BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6}, {2, 6}, {2, 5}, {2, 3, 4}, {1, 6}, {0, 3, 5}, {0, 3, 4}, {0, 1, 5}]

def sevenNineExtensionVector112Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector112Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector112Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector112_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector112 =
      sevenNineExtensionVector112BlockerRows := by
  decide

theorem sevenNineExtensionVector112_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector112 =
      sevenNineExtensionVector112Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector112_blocker_rows]
  decide

def sevenNineExtensionVector112Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6, 7}, {2, 6, 7}, {2, 5, 7}, {2, 3, 4}, {1, 6, 7}, {0, 3, 5}, {0, 3, 4}, {0, 1, 5}]

theorem sevenNineExtensionVector112_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector112
        sevenNineExtensionVector112Selected0 =
      sevenNineExtensionVector112Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector112_blocker_rows]
  decide

def sevenNineExtensionVector112Eligible0 :
    List MiddleFourModelPoint :=
  [0, 1, 2, 4, 5, 6]

def sevenNineExtensionVector112BaseBlocker0 :
    G413.Hypergraph MiddleFourModelPoint :=
  ([{0, 2, 6}, {0, 2, 7}, {0, 3, 7}, {0, 4, 7}, {1, 2, 3}, {1, 3, 7}, {3, 5, 6}, {3, 5, 7}, {4, 5, 6}, {4, 5, 7}]).toFinset

theorem sevenNineExtensionVector112_eligible0 :
    middleFourModelEligibleOldPointList sevenNineExtensionVector112
        sevenNineExtensionVector112Base0 =
      sevenNineExtensionVector112Eligible0 := by
  decide

theorem sevenNineExtensionVector112_base_blocker0 :
    fastBlocker sevenNineExtensionVector112Base0 =
      sevenNineExtensionVector112BaseBlocker0 := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
