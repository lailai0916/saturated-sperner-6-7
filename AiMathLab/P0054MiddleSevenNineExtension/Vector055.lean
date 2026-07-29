import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector053

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector055 : List Nat :=
  [0, 0, 2, 0, 0, 2, 0, 1, 1, 0, 0, 1, 0, 0]

theorem sevenNineExtensionVector055_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 55 [] =
      sevenNineExtensionVector055 := by
  decide

def sevenNineExtensionVector055BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5}, {2, 5}, {1, 6}, {1, 3, 4}, {1, 2, 4}, {0, 6}, {0, 3, 4}, {0, 2, 4}]

def sevenNineExtensionVector055Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector055Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector055Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector055_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector055 =
      sevenNineExtensionVector055BlockerRows := by
  decide

theorem sevenNineExtensionVector055_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector055 =
      sevenNineExtensionVector055Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector055_blocker_rows]
  decide

def sevenNineExtensionVector055Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {2, 5, 7}, {1, 6, 7}, {1, 3, 4}, {1, 2, 4}, {0, 6, 7}, {0, 3, 4}, {0, 2, 4}]

theorem sevenNineExtensionVector055_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector055
        sevenNineExtensionVector055Selected0 =
      sevenNineExtensionVector055Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector055_blocker_rows]
  decide

def sevenNineExtensionVector055Eligible0 :
    List MiddleFourModelPoint :=
  [0, 1, 2, 3, 5, 6]

def sevenNineExtensionVector055BaseBlocker0 :
    G413.Hypergraph MiddleFourModelPoint :=
  ([{4, 7}, {0, 1, 5}, {0, 1, 7}, {2, 3, 6}, {2, 3, 7}, {4, 5, 6}, {0, 1, 2, 3}]).toFinset

theorem sevenNineExtensionVector055_eligible0 :
    middleFourModelEligibleOldPointList sevenNineExtensionVector055
        sevenNineExtensionVector055Base0 =
      sevenNineExtensionVector055Eligible0 := by
  decide

theorem sevenNineExtensionVector055_base_blocker0 :
    fastBlocker sevenNineExtensionVector055Base0 =
      sevenNineExtensionVector055BaseBlocker0 := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
