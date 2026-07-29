import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector012

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector014 : List Nat :=
  [1, 0, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 0, 0]

theorem sevenNineExtensionVector014_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 14 [] =
      sevenNineExtensionVector014 := by
  decide

def sevenNineExtensionVector014BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4}, {2, 4}, {1, 6}, {1, 5}, {0, 3, 6}, {0, 3, 5}, {0, 2, 6}, {0, 2, 5}]

def sevenNineExtensionVector014Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector014Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector014Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector014_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector014 =
      sevenNineExtensionVector014BlockerRows := by
  decide

theorem sevenNineExtensionVector014_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector014 =
      sevenNineExtensionVector014Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector014_blocker_rows]
  decide

def sevenNineExtensionVector014Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 7}, {2, 4, 7}, {1, 6, 7}, {1, 5, 7}, {0, 3, 6}, {0, 3, 5}, {0, 2, 6}, {0, 2, 5}]

theorem sevenNineExtensionVector014_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector014
        sevenNineExtensionVector014Selected0 =
      sevenNineExtensionVector014Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector014_blocker_rows]
  decide

def sevenNineExtensionVector014Eligible0 :
    List MiddleFourModelPoint :=
  [1, 2, 3, 4, 5, 6]

def sevenNineExtensionVector014BaseBlocker0 :
    G413.Hypergraph MiddleFourModelPoint :=
  ([{0, 7}, {0, 1, 4}, {1, 2, 3}, {2, 3, 7}, {4, 5, 6}, {5, 6, 7}, {2, 3, 5, 6}]).toFinset

theorem sevenNineExtensionVector014_eligible0 :
    middleFourModelEligibleOldPointList sevenNineExtensionVector014
        sevenNineExtensionVector014Base0 =
      sevenNineExtensionVector014Eligible0 := by
  decide

theorem sevenNineExtensionVector014_base_blocker0 :
    fastBlocker sevenNineExtensionVector014Base0 =
      sevenNineExtensionVector014BaseBlocker0 := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
