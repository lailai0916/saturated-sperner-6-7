import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector086

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector088 : List Nat :=
  [0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0]

theorem sevenNineExtensionVector088_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 88 [] =
      sevenNineExtensionVector088 := by
  decide

def sevenNineExtensionVector088BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 5}, {2, 5}, {2, 4}, {2, 3}, {1, 4}, {0, 3, 5}, {0, 1, 5}, {0, 1, 3}]

def sevenNineExtensionVector088Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector088Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector088Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector088_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector088 =
      sevenNineExtensionVector088BlockerRows := by
  decide

theorem sevenNineExtensionVector088_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector088 =
      sevenNineExtensionVector088Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector088_blocker_rows]
  decide

def sevenNineExtensionVector088Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 5}, {2, 5, 6}, {2, 4, 6}, {2, 3, 6}, {1, 4, 6}, {0, 3, 5}, {0, 1, 5}, {0, 1, 3}]

theorem sevenNineExtensionVector088_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector088
        sevenNineExtensionVector088Selected0 =
      sevenNineExtensionVector088Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector088_blocker_rows]
  decide

def sevenNineExtensionVector088Eligible0 :
    List MiddleFourModelPoint :=
  [0, 1, 2, 4]

def sevenNineExtensionVector088BaseBlocker0 :
    G413.Hypergraph MiddleFourModelPoint :=
  ([{0, 2, 4}, {0, 3, 6}, {0, 4, 6}, {0, 5, 6}, {1, 2, 3}, {1, 2, 5}, {1, 3, 6}, {1, 5, 6}, {3, 4, 5}, {3, 5, 6}]).toFinset

theorem sevenNineExtensionVector088_eligible0 :
    middleFourModelEligibleOldPointList sevenNineExtensionVector088
        sevenNineExtensionVector088Base0 =
      sevenNineExtensionVector088Eligible0 := by
  decide

theorem sevenNineExtensionVector088_base_blocker0 :
    fastBlocker sevenNineExtensionVector088Base0 =
      sevenNineExtensionVector088BaseBlocker0 := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
