import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector118

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector120 : List Nat :=
  [1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1]

theorem sevenNineExtensionVector120_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 120 [] =
      sevenNineExtensionVector120 := by
  decide

def sevenNineExtensionVector120BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{5, 6}, {3, 5}, {2, 6}, {2, 3, 4}, {1, 2, 5}, {1, 2, 4}, {0, 6}, {0, 3, 4}]

def sevenNineExtensionVector120Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector120Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector120Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector120_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector120 =
      sevenNineExtensionVector120BlockerRows := by
  decide

theorem sevenNineExtensionVector120_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector120 =
      sevenNineExtensionVector120Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector120_blocker_rows]
  decide

def sevenNineExtensionVector120Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{5, 6, 7}, {3, 5, 7}, {2, 6, 7}, {2, 3, 4}, {1, 2, 5}, {1, 2, 4}, {0, 6, 7}, {0, 3, 4}]

theorem sevenNineExtensionVector120_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector120
        sevenNineExtensionVector120Selected0 =
      sevenNineExtensionVector120Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector120_blocker_rows]
  decide

def sevenNineExtensionVector120Eligible0 :
    List MiddleFourModelPoint :=
  [0, 1, 3, 4, 5, 6]

def sevenNineExtensionVector120BaseBlocker0 :
    G413.Hypergraph MiddleFourModelPoint :=
  ([{0, 2, 5}, {0, 2, 7}, {1, 3, 6}, {1, 3, 7}, {1, 4, 7}, {2, 3, 6}, {2, 3, 7}, {2, 4, 7}, {4, 5, 6}, {4, 5, 7}]).toFinset

theorem sevenNineExtensionVector120_eligible0 :
    middleFourModelEligibleOldPointList sevenNineExtensionVector120
        sevenNineExtensionVector120Base0 =
      sevenNineExtensionVector120Eligible0 := by
  decide

theorem sevenNineExtensionVector120_base_blocker0 :
    fastBlocker sevenNineExtensionVector120Base0 =
      sevenNineExtensionVector120BaseBlocker0 := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
