import AiMathLab.P0054MiddleSevenNineExtension.Vector027
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck025

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector027_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector027 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector027_selections]
  unfold sevenNineExtensionVector027Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector027_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
