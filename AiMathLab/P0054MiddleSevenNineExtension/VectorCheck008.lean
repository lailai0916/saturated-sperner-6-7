import AiMathLab.P0054MiddleSevenNineExtension.Vector008
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck006

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector008_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector008 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector008_selections]
  unfold sevenNineExtensionVector008Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector008_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
