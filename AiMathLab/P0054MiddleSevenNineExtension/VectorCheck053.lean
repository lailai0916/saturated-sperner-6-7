import AiMathLab.P0054MiddleSevenNineExtension.Vector053
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck051

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector053_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector053 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector053_selections]
  unfold sevenNineExtensionVector053Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector053_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
