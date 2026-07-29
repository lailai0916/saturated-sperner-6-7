import AiMathLab.P0054MiddleSevenNineExtension.Vector012
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck010

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector012_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector012 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector012_selections]
  unfold sevenNineExtensionVector012Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector012_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
