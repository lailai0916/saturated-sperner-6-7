import AiMathLab.P0054MiddleSevenNineExtension.Vector104
import AiMathLab.P0054MiddleSevenNineExtension.Selection104
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck102

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector104_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector104 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector104_selections]
  unfold sevenNineExtensionVector104Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector104_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
