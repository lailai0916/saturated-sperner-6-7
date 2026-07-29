import AiMathLab.P0054MiddleSevenNineExtension.Vector098
import AiMathLab.P0054MiddleSevenNineExtension.Selection098
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck096

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector098_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector098 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector098_selections]
  unfold sevenNineExtensionVector098Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector098_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
