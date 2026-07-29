import AiMathLab.P0054MiddleSevenNineExtension.Vector126
import AiMathLab.P0054MiddleSevenNineExtension.Selection126
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck124

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector126_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector126 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector126_selections]
  unfold sevenNineExtensionVector126Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector126_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
