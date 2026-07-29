import AiMathLab.P0054MiddleSevenNineExtension.Vector115
import AiMathLab.P0054MiddleSevenNineExtension.Selection115
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck113

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector115_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector115 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector115_selections]
  unfold sevenNineExtensionVector115Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector115_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
