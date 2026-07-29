import AiMathLab.P0054MiddleSevenNineExtension.Vector058
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck056

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector058_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector058 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector058_selections]
  unfold sevenNineExtensionVector058Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector058_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
