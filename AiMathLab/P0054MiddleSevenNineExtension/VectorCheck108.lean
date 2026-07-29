import AiMathLab.P0054MiddleSevenNineExtension.Vector108
import AiMathLab.P0054MiddleSevenNineExtension.Selection108
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck106

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector108_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector108 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector108_selections]
  unfold sevenNineExtensionVector108Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector108_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
