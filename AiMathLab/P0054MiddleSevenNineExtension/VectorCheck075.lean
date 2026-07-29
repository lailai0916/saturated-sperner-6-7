import AiMathLab.P0054MiddleSevenNineExtension.Vector075
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck073

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector075_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector075 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector075_selections]
  unfold sevenNineExtensionVector075Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector075_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
