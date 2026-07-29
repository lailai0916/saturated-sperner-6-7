import AiMathLab.P0054MiddleSevenNineExtension.Vector038
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck036

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector038_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector038 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector038_selections]
  unfold sevenNineExtensionVector038Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector038_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
