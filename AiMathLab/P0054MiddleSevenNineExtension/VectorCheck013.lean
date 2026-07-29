import AiMathLab.P0054MiddleSevenNineExtension.Vector013
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck011

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector013_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector013 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector013_selections]
  unfold sevenNineExtensionVector013Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector013_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
