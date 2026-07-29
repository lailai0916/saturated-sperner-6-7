import AiMathLab.P0054MiddleSevenNineExtension.Vector031
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck029

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector031_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector031 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector031_selections]
  unfold sevenNineExtensionVector031Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector031_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
