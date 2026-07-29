import AiMathLab.P0054MiddleSevenNineExtension.Vector078
import AiMathLab.P0054MiddleSevenNineExtension.Selection078
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck076

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector078_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector078 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector078_selections]
  unfold sevenNineExtensionVector078Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector078_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
