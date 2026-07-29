import AiMathLab.P0054MiddleSevenNineExtension.Vector055
import AiMathLab.P0054MiddleSevenNineExtension.Selection055
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck053

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector055_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector055 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector055_selections]
  unfold sevenNineExtensionVector055Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector055_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
