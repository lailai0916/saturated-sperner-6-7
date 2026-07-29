import AiMathLab.P0054MiddleSevenNineExtension.Vector132
import AiMathLab.P0054MiddleSevenNineExtension.Selection132
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck130

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector132_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector132 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector132_selections]
  unfold sevenNineExtensionVector132Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector132_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
