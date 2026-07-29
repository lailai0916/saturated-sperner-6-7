import AiMathLab.P0054MiddleSevenNineExtension.Vector035
import AiMathLab.P0054MiddleSevenNineExtension.Selection035
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck033

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector035_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector035 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector035_selections]
  unfold sevenNineExtensionVector035Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector035_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
