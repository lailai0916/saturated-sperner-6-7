import AiMathLab.P0054MiddleSevenNineExtension.Vector028
import AiMathLab.P0054MiddleSevenNineExtension.Selection028
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck026

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector028_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector028 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector028_selections]
  unfold sevenNineExtensionVector028Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector028_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
