import AiMathLab.P0054MiddleSevenNineExtension.Vector091
import AiMathLab.P0054MiddleSevenNineExtension.Selection091
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck089

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector091_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector091 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector091_selections]
  unfold sevenNineExtensionVector091Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector091_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
