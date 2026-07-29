import AiMathLab.P0054MiddleSevenNineExtension.Vector090
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck088

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector090_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector090 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector090_selections]
  unfold sevenNineExtensionVector090Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector090_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
