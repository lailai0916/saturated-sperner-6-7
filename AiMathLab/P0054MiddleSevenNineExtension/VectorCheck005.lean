import AiMathLab.P0054MiddleSevenNineExtension.Vector005
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck003

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector005_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector005 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector005_selections]
  unfold sevenNineExtensionVector005Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector005_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
