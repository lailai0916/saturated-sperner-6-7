import AiMathLab.P0054MiddleSevenNineExtension.Vector007
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck005

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector007_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector007 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector007_selections]
  unfold sevenNineExtensionVector007Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector007_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
