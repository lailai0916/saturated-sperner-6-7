import AiMathLab.P0054MiddleSevenNineExtension.Vector032
import AiMathLab.P0054MiddleSevenNineExtension.Selection032
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck030

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector032_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector032 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector032_selections]
  unfold sevenNineExtensionVector032Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector032_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
