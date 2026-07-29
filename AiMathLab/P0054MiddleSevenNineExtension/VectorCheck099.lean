import AiMathLab.P0054MiddleSevenNineExtension.Vector099
import AiMathLab.P0054MiddleSevenNineExtension.Selection099
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck097

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector099_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector099 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector099_selections]
  unfold sevenNineExtensionVector099Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector099_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
