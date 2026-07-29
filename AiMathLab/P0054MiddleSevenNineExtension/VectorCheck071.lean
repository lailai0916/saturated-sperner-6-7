import AiMathLab.P0054MiddleSevenNineExtension.Vector071
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck069

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector071_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector071 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector071_selections]
  unfold sevenNineExtensionVector071Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector071_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
