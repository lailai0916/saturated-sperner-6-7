import AiMathLab.P0054MiddleSevenNineExtension.Vector084
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck082

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector084_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector084 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector084_selections]
  unfold sevenNineExtensionVector084Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector084_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
