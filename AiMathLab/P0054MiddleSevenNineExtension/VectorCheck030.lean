import AiMathLab.P0054MiddleSevenNineExtension.Vector030
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck028

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector030_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector030 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector030_selections]
  unfold sevenNineExtensionVector030Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector030_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
