import AiMathLab.P0054MiddleSevenNineExtension.Vector118
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck116

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector118_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector118 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector118_selections]
  unfold sevenNineExtensionVector118Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector118_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
