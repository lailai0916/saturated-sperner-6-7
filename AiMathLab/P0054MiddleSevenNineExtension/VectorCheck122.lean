import AiMathLab.P0054MiddleSevenNineExtension.Vector122
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck120

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector122_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector122 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector122_selections]
  unfold sevenNineExtensionVector122Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector122_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
