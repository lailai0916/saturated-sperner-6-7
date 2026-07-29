import AiMathLab.P0054MiddleSevenNineExtension.Vector042
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck040

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector042_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector042 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector042_selections]
  unfold sevenNineExtensionVector042Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector042_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
