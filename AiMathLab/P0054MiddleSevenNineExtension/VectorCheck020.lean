import AiMathLab.P0054MiddleSevenNineExtension.Vector020
import AiMathLab.P0054MiddleSevenNineExtension.Selection020
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck018

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector020_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector020 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector020_selections]
  unfold sevenNineExtensionVector020Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector020_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
