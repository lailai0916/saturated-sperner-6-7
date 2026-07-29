import AiMathLab.P0054MiddleSevenNineExtension.Vector067
import AiMathLab.P0054MiddleSevenNineExtension.Selection067
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck065

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector067_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector067 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector067_selections]
  unfold sevenNineExtensionVector067Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector067_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
