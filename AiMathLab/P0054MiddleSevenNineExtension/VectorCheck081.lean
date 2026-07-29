import AiMathLab.P0054MiddleSevenNineExtension.Vector081
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck079

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector081_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector081 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector081_selections]
  unfold sevenNineExtensionVector081Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector081_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
