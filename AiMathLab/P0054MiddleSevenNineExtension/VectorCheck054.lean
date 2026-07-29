import AiMathLab.P0054MiddleSevenNineExtension.Vector054
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck052

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector054_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector054 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector054_selections]
  unfold sevenNineExtensionVector054Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector054_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
