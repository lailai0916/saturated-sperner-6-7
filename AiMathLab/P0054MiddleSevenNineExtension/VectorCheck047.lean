import AiMathLab.P0054MiddleSevenNineExtension.Vector047
import AiMathLab.P0054MiddleSevenNineExtension.Selection047
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck045

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector047_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector047 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector047_selections]
  unfold sevenNineExtensionVector047Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector047_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
