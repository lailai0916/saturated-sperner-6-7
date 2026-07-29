import AiMathLab.P0054MiddleSevenNineExtension.Vector021
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck019

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector021_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector021 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector021_selections]
  unfold sevenNineExtensionVector021Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector021_selection0_check]
  rw [sevenNineExtensionVector021_selection1_check]
  rw [sevenNineExtensionVector021_selection2_check]
  rw [sevenNineExtensionVector021_selection3_check]
  rw [sevenNineExtensionVector021_selection4_check]
  rw [sevenNineExtensionVector021_selection5_check]
  rw [sevenNineExtensionVector021_selection6_check]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
