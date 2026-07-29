import AiMathLab.P0054MiddleSevenNineK4Base0
import AiMathLab.P0054MiddleSevenNineK4Base1
import AiMathLab.P0054MiddleSevenNineK4Base2
import AiMathLab.P0054MiddleSevenNineK4Base3
import AiMathLab.P0054MiddleSevenNineK4Base4

namespace AiMathLab.P0054.MiddleSevenNineK4Finite

theorem sevenNineK4ExtensionCheck_true :
    sevenNineK4ExtensionCheck = true := by
  unfold sevenNineK4ExtensionCheck
  rw [List.all_eq_true]
  intro base hBase
  simp only [sevenNineK4Bases, List.mem_cons, List.not_mem_nil,
    or_false] at hBase
  rcases hBase with hBase | hBase | hBase | hBase | hBase
  · subst base
    simpa [sevenNineK4Bases] using sevenNineK4_base_0_check
  · subst base
    simpa [sevenNineK4Bases] using sevenNineK4_base_1_check
  · subst base
    simpa [sevenNineK4Bases] using sevenNineK4_base_2_check
  · subst base
    simpa [sevenNineK4Bases] using sevenNineK4_base_3_check
  · subst base
    simpa [sevenNineK4Bases] using sevenNineK4_base_4_check

end AiMathLab.P0054.MiddleSevenNineK4Finite
