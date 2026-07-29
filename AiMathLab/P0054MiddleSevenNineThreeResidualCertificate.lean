import AiMathLab.P0054MiddleSevenNineThreeResidualChunk0
import AiMathLab.P0054MiddleSevenNineThreeResidualChunk1
import AiMathLab.P0054MiddleSevenNineThreeResidualChunk2
import AiMathLab.P0054MiddleSevenNineThreeResidualChunk3
import AiMathLab.P0054MiddleSevenNineThreeResidualChunk4
import AiMathLab.P0054MiddleSevenNineThreeResidualChunk5

namespace AiMathLab.P0054.MiddleSevenNineThreeResidualFinite

theorem three_residual_marginal_certificate_check :
    threeResidualMarginalCertificateCheck = true := by
  unfold threeResidualMarginalCertificateCheck
  rw [List.all_eq_true]
  intro p hp
  have hpUpper : p < 6 := List.mem_range.mp hp
  interval_cases p <;>
    simp only [three_residual_marginal_chunk_0, three_residual_marginal_chunk_1, three_residual_marginal_chunk_2, three_residual_marginal_chunk_3, three_residual_marginal_chunk_4, three_residual_marginal_chunk_5]

end AiMathLab.P0054.MiddleSevenNineThreeResidualFinite

