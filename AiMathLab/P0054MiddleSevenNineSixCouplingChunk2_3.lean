import AiMathLab.P0054MiddleSevenNineSixCouplingFiniteCore
import AiMathLab.P0054MiddleSevenNineSixCouplingChunk2_2

namespace AiMathLab.P0054.MiddleSevenNineSixCouplingFinite

set_option maxHeartbeats 0 in
theorem six_row_coupling_chunk_2_3 :
    sixRowCouplingCheck (sixResidualProfile 2)
      (sixResidualProfile 3) = true := by
  decide

end AiMathLab.P0054.MiddleSevenNineSixCouplingFinite
