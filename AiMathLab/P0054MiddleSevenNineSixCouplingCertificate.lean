import AiMathLab.P0054MiddleSevenNineSixCouplingChunk0_0
import AiMathLab.P0054MiddleSevenNineSixCouplingChunk0_1
import AiMathLab.P0054MiddleSevenNineSixCouplingChunk0_2
import AiMathLab.P0054MiddleSevenNineSixCouplingChunk0_3
import AiMathLab.P0054MiddleSevenNineSixCouplingChunk0_4
import AiMathLab.P0054MiddleSevenNineSixCouplingChunk0_5
import AiMathLab.P0054MiddleSevenNineSixCouplingChunk1_0
import AiMathLab.P0054MiddleSevenNineSixCouplingChunk1_1
import AiMathLab.P0054MiddleSevenNineSixCouplingChunk1_2
import AiMathLab.P0054MiddleSevenNineSixCouplingChunk1_3
import AiMathLab.P0054MiddleSevenNineSixCouplingChunk1_4
import AiMathLab.P0054MiddleSevenNineSixCouplingChunk1_5
import AiMathLab.P0054MiddleSevenNineSixCouplingChunk2_0
import AiMathLab.P0054MiddleSevenNineSixCouplingChunk2_1
import AiMathLab.P0054MiddleSevenNineSixCouplingChunk2_2
import AiMathLab.P0054MiddleSevenNineSixCouplingChunk2_3
import AiMathLab.P0054MiddleSevenNineSixCouplingChunk2_4
import AiMathLab.P0054MiddleSevenNineSixCouplingChunk2_5
import AiMathLab.P0054MiddleSevenNineSixCouplingChunk3_0
import AiMathLab.P0054MiddleSevenNineSixCouplingChunk3_1
import AiMathLab.P0054MiddleSevenNineSixCouplingChunk3_2
import AiMathLab.P0054MiddleSevenNineSixCouplingChunk3_3
import AiMathLab.P0054MiddleSevenNineSixCouplingChunk3_4
import AiMathLab.P0054MiddleSevenNineSixCouplingChunk3_5
import AiMathLab.P0054MiddleSevenNineSixCouplingChunk4_0
import AiMathLab.P0054MiddleSevenNineSixCouplingChunk4_1
import AiMathLab.P0054MiddleSevenNineSixCouplingChunk4_2
import AiMathLab.P0054MiddleSevenNineSixCouplingChunk4_3
import AiMathLab.P0054MiddleSevenNineSixCouplingChunk4_4
import AiMathLab.P0054MiddleSevenNineSixCouplingChunk4_5
import AiMathLab.P0054MiddleSevenNineSixCouplingChunk5_0
import AiMathLab.P0054MiddleSevenNineSixCouplingChunk5_1
import AiMathLab.P0054MiddleSevenNineSixCouplingChunk5_2
import AiMathLab.P0054MiddleSevenNineSixCouplingChunk5_3
import AiMathLab.P0054MiddleSevenNineSixCouplingChunk5_4
import AiMathLab.P0054MiddleSevenNineSixCouplingChunk5_5

namespace AiMathLab.P0054.MiddleSevenNineSixCouplingFinite

theorem six_row_coupling_certificate_check :
    sixRowCouplingCertificateCheck = true := by
  unfold sixRowCouplingCertificateCheck
  rw [List.all_eq_true]
  intro leftIndex hLeftIndex
  rw [List.all_eq_true]
  intro rightIndex hRightIndex
  have hLeft : leftIndex < 6 := List.mem_range.mp hLeftIndex
  have hRight : rightIndex < 6 := List.mem_range.mp hRightIndex
  interval_cases leftIndex <;> interval_cases rightIndex <;>
    simp only [six_row_coupling_chunk_0_0,
      six_row_coupling_chunk_0_1,
      six_row_coupling_chunk_0_2,
      six_row_coupling_chunk_0_3,
      six_row_coupling_chunk_0_4,
      six_row_coupling_chunk_0_5,
      six_row_coupling_chunk_1_0,
      six_row_coupling_chunk_1_1,
      six_row_coupling_chunk_1_2,
      six_row_coupling_chunk_1_3,
      six_row_coupling_chunk_1_4,
      six_row_coupling_chunk_1_5,
      six_row_coupling_chunk_2_0,
      six_row_coupling_chunk_2_1,
      six_row_coupling_chunk_2_2,
      six_row_coupling_chunk_2_3,
      six_row_coupling_chunk_2_4,
      six_row_coupling_chunk_2_5,
      six_row_coupling_chunk_3_0,
      six_row_coupling_chunk_3_1,
      six_row_coupling_chunk_3_2,
      six_row_coupling_chunk_3_3,
      six_row_coupling_chunk_3_4,
      six_row_coupling_chunk_3_5,
      six_row_coupling_chunk_4_0,
      six_row_coupling_chunk_4_1,
      six_row_coupling_chunk_4_2,
      six_row_coupling_chunk_4_3,
      six_row_coupling_chunk_4_4,
      six_row_coupling_chunk_4_5,
      six_row_coupling_chunk_5_0,
      six_row_coupling_chunk_5_1,
      six_row_coupling_chunk_5_2,
      six_row_coupling_chunk_5_3,
      six_row_coupling_chunk_5_4,
      six_row_coupling_chunk_5_5]

end AiMathLab.P0054.MiddleSevenNineSixCouplingFinite

