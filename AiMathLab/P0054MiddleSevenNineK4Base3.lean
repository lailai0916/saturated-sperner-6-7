import AiMathLab.P0054MiddleSevenNineK4Chunk3_08
import AiMathLab.P0054MiddleSevenNineK4BaseCore

namespace AiMathLab.P0054.MiddleSevenNineK4Finite

theorem sevenNineK4_base_3_check :
    sevenNineK4BaseCheck (sevenNineK4Bases.getD 3 []) = true :=
  sevenNineK4BaseCheck_3_of_chunk_checks
    sevenNineK4_chunk_3_00_check
    sevenNineK4_chunk_3_01_check
    sevenNineK4_chunk_3_02_check
    sevenNineK4_chunk_3_03_check
    sevenNineK4_chunk_3_04_check
    sevenNineK4_chunk_3_05_check
    sevenNineK4_chunk_3_06_check
    sevenNineK4_chunk_3_07_check
    sevenNineK4_chunk_3_08_check

end AiMathLab.P0054.MiddleSevenNineK4Finite
