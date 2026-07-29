import AiMathLab.P0054MiddleSevenNineK4Chunk2_08
import AiMathLab.P0054MiddleSevenNineK4BaseCore

namespace AiMathLab.P0054.MiddleSevenNineK4Finite

theorem sevenNineK4_base_2_check :
    sevenNineK4BaseCheck (sevenNineK4Bases.getD 2 []) = true :=
  sevenNineK4BaseCheck_2_of_chunk_checks
    sevenNineK4_chunk_2_00_check
    sevenNineK4_chunk_2_01_check
    sevenNineK4_chunk_2_02_check
    sevenNineK4_chunk_2_03_check
    sevenNineK4_chunk_2_04_check
    sevenNineK4_chunk_2_05_check
    sevenNineK4_chunk_2_06_check
    sevenNineK4_chunk_2_07_check
    sevenNineK4_chunk_2_08_check

end AiMathLab.P0054.MiddleSevenNineK4Finite
