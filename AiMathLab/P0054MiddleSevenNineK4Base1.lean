import AiMathLab.P0054MiddleSevenNineK4Chunk1_08
import AiMathLab.P0054MiddleSevenNineK4BaseCore

namespace AiMathLab.P0054.MiddleSevenNineK4Finite

theorem sevenNineK4_base_1_check :
    sevenNineK4BaseCheck (sevenNineK4Bases.getD 1 []) = true :=
  sevenNineK4BaseCheck_1_of_chunk_checks
    sevenNineK4_chunk_1_00_check
    sevenNineK4_chunk_1_01_check
    sevenNineK4_chunk_1_02_check
    sevenNineK4_chunk_1_03_check
    sevenNineK4_chunk_1_04_check
    sevenNineK4_chunk_1_05_check
    sevenNineK4_chunk_1_06_check
    sevenNineK4_chunk_1_07_check
    sevenNineK4_chunk_1_08_check

end AiMathLab.P0054.MiddleSevenNineK4Finite
