import AiMathLab.P0054MiddleSevenNineK4Chunk4_08
import AiMathLab.P0054MiddleSevenNineK4BaseCore

namespace AiMathLab.P0054.MiddleSevenNineK4Finite

theorem sevenNineK4_base_4_check :
    sevenNineK4BaseCheck (sevenNineK4Bases.getD 4 []) = true :=
  sevenNineK4BaseCheck_4_of_chunk_checks
    sevenNineK4_chunk_4_00_check
    sevenNineK4_chunk_4_01_check
    sevenNineK4_chunk_4_02_check
    sevenNineK4_chunk_4_03_check
    sevenNineK4_chunk_4_04_check
    sevenNineK4_chunk_4_05_check
    sevenNineK4_chunk_4_06_check
    sevenNineK4_chunk_4_07_check
    sevenNineK4_chunk_4_08_check

end AiMathLab.P0054.MiddleSevenNineK4Finite
