import AiMathLab.P0054G420.MiddleFourDegreeFourVector20

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector20Chunk4_06 :
    List (List MiddleFourModelPoint) :=
  [[1, 2], [1, 2, 5], [1, 2, 4], [1, 2, 4, 5]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector20_chunk4_06_check :
    middleFourModelRawChunkCheck middleFourDegreeFourVector20
        middleFourDegreeFourVector20Base4
        middleFourDegreeFourVector20Chunk4_06 = true := by
  decide

end AiMathLab.P0054.G420
