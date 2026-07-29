import AiMathLab.P0054G420.MiddleFourDegreeFourVector20

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector20Chunk4_11 :
    List (List MiddleFourModelPoint) :=
  [[0, 2, 3], [0, 2, 3, 5], [0, 2, 3, 4], [0, 2, 3, 4, 5]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector20_chunk4_11_check :
    middleFourModelRawChunkCheck middleFourDegreeFourVector20
        middleFourDegreeFourVector20Base4
        middleFourDegreeFourVector20Chunk4_11 = true := by
  decide

end AiMathLab.P0054.G420
