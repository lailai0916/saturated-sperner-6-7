import AiMathLab.P0054G420.MiddleFourDegreeFourVector20

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector20Chunk3_07 :
    List (List MiddleFourModelPoint) :=
  [[1, 2, 3], [1, 2, 3, 5], [1, 2, 3, 4], [1, 2, 3, 4, 5]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector20_chunk3_07_check :
    middleFourModelRawChunkCheck middleFourDegreeFourVector20
        middleFourDegreeFourVector20Base3
        middleFourDegreeFourVector20Chunk3_07 = true := by
  decide

end AiMathLab.P0054.G420
