import AiMathLab.P0054G420.MiddleFourDegreeFourVector20

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector20Chunk3_10 :
    List (List MiddleFourModelPoint) :=
  [[0, 2], [0, 2, 5], [0, 2, 4], [0, 2, 4, 5]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector20_chunk3_10_check :
    middleFourModelRawChunkCheck middleFourDegreeFourVector20
        middleFourDegreeFourVector20Base3
        middleFourDegreeFourVector20Chunk3_10 = true := by
  decide

end AiMathLab.P0054.G420
