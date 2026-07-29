import AiMathLab.P0054G420.MiddleFourDegreeFourVector20

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector20Chunk2_05 :
    List (List MiddleFourModelPoint) :=
  [[1, 3], [1, 3, 5], [1, 3, 4], [1, 3, 4, 5]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector20_chunk2_05_check :
    middleFourModelRawChunkCheck middleFourDegreeFourVector20
        middleFourDegreeFourVector20Base2
        middleFourDegreeFourVector20Chunk2_05 = true := by
  decide

end AiMathLab.P0054.G420
