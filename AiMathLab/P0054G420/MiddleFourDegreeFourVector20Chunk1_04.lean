import AiMathLab.P0054G420.MiddleFourDegreeFourVector20

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector20Chunk1_04 :
    List (List MiddleFourModelPoint) :=
  [[1], [1, 5], [1, 4], [1, 4, 5]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector20_chunk1_04_check :
    middleFourModelRawChunkCheck middleFourDegreeFourVector20
        middleFourDegreeFourVector20Base1
        middleFourDegreeFourVector20Chunk1_04 = true := by
  decide

end AiMathLab.P0054.G420
