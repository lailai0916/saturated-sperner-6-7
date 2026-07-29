import AiMathLab.P0054G420.MiddleFourDegreeFourVector20

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector20Chunk0_09 :
    List (List MiddleFourModelPoint) :=
  [[0, 3], [0, 3, 6], [0, 3, 5], [0, 3, 5, 6], [0, 3, 4], [0, 3, 4, 6], [0, 3, 4, 5], [0, 3, 4, 5, 6]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector20_chunk0_09_check :
    middleFourModelRawChunkCheck middleFourDegreeFourVector20
        middleFourDegreeFourVector20Base0
        middleFourDegreeFourVector20Chunk0_09 = true := by
  decide

end AiMathLab.P0054.G420
