import AiMathLab.P0054G420.MiddleFourDegreeFourVector20

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector20Chunk0_08 :
    List (List MiddleFourModelPoint) :=
  [[0], [0, 6], [0, 5], [0, 5, 6], [0, 4], [0, 4, 6], [0, 4, 5], [0, 4, 5, 6]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector20_chunk0_08_check :
    middleFourModelRawChunkCheck middleFourDegreeFourVector20
        middleFourDegreeFourVector20Base0
        middleFourDegreeFourVector20Chunk0_08 = true := by
  decide

end AiMathLab.P0054.G420
