import AiMathLab.P0054G420.MiddleFourDegreeFourVector20

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector20Chunk2_00 :
    List (List MiddleFourModelPoint) :=
  [[], [5], [4], [4, 5]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector20_chunk2_00_check :
    middleFourModelRawChunkCheck middleFourDegreeFourVector20
        middleFourDegreeFourVector20Base2
        middleFourDegreeFourVector20Chunk2_00 = true := by
  decide

end AiMathLab.P0054.G420
