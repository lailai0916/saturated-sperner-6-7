import AiMathLab.P0054FanoAdjacentEightFiveFiniteCore

namespace AiMathLab.P0054.FanoAdjacentEightFiveFinite

-- Kernel reduction checks nine independent blocks of nine labelled Fano selections.
set_option Elab.async false in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem fanoEightFive_chunk_02_subchunk_0_check :
    fanoEightFiveCoreSubchunkCheck 2 0 = true := by
  decide

set_option Elab.async false in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem fanoEightFive_chunk_02_subchunk_1_check :
    fanoEightFiveCoreSubchunkCheck 2 1 = true := by
  decide

set_option Elab.async false in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem fanoEightFive_chunk_02_subchunk_2_check :
    fanoEightFiveCoreSubchunkCheck 2 2 = true := by
  decide

set_option Elab.async false in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem fanoEightFive_chunk_02_subchunk_3_check :
    fanoEightFiveCoreSubchunkCheck 2 3 = true := by
  decide

set_option Elab.async false in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem fanoEightFive_chunk_02_subchunk_4_check :
    fanoEightFiveCoreSubchunkCheck 2 4 = true := by
  decide

set_option Elab.async false in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem fanoEightFive_chunk_02_subchunk_5_check :
    fanoEightFiveCoreSubchunkCheck 2 5 = true := by
  decide

set_option Elab.async false in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem fanoEightFive_chunk_02_subchunk_6_check :
    fanoEightFiveCoreSubchunkCheck 2 6 = true := by
  decide

set_option Elab.async false in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem fanoEightFive_chunk_02_subchunk_7_check :
    fanoEightFiveCoreSubchunkCheck 2 7 = true := by
  decide

set_option Elab.async false in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem fanoEightFive_chunk_02_subchunk_8_check :
    fanoEightFiveCoreSubchunkCheck 2 8 = true := by
  decide

theorem fanoEightFive_chunk_02_check :
    fanoEightFiveCoreChunkCheck 2 = true := by
  exact fanoEightFiveCoreChunkCheck_of_subchunks 2
    fanoEightFive_chunk_02_subchunk_0_check
    fanoEightFive_chunk_02_subchunk_1_check
    fanoEightFive_chunk_02_subchunk_2_check
    fanoEightFive_chunk_02_subchunk_3_check
    fanoEightFive_chunk_02_subchunk_4_check
    fanoEightFive_chunk_02_subchunk_5_check
    fanoEightFive_chunk_02_subchunk_6_check
    fanoEightFive_chunk_02_subchunk_7_check
    fanoEightFive_chunk_02_subchunk_8_check

end AiMathLab.P0054.FanoAdjacentEightFiveFinite
