import AiMathLab.P0054FanoAdjacentEightFiveFiniteCore

namespace AiMathLab.P0054.FanoAdjacentEightFiveFinite

-- Kernel reduction checks nine independent blocks of nine labelled Fano selections.
set_option Elab.async false in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem fanoEightFive_chunk_20_subchunk_0_check :
    fanoEightFiveCoreSubchunkCheck 20 0 = true := by
  decide

set_option Elab.async false in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem fanoEightFive_chunk_20_subchunk_1_check :
    fanoEightFiveCoreSubchunkCheck 20 1 = true := by
  decide

set_option Elab.async false in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem fanoEightFive_chunk_20_subchunk_2_check :
    fanoEightFiveCoreSubchunkCheck 20 2 = true := by
  decide

set_option Elab.async false in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem fanoEightFive_chunk_20_subchunk_3_check :
    fanoEightFiveCoreSubchunkCheck 20 3 = true := by
  decide

set_option Elab.async false in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem fanoEightFive_chunk_20_subchunk_4_check :
    fanoEightFiveCoreSubchunkCheck 20 4 = true := by
  decide

set_option Elab.async false in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem fanoEightFive_chunk_20_subchunk_5_check :
    fanoEightFiveCoreSubchunkCheck 20 5 = true := by
  decide

set_option Elab.async false in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem fanoEightFive_chunk_20_subchunk_6_check :
    fanoEightFiveCoreSubchunkCheck 20 6 = true := by
  decide

set_option Elab.async false in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem fanoEightFive_chunk_20_subchunk_7_check :
    fanoEightFiveCoreSubchunkCheck 20 7 = true := by
  decide

set_option Elab.async false in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem fanoEightFive_chunk_20_subchunk_8_check :
    fanoEightFiveCoreSubchunkCheck 20 8 = true := by
  decide

theorem fanoEightFive_chunk_20_check :
    fanoEightFiveCoreChunkCheck 20 = true := by
  exact fanoEightFiveCoreChunkCheck_of_subchunks 20
    fanoEightFive_chunk_20_subchunk_0_check
    fanoEightFive_chunk_20_subchunk_1_check
    fanoEightFive_chunk_20_subchunk_2_check
    fanoEightFive_chunk_20_subchunk_3_check
    fanoEightFive_chunk_20_subchunk_4_check
    fanoEightFive_chunk_20_subchunk_5_check
    fanoEightFive_chunk_20_subchunk_6_check
    fanoEightFive_chunk_20_subchunk_7_check
    fanoEightFive_chunk_20_subchunk_8_check

end AiMathLab.P0054.FanoAdjacentEightFiveFinite
