import AiMathLab.P0054FanoAdjacentEightFiveFiniteCore

namespace AiMathLab.P0054.FanoAdjacentEightFiveFinite

-- Kernel reduction checks nine independent blocks of nine labelled Fano selections.
set_option Elab.async false in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem fanoEightFive_chunk_19_subchunk_0_check :
    fanoEightFiveCoreSubchunkCheck 19 0 = true := by
  decide

set_option Elab.async false in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem fanoEightFive_chunk_19_subchunk_1_check :
    fanoEightFiveCoreSubchunkCheck 19 1 = true := by
  decide

set_option Elab.async false in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem fanoEightFive_chunk_19_subchunk_2_check :
    fanoEightFiveCoreSubchunkCheck 19 2 = true := by
  decide

set_option Elab.async false in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem fanoEightFive_chunk_19_subchunk_3_check :
    fanoEightFiveCoreSubchunkCheck 19 3 = true := by
  decide

set_option Elab.async false in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem fanoEightFive_chunk_19_subchunk_4_check :
    fanoEightFiveCoreSubchunkCheck 19 4 = true := by
  decide

set_option Elab.async false in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem fanoEightFive_chunk_19_subchunk_5_check :
    fanoEightFiveCoreSubchunkCheck 19 5 = true := by
  decide

set_option Elab.async false in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem fanoEightFive_chunk_19_subchunk_6_check :
    fanoEightFiveCoreSubchunkCheck 19 6 = true := by
  decide

set_option Elab.async false in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem fanoEightFive_chunk_19_subchunk_7_check :
    fanoEightFiveCoreSubchunkCheck 19 7 = true := by
  decide

set_option Elab.async false in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem fanoEightFive_chunk_19_subchunk_8_check :
    fanoEightFiveCoreSubchunkCheck 19 8 = true := by
  decide

theorem fanoEightFive_chunk_19_check :
    fanoEightFiveCoreChunkCheck 19 = true := by
  exact fanoEightFiveCoreChunkCheck_of_subchunks 19
    fanoEightFive_chunk_19_subchunk_0_check
    fanoEightFive_chunk_19_subchunk_1_check
    fanoEightFive_chunk_19_subchunk_2_check
    fanoEightFive_chunk_19_subchunk_3_check
    fanoEightFive_chunk_19_subchunk_4_check
    fanoEightFive_chunk_19_subchunk_5_check
    fanoEightFive_chunk_19_subchunk_6_check
    fanoEightFive_chunk_19_subchunk_7_check
    fanoEightFive_chunk_19_subchunk_8_check

end AiMathLab.P0054.FanoAdjacentEightFiveFinite
