import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk4_00
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk4_01
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk4_02
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk4_03
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk4_04
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk4_05
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk4_06
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk4_07
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk4_08
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk4_09
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk4_10
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk4_11
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk4_12
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk4_13
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk4_14
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk4_15

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector20Chunks4 :
    List (List (List MiddleFourModelPoint)) :=
  [middleFourDegreeFourVector20Chunk4_00, middleFourDegreeFourVector20Chunk4_01, middleFourDegreeFourVector20Chunk4_02, middleFourDegreeFourVector20Chunk4_03, middleFourDegreeFourVector20Chunk4_04, middleFourDegreeFourVector20Chunk4_05, middleFourDegreeFourVector20Chunk4_06, middleFourDegreeFourVector20Chunk4_07, middleFourDegreeFourVector20Chunk4_08, middleFourDegreeFourVector20Chunk4_09, middleFourDegreeFourVector20Chunk4_10, middleFourDegreeFourVector20Chunk4_11, middleFourDegreeFourVector20Chunk4_12, middleFourDegreeFourVector20Chunk4_13, middleFourDegreeFourVector20Chunk4_14, middleFourDegreeFourVector20Chunk4_15]

theorem middleFourDegreeFourVector20_chunks4_flatten :
    middleFourDegreeFourVector20Chunks4.flatMap id =
      middleFourListPowerset middleFourDegreeFourVector20Eligible4 := by
  decide

theorem middleFourDegreeFourVector20_chunks4_check :
    middleFourDegreeFourVector20Chunks4.all
      (middleFourModelRawChunkCheck middleFourDegreeFourVector20
        middleFourDegreeFourVector20Base4) = true := by
  unfold middleFourDegreeFourVector20Chunks4
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourVector20_chunk4_00_check]
  rw [middleFourDegreeFourVector20_chunk4_01_check]
  rw [middleFourDegreeFourVector20_chunk4_02_check]
  rw [middleFourDegreeFourVector20_chunk4_03_check]
  rw [middleFourDegreeFourVector20_chunk4_04_check]
  rw [middleFourDegreeFourVector20_chunk4_05_check]
  rw [middleFourDegreeFourVector20_chunk4_06_check]
  rw [middleFourDegreeFourVector20_chunk4_07_check]
  rw [middleFourDegreeFourVector20_chunk4_08_check]
  rw [middleFourDegreeFourVector20_chunk4_09_check]
  rw [middleFourDegreeFourVector20_chunk4_10_check]
  rw [middleFourDegreeFourVector20_chunk4_11_check]
  rw [middleFourDegreeFourVector20_chunk4_12_check]
  rw [middleFourDegreeFourVector20_chunk4_13_check]
  rw [middleFourDegreeFourVector20_chunk4_14_check]
  rw [middleFourDegreeFourVector20_chunk4_15_check]
  decide

theorem middleFourDegreeFourVector20_raw4_check :
    (middleFourListPowerset
      middleFourDegreeFourVector20Eligible4).all
      (middleFourModelRawOldCheck middleFourDegreeFourVector20
        middleFourDegreeFourVector20Base4) = true :=
  middleFourModelRawSelectionCheck_of_chunks _ _ _ _
    middleFourDegreeFourVector20_chunks4_flatten
    middleFourDegreeFourVector20_chunks4_check

theorem middleFourDegreeFourVector20_selection4_check :
    (middleFourModelCandidateRowsForSelection middleFourDegreeFourVector20
      middleFourDegreeFourVector20Selected4).all
      (fun candidate => decide ((fastBlocker candidate).card ≠ 8)) = true :=
  middleFourModelCandidateRowsForSelection_check_of_raw _ _ _ _
    middleFourDegreeFourVector20_base4 (by decide)
    middleFourDegreeFourVector20_eligible4
    middleFourDegreeFourVector20_raw4_check

end AiMathLab.P0054.G420
