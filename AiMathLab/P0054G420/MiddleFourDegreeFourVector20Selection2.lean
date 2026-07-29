import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk2_00
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk2_01
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk2_02
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk2_03
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk2_04
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk2_05
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk2_06
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk2_07
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk2_08
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk2_09
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk2_10
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk2_11
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk2_12
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk2_13
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk2_14
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk2_15

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector20Chunks2 :
    List (List (List MiddleFourModelPoint)) :=
  [middleFourDegreeFourVector20Chunk2_00, middleFourDegreeFourVector20Chunk2_01, middleFourDegreeFourVector20Chunk2_02, middleFourDegreeFourVector20Chunk2_03, middleFourDegreeFourVector20Chunk2_04, middleFourDegreeFourVector20Chunk2_05, middleFourDegreeFourVector20Chunk2_06, middleFourDegreeFourVector20Chunk2_07, middleFourDegreeFourVector20Chunk2_08, middleFourDegreeFourVector20Chunk2_09, middleFourDegreeFourVector20Chunk2_10, middleFourDegreeFourVector20Chunk2_11, middleFourDegreeFourVector20Chunk2_12, middleFourDegreeFourVector20Chunk2_13, middleFourDegreeFourVector20Chunk2_14, middleFourDegreeFourVector20Chunk2_15]

theorem middleFourDegreeFourVector20_chunks2_flatten :
    middleFourDegreeFourVector20Chunks2.flatMap id =
      middleFourListPowerset middleFourDegreeFourVector20Eligible2 := by
  decide

theorem middleFourDegreeFourVector20_chunks2_check :
    middleFourDegreeFourVector20Chunks2.all
      (middleFourModelRawChunkCheck middleFourDegreeFourVector20
        middleFourDegreeFourVector20Base2) = true := by
  unfold middleFourDegreeFourVector20Chunks2
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourVector20_chunk2_00_check]
  rw [middleFourDegreeFourVector20_chunk2_01_check]
  rw [middleFourDegreeFourVector20_chunk2_02_check]
  rw [middleFourDegreeFourVector20_chunk2_03_check]
  rw [middleFourDegreeFourVector20_chunk2_04_check]
  rw [middleFourDegreeFourVector20_chunk2_05_check]
  rw [middleFourDegreeFourVector20_chunk2_06_check]
  rw [middleFourDegreeFourVector20_chunk2_07_check]
  rw [middleFourDegreeFourVector20_chunk2_08_check]
  rw [middleFourDegreeFourVector20_chunk2_09_check]
  rw [middleFourDegreeFourVector20_chunk2_10_check]
  rw [middleFourDegreeFourVector20_chunk2_11_check]
  rw [middleFourDegreeFourVector20_chunk2_12_check]
  rw [middleFourDegreeFourVector20_chunk2_13_check]
  rw [middleFourDegreeFourVector20_chunk2_14_check]
  rw [middleFourDegreeFourVector20_chunk2_15_check]
  decide

theorem middleFourDegreeFourVector20_raw2_check :
    (middleFourListPowerset
      middleFourDegreeFourVector20Eligible2).all
      (middleFourModelRawOldCheck middleFourDegreeFourVector20
        middleFourDegreeFourVector20Base2) = true :=
  middleFourModelRawSelectionCheck_of_chunks _ _ _ _
    middleFourDegreeFourVector20_chunks2_flatten
    middleFourDegreeFourVector20_chunks2_check

theorem middleFourDegreeFourVector20_selection2_check :
    (middleFourModelCandidateRowsForSelection middleFourDegreeFourVector20
      middleFourDegreeFourVector20Selected2).all
      (fun candidate => decide ((fastBlocker candidate).card ≠ 8)) = true :=
  middleFourModelCandidateRowsForSelection_check_of_raw _ _ _ _
    middleFourDegreeFourVector20_base2 (by decide)
    middleFourDegreeFourVector20_eligible2
    middleFourDegreeFourVector20_raw2_check

end AiMathLab.P0054.G420
