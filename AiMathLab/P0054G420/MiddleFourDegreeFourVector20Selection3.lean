import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk3_00
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk3_01
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk3_02
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk3_03
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk3_04
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk3_05
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk3_06
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk3_07
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk3_08
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk3_09
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk3_10
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk3_11
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk3_12
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk3_13
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk3_14
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk3_15

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector20Chunks3 :
    List (List (List MiddleFourModelPoint)) :=
  [middleFourDegreeFourVector20Chunk3_00, middleFourDegreeFourVector20Chunk3_01, middleFourDegreeFourVector20Chunk3_02, middleFourDegreeFourVector20Chunk3_03, middleFourDegreeFourVector20Chunk3_04, middleFourDegreeFourVector20Chunk3_05, middleFourDegreeFourVector20Chunk3_06, middleFourDegreeFourVector20Chunk3_07, middleFourDegreeFourVector20Chunk3_08, middleFourDegreeFourVector20Chunk3_09, middleFourDegreeFourVector20Chunk3_10, middleFourDegreeFourVector20Chunk3_11, middleFourDegreeFourVector20Chunk3_12, middleFourDegreeFourVector20Chunk3_13, middleFourDegreeFourVector20Chunk3_14, middleFourDegreeFourVector20Chunk3_15]

theorem middleFourDegreeFourVector20_chunks3_flatten :
    middleFourDegreeFourVector20Chunks3.flatMap id =
      middleFourListPowerset middleFourDegreeFourVector20Eligible3 := by
  decide

theorem middleFourDegreeFourVector20_chunks3_check :
    middleFourDegreeFourVector20Chunks3.all
      (middleFourModelRawChunkCheck middleFourDegreeFourVector20
        middleFourDegreeFourVector20Base3) = true := by
  unfold middleFourDegreeFourVector20Chunks3
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourVector20_chunk3_00_check]
  rw [middleFourDegreeFourVector20_chunk3_01_check]
  rw [middleFourDegreeFourVector20_chunk3_02_check]
  rw [middleFourDegreeFourVector20_chunk3_03_check]
  rw [middleFourDegreeFourVector20_chunk3_04_check]
  rw [middleFourDegreeFourVector20_chunk3_05_check]
  rw [middleFourDegreeFourVector20_chunk3_06_check]
  rw [middleFourDegreeFourVector20_chunk3_07_check]
  rw [middleFourDegreeFourVector20_chunk3_08_check]
  rw [middleFourDegreeFourVector20_chunk3_09_check]
  rw [middleFourDegreeFourVector20_chunk3_10_check]
  rw [middleFourDegreeFourVector20_chunk3_11_check]
  rw [middleFourDegreeFourVector20_chunk3_12_check]
  rw [middleFourDegreeFourVector20_chunk3_13_check]
  rw [middleFourDegreeFourVector20_chunk3_14_check]
  rw [middleFourDegreeFourVector20_chunk3_15_check]
  decide

theorem middleFourDegreeFourVector20_raw3_check :
    (middleFourListPowerset
      middleFourDegreeFourVector20Eligible3).all
      (middleFourModelRawOldCheck middleFourDegreeFourVector20
        middleFourDegreeFourVector20Base3) = true :=
  middleFourModelRawSelectionCheck_of_chunks _ _ _ _
    middleFourDegreeFourVector20_chunks3_flatten
    middleFourDegreeFourVector20_chunks3_check

theorem middleFourDegreeFourVector20_selection3_check :
    (middleFourModelCandidateRowsForSelection middleFourDegreeFourVector20
      middleFourDegreeFourVector20Selected3).all
      (fun candidate => decide ((fastBlocker candidate).card ≠ 8)) = true :=
  middleFourModelCandidateRowsForSelection_check_of_raw _ _ _ _
    middleFourDegreeFourVector20_base3 (by decide)
    middleFourDegreeFourVector20_eligible3
    middleFourDegreeFourVector20_raw3_check

end AiMathLab.P0054.G420
