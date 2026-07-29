import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk1_00
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk1_01
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk1_02
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk1_03
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk1_04
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk1_05
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk1_06
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk1_07
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk1_08
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk1_09
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk1_10
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk1_11
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk1_12
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk1_13
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk1_14
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk1_15

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector20Chunks1 :
    List (List (List MiddleFourModelPoint)) :=
  [middleFourDegreeFourVector20Chunk1_00, middleFourDegreeFourVector20Chunk1_01, middleFourDegreeFourVector20Chunk1_02, middleFourDegreeFourVector20Chunk1_03, middleFourDegreeFourVector20Chunk1_04, middleFourDegreeFourVector20Chunk1_05, middleFourDegreeFourVector20Chunk1_06, middleFourDegreeFourVector20Chunk1_07, middleFourDegreeFourVector20Chunk1_08, middleFourDegreeFourVector20Chunk1_09, middleFourDegreeFourVector20Chunk1_10, middleFourDegreeFourVector20Chunk1_11, middleFourDegreeFourVector20Chunk1_12, middleFourDegreeFourVector20Chunk1_13, middleFourDegreeFourVector20Chunk1_14, middleFourDegreeFourVector20Chunk1_15]

theorem middleFourDegreeFourVector20_chunks1_flatten :
    middleFourDegreeFourVector20Chunks1.flatMap id =
      middleFourListPowerset middleFourDegreeFourVector20Eligible1 := by
  decide

theorem middleFourDegreeFourVector20_chunks1_check :
    middleFourDegreeFourVector20Chunks1.all
      (middleFourModelRawChunkCheck middleFourDegreeFourVector20
        middleFourDegreeFourVector20Base1) = true := by
  unfold middleFourDegreeFourVector20Chunks1
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourVector20_chunk1_00_check]
  rw [middleFourDegreeFourVector20_chunk1_01_check]
  rw [middleFourDegreeFourVector20_chunk1_02_check]
  rw [middleFourDegreeFourVector20_chunk1_03_check]
  rw [middleFourDegreeFourVector20_chunk1_04_check]
  rw [middleFourDegreeFourVector20_chunk1_05_check]
  rw [middleFourDegreeFourVector20_chunk1_06_check]
  rw [middleFourDegreeFourVector20_chunk1_07_check]
  rw [middleFourDegreeFourVector20_chunk1_08_check]
  rw [middleFourDegreeFourVector20_chunk1_09_check]
  rw [middleFourDegreeFourVector20_chunk1_10_check]
  rw [middleFourDegreeFourVector20_chunk1_11_check]
  rw [middleFourDegreeFourVector20_chunk1_12_check]
  rw [middleFourDegreeFourVector20_chunk1_13_check]
  rw [middleFourDegreeFourVector20_chunk1_14_check]
  rw [middleFourDegreeFourVector20_chunk1_15_check]
  decide

theorem middleFourDegreeFourVector20_raw1_check :
    (middleFourListPowerset
      middleFourDegreeFourVector20Eligible1).all
      (middleFourModelRawOldCheck middleFourDegreeFourVector20
        middleFourDegreeFourVector20Base1) = true :=
  middleFourModelRawSelectionCheck_of_chunks _ _ _ _
    middleFourDegreeFourVector20_chunks1_flatten
    middleFourDegreeFourVector20_chunks1_check

theorem middleFourDegreeFourVector20_selection1_check :
    (middleFourModelCandidateRowsForSelection middleFourDegreeFourVector20
      middleFourDegreeFourVector20Selected1).all
      (fun candidate => decide ((fastBlocker candidate).card ≠ 8)) = true :=
  middleFourModelCandidateRowsForSelection_check_of_raw _ _ _ _
    middleFourDegreeFourVector20_base1 (by decide)
    middleFourDegreeFourVector20_eligible1
    middleFourDegreeFourVector20_raw1_check

end AiMathLab.P0054.G420
