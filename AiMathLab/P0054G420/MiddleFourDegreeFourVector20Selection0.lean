import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk0_00
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk0_01
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk0_02
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk0_03
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk0_04
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk0_05
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk0_06
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk0_07
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk0_08
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk0_09
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk0_10
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk0_11
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk0_12
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk0_13
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk0_14
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Chunk0_15

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector20Chunks0 :
    List (List (List MiddleFourModelPoint)) :=
  [middleFourDegreeFourVector20Chunk0_00, middleFourDegreeFourVector20Chunk0_01, middleFourDegreeFourVector20Chunk0_02, middleFourDegreeFourVector20Chunk0_03, middleFourDegreeFourVector20Chunk0_04, middleFourDegreeFourVector20Chunk0_05, middleFourDegreeFourVector20Chunk0_06, middleFourDegreeFourVector20Chunk0_07, middleFourDegreeFourVector20Chunk0_08, middleFourDegreeFourVector20Chunk0_09, middleFourDegreeFourVector20Chunk0_10, middleFourDegreeFourVector20Chunk0_11, middleFourDegreeFourVector20Chunk0_12, middleFourDegreeFourVector20Chunk0_13, middleFourDegreeFourVector20Chunk0_14, middleFourDegreeFourVector20Chunk0_15]

theorem middleFourDegreeFourVector20_chunks0_flatten :
    middleFourDegreeFourVector20Chunks0.flatMap id =
      middleFourListPowerset middleFourDegreeFourVector20Eligible0 := by
  decide

theorem middleFourDegreeFourVector20_chunks0_check :
    middleFourDegreeFourVector20Chunks0.all
      (middleFourModelRawChunkCheck middleFourDegreeFourVector20
        middleFourDegreeFourVector20Base0) = true := by
  unfold middleFourDegreeFourVector20Chunks0
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourVector20_chunk0_00_check]
  rw [middleFourDegreeFourVector20_chunk0_01_check]
  rw [middleFourDegreeFourVector20_chunk0_02_check]
  rw [middleFourDegreeFourVector20_chunk0_03_check]
  rw [middleFourDegreeFourVector20_chunk0_04_check]
  rw [middleFourDegreeFourVector20_chunk0_05_check]
  rw [middleFourDegreeFourVector20_chunk0_06_check]
  rw [middleFourDegreeFourVector20_chunk0_07_check]
  rw [middleFourDegreeFourVector20_chunk0_08_check]
  rw [middleFourDegreeFourVector20_chunk0_09_check]
  rw [middleFourDegreeFourVector20_chunk0_10_check]
  rw [middleFourDegreeFourVector20_chunk0_11_check]
  rw [middleFourDegreeFourVector20_chunk0_12_check]
  rw [middleFourDegreeFourVector20_chunk0_13_check]
  rw [middleFourDegreeFourVector20_chunk0_14_check]
  rw [middleFourDegreeFourVector20_chunk0_15_check]
  decide

theorem middleFourDegreeFourVector20_raw0_check :
    (middleFourListPowerset
      middleFourDegreeFourVector20Eligible0).all
      (middleFourModelRawOldCheck middleFourDegreeFourVector20
        middleFourDegreeFourVector20Base0) = true :=
  middleFourModelRawSelectionCheck_of_chunks _ _ _ _
    middleFourDegreeFourVector20_chunks0_flatten
    middleFourDegreeFourVector20_chunks0_check

theorem middleFourDegreeFourVector20_selection0_check :
    (middleFourModelCandidateRowsForSelection middleFourDegreeFourVector20
      middleFourDegreeFourVector20Selected0).all
      (fun candidate => decide ((fastBlocker candidate).card ≠ 8)) = true :=
  middleFourModelCandidateRowsForSelection_check_of_raw _ _ _ _
    middleFourDegreeFourVector20_base0 (by decide)
    middleFourDegreeFourVector20_eligible0
    middleFourDegreeFourVector20_raw0_check

end AiMathLab.P0054.G420
