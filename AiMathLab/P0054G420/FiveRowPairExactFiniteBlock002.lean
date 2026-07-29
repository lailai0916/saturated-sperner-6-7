import AiMathLab.P0054G420.FiveRowPairExactFiniteMasks
import AiMathLab.P0054G420.FiveRowPairExactFiniteFourCheck000
import AiMathLab.P0054G420.FiveRowPairExactFiniteFourCheck001
import AiMathLab.P0054G420.FiveRowPairExactFiniteFourCheck002
import AiMathLab.P0054G420.FiveRowPairExactFiniteFourCheck003
import AiMathLab.P0054G420.FiveRowPairExactFiniteFourCheck004
import AiMathLab.P0054G420.FiveRowPairExactFiniteFourCheck005
import AiMathLab.P0054G420.FiveRowPairExactFiniteThreeCheck000
import AiMathLab.P0054G420.FiveRowPairExactFiniteThreeCheck001
import AiMathLab.P0054G420.FiveRowPairExactFiniteThreeCheck002
import AiMathLab.P0054G420.FiveRowPairExactFiniteThreeCheck003
import AiMathLab.P0054G420.FiveRowPairExactFiniteThreeCheck004
import AiMathLab.P0054G420.FiveRowPairExactFiniteThreeCheck005

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- This fixed block exhausts sixty-four support masks for the exceptional case.
theorem four_exceptional_pair_exact_block_002 (offset : Fin 64) :
    smallFourClassificationMaskCheck 3
      fourExceptionalMultiplicityLeafValid
      fourExceptionalMultiplicityInCertificate (128 + offset.val) = true := by
  fin_cases offset
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_000) 139 (by decide)
  · rfl
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_001) 143 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_002) 155 (by decide)
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_002) 158 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_002) 159 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_003) 171 (by decide)
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_003) 173 (by decide)
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_003) 175 (by decide)
  · rfl
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_004) 179 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_004) 180 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_004) 181 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_004) 182 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_004) 183 (by decide)
  · rfl
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_004) 187 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_004) 188 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_005) 189 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_005) 190 (by decide)
  · rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- This fixed block exhausts sixty-four support masks for the padded case.
theorem three_padded_pair_exact_block_002 (offset : Fin 64) :
    smallFourClassificationMaskCheck 0
      threePaddedMultiplicityLeafValid
      threePaddedMultiplicityInCertificate (128 + offset.val) = true := by
  fin_cases offset
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      three_padded_pair_exact_mask_group_000) 139 (by decide)
  · rfl
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      three_padded_pair_exact_mask_group_001) 143 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      three_padded_pair_exact_mask_group_002) 155 (by decide)
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      three_padded_pair_exact_mask_group_002) 158 (by decide)
  · exact (List.all_eq_true.mp
      three_padded_pair_exact_mask_group_002) 159 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      three_padded_pair_exact_mask_group_003) 171 (by decide)
  · rfl
  · exact (List.all_eq_true.mp
      three_padded_pair_exact_mask_group_003) 173 (by decide)
  · rfl
  · exact (List.all_eq_true.mp
      three_padded_pair_exact_mask_group_003) 175 (by decide)
  · rfl
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      three_padded_pair_exact_mask_group_004) 179 (by decide)
  · exact (List.all_eq_true.mp
      three_padded_pair_exact_mask_group_004) 180 (by decide)
  · exact (List.all_eq_true.mp
      three_padded_pair_exact_mask_group_004) 181 (by decide)
  · exact (List.all_eq_true.mp
      three_padded_pair_exact_mask_group_004) 182 (by decide)
  · exact (List.all_eq_true.mp
      three_padded_pair_exact_mask_group_004) 183 (by decide)
  · rfl
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      three_padded_pair_exact_mask_group_004) 187 (by decide)
  · exact (List.all_eq_true.mp
      three_padded_pair_exact_mask_group_004) 188 (by decide)
  · exact (List.all_eq_true.mp
      three_padded_pair_exact_mask_group_005) 189 (by decide)
  · exact (List.all_eq_true.mp
      three_padded_pair_exact_mask_group_005) 190 (by decide)
  · rfl

end AiMathLab.P0054.G420
