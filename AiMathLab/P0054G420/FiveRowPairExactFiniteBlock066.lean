import AiMathLab.P0054G420.FiveRowPairExactFiniteMasks
import AiMathLab.P0054G420.FiveRowPairExactFiniteFourCheck044
import AiMathLab.P0054G420.FiveRowPairExactFiniteFourCheck045
import AiMathLab.P0054G420.FiveRowPairExactFiniteFourCheck046

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- This fixed block exhausts sixty-four support masks for the exceptional case.
theorem four_exceptional_pair_exact_block_066 (offset : Fin 64) :
    smallFourClassificationMaskCheck 3
      fourExceptionalMultiplicityLeafValid
      fourExceptionalMultiplicityInCertificate (4224 + offset.val) = true := by
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
      four_exceptional_pair_exact_mask_group_044) 4235 (by decide)
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_044) 4238 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_045) 4239 (by decide)
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
      four_exceptional_pair_exact_mask_group_045) 4251 (by decide)
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_045) 4254 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_045) 4259 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_046) 4260 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_046) 4261 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_046) 4262 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_046) 4263 (by decide)
  · rfl
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_046) 4267 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_046) 4268 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_046) 4269 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_046) 4270 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_046) 4275 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_046) 4276 (by decide)
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

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- This fixed block exhausts sixty-four support masks for the padded case.
theorem three_padded_pair_exact_block_066 (offset : Fin 64) :
    smallFourClassificationMaskCheck 0
      threePaddedMultiplicityLeafValid
      threePaddedMultiplicityInCertificate (4224 + offset.val) = true := by
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
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.G420
