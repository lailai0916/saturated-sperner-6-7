import AiMathLab.P0054G420.FiveRowPairExactFiniteMasks
import AiMathLab.P0054G420.FiveRowPairExactFiniteFourCheck034
import AiMathLab.P0054G420.FiveRowPairExactFiniteFourCheck035
import AiMathLab.P0054G420.FiveRowPairExactFiniteFourCheck036
import AiMathLab.P0054G420.FiveRowPairExactFiniteFourCheck037
import AiMathLab.P0054G420.FiveRowPairExactFiniteThreeCheck011
import AiMathLab.P0054G420.FiveRowPairExactFiniteThreeCheck012

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- This fixed block exhausts sixty-four support masks for the exceptional case.
theorem four_exceptional_pair_exact_block_040 (offset : Fin 64) :
    smallFourClassificationMaskCheck 3
      fourExceptionalMultiplicityLeafValid
      fourExceptionalMultiplicityInCertificate (2560 + offset.val) = true := by
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
      four_exceptional_pair_exact_mask_group_034) 2571 (by decide)
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_034) 2573 (by decide)
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_034) 2575 (by decide)
  · rfl
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_034) 2579 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_035) 2580 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_035) 2581 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_035) 2582 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_035) 2583 (by decide)
  · rfl
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_035) 2587 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_036) 2588 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_036) 2589 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_036) 2590 (by decide)
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_036) 2593 (by decide)
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_036) 2595 (by decide)
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_036) 2597 (by decide)
  · rfl
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_036) 2601 (by decide)
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_036) 2603 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_037) 2609 (by decide)
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_037) 2612 (by decide)
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_037) 2614 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_037) 2620 (by decide)
  · rfl
  · rfl
  · rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- This fixed block exhausts sixty-four support masks for the padded case.
theorem three_padded_pair_exact_block_040 (offset : Fin 64) :
    smallFourClassificationMaskCheck 0
      threePaddedMultiplicityLeafValid
      threePaddedMultiplicityInCertificate (2560 + offset.val) = true := by
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
      three_padded_pair_exact_mask_group_011) 2571 (by decide)
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
  · exact (List.all_eq_true.mp
      three_padded_pair_exact_mask_group_011) 2593 (by decide)
  · rfl
  · exact (List.all_eq_true.mp
      three_padded_pair_exact_mask_group_011) 2595 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      three_padded_pair_exact_mask_group_011) 2601 (by decide)
  · rfl
  · exact (List.all_eq_true.mp
      three_padded_pair_exact_mask_group_012) 2603 (by decide)
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
