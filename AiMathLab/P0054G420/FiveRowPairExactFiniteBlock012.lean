import AiMathLab.P0054G420.FiveRowPairExactFiniteMasks
import AiMathLab.P0054G420.FiveRowPairExactFiniteFourCheck015
import AiMathLab.P0054G420.FiveRowPairExactFiniteFourCheck016
import AiMathLab.P0054G420.FiveRowPairExactFiniteFourCheck017
import AiMathLab.P0054G420.FiveRowPairExactFiniteThreeCheck008

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- This fixed block exhausts sixty-four support masks for the exceptional case.
theorem four_exceptional_pair_exact_block_012 (offset : Fin 64) :
    smallFourClassificationMaskCheck 3
      fourExceptionalMultiplicityLeafValid
      fourExceptionalMultiplicityInCertificate (768 + offset.val) = true := by
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
      four_exceptional_pair_exact_mask_group_015) 779 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_015) 780 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_015) 781 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_015) 782 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_015) 783 (by decide)
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
      four_exceptional_pair_exact_mask_group_015) 794 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_015) 795 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_015) 796 (by decide)
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
      four_exceptional_pair_exact_mask_group_015) 809 (by decide)
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_016) 811 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_016) 812 (by decide)
  · rfl
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_016) 816 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_016) 817 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_016) 818 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_017) 819 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_017) 820 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_017) 821 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_017) 822 (by decide)
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_017) 824 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_017) 825 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_017) 826 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- This fixed block exhausts sixty-four support masks for the padded case.
theorem three_padded_pair_exact_block_012 (offset : Fin 64) :
    smallFourClassificationMaskCheck 0
      threePaddedMultiplicityLeafValid
      threePaddedMultiplicityInCertificate (768 + offset.val) = true := by
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
      three_padded_pair_exact_mask_group_008) 779 (by decide)
  · exact (List.all_eq_true.mp
      three_padded_pair_exact_mask_group_008) 780 (by decide)
  · exact (List.all_eq_true.mp
      three_padded_pair_exact_mask_group_008) 781 (by decide)
  · exact (List.all_eq_true.mp
      three_padded_pair_exact_mask_group_008) 782 (by decide)
  · exact (List.all_eq_true.mp
      three_padded_pair_exact_mask_group_008) 783 (by decide)
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
