import AiMathLab.P0054G420.FiveRowPairExactFiniteMasks
import AiMathLab.P0054G420.FiveRowPairExactFiniteFourCheck040
import AiMathLab.P0054G420.FiveRowPairExactFiniteFourCheck041
import AiMathLab.P0054G420.FiveRowPairExactFiniteFourCheck042

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- This fixed block exhausts sixty-four support masks for the exceptional case.
theorem four_exceptional_pair_exact_block_048 (offset : Fin 64) :
    smallFourClassificationMaskCheck 3
      fourExceptionalMultiplicityLeafValid
      fourExceptionalMultiplicityInCertificate (3072 + offset.val) = true := by
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
      four_exceptional_pair_exact_mask_group_040) 3083 (by decide)
  · rfl
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_041) 3087 (by decide)
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_041) 3090 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_041) 3091 (by decide)
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_041) 3094 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_041) 3095 (by decide)
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_041) 3098 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_041) 3099 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_041) 3105 (by decide)
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_042) 3107 (by decide)
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_042) 3109 (by decide)
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_042) 3111 (by decide)
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_042) 3113 (by decide)
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_042) 3115 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_042) 3120 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_042) 3121 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_042) 3122 (by decide)
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

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- This fixed block exhausts sixty-four support masks for the padded case.
theorem three_padded_pair_exact_block_048 (offset : Fin 64) :
    smallFourClassificationMaskCheck 0
      threePaddedMultiplicityLeafValid
      threePaddedMultiplicityInCertificate (3072 + offset.val) = true := by
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
