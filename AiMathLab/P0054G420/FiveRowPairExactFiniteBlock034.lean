import AiMathLab.P0054G420.FiveRowPairExactFiniteMasks
import AiMathLab.P0054G420.FiveRowPairExactFiniteFourCheck027
import AiMathLab.P0054G420.FiveRowPairExactFiniteFourCheck028
import AiMathLab.P0054G420.FiveRowPairExactFiniteThreeCheck009
import AiMathLab.P0054G420.FiveRowPairExactFiniteThreeCheck010

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- This fixed block exhausts sixty-four support masks for the exceptional case.
theorem four_exceptional_pair_exact_block_034 (offset : Fin 64) :
    smallFourClassificationMaskCheck 3
      fourExceptionalMultiplicityLeafValid
      fourExceptionalMultiplicityInCertificate (2176 + offset.val) = true := by
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
      four_exceptional_pair_exact_mask_group_027) 2187 (by decide)
  · rfl
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_027) 2191 (by decide)
  · rfl
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_027) 2195 (by decide)
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_027) 2198 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_027) 2199 (by decide)
  · rfl
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_027) 2203 (by decide)
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_028) 2206 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_028) 2211 (by decide)
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_028) 2213 (by decide)
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_028) 2215 (by decide)
  · rfl
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_028) 2219 (by decide)
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_028) 2221 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_028) 2228 (by decide)
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
theorem three_padded_pair_exact_block_034 (offset : Fin 64) :
    smallFourClassificationMaskCheck 0
      threePaddedMultiplicityLeafValid
      threePaddedMultiplicityInCertificate (2176 + offset.val) = true := by
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
      three_padded_pair_exact_mask_group_009) 2187 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      three_padded_pair_exact_mask_group_009) 2195 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      three_padded_pair_exact_mask_group_009) 2203 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      three_padded_pair_exact_mask_group_010) 2211 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      three_padded_pair_exact_mask_group_010) 2219 (by decide)
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
