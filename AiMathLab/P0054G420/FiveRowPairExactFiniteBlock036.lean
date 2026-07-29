import AiMathLab.P0054G420.FiveRowPairExactFiniteMasks
import AiMathLab.P0054G420.FiveRowPairExactFiniteFourCheck029
import AiMathLab.P0054G420.FiveRowPairExactFiniteFourCheck030
import AiMathLab.P0054G420.FiveRowPairExactFiniteFourCheck031
import AiMathLab.P0054G420.FiveRowPairExactFiniteFourCheck032
import AiMathLab.P0054G420.FiveRowPairExactFiniteThreeCheck010
import AiMathLab.P0054G420.FiveRowPairExactFiniteThreeCheck011

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- This fixed block exhausts sixty-four support masks for the exceptional case.
theorem four_exceptional_pair_exact_block_036 (offset : Fin 64) :
    smallFourClassificationMaskCheck 3
      fourExceptionalMultiplicityLeafValid
      fourExceptionalMultiplicityInCertificate (2304 + offset.val) = true := by
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
      four_exceptional_pair_exact_mask_group_029) 2315 (by decide)
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_029) 2318 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_029) 2319 (by decide)
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_029) 2322 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_030) 2323 (by decide)
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_030) 2326 (by decide)
  · rfl
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_030) 2330 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_030) 2331 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_030) 2339 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_030) 2340 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_030) 2341 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_031) 2342 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_031) 2343 (by decide)
  · rfl
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_031) 2347 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_031) 2348 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_031) 2349 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_031) 2350 (by decide)
  · rfl
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_032) 2354 (by decide)
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_032) 2356 (by decide)
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_032) 2357 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      four_exceptional_pair_exact_mask_group_032) 2364 (by decide)
  · rfl
  · rfl
  · rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- This fixed block exhausts sixty-four support masks for the padded case.
theorem three_padded_pair_exact_block_036 (offset : Fin 64) :
    smallFourClassificationMaskCheck 0
      threePaddedMultiplicityLeafValid
      threePaddedMultiplicityInCertificate (2304 + offset.val) = true := by
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
      three_padded_pair_exact_mask_group_010) 2315 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      three_padded_pair_exact_mask_group_010) 2322 (by decide)
  · exact (List.all_eq_true.mp
      three_padded_pair_exact_mask_group_010) 2323 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (List.all_eq_true.mp
      three_padded_pair_exact_mask_group_010) 2330 (by decide)
  · exact (List.all_eq_true.mp
      three_padded_pair_exact_mask_group_011) 2331 (by decide)
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
