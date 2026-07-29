import AiMathLab.P0054G420.FiveRowPairExactFiniteMasks

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The offline node budget is at most 100; Lean rechecks the whole group.
theorem four_exceptional_pair_exact_mask_group_017 :
    fourPairExactMaskGroup017.all
      (smallFourClassificationMaskCheck 3
        fourExceptionalMultiplicityLeafValid fourExceptionalMultiplicityInCertificate) = true := by
  rfl

end AiMathLab.P0054.G420
