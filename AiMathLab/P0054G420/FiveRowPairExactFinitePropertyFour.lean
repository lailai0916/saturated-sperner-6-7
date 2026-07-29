import AiMathLab.P0054G420.FiveRowPairExactFinitePropertyFour00
import AiMathLab.P0054G420.FiveRowPairExactFinitePropertyFour01
import AiMathLab.P0054G420.FiveRowPairExactFinitePropertyFour02
import AiMathLab.P0054G420.FiveRowPairExactFinitePropertyFour03
import AiMathLab.P0054G420.FiveRowPairExactFinitePropertyFour04
import AiMathLab.P0054G420.FiveRowPairExactFinitePropertyFour05

namespace AiMathLab.P0054.G420

theorem four_exceptional_certificate_property :
    ∀ values ∈ fourExceptionalMultiplicityCertificate,
      FourExceptionalModelProperty values := by
  intro values hValues
  simp [fourExceptionalMultiplicityCertificate] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl
  · exact four_exceptional_model_property_00
  · exact four_exceptional_model_property_01
  · exact four_exceptional_model_property_02
  · exact four_exceptional_model_property_03
  · exact four_exceptional_model_property_04
  · exact four_exceptional_model_property_05

theorem four_exceptional_certificate_supports_length :
    ∀ values ∈ fourExceptionalMultiplicityCertificate,
      (middleFourModelSupports values).length < 16 := by
  decide

end AiMathLab.P0054.G420
