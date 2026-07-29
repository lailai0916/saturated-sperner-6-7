import AiMathLab.P0054G420.FiveRowPairExactFinitePropertyThree00
import AiMathLab.P0054G420.FiveRowPairExactFinitePropertyThree01
import AiMathLab.P0054G420.FiveRowPairExactFinitePropertyThree02
import AiMathLab.P0054G420.FiveRowPairExactFinitePropertyThree03
import AiMathLab.P0054G420.FiveRowPairExactFinitePropertyThree04
import AiMathLab.P0054G420.FiveRowPairExactFinitePropertyThree05
import AiMathLab.P0054G420.FiveRowPairExactFinitePropertyThree06
import AiMathLab.P0054G420.FiveRowPairExactFinitePropertyThree07
import AiMathLab.P0054G420.FiveRowPairExactFinitePropertyThree08
import AiMathLab.P0054G420.FiveRowPairExactFinitePropertyThree09
import AiMathLab.P0054G420.FiveRowPairExactFinitePropertyThree10
import AiMathLab.P0054G420.FiveRowPairExactFinitePropertyThree11
import AiMathLab.P0054G420.FiveRowPairExactFinitePropertyThree12
import AiMathLab.P0054G420.FiveRowPairExactFinitePropertyThree13
import AiMathLab.P0054G420.FiveRowPairExactFinitePropertyThree14

namespace AiMathLab.P0054.G420

theorem three_padded_certificate_property :
    ∀ values ∈ threePaddedMultiplicityCertificate,
      ThreePaddedModelProperty values := by
  intro values hValues
  simp [threePaddedMultiplicityCertificate] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact three_padded_model_property_00
  · exact three_padded_model_property_01
  · exact three_padded_model_property_02
  · exact three_padded_model_property_03
  · exact three_padded_model_property_04
  · exact three_padded_model_property_05
  · exact three_padded_model_property_06
  · exact three_padded_model_property_07
  · exact three_padded_model_property_08
  · exact three_padded_model_property_09
  · exact three_padded_model_property_10
  · exact three_padded_model_property_11
  · exact three_padded_model_property_12
  · exact three_padded_model_property_13
  · exact three_padded_model_property_14

theorem three_padded_certificate_supports_length :
    ∀ values ∈ threePaddedMultiplicityCertificate,
      (middleFourModelSupports values).length < 16 := by
  decide

end AiMathLab.P0054.G420
