import AiMathLab.P0054G420.MiddleFourDegreeFourCheck
import AiMathLab.P0054G420.MiddleFourActualEnumerated

namespace AiMathLab.P0054.G420

open G413 G419

theorem middleFourActualSupportMultiplicity_degreeFour_check {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {T : G413.Hypergraph alpha} (rowOrder : Fin 4 ≃ T)
    (hTClutter : IsClutter T)
    (hBRows : RowsCardAtLeast (blocker T) 2)
    (hTRows : RowsCardAtLeast T 3)
    (hTUpper : ∀ E ∈ T, E.card ≤ 8)
    (hBCard : (blocker T).card ≤ 8)
    (hPairCard : (pairRows (blocker T)).card ≤ 4) :
    middleFourDegreeFourValuesCheck
      (fourActualSupportMultiplicity rowOrder).toList = true := by
  have hCertificate := middleFourActualSupportMultiplicity_in_certificate rowOrder
    hTClutter hBRows hTRows hTUpper hBCard hPairCard
  unfold middleFourMultiplicityInCertificate at hCertificate
  obtain ⟨values, hValues, hListCheck⟩ := List.any_eq_true.mp hCertificate
  have hList : (fourActualSupportMultiplicity rowOrder).toList = values :=
    of_decide_eq_true hListCheck
  rw [hList]
  exact List.all_eq_true.mp middleFourMultiplicityCertificate_degreeFour_check
    values hValues

end AiMathLab.P0054.G420
