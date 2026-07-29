import AiMathLab.P0054G417
import AiMathLab.P0054G418
import AiMathLab.P0054G419.KernelAReduction
import AiMathLab.P0054G419.KernelBExclude
import AiMathLab.P0054G419.KernelCExclude

namespace AiMathLab.P0054.G419

open G413

theorem sixTen_degreeThree_impossible {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α}
    (hHClutter : IsClutter H)
    (hHCard : H.card = 6)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hBCard : (blocker H).card = 10)
    {x : α} (hDegree : degree H x = 3) : False := by
  obtain ⟨A, B, C, hAB, hAC, hBC, hK, hProfile⟩ :=
    sixTen_degreeThree_kernel_profile
      hHClutter hHCard hHRows hBRows hBCard hDegree
  unfold OrderedThreeKernelProfile at hProfile
  rcases hProfile with hProfile | hProfile | hProfile | hProfile |
    hProfile | hProfile | hProfile
  · exact sixTen_degreeThree_kernelA_impossible
      hHClutter hHCard hHRows hBRows hBCard hDegree
      hK hAB hAC hBC hProfile
  · exact sixTen_degreeThree_kernelB_impossible
      hHClutter hHCard hHRows hBRows hBCard hDegree
      hK hAB hAC hBC (Or.inl hProfile)
  · exact sixTen_degreeThree_kernelB_impossible
      hHClutter hHCard hHRows hBRows hBCard hDegree
      hK hAB hAC hBC (Or.inr (Or.inl hProfile))
  · exact sixTen_degreeThree_kernelB_impossible
      hHClutter hHCard hHRows hBRows hBCard hDegree
      hK hAB hAC hBC (Or.inr (Or.inr hProfile))
  · exact sixTen_degreeThree_kernelC_impossible
      hHClutter hHCard hHRows hBRows hBCard hDegree
      hK hAB hAC hBC (Or.inl hProfile)
  · exact sixTen_degreeThree_kernelC_impossible
      hHClutter hHCard hHRows hBRows hBCard hDegree
      hK hAB hAC hBC (Or.inr (Or.inl hProfile))
  · exact sixTen_degreeThree_kernelC_impossible
      hHClutter hHCard hHRows hBRows hBCard hDegree
      hK hAB hAC hBC (Or.inr (Or.inr hProfile))

theorem sixTen_impossible {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α}
    (hHClutter : IsClutter H)
    (hHCard : H.card = 6)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hBCard : (blocker H).card = 10) : False := by
  have hDegreeUpper := G418.sixRow_maxDegreeAtMost_three
    hHCard hHRows hBRows hBCard
  by_cases hLowDegree : MaxDegreeAtMost H 2
  · exact G417.sixTen_lowDegree_impossible
      hHCard hHRows hBCard hLowDegree
  · unfold MaxDegreeAtMost at hLowDegree
    push Not at hLowDegree
    obtain ⟨x, hxDegree⟩ := hLowDegree
    have hDegreeThree : degree H x = 3 := by
      have hUpper := hDegreeUpper x
      omega
    exact sixTen_degreeThree_impossible
      hHClutter hHCard hHRows hBRows hBCard hDegreeThree

end AiMathLab.P0054.G419
