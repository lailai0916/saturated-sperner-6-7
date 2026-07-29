import AiMathLab.P0054MiddleSevenEightFiveKernelBranch

/-!
# Excluding the middle split seven plus eight

Both blocker-dual sides have maximum degree three, and the middle-cover
argument supplies a three-point row on one of them.  The two possible
locations are excluded by the Fano branch and the five-row-kernel branch.
-/

namespace AiMathLab.P0054.MiddleSevenEight

open AiMathLab.P0054.G413
open AiMathLab.P0054.MiddleSevenEightBasics
open AiMathLab.P0054.MiddleSevenEightDegree
open AiMathLab.P0054.MiddleSevenEightFanoBranch
open AiMathLab.P0054.MiddleSevenEightFiveKernelBranch

theorem sevenEight_impossible {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α}
    (hHClutter : IsClutter H)
    (hHCard : H.card = 7)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hBCard : (blocker H).card = 8) :
    False := by
  have hHMaxDegree : MaxDegreeAtMost H 3 :=
    sevenRows_maxDegreeAtMost_three hHClutter hHCard hHRows hBRows hBCard
  have hDualRows : RowsCardAtLeast (blocker (blocker H)) 3 := by
    simpa [blocker_involution hHClutter] using hHRows
  have hDualCard : (blocker (blocker H)).card = 7 := by
    simpa [blocker_involution hHClutter] using hHCard
  have hBMaxDegree : MaxDegreeAtMost (blocker H) 3 :=
    eightRows_maxDegreeAtMost_three (blocker_isClutter H) hBCard hBRows
      hDualRows hDualCard
  rcases sevenEight_has_three_row hHCard hBCard hHRows hBRows with
      ⟨T, hTH, hTCard⟩ | ⟨T, hTB, hTCard⟩
  · exact threeRow_on_sevenSide_impossible hHClutter hHCard hHRows
      hHMaxDegree hBCard hBRows hBMaxDegree hTH hTCard
  · exact threeRow_on_eightSide_impossible hHClutter hHCard hHRows
      hHMaxDegree hBCard hBRows hBMaxDegree hTB hTCard

end AiMathLab.P0054.MiddleSevenEight
