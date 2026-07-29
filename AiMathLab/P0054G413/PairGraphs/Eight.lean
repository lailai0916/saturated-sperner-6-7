import AiMathLab.P0054G413.PairGraphs.ThreeK2Lift

namespace AiMathLab.P0054.G413

theorem fiveRow_eight_blocker_impossible {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α}
    (hK : IsClutter K)
    (hKcard : K.card = 5)
    (hKRows : RowsCardAtLeast K 3)
    (hKDegree : MaxDegreeAtMost K 3)
    (hBcard : (blocker K).card = 8)
    (hBRows : RowsCardAtLeast (blocker K) 2)
    (hBDegree : MaxDegreeAtMost (blocker K) 3)
    (hPairRowsCard : (pairRows (blocker K)).card = 3) :
    False := by
  have hDualCard : (blocker (blocker K)).card = 5 := by
    rw [blocker_involution hK, hKcard]
  have hDualRows : RowsCardAtLeast (blocker (blocker K)) 3 := by
    rw [blocker_involution hK]
    exact hKRows
  have hDualDegree : MaxDegreeAtMost (blocker (blocker K)) 3 := by
    rw [blocker_involution hK]
    exact hKDegree
  rcases three_pair_graph_classification hPairRowsCard with
      hP4 | hP3K2 | hThreeK2 | hK3 | hK13
  · exact p4_pairGraph_impossible (blocker_isClutter K) hBcard hBRows hBDegree
      hDualCard hDualRows hDualDegree hP4
  · obtain ⟨a, p, q, u, v, hVertices, hPairs⟩ := hP3K2
    exact p3k2_pairGraph_impossible hVertices (blocker_isClutter K) hBcard
      hBRows hBDegree hDualCard hDualRows hDualDegree hPairs
  · exact threeK2_pairGraph_impossible (blocker_isClutter K) hBcard hBRows
      hBDegree hDualCard hDualRows hDualDegree hThreeK2
  · exact k3_pairGraph_impossible hDualCard hDualDegree hK3
  · exact k13_pairGraph_impossible (blocker_isClutter K) hBcard hBRows
      hBDegree hPairRowsCard hDualCard hDualRows hDualDegree hK13

end AiMathLab.P0054.G413
