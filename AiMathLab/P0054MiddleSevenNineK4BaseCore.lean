import AiMathLab.P0054MiddleSevenNineK4FiniteCore

namespace AiMathLab.P0054.MiddleSevenNineK4Finite

theorem sevenNineK4BaseChunks_all_of_indexed
    (baseIndex : Nat)
    (hChunks : ∀ index, index < sevenNineK4BaseChunkCount baseIndex →
      (sevenNineK4ChunkOldPairs
        (sevenNineK4Bases.getD baseIndex []) index).all
        (sevenNineK4OldPairCheck
          (sevenNineK4Bases.getD baseIndex [])) = true) :
    (sevenNineK4BaseChunks baseIndex).all (fun chunk =>
      chunk.all (sevenNineK4OldPairCheck
        (sevenNineK4Bases.getD baseIndex []))) = true := by
  rw [List.all_eq_true]
  intro chunk hChunk
  rw [sevenNineK4BaseChunks, List.mem_map] at hChunk
  obtain ⟨index, hIndex, rfl⟩ := hChunk
  exact hChunks index (List.mem_range.mp hIndex)

theorem sevenNineK4BaseCheck_of_indexed_chunk_checks
    (baseIndex : Nat)
    (hFlatten : (sevenNineK4BaseChunks baseIndex).flatMap id =
      sevenNineK4OldPairs (sevenNineK4Bases.getD baseIndex []))
    (hChunks : ∀ index, index < sevenNineK4BaseChunkCount baseIndex →
      sevenNineK4ChunkCheck baseIndex index = true) :
    sevenNineK4BaseCheck (sevenNineK4Bases.getD baseIndex []) = true := by
  apply sevenNineK4BaseCheck_of_chunks
    (sevenNineK4Bases.getD baseIndex [])
    (sevenNineK4BaseChunks baseIndex) hFlatten
  apply sevenNineK4BaseChunks_all_of_indexed
  intro index hIndex
  simpa [sevenNineK4ChunkCheck] using hChunks index hIndex

set_option maxHeartbeats 0 in
-- Each wrapper compares one closed flatten certificate with its dependent type once.
theorem sevenNineK4BaseCheck_0_of_indexed_chunk_checks
    (hChunks : ∀ index, index < sevenNineK4BaseChunkCount 0 →
      sevenNineK4ChunkCheck 0 index = true) :
    sevenNineK4BaseCheck (sevenNineK4Bases.getD 0 []) = true :=
  sevenNineK4BaseCheck_of_indexed_chunk_checks 0
    sevenNineK4BaseChunks_flatten_0 hChunks

set_option maxHeartbeats 0 in
-- Each wrapper compares one closed flatten certificate with its dependent type once.
theorem sevenNineK4BaseCheck_1_of_indexed_chunk_checks
    (hChunks : ∀ index, index < sevenNineK4BaseChunkCount 1 →
      sevenNineK4ChunkCheck 1 index = true) :
    sevenNineK4BaseCheck (sevenNineK4Bases.getD 1 []) = true :=
  sevenNineK4BaseCheck_of_indexed_chunk_checks 1
    sevenNineK4BaseChunks_flatten_1 hChunks

set_option maxHeartbeats 0 in
-- Each wrapper compares one closed flatten certificate with its dependent type once.
theorem sevenNineK4BaseCheck_2_of_indexed_chunk_checks
    (hChunks : ∀ index, index < sevenNineK4BaseChunkCount 2 →
      sevenNineK4ChunkCheck 2 index = true) :
    sevenNineK4BaseCheck (sevenNineK4Bases.getD 2 []) = true :=
  sevenNineK4BaseCheck_of_indexed_chunk_checks 2
    sevenNineK4BaseChunks_flatten_2 hChunks

set_option maxHeartbeats 0 in
-- Each wrapper compares one closed flatten certificate with its dependent type once.
theorem sevenNineK4BaseCheck_3_of_indexed_chunk_checks
    (hChunks : ∀ index, index < sevenNineK4BaseChunkCount 3 →
      sevenNineK4ChunkCheck 3 index = true) :
    sevenNineK4BaseCheck (sevenNineK4Bases.getD 3 []) = true :=
  sevenNineK4BaseCheck_of_indexed_chunk_checks 3
    sevenNineK4BaseChunks_flatten_3 hChunks

set_option maxHeartbeats 0 in
-- Each wrapper compares one closed flatten certificate with its dependent type once.
theorem sevenNineK4BaseCheck_4_of_indexed_chunk_checks
    (hChunks : ∀ index, index < sevenNineK4BaseChunkCount 4 →
      sevenNineK4ChunkCheck 4 index = true) :
    sevenNineK4BaseCheck (sevenNineK4Bases.getD 4 []) = true :=
  sevenNineK4BaseCheck_of_indexed_chunk_checks 4
    sevenNineK4BaseChunks_flatten_4 hChunks

set_option maxHeartbeats 0 in
-- The fixed-arity wrapper isolates all index elimination from generated imports.
theorem sevenNineK4BaseCheck_0_of_chunk_checks
    (h00 : sevenNineK4ChunkCheck 0 0 = true)
    (h01 : sevenNineK4ChunkCheck 0 1 = true)
    (h02 : sevenNineK4ChunkCheck 0 2 = true)
    (h03 : sevenNineK4ChunkCheck 0 3 = true)
    (h04 : sevenNineK4ChunkCheck 0 4 = true)
    (h05 : sevenNineK4ChunkCheck 0 5 = true)
    (h06 : sevenNineK4ChunkCheck 0 6 = true)
    (h07 : sevenNineK4ChunkCheck 0 7 = true)
    (h08 : sevenNineK4ChunkCheck 0 8 = true)
    (h09 : sevenNineK4ChunkCheck 0 9 = true)
    (h10 : sevenNineK4ChunkCheck 0 10 = true)
    (h11 : sevenNineK4ChunkCheck 0 11 = true)
    (h12 : sevenNineK4ChunkCheck 0 12 = true)
    (h13 : sevenNineK4ChunkCheck 0 13 = true)
    (h14 : sevenNineK4ChunkCheck 0 14 = true)
    (h15 : sevenNineK4ChunkCheck 0 15 = true)
    (h16 : sevenNineK4ChunkCheck 0 16 = true)
    (h17 : sevenNineK4ChunkCheck 0 17 = true)
    (h18 : sevenNineK4ChunkCheck 0 18 = true)
    (h19 : sevenNineK4ChunkCheck 0 19 = true)
    (h20 : sevenNineK4ChunkCheck 0 20 = true)
    (h21 : sevenNineK4ChunkCheck 0 21 = true)
    (h22 : sevenNineK4ChunkCheck 0 22 = true)
    (h23 : sevenNineK4ChunkCheck 0 23 = true)
    (h24 : sevenNineK4ChunkCheck 0 24 = true)
    (h25 : sevenNineK4ChunkCheck 0 25 = true)
    (h26 : sevenNineK4ChunkCheck 0 26 = true) :
    sevenNineK4BaseCheck (sevenNineK4Bases.getD 0 []) = true := by
  apply sevenNineK4BaseCheck_0_of_indexed_chunk_checks
  intro index hIndex
  have hIndex' : index < 27 := by
    simpa [sevenNineK4BaseChunkCount] using hIndex
  have hCases :
      index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
      index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 ∨
      index = 8 ∨ index = 9 ∨ index = 10 ∨ index = 11 ∨
      index = 12 ∨ index = 13 ∨ index = 14 ∨ index = 15 ∨
      index = 16 ∨ index = 17 ∨ index = 18 ∨ index = 19 ∨
      index = 20 ∨ index = 21 ∨ index = 22 ∨ index = 23 ∨
      index = 24 ∨ index = 25 ∨ index = 26 := by
    omega
  rcases hCases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 |
    h9 | h10' | h11' | h12' | h13' | h14' | h15' | h16' | h17' |
    h18' | h19' | h20' | h21' | h22' | h23' | h24' | h25' | h26'
  · subst index; exact h00
  · subst index; exact h01
  · subst index; exact h02
  · subst index; exact h03
  · subst index; exact h04
  · subst index; exact h05
  · subst index; exact h06
  · subst index; exact h07
  · subst index; exact h08
  · subst index; exact h09
  · subst index; exact h10
  · subst index; exact h11
  · subst index; exact h12
  · subst index; exact h13
  · subst index; exact h14
  · subst index; exact h15
  · subst index; exact h16
  · subst index; exact h17
  · subst index; exact h18
  · subst index; exact h19
  · subst index; exact h20
  · subst index; exact h21
  · subst index; exact h22
  · subst index; exact h23
  · subst index; exact h24
  · subst index; exact h25
  · subst index; exact h26

set_option maxHeartbeats 0 in
-- The fixed-arity wrapper isolates all index elimination from generated imports.
theorem sevenNineK4BaseCheck_1_of_chunk_checks
    (h00 : sevenNineK4ChunkCheck 1 0 = true)
    (h01 : sevenNineK4ChunkCheck 1 1 = true)
    (h02 : sevenNineK4ChunkCheck 1 2 = true)
    (h03 : sevenNineK4ChunkCheck 1 3 = true)
    (h04 : sevenNineK4ChunkCheck 1 4 = true)
    (h05 : sevenNineK4ChunkCheck 1 5 = true)
    (h06 : sevenNineK4ChunkCheck 1 6 = true)
    (h07 : sevenNineK4ChunkCheck 1 7 = true)
    (h08 : sevenNineK4ChunkCheck 1 8 = true) :
    sevenNineK4BaseCheck (sevenNineK4Bases.getD 1 []) = true := by
  apply sevenNineK4BaseCheck_1_of_indexed_chunk_checks
  intro index hIndex
  have hIndex' : index < 9 := by
    simpa [sevenNineK4BaseChunkCount] using hIndex
  have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
      index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 := by
    omega
  rcases hCases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · subst index; exact h00
  · subst index; exact h01
  · subst index; exact h02
  · subst index; exact h03
  · subst index; exact h04
  · subst index; exact h05
  · subst index; exact h06
  · subst index; exact h07
  · subst index; exact h08

set_option maxHeartbeats 0 in
-- The fixed-arity wrapper isolates all index elimination from generated imports.
theorem sevenNineK4BaseCheck_2_of_chunk_checks
    (h00 : sevenNineK4ChunkCheck 2 0 = true)
    (h01 : sevenNineK4ChunkCheck 2 1 = true)
    (h02 : sevenNineK4ChunkCheck 2 2 = true)
    (h03 : sevenNineK4ChunkCheck 2 3 = true)
    (h04 : sevenNineK4ChunkCheck 2 4 = true)
    (h05 : sevenNineK4ChunkCheck 2 5 = true)
    (h06 : sevenNineK4ChunkCheck 2 6 = true)
    (h07 : sevenNineK4ChunkCheck 2 7 = true)
    (h08 : sevenNineK4ChunkCheck 2 8 = true) :
    sevenNineK4BaseCheck (sevenNineK4Bases.getD 2 []) = true := by
  apply sevenNineK4BaseCheck_2_of_indexed_chunk_checks
  intro index hIndex
  have hIndex' : index < 9 := by
    simpa [sevenNineK4BaseChunkCount] using hIndex
  have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
      index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 := by
    omega
  rcases hCases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · subst index; exact h00
  · subst index; exact h01
  · subst index; exact h02
  · subst index; exact h03
  · subst index; exact h04
  · subst index; exact h05
  · subst index; exact h06
  · subst index; exact h07
  · subst index; exact h08

set_option maxHeartbeats 0 in
-- The fixed-arity wrapper isolates all index elimination from generated imports.
theorem sevenNineK4BaseCheck_3_of_chunk_checks
    (h00 : sevenNineK4ChunkCheck 3 0 = true)
    (h01 : sevenNineK4ChunkCheck 3 1 = true)
    (h02 : sevenNineK4ChunkCheck 3 2 = true)
    (h03 : sevenNineK4ChunkCheck 3 3 = true)
    (h04 : sevenNineK4ChunkCheck 3 4 = true)
    (h05 : sevenNineK4ChunkCheck 3 5 = true)
    (h06 : sevenNineK4ChunkCheck 3 6 = true)
    (h07 : sevenNineK4ChunkCheck 3 7 = true)
    (h08 : sevenNineK4ChunkCheck 3 8 = true) :
    sevenNineK4BaseCheck (sevenNineK4Bases.getD 3 []) = true := by
  apply sevenNineK4BaseCheck_3_of_indexed_chunk_checks
  intro index hIndex
  have hIndex' : index < 9 := by
    simpa [sevenNineK4BaseChunkCount] using hIndex
  have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
      index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 := by
    omega
  rcases hCases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · subst index; exact h00
  · subst index; exact h01
  · subst index; exact h02
  · subst index; exact h03
  · subst index; exact h04
  · subst index; exact h05
  · subst index; exact h06
  · subst index; exact h07
  · subst index; exact h08

set_option maxHeartbeats 0 in
-- The fixed-arity wrapper isolates all index elimination from generated imports.
theorem sevenNineK4BaseCheck_4_of_chunk_checks
    (h00 : sevenNineK4ChunkCheck 4 0 = true)
    (h01 : sevenNineK4ChunkCheck 4 1 = true)
    (h02 : sevenNineK4ChunkCheck 4 2 = true)
    (h03 : sevenNineK4ChunkCheck 4 3 = true)
    (h04 : sevenNineK4ChunkCheck 4 4 = true)
    (h05 : sevenNineK4ChunkCheck 4 5 = true)
    (h06 : sevenNineK4ChunkCheck 4 6 = true)
    (h07 : sevenNineK4ChunkCheck 4 7 = true)
    (h08 : sevenNineK4ChunkCheck 4 8 = true) :
    sevenNineK4BaseCheck (sevenNineK4Bases.getD 4 []) = true := by
  apply sevenNineK4BaseCheck_4_of_indexed_chunk_checks
  intro index hIndex
  have hIndex' : index < 9 := by
    simpa [sevenNineK4BaseChunkCount] using hIndex
  have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
      index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 := by
    omega
  rcases hCases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · subst index; exact h00
  · subst index; exact h01
  · subst index; exact h02
  · subst index; exact h03
  · subst index; exact h04
  · subst index; exact h05
  · subst index; exact h06
  · subst index; exact h07
  · subst index; exact h08

end AiMathLab.P0054.MiddleSevenNineK4Finite
