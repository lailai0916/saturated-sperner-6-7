import AiMathLab.P0054MiddleSevenNineSevenSideBasics

/-!
# Finite checker for the six-row residual coupling

Lists are intentional here: repeated masks represent distinct parallel
actual points and must not be collapsed to a finset.
-/

namespace AiMathLab.P0054.MiddleSevenNineSixCouplingFinite

def threeMaskRank (mask : Nat) : Nat :=
  ((List.range 3).filter fun bit ↦ mask.testBit bit).length

def sixResidualProfiles : List (List Nat) :=
  [[1, 1, 2, 4, 6],
   [1, 1, 2, 5, 6],
   [1, 2, 3, 4, 5],
   [1, 2, 5, 6],
   [1, 3, 5, 6],
   [3, 5, 6]]

def sixResidualProfile (index : Nat) : List Nat :=
  sixResidualProfiles.getD index []

def sixShiftRightSupport (support : Nat) : Nat :=
  Nat.shiftLeft support 3

def sixJoinSupports (left right : Nat) : Nat :=
  Nat.lor left (sixShiftRightSupport right)

def sixPairCoverCount : List Nat → Nat
  | [] => 0
  | support :: supports =>
      (supports.filter fun other ↦ Nat.lor support other = 63).length +
        sixPairCoverCount supports

def sixRowCouplingAuxCheck : List Nat → List Nat → List Nat → Bool
  | [], right, accumulated =>
      decide (4 ≤ sixPairCoverCount
        ([7, 56] ++ accumulated ++ right.map sixShiftRightSupport))
  | leftSupport :: left, right, accumulated =>
      sixRowCouplingAuxCheck left right (leftSupport :: accumulated) &&
        (List.range right.length).all fun index ↦
          match right[index]? with
          | none => true
          | some rightSupport =>
              if threeMaskRank leftSupport + threeMaskRank rightSupport ≤ 4 then
                sixRowCouplingAuxCheck left (right.eraseIdx index)
                  (sixJoinSupports leftSupport rightSupport :: accumulated)
              else true

def sixRowCouplingCheck (left right : List Nat) : Bool :=
  sixRowCouplingAuxCheck (left ++ [7]) (right ++ [7]) []

inductive SixRowCouplingGeneratedAux :
    List Nat → List Nat → List Nat → List Nat → Prop
  | nil (right accumulated) :
      SixRowCouplingGeneratedAux [] right accumulated
        ([7, 56] ++ accumulated ++ right.map sixShiftRightSupport)
  | unmatched {leftSupport : Nat} {left right accumulated output : List Nat}
      (hGenerated : SixRowCouplingGeneratedAux left right
        (leftSupport :: accumulated) output) :
      SixRowCouplingGeneratedAux (leftSupport :: left) right accumulated output
  | matched {leftSupport rightSupport index : Nat}
      {left right accumulated output : List Nat}
      (hIndex : index < right.length)
      (hGet : right[index]? = some rightSupport)
      (hRank : threeMaskRank leftSupport + threeMaskRank rightSupport ≤ 4)
      (hGenerated : SixRowCouplingGeneratedAux left (right.eraseIdx index)
        (sixJoinSupports leftSupport rightSupport :: accumulated) output) :
      SixRowCouplingGeneratedAux (leftSupport :: left) right accumulated output

def SixRowCouplingGenerated
    (left right output : List Nat) : Prop :=
  SixRowCouplingGeneratedAux (left ++ [7]) (right ++ [7]) [] output

theorem sixRowCouplingAuxCheck_sound
    {left right accumulated output : List Nat}
    (hGenerated : SixRowCouplingGeneratedAux left right accumulated output)
    (hCheck : sixRowCouplingAuxCheck left right accumulated = true) :
    4 ≤ sixPairCoverCount output := by
  induction hGenerated with
  | nil right accumulated =>
      exact of_decide_eq_true (by
        simpa [sixRowCouplingAuxCheck] using hCheck)
  | @unmatched leftSupport left right accumulated output hGenerated ih =>
      change (_ && _) = true at hCheck
      have hParts := Bool.and_eq_true_iff.mp hCheck
      exact ih hParts.1
  | @matched leftSupport rightSupport index left right accumulated output
      hIndex hGet hRank hGenerated ih =>
      change (_ && _) = true at hCheck
      have hParts := Bool.and_eq_true_iff.mp hCheck
      have hBranch := List.all_eq_true.mp hParts.2 index
        (List.mem_range.mpr hIndex)
      have hRecursive : sixRowCouplingAuxCheck left (right.eraseIdx index)
          (sixJoinSupports leftSupport rightSupport :: accumulated) = true := by
        simpa [hGet, hRank] using hBranch
      exact ih hRecursive

theorem sixRowCouplingCheck_sound
    {left right output : List Nat}
    (hGenerated : SixRowCouplingGenerated left right output)
    (hCheck : sixRowCouplingCheck left right = true) :
    4 ≤ sixPairCoverCount output := by
  exact sixRowCouplingAuxCheck_sound hGenerated hCheck

def sixRowCouplingCertificateCheck : Bool :=
  (List.range 6).all fun leftIndex ↦
    (List.range 6).all fun rightIndex ↦
      sixRowCouplingCheck (sixResidualProfile leftIndex)
        (sixResidualProfile rightIndex)

end AiMathLab.P0054.MiddleSevenNineSixCouplingFinite
