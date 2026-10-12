import Qhl.Logic.Source.Nonvacuity
import Qhl.Examples.BoundedRUSTriple
import Qhl.Examples.HubbardLCUPredicate
import Qhl.Examples.QFTClassicalTriple

/-! # Non-vacuity of stored-input and effect-valued source preconditions -/
namespace Qhl.ExampleNonvacuity
open Finset
open scoped ComplexInnerProductSpace ComplexOrder

/-- The actual stored-bound RUS success precondition has a positive input at N=1. -/
theorem rusStoredSuccess (ψ : 𝕢) (hψ : ‖ψ‖ = 1) :
    let A := HeraldedRUS.ClassicalInput.preQ betaPS
      BoundedRUS.norm_betaPS_le_one ψ hψ
    ∃ s : CQState HeraldedRUS.ClassicalInput.Store HeraldedRUS.D,
      A.classical s.cls ∧ A.defined s.cls ∧ 0 < expectE A.quantum.op s := by
  refine ⟨⟨(1, true, 0), (BoundedRUS.inputState ψ).q⟩, Nat.le_refl 1, trivial, ?_⟩
  change 0 < expectE
    (HeraldedRUS.heraldPreQ betaPS BoundedRUS.norm_betaPS_le_one 1 ψ hψ).op
    (BoundedRUS.inputState ψ)
  rw [BoundedRUS.boundedRusSuccessPre_expect hψ 1]
  norm_num

/-- The K=I member of the LCU predicate family reuses the positive success input. -/
theorem lcuPredicate (x : ℕ) (hx : 0 < x) :
    let A := HubbardLCUPredicate.predicatePre x hx 1 isEffect_one
    ∃ s : CQState HubbardLCU.STc (QubitCells (HubbardLCU.WL x)),
      A.classical s.cls ∧ A.defined s.cls ∧ 0 < expectE A.quantum.op s := by
  dsimp only
  rw [HubbardLCUPredicate.predicatePre_one]
  obtain ⟨g, hg⟩ := HubbardLCUSuccess.succPre_witness x hx
  refine ⟨⟨(0, 0, (0, 1)), PDensity.pure (HubbardQSP.sysEmb x
    (deltav (QubitCells (HubbardLCU.SysL x)) (qbIdx (HubbardLCU.SysL x) g)))⟩,
    HubbardLCUSuccess.lam_zero_one_pos x hx, trivial, ?_⟩
  rw [← HubbardLCUSuccess.Source.successPre_toAssn x hx,
    SourceAssertion.toAssn, expectE_mask_of_pos
      (show (HubbardLCUSuccess.Source.successPre x hx).classical
        (0, 0, (0, 1)) ∧ (HubbardLCUSuccess.Source.successPre x hx).defined
        (0, 0, (0, 1)) from ⟨HubbardLCUSuccess.lam_zero_one_pos x hx, trivial⟩)] at hg
  exact hg

/-- The arbitrary-input QFT source precondition accepts its intended input. -/
theorem qftArbitrary (n : ℕ) (ψ : HS (QubitD n) univ) (hψ : ‖ψ‖ = 1) :
    let A := SourceAssertion.ofAssn (Assn.ofState ψ hψ)
      (fun _ : QFTClassicalTriple.Store n => True)
    ∃ s : CQState (QFTClassicalTriple.Store n) (QubitD n),
      A.classical s.cls ∧ A.defined s.cls ∧ s.q.mass = 1 ∧
        0 < expectE A.quantum.op s :=
  SourceAssertion.ofState_nonvacuous ψ hψ (fun _ => True) ((0, 0), fun _ => false) trivial

end Qhl.ExampleNonvacuity

#print axioms Qhl.ExampleNonvacuity.rusStoredSuccess
#print axioms Qhl.ExampleNonvacuity.lcuPredicate
#print axioms Qhl.ExampleNonvacuity.qftArbitrary
