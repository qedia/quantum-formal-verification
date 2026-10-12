import Qhl.Examples.HubbardLCUFullPredicate
import Qhl.Examples.HubbardQSPFullPredicate

/-! Exact success expectations for arbitrary system effects on the initialized
LCU and actual BK-QSP programs. Complementary source derivations provide equality,
not merely a lower bound from one total-correctness judgment. -/
namespace Qhl.HubbardLCUPredicate
open Qhl Qhl.HubbardLCU Qhl.HubbardQSP Qhl.HubbardLCUSuccess Qhl.BravyiKitaev Finset
variable (x : ℕ) (hx : 0 < x)
variable (K : EndM (QubitCells (SysL x)) (univ : Finset (SysL x))) (hK : IsEffect K)

/-- Exact initialized LCU expectation for the computed Hamiltonian predicate,
including cross-eigenspace system effects and arbitrary input density operators. -/
theorem lcuPredicate_exact (s : CQState STc (QubitCells (WL x)))
    (hlam : 0 < lam x (coef s.cls)) :
    PostH (Config.init (lcuInitProg x hx) s) (predicatePost x K hK).op =
      expectE (fun σ => sysLift (L₂ := AncL x) (predicateBlock x K (coef σ))) s := by
  let M := (predicatePost x K hK).op (0, 0, 0, 0)
  let hM : IsEffect M := (predicatePost x K hK).isEffect (0, 0, 0, 0)
  have hw : HubbardLCUFullPredicate.wpLCU x hx M hM = wpLCU x hx K hK := by
    apply Assn.ext
    funext σ
    rw [HubbardLCUFullPredicate.wpLCU_op, wpLCU_op]
    rfl
  have h := HubbardLCUFullPredicate.exact_expectation x hx M hM s
  change PostH (Config.init (lcuInitProg x hx) s) (predicatePost x K hK).op = _ at h
  rw [h]
  apply expectE_congr_cls
  change ((HubbardLCUFullPredicate.wpLCU x hx M hM).initPre (fun _ => ancS x)).op s.cls = _
  rw [hw]
  exact initWp_op x hx K hK s.cls hlam

end Qhl.HubbardLCUPredicate

namespace Qhl.HubbardQSPPredicates
open Qhl Qhl.HubbardLCU Qhl.HubbardQSP Qhl.HubbardQSPSuccess Finset
variable (x : ℕ) (hx : 0 < x) (d : ℕ)
variable (K : EndM (QubitCells (SysL x)) (univ : Finset (SysL x))) (hK : IsEffect K)

/-- The initialized QSP loop has the exact computed expectation for every system effect. -/
theorem predicate_exact (s : CQState (STQc d) (QubitCells (WL x))) :
    PostH (Config.init (qspInitProg x hx d) s) (post x d K hK).op =
      expectE (pre x hx d K hK).op s :=
  HubbardQSPFullPredicate.exact_expectation x hx d
    ((post x d K hK).op s.cls) ((post x d K hK).isEffect s.cls) s

end Qhl.HubbardQSPPredicates

namespace Qhl.HubbardQSPBK
open Qhl Qhl.HubbardLCU Qhl.HubbardQSP Qhl.HubbardQSPSuccess
open Qhl.HubbardLCUSuccess Qhl.BravyiKitaev Finset
variable (x : ℕ) (hx : 0 < x) (d : ℕ)
variable (K : EndM (QubitCells (SysL x)) (univ : Finset (SysL x))) (hK : IsEffect K)

/-- Exact initialized BK-QSP expectation at the already computed precondition. -/
theorem predicate_exact (s : CQState (STQc d) (QubitCells (WL x))) :
    PostH (Config.init (qspBKProg x hx d) s) (HubbardQSPPredicates.post x d K hK).op =
      expectE (pre x hx d K hK).op s := by
  exact HubbardQSPFullPredicate.bk_exact_expectation x hx d
    ((HubbardQSPPredicates.post x d K hK).op s.cls)
    ((HubbardQSPPredicates.post x d K hK).isEffect s.cls) s

/-- The exact expectation is B†F†KFB on arbitrary input density operators. -/
theorem predicate_exact_block (s : CQState (STQc d) (QubitCells (WL x))) :
    PostH (Config.init (qspBKProg x hx d) s) (HubbardQSPPredicates.post x d K hK).op =
      expectE (fun σ => sysLift (L₂ := AncL x)
        (LinearMap.adjoint (BKTransform.bkUnitary x).val ∘ₗ
          LinearMap.adjoint (HubbardQSPPredicates.block x hx d σ) ∘ₗ K ∘ₗ
          HubbardQSPPredicates.block x hx d σ ∘ₗ (BKTransform.bkUnitary x).val)) s := by
  rw [predicate_exact]
  exact expectE_congr_cls (pre_op x hx d K hK s.cls)

/-- Under the existing spectral hypotheses the actual BK-prefixed program has
exact readings B†PΦ†KPΦB, with the independently defined QSP polynomial. -/
theorem predicate_exact_spectralPolynomial {ι : Type*}
    (b : Module.Basis ι ℂ (HS (QubitCells (SysL x)) (univ : Finset (SysL x))))
    (e : ι → ℝ) (s : CQState (STQc d) (QubitCells (WL x)))
    (hlam : 0 < lam x (coefQ d s.cls)) (hnorm : ∀ i, ‖b i‖ = 1)
    (heig : ∀ i, hubbardOp x (coefQ d s.cls).1 (coefQ d s.cls).2 (b i) = (e i : ℂ) • b i)
    (hstrict : ∀ i, (e i / lam x (coefQ d s.cls)) ^ 2 < 1) :
    PostH (Config.init (qspBKProg x hx d) s) (HubbardQSPPredicates.post x d K hK).op =
      expectE (fun σ => sysLift (L₂ := AncL x)
        (LinearMap.adjoint (BKTransform.bkUnitary x).val ∘ₗ
          LinearMap.adjoint (HubbardQSPPredicates.spectralPolynomial x d b e σ) ∘ₗ K ∘ₗ
          HubbardQSPPredicates.spectralPolynomial x d b e σ ∘ₗ
          (BKTransform.bkUnitary x).val)) s := by
  rw [predicate_exact]
  exact expectE_congr_cls (pre_op_spectralPolynomial x hx d K hK b e s.cls
    hlam hnorm heig hstrict)

end Qhl.HubbardQSPBK

#print axioms Qhl.HubbardLCUPredicate.lcuPredicate_exact
#print axioms Qhl.HubbardQSPBK.predicate_exact
#print axioms Qhl.HubbardQSPBK.predicate_exact_block
#print axioms Qhl.HubbardQSPBK.predicate_exact_spectralPolynomial

#print axioms Qhl.HubbardQSPPredicates.predicate_exact
