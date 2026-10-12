import Qhl.Examples.HubbardQSPSpectral
import Qhl.Logic.Source.Nonvacuity

/-! # A strict-spectrum, positive-depth witness for the literal BK-QSP example -/
namespace Qhl.HubbardQSPNonvacuity
open Finset BravyiKitaev HubbardLCU HubbardQSP HubbardQSPSuccess
open HubbardQSPSpectral
open scoped ComplexInnerProductSpace ComplexOrder

noncomputable def vacuum : WitnessSpace := bkKet 1 ![false, false]

theorem vacuum_norm : ‖vacuum‖ = 1 := by
  apply norm_eq_one_of_inner_self
  exact (dv_dot (QubitCells (SysL 1)) _ _).trans (if_pos rfl)

theorem vacuum_eig : hubbardOp 1 1 1 vacuum = (0 : ℂ) • vacuum := by
  simpa [vacuum] using hubbard_one_apply false false

/-- Both couplings are nonzero and the loop executes twice with zero phases. -/
def store : STQc 2 := ((0, 0, (1, 1)), (fun _ => 0), 0)

noncomputable def input : WitnessSpace :=
  LinearMap.adjoint (BKTransform.bkUnitary 1).val vacuum

theorem input_norm : ‖input‖ = 1 :=
  norm_eq_one_of_isUnitary (BKTransform.bkUnitary 1).isUnitary.adjoint vacuum_norm

theorem bk_input : (BKTransform.bkUnitary 1).val input = vacuum := by
  have h := congrArg (fun T => T vacuum) (BKTransform.bkUnitary 1).isUnitary.2
  exact h

private theorem block_eigen (x : ℕ) (hx : 0 < x) (d : ℕ) (σ : STQc d)
    (v : HS (QubitCells (SysL x)) (univ : Finset (SysL x))) (hv : ‖v‖ = 1)
    (E : ℝ) (hlam : 0 < lam x (coefQ d σ))
    (he : hubbardOp x (coefQ d σ).1 (coefQ d σ).2 v = (E : ℂ) • v)
    (hs : (E / lam x (coefQ d σ)) ^ 2 < 1) :
    HubbardQSPPredicates.block x hx d σ v =
      Qubitization.qspPoly (E / lam x (coefQ d σ)) (phiSeq d (phis d σ)) d • v := by
  change LinearMap.adjoint (sysEmb x)
    (Qubitization.passProd _ _ _ _ 0 d (sysEmb x v)) = _
  rw [Qubitization.passProd_emb]
  exact Qubitization.emb_adj_qspIter
    (hubbard_qubitization x hx (coefQ d σ) hlam v hv E he) hs _ d

theorem block_vacuum :
    HubbardQSPPredicates.block 1 (by decide) 2 store vacuum = -vacuum := by
  rw [block_eigen 1 (by decide) 2 store vacuum vacuum_norm 0
    (by change 0 < lam 1 (1, 1); rw [lam_one_one]; norm_num)
    vacuum_eig (by norm_num), zero_div]
  have hp : Qubitization.qspPoly 0 (phiSeq 2 (phis 2 store)) 2 = -1 := by
    change Qubitization.qspPoly 0 (phiSeq 2 (fun _ => 0)) (2 * 1) = -1
    rw [phiSeq_zero, Qubitization.qspPoly_zero_even]
    norm_num
  rw [hp, neg_one_smul]

private theorem pre_expect_block (x : ℕ) (hx : 0 < x) (d : ℕ) (σ : STQc d)
    (v : HS (QubitCells (SysL x)) (univ : Finset (SysL x))) :
    expectE (HubbardQSPBK.pre x hx d 1 isEffect_one).op
      ⟨σ, PDensity.pure (sysEmb x v)⟩ =
      ENNReal.ofReal (‖HubbardQSPPredicates.block x hx d σ
        ((BKTransform.bkUnitary x).val v)‖ ^ 2) := by
  rw [expectE_pure, HubbardQSPBK.pre_op]
  change ENNReal.ofReal (⟪ancEmbed (anc0 x) v,
    sysLift _ (ancEmbed (anc0 x) v)⟫ : ℂ).re = _
  rw [inner_emb_sysLift]
  simp only [LinearMap.comp_apply, Module.End.one_apply,
    LinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- The actual initialized BK-QSP precondition at K=I has expectation one. -/
theorem pre_expect_one :
    expectE (HubbardQSPBK.pre 1 (by decide) 2 1 isEffect_one).op
      ⟨store, PDensity.pure (sysEmb 1 input)⟩ = 1 := by
  rw [pre_expect_block, bk_input, block_vacuum, norm_neg, vacuum_norm]
  norm_num

/-- All spectral premises hold at the same positive-expectation input. -/
theorem source_nonvacuous :
    let φ : STQc 2 → Prop := fun σ =>
      0 < lam 1 (coefQ 2 σ) ∧
      (∀ i, hubbardOp 1 (coefQ 2 σ).1 (coefQ 2 σ).2 (witnessBasis i) =
        (witnessEigenvalues i : ℂ) • witnessBasis i) ∧
      (∀ i, (witnessEigenvalues i / lam 1 (coefQ 2 σ)) ^ 2 < 1)
    let A := SourceAssertion.ofAssn (HubbardQSPBK.pre 1 (by decide) 2 1 isEffect_one) φ
    ∃ s : CQState (STQc 2) (QubitCells (WL 1)),
      A.classical s.cls ∧ A.defined s.cls ∧ s.q.mass = 1 ∧
        0 < expectE A.quantum.op s := by
  refine ⟨⟨store, PDensity.pure (sysEmb 1 input)⟩, ?_, trivial, ?_, ?_⟩
  · exact ⟨by change 0 < lam 1 (1, 1); rw [lam_one_one]; norm_num,
      witness_eig, witness_strict⟩
  · apply PDensity.mass_pure
    exact norm_inS 1 input input_norm
  · change 0 < expectE (HubbardQSPBK.pre 1 (by decide) 2 1 isEffect_one).op _
    rw [pre_expect_one]
    exact zero_lt_one

end Qhl.HubbardQSPNonvacuity
#print axioms Qhl.HubbardQSPNonvacuity.source_nonvacuous
