import Qhl.Register.Qubits
import Qhl.Gate.Phase
import Qhl.Gate.HeraldedBlock
import Qhl.Logic.PreCompute
import Qhl.Logic.Frame

/-!
# The standard two-qubit world `Bool`

The two-cell instance of the standard labelled qubit system
(`Qhl/Register/Qubits.lean`): the world `Bool` of two qubit cells — the
canonical fixture of every two-wire example (Bell, RUS) — with its product
states and their inner-product/norm algebra. Promoted from the RUS example
(ownership test: nothing here names a program, a Hoare triple or a particular
gate).

* `fam u v` — the cell-state family with `u` on the cell `false` and `v` on
  the cell `true`, and the two-wire product state `gv u v = prodV (fam u v)`
  (CoqQ `tenvm` on two cells).
* `gv_inner` (CoqQ `tenvm_dot`), `norm_gv` (CoqQ `tenvm_norm`), linearity of
  `gv` in its first factor, and the `Function.update` collapses
  `fam_update_a`/`fam_update_both` in the shape the one-site
  (`regLift_singleGate_prodV`) and two-site (`regLift_pairGate_prodV`) bridges
  produce.
* the named unit-norm and orthogonality instances `norm_gv_q0` …
  `inner_gv_q0_q1` that rank-one invariant algebra consumes.
* the reset channel of the cell `false` — the Kraus family `gKraus` of
  `a := ∣0⟩` (the library's `initKraus` at the cell set of `Reg.single false`),
  its classical index `idxA`, and the predicate transformer `dualInit_outerLM`
  on a rank-one two-wire projector.
-/

namespace Qhl.TwoQubits

open Qhl Finset
open scoped ComplexInnerProductSpace

/-- The two-cell state family with `u` on the cell `false` and `v` on the
cell `true`. -/
def fam (u v : 𝕢) : ∀ i : Bool, EuclideanSpace ℂ (QubitCells Bool i) :=
  fun i => bif i then v else u

@[simp] theorem fam_false (u v : 𝕢) : fam u v false = u := rfl
@[simp] theorem fam_true (u v : 𝕢) : fam u v true = v := rfl

/-- The two-wire product state `u ⊗ v` of the world. -/
noncomputable def gv (u v : 𝕢) : HS (QubitCells Bool) (univ : Finset Bool) :=
  prodV (QubitCells Bool) (fam u v)

/-- The two-element product over the world, pinned once. -/
theorem prod_univ_bool {M : Type*} [CommMonoid M] (f : ↥(univ : Finset Bool) → M) :
    ∏ i, f i = f ⟨true, mem_univ _⟩ * f ⟨false, mem_univ _⟩ := by
  rw [← Equiv.prod_comp (Equiv.subtypeUnivEquiv (fun x : Bool => mem_univ x)).symm,
    Fintype.prod_bool]
  rfl

theorem gv_apply (u v : 𝕢) (l : QIdx (QubitCells Bool) (univ : Finset Bool)) :
    gv u v l = v (l ⟨true, mem_univ _⟩) * u (l ⟨false, mem_univ _⟩) := by
  rw [gv, prodV_apply, prod_univ_bool]
  rfl

/-- CoqQ `tenvm_dot` on two cells: the product state multiplies the two
factors' inner products. -/
theorem gv_inner (u v u' v' : 𝕢) : ⟪gv u v, gv u' v'⟫ = ⟪v, v'⟫ * ⟪u, u'⟫ := by
  rw [gv, gv, prodV_inner (QubitCells Bool) (fam u v) (fam u' v'), prod_univ_bool]
  rfl

theorem gv_smul_left (c : ℂ) (u v : 𝕢) : gv (c • u) v = c • gv u v := by
  refine PiLp.ext fun l => ?_
  simp only [gv_apply, PiLp.smul_apply, smul_eq_mul]
  ring

theorem gv_add_left (u u' v : 𝕢) : gv (u + u') v = gv u v + gv u' v := by
  refine PiLp.ext fun l => ?_
  simp only [gv_apply, PiLp.add_apply]
  ring

theorem gv_smul_right (c : ℂ) (u v : 𝕢) : gv u (c • v) = c • gv u v := by
  refine PiLp.ext fun l => ?_
  simp only [gv_apply, PiLp.smul_apply, smul_eq_mul]
  ring

theorem gv_add_right (u v v' : 𝕢) : gv u (v + v') = gv u v + gv u v' := by
  refine PiLp.ext fun l => ?_
  simp only [gv_apply, PiLp.add_apply]
  ring

theorem norm_gv {u v : 𝕢} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) : ‖gv u v‖ = 1 :=
  norm_prodV_eq_one _ fun i => by cases i <;> simpa

theorem fam_update_a (u v u' : 𝕢) : Function.update (fam u v) false u' = fam u' v := by
  funext i
  cases i
  · exact Function.update_self _ _ _
  · exact Function.update_of_ne (by decide) _ _

theorem fam_update_both (u v u' v' : 𝕢) :
    Function.update (Function.update (fam u v) false u') true v' = fam u' v' := by
  funext i
  cases i
  · rw [Function.update_of_ne (by decide), fam_update_a]
    rfl
  · exact Function.update_self _ _ _

/-! ### The named unit-norm and orthogonality instances -/

theorem norm_gv_q0 {ψ : 𝕢} (hψ : ‖ψ‖ = 1) : ‖gv q0 ψ‖ = 1 := norm_gv norm_q0 hψ
theorem norm_gv_q1 {ψ : 𝕢} (hψ : ‖ψ‖ = 1) : ‖gv q1 ψ‖ = 1 := norm_gv norm_q1 hψ
theorem norm_gv_qplus {ψ : 𝕢} (hψ : ‖ψ‖ = 1) : ‖gv qplus ψ‖ = 1 := norm_gv norm_qplus hψ
theorem norm_gv_qminus {ψ : 𝕢} (hψ : ‖ψ‖ = 1) : ‖gv qminus ψ‖ = 1 := norm_gv norm_qminus hψ

theorem inner_gv_q0_q1 {ψ : 𝕢} : (⟪gv q0 ψ, gv q1 ψ⟫ : ℂ) = 0 := by
  rw [gv_inner, inner_q0_q1, mul_zero]

/-! ### The reset channel of the cell `false`

The Kraus description of the one-cell initialisation `a := ∣0⟩` on the cell
`false`, and its predicate transformer on a rank-one two-wire projector.
Nothing here names a program: only the register `Reg.single false` and
generic kets appear. -/

/-- The Kraus family of `a := ∣0⟩`, on the whole world — the library's
`initKraus` (`Qhl/Logic/PreCompute.lean`) at the cell set of the cell
`false`. -/
noncomputable abbrev gKraus (x : QIdx (QubitCells Bool) (Reg.single false).sig) :
    EndM (QubitCells Bool) (univ : Finset Bool) :=
  initKraus (QubitCells Bool) (Reg.single false).sig x

theorem initLift_regA :
    initLift (D := QubitCells Bool) (Reg.single false).sig
      = kraussoOf (QubitCells Bool) gKraus :=
  initLift_eq_kraussoOf (Reg.single false).sig

/-- The classical states of the cell-`false` register, indexed by the bit they
carry. -/
noncomputable def idxA : Bool ≃ QIdx (QubitCells Bool) (Reg.single false).sig where
  toFun b := Reg.singleIdx (QubitCells Bool) false b
  invFun x := x ⟨false, Reg.self_mem_sig_single false⟩
  left_inv b := Reg.singleIdx_at (QubitCells Bool) false _ b
  right_inv x := Reg.idxEquiv_single_const (QubitCells Bool) false _ x

theorem deltav_idxA (b : Bool) :
    deltav (QubitCells Bool) (idxA b) = singleIso (QubitCells Bool) false (qbit b) :=
  (singleIso_single (QubitCells Bool) false b).symm

theorem default_eq_idxA :
    (default : QIdx (QubitCells Bool) (Reg.single false).sig) = idxA false :=
  (Reg.idxEquiv_single_const (QubitCells Bool) false
    (Reg.self_mem_sig_single false) default).symm

/-- The dual Kraus operator, in the one-site form the product-state bridge
consumes. -/
theorem adjoint_gKraus (b : Bool) :
    LinearMap.adjoint (gKraus (idxA b))
      = liftF (QubitCells Bool) (subset_univ (Reg.single false).sig)
          (singleOp (QubitCells Bool) false (outerLM (qbit b) q0)) := by
  rw [gKraus, initKraus, adjoint_liftF (QubitCells Bool) (subset_univ (Reg.single false).sig)
      (outerLM (deltav (QubitCells Bool)
          (default : QIdx (QubitCells Bool) (Reg.single false).sig))
        (deltav (QubitCells Bool) (idxA b)))]
  rw [adjoint_outerLM, default_eq_idxA, deltav_idxA, deltav_idxA, singleOp,
    conj_isometryEquiv_outerLM]
  rfl

theorem adjoint_gKraus_gv (b : Bool) (u v : 𝕢) :
    LinearMap.adjoint (gKraus (idxA b)) (gv u v) = (⟪q0, u⟫ : ℂ) • gv (qbit b) v := by
  rw [adjoint_gKraus, gv, liftF_singleOp_prodV (QubitCells Bool) false (subset_univ _),
    fam_false, outerLM_apply, fam_update_a, ← gv_smul_left]
  rfl

/-- **The initialisation transformer on a rank-one projector**: resetting the
cell `false` turns `∣u ⊗ v⟩⟨u ⊗ v∣` into `|⟪0,u⟫|²` times the *decomposed*
effect `∣0 ⊗ v⟩⟨0 ⊗ v∣ + ∣1 ⊗ v⟩⟨1 ⊗ v∣`. -/
theorem dualInit_outerLM (u v : 𝕢) :
    dualSO (QubitCells Bool) (initLift (D := QubitCells Bool) (Reg.single false).sig)
        (outerLM (gv u v) (gv u v))
      = ((⟪q0, u⟫ : ℂ) * star (⟪q0, u⟫ : ℂ)) •
          (outerLM (gv q0 v) (gv q0 v) + outerLM (gv q1 v) (gv q1 v)) := by
  rw [initLift_regA, dualSO_kraussoOf, kraussoOf_apply]
  rw [← Equiv.sum_comp idxA fun x : QIdx (QubitCells Bool) (Reg.single false).sig =>
    LinearMap.adjoint (gKraus x) ∘ₗ outerLM (gv u v) (gv u v)
      ∘ₗ LinearMap.adjoint (LinearMap.adjoint (gKraus x))]
  simp only [LinearMap.adjoint_adjoint, adjoint_comp_outerLM_comp, adjoint_gKraus_gv,
    outerLM_smul_self, Fintype.sum_bool, qbit_false, qbit_true]
  rw [smul_add]
  abel

/-! ### The pair-space presentation of the two-qubit world

The reindexing isometry `tq` between the pair space `EuclideanSpace ℂ
(Bool × Bool)` — where the two-wire gate algebra (`vpair`, `pairCtr`,
`Qhl/Gate/HeraldedBlock.lean`) lives — and the labelled whole-world space
`HS (QubitCells Bool) univ`, with `tq_vpair : tq (u ⊗ v) = gv u v`. Built from
the library transports `pairEnc` (`Qhl/Logic/Frame.lean`) and `castH`
(Decision H1: casts are reindexings, never `Eq.rec`). -/

/-- The two-cell pair register covers the whole world. -/
theorem sig_pair_univ :
    (Reg.pair false true Bool.false_ne_true).sig = (univ : Finset Bool) := by
  rw [Reg.sig_pair]
  decide

/-- The pair space `ℂ^{Bool × Bool}` as the labelled two-qubit world:
`pairEnc` followed by the cast along `{false, true} = univ`. -/
noncomputable def tq :
    EuclideanSpace ℂ (Bool × Bool) ≃ₗᵢ[ℂ] HS (QubitCells Bool) (univ : Finset Bool) :=
  (pairEnc (QubitCells Bool) false true Bool.false_ne_true).trans
    (castH (QubitCells Bool) sig_pair_univ)

/-- The transport of a pair vector is the two-wire product state. -/
theorem tq_vpair (u v : 𝕢) : tq (vpair u v) = gv u v := by
  rw [tq, LinearIsometryEquiv.trans_apply,
    show vpair u v = vpair (fam u v false) (fam u v true) from rfl,
    ← prodV_sig_pair false true Bool.false_ne_true (fam u v), castH_prodV]
  rfl

theorem tq_symm_gv (u v : 𝕢) : tq.symm (gv u v) = vpair u v := by
  rw [← tq_vpair, LinearIsometryEquiv.symm_apply_apply]

/-! ### The store-free ancilla measurement

The computational-basis measurement of the cell `false` and its whole-world
branch operators, promoted from the RUS example (ownership test: nothing here
names a program or a store — only the register `Reg.single false`). The
declarations are `protected` so that a file opening both this namespace and
the retained example namespace `Qhl.RUS` (which keeps its own copies) meets no
ambiguous names. -/

/-- The two outcomes as classical states of the ancilla register's tuple
space. -/
protected def outcomeEquiv : Fin 2 ≃ TIdx (QubitCells Bool) (Reg.single false).toFun :=
  finTwoEquiv.trans (Equiv.funUnique (Fin 1) Bool).symm

/-- The computational-basis measurement of the ancilla cell. -/
protected noncomputable def meas0 :
    QMeasure 2 (TSpace (QubitCells Bool) (Reg.single (false : Bool)).toFun) :=
  basisMeas TwoQubits.outcomeEquiv

/-- The two branch operators, unfolded once by `rfl`. -/
protected theorem meas0_M (i : Fin 2) :
    TwoQubits.meas0.M i
      = outerLM (EuclideanSpace.single (TwoQubits.outcomeEquiv i) (1 : ℂ))
          (EuclideanSpace.single (TwoQubits.outcomeEquiv i) (1 : ℂ)) := rfl

/-- The branch operator as the transported one-qubit projector `∣b⟩⟨b∣`. -/
protected theorem meas0_M_eq (i : Fin 2) :
    TwoQubits.meas0.M i
      = (tupleOne (QubitCells Bool) false).toLinearEquiv.conj
          (outerLM (qbit (finTwoEquiv i)) (qbit (finTwoEquiv i))) := by
  have h : (tupleOne (QubitCells Bool) false) (qbit (finTwoEquiv i))
      = EuclideanSpace.single (TwoQubits.outcomeEquiv i) (1 : ℂ) := by
    rw [qbit, tupleOne, euclCongr_single]
    rfl
  rw [TwoQubits.meas0_M, conj_isometryEquiv_outerLM, h]

protected theorem regA_op_meas0 (i : Fin 2) :
    (Reg.single false).op (QubitCells Bool) (TwoQubits.meas0.M i)
      = singleOp (QubitCells Bool) false
          (outerLM (qbit (finTwoEquiv i)) (qbit (finTwoEquiv i))) := by
  rw [TwoQubits.meas0_M_eq]
  exact reg_op_single (QubitCells Bool) false _

/-- The whole-world operator of the measurement branch `i`. -/
protected noncomputable def Kmeas (i : Fin 2) :
    EndM (QubitCells Bool) (univ : Finset Bool) :=
  regLift (Reg.single false) (TwoQubits.meas0.M i)

/-- The branch operator on a two-wire product state: it projects the ancilla
factor onto `∣b⟩` and leaves the data wire alone. -/
protected theorem Kmeas_gv (i : Fin 2) (u v : 𝕢) :
    TwoQubits.Kmeas i (gv u v)
      = (⟪qbit (finTwoEquiv i), u⟫ : ℂ) • gv (qbit (finTwoEquiv i)) v := by
  rw [TwoQubits.Kmeas, regLift, TwoQubits.regA_op_meas0, gv,
    liftF_singleOp_prodV (QubitCells Bool) false (subset_univ _), fam_false, outerLM_apply,
    fam_update_a, ← gv_smul_left]
  rfl

protected theorem adjoint_Kmeas (i : Fin 2) :
    LinearMap.adjoint (TwoQubits.Kmeas i) = TwoQubits.Kmeas i := by
  rw [TwoQubits.Kmeas, adjoint_regLift (Reg.single false) (TwoQubits.meas0.M i)]
  congr 1
  rw [TwoQubits.meas0_M, adjoint_outerLM]

/-- The rank-one conjugation identity of the (self-adjoint) branch operator:
the predicate transformer of the measurement on a rank-one effect is again
rank one. -/
protected theorem kmeas_conj_outer (i : Fin 2)
    (u v : HS (QubitCells Bool) (univ : Finset Bool)) :
    TwoQubits.Kmeas i ∘ₗ outerLM u v ∘ₗ TwoQubits.Kmeas i
      = outerLM (TwoQubits.Kmeas i u) (TwoQubits.Kmeas i v) := by
  nth_rewrite 1 [← TwoQubits.adjoint_Kmeas i]
  rw [adjoint_comp_outerLM_comp, TwoQubits.adjoint_Kmeas]

protected theorem Kmeas_complete :
    LinearMap.adjoint (TwoQubits.Kmeas 0) ∘ₗ TwoQubits.Kmeas 0
      + LinearMap.adjoint (TwoQubits.Kmeas 1) ∘ₗ TwoQubits.Kmeas 1 = 1 := by
  have h := isQMeasure_regLift (Reg.single false) TwoQubits.meas0
  rw [IsQMeasure, Fin.sum_univ_two] at h
  exact h

protected theorem Kmeas_zero_gv_q0 (v : 𝕢) :
    TwoQubits.Kmeas 0 (gv q0 v) = gv q0 v := by
  rw [TwoQubits.Kmeas_gv, show finTwoEquiv 0 = false from rfl, qbit_false, inner_q0_q0,
    one_smul]

protected theorem Kmeas_one_gv_q0 (v : 𝕢) : TwoQubits.Kmeas 1 (gv q0 v) = 0 := by
  rw [TwoQubits.Kmeas_gv, show finTwoEquiv 1 = true from rfl, qbit_true, inner_q1_q0,
    zero_smul]

protected theorem Kmeas_one_gv_q1 (v : 𝕢) :
    TwoQubits.Kmeas 1 (gv q1 v) = gv q1 v := by
  rw [TwoQubits.Kmeas_gv, show finTwoEquiv 1 = true from rfl, qbit_true, inner_q1_q1,
    one_smul]

/-! ### The reset channel on an arbitrary rank-one projector

`dualInit_outerLM` above handles a *product* rank-one `∣u ⊗ v⟩⟨u ⊗ v∣`. The
backward chain of a heralded attempt block meets rank-ones of arbitrary —
entangled — two-wire vectors `ξ`, so the general form is needed: the data-wire
remnant is the ancilla-`∣0⟩` contraction `pairCtr q0 (tq.symm ξ)`
(`Qhl/Gate/HeraldedBlock.lean`), and the reset decomposes the projector over
the two ancilla basis states exactly as in the product case. -/

/-- The dual Kraus operator of the reset on an arbitrary two-wire vector: only
the ancilla-`∣0⟩` row survives, transplanted to the ancilla state `∣b⟩`. -/
theorem adjoint_gKraus_apply (b : Bool) (ξ : HS (QubitCells Bool) (univ : Finset Bool)) :
    LinearMap.adjoint (gKraus (idxA b)) ξ = gv (qbit b) (pairCtr q0 (tq.symm ξ)) := by
  have hy : pairCtr q0 (tq.symm ξ) = rowVec false (tq.symm ξ) := by
    rw [← qbit_false, pairCtr_qbit]
  have hξ : ξ = gv q0 (rowVec false (tq.symm ξ)) + gv q1 (rowVec true (tq.symm ξ)) := by
    conv_lhs => rw [← tq.apply_symm_apply ξ, vpair_rowVec_decomp (tq.symm ξ)]
    rw [map_add, tq_vpair, tq_vpair]
  rw [hy]
  conv_lhs => rw [hξ]
  rw [map_add, adjoint_gKraus_gv, adjoint_gKraus_gv, inner_q0_q0, inner_q0_q1, one_smul,
    zero_smul, add_zero]

/-- **The initialisation transformer on an arbitrary rank-one projector**:
resetting the cell `false` turns `∣ξ⟩⟨ξ∣` into the decomposed effect
`∣0 ⊗ y⟩⟨0 ⊗ y∣ + ∣1 ⊗ y⟩⟨1 ⊗ y∣` of the surviving data-wire vector
`y = (⟨0∣ ⊗ 1)(tq⁻¹ ξ)`. On a product `ξ = u ⊗ v` this is `dualInit_outerLM`
(`y = ⟪0,u⟫ • v`). -/
theorem dualInit_outer_general (ξ : HS (QubitCells Bool) (univ : Finset Bool)) :
    dualSO (QubitCells Bool) (initLift (D := QubitCells Bool) (Reg.single false).sig)
        (outerLM ξ ξ)
      = outerLM (gv q0 (pairCtr q0 (tq.symm ξ))) (gv q0 (pairCtr q0 (tq.symm ξ)))
        + outerLM (gv q1 (pairCtr q0 (tq.symm ξ))) (gv q1 (pairCtr q0 (tq.symm ξ))) := by
  rw [initLift_regA, dualSO_kraussoOf, kraussoOf_apply]
  rw [← Equiv.sum_comp idxA fun x : QIdx (QubitCells Bool) (Reg.single false).sig =>
    LinearMap.adjoint (gKraus x) ∘ₗ outerLM ξ ξ
      ∘ₗ LinearMap.adjoint (LinearMap.adjoint (gKraus x))]
  simp only [LinearMap.adjoint_adjoint, adjoint_comp_outerLM_comp, adjoint_gKraus_apply,
    Fintype.sum_bool, qbit_false, qbit_true]
  abel

end Qhl.TwoQubits
