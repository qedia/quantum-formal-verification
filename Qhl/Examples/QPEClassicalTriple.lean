import Qhl.Examples.InverseQFTClassicalTriple
import Qhl.Logic.PreservedMask

import Qhl.Examples.QPETriple
import Qhl.Logic.StateApproximation

/-! # Exact QPE with a read-only classical phase witness

The store contains the loop counter and a bit array `x`. The algorithm reads
only the counter: `x` is a specification witness, not an input controlling the
gates. The precondition tests the actual eigenrelation at the stored `x`.
-/
namespace Qhl.QPEClassicalTriple
open Finset QPETriple
open scoped ComplexInnerProductSpace ComplexOrder

abbrev Store (n : ℕ) := ℕ × (Fin n → Bool)
variable (n : ℕ) [NeZero n]

def counter : CounterLens (Store n) := CounterLens.fst _

def phReg : RegExpr (Store n) (QubitL (n + 1)) 1 := fun σ => phRegE n σ.1
noncomputable def phGate (σ : Store n) := QPETriple.phGate n σ.1
noncomputable def phCtrl : Prog (Store n) (QubitD (n + 1)) :=
  countedProg (counter n) (fun _ => n) (.unitary 1 (phReg n) (phGate n))
def kickReg : RegExpr (Store n) (QubitL (n + 1)) 2 := fun σ => kickRegE n σ.1
noncomputable def kickGate (U : UnitaryOp 𝕢) (σ : Store n) := QPETriple.kickGate n U σ.1
noncomputable def kickCir (U : UnitaryOp 𝕢) : Prog (Store n) (QubitD (n + 1)) :=
  countedProg (counter n) (fun _ => n) (.unitary 2 (kickReg n) (kickGate n U))

def iqftStore : StoreLens (Store n) (QFTClassicalTriple.Store n) where
  get σ := (Nat.unpair σ.1, σ.2)
  put _ τ := (Nat.pair τ.1.1 τ.1.2, τ.2)

omit [NeZero n] in
theorem iqftStore_get_put (σ : Store n) (τ : QFTClassicalTriple.Store n) :
    (iqftStore n).get ((iqftStore n).put σ τ) = τ := by
  simp [iqftStore, Nat.unpair_pair]

/-- Reuse the verified store-indexed inverse QFT on the counting register. -/
noncomputable def iqftCtrl : Prog (Store n) (QubitD (n + 1)) :=
  ((InverseQFTClassicalTriple.iqftRevCir n).mapStore (iqftStore n)).onReg (ctrlEmb n)

noncomputable def qpeCir (U : UnitaryOp 𝕢) : Prog (Store n) (QubitD (n + 1)) :=
  (phCtrl n).seq ((kickCir n U).seq (iqftCtrl n))

/-- Constructor-level equality proves that the phase witness never selects
any gate or guard. The algorithm is exactly the original QPE circuit. -/
theorem qpeCir_eq_mapStore (U : UnitaryOp 𝕢) :
    qpeCir n U = (QPETriple.qpeCir n U).mapStore StoreLens.fst := rfl

variable (U : UnitaryOp 𝕢) (ψ : 𝕢) (hψ : ‖ψ‖ = 1)

/-- The stored phase witness must satisfy the actual eigenrelation. -/
def eigen (σ : Store n) : Prop :=
  (U : 𝕢 →ₗ[ℂ] 𝕢) ψ =
    Complex.exp (((2 * Real.pi * ((natVal σ.2 : ℝ) / 2 ^ n) : ℝ) : ℂ) * Complex.I) • ψ

noncomputable def initial : Assn (Store n) (QubitD (n + 1)) :=
  prodA (QubitD (n + 1)) (qpeInitFam n ψ) (norm_qpeInitFam n ψ hψ)
noncomputable def plus : Assn (Store n) (QubitD (n + 1)) :=
  prodA (QubitD (n + 1)) (qpePlusFam n ψ) (norm_qpePlusFam n ψ hψ)
noncomputable def phased : Assn (Store n) (QubitD (n + 1)) :=
  Assn.ofStateFam (fun σ => prodV (QubitD (n + 1)) (W := univ) (qpePhasedFam n σ.2 ψ))
    (fun σ => norm_prodV_eq_one _ (norm_qpePhasedFam n σ.2 ψ hψ))
noncomputable def output : Assn (Store n) (QubitD (n + 1)) :=
  Assn.ofStateFam (fun σ => prodV (QubitD (n + 1)) (W := univ) (qpeOutFam n σ.2 ψ))
    (fun σ => norm_prodV_eq_one _ (norm_qpeOutFam n σ.2 ψ hψ))

theorem ph_preserves_input : (phCtrl n).Preserves (fun σ => σ.2) := by
  simp [phCtrl, countedProg, Prog.Preserves, counter, CounterLens.fst]

/-- The imported Hadamard subroutine carries the actual eigenrelation mask. -/
theorem phDeriv :
    DerivTot ((initial n ψ hψ).mask (eigen n U ψ)) (phCtrl n)
      ((plus n ψ hψ).mask (eigen n U ψ)) := by
  have hd := (QPETriple.phDeriv n ψ hψ).mapStore_pull
    (StoreLens.fst (R := Fin n → Bool)) (fun _ _ => rfl)
  have hm := hd.mask_preserved (eigen n U ψ)
    ((ph_preserves_input n).comp (fun x => eigen n U ψ (0, x)))
  refine DerivTot.conseq (Assn.le_refl' _) hm ?_
  intro σ
  by_cases he : eigen n U ψ σ
  · rw [Assn.mask_op_of_pos he, Assn.mask_op_of_pos he]
    change ((prodA (QubitD (n + 1)) (qpePlusFam n ψ)
      (norm_qpePlusFam n ψ hψ)).mask (fun k : ℕ => k = n)).op σ.1 ≤ _
    by_cases hk : σ.1 = n
    · rw [Assn.mask_op_of_pos (φ := fun k : ℕ => k = n) (σ := σ.1) hk]
      exact le_rfl
    · rw [Assn.mask_op_of_neg (φ := fun k : ℕ => k = n) (σ := σ.1) hk]
      exact ((plus n ψ hψ).isEffect σ).1
  · rw [Assn.mask_op_of_neg he, Assn.mask_op_of_neg he]

/-- The kickback invariant evaluates the stored witness. The eigenrelation
needed by each gate action comes from the classical mask of this derivation. -/
theorem kickDeriv :
    DerivTot ((plus n ψ hψ).mask (eigen n U ψ)) (kickCir n U)
      ((phased n ψ hψ).mask (eigen n U ψ)) := by
  refine DerivTot.countedStateChainVarSource (counter n)
    (hv₀ := fun _ => norm_prodV_eq_one _ (norm_qpePlusFam n ψ hψ))
    (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (fun k σ => prodV (QubitD (n + 1)) (W := univ) (qpeKickFam n σ.2 ψ k))
    (fun k σ => norm_prodV_eq_one _ (norm_qpeKickFam n σ.2 ψ hψ k))
    (fun _ _ _ => rfl) ?_ ?_ ?_ ?_
  · intro σ _
    exact congrArg _ (qpeKickFam_zero n σ.2 ψ)
  · intro σ _
    exact congrArg _ (qpeKickFam_full n σ.2 ψ)
  · exact DerivTot.countedRung_pair_fam (kickReg n) (kickGate n U)
      (fun σ => qpeCell n σ.1) (fun _ => Fin.last n)
      (fun σ _ => qpeCell_ne_last n σ.1)
      (fun σ => control (U ^ 2 ^ (n - 1 - σ.1)))
      (fun σ => norm_qpeKickFam n σ.2 ψ hψ σ.1)
      (fun σ => norm_qpeKickFam n σ.2 ψ hψ (σ.1 + 1))
      (fun σ _ => ⟨(Reg.pair _ _ (qpeCell_ne_last n σ.1)).inj, rfl⟩)
      (fun σ hσ => by
        have hk : σ.1 < n := hσ.2
        refine ⟨phaseKet (qftAngle σ.2 (n - 1 - σ.1)), ψ, ?_, ?_⟩
        · have hctrl : qpeKickFam n σ.2 ψ σ.1 (qpeCell n σ.1) = qplus := by
            rw [qpeCell_of_lt n hk]
            exact qpeKickFam_ctrl n σ.2 ψ ⟨σ.1, hk⟩
          rw [hctrl, qpeKickFam_last n σ.2 ψ σ.1, ← phaseKet_zero,
            control_pow_vpair_phaseKet U hσ.1 (2 ^ (n - 1 - σ.1)) 0, zero_add,
            phaseKet_kick n σ.2 (show n - 1 - σ.1 < n by omega)]
        · rw [qpeCell_of_lt n hk]
          exact qpeKickFam_step n σ.2 ψ ⟨σ.1, hk⟩)
  · intro z
    exact DerivTot.unitary_identity_mask (kickReg n) (kickGate n U)
      (fun σ _ => (Reg.pair _ _ (qpeCell_ne_last n σ.1)).inj)


/-- The fixed target frame is independent of the phase witness. -/
noncomputable def targetFrame :=
  prodV (QubitD (n + 1)) (W := univ \ embRange (ctrlEmb n)) (qpeInitFam n ψ)

omit [NeZero n] in
include hψ in
theorem norm_targetFrame : ‖targetFrame n ψ‖ = 1 :=
  norm_prodV_eq_one _ (norm_qpeInitFam n ψ hψ)

omit [NeZero n] in
private theorem outside_target (i : Fin (n + 1)) (hi : i ∈ univ \ embRange (ctrlEmb n)) :
    i = Fin.last n := by
  have hns : ¬ (i : ℕ) < n := by
    intro hc
    exact (mem_sdiff.mp hi).2 (mem_map.mpr
      ⟨⟨i.val, hc⟩, mem_univ _, Fin.ext rfl⟩)
  exact Fin.ext (by have := i.isLt; simp; omega)

omit [NeZero n] in
/-- A pointwise endpoint identity using the existing constant-frame lemma.
Only the counting-register factors vary with the classical store. -/
private theorem frame_endpoint
    (f : Store n → Fin (n + 1) → 𝕢) (hf : ∀ σ i, ‖f σ i‖ = 1)
    (hout : ∀ σ, f σ (Fin.last n) = ψ) :
    (Assn.ofStateFam
      (fun σ => prodV (QubitD n) (W := univ) (fun j => f σ j.castSucc))
      (fun σ => norm_prodV_eq_one _ (fun j => hf σ j.castSucc))).embFrame
        (emb := ctrlEmb n) (outerLM (targetFrame n ψ) (targetFrame n ψ))
        (isEffect_outerLM_self (norm_targetFrame n ψ hψ)) =
      Assn.ofStateFam (fun σ => prodV (QubitD (n + 1)) (W := univ) (f σ))
        (fun σ => norm_prodV_eq_one _ (hf σ)) := by
  apply Assn.ext
  funext σ
  have he : targetFrame n ψ =
      prodV (QubitD (n + 1)) (W := univ \ embRange (ctrlEmb n)) (f σ) := by
    apply prodV_congr
    intro i hi
    rw [outside_target n i hi, hout σ]
    simp [qpeInitFam]
  change ((prodA (σT := Store n) (QubitD n) (fun j => f σ j.castSucc)
      (fun j => hf σ j.castSucc)).embFrame (emb := ctrlEmb n)
        (outerLM (targetFrame n ψ) (targetFrame n ψ))
        (isEffect_outerLM_self (norm_targetFrame n ψ hψ))).op σ =
    (prodA (QubitD (n + 1)) (f σ) (hf σ)).op σ
  simp only [he]
  exact congrArg (fun A : Assn (Store n) (QubitD (n + 1)) => A.op σ)
    (Assn.embFrame_prodA (ctrlEmb n) (f σ) (hf σ))

/-- Consume the new store-indexed inverse-QFT proof, with the target ket
preserved by the derived register frame rule. -/
theorem iqftCtrlDeriv :
    DerivTot (phased n ψ hψ) (iqftCtrl n) (output n ψ hψ) := by
  have hd := (InverseQFTClassicalTriple.iqftRevDeriv n).mapStore_pull
    (iqftStore n) (iqftStore_get_put n)
  have hf := hd.embFrame_onReg (emb := ctrlEmb n)
    (R := outerLM (targetFrame n ψ) (targetFrame n ψ))
    (hR := isEffect_outerLM_self (norm_targetFrame n ψ hψ))
  have hin : (QFTClassicalTriple.outputAssn n).pull (iqftStore n).get =
      Assn.ofStateFam
        (fun σ : Store n => prodV (QubitD n) (W := univ)
          (fun j => qpePhasedFam n σ.2 ψ j.castSucc))
        (fun σ => norm_prodV_eq_one _ (fun j => norm_qpePhasedFam n σ.2 ψ hψ j.castSucc)) := by
    apply Assn.ext
    funext σ
    simp only [Assn.pull_op, QFTClassicalTriple.outputAssn, Assn.ofStateFam_op,
      iqftStore, fourierState_eq_prodV]
    congr 1 <;> apply congrArg (prodV (QubitD n)) <;> funext j
      <;> exact (qpePhasedFam_castSucc n σ.2 ψ j).symm
  have hout : (QFTClassicalTriple.inputAssn n).pull (iqftStore n).get =
      Assn.ofStateFam
        (fun σ : Store n => prodV (QubitD n) (W := univ)
          (fun j => qpeOutFam n σ.2 ψ j.castSucc))
        (fun σ => norm_prodV_eq_one _ (fun j => norm_qpeOutFam n σ.2 ψ hψ j.castSucc)) := by
    apply Assn.ext
    funext σ
    simp only [Assn.pull_op, QFTClassicalTriple.inputAssn, Assn.ofStateFam_op,
      iqftStore, QFTClassicalTriple.basisState]
    congr 1 <;> apply congrArg (prodV (QubitD n)) <;> funext j
      <;> exact (qpeOutFam_castSucc n σ.2 ψ j).symm
  rw [hin, hout,
    frame_endpoint n ψ hψ (fun σ => qpePhasedFam n σ.2 ψ)
      (fun σ => norm_qpePhasedFam n σ.2 ψ hψ) (fun σ => qpePhasedFam_last n σ.2 ψ),
    frame_endpoint n ψ hψ (fun σ => qpeOutFam n σ.2 ψ)
      (fun σ => norm_qpeOutFam n σ.2 ψ hψ) (fun σ => qpeOutFam_last n σ.2 ψ)] at hf
  exact hf

/-- The exact QPE specification tests the stored phase witness. There is no
external eigenvalue hypothesis in this constructor derivation. -/
theorem qpeDeriv :
    DerivTot ((initial n ψ hψ).mask (eigen n U ψ)) (qpeCir n U) (output n ψ hψ) :=
  (phDeriv n U ψ hψ).seq ((kickDeriv n U ψ hψ).seq
    (DerivTot.conseq (Assn.mask_le_of_imp_le fun _ _ => le_rfl)
      (iqftCtrlDeriv n ψ hψ) (Assn.le_refl' _)))

theorem qpeValid :
    validTot ((initial n ψ hψ).mask (eigen n U ψ)) (qpeCir n U) (output n ψ hψ) :=
  (qpeDeriv n U ψ hψ).sound


/-- Every update preserves the witness, regardless of the quantum state. -/
theorem qpeCir_preserves_input : (qpeCir n U).Preserves (fun σ => σ.2) := by
  rw [qpeCir_eq_mapStore]
  generalize QPETriple.qpeCir n U = P
  induction P <;> simp_all [Prog.mapStore, Prog.Preserves, StoreLens.fst]

omit [NeZero n] in
/-- At fixed x, both quantum endpoint effects are those of the original QPE. -/
theorem initial_op (σ : Store n) :
    (initial n ψ hψ).op σ =
      (prodA (σT := ℕ) (QubitD (n + 1)) (qpeInitFam n ψ)
        (norm_qpeInitFam n ψ hψ)).op σ.1 := rfl

omit [NeZero n] in
theorem output_op (σ : Store n) :
    (output n ψ hψ).op σ =
      (prodA (σT := ℕ) (QubitD (n + 1)) (qpeOutFam n σ.2 ψ)
        (norm_qpeOutFam n σ.2 ψ hψ)).op σ.1 := rfl

omit [NeZero n] in
theorem precondition_op (σ : Store n) (he : eigen n U ψ σ) :
    ((initial n ψ hψ).mask (eigen n U ψ)).op σ =
      (prodA (σT := ℕ) (QubitD (n + 1)) (qpeInitFam n ψ)
        (norm_qpeInitFam n ψ hψ)).op σ.1 := by
  rw [Assn.mask_op_of_pos he]
  rfl

noncomputable def initialState (σ : Store n) : CQState (Store n) (QubitD (n + 1)) :=
  ⟨σ, ⟨outerLM (prodV (QubitD (n + 1)) (W := univ) (qpeInitFam n ψ))
    (prodV (QubitD (n + 1)) (W := univ) (qpeInitFam n ψ)), isPositive_outerLM_self _⟩⟩

omit [NeZero n] in
/-- Every admissible stored phase has a full-weight intended pure input. -/
theorem precondition_expect_one (σ : Store n) (he : eigen n U ψ σ) :
    expectE ((initial n ψ hψ).mask (eigen n U ψ)).op (initialState n ψ σ) = 1 := by
  have hn := norm_prodV_eq_one (W := univ) (qpeInitFam n ψ) (norm_qpeInitFam n ψ hψ)
  have hin : (⟪prodV (QubitD (n + 1)) (W := univ) (qpeInitFam n ψ),
      prodV (QubitD (n + 1)) (W := univ) (qpeInitFam n ψ)⟫ : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hn]
    norm_num
  rw [expectE, expect]
  simp only [initialState]
  rw [Assn.mask_op_of_pos he]
  simp only [initial, prodA_op, trace_outerLM_comp, outerLM_apply, inner_smul_right, hin]
  norm_num

omit [NeZero n] in
/-- Each counting output factor reads the corresponding stored bit. -/
theorem output_readout (σ : Store n) (j : Fin n) :
    qpeOutFam n σ.2 ψ j.castSucc = qbit (σ.2 j) := qpeOutFam_castSucc n σ.2 ψ j


omit [NeZero n] in
/-- A concrete admissible family: identity has exact zero eigenphase. -/
theorem identity_eigen (k : ℕ) : eigen n (1 : UnitaryOp 𝕢) ψ (k, fun _ => false) := by
  simp [eigen, natVal]

omit [NeZero n] in
/-- An actual full-weight input instance, not just conditional nonvacuity. -/
theorem identity_precondition_expect_one (k : ℕ) :
    expectE ((initial n ψ hψ).mask (eigen n (1 : UnitaryOp 𝕢) ψ)).op
      (initialState n ψ (k, fun _ => false)) = 1 :=
  precondition_expect_one n 1 ψ hψ _ (identity_eigen n ψ k)

end Qhl.QPEClassicalTriple

#print axioms Qhl.QPEClassicalTriple.qpeDeriv
#print axioms Qhl.QPEClassicalTriple.qpeValid
#print axioms Qhl.QPEClassicalTriple.precondition_expect_one
#print axioms Qhl.QPEClassicalTriple.qpeCir_eq_mapStore

#print axioms Qhl.QPEClassicalTriple.identity_precondition_expect_one

namespace Qhl.InverseQFTPlacedSource
open Finset QPETriple SourceDerivTot
namespace Stored
open QFTClassicalTriple InverseQFTClassicalTriple
variable (n : ℕ) [NeZero n]
variable (R : EndM (QubitD (n + 1)) (univ \ embRange (ctrlEmb n))) (hR : IsEffect R)

def stageCounter : CounterLens (QPEClassicalTriple.Store n) :=
  (QFTClassicalTriple.stageCounter n).pullback (QPEClassicalTriple.iqftStore n)
    (QPEClassicalTriple.iqftStore_get_put n)
def rungCounter : CounterLens (QPEClassicalTriple.Store n) :=
  (QFTClassicalTriple.rungCounter n).pullback (QPEClassicalTriple.iqftStore n)
    (QPEClassicalTriple.iqftStore_get_put n)
def swapReg : RegExpr (QPEClassicalTriple.Store n) (QubitL n) 2 :=
  fun σ => QFTClassicalTriple.swapReg n ((QPEClassicalTriple.iqftStore n).get σ)
noncomputable def swapGate (σ : QPEClassicalTriple.Store n) :=
  QFTClassicalTriple.swapGate n ((QPEClassicalTriple.iqftStore n).get σ)
def ihReg : RegExpr (QPEClassicalTriple.Store n) (QubitL n) 1 :=
  fun σ => InverseQFTClassicalTriple.ihReg n ((QPEClassicalTriple.iqftStore n).get σ)
noncomputable def ihGate (σ : QPEClassicalTriple.Store n) :=
  InverseQFTClassicalTriple.ihGate n ((QPEClassicalTriple.iqftStore n).get σ)
def iladReg : RegExpr (QPEClassicalTriple.Store n) (QubitL n) 2 :=
  fun σ => InverseQFTClassicalTriple.iladReg n ((QPEClassicalTriple.iqftStore n).get σ)
noncomputable def iladGate (σ : QPEClassicalTriple.Store n) :=
  InverseQFTClassicalTriple.iladGate n ((QPEClassicalTriple.iqftStore n).get σ)
noncomputable def revCirc : Prog (QPEClassicalTriple.Store n) (QubitD (n + 1)) :=
  ((QFTClassicalTriple.revCirc n).mapStore (QPEClassicalTriple.iqftStore n)).onReg (ctrlEmb n)
noncomputable def iqftSub : Prog (QPEClassicalTriple.Store n) (QubitD (n + 1)) :=
  ((InverseQFTClassicalTriple.iqftSub n).mapStore (QPEClassicalTriple.iqftStore n)).onReg
        (ctrlEmb n)
noncomputable def iqftIter : Prog (QPEClassicalTriple.Store n) (QubitD (n + 1)) :=
  ((InverseQFTClassicalTriple.iqftIter n).mapStore (QPEClassicalTriple.iqftStore n)).onReg
        (ctrlEmb n)
/-- The backward reversal reads the stored array in its invariant. -/
theorem revCircBack_deriv :
    SourceDerivTot
      (SourceAssertion.ofAssn (framedFam (ctrlEmb n) R hR
        (fun σ : QPEClassicalTriple.Store n => prodV
        (QubitD n) (W := univ)
          (iqftRevFamN n σ.2 0))
        (fun σ : QPEClassicalTriple.Store n => norm_prodV_eq_one _ (norm_iqftRevFamN n σ.2 0)))
        fun _ => True)
      (revCirc n)
      (SourceAssertion.ofAssn (framedFam (ctrlEmb n) R hR
        (fun σ : QPEClassicalTriple.Store n => prodV
        (QubitD n) (W := univ)
          (iqftRevFamN n σ.2 (n / 2)))
        (fun σ : QPEClassicalTriple.Store n =>
          norm_prodV_eq_one _ (norm_iqftRevFamN n σ.2 (n / 2)))) fun _ => True) := by
  refine framedCounted (ctrlEmb n) R hR (stageCounter n) (fun _ => n / 2) (fun _ => True)
    (by intros; simp [stageCounter, rungCounter, CounterLens.pullbackFst, CounterLens.pullback,
        StoreLens.fst, QPEClassicalTriple.iqftStore, QFTClassicalTriple.stageCounter,
        QFTClassicalTriple.rungCounter, CounterLens.fst, CounterLens.snd]) (by intros; simp
        [stageCounter, rungCounter, CounterLens.pullbackFst, CounterLens.pullback,
        StoreLens.fst, QPEClassicalTriple.iqftStore, QFTClassicalTriple.stageCounter,
        QFTClassicalTriple.rungCounter, CounterLens.fst, CounterLens.snd])
    (fun m σ => prodV (QubitD n) (W := univ) (iqftRevFamN n σ.2 m))
    (fun m σ => norm_prodV_eq_one _ (norm_iqftRevFamN n σ.2 m))
    (by intros; simp [stageCounter, rungCounter, CounterLens.pullbackFst, CounterLens.pullback,
        StoreLens.fst, QPEClassicalTriple.iqftStore, QFTClassicalTriple.stageCounter,
        QFTClassicalTriple.rungCounter, CounterLens.fst, CounterLens.snd]) (by intros; simp
        [stageCounter, rungCounter, CounterLens.pullbackFst, CounterLens.pullback,
        StoreLens.fst, QPEClassicalTriple.iqftStore, QFTClassicalTriple.stageCounter,
        QFTClassicalTriple.rungCounter, CounterLens.fst, CounterLens.snd]) (by intros; simp
        [stageCounter, rungCounter, CounterLens.pullbackFst, CounterLens.pullback,
        StoreLens.fst, QPEClassicalTriple.iqftStore, QFTClassicalTriple.stageCounter,
        QFTClassicalTriple.rungCounter, CounterLens.fst, CounterLens.snd]) ?_ ?_
  · exact framedPair (ctrlEmb n) R hR (swapReg n) (swapGate n)
      (fun σ => QFTTriple.ctrl n (Nat.unpair σ.1)) (fun σ => QFTTriple.mir n (Nat.unpair σ.1))
      (fun σ hσ => QFTTriple.ctrl_ne_mir n (σ := Nat.unpair σ.1) hσ.2) (fun _ => SWAP)
      (fun σ => norm_iqftRevFamN n σ.2 (Nat.unpair σ.1).1)
      (fun σ => norm_iqftRevFamN n σ.2 ((Nat.unpair σ.1).1 + 1))
      (fun σ hσ => by
        have hne := QFTTriple.ctrl_ne_mir n (σ := Nat.unpair σ.1) hσ.2
        refine ⟨(Reg.pair _ _ hne).inj, ?_⟩
        change regLift (D := QubitD n)
          ⟨QFTTriple.swapReg n (Nat.unpair σ.1), (Reg.pair _ _ hne).inj⟩
          (QFTTriple.swapGate n (Nat.unpair σ.1)) =
          regLift (D := QubitD n)
            (Reg.pair (QFTTriple.ctrl n (Nat.unpair σ.1)) (QFTTriple.mir n (Nat.unpair σ.1)) hne)
            (pairGate (D := QubitD n)
              (QFTTriple.ctrl n (Nat.unpair σ.1)) (QFTTriple.mir n (Nat.unpair σ.1)) hne SWAP)
        rw [show QFTTriple.swapGate n (Nat.unpair σ.1) = pairGate (D := QubitD n)
            (QFTTriple.ctrl n (Nat.unpair σ.1)) (QFTTriple.mir n (Nat.unpair σ.1)) hne SWAP
        from by
          simp only [QFTTriple.swapGate]; rw [dif_pos hne]]
        rfl)
      (fun σ hσ => by
        have hk : (Nat.unpair σ.1).1 < n / 2 := hσ.2
        have hc : QFTTriple.ctrl n (Nat.unpair σ.1) = cell n (Nat.unpair σ.1).1 := rfl
        have hm : QFTTriple.mir n (Nat.unpair σ.1) = cell n (n - 1 - (Nat.unpair σ.1).1) := rfl
        exact ⟨phaseKet (qftAngle σ.2 (Nat.unpair σ.1).1),
          phaseKet (qftAngle σ.2 (n - 1 - (Nat.unpair σ.1).1)),
          by rw [hc, hm, iqftRevFamN_left n σ.2 hk, iqftRevFamN_right n σ.2 hk, SWAP_vpair],
          by rw [hc, hm]; exact iqftRevFamN_step n σ.2 hk⟩)
  · intro z
    exact framedIdentity (ctrlEmb n) (swapReg n) (swapGate n) _ fun σ hσ =>
      (Reg.pair _ _ (QFTTriple.ctrl_ne_mir n (σ := Nat.unpair σ.1) hσ.2.1)).inj

/-- The inverse controlled-phase gate advances the decreasing ladder family. -/
private theorem iladder_action (σ : QPEClassicalTriple.Store n) (hk : (Nat.unpair σ.1).1 < n)
        (hj : (Nat.unpair σ.1).2 < (Nat.unpair σ.1).1) :
    ∃ hinj : Function.Injective (iladReg n σ),
      regLift (D := QubitD n) ⟨iladReg n σ, hinj⟩ (iladGate n σ)
        (prodV (QubitD n) (W := univ)
          (qftLadderFamN n σ.2 (n - 1 - (Nat.unpair σ.1).1) ((Nat.unpair σ.1).1 - (Nat.unpair
        σ.1).2))) =
        prodV (QubitD n) (W := univ)
          (qftLadderFamN n σ.2 (n - 1 - (Nat.unpair σ.1).1) ((Nat.unpair σ.1).1 - ((Nat.unpair
        σ.1).2 + 1))) := by
  have hne : InverseQFTTriple.ictrl n (Nat.unpair σ.1) ≠ InverseQFTTriple.itgt n (Nat.unpair
        σ.1) :=
    InverseQFTTriple.ictrl_ne_itgt n (σ := Nat.unpair σ.1) hk hj
  refine ⟨(Reg.pair _ _ hne).inj, ?_⟩
  rw [show regLift (D := QubitD n) ⟨iladReg n σ, (Reg.pair _ _ hne).inj⟩ (iladGate n σ)
      = regLift (D := QubitD n)
          (Reg.pair (InverseQFTTriple.ictrl n (Nat.unpair σ.1)) (InverseQFTTriple.itgt n
        (Nat.unpair σ.1)) hne)
          (pairGate (D := QubitD n) (InverseQFTTriple.ictrl n (Nat.unpair σ.1))
        (InverseQFTTriple.itgt n (Nat.unpair σ.1)) hne
            (cphase (-(2 * Real.pi / 2 ^ ((Nat.unpair σ.1).1 - 1 - (Nat.unpair σ.1).2 + 2)))))
        from by
    rw [show iladGate n σ = pairGate (D := QubitD n)
        (InverseQFTTriple.ictrl n (Nat.unpair σ.1)) (InverseQFTTriple.itgt n (Nat.unpair σ.1)) hne
        (cphase (-(2 * Real.pi / 2 ^ ((Nat.unpair σ.1).1 - 1 - (Nat.unpair σ.1).2 + 2)))) from by
      change InverseQFTTriple.iladGate n (Nat.unpair σ.1) = _
      simp only [InverseQFTTriple.iladGate]; rw [dif_pos hne]]
    rfl]
  exact regLift_cphase_neg_qftLadderFamN n σ.2 hk hj hne


theorem iqftSub_current {φ : QPEClassicalTriple.Store n → Prop}
    (hφ : ∀ σ v, φ ((rungCounter n).set σ v) ↔ φ σ)
    (hk : ∀ σ, φ σ → (Nat.unpair σ.1).1 < n) :
    SourceDerivTot
      (SourceAssertion.ofAssn (framedFam (ctrlEmb n) R hR (fun σ : QPEClassicalTriple.Store n =>
        prodV (QubitD n) (W := univ) (qftStageFam n σ.2 (n - (Nat.unpair σ.1).1)))
        (fun σ => norm_prodV_eq_one _ (norm_qftStageFam n σ.2 (n - (Nat.unpair σ.1).1)))) φ)
      (iqftSub n)
      (SourceAssertion.ofAssn (framedFam (ctrlEmb n) R hR (fun σ : QPEClassicalTriple.Store n =>
        prodV (QubitD n) (W := univ) (qftStageMidN n σ.2 (n - 1 - (Nat.unpair σ.1).1)))
        (fun σ => norm_prodV_eq_one _
          (norm_qftStageMidN n σ.2 (n - 1 - (Nat.unpair σ.1).1)))) φ) := by
    refine framedCounted (ctrlEmb n) R hR (rungCounter n)
      (fun σ => (Nat.unpair σ.1).1) φ hφ (by intros; simp [stageCounter, rungCounter,
        CounterLens.pullbackFst, CounterLens.pullback, StoreLens.fst,
        QPEClassicalTriple.iqftStore, QFTClassicalTriple.stageCounter,
        QFTClassicalTriple.rungCounter, CounterLens.fst, CounterLens.snd])
      (fun m σ => prodV (QubitD n) (W := univ)
        (qftLadderFamN n σ.2 (n - 1 - (Nat.unpair σ.1).1) ((Nat.unpair σ.1).1 - m)))
      (fun m σ => norm_prodV_eq_one _
        (norm_qftLadderFamN n σ.2 (n - 1 - (Nat.unpair σ.1).1) ((Nat.unpair σ.1).1 - m)))
      (by intros; simp [stageCounter, rungCounter, CounterLens.pullbackFst,
        CounterLens.pullback, StoreLens.fst, QPEClassicalTriple.iqftStore,
        QFTClassicalTriple.stageCounter, QFTClassicalTriple.rungCounter, CounterLens.fst,
        CounterLens.snd]) ?_ ?_ ?_ ?_
    · intro σ hσ
      apply congrArg
      have hlt := hk σ hσ
      calc
        qftLadderFamN n σ.2 (n - 1 - (Nat.unpair σ.1).1) ((Nat.unpair σ.1).1 - 0) =
            qftLadderFamN n σ.2 (n - 1 - (Nat.unpair σ.1).1) (n - 1 - (n - 1 - (Nat.unpair
        σ.1).1)) := by
          congr 1
          omega
        _ = qftStageFam n σ.2 ((n - 1 - (Nat.unpair σ.1).1) + 1) :=
          qftLadderFamN_full n σ.2 (by omega)
        _ = qftStageFam n σ.2 (n - (Nat.unpair σ.1).1) := by congr 1; omega
    · intro σ _
      rw [Nat.sub_self]
      exact congrArg _ (qftLadderFamN_zero n σ.2 (n - 1 - (Nat.unpair σ.1).1))
    · exact framedRung (ctrlEmb n) R hR (iladReg n) (iladGate n) _ _
        fun σ hσ => iladder_action n σ (hk σ hσ.1) hσ.2
    · intro z
      exact framedIdentity (ctrlEmb n) (iladReg n) (iladGate n) _ fun σ hσ =>
        (Reg.pair _ _ (InverseQFTTriple.ictrl_ne_itgt n (σ := Nat.unpair σ.1) (hk σ hσ.1)
        hσ.2.1)).inj

/-- Reverse stages use the QFT stage family at the decreasing index. -/
theorem iqftIter_deriv :
    SourceDerivTot
      (SourceAssertion.ofAssn (framedFam (ctrlEmb n) R hR
        (fun σ : QPEClassicalTriple.Store n => prodV
        (QubitD n) (W := univ)
          (qftStageFam n σ.2 n))
        (fun σ => norm_prodV_eq_one _ (norm_qftStageFam n σ.2 n))) fun _ => True)
      (iqftIter n)
      (SourceAssertion.ofAssn (framedFam (ctrlEmb n) R hR
        (fun σ : QPEClassicalTriple.Store n => prodV
        (QubitD n) (W := univ)
          (qftStageFam n σ.2 0))
        (fun σ => norm_prodV_eq_one _ (norm_qftStageFam n σ.2 0))) fun _ => True) := by
  refine framedCounted (ctrlEmb n) R hR (stageCounter n) (fun _ => n) (fun _ => True)
    (by intros; simp [stageCounter, rungCounter, CounterLens.pullbackFst, CounterLens.pullback,
        StoreLens.fst, QPEClassicalTriple.iqftStore, QFTClassicalTriple.stageCounter,
        QFTClassicalTriple.rungCounter, CounterLens.fst, CounterLens.snd]) (by intros; simp
        [stageCounter, rungCounter, CounterLens.pullbackFst, CounterLens.pullback,
        StoreLens.fst, QPEClassicalTriple.iqftStore, QFTClassicalTriple.stageCounter,
        QFTClassicalTriple.rungCounter, CounterLens.fst, CounterLens.snd])
    (fun m σ => prodV (QubitD n) (W := univ) (qftStageFam n σ.2 (n - m)))
    (fun m σ => norm_prodV_eq_one _ (norm_qftStageFam n σ.2 (n - m)))
    (by intros; simp [stageCounter, rungCounter, CounterLens.pullbackFst, CounterLens.pullback,
        StoreLens.fst, QPEClassicalTriple.iqftStore, QFTClassicalTriple.stageCounter,
        QFTClassicalTriple.rungCounter, CounterLens.fst, CounterLens.snd]) (by intros; simp
        [stageCounter, rungCounter, CounterLens.pullbackFst, CounterLens.pullback,
        StoreLens.fst, QPEClassicalTriple.iqftStore, QFTClassicalTriple.stageCounter,
        QFTClassicalTriple.rungCounter, CounterLens.fst, CounterLens.snd]) (fun _ _ => by rw
        [Nat.sub_self]) ?_ ?_
  · refine SourceDerivTot.seq (iqftSub_current n R hR
      (φ := fun σ => True ∧ (Nat.unpair σ.1).1 < n) (by intros; simp [stageCounter,
        rungCounter, CounterLens.pullbackFst, CounterLens.pullback, StoreLens.fst,
        QPEClassicalTriple.iqftStore, QFTClassicalTriple.stageCounter,
        QFTClassicalTriple.rungCounter, CounterLens.fst, CounterLens.snd]) (fun _ h => h.2)) ?_
    exact framedSingle (ctrlEmb n) R hR (ihReg n) (ihGate n)
      (fun σ => InverseQFTTriple.ictrl n (Nat.unpair σ.1)) (fun _ => H)
      (fun σ => norm_qftStageMidN n σ.2 (n - 1 - (Nat.unpair σ.1).1))
      (fun σ => norm_qftStageFam n σ.2 (n - ((Nat.unpair σ.1).1 + 1)))
      (fun σ _ => ⟨(Reg.single (InverseQFTTriple.ictrl n (Nat.unpair σ.1))).inj, rfl⟩)
      (fun σ hσ => by
        change Function.update _ (cell n (n - 1 - (Nat.unpair σ.1).1)) _ = _
        rw [show n - ((Nat.unpair σ.1).1 + 1) = n - 1 - (Nat.unpair σ.1).1 from by omega]
        exact qftStageMidN_step_H n σ.2 (by have h := hσ.2; omega))
  · intro z
    refine SourceDerivTot.seq ?_
      (framedIdentity (ctrlEmb n) (ihReg n) (ihGate n) _
        (fun σ _ => (Reg.single (InverseQFTTriple.ictrl n (Nat.unpair σ.1))).inj))
    refine SourceDerivTot.countedIdentity (rungCounter n) (fun σ => (Nat.unpair σ.1).1) _
      (by intros; simp [stageCounter, rungCounter, CounterLens.pullbackFst,
        CounterLens.pullback, StoreLens.fst, QPEClassicalTriple.iqftStore,
        QFTClassicalTriple.stageCounter, QFTClassicalTriple.rungCounter, CounterLens.fst,
        CounterLens.snd]) (by intros; simp [stageCounter, rungCounter, CounterLens.pullbackFst,
        CounterLens.pullback, StoreLens.fst, QPEClassicalTriple.iqftStore,
        QFTClassicalTriple.stageCounter, QFTClassicalTriple.rungCounter, CounterLens.fst,
        CounterLens.snd]) _ ?_ ?_
    · exact framedIdentity (ctrlEmb n) (iladReg n) (iladGate n) _ fun σ hσ =>
        (Reg.pair _ _ (InverseQFTTriple.ictrl_ne_itgt n (σ := Nat.unpair σ.1) hσ.1.2.1 hσ.2)).inj
    · intro z'
      exact framedIdentity (ctrlEmb n) (iladReg n) (iladGate n) _ fun σ hσ =>
        (Reg.pair _ _ (InverseQFTTriple.ictrl_ne_itgt n (σ := Nat.unpair σ.1) hσ.1.2.1
        hσ.2.1)).inj


/-- Exact mapped and placed inverse circuit with a fixed quantum frame. -/
theorem iqftRevDeriv :
    SourceDerivTot
      (SourceAssertion.ofAssn
        (((outputAssn n).pull (QPEClassicalTriple.iqftStore n).get).embFrame
          (emb := ctrlEmb n) R hR) (fun _ => True))
      (QPEClassicalTriple.iqftCtrl n)
      (SourceAssertion.ofAssn
        (((inputAssn n).pull (QPEClassicalTriple.iqftStore n).get).embFrame
          (emb := ctrlEmb n) R hR) (fun _ => True)) := by
  refine .seq (.conseq ?_ (revCircBack_deriv n R hR) ?_)
    (.conseq (SourceAssertion.entails_refl _) (iqftIter_deriv n R hR) ?_)
  · apply SourceAssertion.entails_ofAssn
    · intro _ h; exact h
    · intro σ _
      simp only [framedFam, Assn.embFrame_op, Assn.pull_op, outputAssn, Assn.ofStateFam_op]
      change _ ≤ castF _ _ _ (tenf _ (embOp _ _ _
        (outerLM (prodV (QubitD n) (iqftRevFamN n σ.2 0))
          (prodV (QubitD n) (iqftRevFamN n σ.2 0)))) R)
      rw [fourierState_eq_prodV, iqftRevFamN_zero]
      exact le_rfl
  · apply SourceAssertion.entails_ofAssn
    · intro _ h; exact h
    · intro σ _
      simp only [framedFam, Assn.embFrame_op, Assn.ofStateFam_op,
        iqftRevFamN_half, qftStageFam_full]
      exact le_rfl
  · apply SourceAssertion.entails_ofAssn
    · intro _ h; exact h
    · intro σ _
      simp only [framedFam, Assn.embFrame_op, Assn.pull_op, inputAssn,
        basisState, Assn.ofStateFam_op, qftStageFam_zero]
      exact le_rfl

end Stored

end Qhl.InverseQFTPlacedSource

namespace Qhl.QPEClassicalSource
open Finset QPETriple QPEClassicalTriple
open scoped ComplexInnerProductSpace ComplexOrder
variable (n : ℕ) [NeZero n] (U : UnitaryOp 𝕢) (ψ : 𝕢) (hψ : ‖ψ‖ = 1)

theorem phDeriv :
    SourceDerivTot (SourceAssertion.ofAssn (initial n ψ hψ) (eigen n U ψ))
      (QPEClassicalTriple.phCtrl n)
      (SourceAssertion.ofAssn (plus n ψ hψ) (eigen n U ψ)) := by
  have h0 : qpeInitFam n ψ
      = ParallelHadamardTriple.phFamOn n (ctrlReg n) (fun _ => ψ) 0 := by
    rw [ParallelHadamardTriple.phFamOn_zero]
    funext i
    by_cases h : (i : ℕ) < n
    · rw [if_pos (mem_sig_ctrlReg.mpr h)]
      simp only [qpeInitFam]
      rw [if_pos h]
    · rw [if_neg fun hc => h (mem_sig_ctrlReg.mp hc)]
      simp only [qpeInitFam]
      rw [if_neg h]
  have h1 : ParallelHadamardTriple.phFamOn n (ctrlReg n) (fun _ => ψ) n
      = qpePlusFam n ψ := by
    rw [ParallelHadamardTriple.phFamOn_full]
    funext i
    by_cases h : (i : ℕ) < n
    · rw [if_pos (mem_sig_ctrlReg.mpr h)]
      simp only [qpePlusFam]
      rw [if_pos h]
    · rw [if_neg fun hc => h (mem_sig_ctrlReg.mp hc)]
      simp only [qpePlusFam]
      rw [if_neg h]
  refine .conseq ?_
    (ParallelHadamardSource.phDerivOnWith n (ctrlReg n) (counter n)
      (fun _ => ψ) (fun _ => hψ) (eigen n U ψ) (fun _ _ => Iff.rfl)) ?_
  · apply SourceAssertion.entails_ofAssn _ _ _ _ (fun _ h => h)
    intro σ _
    apply le_of_eq
    change (prodA _ _ _).op σ = (prodA _ _ _).op σ
    rw [prodA_op, prodA_op, h0]
  · apply SourceAssertion.entails_ofAssn _ _ _ _ (fun _ h => h.1)
    intro σ _
    apply le_of_eq
    change (prodA _ _ _).op σ = (prodA _ _ _).op σ
    rw [prodA_op, prodA_op, h1]

theorem kickDeriv :
    SourceDerivTot (SourceAssertion.ofAssn (plus n ψ hψ) (eigen n U ψ))
      (QPEClassicalTriple.kickCir n U)
      (SourceAssertion.ofAssn (phased n ψ hψ) (eigen n U ψ)) := by
  refine SourceDerivTot.countedStateChainVar (counter n) (fun _ => n) (eigen n U ψ)
    (hv₀ := fun _ => norm_prodV_eq_one _ (norm_qpePlusFam n ψ hψ))
    (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (fun k σ => prodV (QubitD (n + 1)) (W := univ) (qpeKickFam n σ.2 ψ k))
    (fun k σ => norm_prodV_eq_one _ (norm_qpeKickFam n σ.2 ψ hψ k))
    (fun _ _ _ => rfl) ?_ ?_ ?_ ?_
  · intro σ _
    exact congrArg _ (qpeKickFam_zero n σ.2 ψ)
  · intro σ _
    exact congrArg _ (qpeKickFam_full n σ.2 ψ)
  · exact SourceDerivTot.countedRung_pair_fam (kickReg n) (QPEClassicalTriple.kickGate n U)
      (fun σ => qpeCell n σ.1) (fun _ => Fin.last n)
      (fun σ _ => qpeCell_ne_last n σ.1)
      (fun σ => control (U ^ 2 ^ (n - 1 - σ.1)))
      (fun σ => norm_qpeKickFam n σ.2 ψ hψ σ.1)
      (fun σ => norm_qpeKickFam n σ.2 ψ hψ (σ.1 + 1))
      (fun σ _ => ⟨(Reg.pair _ _ (qpeCell_ne_last n σ.1)).inj, rfl⟩)
      (fun σ hσ => by
        have hk : σ.1 < n := hσ.2
        refine ⟨phaseKet (qftAngle σ.2 (n - 1 - σ.1)), ψ, ?_, ?_⟩
        · have hctrl : qpeKickFam n σ.2 ψ σ.1 (qpeCell n σ.1) = qplus := by
            rw [qpeCell_of_lt n hk]
            exact qpeKickFam_ctrl n σ.2 ψ ⟨σ.1, hk⟩
          rw [hctrl, qpeKickFam_last n σ.2 ψ σ.1, ← phaseKet_zero,
            control_pow_vpair_phaseKet U hσ.1 (2 ^ (n - 1 - σ.1)) 0, zero_add,
            phaseKet_kick n σ.2 (show n - 1 - σ.1 < n by omega)]
        · rw [qpeCell_of_lt n hk]
          exact qpeKickFam_step n σ.2 ψ ⟨σ.1, hk⟩)
  · intro z
    exact SourceDerivTot.unitary_identity (kickReg n) (QPEClassicalTriple.kickGate n U) _
      (fun σ _ => (Reg.pair _ _ (qpeCell_ne_last n σ.1)).inj)

/-- The actual stored-input inverse QFT is derived on the counting register. -/
theorem iqftCtrlDeriv :
    SourceDerivTot (SourceAssertion.ofAssn (phased n ψ hψ) (fun _ => True))
      (QPEClassicalTriple.iqftCtrl n)
      (SourceAssertion.ofAssn (output n ψ hψ) (fun _ => True)) := by
  have hf := InverseQFTPlacedSource.Stored.iqftRevDeriv n
    (outerLM (targetFrame n ψ) (targetFrame n ψ))
    (isEffect_outerLM_self (norm_targetFrame n ψ hψ))
  have hin : (QFTClassicalTriple.outputAssn n).pull (QPEClassicalTriple.iqftStore n).get =
      Assn.ofStateFam
        (fun σ : Store n => prodV (QubitD n) (W := univ)
          (fun j => qpePhasedFam n σ.2 ψ j.castSucc))
        (fun σ => norm_prodV_eq_one _ (fun j => norm_qpePhasedFam n σ.2 ψ hψ j.castSucc)) := by
    apply Assn.ext
    funext σ
    simp only [Assn.pull_op, QFTClassicalTriple.outputAssn, Assn.ofStateFam_op,
      QPEClassicalTriple.iqftStore, fourierState_eq_prodV]
    congr 1 <;> apply congrArg (prodV (QubitD n)) <;> funext j
      <;> exact (qpePhasedFam_castSucc n σ.2 ψ j).symm
  have hout : (QFTClassicalTriple.inputAssn n).pull (QPEClassicalTriple.iqftStore n).get =
      Assn.ofStateFam
        (fun σ : Store n => prodV (QubitD n) (W := univ)
          (fun j => qpeOutFam n σ.2 ψ j.castSucc))
        (fun σ => norm_prodV_eq_one _ (fun j => norm_qpeOutFam n σ.2 ψ hψ j.castSucc)) := by
    apply Assn.ext
    funext σ
    simp only [Assn.pull_op, QFTClassicalTriple.inputAssn, Assn.ofStateFam_op,
      QPEClassicalTriple.iqftStore, QFTClassicalTriple.basisState]
    congr 1 <;> apply congrArg (prodV (QubitD n)) <;> funext j
      <;> exact (qpeOutFam_castSucc n σ.2 ψ j).symm
  rw [hin, hout,
    frame_endpoint n ψ hψ (fun σ => qpePhasedFam n σ.2 ψ)
      (fun σ => norm_qpePhasedFam n σ.2 ψ hψ) (fun σ => qpePhasedFam_last n σ.2 ψ),
    frame_endpoint n ψ hψ (fun σ => qpeOutFam n σ.2 ψ)
      (fun σ => norm_qpeOutFam n σ.2 ψ hψ) (fun σ => qpeOutFam_last n σ.2 ψ)] at hf
  exact hf

/-- The unchanged QPE circuit with the stored eigenrelation as classical precondition. -/
theorem qpeDeriv :
    SourceDerivTot (SourceAssertion.ofAssn (initial n ψ hψ) (eigen n U ψ))
      (QPEClassicalTriple.qpeCir n U)
      (SourceAssertion.ofAssn (output n ψ hψ) (fun _ => True)) := by
  refine (phDeriv n U ψ hψ).seq ((kickDeriv n U ψ hψ).seq
    (.conseq ?_ (iqftCtrlDeriv n ψ hψ) (SourceAssertion.entails_refl _)))
  exact SourceAssertion.entails_ofAssn _ _ _ _ (fun _ _ => trivial) (fun _ _ => le_rfl)

theorem qpeValid : validTot ((initial n ψ hψ).mask (eigen n U ψ))
    (QPEClassicalTriple.qpeCir n U) (output n ψ hψ) := by
  have h := (qpeDeriv n U ψ hψ).sound
  rw [SourceAssertion.toAssn_ofAssn_true, SourceAssertion.toAssn_ofAssn] at h
  exact h

end Qhl.QPEClassicalSource

#print axioms Qhl.QPEClassicalSource.qpeDeriv
#print axioms Qhl.QPEClassicalSource.qpeValid
