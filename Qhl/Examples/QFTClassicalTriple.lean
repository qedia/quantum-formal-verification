import Qhl.Examples.QFTTriple
import Qhl.Program.StoreLens
import Qhl.Examples.QFTComplete
import Qhl.Logic.Subroutine
import Qhl.Logic.StateApproximation

/-! # QFT with a read-only classical input array

The quantum width `n ≥ 1` is fixed externally. The classical store contains
both loop counters and an input bit array `x : Fin n → Bool`. The circuit
preserves that array, and its endpoint predicates read it from the store.
All loops are literal counted `while` programs, and all derivations use the
source counted-loop rules with separate identity-predicate rank premises.
The original two-counter QFT remains available unchanged.
-/

namespace Qhl.QFTClassicalTriple
open Finset
open scoped ComplexInnerProductSpace

/-- Mutable stage/rung counters, paired with the read-only input array. -/
abbrev Store (n : ℕ) := (ℕ × ℕ) × (Fin n → Bool)

variable (n : ℕ) [NeZero n]

/-- The stage counter does not overwrite the stored input. -/
def stageCounter : CounterLens (Store n) := CounterLens.pullbackFst (CounterLens.fst ℕ)
/-- The rung counter does not overwrite the stored input. -/
def rungCounter : CounterLens (Store n) := CounterLens.pullbackFst (CounterLens.snd ℕ)

omit [NeZero n] in
@[simp] theorem stageCounter_set_input (σ : Store n) (v : ℕ) :
    ((stageCounter n).set σ v).2 = σ.2 := rfl
omit [NeZero n] in
@[simp] theorem rungCounter_set_input (σ : Store n) (v : ℕ) :
    ((rungCounter n).set σ v).2 = σ.2 := rfl

/-- Register and gate expressions read the current counters. -/
def hReg : RegExpr (Store n) (QubitL n) 1 := fun σ => QFTTriple.hReg n σ.1
noncomputable def hGate (σ : Store n) : UnitaryOp (TSpace (QubitD n) (hReg n σ)) :=
  QFTTriple.hGate n σ.1
def ladReg : RegExpr (Store n) (QubitL n) 2 := fun σ => QFTTriple.ladReg n σ.1
noncomputable def ladGate (σ : Store n) : UnitaryOp (TSpace (QubitD n) (ladReg n σ)) :=
  QFTTriple.ladGate n σ.1
def swapReg : RegExpr (Store n) (QubitL n) 2 := fun σ => QFTTriple.swapReg n σ.1
noncomputable def swapGate (σ : Store n) : UnitaryOp (TSpace (QubitD n) (swapReg n σ)) :=
  QFTTriple.swapGate n σ.1

noncomputable def qftSub : Prog (Store n) (QubitD n) :=
  countedProg (rungCounter n) (fun σ => n - 1 - σ.1.1)
    (.unitary 2 (ladReg n) (ladGate n))
noncomputable def qftIter : Prog (Store n) (QubitD n) :=
  countedProg (stageCounter n) (fun _ => n)
    ((Prog.unitary 1 (hReg n) (hGate n)).seq (qftSub n))
noncomputable def revCirc : Prog (Store n) (QubitD n) :=
  countedProg (stageCounter n) (fun _ => n / 2)
    (.unitary 2 (swapReg n) (swapGate n))
noncomputable def qftCir : Prog (Store n) (QubitD n) := (qftIter n).seq (revCirc n)

/-- Erasing the read-only component gives exactly the old program's store
transport, constructor for constructor. -/
theorem qftCir_eq_mapStore :
    qftCir n = (QFTTriple.qftCir n).mapStore StoreLens.fst := rfl

/-- Every classical update preserves the stored array, independently of any
quantum assertion or initial state. -/
theorem qftCir_preserves_input : (qftCir n).Preserves (fun σ => σ.2) := by
  simp [qftCir, qftIter, qftSub, revCirc, countedProg, Prog.Preserves,
    stageCounter, rungCounter, CounterLens.pullbackFst, CounterLens.pullback,
    StoreLens.fst, CounterLens.fst, CounterLens.snd]

noncomputable def basisState (σ : Store n) :=
  prodV (QubitD n) (W := (univ : Finset (QubitL n))) (fun i => qbit (σ.2 i))
omit [NeZero n] in
theorem norm_basisState (σ : Store n) : ‖basisState n σ‖ = 1 :=
  norm_prodV_eq_one _ fun _ => norm_qbit _

/-- The endpoints evaluate the classical input array in the current store. -/
noncomputable def inputAssn : Assn (Store n) (QubitD n) :=
  Assn.ofStateFam (basisState n) (norm_basisState n)
noncomputable def outputAssn : Assn (Store n) (QubitD n) :=
  Assn.ofStateFam (fun σ => fourierState n σ.2) (fun σ => norm_fourierState n σ.2)

private theorem ladder_action (σ : Store n) (hk : σ.1.1 < n)
    (hj : σ.1.2 < n - 1 - σ.1.1) :
    ∃ hinj : Function.Injective (ladReg n σ),
      regLift (D := QubitD n) ⟨ladReg n σ, hinj⟩ (ladGate n σ)
        (prodV (QubitD n) (W := univ) (qftLadderFamN n σ.2 σ.1.1 σ.1.2)) =
        prodV (QubitD n) (W := univ) (qftLadderFamN n σ.2 σ.1.1 (σ.1.2 + 1)) := by
  have hne := QFTTriple.ctrl_ne_tgt n (σ := σ.1) hk hj
  refine ⟨(Reg.pair _ _ hne).inj, ?_⟩
  change regLift (D := QubitD n) ⟨QFTTriple.ladReg n σ.1, (Reg.pair _ _ hne).inj⟩
    (QFTTriple.ladGate n σ.1) _ = _
  rw [show QFTTriple.ladGate n σ.1 = pairGate (D := QubitD n)
      (QFTTriple.ctrl n σ.1) (QFTTriple.tgt n σ.1) hne
      (cphase (2 * Real.pi / 2 ^ (σ.1.2 + 2))) from by
    simp only [QFTTriple.ladGate]; rw [dif_pos hne]]
  exact regLift_cphase_qftLadderFamN n σ.2 hk hj hne

/-- Inner ladder invariant reads both the outer counter and the stored array. -/
theorem qftSub_deriv {φ : Store n → Prop}
    (hφ : ∀ σ v, φ ((rungCounter n).set σ v) ↔ φ σ)
    (hk : ∀ σ, φ σ → σ.1.1 < n) :
    DerivTot
      ((Assn.ofStateFam (fun σ : Store n => prodV (QubitD n) (W := univ)
          (qftStageMidN n σ.2 σ.1.1))
        (fun σ : Store n => norm_prodV_eq_one _ (norm_qftStageMidN n σ.2 σ.1.1))).mask φ)
      (qftSub n)
      ((Assn.ofStateFam (fun σ : Store n => prodV (QubitD n) (W := univ)
          (qftStageFam n σ.2 (σ.1.1 + 1)))
        (fun σ : Store n => norm_prodV_eq_one _ (norm_qftStageFam n σ.2 (σ.1.1 + 1)))).mask φ) := by
  refine DerivTot.countedStateChainVarSource (rungCounter n) hφ (fun _ _ => rfl)
    (fun m σ => prodV (QubitD n) (W := univ) (qftLadderFamN n σ.2 σ.1.1 m))
    (fun m σ => norm_prodV_eq_one _ (norm_qftLadderFamN n σ.2 σ.1.1 m))
    (fun _ _ _ => rfl) ?_ ?_ ?_ ?_
  · intro σ _; exact congrArg _ (qftLadderFamN_zero n σ.2 σ.1.1)
  · intro σ hσ; exact congrArg _ (qftLadderFamN_full n σ.2 (hk σ hσ))
  · exact DerivTot.countedRung_fam (ladReg n) (ladGate n) _ _
      fun σ hσ => ladder_action n σ (hk σ hσ.1) hσ.2
  · intro z
    exact DerivTot.unitary_identityMask (ladReg n) (ladGate n) _ fun σ hσ =>
      (Reg.pair _ _ (QFTTriple.ctrl_ne_tgt n (σ := σ.1) (hk σ hσ.1) hσ.2.1)).inj

/-- The outer stage loop, with an invariant indexed by the stored input. -/
theorem qftIter_deriv :
    DerivTot
      ((Assn.ofStateFam (fun σ : Store n => prodV (QubitD n) (W := univ)
          (qftStageFam n σ.2 0))
        (fun σ : Store n => norm_prodV_eq_one _ (norm_qftStageFam n σ.2 0))).mask fun _ => True)
      (qftIter n)
      ((Assn.ofStateFam (fun σ : Store n => prodV (QubitD n) (W := univ)
          (qftStageFam n σ.2 n))
        (fun σ : Store n =>
          norm_prodV_eq_one _ (norm_qftStageFam n σ.2 n))).mask fun _ => True) := by
  refine DerivTot.countedStateChainVarSource (stageCounter n)
    (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (fun m σ => prodV (QubitD n) (W := univ) (qftStageFam n σ.2 m))
    (fun m σ => norm_prodV_eq_one _ (norm_qftStageFam n σ.2 m))
    (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) ?_ ?_
  · refine DerivTot.seq ?_ (qftSub_deriv n
      (φ := fun σ => True ∧ σ.1.1 < n) (fun _ _ => Iff.rfl) (fun _ h => h.2))
    exact DerivTot.countedRung_single_fam (hReg n) (hGate n)
      (fun σ => QFTTriple.ctrl n σ.1) (fun _ => H)
      (fun σ => norm_qftStageFam n σ.2 σ.1.1)
      (fun σ => norm_qftStageMidN n σ.2 σ.1.1)
      (fun σ _ => ⟨(Reg.single (QFTTriple.ctrl n σ.1)).inj, rfl⟩)
      (fun σ hσ => qftStageMidN_eq_update_H n σ.2 hσ.2)
  · intro z
    refine DerivTot.seq
      (DerivTot.unitary_identityMask (hReg n) (hGate n) _
        (fun σ _ => (Reg.single (QFTTriple.ctrl n σ.1)).inj)) ?_
    refine DerivTot.countedIdentityVarSource (rungCounter n)
      (fun _ _ => Iff.rfl) (fun _ _ => rfl) ?_ ?_
    · exact DerivTot.unitary_identityMask (ladReg n) (ladGate n) _ fun σ hσ =>
        (Reg.pair _ _ (QFTTriple.ctrl_ne_tgt n (σ := σ.1) hσ.1.2.1 hσ.2)).inj
    · intro z'
      exact DerivTot.unitary_identityMask (ladReg n) (ladGate n) _ fun σ hσ =>
        (Reg.pair _ _ (QFTTriple.ctrl_ne_tgt n (σ := σ.1) hσ.1.2.1 hσ.2.1)).inj

/-- The final reversal preserves the stored array as well. -/
theorem revCirc_deriv :
    DerivTot
      ((Assn.ofStateFam (fun σ : Store n => prodV (QubitD n) (W := univ)
          (qftRevFamN n σ.2 0))
        (fun σ : Store n => norm_prodV_eq_one _ (norm_qftRevFamN n σ.2 0))).mask fun _ => True)
      (revCirc n)
      ((Assn.ofStateFam (fun σ : Store n => prodV (QubitD n) (W := univ)
          (qftRevFamN n σ.2 (n / 2)))
        (fun σ : Store n =>
          norm_prodV_eq_one _ (norm_qftRevFamN n σ.2 (n / 2)))).mask fun _ => True) := by
  refine DerivTot.countedStateChainVarSource (stageCounter n)
    (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (fun m σ => prodV (QubitD n) (W := univ) (qftRevFamN n σ.2 m))
    (fun m σ => norm_prodV_eq_one _ (norm_qftRevFamN n σ.2 m))
    (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) ?_ ?_
  · exact DerivTot.countedRung_pair_fam (swapReg n) (swapGate n)
      (fun σ => QFTTriple.ctrl n σ.1) (fun σ => QFTTriple.mir n σ.1)
      (fun σ hσ => QFTTriple.ctrl_ne_mir n (σ := σ.1) hσ.2) (fun _ => SWAP)
      (fun σ => norm_qftRevFamN n σ.2 σ.1.1)
      (fun σ => norm_qftRevFamN n σ.2 (σ.1.1 + 1))
      (fun σ hσ => by
        have hne := QFTTriple.ctrl_ne_mir n (σ := σ.1) hσ.2
        refine ⟨(Reg.pair _ _ hne).inj, ?_⟩
        change regLift (D := QubitD n)
          ⟨QFTTriple.swapReg n σ.1, (Reg.pair _ _ hne).inj⟩
          (QFTTriple.swapGate n σ.1) =
          regLift (D := QubitD n)
            (Reg.pair (QFTTriple.ctrl n σ.1) (QFTTriple.mir n σ.1) hne)
            (pairGate (D := QubitD n)
              (QFTTriple.ctrl n σ.1) (QFTTriple.mir n σ.1) hne SWAP)
        rw [show QFTTriple.swapGate n σ.1 = pairGate (D := QubitD n)
            (QFTTriple.ctrl n σ.1) (QFTTriple.mir n σ.1) hne SWAP from by
          simp only [QFTTriple.swapGate]; rw [dif_pos hne]]
        rfl)
      (fun σ hσ => by
        have hk : σ.1.1 < n / 2 := hσ.2
        have hc : QFTTriple.ctrl n σ.1 = cell n σ.1.1 := rfl
        have hm : QFTTriple.mir n σ.1 = cell n (n - 1 - σ.1.1) := rfl
        exact ⟨phaseKet (qftAngle σ.2 (n - 1 - σ.1.1)),
          phaseKet (qftAngle σ.2 σ.1.1),
          by rw [hc, hm, qftRevFamN_left n σ.2 hk, qftRevFamN_right n σ.2 hk, SWAP_vpair],
          by rw [hc, hm]; exact qftRevFamN_step n σ.2 hk⟩)
  · intro z
    exact DerivTot.unitary_identityMask (swapReg n) (swapGate n) _ fun σ hσ =>
      (Reg.pair _ _ (QFTTriple.ctrl_ne_mir n (σ := σ.1) hσ.2.1)).inj

/-- A ladder preserves any classical predicate insensitive to its rung counter.
The identity quantum assertion makes this independent of the quantum input. -/
theorem qftSub_preserves {φ : Store n → Prop}
    (hφ : ∀ σ v, φ ((rungCounter n).set σ v) ↔ φ σ)
    (hk : ∀ σ, φ σ → σ.1.1 < n) :
    DerivTot ((Assn.one : Assn (Store n) (QubitD n)).mask φ) (qftSub n)
      (Assn.one.mask φ) := by
  refine DerivTot.countedIdentityVarSource (rungCounter n) hφ (fun _ _ => rfl) ?_ ?_
  · exact DerivTot.unitary_identityMask (ladReg n) (ladGate n) _ fun σ hσ =>
      (Reg.pair _ _ (QFTTriple.ctrl_ne_tgt n (σ := σ.1) (hk σ hσ.1) hσ.2)).inj
  · intro z
    exact DerivTot.unitary_identityMask (ladReg n) (ladGate n) _ fun σ hσ =>
      (Reg.pair _ _ (QFTTriple.ctrl_ne_tgt n (σ := σ.1) (hk σ hσ.1) hσ.2.1)).inj

/-- The whole circuit preserves every predicate of the stored input array,
on every quantum input. Taking `p := fun x => x = x₀` expresses read-only `x`. -/
theorem inputPreservedDeriv (p : (Fin n → Bool) → Prop) :
    DerivTot ((Assn.one : Assn (Store n) (QubitD n)).mask fun σ => p σ.2)
      (qftCir n) (Assn.one.mask fun σ => p σ.2) := by
  have hi : DerivTot ((Assn.one : Assn (Store n) (QubitD n)).mask fun σ => p σ.2)
      (qftIter n) (Assn.one.mask fun σ => p σ.2) := by
    refine DerivTot.countedIdentityVarSource (stageCounter n)
      (fun _ _ => Iff.rfl) (fun _ _ => rfl) ?_ ?_
    · refine DerivTot.seq
        (DerivTot.unitary_identityMask (hReg n) (hGate n) _
          (fun σ _ => (Reg.single (QFTTriple.ctrl n σ.1)).inj)) ?_
      exact qftSub_preserves n (fun _ _ => Iff.rfl) (fun _ h => h.2)
    · intro z
      refine DerivTot.seq
        (DerivTot.unitary_identityMask (hReg n) (hGate n) _
          (fun σ _ => (Reg.single (QFTTriple.ctrl n σ.1)).inj)) ?_
      exact qftSub_preserves n (fun _ _ => Iff.rfl) (fun _ h => h.2.1)
  refine DerivTot.seq hi ?_
  refine DerivTot.countedIdentityVarSource (stageCounter n)
    (fun _ _ => Iff.rfl) (fun _ _ => rfl) ?_ ?_
  · exact DerivTot.unitary_identityMask (swapReg n) (swapGate n) _ fun σ hσ =>
      (Reg.pair _ _ (QFTTriple.ctrl_ne_mir n (σ := σ.1) hσ.2)).inj
  · intro z
    exact DerivTot.unitary_identityMask (swapReg n) (swapGate n) _ fun σ hσ =>
      (Reg.pair _ _ (QFTTriple.ctrl_ne_mir n (σ := σ.1) hσ.2.1)).inj

theorem inputPreservedValid (p : (Fin n → Bool) → Prop) :
    validTot ((Assn.one : Assn (Store n) (QubitD n)).mask fun σ => p σ.2)
      (qftCir n) (Assn.one.mask fun σ => p σ.2) :=
  (inputPreservedDeriv n p).sound

/-- Source-rule total-correctness derivation with genuinely store-dependent
basis-input and Fourier-output predicates. -/
theorem qftDeriv : DerivTot (inputAssn n) (qftCir n) (outputAssn n) := by
  refine DerivTot.seq (DerivTot.conseq ?_ (qftIter_deriv n) ?_)
    (DerivTot.conseq (Assn.le_refl' _) (revCirc_deriv n) ?_)
  · intro σ
    simp only [Assn.mask, if_true, inputAssn,
      Assn.ofStateFam_op, basisState, qftStageFam_zero]
    exact le_rfl
  · intro σ
    simp only [Assn.mask, if_true, Assn.ofStateFam_op,
      qftRevFamN, qftRevFam_zero, qftStageFam_full]
    exact le_rfl
  · intro σ
    simp only [Assn.mask, if_true, outputAssn,
      Assn.ofStateFam_op, qftRevFamN, qftRevFam_half]
    rw [fourierState_eq_prodV n σ.2]
    simp only [revIdx_val]
    exact le_rfl

/-- Semantic validity is obtained only through source-rule soundness. -/
theorem qftValid : validTot (inputAssn n) (qftCir n) (outputAssn n) :=
  (qftDeriv n).sound

omit [NeZero n] in
/-- Fixing the stored array recovers the original basis-input projector. -/
theorem input_specialize (c : ℕ × ℕ) (x : Fin n → Bool) :
    (inputAssn n).op (c, x) =
      (Assn.ofState (σT := ℕ × ℕ)
        (prodV (QubitD n) (W := univ) (fun i => qbit (x i)))
        (norm_prodV_eq_one _ fun _ => norm_qbit _)).op c := rfl
omit [NeZero n] in
/-- Fixing the stored array recovers the original Fourier-output projector. -/
theorem output_specialize (c : ℕ × ℕ) (x : Fin n → Bool) :
    (outputAssn n).op (c, x) =
      (Assn.ofState (σT := ℕ × ℕ) (fourierState n x) (norm_fourierState n x)).op c := rfl

omit [NeZero n] in
/-- Every classical store admits a normalized quantum input satisfying the
precondition with expectation one; the triple is not vacuous. -/
theorem input_nonvacuous (σ : Store n) :
    expectE (inputAssn n).op ⟨σ, PDensity.pure (basisState n σ)⟩ = 1 := by
  rw [expectE_pure]
  change ENNReal.ofReal (⟪basisState n σ,
    (outerLM (basisState n σ) (basisState n σ)) (basisState n σ)⟫.re) = 1
  rw [outerLM_apply]
  simp [inner_self_eq_norm_sq_to_K, norm_basisState]

/-- The uniform-superposition triple for this very same enlarged-store program.
Its fixed quantum endpoints intentionally do not read the stored basis label. -/
theorem qftUniformDeriv :
    DerivTot (σT := Store n)
      (Assn.ofState (allPlusOn (QubitL n)) (norm_allPlusOn (QubitL n))) (qftCir n)
      (Assn.ofState (allZerosOn (QubitL n)) (norm_allZerosOn (QubitL n))) := by
  rw [qftCir_eq_mapStore]
  exact (QFTUniform.qftUniformDeriv n).mapStore_pull StoreLens.fst (fun _ _ => rfl)

/-- Arbitrary-input correctness reuses the basis/uniform phase recovery in
`QFTComplete`, transported through the same store lens. -/
theorem qftAllInputDeriv (ψ : HS (QubitD n) (univ : Finset (QubitL n))) (hψ : ‖ψ‖ = 1) :
    DerivTot (σT := Store n) (Assn.ofState ψ hψ) (qftCir n)
      (Assn.ofState ((qftOp n : EndM (QubitD n) (univ : Finset (QubitL n))) ψ)
        (norm_eq_one_of_isUnitary (qftOp n).isUnitary hψ)) := by
  rw [qftCir_eq_mapStore]
  exact (QFTComplete.qftAllInputDeriv n ψ hψ).mapStore_pull StoreLens.fst (fun _ _ => rfl)

theorem qftUniformValid :
    validTot (σT := Store n)
      (Assn.ofState (allPlusOn (QubitL n)) (norm_allPlusOn (QubitL n))) (qftCir n)
      (Assn.ofState (allZerosOn (QubitL n)) (norm_allZerosOn (QubitL n))) :=
  (qftUniformDeriv n).sound

theorem qftAllInputValid (ψ : HS (QubitD n) (univ : Finset (QubitL n))) (hψ : ‖ψ‖ = 1) :
    validTot (σT := Store n) (Assn.ofState ψ hψ) (qftCir n)
      (Assn.ofState ((qftOp n : EndM (QubitD n) (univ : Finset (QubitL n))) ψ)
        (norm_eq_one_of_isUnitary (qftOp n).isUnitary hψ)) :=
  (qftAllInputDeriv n ψ hψ).sound

end Qhl.QFTClassicalTriple

namespace Qhl.QFTClassicalSource
open Finset QFTClassicalTriple
variable (n : ℕ) [NeZero n]


/-- Inner ladder invariant reads both the outer counter and the stored array. -/
theorem qftSub_deriv {φ : Store n → Prop}
    (hφ : ∀ σ v, φ ((rungCounter n).set σ v) ↔ φ σ)
    (hk : ∀ σ, φ σ → σ.1.1 < n) :
    SourceDerivTot
      (SourceAssertion.ofAssn (Assn.ofStateFam (fun σ : Store n => prodV (QubitD n) (W := univ)
          (qftStageMidN n σ.2 σ.1.1))
        (fun σ : Store n => norm_prodV_eq_one _ (norm_qftStageMidN n σ.2 σ.1.1))) φ)
      (qftSub n)
      (SourceAssertion.ofAssn (Assn.ofStateFam (fun σ : Store n => prodV (QubitD n) (W := univ)
          (qftStageFam n σ.2 (σ.1.1 + 1)))
        (fun σ : Store n => norm_prodV_eq_one _ (norm_qftStageFam n σ.2 (σ.1.1 + 1)))) φ) := by
  refine SourceDerivTot.countedStateChainVar (rungCounter n)
    (fun σ => n - 1 - σ.1.1) φ hφ (fun _ _ => rfl)
    (fun m σ => prodV (QubitD n) (W := univ) (qftLadderFamN n σ.2 σ.1.1 m))
    (fun m σ => norm_prodV_eq_one _ (norm_qftLadderFamN n σ.2 σ.1.1 m))
    (fun _ _ _ => rfl) ?_ ?_ ?_ ?_
  · intro σ _; exact congrArg _ (qftLadderFamN_zero n σ.2 σ.1.1)
  · intro σ hσ; exact congrArg _ (qftLadderFamN_full n σ.2 (hk σ hσ))
  · exact SourceDerivTot.countedRung_fam (ladReg n) (ladGate n) _ _
      fun σ hσ => ladder_action n σ (hk σ hσ.1) hσ.2
  · intro z
    exact SourceDerivTot.unitary_identity (ladReg n) (ladGate n) _ fun σ hσ =>
      (Reg.pair _ _ (QFTTriple.ctrl_ne_tgt n (σ := σ.1) (hk σ hσ.1) hσ.2.1)).inj

/-- The outer stage loop, with an invariant indexed by the stored input. -/
theorem qftIter_deriv :
    SourceDerivTot
      (SourceAssertion.ofAssn (Assn.ofStateFam (fun σ : Store n => prodV (QubitD n) (W := univ)
          (qftStageFam n σ.2 0))
        (fun σ : Store n => norm_prodV_eq_one _ (norm_qftStageFam n σ.2 0))) fun _ => True)
      (qftIter n)
      (SourceAssertion.ofAssn (Assn.ofStateFam (fun σ : Store n => prodV (QubitD n) (W := univ)
          (qftStageFam n σ.2 n))
        (fun σ : Store n =>
          norm_prodV_eq_one _ (norm_qftStageFam n σ.2 n))) fun _ => True) := by
  refine SourceDerivTot.countedStateChainVar (stageCounter n) (fun _ => n) (fun _ => True)
    (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (fun m σ => prodV (QubitD n) (W := univ) (qftStageFam n σ.2 m))
    (fun m σ => norm_prodV_eq_one _ (norm_qftStageFam n σ.2 m))
    (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) ?_ ?_
  · refine SourceDerivTot.seq ?_ (qftSub_deriv n
      (φ := fun σ => True ∧ σ.1.1 < n) (fun _ _ => Iff.rfl) (fun _ h => h.2))
    exact SourceDerivTot.countedRung_single_fam (hReg n) (hGate n)
      (fun σ => QFTTriple.ctrl n σ.1) (fun _ => H)
      (fun σ => norm_qftStageFam n σ.2 σ.1.1)
      (fun σ => norm_qftStageMidN n σ.2 σ.1.1)
      (fun σ _ => ⟨(Reg.single (QFTTriple.ctrl n σ.1)).inj, rfl⟩)
      (fun σ hσ => qftStageMidN_eq_update_H n σ.2 hσ.2)
  · intro z
    refine SourceDerivTot.seq
      (SourceDerivTot.unitary_identity (hReg n) (hGate n) _
        (fun σ _ => (Reg.single (QFTTriple.ctrl n σ.1)).inj)) ?_
    refine SourceDerivTot.countedIdentity (rungCounter n) (fun σ => n - 1 - σ.1.1) _
      (fun _ _ => Iff.rfl) (fun _ _ => rfl) _ ?_ ?_
    · exact SourceDerivTot.unitary_identity (ladReg n) (ladGate n) _ fun σ hσ =>
        (Reg.pair _ _ (QFTTriple.ctrl_ne_tgt n (σ := σ.1) hσ.1.2.1 hσ.2)).inj
    · intro z'
      exact SourceDerivTot.unitary_identity (ladReg n) (ladGate n) _ fun σ hσ =>
        (Reg.pair _ _ (QFTTriple.ctrl_ne_tgt n (σ := σ.1) hσ.1.2.1 hσ.2.1)).inj

/-- The final reversal preserves the stored array as well. -/
theorem revCirc_deriv :
    SourceDerivTot
      (SourceAssertion.ofAssn (Assn.ofStateFam (fun σ : Store n => prodV (QubitD n) (W := univ)
          (qftRevFamN n σ.2 0))
        (fun σ : Store n => norm_prodV_eq_one _ (norm_qftRevFamN n σ.2 0))) fun _ => True)
      (revCirc n)
      (SourceAssertion.ofAssn (Assn.ofStateFam (fun σ : Store n => prodV (QubitD n) (W := univ)
          (qftRevFamN n σ.2 (n / 2)))
        (fun σ : Store n =>
          norm_prodV_eq_one _ (norm_qftRevFamN n σ.2 (n / 2)))) fun _ => True) := by
  refine SourceDerivTot.countedStateChainVar (stageCounter n) (fun _ => n / 2) (fun _ => True)
    (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (fun m σ => prodV (QubitD n) (W := univ) (qftRevFamN n σ.2 m))
    (fun m σ => norm_prodV_eq_one _ (norm_qftRevFamN n σ.2 m))
    (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) ?_ ?_
  · exact SourceDerivTot.countedRung_pair_fam (swapReg n) (swapGate n)
      (fun σ => QFTTriple.ctrl n σ.1) (fun σ => QFTTriple.mir n σ.1)
      (fun σ hσ => QFTTriple.ctrl_ne_mir n (σ := σ.1) hσ.2) (fun _ => SWAP)
      (fun σ => norm_qftRevFamN n σ.2 σ.1.1)
      (fun σ => norm_qftRevFamN n σ.2 (σ.1.1 + 1))
      (fun σ hσ => by
        have hne := QFTTriple.ctrl_ne_mir n (σ := σ.1) hσ.2
        refine ⟨(Reg.pair _ _ hne).inj, ?_⟩
        change regLift (D := QubitD n)
          ⟨QFTTriple.swapReg n σ.1, (Reg.pair _ _ hne).inj⟩
          (QFTTriple.swapGate n σ.1) =
          regLift (D := QubitD n)
            (Reg.pair (QFTTriple.ctrl n σ.1) (QFTTriple.mir n σ.1) hne)
            (pairGate (D := QubitD n)
              (QFTTriple.ctrl n σ.1) (QFTTriple.mir n σ.1) hne SWAP)
        rw [show QFTTriple.swapGate n σ.1 = pairGate (D := QubitD n)
            (QFTTriple.ctrl n σ.1) (QFTTriple.mir n σ.1) hne SWAP from by
          simp only [QFTTriple.swapGate]; rw [dif_pos hne]]
        rfl)
      (fun σ hσ => by
        have hk : σ.1.1 < n / 2 := hσ.2
        have hc : QFTTriple.ctrl n σ.1 = cell n σ.1.1 := rfl
        have hm : QFTTriple.mir n σ.1 = cell n (n - 1 - σ.1.1) := rfl
        exact ⟨phaseKet (qftAngle σ.2 (n - 1 - σ.1.1)),
          phaseKet (qftAngle σ.2 σ.1.1),
          by rw [hc, hm, qftRevFamN_left n σ.2 hk, qftRevFamN_right n σ.2 hk, SWAP_vpair],
          by rw [hc, hm]; exact qftRevFamN_step n σ.2 hk⟩)
  · intro z
    exact SourceDerivTot.unitary_identity (swapReg n) (swapGate n) _ fun σ hσ =>
      (Reg.pair _ _ (QFTTriple.ctrl_ne_mir n (σ := σ.1) hσ.2.1)).inj

/-- A ladder preserves any classical predicate insensitive to its rung counter.
The identity quantum assertion makes this independent of the quantum input. -/
theorem qftSub_preserves {φ : Store n → Prop}
    (hφ : ∀ σ v, φ ((rungCounter n).set σ v) ↔ φ σ)
    (hk : ∀ σ, φ σ → σ.1.1 < n) :
    SourceDerivTot (SourceAssertion.ofAssn (Assn.one : Assn (Store n) (QubitD n)) φ) (qftSub n)
      (SourceAssertion.identity φ) := by
  refine SourceDerivTot.countedIdentity (rungCounter n) (fun σ => n - 1 - σ.1.1)
    φ hφ (fun _ _ => rfl) _ ?_ ?_
  · exact SourceDerivTot.unitary_identity (ladReg n) (ladGate n) _ fun σ hσ =>
      (Reg.pair _ _ (QFTTriple.ctrl_ne_tgt n (σ := σ.1) (hk σ hσ.1) hσ.2)).inj
  · intro z
    exact SourceDerivTot.unitary_identity (ladReg n) (ladGate n) _ fun σ hσ =>
      (Reg.pair _ _ (QFTTriple.ctrl_ne_tgt n (σ := σ.1) (hk σ hσ.1) hσ.2.1)).inj

/-- The whole circuit preserves every predicate of the stored input array,
on every quantum input. Taking `p := fun x => x = x₀` expresses read-only `x`. -/
theorem inputPreservedDeriv (p : (Fin n → Bool) → Prop) :
    SourceDerivTot (SourceAssertion.ofAssn (Assn.one : Assn (Store n) (QubitD n)) fun σ => p σ.2)
      (qftCir n) (SourceAssertion.identity fun σ => p σ.2) := by
  have hi : SourceDerivTot
      (SourceAssertion.ofAssn (Assn.one : Assn (Store n) (QubitD n)) fun σ => p σ.2)
      (qftIter n) (SourceAssertion.identity fun σ => p σ.2) := by
    refine SourceDerivTot.countedIdentity (stageCounter n) (fun _ => n) _
      (fun _ _ => Iff.rfl) (fun _ _ => rfl) _ ?_ ?_
    · refine SourceDerivTot.seq
        (SourceDerivTot.unitary_identity (hReg n) (hGate n) _
          (fun σ _ => (Reg.single (QFTTriple.ctrl n σ.1)).inj)) ?_
      exact qftSub_preserves n (fun _ _ => Iff.rfl) (fun _ h => h.2)
    · intro z
      refine SourceDerivTot.seq
        (SourceDerivTot.unitary_identity (hReg n) (hGate n) _
          (fun σ _ => (Reg.single (QFTTriple.ctrl n σ.1)).inj)) ?_
      exact qftSub_preserves n (fun _ _ => Iff.rfl) (fun _ h => h.2.1)
  refine SourceDerivTot.seq hi ?_
  refine SourceDerivTot.countedIdentity (stageCounter n) (fun _ => n / 2) _
    (fun _ _ => Iff.rfl) (fun _ _ => rfl) _ ?_ ?_
  · exact SourceDerivTot.unitary_identity (swapReg n) (swapGate n) _ fun σ hσ =>
      (Reg.pair _ _ (QFTTriple.ctrl_ne_mir n (σ := σ.1) hσ.2)).inj
  · intro z
    exact SourceDerivTot.unitary_identity (swapReg n) (swapGate n) _ fun σ hσ =>
      (Reg.pair _ _ (QFTTriple.ctrl_ne_mir n (σ := σ.1) hσ.2.1)).inj

theorem qftDeriv : SourceDerivTot
    (SourceAssertion.ofAssn (inputAssn n) (fun _ => True)) (qftCir n)
    (SourceAssertion.ofAssn (outputAssn n) (fun _ => True)) := by
  refine SourceDerivTot.seq (SourceDerivTot.conseq ?_ (qftIter_deriv n) ?_)
    (SourceDerivTot.conseq (SourceAssertion.entails_refl _) (revCirc_deriv n) ?_)
  · apply SourceAssertion.entails_ofAssn
    · intro _ h; exact h
    · intro σ _
      simp only [inputAssn, Assn.ofStateFam_op, basisState, qftStageFam_zero]
      exact le_rfl
  · apply SourceAssertion.entails_ofAssn
    · intro _ h; exact h
    · intro σ _
      simp only [Assn.ofStateFam_op, qftRevFamN, qftRevFam_zero, qftStageFam_full]
      exact le_rfl
  · apply SourceAssertion.entails_ofAssn
    · intro _ h; exact h
    · intro σ _
      simp only [outputAssn, Assn.ofStateFam_op, qftRevFamN, qftRevFam_half]
      rw [fourierState_eq_prodV n σ.2]
      simp only [revIdx_val]
      exact le_rfl

theorem qftValid : validTot (inputAssn n) (qftCir n) (outputAssn n) := by
  simpa only [SourceAssertion.toAssn_ofAssn_true] using (qftDeriv n).sound

/-- The Hadamard exchanges the next plus factor for zero. -/
private theorem zeroPrefix_step {k : ℕ} (hk : k < n) :
    Function.update (QFTUniform.zeroPrefix n k) (cell n k)
      ((H : 𝕢 →ₗ[ℂ] 𝕢) (QFTUniform.zeroPrefix n k (cell n k))) =
      QFTUniform.zeroPrefix n (k + 1) := by
  have hc : QFTUniform.zeroPrefix n k (cell n k) = qplus :=
    if_neg (by rw [cell_val n hk]; omega)
  rw [hc, H_qplus]
  funext i
  by_cases hi : i = cell n k
  · subst hi
    rw [Function.update_self]
    exact (if_pos (by rw [cell_val n hk]; omega)).symm
  · rw [Function.update_of_ne hi]
    have hv : (i : ℕ) ≠ k := fun h => hi (Fin.ext (h.trans (cell_val n hk).symm))
    simp only [QFTUniform.zeroPrefix]
    split_ifs <;> first | rfl | omega

open QFTUniform in
/-- The controlled-phase ladder fixes the zero control, for the stored-input program. -/
theorem ladderUniform {φ : Store n → Prop}
    (hφ : ∀ σ v, φ ((rungCounter n).set σ v) ↔ φ σ)
    (hk : ∀ σ, φ σ → σ.1.1 < n) :
    SourceDerivTot
      (SourceAssertion.ofAssn (Assn.ofStateFam
        (fun σ : Store n => prodV (QubitD n) (W := univ) (zeroPrefix n (σ.1.1 + 1)))
        (fun σ => norm_prodV_eq_one _ (norm_zeroPrefix n (σ.1.1 + 1)))) φ)
      (qftSub n)
      (SourceAssertion.ofAssn (Assn.ofStateFam
        (fun σ : Store n => prodV (QubitD n) (W := univ) (zeroPrefix n (σ.1.1 + 1)))
        (fun σ => norm_prodV_eq_one _ (norm_zeroPrefix n (σ.1.1 + 1)))) φ) := by
  refine SourceDerivTot.countedStateChainVar (rungCounter n)
    (fun σ => n - 1 - σ.1.1) φ hφ (fun _ _ => rfl)
    (fun _ σ => prodV (QubitD n) (W := univ) (zeroPrefix n (σ.1.1 + 1)))
    (fun _ σ => norm_prodV_eq_one _ (norm_zeroPrefix n (σ.1.1 + 1)))
    (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) ?_ ?_
  · exact SourceDerivTot.countedRung_pair_fam (ladReg n) (ladGate n)
      (fun σ => QFTTriple.ctrl n σ.1) (fun σ => QFTTriple.tgt n σ.1)
      (fun σ hσ => QFTTriple.ctrl_ne_tgt n (σ := σ.1) (hk σ hσ.1) hσ.2)
      (fun σ => cphase (2 * Real.pi / 2 ^ (σ.1.2 + 2)))
      (fun σ => norm_zeroPrefix n (σ.1.1 + 1))
      (fun σ => norm_zeroPrefix n (σ.1.1 + 1))
      (fun σ hσ => by
        have hn := QFTTriple.ctrl_ne_tgt n (σ := σ.1) (hk σ hσ.1) hσ.2
        refine ⟨(Reg.pair _ _ hn).inj, ?_⟩
        simp only [ladGate, QFTTriple.ladGate, dif_pos hn]
        rfl)
      (fun σ hσ => by
        have hc : zeroPrefix n (σ.1.1 + 1) (QFTTriple.ctrl n σ.1) = q0 :=
          if_pos (by
            change (cell n σ.1.1).val < σ.1.1 + 1
            rw [cell_val n (hk σ hσ.1)]
            omega)
        refine ⟨zeroPrefix n (σ.1.1 + 1) (QFTTriple.ctrl n σ.1),
          zeroPrefix n (σ.1.1 + 1) (QFTTriple.tgt n σ.1), ?_, ?_⟩
        · rw [hc]; exact control_vpair_q0 _ _
        · simp only [Function.update_eq_self])
  · intro z
    exact SourceDerivTot.unitary_identity (ladReg n) (ladGate n) _ fun σ hσ =>
      (Reg.pair _ _ (QFTTriple.ctrl_ne_tgt n (σ := σ.1) (hk σ hσ.1) hσ.2.1)).inj

open QFTUniform in
/-- Source stage derivation for the uniform input, preserving the exact program. -/
theorem iterUniform : SourceDerivTot
    (SourceAssertion.ofAssn (allPlusA (QubitL n) (Store n)) (fun _ => True))
    (qftIter n)
    (SourceAssertion.ofAssn (allZerosA (QubitL n) (Store n)) (fun _ => True)) := by
  refine SourceDerivTot.countedStateChainVar
    (hv₀ := fun _ => norm_allPlusOn (QubitL n))
    (hv₁ := fun _ => norm_allZerosOn (QubitL n)) (stageCounter n) (fun _ => n) (fun _ => True)
    (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (fun k _ => prodV (QubitD n) (W := univ) (zeroPrefix n k))
    (fun k _ => norm_prodV_eq_one _ (norm_zeroPrefix n k))
    (fun _ _ _ => rfl) ?_ ?_ ?_ ?_
  · intro _ _; exact congrArg _ (zeroPrefix_zero n)
  · intro _ _; exact congrArg _ (zeroPrefix_full n)
  · refine SourceDerivTot.seq ?_ (ladderUniform n (fun _ _ => Iff.rfl) (fun _ h => h.2))
    exact SourceDerivTot.countedRung_single_fam (hReg n) (hGate n)
      (fun σ => QFTTriple.ctrl n σ.1) (fun _ => H)
      (fun σ => norm_zeroPrefix n σ.1.1) (fun σ => norm_zeroPrefix n (σ.1.1 + 1))
      (fun σ _ => ⟨(Reg.single (QFTTriple.ctrl n σ.1)).inj, rfl⟩)
      (fun σ hσ => zeroPrefix_step n hσ.2)
  · intro z
    refine SourceDerivTot.seq
      (SourceDerivTot.unitary_identity (hReg n) (hGate n) _
        (fun σ _ => (Reg.single (QFTTriple.ctrl n σ.1)).inj)) ?_
    exact qftSub_preserves n (fun _ _ => Iff.rfl) (fun _ h => h.2.1)

/-- Source reversal derivation fixes the all-zero input. -/
theorem reversalUniform : SourceDerivTot
    (SourceAssertion.ofAssn (allZerosA (QubitL n) (Store n)) (fun _ => True))
    (revCirc n)
    (SourceAssertion.ofAssn (allZerosA (QubitL n) (Store n)) (fun _ => True)) := by
  refine SourceDerivTot.countedStateChainVar
    (hv₀ := fun _ => norm_allZerosOn (QubitL n))
    (hv₁ := fun _ => norm_allZerosOn (QubitL n)) (stageCounter n) (fun _ => n / 2) (fun _ => True)
    (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (fun _ _ => prodV (QubitD n) (W := univ) (fun _ => q0))
    (fun _ _ => norm_prodV_eq_one _ (fun _ => norm_q0))
    (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) ?_ ?_
  · exact SourceDerivTot.countedRung_pair_fam (swapReg n) (swapGate n)
      (v := fun _ _ => q0) (w := fun _ _ => q0)
      (fun σ => QFTTriple.ctrl n σ.1) (fun σ => QFTTriple.mir n σ.1)
      (fun σ hσ => QFTTriple.ctrl_ne_mir n (σ := σ.1) hσ.2) (fun _ => SWAP)
      (fun _ _ => norm_q0) (fun _ _ => norm_q0)
      (fun σ hσ => by
        have hn := QFTTriple.ctrl_ne_mir n (σ := σ.1) hσ.2
        refine ⟨(Reg.pair _ _ hn).inj, ?_⟩
        simp only [swapGate, QFTTriple.swapGate, dif_pos hn]
        rfl)
      (fun _ _ => ⟨q0, q0, SWAP_vpair _ _, by simp only [Function.update_eq_self]⟩)
  · intro z
    exact SourceDerivTot.unitary_identity (swapReg n) (swapGate n) _ fun σ hσ =>
      (Reg.pair _ _ (QFTTriple.ctrl_ne_mir n (σ := σ.1) hσ.2.1)).inj

/-- Uniform-input source correctness of the same stored-input circuit. -/
theorem qftUniformDeriv : SourceDerivTot
    (SourceAssertion.ofAssn (allPlusA (QubitL n) (Store n)) (fun _ => True))
    (qftCir n)
    (SourceAssertion.ofAssn (allZerosA (QubitL n) (Store n)) (fun _ => True)) :=
  (iterUniform n).seq (reversalUniform n)

end Qhl.QFTClassicalSource

namespace Qhl.QFTArbitraryClassicalSource
open Finset QFTClassicalTriple QFTArbitrary
open QFTTriple (qftSubOp qftIterOp qftCirOp revCircOp ctrl_ne_tgt ctrl_ne_mir
  passOpH passOpLad passOpSwap ctrl)
variable (n : ℕ) [NeZero n]
theorem qftSub_deriv (v : (Store n) → HS (QubitD n) (univ : Finset (QubitL n)))
    (hv : ∀ σ, ‖v σ‖ = 1) (hvset : ∀ σ m, v ((rungCounter n).set σ m) = v σ)
    {φ : (Store n) → Prop} (hφ : ∀ σ m, φ ((rungCounter n).set σ m) ↔ φ σ)
    (hk : ∀ σ, φ σ → σ.1.1 < n) :
    SourceDerivTot (SourceAssertion.ofAssn (Assn.ofStateFam v hv) φ) (qftSub n)
      (SourceAssertion.ofAssn (Assn.ofStateFam (fun σ : Store n => qftSubOp n σ.1.1 (v σ))
        (fun σ : Store n => norm_eq_one_of_isUnitary (isUnitary_qftSubOp n σ.1.1) (hv σ))) φ) := by
  refine SourceDerivTot.countedStateChainVar (rungCounter n)
    (fun σ => n - 1 - σ.1.1) φ hφ (fun _ _ => rfl)
    (fun m (σ : Store n) => ladderPre n σ.1.1 m (v σ))
    (fun m (σ : Store n) => norm_eq_one_of_isUnitary (isUnitary_ladderPre n σ.1.1 m) (hv σ))
    (fun _ σ m => congrArg _ (hvset σ m)) (fun _ _ => rfl) ?_ ?_ ?_
  · intro σ _
    rw [ladderPre_full]
  · simp only [rungCounter, CounterLens.pullbackFst, CounterLens.pullback,
      StoreLens.fst, CounterLens.snd, Function.comp_def]
    exact SourceDerivTot.countedRung_fam (ladReg n) (ladGate n) _ _ fun σ hσ => by
      have hne := ctrl_ne_tgt n (hk σ hσ.1) hσ.2
      have hd : Function.Injective (ladReg n σ) := (Reg.pair _ _ hne).inj
      refine ⟨hd, ?_⟩
      rw [ladderPre_succ n σ.1.1 σ.1.2 hσ.2]
      change regLift ⟨ladReg n σ, _⟩ (ladGate n σ) _ = passOpLad n σ.1 _
      rw [passOpLad, dif_pos hne]
      rfl
  · intro z
    exact SourceDerivTot.unitary_identity (ladReg n) (ladGate n) _ fun σ hσ =>
      (Reg.pair _ _ (ctrl_ne_tgt n (hk σ hσ.1) hσ.2.1)).inj


variable (ψ : HS (QubitD n) (univ : Finset (QubitL n))) (hψ : ‖ψ‖ = 1)

/-- Each stage advances the circuit prefix by a genuine source derivation. -/
theorem stage_deriv : SourceDerivTot
    (SourceAssertion.ofAssn
      (Assn.ofStateFam (fun σ : Store n => iterPre n σ.1.1 ψ)
        (fun σ => norm_eq_one_of_isUnitary (isUnitary_iterPre n σ.1.1) hψ))
      (fun σ => True ∧ σ.1.1 < n))
    ((Prog.unitary 1 (hReg n) (hGate n)).seq (qftSub n))
    (SourceAssertion.ofAssn
      (Assn.ofStateFam (fun σ : Store n => iterPre n (σ.1.1 + 1) ψ)
        (fun σ => norm_eq_one_of_isUnitary (isUnitary_iterPre n (σ.1.1 + 1)) hψ))
      (fun σ => True ∧ σ.1.1 < n)) := by
  let v : (Store n) → HS (QubitD n) (univ : Finset (QubitL n)) :=
    fun σ => passOpH n (σ.1.1, 0) (iterPre n σ.1.1 ψ)
  have hv σ : ‖v σ‖ = 1 := norm_eq_one_of_isUnitary (isUnitary_passOpH n _)
    (norm_eq_one_of_isUnitary (isUnitary_iterPre n σ.1.1) hψ)
  refine SourceDerivTot.seq
    (B := SourceAssertion.ofAssn (Assn.ofStateFam v hv) (fun σ => True ∧ σ.1.1 < n))
    (SourceDerivTot.countedRung_fam (hReg n) (hGate n) _ hv
      (fun σ _ => ⟨(Reg.single _).inj, rfl⟩)) ?_
  refine SourceDerivTot.conseq (SourceAssertion.entails_refl _)
    (qftSub_deriv n v hv (fun _ _ => rfl) (fun _ _ => Iff.rfl) (fun _ h => h.2)) ?_
  apply SourceAssertion.entails_ofAssn
  · intro _ h; exact h
  · intro σ hσ
    apply le_of_eq
    rw [Assn.ofStateFam_op, Assn.ofStateFam_op, iterPre_succ n σ.1.1 hσ.2]
    rfl

/-- The source stage loop on an arbitrary input, independent of Fourier identities. -/
theorem qftIter_deriv : SourceDerivTot
    (SourceAssertion.ofAssn (Assn.ofState ψ hψ) (fun _ => True)) (qftIter n)
    (SourceAssertion.ofAssn
      (Assn.ofState (qftIterOp n ψ)
        (norm_eq_one_of_isUnitary (isUnitary_qftIterOp n) hψ)) (fun _ => True)) := by
  refine SourceDerivTot.countedStateChainVar
    (hv₀ := fun _ => hψ)
    (hv₁ := fun _ => norm_eq_one_of_isUnitary (isUnitary_qftIterOp n) hψ)
    (stageCounter n) (fun _ => n)
    (fun _ => True) (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (fun k _ => iterPre n k ψ)
    (fun k _ => norm_eq_one_of_isUnitary (isUnitary_iterPre n k) hψ)
    (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => by rw [iterPre_full])
    (stage_deriv n ψ hψ) ?_
  intro z
  refine SourceDerivTot.seq
    (SourceDerivTot.unitary_identity (hReg n) (hGate n) _
      (fun σ _ => (Reg.single (ctrl n σ.1)).inj)) ?_
  exact QFTClassicalSource.qftSub_preserves n (fun _ _ => Iff.rfl) (fun _ h => h.2.1)

/-- The source reversal loop on an arbitrary unit input. -/
theorem revCirc_deriv : SourceDerivTot
    (SourceAssertion.ofAssn (Assn.ofState ψ hψ) (fun _ => True)) (revCirc n)
    (SourceAssertion.ofAssn
      (Assn.ofState (revCircOp n ψ)
        (norm_eq_one_of_isUnitary (isUnitary_revCircOp n) hψ)) (fun _ => True)) := by
  refine SourceDerivTot.countedStateChainVar
    (hv₀ := fun _ => hψ)
    (hv₁ := fun _ => norm_eq_one_of_isUnitary (isUnitary_revCircOp n) hψ)
    (stageCounter n) (fun _ => n / 2)
    (fun _ => True) (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (fun k _ => revPre n k ψ)
    (fun k _ => norm_eq_one_of_isUnitary (isUnitary_revPre n k) hψ)
    (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => by rw [revPre_full]) ?_ ?_
  · simp only [stageCounter, CounterLens.pullbackFst, CounterLens.pullback,
      StoreLens.fst, CounterLens.fst, Function.comp_def]
    exact SourceDerivTot.countedRung_fam (swapReg n) (swapGate n) _ _ fun σ hσ => by
      have hne := ctrl_ne_mir n (σ := σ.1) hσ.2
      refine ⟨(Reg.pair _ _ hne).inj, ?_⟩
      rw [show revPre n (σ.1.1 + 1) = passOpSwap n (σ.1.1, 0) ∘ₗ revPre n σ.1.1 from
        chainPre_finRange_succ _ hσ.2]
      change regLift ⟨swapReg n σ, _⟩ (swapGate n σ) _ = passOpSwap n σ.1 _
      rw [passOpSwap, dif_pos hne]
      rfl
  · intro z
    exact SourceDerivTot.unitary_identity (swapReg n) (swapGate n) _ fun σ hσ =>
      (Reg.pair _ _ (ctrl_ne_mir n (σ := σ.1) hσ.2.1)).inj

/-- Supporting circuit-output triple, built entirely from source constructors. -/
theorem qftDeriv : SourceDerivTot
    (SourceAssertion.ofAssn (Assn.ofState ψ hψ) (fun _ => True)) (qftCir n)
    (SourceAssertion.ofAssn (Assn.ofState (qftCirOp n ψ) (norm_qftCirOp n ψ hψ))
      (fun _ => True)) :=
  (qftIter_deriv n ψ hψ).seq (revCirc_deriv n (qftIterOp n ψ)
    (norm_eq_one_of_isUnitary (isUnitary_qftIterOp n) hψ))

theorem qftValid : validTot (Assn.ofState ψ hψ) (qftCir n)
    (Assn.ofState (qftCirOp n ψ) (norm_qftCirOp n ψ hψ)) := by
  simpa only [SourceAssertion.toAssn_ofAssn_true] using (qftDeriv n ψ hψ).sound
end Qhl.QFTArbitraryClassicalSource


namespace Qhl.QFTClassicalSource
open Finset QFTClassicalTriple
variable (n : ℕ) [NeZero n]
/-- The stored-input program on arbitrary quantum inputs, with the independent Fourier target. -/
theorem qftAllInputDeriv (ψ : HS (QubitD n) (univ : Finset (QubitL n))) (hψ : ‖ψ‖ = 1) :
    SourceDerivTot
      (SourceAssertion.ofAssn (Assn.ofState ψ hψ) (fun _ => True)) (qftCir n)
      (SourceAssertion.ofAssn
        (Assn.ofState ((qftOp n : EndM (QubitD n) (univ : Finset (QubitL n))) ψ)
          (norm_eq_one_of_isUnitary (qftOp n).isUnitary hψ)) (fun _ => True)) := by
  refine SourceDerivTot.conseq (SourceAssertion.entails_refl _)
    (QFTArbitraryClassicalSource.qftDeriv n ψ hψ) ?_
  apply SourceAssertion.entails_ofAssn
  · intro _ h; exact h
  · intro σ _
    exact le_of_eq (QFTCompleteSource.qft_projector_from_triples n ψ)
end Qhl.QFTClassicalSource

namespace Qhl.QFTClassicalSource
open Finset QFTClassicalTriple
variable (n : ℕ) [NeZero n]

/-- Source soundness yields the original identity-effect input-preservation triple. -/
theorem inputPreservedValid (p : (Fin n → Bool) → Prop) :
    validTot ((Assn.one : Assn (Store n) (QubitD n)).mask fun σ => p σ.2)
      (qftCir n) (Assn.one.mask fun σ => p σ.2) := by
  have h := (inputPreservedDeriv n p).sound
  change validTot
    (SourceAssertion.ofAssn (Assn.one : Assn (Store n) (QubitD n)) (fun σ => p σ.2)).toAssn
    (qftCir n)
    (SourceAssertion.ofAssn (Assn.one : Assn (Store n) (QubitD n)) (fun σ => p σ.2)).toAssn at h
  simpa only [SourceAssertion.toAssn_ofAssn] using h

/-- The uniform-input semantic export follows from its own source derivation. -/
theorem qftUniformValid : validTot
    (Assn.ofState (allPlusOn (QubitL n)) (norm_allPlusOn (QubitL n))) (qftCir n)
    (Assn.ofState (allZerosOn (QubitL n)) (norm_allZerosOn (QubitL n))) := by
  simpa only [SourceAssertion.toAssn_ofAssn_true, allPlusA, allZerosA]
    using (qftUniformDeriv n).sound

/-- The stored-input circuit's arbitrary-input semantic Fourier guarantee. -/
theorem qftAllInputValid (ψ : HS (QubitD n) (univ : Finset (QubitL n))) (hψ : ‖ψ‖ = 1) :
    validTot (Assn.ofState ψ hψ) (qftCir n)
      (Assn.ofState ((qftOp n : EndM (QubitD n) (univ : Finset (QubitL n))) ψ)
        (norm_eq_one_of_isUnitary (qftOp n).isUnitary hψ)) := by
  simpa only [SourceAssertion.toAssn_ofAssn_true] using (qftAllInputDeriv n ψ hψ).sound
end Qhl.QFTClassicalSource
