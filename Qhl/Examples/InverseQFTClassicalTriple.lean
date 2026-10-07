import Qhl.Examples.QFTClassicalTriple
import Qhl.Examples.InverseQFTTriple

/-! # Inverse QFT with a read-only classical input array

The width remains a fixed quantum-world parameter. The classical store and
endpoint assertions are exactly those of `QFTClassicalTriple`, with the
endpoints reversed. The literal inverse circuit traverses the QFT invariant
families backward, reading the input array from the store in every invariant.
All loop derivations use source counted-loop rules and separate identity
termination premises. The old two-counter development remains unchanged.
-/

namespace Qhl.InverseQFTClassicalTriple
open Finset
open QFTClassicalTriple
open scoped ComplexInnerProductSpace

variable (n : ℕ) [NeZero n]

def ihReg : RegExpr (Store n) (QubitL n) 1 := fun σ => InverseQFTTriple.ihReg n σ.1
noncomputable def ihGate (σ : Store n) : UnitaryOp (TSpace (QubitD n) (ihReg n σ)) :=
  InverseQFTTriple.ihGate n σ.1
def iladReg : RegExpr (Store n) (QubitL n) 2 := fun σ => InverseQFTTriple.iladReg n σ.1
noncomputable def iladGate (σ : Store n) :
    UnitaryOp (TSpace (QubitD n) (iladReg n σ)) := InverseQFTTriple.iladGate n σ.1

noncomputable def iqftSub : Prog (Store n) (QubitD n) :=
  countedProg (rungCounter n) (fun σ => σ.1.1)
    (.unitary 2 (iladReg n) (iladGate n))
noncomputable def iqftIter : Prog (Store n) (QubitD n) :=
  countedProg (stageCounter n) (fun _ => n)
    ((iqftSub n).seq (Prog.unitary 1 (ihReg n) (ihGate n)))
noncomputable def iqftRevCir : Prog (Store n) (QubitD n) :=
  (revCirc n).seq (iqftIter n)

/-- Exact constructor-level correspondence with the original inverse circuit. -/
theorem iqftRevCir_eq_mapStore :
    iqftRevCir n = (InverseQFTTriple.iqftRevCir n).mapStore StoreLens.fst := rfl

/-- Every classical update preserves the input array. -/
theorem iqftRevCir_preserves_input : (iqftRevCir n).Preserves (fun σ => σ.2) := by
  simp [iqftRevCir, iqftIter, iqftSub, revCirc, countedProg, Prog.Preserves,
    stageCounter, rungCounter, CounterLens.pullbackFst, CounterLens.pullback,
    StoreLens.fst, CounterLens.fst, CounterLens.snd]

/-- The backward reversal reads the stored array in its invariant. -/
theorem revCircBack_deriv :
    DerivTot
      ((Assn.ofStateFam (fun σ : Store n => prodV (QubitD n) (W := univ)
          (iqftRevFamN n σ.2 0))
        (fun σ : Store n => norm_prodV_eq_one _ (norm_iqftRevFamN n σ.2 0))).mask fun _ => True)
      (revCirc n)
      ((Assn.ofStateFam (fun σ : Store n => prodV (QubitD n) (W := univ)
          (iqftRevFamN n σ.2 (n / 2)))
        (fun σ : Store n =>
          norm_prodV_eq_one _ (norm_iqftRevFamN n σ.2 (n / 2)))).mask fun _ => True) := by
  refine DerivTot.countedStateChainVarSource (stageCounter n)
    (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (fun m σ => prodV (QubitD n) (W := univ) (iqftRevFamN n σ.2 m))
    (fun m σ => norm_prodV_eq_one _ (norm_iqftRevFamN n σ.2 m))
    (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) ?_ ?_
  · exact DerivTot.countedRung_pair_fam (swapReg n) (swapGate n)
      (fun σ => QFTTriple.ctrl n σ.1) (fun σ => QFTTriple.mir n σ.1)
      (fun σ hσ => QFTTriple.ctrl_ne_mir n (σ := σ.1) hσ.2) (fun _ => SWAP)
      (fun σ => norm_iqftRevFamN n σ.2 σ.1.1)
      (fun σ => norm_iqftRevFamN n σ.2 (σ.1.1 + 1))
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
        exact ⟨phaseKet (qftAngle σ.2 σ.1.1),
          phaseKet (qftAngle σ.2 (n - 1 - σ.1.1)),
          by rw [hc, hm, iqftRevFamN_left n σ.2 hk, iqftRevFamN_right n σ.2 hk, SWAP_vpair],
          by rw [hc, hm]; exact iqftRevFamN_step n σ.2 hk⟩)
  · intro z
    exact DerivTot.unitary_identityMask (swapReg n) (swapGate n) _ fun σ hσ =>
      (Reg.pair _ _ (QFTTriple.ctrl_ne_mir n (σ := σ.1) hσ.2.1)).inj

/-- The inverse controlled-phase gate advances the decreasing ladder family. -/
private theorem iladder_action (σ : Store n) (hk : σ.1.1 < n) (hj : σ.1.2 < σ.1.1) :
    ∃ hinj : Function.Injective (iladReg n σ),
      regLift (D := QubitD n) ⟨iladReg n σ, hinj⟩ (iladGate n σ)
        (prodV (QubitD n) (W := univ)
          (qftLadderFamN n σ.2 (n - 1 - σ.1.1) (σ.1.1 - σ.1.2))) =
        prodV (QubitD n) (W := univ)
          (qftLadderFamN n σ.2 (n - 1 - σ.1.1) (σ.1.1 - (σ.1.2 + 1))) := by
  have hne : InverseQFTTriple.ictrl n σ.1 ≠ InverseQFTTriple.itgt n σ.1 :=
    InverseQFTTriple.ictrl_ne_itgt n (σ := σ.1) hk hj
  refine ⟨(Reg.pair _ _ hne).inj, ?_⟩
  rw [show regLift (D := QubitD n) ⟨iladReg n σ, (Reg.pair _ _ hne).inj⟩ (iladGate n σ)
      = regLift (D := QubitD n)
          (Reg.pair (InverseQFTTriple.ictrl n σ.1) (InverseQFTTriple.itgt n σ.1) hne)
          (pairGate (D := QubitD n) (InverseQFTTriple.ictrl n σ.1) (InverseQFTTriple.itgt n σ.1) hne
            (cphase (-(2 * Real.pi / 2 ^ (σ.1.1 - 1 - σ.1.2 + 2))))) from by
    rw [show iladGate n σ = pairGate (D := QubitD n)
        (InverseQFTTriple.ictrl n σ.1) (InverseQFTTriple.itgt n σ.1) hne
        (cphase (-(2 * Real.pi / 2 ^ (σ.1.1 - 1 - σ.1.2 + 2)))) from by
      simp only [iladGate, InverseQFTTriple.iladGate]; rw [dif_pos hne]]
    rfl]
  exact regLift_cphase_neg_qftLadderFamN n σ.2 hk hj hne

theorem iqftSub_current {φ : Store n → Prop}
    (hφ : ∀ σ v, φ ((rungCounter n).set σ v) ↔ φ σ)
    (hk : ∀ σ, φ σ → σ.1.1 < n) :
    DerivTot
      ((Assn.ofStateFam (fun σ : Store n =>
        prodV (QubitD n) (W := univ) (qftStageFam n σ.2 (n - σ.1.1)))
        (fun σ => norm_prodV_eq_one _ (norm_qftStageFam n σ.2 (n - σ.1.1)))).mask φ)
      (iqftSub n)
      ((Assn.ofStateFam (fun σ : Store n =>
        prodV (QubitD n) (W := univ) (qftStageMidN n σ.2 (n - 1 - σ.1.1)))
        (fun σ => norm_prodV_eq_one _
          (norm_qftStageMidN n σ.2 (n - 1 - σ.1.1)))).mask φ) := by
    refine DerivTot.countedStateChainVarSource (rungCounter n) hφ (fun _ _ => rfl)
      (fun m σ => prodV (QubitD n) (W := univ)
        (qftLadderFamN n σ.2 (n - 1 - σ.1.1) (σ.1.1 - m)))
      (fun m σ => norm_prodV_eq_one _
        (norm_qftLadderFamN n σ.2 (n - 1 - σ.1.1) (σ.1.1 - m)))
      (fun _ _ _ => rfl) ?_ ?_ ?_ ?_
    · intro σ hσ
      apply congrArg
      have hlt := hk σ hσ
      calc
        qftLadderFamN n σ.2 (n - 1 - σ.1.1) (σ.1.1 - 0) =
            qftLadderFamN n σ.2 (n - 1 - σ.1.1) (n - 1 - (n - 1 - σ.1.1)) := by
          congr 1
          omega
        _ = qftStageFam n σ.2 ((n - 1 - σ.1.1) + 1) :=
          qftLadderFamN_full n σ.2 (by omega)
        _ = qftStageFam n σ.2 (n - σ.1.1) := by congr 1; omega
    · intro σ _
      rw [Nat.sub_self]
      exact congrArg _ (qftLadderFamN_zero n σ.2 (n - 1 - σ.1.1))
    · exact DerivTot.countedRung_fam (iladReg n) (iladGate n) _ _
        fun σ hσ => iladder_action n σ (hk σ hσ.1) hσ.2
    · intro z
      exact DerivTot.unitary_identityMask (iladReg n) (iladGate n) _ fun σ hσ =>
        (Reg.pair _ _ (InverseQFTTriple.ictrl_ne_itgt n (σ := σ.1) (hk σ hσ.1) hσ.2.1)).inj

/-- Reverse stages use the QFT stage family at the decreasing index. -/
theorem iqftIter_deriv :
    DerivTot
      ((Assn.ofStateFam (fun σ : Store n => prodV (QubitD n) (W := univ)
          (qftStageFam n σ.2 n))
        (fun σ => norm_prodV_eq_one _ (norm_qftStageFam n σ.2 n))).mask fun _ => True)
      (iqftIter n)
      ((Assn.ofStateFam (fun σ : Store n => prodV (QubitD n) (W := univ)
          (qftStageFam n σ.2 0))
        (fun σ => norm_prodV_eq_one _ (norm_qftStageFam n σ.2 0))).mask
          fun _ => True) := by
  refine DerivTot.countedStateChainVarSource (stageCounter n)
    (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (fun m σ => prodV (QubitD n) (W := univ) (qftStageFam n σ.2 (n - m)))
    (fun m σ => norm_prodV_eq_one _ (norm_qftStageFam n σ.2 (n - m)))
    (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => by rw [Nat.sub_self]) ?_ ?_
  · refine DerivTot.seq (iqftSub_current n
      (φ := fun σ => True ∧ σ.1.1 < n) (fun _ _ => Iff.rfl) (fun _ h => h.2)) ?_
    exact DerivTot.countedRung_single_fam (ihReg n) (ihGate n)
      (fun σ => InverseQFTTriple.ictrl n σ.1) (fun _ => H)
      (fun σ => norm_qftStageMidN n σ.2 (n - 1 - σ.1.1))
      (fun σ => norm_qftStageFam n σ.2 (n - (σ.1.1 + 1)))
      (fun σ _ => ⟨(Reg.single (InverseQFTTriple.ictrl n σ.1)).inj, rfl⟩)
      (fun σ hσ => by
        change Function.update _ (cell n (n - 1 - σ.1.1)) _ = _
        rw [show n - (σ.1.1 + 1) = n - 1 - σ.1.1 from by omega]
        exact qftStageMidN_step_H n σ.2 (by have h := hσ.2; omega))
  · intro z
    refine DerivTot.seq ?_
      (DerivTot.unitary_identityMask (ihReg n) (ihGate n) _
        (fun σ _ => (Reg.single (InverseQFTTriple.ictrl n σ.1)).inj))
    refine DerivTot.countedIdentityVarSource (rungCounter n)
      (fun _ _ => Iff.rfl) (fun _ _ => rfl) ?_ ?_
    · exact DerivTot.unitary_identityMask (iladReg n) (iladGate n) _ fun σ hσ =>
        (Reg.pair _ _ (InverseQFTTriple.ictrl_ne_itgt n (σ := σ.1) hσ.1.2.1 hσ.2)).inj
    · intro z'
      exact DerivTot.unitary_identityMask (iladReg n) (iladGate n) _ fun σ hσ =>
        (Reg.pair _ _ (InverseQFTTriple.ictrl_ne_itgt n (σ := σ.1) hσ.1.2.1 hσ.2.1)).inj

/-- The actual stored-x Fourier predicate is transformed into its basis predicate. -/
theorem iqftRevDeriv :
    DerivTot (outputAssn n) (iqftRevCir n) (inputAssn n) := by
  refine DerivTot.seq (DerivTot.conseq ?_ (revCircBack_deriv n) ?_)
    (DerivTot.conseq (Assn.le_refl' _) (iqftIter_deriv n) ?_)
  · intro σ
    simp only [outputAssn, Assn.ofStateFam_op, Assn.mask, if_true]
    rw [fourierState_eq_prodV n σ.2, iqftRevFamN_zero]
  · intro σ
    simp only [Assn.mask, if_true, Assn.ofStateFam_op, iqftRevFamN_half,
      qftStageFam_full]
    exact le_rfl
  · intro σ
    simp only [inputAssn, basisState, Assn.mask, if_true, Assn.ofStateFam_op,
      qftStageFam_zero]
    exact le_rfl

/-- Product-state endpoint form for register-framed reuse in QPE. This is a
consequence of the stored-input circuit derivation, not an operator shortcut. -/
theorem iqftProdDeriv :
    DerivTot
      (Assn.ofStateFam (fun σ : Store n => prodV (QubitD n) (W := univ)
        (fun i => phaseKet (qftAngle σ.2 (n - 1 - (i : ℕ)))))
        (fun _ => norm_prodV_eq_one _ fun _ => norm_phaseKet _))
      (iqftRevCir n)
      (Assn.ofStateFam (fun σ : Store n => prodV (QubitD n) (W := univ)
        (fun i => qbit (σ.2 i)))
        (fun _ => norm_prodV_eq_one _ fun _ => norm_qbit _)) := by
  refine DerivTot.conseq ?_ (iqftRevDeriv n) (fun _ => le_rfl)
  intro σ
  simp only [outputAssn, Assn.ofStateFam_op]
  rw [fourierState_eq_prodV n σ.2]

omit [NeZero n] in
/-- Freezing the stored array recovers the old inverse Fourier precondition. -/
theorem input_specialize (c : ℕ × ℕ) (x : Fin n → Bool) :
    (outputAssn n).op (c, x) =
      (Assn.ofState (σT := ℕ × ℕ) (fourierState n x) (norm_fourierState n x)).op c :=
  QFTClassicalTriple.output_specialize n c x

omit [NeZero n] in
/-- Freezing the stored array recovers the old inverse basis postcondition. -/
theorem output_specialize (c : ℕ × ℕ) (x : Fin n → Bool) :
    (inputAssn n).op (c, x) =
      (Assn.ofState (σT := ℕ × ℕ)
        (prodV (QubitD n) (W := univ) (fun i => qbit (x i)))
        (norm_prodV_eq_one _ fun _ => norm_qbit _)).op c :=
  QFTClassicalTriple.input_specialize n c x

/-- Total semantic correctness follows from source-rule soundness. -/
theorem iqftRevValid : validTot (outputAssn n) (iqftRevCir n) (inputAssn n) :=
  (iqftRevDeriv n).sound

omit [NeZero n] in
/-- The Fourier precondition has expectation one on a normalized input at every store. -/
theorem input_nonvacuous (σ : Store n) :
    expectE (outputAssn n).op ⟨σ, PDensity.pure (fourierState n σ.2)⟩ = 1 := by
  rw [expectE_pure]
  change ENNReal.ofReal (⟪fourierState n σ.2,
    (outerLM (fourierState n σ.2) (fourierState n σ.2)) (fourierState n σ.2)⟫.re) = 1
  rw [outerLM_apply]
  simp [inner_self_eq_norm_sq_to_K, norm_fourierState]

end Qhl.InverseQFTClassicalTriple

namespace Qhl.InverseQFTClassicalSource
open Finset QFTClassicalTriple InverseQFTClassicalTriple
variable (n : ℕ) [NeZero n]

/-- The backward reversal reads the stored array in its invariant. -/
theorem revCircBack_deriv :
    SourceDerivTot
      (SourceAssertion.ofAssn (Assn.ofStateFam (fun σ : Store n => prodV (QubitD n) (W := univ)
          (iqftRevFamN n σ.2 0))
        (fun σ : Store n => norm_prodV_eq_one _ (norm_iqftRevFamN n σ.2 0))) fun _ => True)
      (revCirc n)
      (SourceAssertion.ofAssn (Assn.ofStateFam (fun σ : Store n => prodV (QubitD n) (W := univ)
          (iqftRevFamN n σ.2 (n / 2)))
        (fun σ : Store n =>
          norm_prodV_eq_one _ (norm_iqftRevFamN n σ.2 (n / 2)))) fun _ => True) := by
  refine SourceDerivTot.countedStateChainVar (stageCounter n) (fun _ => n / 2) (fun _ => True)
    (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (fun m σ => prodV (QubitD n) (W := univ) (iqftRevFamN n σ.2 m))
    (fun m σ => norm_prodV_eq_one _ (norm_iqftRevFamN n σ.2 m))
    (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) ?_ ?_
  · exact SourceDerivTot.countedRung_pair_fam (swapReg n) (swapGate n)
      (fun σ => QFTTriple.ctrl n σ.1) (fun σ => QFTTriple.mir n σ.1)
      (fun σ hσ => QFTTriple.ctrl_ne_mir n (σ := σ.1) hσ.2) (fun _ => SWAP)
      (fun σ => norm_iqftRevFamN n σ.2 σ.1.1)
      (fun σ => norm_iqftRevFamN n σ.2 (σ.1.1 + 1))
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
        exact ⟨phaseKet (qftAngle σ.2 σ.1.1),
          phaseKet (qftAngle σ.2 (n - 1 - σ.1.1)),
          by rw [hc, hm, iqftRevFamN_left n σ.2 hk, iqftRevFamN_right n σ.2 hk, SWAP_vpair],
          by rw [hc, hm]; exact iqftRevFamN_step n σ.2 hk⟩)
  · intro z
    exact SourceDerivTot.unitary_identity (swapReg n) (swapGate n) _ fun σ hσ =>
      (Reg.pair _ _ (QFTTriple.ctrl_ne_mir n (σ := σ.1) hσ.2.1)).inj

theorem iqftSub_current {φ : Store n → Prop}
    (hφ : ∀ σ v, φ ((rungCounter n).set σ v) ↔ φ σ)
    (hk : ∀ σ, φ σ → σ.1.1 < n) :
    SourceDerivTot
      (SourceAssertion.ofAssn (Assn.ofStateFam (fun σ : Store n =>
        prodV (QubitD n) (W := univ) (qftStageFam n σ.2 (n - σ.1.1)))
        (fun σ => norm_prodV_eq_one _ (norm_qftStageFam n σ.2 (n - σ.1.1)))) φ)
      (iqftSub n)
      (SourceAssertion.ofAssn (Assn.ofStateFam (fun σ : Store n =>
        prodV (QubitD n) (W := univ) (qftStageMidN n σ.2 (n - 1 - σ.1.1)))
        (fun σ => norm_prodV_eq_one _
          (norm_qftStageMidN n σ.2 (n - 1 - σ.1.1)))) φ) := by
    refine SourceDerivTot.countedStateChainVar (rungCounter n)
      (fun σ => σ.1.1) φ hφ (fun _ _ => rfl)
      (fun m σ => prodV (QubitD n) (W := univ)
        (qftLadderFamN n σ.2 (n - 1 - σ.1.1) (σ.1.1 - m)))
      (fun m σ => norm_prodV_eq_one _
        (norm_qftLadderFamN n σ.2 (n - 1 - σ.1.1) (σ.1.1 - m)))
      (fun _ _ _ => rfl) ?_ ?_ ?_ ?_
    · intro σ hσ
      apply congrArg
      have hlt := hk σ hσ
      calc
        qftLadderFamN n σ.2 (n - 1 - σ.1.1) (σ.1.1 - 0) =
            qftLadderFamN n σ.2 (n - 1 - σ.1.1) (n - 1 - (n - 1 - σ.1.1)) := by
          congr 1
          omega
        _ = qftStageFam n σ.2 ((n - 1 - σ.1.1) + 1) :=
          qftLadderFamN_full n σ.2 (by omega)
        _ = qftStageFam n σ.2 (n - σ.1.1) := by congr 1; omega
    · intro σ _
      rw [Nat.sub_self]
      exact congrArg _ (qftLadderFamN_zero n σ.2 (n - 1 - σ.1.1))
    · exact SourceDerivTot.countedRung_fam (iladReg n) (iladGate n) _ _
        fun σ hσ => iladder_action n σ (hk σ hσ.1) hσ.2
    · intro z
      exact SourceDerivTot.unitary_identity (iladReg n) (iladGate n) _ fun σ hσ =>
        (Reg.pair _ _ (InverseQFTTriple.ictrl_ne_itgt n (σ := σ.1) (hk σ hσ.1) hσ.2.1)).inj

/-- Reverse stages use the QFT stage family at the decreasing index. -/
theorem iqftIter_deriv :
    SourceDerivTot
      (SourceAssertion.ofAssn (Assn.ofStateFam (fun σ : Store n => prodV (QubitD n) (W := univ)
          (qftStageFam n σ.2 n))
        (fun σ => norm_prodV_eq_one _ (norm_qftStageFam n σ.2 n))) fun _ => True)
      (iqftIter n)
      (SourceAssertion.ofAssn (Assn.ofStateFam (fun σ : Store n => prodV (QubitD n) (W := univ)
          (qftStageFam n σ.2 0))
        (fun σ => norm_prodV_eq_one _ (norm_qftStageFam n σ.2 0))) fun _ => True) := by
  refine SourceDerivTot.countedStateChainVar (stageCounter n) (fun _ => n) (fun _ => True)
    (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (fun m σ => prodV (QubitD n) (W := univ) (qftStageFam n σ.2 (n - m)))
    (fun m σ => norm_prodV_eq_one _ (norm_qftStageFam n σ.2 (n - m)))
    (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => by rw [Nat.sub_self]) ?_ ?_
  · refine SourceDerivTot.seq (iqftSub_current n
      (φ := fun σ => True ∧ σ.1.1 < n) (fun _ _ => Iff.rfl) (fun _ h => h.2)) ?_
    exact SourceDerivTot.countedRung_single_fam (ihReg n) (ihGate n)
      (fun σ => InverseQFTTriple.ictrl n σ.1) (fun _ => H)
      (fun σ => norm_qftStageMidN n σ.2 (n - 1 - σ.1.1))
      (fun σ => norm_qftStageFam n σ.2 (n - (σ.1.1 + 1)))
      (fun σ _ => ⟨(Reg.single (InverseQFTTriple.ictrl n σ.1)).inj, rfl⟩)
      (fun σ hσ => by
        change Function.update _ (cell n (n - 1 - σ.1.1)) _ = _
        rw [show n - (σ.1.1 + 1) = n - 1 - σ.1.1 from by omega]
        exact qftStageMidN_step_H n σ.2 (by have h := hσ.2; omega))
  · intro z
    refine SourceDerivTot.seq ?_
      (SourceDerivTot.unitary_identity (ihReg n) (ihGate n) _
        (fun σ _ => (Reg.single (InverseQFTTriple.ictrl n σ.1)).inj))
    refine SourceDerivTot.countedIdentity (rungCounter n) (fun σ => σ.1.1) _
      (fun _ _ => Iff.rfl) (fun _ _ => rfl) _ ?_ ?_
    · exact SourceDerivTot.unitary_identity (iladReg n) (iladGate n) _ fun σ hσ =>
        (Reg.pair _ _ (InverseQFTTriple.ictrl_ne_itgt n (σ := σ.1) hσ.1.2.1 hσ.2)).inj
    · intro z'
      exact SourceDerivTot.unitary_identity (iladReg n) (iladGate n) _ fun σ hσ =>
        (Reg.pair _ _ (InverseQFTTriple.ictrl_ne_itgt n (σ := σ.1) hσ.1.2.1 hσ.2.1)).inj

theorem iqftRevDeriv : SourceDerivTot
    (SourceAssertion.ofAssn (outputAssn n) (fun _ => True)) (iqftRevCir n)
    (SourceAssertion.ofAssn (inputAssn n) (fun _ => True)) := by
  refine SourceDerivTot.seq (SourceDerivTot.conseq ?_ (revCircBack_deriv n) ?_)
    (SourceDerivTot.conseq (SourceAssertion.entails_refl _) (iqftIter_deriv n) ?_)
  · apply SourceAssertion.entails_ofAssn
    · intro _ h; exact h
    · intro σ _
      simp only [outputAssn, Assn.ofStateFam_op]
      rw [fourierState_eq_prodV n σ.2, iqftRevFamN_zero]
  · apply SourceAssertion.entails_ofAssn
    · intro _ h; exact h
    · intro σ _
      simp only [Assn.ofStateFam_op, iqftRevFamN_half, qftStageFam_full]
      exact le_rfl
  · apply SourceAssertion.entails_ofAssn
    · intro _ h; exact h
    · intro σ _
      simp only [inputAssn, basisState, Assn.ofStateFam_op, qftStageFam_zero]
      exact le_rfl

theorem iqftRevValid : validTot (outputAssn n) (iqftRevCir n) (inputAssn n) := by
  simpa only [SourceAssertion.toAssn_ofAssn_true] using (iqftRevDeriv n).sound
/-- Product-state form used when placing the verified inverse circuit in QPE. -/
theorem iqftProdDeriv : SourceDerivTot
    (SourceAssertion.ofAssn
      (Assn.ofStateFam (fun σ : Store n => prodV (QubitD n) (W := univ)
        (fun i => phaseKet (qftAngle σ.2 (n - 1 - (i : ℕ)))))
        (fun _ => norm_prodV_eq_one _ fun _ => norm_phaseKet _)) (fun _ => True))
    (iqftRevCir n)
    (SourceAssertion.ofAssn
      (Assn.ofStateFam (fun σ : Store n => prodV (QubitD n) (W := univ)
        (fun i => qbit (σ.2 i)))
        (fun _ => norm_prodV_eq_one _ fun _ => norm_qbit _)) (fun _ => True)) := by
  refine SourceDerivTot.conseq ?_ (iqftRevDeriv n) (SourceAssertion.entails_refl _)
  apply SourceAssertion.entails_ofAssn
  · intro _ h; exact h
  · intro σ _
    simp only [outputAssn, Assn.ofStateFam_op]
    rw [fourierState_eq_prodV n σ.2]

end Qhl.InverseQFTClassicalSource
