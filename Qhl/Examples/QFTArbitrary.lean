import Qhl.Examples.QFTTriple

/-! # Source-rule QFT execution on an arbitrary unit vector

The postcondition is the actual circuit composite applied to the input. This
implementation-fidelity derivation does not use computational-basis gate action,
Fourier-state identities, or equality between the circuit and Fourier operators.
Each counted loop uses the source total-loop rule with a separate identity premise.
-/

namespace Qhl.QFTArbitrary

open Finset QFTTriple
open scoped ComplexInnerProductSpace

variable (n : ℕ) [NeZero n]

/-- Each program Hadamard lifts to a unitary on the whole register. -/
theorem isUnitary_passOpH (σ : ℕ × ℕ) : IsUnitary (passOpH n σ) :=
  isUnitary_regLift _ _

/-- The total ladder operator is unitary, including its identity off the guard. -/
theorem isUnitary_passOpLad (σ : ℕ × ℕ) : IsUnitary (passOpLad n σ) := by
  unfold passOpLad
  split
  · exact isUnitary_regLift _ _
  · exact isUnitary_one

/-- The total reversal operator is unitary, including its identity off the guard. -/
theorem isUnitary_passOpSwap (σ : ℕ × ℕ) : IsUnitary (passOpSwap n σ) := by
  unfold passOpSwap
  split
  · exact isUnitary_regLift _ _
  · exact isUnitary_one

theorem isUnitary_qftSubOp (k : ℕ) : IsUnitary (qftSubOp n k) :=
  isUnitary_chainOp _ _ fun _ => isUnitary_passOpLad n _

theorem isUnitary_qftStageOp (k : ℕ) : IsUnitary (qftStageOp n k) :=
  (isUnitary_qftSubOp n k).comp (isUnitary_passOpH n _)

theorem isUnitary_qftIterOp : IsUnitary (qftIterOp n) :=
  isUnitary_chainOp _ _ fun _ => isUnitary_qftStageOp n _

theorem isUnitary_revCircOp : IsUnitary (revCircOp n) :=
  isUnitary_chainOp _ _ fun _ => isUnitary_passOpSwap n _

theorem isUnitary_qftCirOp : IsUnitary (qftCirOp n) :=
  (isUnitary_revCircOp n).comp (isUnitary_qftIterOp n)

theorem norm_qftCirOp (ψ : HS (QubitD n) (univ : Finset (QubitL n))) (hψ : ‖ψ‖ = 1) :
    ‖qftCirOp n ψ‖ = 1 := norm_eq_one_of_isUnitary (isUnitary_qftCirOp n) hψ

/-- The ladder prefix at the current stage, acting on an arbitrary vector. -/
noncomputable def ladderPre (k m : ℕ) : EndM (QubitD n) (univ : Finset (QubitL n)) :=
  chainPre (List.finRange (n - 1 - k)) (fun j => passOpLad n (k, j)) m

theorem isUnitary_ladderPre (k m : ℕ) : IsUnitary (ladderPre n k m) :=
  isUnitary_chainOp _ _ fun _ => isUnitary_passOpLad n _

theorem ladderPre_zero (k : ℕ) : ladderPre n k 0 = 1 := rfl

theorem ladderPre_full (k : ℕ) : ladderPre n k (n - 1 - k) = qftSubOp n k :=
  chainPre_finRange_length _

theorem ladderPre_succ (k m : ℕ) (hm : m < n - 1 - k) :
    ladderPre n k (m + 1) = passOpLad n (k, m) ∘ₗ ladderPre n k m :=
  chainPre_finRange_succ _ hm

/-- The source ladder triple accepts an arbitrary store-indexed unit vector,
provided that vector and the classical frame do not read the inner counter. -/
theorem qftSub_deriv (v : (ℕ × ℕ) → HS (QubitD n) (univ : Finset (QubitL n)))
    (hv : ∀ σ, ‖v σ‖ = 1) (hvset : ∀ σ m, v (σ.1, m) = v σ)
    {φ : (ℕ × ℕ) → Prop} (hφ : ∀ σ m, φ (σ.1, m) ↔ φ σ)
    (hk : ∀ σ, φ σ → σ.1 < n) :
    DerivTot ((Assn.ofStateFam v hv).mask φ) (qftSub n)
      ((Assn.ofStateFam (fun σ : ℕ × ℕ => qftSubOp n σ.1 (v σ))
        (fun σ : ℕ × ℕ => norm_eq_one_of_isUnitary (isUnitary_qftSubOp n σ.1) (hv σ))).mask φ) := by
  refine DerivTot.countedStateChainVarSource (CounterLens.snd ℕ) hφ (fun _ _ => rfl)
    (fun m (σ : ℕ × ℕ) => ladderPre n σ.1 m (v σ))
    (fun m (σ : ℕ × ℕ) => norm_eq_one_of_isUnitary (isUnitary_ladderPre n σ.1 m) (hv σ))
    (fun _ σ m => by simp only [CounterLens.snd]; rw [hvset σ m]) (fun _ _ => rfl) ?_ ?_ ?_
  · intro σ _
    rw [ladderPre_full]
  · simp only [CounterLens.snd]
    exact DerivTot.countedRung_fam (ladReg n) (ladGate n) _ _ fun σ hσ => by
      have hne := ctrl_ne_tgt n (hk σ hσ.1) hσ.2
      have hd : Function.Injective (ladReg n σ) := (Reg.pair _ _ hne).inj
      refine ⟨hd, ?_⟩
      rw [ladderPre_succ n σ.1 σ.2 hσ.2]
      change regLift ⟨ladReg n σ, _⟩ (ladGate n σ) _ = passOpLad n σ _
      rw [passOpLad, dif_pos hne]
  · intro z
    exact DerivTot.unitary_identityMask (ladReg n) (ladGate n) _ fun σ hσ =>
      (Reg.pair _ _ (ctrl_ne_tgt n (hk σ hσ.1) hσ.2.1)).inj

/-- The stage prefix, applied to arbitrary input below. -/
noncomputable def iterPre (k : ℕ) : EndM (QubitD n) (univ : Finset (QubitL n)) :=
  chainPre (List.finRange n) (fun i => qftStageOp n i) k

theorem isUnitary_iterPre (k : ℕ) : IsUnitary (iterPre n k) :=
  isUnitary_chainOp _ _ fun _ => isUnitary_qftStageOp n _

theorem iterPre_zero : iterPre n 0 = 1 := rfl

theorem iterPre_full : iterPre n n = qftIterOp n := chainPre_finRange_length _

theorem iterPre_succ (k : ℕ) (hk : k < n) :
    iterPre n (k + 1) = qftStageOp n k ∘ₗ iterPre n k :=
  chainPre_finRange_succ _ hk

variable (ψ : HS (QubitD n) (univ : Finset (QubitL n))) (hψ : ‖ψ‖ = 1)

/-- One stage preserves the arbitrary-input circuit-prefix invariant. -/
theorem stage_deriv :
    DerivTot
      ((Assn.ofStateFam (fun σ : ℕ × ℕ => iterPre n σ.1 ψ)
        (fun σ : ℕ × ℕ => norm_eq_one_of_isUnitary (isUnitary_iterPre n σ.1) hψ)).mask
          fun σ : ℕ × ℕ => σ.1 < n)
      ((Prog.unitary 1 (hReg n) (hGate n)).seq (qftSub n))
      ((Assn.ofStateFam (fun σ : ℕ × ℕ => iterPre n (σ.1 + 1) ψ)
        (fun σ : ℕ × ℕ => norm_eq_one_of_isUnitary (isUnitary_iterPre n (σ.1 + 1)) hψ)).mask
          fun σ : ℕ × ℕ => σ.1 < n) := by
  let v : (ℕ × ℕ) → HS (QubitD n) (univ : Finset (QubitL n)) :=
    fun σ : ℕ × ℕ => passOpH n (σ.1, 0) (iterPre n σ.1 ψ)
  have hv σ : ‖v σ‖ = 1 := norm_eq_one_of_isUnitary (isUnitary_passOpH n _)
    (norm_eq_one_of_isUnitary (isUnitary_iterPre n σ.1) hψ)
  refine DerivTot.seq (B := (Assn.ofStateFam v hv).mask fun σ : ℕ × ℕ => σ.1 < n)
    (DerivTot.countedRung_fam (hReg n) (hGate n) _ hv
      (fun σ _ => ⟨(Reg.single _).inj, rfl⟩)) ?_
  refine DerivTot.conseq (Assn.le_refl' _)
    (qftSub_deriv n v hv (fun _ _ => rfl) (fun _ _ => Iff.rfl) (fun _ h => h)) ?_
  apply Assn.mask_le_mask (fun _ h => h)
  intro σ hσ
  refine le_of_eq ?_
  rw [Assn.ofStateFam_op, Assn.ofStateFam_op, iterPre_succ n σ.1 hσ]
  rfl

/-- The source stage loop on an arbitrary unit input. -/
theorem qftIter_deriv :
    DerivTot (Assn.ofStateFam (fun _ : ℕ × ℕ => ψ) (fun _ => hψ)) (qftIter n)
      (Assn.ofStateFam (fun _ : ℕ × ℕ => qftIterOp n ψ)
        (fun _ => norm_eq_one_of_isUnitary (isUnitary_qftIterOp n) hψ)) := by
  refine DerivTot.conseq (Assn.le_refl' _)
    (DerivTot.countedStateChainSource (CounterLens.fst ℕ)
      (fun k _ => iterPre n k ψ)
      (fun k _ => norm_eq_one_of_isUnitary (isUnitary_iterPre n k) hψ)
      (fun _ _ _ => rfl) rfl (by funext σ; rw [iterPre_full]) ?_ ?_)
    (Assn.mask_le_of_imp_le fun _ _ => le_rfl)
  · simpa only [Assn.ofFam_ofStateFam, CounterLens.fst] using stage_deriv n ψ hψ
  · intro k
    refine DerivTot.seq
      (DerivTot.unitary_identityMask (hReg n) (hGate n) _
        (fun σ _ => (Reg.single (ctrl n σ)).inj)) ?_
    exact DerivTot.countedIdentityVarSource (CounterLens.snd ℕ)
      (fun _ _ => Iff.rfl) (fun _ _ => rfl)
      (DerivTot.unitary_identityMask (ladReg n) (ladGate n) _
        (fun σ hσ => (Reg.pair _ _ (ctrl_ne_tgt n (by
          have h := hσ.1; change σ.1 = k ∧ k < n at h; omega) hσ.2)).inj))
      (fun z => DerivTot.unitary_identityMask (ladReg n) (ladGate n) _
        (fun σ hσ => (Reg.pair _ _ (ctrl_ne_tgt n (by
          have h := hσ.1; change σ.1 = k ∧ k < n at h; omega) hσ.2.1)).inj))

/-- The reversal prefix on arbitrary vectors. -/
noncomputable def revPre (k : ℕ) : EndM (QubitD n) (univ : Finset (QubitL n)) :=
  chainPre (List.finRange (n / 2)) (fun i => passOpSwap n (i, 0)) k

theorem isUnitary_revPre (k : ℕ) : IsUnitary (revPre n k) :=
  isUnitary_chainOp _ _ fun _ => isUnitary_passOpSwap n _

theorem revPre_full : revPre n (n / 2) = revCircOp n := chainPre_finRange_length _

/-- The source reversal loop on an arbitrary unit input. -/
theorem revCirc_deriv :
    DerivTot (Assn.ofStateFam (fun _ : ℕ × ℕ => ψ) (fun _ => hψ)) (revCirc n)
      (Assn.ofStateFam (fun _ : ℕ × ℕ => revCircOp n ψ)
        (fun _ => norm_eq_one_of_isUnitary (isUnitary_revCircOp n) hψ)) := by
  refine DerivTot.conseq (Assn.le_refl' _)
    (DerivTot.countedStateChainSource (CounterLens.fst ℕ)
      (fun k _ => revPre n k ψ)
      (fun k _ => norm_eq_one_of_isUnitary (isUnitary_revPre n k) hψ)
      (fun _ _ _ => rfl) rfl (by funext σ; rw [revPre_full]) ?_ ?_)
    (Assn.mask_le_of_imp_le fun _ _ => le_rfl)
  · rw [Assn.ofFam_ofStateFam, Assn.ofFam_ofStateFam]
    simp only [CounterLens.fst]
    exact DerivTot.countedRung_fam (swapReg n) (swapGate n) _ _ fun σ hσ => by
      have hne := ctrl_ne_mir n hσ
      have hd : Function.Injective (swapReg n σ) := (Reg.pair _ _ hne).inj
      refine ⟨hd, ?_⟩
      rw [show revPre n (σ.1 + 1) = passOpSwap n (σ.1, 0) ∘ₗ revPre n σ.1 from
        chainPre_finRange_succ _ hσ]
      change regLift ⟨swapReg n σ, _⟩ (swapGate n σ) _ = passOpSwap n σ _
      rw [passOpSwap, dif_pos hne]
  · intro k
    exact DerivTot.unitary_identityMask (swapReg n) (swapGate n) _ fun σ hσ =>
      (Reg.pair _ _ (ctrl_ne_mir n (by
        change σ.1 = k ∧ k < n / 2 at hσ; omega))).inj

/-- The literal QFT circuit on an arbitrary unit input, with its circuit-composite output. -/
theorem qftDeriv :
    DerivTot (σT := ℕ × ℕ) (Assn.ofState ψ hψ) (qftCir n)
      (Assn.ofState (qftCirOp n ψ) (norm_qftCirOp n ψ hψ)) :=
  DerivTot.seq (qftIter_deriv n ψ hψ)
    (revCirc_deriv n (qftIterOp n ψ)
      (norm_eq_one_of_isUnitary (isUnitary_qftIterOp n) hψ))

/-- Semantic validity follows from the source-rule derivation and soundness. -/
theorem qftValid :
    validTot (σT := ℕ × ℕ) (Assn.ofState ψ hψ) (qftCir n)
      (Assn.ofState (qftCirOp n ψ) (norm_qftCirOp n ψ hψ)) :=
  (qftDeriv n ψ hψ).sound

end Qhl.QFTArbitrary

namespace Qhl.QFTArbitrarySource
open Finset QFTTriple QFTArbitrary
variable (n : ℕ) [NeZero n]
theorem qftSub_deriv (v : (ℕ × ℕ) → HS (QubitD n) (univ : Finset (QubitL n)))
    (hv : ∀ σ, ‖v σ‖ = 1) (hvset : ∀ σ m, v (σ.1, m) = v σ)
    {φ : (ℕ × ℕ) → Prop} (hφ : ∀ σ m, φ (σ.1, m) ↔ φ σ)
    (hk : ∀ σ, φ σ → σ.1 < n) :
    SourceDerivTot (SourceAssertion.ofAssn (Assn.ofStateFam v hv) φ) (qftSub n)
      (SourceAssertion.ofAssn (Assn.ofStateFam (fun σ : ℕ × ℕ => qftSubOp n σ.1 (v σ))
        (fun σ : ℕ × ℕ => norm_eq_one_of_isUnitary (isUnitary_qftSubOp n σ.1) (hv σ))) φ) := by
  refine SourceDerivTot.countedStateChainVar (CounterLens.snd ℕ)
    (fun σ => n - 1 - σ.1) φ hφ (fun _ _ => rfl)
    (fun m (σ : ℕ × ℕ) => ladderPre n σ.1 m (v σ))
    (fun m (σ : ℕ × ℕ) => norm_eq_one_of_isUnitary (isUnitary_ladderPre n σ.1 m) (hv σ))
    (fun _ σ m => by simp only [CounterLens.snd]; rw [hvset σ m]) (fun _ _ => rfl) ?_ ?_ ?_
  · intro σ _
    rw [ladderPre_full]
  · simp only [CounterLens.snd]
    exact SourceDerivTot.countedRung_fam (ladReg n) (ladGate n) _ _ fun σ hσ => by
      have hne := ctrl_ne_tgt n (hk σ hσ.1) hσ.2
      have hd : Function.Injective (ladReg n σ) := (Reg.pair _ _ hne).inj
      refine ⟨hd, ?_⟩
      rw [ladderPre_succ n σ.1 σ.2 hσ.2]
      change regLift ⟨ladReg n σ, _⟩ (ladGate n σ) _ = passOpLad n σ _
      rw [passOpLad, dif_pos hne]
  · intro z
    exact SourceDerivTot.unitary_identity (ladReg n) (ladGate n) _ fun σ hσ =>
      (Reg.pair _ _ (ctrl_ne_tgt n (hk σ hσ.1) hσ.2.1)).inj


variable (ψ : HS (QubitD n) (univ : Finset (QubitL n))) (hψ : ‖ψ‖ = 1)

/-- Each stage advances the circuit prefix by a genuine source derivation. -/
theorem stage_deriv : SourceDerivTot
    (SourceAssertion.ofAssn
      (Assn.ofStateFam (fun σ : ℕ × ℕ => iterPre n σ.1 ψ)
        (fun σ => norm_eq_one_of_isUnitary (isUnitary_iterPre n σ.1) hψ))
      (fun σ => True ∧ σ.1 < n))
    ((Prog.unitary 1 (hReg n) (hGate n)).seq (qftSub n))
    (SourceAssertion.ofAssn
      (Assn.ofStateFam (fun σ : ℕ × ℕ => iterPre n (σ.1 + 1) ψ)
        (fun σ => norm_eq_one_of_isUnitary (isUnitary_iterPre n (σ.1 + 1)) hψ))
      (fun σ => True ∧ σ.1 < n)) := by
  let v : (ℕ × ℕ) → HS (QubitD n) (univ : Finset (QubitL n)) :=
    fun σ => passOpH n (σ.1, 0) (iterPre n σ.1 ψ)
  have hv σ : ‖v σ‖ = 1 := norm_eq_one_of_isUnitary (isUnitary_passOpH n _)
    (norm_eq_one_of_isUnitary (isUnitary_iterPre n σ.1) hψ)
  refine SourceDerivTot.seq
    (B := SourceAssertion.ofAssn (Assn.ofStateFam v hv) (fun σ => True ∧ σ.1 < n))
    (SourceDerivTot.countedRung_fam (hReg n) (hGate n) _ hv
      (fun σ _ => ⟨(Reg.single _).inj, rfl⟩)) ?_
  refine SourceDerivTot.conseq (SourceAssertion.entails_refl _)
    (qftSub_deriv n v hv (fun _ _ => rfl) (fun _ _ => Iff.rfl) (fun _ h => h.2)) ?_
  apply SourceAssertion.entails_ofAssn
  · intro _ h; exact h
  · intro σ hσ
    apply le_of_eq
    rw [Assn.ofStateFam_op, Assn.ofStateFam_op, iterPre_succ n σ.1 hσ.2]
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
    (CounterLens.fst ℕ) (fun _ => n)
    (fun _ => True) (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (fun k _ => iterPre n k ψ)
    (fun k _ => norm_eq_one_of_isUnitary (isUnitary_iterPre n k) hψ)
    (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => by rw [iterPre_full])
    (stage_deriv n ψ hψ) ?_
  intro z
  refine SourceDerivTot.seq
    (SourceDerivTot.unitary_identity (hReg n) (hGate n) _
      (fun σ _ => (Reg.single (ctrl n σ)).inj)) ?_
  exact QFTSource.qftSub_preserves n (fun _ _ => Iff.rfl) (fun _ h => h.2.1)

/-- The source reversal loop on an arbitrary unit input. -/
theorem revCirc_deriv : SourceDerivTot
    (SourceAssertion.ofAssn (Assn.ofState ψ hψ) (fun _ => True)) (revCirc n)
    (SourceAssertion.ofAssn
      (Assn.ofState (revCircOp n ψ)
        (norm_eq_one_of_isUnitary (isUnitary_revCircOp n) hψ)) (fun _ => True)) := by
  refine SourceDerivTot.countedStateChainVar
    (hv₀ := fun _ => hψ)
    (hv₁ := fun _ => norm_eq_one_of_isUnitary (isUnitary_revCircOp n) hψ)
    (CounterLens.fst ℕ) (fun _ => n / 2)
    (fun _ => True) (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (fun k _ => revPre n k ψ)
    (fun k _ => norm_eq_one_of_isUnitary (isUnitary_revPre n k) hψ)
    (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => by rw [revPre_full]) ?_ ?_
  · simp only [CounterLens.fst]
    exact SourceDerivTot.countedRung_fam (swapReg n) (swapGate n) _ _ fun σ hσ => by
      have hne := ctrl_ne_mir n (σ := σ) hσ.2
      refine ⟨(Reg.pair _ _ hne).inj, ?_⟩
      rw [show revPre n (σ.1 + 1) = passOpSwap n (σ.1, 0) ∘ₗ revPre n σ.1 from
        chainPre_finRange_succ _ hσ.2]
      change regLift ⟨swapReg n σ, _⟩ (swapGate n σ) _ = passOpSwap n σ _
      rw [passOpSwap, dif_pos hne]
  · intro z
    exact SourceDerivTot.unitary_identity (swapReg n) (swapGate n) _ fun σ hσ =>
      (Reg.pair _ _ (ctrl_ne_mir n (σ := σ) hσ.2.1)).inj

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
end Qhl.QFTArbitrarySource
