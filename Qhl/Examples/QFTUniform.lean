import Qhl.Examples.QFTTriple
import Qhl.Gate.ControlledU

/-!
# The QFT circuit on the uniform input

A separate source-rule derivation sends the all-plus product state to the
all-zero product state. It uses only single-gate actions: Hadamard sends plus
to zero, controlled phases fix a zero control, and swaps fix two zero factors.
No composite-operator correctness result is used.
-/
namespace Qhl.QFTUniform
open Finset QFTTriple
variable (n : ℕ) [NeZero n]

/-- The completed prefix is zero and the remaining factors are plus. -/
noncomputable def zeroPrefix (k : ℕ) (i : QubitL n) : 𝕢 :=
  if (i : ℕ) < k then q0 else qplus

theorem norm_zeroPrefix (k : ℕ) (i : QubitL n) : ‖zeroPrefix n k i‖ = 1 := by
  unfold zeroPrefix
  split_ifs <;> simp

theorem zeroPrefix_zero : zeroPrefix n 0 = fun _ => qplus := by
  funext i
  exact if_neg (Nat.not_lt_zero _)

theorem zeroPrefix_full : zeroPrefix n n = fun _ => q0 := by
  funext i
  exact if_pos i.isLt

private theorem zeroPrefix_step {k : ℕ} (hk : k < n) :
    Function.update (zeroPrefix n k) (cell n k)
      ((H : 𝕢 →ₗ[ℂ] 𝕢) (zeroPrefix n k (cell n k))) = zeroPrefix n (k + 1) := by
  have hc : zeroPrefix n k (cell n k) = qplus :=
    if_neg (by rw [cell_val n hk]; omega)
  rw [hc, H_qplus]
  funext i
  by_cases hi : i = cell n k
  · subst hi
    rw [Function.update_self]
    exact (if_pos (by rw [cell_val n hk]; omega)).symm
  · rw [Function.update_of_ne hi]
    have hv : (i : ℕ) ≠ k := fun h => hi (Fin.ext (h.trans (cell_val n hk).symm))
    simp only [zeroPrefix]
    split_ifs <;> first | rfl | omega

/-- The phase ladder preserves a prefix that already contains its zero control. -/
theorem ladderUniform {φ : (ℕ × ℕ) → Prop}
    (hφ : ∀ σ v, φ (σ.1, v) ↔ φ σ) (hk : ∀ σ, φ σ → σ.1 < n) :
    DerivTot
      ((Assn.ofStateFam
        (fun σ : ℕ × ℕ => prodV (QubitD n) (W := univ) (zeroPrefix n (σ.1 + 1)))
        (fun σ => norm_prodV_eq_one _ (norm_zeroPrefix n (σ.1 + 1)))).mask φ)
      (qftSub n)
      ((Assn.ofStateFam
        (fun σ : ℕ × ℕ => prodV (QubitD n) (W := univ) (zeroPrefix n (σ.1 + 1)))
        (fun σ => norm_prodV_eq_one _ (norm_zeroPrefix n (σ.1 + 1)))).mask φ) := by
  refine DerivTot.countedStateChainVarSource (CounterLens.snd ℕ) hφ (fun _ _ => rfl)
    (fun _ σ => prodV (QubitD n) (W := univ) (zeroPrefix n (σ.1 + 1)))
    (fun _ σ => norm_prodV_eq_one _ (norm_zeroPrefix n (σ.1 + 1)))
    (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) ?_ ?_
  · exact DerivTot.countedRung_pair_fam (ladReg n) (ladGate n) (ctrl n) (tgt n)
      (fun σ hσ => ctrl_ne_tgt n (hk σ hσ.1) hσ.2)
      (fun σ => cphase (2 * Real.pi / 2 ^ (σ.2 + 2)))
      (fun σ => norm_zeroPrefix n (σ.1 + 1)) (fun σ => norm_zeroPrefix n (σ.1 + 1))
      (fun σ hσ => by
        have hn := ctrl_ne_tgt n (hk σ hσ.1) hσ.2
        refine ⟨(Reg.pair _ _ hn).inj, ?_⟩
        simp only [ladGate, dif_pos hn]
        rfl)
      (fun σ hσ => by
        have hc : zeroPrefix n (σ.1 + 1) (ctrl n σ) = q0 :=
          if_pos (by change (cell n σ.1).val < σ.1 + 1; rw [cell_val n (hk σ hσ.1)]; omega)
        refine ⟨zeroPrefix n (σ.1 + 1) (ctrl n σ),
          zeroPrefix n (σ.1 + 1) (tgt n σ), ?_, ?_⟩
        · rw [hc]
          exact control_vpair_q0 _ _
        · simp only [Function.update_eq_self])
  · intro z
    exact DerivTot.unitary_identityMask (ladReg n) (ladGate n) _ fun σ hσ =>
      (Reg.pair _ _ (ctrl_ne_tgt n (hk σ hσ.1) hσ.2.1)).inj

/-- The stage loop converts the uniform product state to the all-zero state. -/
theorem iterUniform :
    DerivTot (allPlusA (QubitL n) (ℕ × ℕ)) (qftIter n)
      ((allZerosA (QubitL n) (ℕ × ℕ)).mask fun σ => σ.1 = n) := by
  refine DerivTot.countedProdChainSource (CounterLens.fst ℕ)
    (hψ₀ := fun _ => norm_qplus) (hψ₁ := fun _ => norm_q0)
    (zeroPrefix n) (norm_zeroPrefix n) (zeroPrefix_zero n) (zeroPrefix_full n) ?_ ?_
  · rw [Assn.ofFam_prodA, Assn.ofFam_prodA]
    refine DerivTot.seq ?_ (ladderUniform n (fun _ _ => Iff.rfl) (fun _ h => h))
    exact DerivTot.countedRung_single_fam (hReg n) (hGate n) (ctrl n) (fun _ => H)
      (fun σ => norm_zeroPrefix n σ.1) (fun σ => norm_zeroPrefix n (σ.1 + 1))
      (fun σ _ => ⟨(Reg.single (ctrl n σ)).inj, rfl⟩)
      (fun σ hσ => zeroPrefix_step n hσ)
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

/-- The reversal loop fixes the all-zero product state. -/
theorem reversalUniform :
    DerivTot (allZerosA (QubitL n) (ℕ × ℕ)) (revCirc n)
      ((allZerosA (QubitL n) (ℕ × ℕ)).mask fun σ => σ.1 = n / 2) := by
  refine DerivTot.countedProdChainSource (CounterLens.fst ℕ)
    (hψ₀ := fun _ => norm_q0) (hψ₁ := fun _ => norm_q0)
    (fun _ _ => q0) (fun _ _ => norm_q0) rfl rfl ?_ ?_
  · rw [Assn.ofFam_prodA]
    exact DerivTot.countedRung_pair_fam (swapReg n) (swapGate n) (ctrl n) (mir n)
      (fun σ hσ => ctrl_ne_mir n hσ) (fun _ => SWAP)
      (fun _ _ => norm_q0) (fun _ _ => norm_q0)
      (fun σ hσ => by
        have hn := ctrl_ne_mir n hσ
        refine ⟨(Reg.pair _ _ hn).inj, ?_⟩
        simp only [swapGate, dif_pos hn]
        rfl)
      (fun _ _ => ⟨q0, q0, SWAP_vpair _ _, by simp only [Function.update_eq_self]⟩)
  · intro k
    exact DerivTot.unitary_identityMask (swapReg n) (swapGate n) _ fun σ hσ =>
      (Reg.pair _ _ (ctrl_ne_mir n (by
        change σ.1 = k ∧ k < n / 2 at hσ; omega))).inj

/-- The QFT circuit sends the uniform input to the all-zero basis state. -/
theorem qftUniformDeriv :
    DerivTot (σT := ℕ × ℕ)
      (Assn.ofState (allPlusOn (QubitL n)) (norm_allPlusOn (QubitL n))) (qftCir n)
      (Assn.ofState (allZerosOn (QubitL n)) (norm_allZerosOn (QubitL n))) :=
  DerivTot.seq
    (DerivTot.conseq (Assn.le_refl' _) (iterUniform n) (Assn.mask_le_of_imp_le fun _ _ => le_rfl))
    (DerivTot.conseq (Assn.le_refl' _) (reversalUniform n)
      (Assn.mask_le_of_imp_le fun _ _ => le_rfl))

/-- Semantic validity follows from the source-rule derivation. -/
theorem qftUniformValid :
    validTot (σT := ℕ × ℕ)
      (Assn.ofState (allPlusOn (QubitL n)) (norm_allPlusOn (QubitL n))) (qftCir n)
      (Assn.ofState (allZerosOn (QubitL n)) (norm_allZerosOn (QubitL n))) :=
  (qftUniformDeriv n).sound

end Qhl.QFTUniform

namespace Qhl.QFTSource
open Finset QFTTriple
variable (n : ℕ) [NeZero n]
open QFTUniform in
/-- The controlled-phase ladder fixes the zero control, for the two-counter program. -/
theorem ladderUniform {φ : ℕ × ℕ → Prop}
    (hφ : ∀ σ v, φ ((CounterLens.snd ℕ).set σ v) ↔ φ σ)
    (hk : ∀ σ, φ σ → σ.1 < n) :
    SourceDerivTot
      (SourceAssertion.ofAssn (Assn.ofStateFam
        (fun σ : ℕ × ℕ => prodV (QubitD n) (W := univ) (zeroPrefix n (σ.1 + 1)))
        (fun σ => norm_prodV_eq_one _ (norm_zeroPrefix n (σ.1 + 1)))) φ)
      (qftSub n)
      (SourceAssertion.ofAssn (Assn.ofStateFam
        (fun σ : ℕ × ℕ => prodV (QubitD n) (W := univ) (zeroPrefix n (σ.1 + 1)))
        (fun σ => norm_prodV_eq_one _ (norm_zeroPrefix n (σ.1 + 1)))) φ) := by
  refine SourceDerivTot.countedStateChainVar (CounterLens.snd ℕ)
    (fun σ => n - 1 - σ.1) φ hφ (fun _ _ => rfl)
    (fun _ σ => prodV (QubitD n) (W := univ) (zeroPrefix n (σ.1 + 1)))
    (fun _ σ => norm_prodV_eq_one _ (norm_zeroPrefix n (σ.1 + 1)))
    (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) ?_ ?_
  · exact SourceDerivTot.countedRung_pair_fam (ladReg n) (ladGate n)
      (fun σ => QFTTriple.ctrl n σ) (fun σ => QFTTriple.tgt n σ)
      (fun σ hσ => QFTTriple.ctrl_ne_tgt n (σ := σ) (hk σ hσ.1) hσ.2)
      (fun σ => cphase (2 * Real.pi / 2 ^ (σ.2 + 2)))
      (fun σ => norm_zeroPrefix n (σ.1 + 1))
      (fun σ => norm_zeroPrefix n (σ.1 + 1))
      (fun σ hσ => by
        have hn := QFTTriple.ctrl_ne_tgt n (σ := σ) (hk σ hσ.1) hσ.2
        refine ⟨(Reg.pair _ _ hn).inj, ?_⟩
        simp only [ladGate, QFTTriple.ladGate, dif_pos hn]
        rfl)
      (fun σ hσ => by
        have hc : zeroPrefix n (σ.1 + 1) (QFTTriple.ctrl n σ) = q0 :=
          if_pos (by
            change (cell n σ.1).val < σ.1 + 1
            rw [cell_val n (hk σ hσ.1)]
            omega)
        refine ⟨zeroPrefix n (σ.1 + 1) (QFTTriple.ctrl n σ),
          zeroPrefix n (σ.1 + 1) (QFTTriple.tgt n σ), ?_, ?_⟩
        · rw [hc]; exact control_vpair_q0 _ _
        · simp only [Function.update_eq_self])
  · intro z
    exact SourceDerivTot.unitary_identity (ladReg n) (ladGate n) _ fun σ hσ =>
      (Reg.pair _ _ (QFTTriple.ctrl_ne_tgt n (σ := σ) (hk σ hσ.1) hσ.2.1)).inj

open QFTUniform in
/-- Source stage derivation for the uniform input, preserving the exact program. -/
theorem iterUniform : SourceDerivTot
    (SourceAssertion.ofAssn (allPlusA (QubitL n) (ℕ × ℕ)) (fun _ => True))
    (qftIter n)
    (SourceAssertion.ofAssn (allZerosA (QubitL n) (ℕ × ℕ)) (fun _ => True)) := by
  refine SourceDerivTot.countedStateChainVar
    (hv₀ := fun _ => norm_allPlusOn (QubitL n))
    (hv₁ := fun _ => norm_allZerosOn (QubitL n)) (CounterLens.fst ℕ) (fun _ => n) (fun _ => True)
    (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (fun k _ => prodV (QubitD n) (W := univ) (zeroPrefix n k))
    (fun k _ => norm_prodV_eq_one _ (norm_zeroPrefix n k))
    (fun _ _ _ => rfl) ?_ ?_ ?_ ?_
  · intro _ _; exact congrArg _ (zeroPrefix_zero n)
  · intro _ _; exact congrArg _ (zeroPrefix_full n)
  · refine SourceDerivTot.seq ?_ (ladderUniform n (fun _ _ => Iff.rfl) (fun _ h => h.2))
    exact SourceDerivTot.countedRung_single_fam (hReg n) (hGate n)
      (fun σ => QFTTriple.ctrl n σ) (fun _ => H)
      (fun σ => norm_zeroPrefix n σ.1) (fun σ => norm_zeroPrefix n (σ.1 + 1))
      (fun σ _ => ⟨(Reg.single (QFTTriple.ctrl n σ)).inj, rfl⟩)
      (fun σ hσ => QFTUniform.zeroPrefix_step n hσ.2)
  · intro z
    refine SourceDerivTot.seq
      (SourceDerivTot.unitary_identity (hReg n) (hGate n) _
        (fun σ _ => (Reg.single (QFTTriple.ctrl n σ)).inj)) ?_
    exact qftSub_preserves n (fun _ _ => Iff.rfl) (fun _ h => h.2.1)

/-- Source reversal derivation fixes the all-zero input. -/
theorem reversalUniform : SourceDerivTot
    (SourceAssertion.ofAssn (allZerosA (QubitL n) (ℕ × ℕ)) (fun _ => True))
    (revCirc n)
    (SourceAssertion.ofAssn (allZerosA (QubitL n) (ℕ × ℕ)) (fun _ => True)) := by
  refine SourceDerivTot.countedStateChainVar
    (hv₀ := fun _ => norm_allZerosOn (QubitL n))
    (hv₁ := fun _ => norm_allZerosOn (QubitL n))
    (CounterLens.fst ℕ) (fun _ => n / 2) (fun _ => True)
    (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (fun _ _ => prodV (QubitD n) (W := univ) (fun _ => q0))
    (fun _ _ => norm_prodV_eq_one _ (fun _ => norm_q0))
    (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) ?_ ?_
  · exact SourceDerivTot.countedRung_pair_fam (swapReg n) (swapGate n)
      (v := fun _ _ => q0) (w := fun _ _ => q0)
      (fun σ => QFTTriple.ctrl n σ) (fun σ => QFTTriple.mir n σ)
      (fun σ hσ => QFTTriple.ctrl_ne_mir n (σ := σ) hσ.2) (fun _ => SWAP)
      (fun _ _ => norm_q0) (fun _ _ => norm_q0)
      (fun σ hσ => by
        have hn := QFTTriple.ctrl_ne_mir n (σ := σ) hσ.2
        refine ⟨(Reg.pair _ _ hn).inj, ?_⟩
        simp only [QFTTriple.swapGate, dif_pos hn]
        rfl)
      (fun _ _ => ⟨q0, q0, SWAP_vpair _ _, by simp only [Function.update_eq_self]⟩)
  · intro z
    exact SourceDerivTot.unitary_identity (swapReg n) (swapGate n) _ fun σ hσ =>
      (Reg.pair _ _ (QFTTriple.ctrl_ne_mir n (σ := σ) hσ.2.1)).inj

/-- Uniform-input source correctness of the same two-counter circuit. -/
theorem qftUniformDeriv : SourceDerivTot
    (SourceAssertion.ofAssn (allPlusA (QubitL n) (ℕ × ℕ)) (fun _ => True))
    (qftCir n)
    (SourceAssertion.ofAssn (allZerosA (QubitL n) (ℕ × ℕ)) (fun _ => True)) :=
  (iterUniform n).seq (reversalUniform n)

end Qhl.QFTSource

namespace Qhl.QFTSource
variable (n : ℕ) [NeZero n]
/-- Uniform-input compatibility with the original two-counter semantic specification. -/
theorem qftUniformValid : validTot
    (Assn.ofState (allPlusOn (QubitL n)) (norm_allPlusOn (QubitL n))) (QFTTriple.qftCir n)
    (Assn.ofState (allZerosOn (QubitL n)) (norm_allZerosOn (QubitL n))) := by
  simpa only [SourceAssertion.toAssn_ofAssn_true, allPlusA, allZerosA]
    using (qftUniformDeriv n).sound
end Qhl.QFTSource
