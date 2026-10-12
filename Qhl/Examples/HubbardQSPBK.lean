import Qhl.Examples.HubbardQSPPredicates
import Qhl.Examples.BKTransformWp
import Qhl.Logic.Subroutine
import Qhl.Logic.SysLiftRegister

/-! QSP with the literal Bravyi–Kitaev circuit on the system register. -/
namespace Qhl.HubbardQSPBK
open Qhl HubbardLCU HubbardQSP HubbardQSPSuccess HubbardLCUSuccess BravyiKitaev Finset
open scoped ComplexInnerProductSpace ComplexOrder

variable (x : ℕ) (hx : 0 < x) (d : ℕ)

/-- Only BK's two counters are written; coefficients and phases are retained. -/
def bkStore : StoreLens (STQc d) (ℕ × ℕ) where
  get σ := (σ.1.1, σ.1.2.1)
  put σ k := ((k.1, k.2, coefQ d σ), σ.2)

@[simp] theorem bkStore_get_put (σ : STQc d) (k : ℕ × ℕ) :
    (bkStore d).get ((bkStore d).put σ k) = k := rfl

@[simp] theorem bkStore_coef (σ : STQc d) (k : ℕ × ℕ) :
    coefQ d ((bkStore d).put σ k) = coefQ d σ := rfl

@[simp] theorem bkStore_phis (σ : STQc d) (k : ℕ × ℕ) :
    phis d ((bkStore d).put σ k) = phis d σ := rfl

@[simp] theorem bkStore_cnt (σ : STQc d) (k : ℕ × ℕ) :
    cnt d ((bkStore d).put σ k) = cnt d σ := rfl

/-- Structural register placement retains each conditional CNOT and both loops. -/
noncomputable def bkPrefix : Prog (STQc d) (QubitCells (WL x)) :=
  ((BKTransform.bkProg x).onReg (Function.Embedding.inl)).mapStore (bkStore d)

/-- The paper's circuit, beginning with BK and retaining the prepared ancillas. -/
noncomputable def qspBKCircuit : Prog (STQc d) (QubitCells (WL x)) :=
  (bkPrefix x d).seq (qspProg x hx d)

/-- Ancilla initialization, the actual BK circuit, and the existing QSP loop. -/
noncomputable def qspBKProg : Prog (STQc d) (QubitCells (WL x)) :=
  (Prog.init fun _ => ancS x).seq (qspBKCircuit x hx d)

/-- Initialization preserves an input whose ancillas are already zero. -/
theorem initState (ψ : HS (QubitCells (SysL x)) (univ : Finset (SysL x)))
    (hψ : ‖ψ‖ = 1) :
    SourceDerivTot (SourceAssertion.ofAssn (Ppre x d ψ hψ) (fun _ => True))
      (Prog.init fun _ => ancS x)
      (SourceAssertion.ofAssn (Ppre x d ψ hψ) (fun _ => True)) := by
  refine .conseq ?_ (.initProg (fun _ => ancS x)
    (SourceAssertion.ofAssn (Ppre x d ψ hψ) (fun _ => True))) (SourceAssertion.entails_refl _)
  apply SourceAssertion.entails_ofAssn _ _ _ _ (fun _ _ => trivial)
  intro σ _
  change (Ppre x d ψ hψ).op σ ≤ ((Ppre x d ψ hψ).initPre (fun _ => ancCells (SysL x) (AncL x))).op σ
  rw [initPre_ancCells_op]
  have he : LinearMap.adjoint (sysEmb x) (sysEmb x ψ) = ψ := embAdj_emb x ψ
  change outerLM (sysEmb x ψ) (sysEmb x ψ) ≤ sysLift (L₂ := AncL x)
    (LinearMap.adjoint (sysEmb x) ∘ₗ outerLM (sysEmb x ψ) (sysEmb x ψ) ∘ₗ sysEmb x)
  rw [adjoint_comp_outerLM_self_comp, he]
  rw [sysLift]
  have hterm : ∀ e : AncL x → Bool,
      0 ≤ ancEmbed (L₁ := SysL x) e ∘ₗ outerLM ψ ψ ∘ₗ
        LinearMap.adjoint (ancEmbed (L₁ := SysL x) e) := by
    intro e
    apply (LinearMap.nonneg_iff_isPositive _).mpr
    simpa only [LinearMap.adjoint_adjoint] using
      (isPositive_outerLM_self ψ).adjoint_conj (LinearMap.adjoint (ancEmbed (L₁ := SysL x) e))
  have h := Finset.single_le_sum (fun e _ => hterm e) (Finset.mem_univ (anc0 x))
  have heq : ancEmbed (L₁ := SysL x) (anc0 x) ∘ₗ outerLM ψ ψ ∘ₗ
      LinearMap.adjoint (ancEmbed (L₁ := SysL x) (anc0 x)) =
      outerLM (sysEmb x ψ) (sysEmb x ψ) := by
    simpa only [LinearMap.adjoint_adjoint, sysEmb] using
      (adjoint_comp_outerLM_self_comp
        (LinearMap.adjoint (ancEmbed (L₁ := SysL x) (anc0 x))) ψ)
  rw [heq] at h
  exact h

/-- The two already existing LCU counters serve as BK counters before the walk. -/
theorem bkPrefix_eq : bkPrefix x d =
    BKTransformWp.prog x Function.Embedding.inl (cOuterQ d) (cInnerQ d) := rfl

/-- The placed, nested BK loops transform every counter-independent effect. -/
theorem prefixDeriv (Y : Assn (STQc d) (QubitCells (WL x)))
    (hYo : ∀ σ k, Y.op ((cOuterQ d).set σ k) = Y.op σ)
    (hYi : ∀ σ k, Y.op ((cInnerQ d).set σ k) = Y.op σ) :
    SourceDerivTot (SourceAssertion.ofAssn
      (BKTransformWp.pre x Function.Embedding.inl Y) (fun _ => True))
      (bkPrefix x d) (SourceAssertion.ofAssn Y (fun _ => True)) := by
  rw [bkPrefix_eq]
  exact BKTransformWp.sourceDeriv x Function.Embedding.inl (cOuterQ d) (cInnerQ d)
    (fun _ _ => rfl) (fun _ => True) (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl)
    Y hYo hYi

/-- A literal placed BK rung has the native BK operator on the system. -/
theorem stepWp_op (l k : ℕ) (Y : Assn (STQc d) (QubitCells (WL x))) (σ : STQc d) :
    (BKTransformWp.stepWp x Function.Embedding.inl (fun _ => l) k Y).op σ =
      LinearMap.adjoint (sysLift (L₂ := AncL x) (BKTransform.rungOp x l k)) ∘ₗ
        Y.op σ ∘ₗ sysLift (L₂ := AncL x) (BKTransform.rungOp x l k) := by
  rw [BKTransformWp.stepWp_op]
  by_cases h : liveG x l k
  · rw [dif_pos h, BKTransform.rungOp, dif_pos h]
    have hg : BKTransformWp.gateOp x Function.Embedding.inl l k h =
        sysLift (L₂ := AncL x) (regLift ⟨BKTransform.regE x (l,k),
          BKTransform.distE_of_live x h⟩ (BKTransform.gateE x (l,k))) :=
      regLift_inl_eq_sysLift ⟨BKTransform.regE x (l,k), BKTransform.distE_of_live x h⟩ _
    rw [hg]
  · rw [dif_neg h, BKTransform.rungOp, dif_neg h, sysLift_one,
      LinearMap.adjoint_one, Module.End.one_eq_id, LinearMap.id_comp, LinearMap.comp_id]

theorem levelWp_op (l : ℕ) (Y : Assn (STQc d) (QubitCells (WL x))) (σ : STQc d) :
    (BKTransformWp.levelWp x Function.Embedding.inl l Y).op σ =
      LinearMap.adjoint (sysLift (L₂ := AncL x) (BKTransform.levelOp x l)) ∘ₗ
        Y.op σ ∘ₗ sysLift (L₂ := AncL x) (BKTransform.levelOp x l) := by
  rw [BKTransformWp.levelWp, wpSuffix_zero_op_conj _ _ _
    (fun k => sysLift (L₂ := AncL x) (BKTransform.rungOp x l k)) σ
    (fun k _ A => stepWp_op x d l k A σ)]
  rw [sysLift_chainOp, ← BKTransform.midOp_eq_chainOp_range]
  rfl

theorem prefixPre_op (Y : Assn (STQc d) (QubitCells (WL x))) (σ : STQc d) :
    (BKTransformWp.pre x Function.Embedding.inl Y).op σ =
      LinearMap.adjoint (sysLift (L₂ := AncL x) (BKTransform.bkUnitary x).val) ∘ₗ
        Y.op σ ∘ₗ sysLift (L₂ := AncL x) (BKTransform.bkUnitary x).val := by
  rw [BKTransformWp.pre, wpSuffix_zero_op_conj _ _ _
    (fun l => sysLift (L₂ := AncL x) (BKTransform.levelOp x l)) σ
    (fun l _ A => levelWp_op x d l A σ)]
  rw [sysLift_chainOp, ← BKTransform.atOp_eq_chainOp_range]
  rw [← BKTransform.bkCircuitOp, BKTransform.bkCircuitOp_eq_bkUnitary]

variable (K : EndM (QubitCells (SysL x)) (univ : Finset (SysL x))) (hK : IsEffect K)

noncomputable def entry : Assn (STQc d) (QubitCells (WL x)) :=
  (HubbardQSPPredicates.invariant x hx d K hK).comp
    (fun σ : STQc d => (σ.1, σ.2.1, 0))

noncomputable def pre : Assn (STQc d) (QubitCells (WL x)) :=
  (BKTransformWp.pre x Function.Embedding.inl (entry x hx d K hK)).initPre
    (fun _ => ancS x)

/-- Every system effect is propagated through initialization, actual BK, and QSP. -/
theorem deriv : SourceDerivTot
    (SourceAssertion.ofAssn (pre x hx d K hK) (fun _ => True))
    (qspBKProg x hx d)
    (SourceAssertion.ofAssn (HubbardQSPPredicates.post x d K hK) (fun _ => True)) := by
  exact .seq (.initProg (fun _ => ancS x)
    (SourceAssertion.ofAssn (BKTransformWp.pre x Function.Embedding.inl
      (entry x hx d K hK)) (fun _ => True)))
    (.seq (prefixDeriv x d (entry x hx d K hK) (fun _ _ => rfl) (fun _ _ => rfl))
      (HubbardQSPPredicates.circuit x hx d K hK))

theorem derivUnder (φ : STQc d → Prop) : SourceDerivTot
    (SourceAssertion.ofAssn (pre x hx d K hK) φ)
    (qspBKProg x hx d)
    (SourceAssertion.ofAssn (HubbardQSPPredicates.post x d K hK) (fun _ => True)) := by
  refine .conseq ?_ (deriv x hx d K hK) (SourceAssertion.entails_refl _)
  exact SourceAssertion.entails_ofAssn _ _ _ _ (fun _ _ => trivial) (fun _ _ => le_rfl)

theorem valid : validTot (pre x hx d K hK) (qspBKProg x hx d)
    (HubbardQSPPredicates.post x d K hK) := by
  simpa only [SourceAssertion.toAssn_ofAssn_true] using (deriv x hx d K hK).sound

theorem validUnder (φ : STQc d → Prop) :
    validTot (SourceAssertion.ofAssn (pre x hx d K hK) φ).toAssn
      (qspBKProg x hx d) (HubbardQSPPredicates.post x d K hK) := by
  simpa only [SourceAssertion.toAssn_ofAssn_true] using (derivUnder x hx d K hK φ).sound

/-- The QSP block composed with the independent BK unitary. -/
noncomputable def encodedBlock (σ : STQc d) :
    EndM (QubitCells (SysL x)) (univ : Finset (SysL x)) :=
  HubbardQSPPredicates.block x hx d σ ∘ₗ (BKTransform.bkUnitary x).val

/-- Compression of the prefixed phased walk has the BK factor on the right. -/
theorem encodedBlock_eq (σ : STQc d) :
    LinearMap.adjoint (sysEmb x) ∘ₗ
      walkN x hx (coefQ d σ) (phiSeq d (phis d σ)) 0 d ∘ₗ
      sysLift (L₂ := AncL x) (BKTransform.bkUnitary x).val ∘ₗ sysEmb x =
      encodedBlock x hx d σ := by
  apply LinearMap.ext
  intro v
  simp only [LinearMap.comp_apply, sysEmb, sysLift_apply_emb,
    encodedBlock, HubbardQSPPredicates.block]

/-- The source precondition is B† F† K F B on every input, with no diagonal restriction. -/
theorem pre_op (σ : STQc d) :
    (pre x hx d K hK).op σ = sysLift (L₂ := AncL x)
      (LinearMap.adjoint (BKTransform.bkUnitary x).val ∘ₗ
        LinearMap.adjoint (HubbardQSPPredicates.block x hx d σ) ∘ₗ K ∘ₗ
        HubbardQSPPredicates.block x hx d σ ∘ₗ (BKTransform.bkUnitary x).val) := by
  change ((BKTransformWp.pre x Function.Embedding.inl (entry x hx d K hK)).initPre
    (fun _ => ancCells (SysL x) (AncL x))).op σ = _
  rw [initPre_ancCells_op, prefixPre_op]
  have hcomp : sysLift (L₂ := AncL x) (BKTransform.bkUnitary x).val ∘ₗ sysEmb x =
      sysEmb x ∘ₗ (BKTransform.bkUnitary x).val := by
    apply LinearMap.ext
    intro v
    exact sysLift_apply_emb (L₁ := SysL x) (L₂ := AncL x) (BKTransform.bkUnitary x).val (anc0 x) v
  congr 1
  change LinearMap.adjoint (sysEmb x) ∘ₗ
    (LinearMap.adjoint (sysLift (L₂ := AncL x) (BKTransform.bkUnitary x).val) ∘ₗ
      (entry x hx d K hK).op σ ∘ₗ sysLift (L₂ := AncL x) (BKTransform.bkUnitary x).val) ∘ₗ
      sysEmb x = _
  calc
    _ = LinearMap.adjoint (sysLift (L₂ := AncL x) (BKTransform.bkUnitary x).val ∘ₗ sysEmb x) ∘ₗ
        (entry x hx d K hK).op σ ∘ₗ
        (sysLift (L₂ := AncL x) (BKTransform.bkUnitary x).val ∘ₗ sysEmb x) := by
      simp only [LinearMap.adjoint_comp, LinearMap.comp_assoc]
    _ = _ := by
      rw [hcomp]
      simp only [entry, Assn.comp_op, HubbardQSPPredicates.invariant,
        HubbardQSPPredicates.post, HubbardQSPPredicates.block, walkRem, cnt, coefQ, phis,
        Nat.sub_zero, LinearMap.adjoint_comp, LinearMap.adjoint_adjoint, LinearMap.comp_assoc]

/-- The all-input spectral block retains the actual initial BK transformation. -/
theorem encodedBlock_eq_spectralPolynomial {ι : Type*}
    (b : Module.Basis ι ℂ (HS (QubitCells (SysL x)) (univ : Finset (SysL x))))
    (e : ι → ℝ) (σ : STQc d) (hlam : 0 < lam x (coefQ d σ))
    (hnorm : ∀ i, ‖b i‖ = 1)
    (heig : ∀ i, hubbardOp x (coefQ d σ).1 (coefQ d σ).2 (b i) = (e i : ℂ) • b i)
    (hstrict : ∀ i, (e i / lam x (coefQ d σ)) ^ 2 < 1) :
    encodedBlock x hx d σ =
      HubbardQSPPredicates.spectralPolynomial x d b e σ ∘ₗ (BKTransform.bkUnitary x).val := by
  rw [encodedBlock, HubbardQSPPredicates.block_eq_spectralPolynomial
    x hx d b e σ hlam hnorm heig hstrict]

/-- The spectral interpretation of the full source precondition. -/
theorem pre_op_spectralPolynomial {ι : Type*}
    (b : Module.Basis ι ℂ (HS (QubitCells (SysL x)) (univ : Finset (SysL x))))
    (e : ι → ℝ) (σ : STQc d) (hlam : 0 < lam x (coefQ d σ))
    (hnorm : ∀ i, ‖b i‖ = 1)
    (heig : ∀ i, hubbardOp x (coefQ d σ).1 (coefQ d σ).2 (b i) = (e i : ℂ) • b i)
    (hstrict : ∀ i, (e i / lam x (coefQ d σ)) ^ 2 < 1) :
    (pre x hx d K hK).op σ = sysLift (L₂ := AncL x)
      (LinearMap.adjoint (BKTransform.bkUnitary x).val ∘ₗ
        LinearMap.adjoint (HubbardQSPPredicates.spectralPolynomial x d b e σ) ∘ₗ K ∘ₗ
        HubbardQSPPredicates.spectralPolynomial x d b e σ ∘ₗ (BKTransform.bkUnitary x).val) := by
  rw [pre_op, HubbardQSPPredicates.block_eq_spectralPolynomial
    x hx d b e σ hlam hnorm heig hstrict]

variable (ψ : HS (QubitCells (SysL x)) (univ : Finset (SysL x))) (hψ : ‖ψ‖ = 1)

/-- The actual BK prefix transforms an arbitrary coherent input, with ancillas retained. -/
theorem prefixState : SourceDerivTot
    (SourceAssertion.ofAssn (Ppre x d ψ hψ) (fun _ => True))
    (bkPrefix x d)
    (SourceAssertion.ofAssn (Ppre x d ((BKTransform.bkUnitary x).val ψ)
      (norm_eq_one_of_isUnitary (BKTransform.bkUnitary x).isUnitary hψ)) (fun _ => True)) := by
  refine .conseq ?_ (prefixDeriv x d
    (Ppre x d ((BKTransform.bkUnitary x).val ψ)
      (norm_eq_one_of_isUnitary (BKTransform.bkUnitary x).isUnitary hψ))
    (fun _ _ => rfl) (fun _ _ => rfl)) (SourceAssertion.entails_refl _)
  apply SourceAssertion.entails_ofAssn _ _ _ _ (fun _ _ => trivial)
  intro σ _
  apply le_of_eq
  rw [prefixPre_op, Ppre_op, Ppre_op, adjoint_comp_outerLM_comp, adjoint_sysLift]
  have hact : sysLift (L₂ := AncL x) (LinearMap.adjoint (BKTransform.bkUnitary x).val)
      (sysEmb x ((BKTransform.bkUnitary x).val ψ)) = sysEmb x ψ := by
    rw [sysEmb, sysLift_apply_emb,
      adjoint_apply_apply (BKTransform.bkUnitary x).isUnitary]
  rw [hact]

/-- Source state specification of the uninitialized circuit in the proof outline. -/
theorem stateCircuitDeriv : SourceDerivTot
    (SourceAssertion.ofAssn (Ppre x d ψ hψ) (fun _ => True))
    (qspBKCircuit x hx d)
    (SourceAssertion.ofAssn (Qpost x hx d ((BKTransform.bkUnitary x).val ψ)
      (norm_eq_one_of_isUnitary (BKTransform.bkUnitary x).isUnitary hψ)) (fun _ => True)) :=
  .seq (prefixState x d ψ hψ)
    (HubbardQSP.Source.qspDeriv x hx d ((BKTransform.bkUnitary x).val ψ)
      (norm_eq_one_of_isUnitary (BKTransform.bkUnitary x).isUnitary hψ))

theorem stateCircuitValid : validTot (Ppre x d ψ hψ) (qspBKCircuit x hx d)
    (Qpost x hx d ((BKTransform.bkUnitary x).val ψ)
      (norm_eq_one_of_isUnitary (BKTransform.bkUnitary x).isUnitary hψ)) := by
  simpa only [SourceAssertion.toAssn_ofAssn_true] using (stateCircuitDeriv x hx d ψ hψ).sound

/-- Source derivation for the full store-dependent output state after actual BK. -/
theorem stateDeriv : SourceDerivTot
    (SourceAssertion.ofAssn (Ppre x d ψ hψ) (fun _ => True))
    (qspBKProg x hx d)
    (SourceAssertion.ofAssn (Qpost x hx d ((BKTransform.bkUnitary x).val ψ)
      (norm_eq_one_of_isUnitary (BKTransform.bkUnitary x).isUnitary hψ)) (fun _ => True)) :=
  .seq (initState x d ψ hψ) (stateCircuitDeriv x hx d ψ hψ)

theorem stateValid : validTot (Ppre x d ψ hψ) (qspBKProg x hx d)
    (Qpost x hx d ((BKTransform.bkUnitary x).val ψ)
      (norm_eq_one_of_isUnitary (BKTransform.bkUnitary x).isUnitary hψ)) := by
  simpa only [SourceAssertion.toAssn_ofAssn_true] using (stateDeriv x hx d ψ hψ).sound

end Qhl.HubbardQSPBK

#print axioms Qhl.HubbardQSPBK.deriv
#print axioms Qhl.HubbardQSPBK.valid
#print axioms Qhl.HubbardQSPBK.stateDeriv
#print axioms Qhl.HubbardQSPBK.stateValid
#print axioms Qhl.HubbardQSPBK.pre_op_spectralPolynomial

#print axioms Qhl.HubbardQSPBK.derivUnder
#print axioms Qhl.HubbardQSPBK.validUnder

#print axioms Qhl.HubbardQSPBK.stateCircuitDeriv
#print axioms Qhl.HubbardQSPBK.stateCircuitValid
