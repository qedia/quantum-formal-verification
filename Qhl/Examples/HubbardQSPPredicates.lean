import Qhl.Examples.HubbardQSPSuccess

/-! Generic system-effect specification of the initialized phased-walk loop.
The block is characterized on every input by a supplied unit eigenbasis with
strictly interior normalized eigenvalues. No angle synthesis or simulation
approximation is asserted. -/
namespace Qhl.HubbardQSPPredicates
open Qhl Qhl.HubbardLCU Qhl.HubbardQSP Qhl.HubbardQSPSuccess
open Qhl.BravyiKitaev Qhl.HubbardLCUSuccess Finset
open scoped ComplexInnerProductSpace ComplexOrder
variable (x : ℕ) (hx : 0 < x) (d : ℕ)
variable (K : EndM (QubitCells (SysL x)) (univ : Finset (SysL x))) (hK : IsEffect K)

noncomputable def post : Assn (STQc d) (QubitCells (WL x)) where
  op _ := sysEmb x ∘ₗ K ∘ₗ LinearMap.adjoint (sysEmb x)
  isEffect _ := by
    constructor
    · apply (LinearMap.nonneg_iff_isPositive _).mpr
      simpa only [LinearMap.adjoint_adjoint] using
        hK.isPositive.adjoint_conj (LinearMap.adjoint (sysEmb x))
    · apply le_trans (b := ancZeroEff x) _ (isEffect_ancZeroEff x).2
      rw [LinearMap.le_def]
      have h := ((LinearMap.le_def _ _).mp hK.2).adjoint_conj
        (LinearMap.adjoint (sysEmb x))
      simpa only [LinearMap.adjoint_adjoint, LinearMap.comp_sub, LinearMap.sub_comp,
        Module.End.one_eq_id, LinearMap.id_comp, ancZeroEff, sysEmb] using h


noncomputable def invariant : Assn (STQc d) (QubitCells (WL x)) where
  op σ := LinearMap.adjoint (walkRem x hx d σ) ∘ₗ (post x d K hK).op σ ∘ₗ walkRem x hx d σ
  isEffect σ := isEffect_conj ((post x d K hK).isEffect σ)
    (le_of_eq (isUnitary_walkN x hx (coefQ d σ) (phiSeq d (phis d σ)) _ _).1)

theorem invariant_op (σ : STQc d) : (invariant x hx d K hK).op σ =
    LinearMap.adjoint (walkRem x hx d σ) ∘ₗ
      (sysEmb x ∘ₗ K ∘ₗ LinearMap.adjoint (sysEmb x)) ∘ₗ walkRem x hx d σ := rfl

noncomputable def pre : Assn (STQc d) (QubitCells (WL x)) :=
  ((invariant x hx d K hK).comp fun σ : STQc d => (σ.1, σ.2.1, 0)).initPre
    (fun _ => ancS x)

noncomputable def block (σ : STQc d) :
    EndM (QubitCells (SysL x)) (univ : Finset (SysL x)) :=
  LinearMap.adjoint (sysEmb x) ∘ₗ
    walkN x hx (coefQ d σ) (phiSeq d (phis d σ)) 0 d ∘ₗ sysEmb x

/-- Exact all-input precondition, including all cross-eigenspace entries of K. -/
theorem pre_op (σ : STQc d) :
    (pre x hx d K hK).op σ = sysLift (L₂ := AncL x)
      (LinearMap.adjoint (block x hx d σ) ∘ₗ K ∘ₗ block x hx d σ) := by
  have hi : (pre x hx d K hK).op σ = sysLift (L₂ := AncL x)
      (LinearMap.adjoint (sysEmb x) ∘ₗ
        ((invariant x hx d K hK).comp fun σ : STQc d => (σ.1, σ.2.1, 0)).op σ ∘ₗ
        sysEmb x) := initPre_ancCells_op (L₁ := SysL x) (L₂ := AncL x) _ σ
  rw [hi]
  congr 1
  simp only [Assn.comp_op, invariant, post, block, walkRem, cnt, coefQ, phis,
    Nat.sub_zero, LinearMap.adjoint_comp, LinearMap.adjoint_adjoint,
    LinearMap.comp_assoc]

/-- Source-rule preservation of the arbitrary-effect backward invariant. -/
theorem bodyInvariant : SourceDerivTot
    (SourceAssertion.ofAssn (invariant x hx d K hK) (fun σ => True ∧ gdQ d σ = true))
    (bodyProg x hx d) (SourceAssertion.ofAssn (invariant x hx d K hK) (fun _ => True)) := by
  refine .conseq ?_ (HubbardQSPSuccess.Source.bodyWp x hx d (invariant x hx d K hK)
    (fun _ _ => rfl) (fun _ _ => rfl)) (SourceAssertion.entails_refl _)
  apply SourceAssertion.entails_ofAssn _ _ _ _ (fun _ _ => trivial)
  intro σ hσ
  have hlt : cnt d σ < d := by simpa [gdQ] using hσ.2
  apply le_of_eq
  rw [wpBody_op, invariant_op, invariant_op, walkRem_split x hx d σ hlt,
    adjoint_comp_conj]

theorem loop : SourceDerivTot
    (SourceAssertion.ofAssn (invariant x hx d K hK) (fun _ => True))
    (.while (gdQ d) (bodyProg x hx d))
    (SourceAssertion.ofAssn (invariant x hx d K hK) (fun σ => True ∧ gdQ d σ = false)) := by
  exact .whileLoop (gdQ d) (fun σ => (rank d σ : Int))
    (fun _ _ => Int.natCast_nonneg _) (bodyInvariant x hx d K hK)
    (HubbardQSP.Source.bodyIdentityRank x hx d)

theorem circuit : SourceDerivTot
    (SourceAssertion.ofAssn ((invariant x hx d K hK).comp
      fun σ : STQc d => (σ.1, σ.2.1, 0)) (fun _ => True))
    (qspProg x hx d) (SourceAssertion.ofAssn (post x d K hK) (fun _ => True)) := by
  refine .conseq (SourceAssertion.entails_refl _)
    (.seq (.assign _ (SourceAssertion.ofAssn (invariant x hx d K hK) (fun _ => True)))
      (loop x hx d K hK)) ?_
  apply SourceAssertion.entails_ofAssn _ _ _ _ (fun _ _ => trivial)
  intro σ hσ
  have hge : d ≤ cnt d σ := by simpa [gdQ] using hσ.2
  have hw : walkRem x hx d σ = 1 := by
    unfold walkRem
    rw [Nat.sub_eq_zero_of_le hge]
    rfl
  change LinearMap.adjoint (walkRem x hx d σ) ∘ₗ _ ∘ₗ walkRem x hx d σ ≤ _
  rw [hw, LinearMap.adjoint_one, Module.End.one_eq_id, LinearMap.id_comp, LinearMap.comp_id]

/-- Source-rule derivation for every system effect, including literal initialization. -/
theorem deriv : SourceDerivTot
    (SourceAssertion.ofAssn (pre x hx d K hK) (fun _ => True))
    (qspInitProg x hx d) (SourceAssertion.ofAssn (post x d K hK) (fun _ => True)) := by
  exact .seq (.initProg (fun _ => ancS x)
    (SourceAssertion.ofAssn ((invariant x hx d K hK).comp
      fun σ : STQc d => (σ.1, σ.2.1, 0)) (fun _ => True))) (circuit x hx d K hK)

/-- Restrict the source precondition to any explicit classical domain, for example
stores carrying a strict-spectrum eigenbasis used by the spectral identification. -/
theorem derivUnder (φ : STQc d → Prop) : SourceDerivTot
    (SourceAssertion.ofAssn (pre x hx d K hK) φ)
    (qspInitProg x hx d) (SourceAssertion.ofAssn (post x d K hK) (fun _ => True)) := by
  refine .conseq ?_ (deriv x hx d K hK) (SourceAssertion.entails_refl _)
  exact SourceAssertion.entails_ofAssn _ _ _ _ (fun _ _ => trivial) (fun _ _ => le_rfl)

theorem valid : validTot (pre x hx d K hK) (qspInitProg x hx d) (post x d K hK) := by
  simpa only [SourceAssertion.toAssn_ofAssn_true] using (deriv x hx d K hK).sound

/-- Spectral functional calculus for the independently defined 2×2 QSP entry.
The basis is supplied explicitly; no eigenbasis existence theorem is assumed here. -/
noncomputable def spectralPolynomial {ι : Type*}
    (b : Module.Basis ι ℂ (HS (QubitCells (SysL x)) (univ : Finset (SysL x))))
    (e : ι → ℝ) (σ : STQc d) :
    EndM (QubitCells (SysL x)) (univ : Finset (SysL x)) :=
  b.constr ℂ (fun i => Qubitization.qspPoly (e i / lam x (coefQ d σ))
    (phiSeq d (phis d σ)) d • b i)

/-- The compressed circuit block equals the independently specified spectral
polynomial on all inputs, under an explicit strict-spectrum eigenbasis hypothesis. -/
theorem block_eq_spectralPolynomial {ι : Type*}
    (b : Module.Basis ι ℂ (HS (QubitCells (SysL x)) (univ : Finset (SysL x))))
    (e : ι → ℝ) (σ : STQc d) (hlam : 0 < lam x (coefQ d σ))
    (hnorm : ∀ i, ‖b i‖ = 1)
    (heig : ∀ i, hubbardOp x (coefQ d σ).1 (coefQ d σ).2 (b i) = (e i : ℂ) • b i)
    (hstrict : ∀ i, (e i / lam x (coefQ d σ)) ^ 2 < 1) :
    block x hx d σ = spectralPolynomial x d b e σ := by
  apply b.ext
  intro i
  rw [spectralPolynomial, Module.Basis.constr_basis]
  change LinearMap.adjoint (sysEmb x)
    (Qubitization.passProd _ _ _ _ 0 d (sysEmb x (b i))) = _
  rw [Qubitization.passProd_emb]
  exact Qubitization.emb_adj_qspIter
    (hubbard_qubitization x hx (coefQ d σ) hlam (b i) (hnorm i) (e i) (heig i))
    (hstrict i) _ d

/-- The source triple's precondition is the polynomial-transform predicate,
not only the weakest precondition of a named circuit operator. -/
theorem pre_op_spectralPolynomial {ι : Type*}
    (b : Module.Basis ι ℂ (HS (QubitCells (SysL x)) (univ : Finset (SysL x))))
    (e : ι → ℝ) (σ : STQc d) (hlam : 0 < lam x (coefQ d σ))
    (hnorm : ∀ i, ‖b i‖ = 1)
    (heig : ∀ i, hubbardOp x (coefQ d σ).1 (coefQ d σ).2 (b i) = (e i : ℂ) • b i)
    (hstrict : ∀ i, (e i / lam x (coefQ d σ)) ^ 2 < 1) :
    (pre x hx d K hK).op σ = sysLift (L₂ := AncL x)
      (LinearMap.adjoint (spectralPolynomial x d b e σ) ∘ₗ K ∘ₗ
        spectralPolynomial x d b e σ) := by
  rw [pre_op, block_eq_spectralPolynomial x hx d b e σ hlam hnorm heig hstrict]

end Qhl.HubbardQSPPredicates
#print axioms Qhl.HubbardQSPPredicates.deriv
#print axioms Qhl.HubbardQSPPredicates.pre_op

#print axioms Qhl.HubbardQSPPredicates.pre_op_spectralPolynomial

#print axioms Qhl.HubbardQSPPredicates.derivUnder
