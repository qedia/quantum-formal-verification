import Qhl.Examples.HubbardLCUSuccess

/-! Arbitrary-system-effect LCU source triples. The exact precondition display,
not merely the Hoare inequality, connects the specification to H/λ. -/
namespace Qhl.HubbardLCUPredicate
open Qhl Qhl.HubbardLCU Qhl.HubbardQSP Qhl.HubbardLCUSuccess Qhl.BravyiKitaev Finset
open scoped ComplexInnerProductSpace ComplexOrder
variable (x : ℕ) (hx : 0 < x)
variable (K : EndM (QubitCells (SysL x)) (univ : Finset (SysL x))) (hK : IsEffect K)

/-- Vacuum ancillas together with an arbitrary system predicate. -/
noncomputable def predicatePost : Assn STc (QubitCells (WL x)) :=
  ⟨fun _ => sysEmb x ∘ₗ K ∘ₗ LinearMap.adjoint (sysEmb x), fun _ => by
    constructor
    · rw [LinearMap.nonneg_iff_isPositive, isPositive_iff_inner_nonneg]
      intro u
      rw [LinearMap.comp_apply, LinearMap.comp_apply, ← LinearMap.adjoint_inner_left]
      simpa only [LinearMap.zero_apply, inner_zero_right] using
        (le_iff_inner_le _ _).mp hK.1 (LinearMap.adjoint (sysEmb x) u)
    · apply le_trans (b := ancZeroEff x)
      · rw [le_iff_inner_le]
        intro u
        change ⟪u, sysEmb x (K (LinearMap.adjoint (sysEmb x) u))⟫ ≤
          ⟪u, sysEmb x (LinearMap.adjoint (sysEmb x) u)⟫
        simpa only [Module.End.one_apply, LinearMap.adjoint_inner_left] using
          (le_iff_inner_le _ _).mp hK.2 (LinearMap.adjoint (sysEmb x) u)
      · exact (isEffect_ancZeroEff x).2⟩

noncomputable def wpU5 : Assn STc (QubitCells (WL x)) :=
  (predicatePost x K hK).unitaryPre (RegExpr.const (Reg.single (aC x (a0 x hx))))
    (fun _ => singleGate (QubitCells (WL x)) (aC x (a0 x hx)) X)

/-- wp of the counted inverse-Givens loop of UNPREPARE: the suffix family of
the `unprepT` passes at entry. -/
noncomputable def wpU4 : Assn STc (QubitCells (WL x)) :=
  wpSuffix (unprepT x hx) (HubbardLCU.NT x - 1) (wpU5 x hx K hK) 0

/-- wp of SELECT: the suffix family of the `rungT` passes at entry. -/
noncomputable def wpU3 : Assn STc (QubitCells (WL x)) :=
  wpSuffix (rungT x hx) (HubbardLCU.NT x) (wpU4 x hx K hK) 0

/-- wp of the counted Givens loop of PREPARE. -/
noncomputable def wpU2 : Assn STc (QubitCells (WL x)) :=
  wpSuffix (prepT x hx) (HubbardLCU.NT x - 1) (wpU3 x hx K hK) 0

/-- **The folded (Ax-Uni) precondition of the whole LCU circuit.** -/
noncomputable def wpLCU : Assn STc (QubitCells (WL x)) :=
  (wpU2 x hx K hK).unitaryPre (RegExpr.const (Reg.single (aC x (a0 x hx))))
    (fun _ => singleGate (QubitCells (WL x)) (aC x (a0 x hx)) X)

theorem wpU4_op_set (c : CounterLens STc) (hc : ∀ σ v, coef (c.set σ v) = coef σ)
    (σ : STc) (v : ℕ) : (wpU4 x hx K hK).op (c.set σ v) = (wpU4 x hx K hK).op σ :=
  wpSuffix_op_set (unprepT x hx) (wpU5 x hx K hK) c
    (fun k A hA σ' v' => unprepT_op_set x hx c hc k A hA σ' v')
    (fun _ _ => rfl) 0 σ v

theorem wpU3_op_set (c : CounterLens STc) (hc : ∀ σ v, coef (c.set σ v) = coef σ)
    (σ : STc) (v : ℕ) : (wpU3 x hx K hK).op (c.set σ v) = (wpU3 x hx K hK).op σ :=
  wpSuffix_op_set (rungT x hx) (wpU4 x hx K hK) c
    (fun k A hA σ' v' => rungT_op_set x hx c hc k A hA σ' v')
    (fun σ' v' => wpU4_op_set x hx K hK c hc σ' v') 0 σ v

theorem prepLoopWp :
    SourceDerivTot (SourceAssertion.ofAssn (wpU2 x hx K hK) (fun _ => True))
      (countedProg (CounterLens.fst3 ST) (fun _ => HubbardLCU.NT x - 1) (prepBody x hx))
      (SourceAssertion.ofAssn (wpU3 x hx K hK) (fun _ => True)) := by
  refine .conseq (SourceAssertion.entails_refl _)
    (SourceDerivTot.countedWpChain (CounterLens.fst3 ST) (HubbardLCU.NT x - 1)
      (fun _ => True) (prepRegE x hx) (prepGateE x hx) (prepT x hx) (wpU3 x hx K hK)
      (fun _ _ => Iff.rfl)
      (fun k A hA σ v => prepT_op_set x hx (CounterLens.fst3 ST)
        (fun _ _ => rfl) k A hA σ v)
      (fun σ v => wpU3_op_set x hx K hK (CounterLens.fst3 ST) (fun _ _ => rfl) σ v)
      (fun _ _ _ => (prepReg x _).inj)
      (fun k _ σ _ hget A => by subst hget; rfl)) ?_
  exact SourceAssertion.entails_ofAssn _ _ _ _ (fun _ _ => trivial) (fun _ _ => le_rfl)

/-- UNPREPARE's weakest-precondition loop derived from source rules. -/
theorem unprepLoopWp :
    SourceDerivTot (SourceAssertion.ofAssn (wpU4 x hx K hK) (fun _ => True))
      (countedProg (CounterLens.fst3 ST) (fun _ => HubbardLCU.NT x - 1) (unprepBody x hx))
      (SourceAssertion.ofAssn (wpU5 x hx K hK) (fun _ => True)) := by
  refine .conseq (SourceAssertion.entails_refl _)
    (SourceDerivTot.countedWpChain (CounterLens.fst3 ST) (HubbardLCU.NT x - 1)
      (fun _ => True) (unprepRegE x hx) (unprepGateE x hx) (unprepT x hx) (wpU5 x hx K hK)
      (fun _ _ => Iff.rfl)
      (fun k A hA σ v => unprepT_op_set x hx (CounterLens.fst3 ST)
        (fun _ _ => rfl) k A hA σ v)
      (fun _ _ => rfl) (fun _ _ _ => (prepReg x _).inj)
      (fun k _ σ _ hget A => by subst hget; rfl)) ?_
  exact SourceAssertion.entails_ofAssn _ _ _ _ (fun _ _ => trivial) (fun _ _ => le_rfl)

/-- Source weakest-precondition preservation through a compound SELECT rung. -/
theorem selectWpStep :
    SourceDerivTot
      (SourceAssertion.ofAssn (Assn.ofFam (CounterLens.fst3 ST).get
        (wpSuffix (rungT x hx) (HubbardLCU.NT x) (wpU4 x hx K hK)))
        (fun σ => True ∧ σ.1 < HubbardLCU.NT x))
      (rungBody x hx)
      (SourceAssertion.ofAssn (Assn.ofFam (CounterLens.fst3 ST).get
        (fun k => wpSuffix (rungT x hx) (HubbardLCU.NT x) (wpU4 x hx K hK) (k + 1)))
        (fun σ => True ∧ σ.1 < HubbardLCU.NT x)) := by
  let J : ℕ → Assn STc (QubitCells (WL x)) := fun m =>
    Assn.ofFam (CounterLens.fst3 ST).get fun k =>
      wpSuffix (letterT x hx k) (2 ^ x)
        (wpSuffix (rungT x hx) (HubbardLCU.NT x) (wpU4 x hx K hK) (k + 1)) m
  refine .seq (B := SourceAssertion.ofAssn (J 0)
    (fun σ => True ∧ σ.1 < HubbardLCU.NT x)) ?_ ?_
  · apply SourceDerivTot.unitary_ofAssn (sgnRegE x hx) (sgnGateE x hx)
      _ _ _ _ (fun _ h => h) (fun _ _ => (Reg.single _).inj)
    intro σ hσ
    rw [Assn.ofFam_op]
    simp only [CounterLens.fst3]
    rw [wpSuffix_of_lt hσ.2]
    change (rungT x hx σ.1 _).op σ ≤
      ((Assn.ofFam (CounterLens.fst3 ST).get _).unitaryPre _ _).op σ
    rw [Assn.unitaryPre_ofFam_op]
    exact le_rfl
  · refine .conseq (SourceAssertion.entails_refl _)
      (SourceDerivTot.countedFamily (CounterLens.snd3 ST) (2 ^ x)
        (fun σ => True ∧ σ.1 < HubbardLCU.NT x) J (ctrlBody x hx)
        (fun _ _ => Iff.rfl) ?_ ?_ ?_) ?_
    · intro m σ v
      change (wpSuffix (letterT x hx σ.1) (2 ^ x)
        (wpSuffix (rungT x hx) (HubbardLCU.NT x) (wpU4 x hx K hK) (σ.1 + 1)) m).op
          ((CounterLens.snd3 ST).set σ v) = _
      apply wpSuffix_op_set (letterT x hx σ.1) _ (CounterLens.snd3 ST)
        (fun k A hA σ' v' => letterT_op_set x hx (CounterLens.snd3 ST) σ.1 k A hA σ' v')
      intro σ' v'
      exact wpSuffix_op_set (rungT x hx) (wpU4 x hx K hK) (CounterLens.snd3 ST)
        (fun k A hA τ w => rungT_op_set x hx (CounterLens.snd3 ST)
          (fun _ _ => rfl) k A hA τ w)
        (fun τ w => wpU4_op_set x hx K hK (CounterLens.snd3 ST) (fun _ _ => rfl) τ w)
        (σ.1 + 1) σ' v'
    · apply SourceDerivTot.unitary_ofAssn (ctrlRegE x hx) (ctrlGateE x hx)
        _ _ _ _ (fun _ h => h) (fun _ _ => (ctrlReg x _ _).inj)
      intro σ hσ
      simp only [J, Assn.ofFam_op, CounterLens.snd3, CounterLens.fst3]
      have hm : σ.2.1 < 2 ^ x := hσ.2
      rw [wpSuffix_of_lt hm]
      rw [Assn.unitaryPre_ofFam_op, Assn.unitaryPre_ofFam_op]
      exact le_rfl
    · intro z
      exact SourceDerivTot.unitary_identity (ctrlRegE x hx) (ctrlGateE x hx) _
        (fun _ _ => (ctrlReg x _ _).inj)
    · apply SourceAssertion.entails_ofAssn _ _ _ _ (fun _ h => h.1)
      intro σ _
      simp only [J, Assn.ofFam_op, CounterLens.fst3, wpSuffix_full]
      exact le_rfl

/-- SELECT's source weakest-precondition loop. -/
theorem selectWp :
    SourceDerivTot (SourceAssertion.ofAssn (wpU3 x hx K hK) (fun _ => True))
      (selProg x hx) (SourceAssertion.ofAssn (wpU4 x hx K hK) (fun _ => True)) := by
  refine .conseq (SourceAssertion.entails_refl _)
    (SourceDerivTot.countedWpBody (CounterLens.fst3 ST) (HubbardLCU.NT x)
      (fun _ => True) (rungT x hx) (wpU4 x hx K hK) (rungBody x hx)
      (fun _ _ => Iff.rfl)
      (fun k A hA σ v => rungT_op_set x hx (CounterLens.fst3 ST)
        (fun _ _ => rfl) k A hA σ v)
      (fun σ v => wpU4_op_set x hx K hK (CounterLens.fst3 ST) (fun _ _ => rfl) σ v)
      (selectWpStep x hx K hK)
      (fun _ => HubbardLCU.Source.rungIdentity x hx _ (fun _ _ => Iff.rfl))) ?_
  exact SourceAssertion.entails_ofAssn _ _ _ _ (fun _ _ => trivial) (fun _ _ => le_rfl)

/-- The source weakest-precondition derivation for the literal entire LCU circuit. -/
theorem lcuWp :
    SourceDerivTot (SourceAssertion.ofAssn (wpLCU x hx K hK) (fun _ => True))
      (lcuProg x hx) (SourceAssertion.ofAssn (predicatePost x K hK) (fun _ => True)) := by
  refine .seq (.seq ?_ (prepLoopWp x hx K hK))
    (.seq (selectWp x hx K hK) (.seq (unprepLoopWp x hx K hK) ?_))
  · exact SourceDerivTot.unitary_ofAssn _ _ _ _ _ _ (fun _ h => h)
      (fun _ _ => (Reg.single _).inj) (fun _ _ => le_rfl)
  · exact SourceDerivTot.unitary_ofAssn _ _ _ _ _ _ (fun _ h => h)
      (fun _ _ => (Reg.single _).inj) (fun _ _ => le_rfl)

theorem wpU5_op (σ : STc) :
    (wpU5 x hx K hK).op σ
      = LinearMap.adjoint (xLift x hx) ∘ₗ (predicatePost x K hK).op σ ∘ₗ xLift x hx :=
  Assn.unitaryPre_const_op (predicatePost x K hK) (Reg.single (aC x (a0 x hx)))
    (fun _ => singleGate (QubitCells (WL x)) (aC x (a0 x hx)) X) σ

theorem wpU4_op (σ : STc) :
    (wpU4 x hx K hK).op σ
      = LinearMap.adjoint (unprepChain x hx (coef σ)) ∘ₗ (wpU5 x hx K hK).op σ ∘ₗ
          unprepChain x hx (coef σ) := by
  refine (wpSuffix_zero_op_conj (unprepT x hx) (HubbardLCU.NT x - 1) (wpU5 x hx K hK)
    (unprepG x hx (coef σ)) σ (fun j _ A => unprepT_op x hx j A σ)).trans ?_
  rw [chainOp_unprepG x hx (coef σ)]

theorem wpU3_op (σ : STc) :
    (wpU3 x hx K hK).op σ
      = LinearMap.adjoint (selOp x (coef σ)) ∘ₗ (wpU4 x hx K hK).op σ ∘ₗ
          selOp x (coef σ) := by
  refine (wpSuffix_zero_op_conj (rungT x hx) (HubbardLCU.NT x) (wpU4 x hx K hK)
    (fun k => rungOp x (coef σ) (lCell x hx k)) σ
    (fun k _ A => rungT_op x hx k A σ)).trans ?_
  rw [chainOp_rungG x hx (coef σ)]

theorem wpU2_op (σ : STc) :
    (wpU2 x hx K hK).op σ
      = LinearMap.adjoint (prepChain x hx (coef σ)) ∘ₗ (wpU3 x hx K hK).op σ ∘ₗ
          prepChain x hx (coef σ) := by
  refine (wpSuffix_zero_op_conj (prepT x hx) (HubbardLCU.NT x - 1) (wpU3 x hx K hK)
    (prepG x hx (coef σ)) σ (fun j _ A => prepT_op x hx j A σ)).trans ?_
  rw [chainOp_prepG x hx (coef σ)]

/-- **The wp display**: the folded (Ax-Uni) precondition of the whole circuit
is the single conjugation `W† (∣0…0⟩⟨0…0∣_a ⊗ K) W` by the circuit operator
at the stored coefficients. -/
theorem wpLCU_op (σ : STc) :
    (wpLCU x hx K hK).op σ
      = LinearMap.adjoint (lcuOp x hx (coef σ)) ∘ₗ (predicatePost x K hK).op σ ∘ₗ
          lcuOp x hx (coef σ) := by
  have h1 : (wpLCU x hx K hK).op σ
      = LinearMap.adjoint (xLift x hx) ∘ₗ (wpU2 x hx K hK).op σ ∘ₗ xLift x hx :=
    Assn.unitaryPre_const_op (wpU2 x hx K hK) (Reg.single (aC x (a0 x hx)))
      (fun _ => singleGate (QubitCells (WL x)) (aC x (a0 x hx)) X) σ
  rw [h1, wpU2_op x hx K hK σ, wpU3_op x hx K hK σ, wpU4_op x hx K hK σ, wpU5_op x hx K hK σ,
    show lcuOp x hx (coef σ)
      = ((xLift x hx ∘ₗ unprepChain x hx (coef σ)) ∘ₗ selOp x (coef σ)) ∘ₗ
          (prepChain x hx (coef σ) ∘ₗ xLift x hx) from rfl]
  rw [LinearMap.adjoint_comp, LinearMap.adjoint_comp, LinearMap.adjoint_comp,
    LinearMap.adjoint_comp]
  simp only [LinearMap.comp_assoc]


/-- The physical system predicate λ⁻² H† K H. -/
noncomputable def predicateBlock (σ : ST) :
    EndM (QubitCells (SysL x)) (univ : Finset (SysL x)) :=
  (((lam x σ)⁻¹ ^ 2 : ℝ) : ℂ) •
    (LinearMap.adjoint (hubbardOp x σ.1 σ.2) ∘ₗ K ∘ₗ hubbardOp x σ.1 σ.2)

/-- Exact block-predicate identity, stronger than a Hoare lower bound. -/
theorem predicateBlock_eq_conj (σ : ST) (hlam : 0 < lam x σ) :
    LinearMap.adjoint (LinearMap.adjoint (sysEmb x) ∘ₗ lcuOp x hx σ ∘ₗ sysEmb x) ∘ₗ
      K ∘ₗ (LinearMap.adjoint (sysEmb x) ∘ₗ lcuOp x hx σ ∘ₗ sysEmb x)
      = predicateBlock x K σ := by
  rw [blockOp_eq x hx σ hlam, ← LinearMap.star_eq_adjoint, star_smul,
    LinearMap.star_eq_adjoint, LinearMap.smul_comp, LinearMap.comp_smul,
    LinearMap.comp_smul, smul_smul,
    show star ((((lam x σ)⁻¹ : ℝ) : ℂ)) * (((lam x σ)⁻¹ : ℝ) : ℂ)
        = (((lam x σ)⁻¹ ^ 2 : ℝ) : ℂ) from by
      rw [RCLike.star_def, Complex.conj_ofReal]
      push_cast
      ring]
  rfl

include hx hK in
/-- The generalized system predicate is an effect, including λ=0. -/
theorem isEffect_predicateBlock (σ : ST) : IsEffect (predicateBlock x K σ) := by
  rcases lt_or_ge 0 (lam x σ) with hlam | hlam
  · rw [← predicateBlock_eq_conj x hx K σ hlam]
    apply isEffect_conj hK
    rw [succBlock_eq_conj x hx σ hlam]
    exact (isEffect_succBlock x hx σ).2
  · have h0 : lam x σ = 0 := le_antisymm hlam (lam_nonneg x σ)
    have hz : predicateBlock x K σ = 0 := by
      rw [predicateBlock, h0]
      norm_num
    rw [hz]
    exact isEffect_zero

/-- Explicit classical/quantum precondition, independent of loop counters. -/
noncomputable def predicatePre : SourceAssertion STc (QubitCells (WL x)) :=
  SourceAssertion.ofAssn
    ⟨fun σ => sysLift (L₂ := AncL x) (predicateBlock x K (coef σ)),
      fun σ => isEffect_sysLift (isEffect_predicateBlock x hx K hK (coef σ))⟩
    (fun σ => 0 < lam x (coef σ))

/-- Exact backward calculation, valid on all inputs, with no eigenstate premise. -/
theorem initWp_op (σ : STc) (hlam : 0 < lam x (coef σ)) :
    ((wpLCU x hx K hK).initPre fun _ => ancS x).op σ =
      sysLift (L₂ := AncL x) (predicateBlock x K (coef σ)) := by
  rw [show ((wpLCU x hx K hK).initPre fun _ => ancS x).op σ =
      sysLift (L₂ := AncL x) (LinearMap.adjoint (sysEmb x) ∘ₗ
        (wpLCU x hx K hK).op σ ∘ₗ sysEmb x) from
      initPre_ancCells_op (L₁ := SysL x) (L₂ := AncL x) (wpLCU x hx K hK) σ,
    wpLCU_op x hx K hK σ]
  apply congrArg
  rw [← predicateBlock_eq_conj x hx K (coef σ) hlam]
  change LinearMap.adjoint (sysEmb x) ∘ₗ
    (LinearMap.adjoint (lcuOp x hx (coef σ)) ∘ₗ
      (sysEmb x ∘ₗ K ∘ₗ LinearMap.adjoint (sysEmb x)) ∘ₗ lcuOp x hx (coef σ)) ∘ₗ
    sysEmb x = _
  simp only [LinearMap.adjoint_comp, LinearMap.adjoint_adjoint, LinearMap.comp_assoc]

/-- Arbitrary-predicate LCU triple, derived from the source rules. -/
theorem lcuPredicateDeriv :
    SourceDerivTot (predicatePre x hx K hK) (lcuInitProg x hx)
      (SourceAssertion.ofAssn (predicatePost x K hK) (fun _ => True)) := by
  refine .conseq ?_
    (.seq (.initProg (fun _ => ancS x)
      (SourceAssertion.ofAssn (wpLCU x hx K hK) (fun _ => True))) (lcuWp x hx K hK))
    (SourceAssertion.entails_refl _)
  apply SourceAssertion.entails_ofAssn _ _ _ _ (fun _ _ => trivial)
  intro σ hσ
  exact le_of_eq (initWp_op x hx K hK σ hσ).symm

/-- Soundness over every input density operator. -/
theorem lcuPredicateValid :
    validTot (predicatePre x hx K hK).toAssn (lcuInitProg x hx)
      (predicatePost x K hK) := by
  simpa only [SourceAssertion.toAssn_ofAssn_true] using
    (lcuPredicateDeriv x hx K hK).sound

/-- The K=I physical predicate is the original success observable. -/
theorem predicateBlock_one (σ : ST) : predicateBlock x 1 σ = succBlock x σ := by
  simp only [predicateBlock, succBlock, Module.End.one_eq_id, LinearMap.id_comp]

/-- The K=I postcondition is the original vacuum success effect. -/
theorem predicatePost_one : predicatePost x 1 isEffect_one = vacPost x := by
  apply Assn.ext
  funext σ
  simp only [predicatePost, vacPost, Module.End.one_eq_id, LinearMap.id_comp]
  rfl

/-- The K=I source precondition recovers the existing success specification. -/
theorem predicatePre_one : predicatePre x hx 1 isEffect_one =
    HubbardLCUSuccess.Source.successPre x hx := by
  unfold predicatePre HubbardLCUSuccess.Source.successPre
  apply congrArg (fun A => SourceAssertion.ofAssn A (fun σ => 0 < lam x (coef σ)))
  apply Assn.ext
  funext σ
  exact congrArg (sysLift (L₂ := AncL x)) (predicateBlock_one x (coef σ))

end Qhl.HubbardLCUPredicate

#print axioms Qhl.HubbardLCUPredicate.lcuPredicateDeriv
#print axioms Qhl.HubbardLCUPredicate.lcuPredicateValid
#print axioms Qhl.HubbardLCUPredicate.initWp_op
