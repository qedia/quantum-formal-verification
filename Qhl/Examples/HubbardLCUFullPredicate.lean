import Qhl.Examples.HubbardLCUPredicate
import Qhl.Logic.ExactExpectation

/-! The existing LCU counted source proof at any constant full-register effect. -/
namespace Qhl.HubbardLCUFullPredicate
open Qhl Qhl.HubbardLCU Qhl.HubbardQSP Qhl.HubbardLCUSuccess Qhl.BravyiKitaev Finset
open scoped ComplexInnerProductSpace ComplexOrder
variable (x : ℕ) (hx : 0 < x)
variable (M : EndM (QubitCells (WL x)) (univ : Finset (WL x))) (hM : IsEffect M)
noncomputable def post : Assn STc (QubitCells (WL x)) := ⟨fun _ => M, fun _ => hM⟩

noncomputable def wpU5 : Assn STc (QubitCells (WL x)) :=
  (post x M hM).unitaryPre (RegExpr.const (Reg.single (aC x (a0 x hx))))
    (fun _ => singleGate (QubitCells (WL x)) (aC x (a0 x hx)) X)

/-- wp of the counted inverse-Givens loop of UNPREPARE: the suffix family of
the `unprepT` passes at entry. -/
noncomputable def wpU4 : Assn STc (QubitCells (WL x)) :=
  wpSuffix (unprepT x hx) (HubbardLCU.NT x - 1) (wpU5 x hx M hM) 0

/-- wp of SELECT: the suffix family of the `rungT` passes at entry. -/
noncomputable def wpU3 : Assn STc (QubitCells (WL x)) :=
  wpSuffix (rungT x hx) (HubbardLCU.NT x) (wpU4 x hx M hM) 0

/-- wp of the counted Givens loop of PREPARE. -/
noncomputable def wpU2 : Assn STc (QubitCells (WL x)) :=
  wpSuffix (prepT x hx) (HubbardLCU.NT x - 1) (wpU3 x hx M hM) 0

/-- **The folded (Ax-Uni) precondition of the whole LCU circuit.** -/
noncomputable def wpLCU : Assn STc (QubitCells (WL x)) :=
  (wpU2 x hx M hM).unitaryPre (RegExpr.const (Reg.single (aC x (a0 x hx))))
    (fun _ => singleGate (QubitCells (WL x)) (aC x (a0 x hx)) X)

theorem wpU4_op_set (c : CounterLens STc) (hc : ∀ σ v, coef (c.set σ v) = coef σ)
    (σ : STc) (v : ℕ) : (wpU4 x hx M hM).op (c.set σ v) = (wpU4 x hx M hM).op σ :=
  wpSuffix_op_set (unprepT x hx) (wpU5 x hx M hM) c
    (fun k A hA σ' v' => unprepT_op_set x hx c hc k A hA σ' v')
    (fun _ _ => rfl) 0 σ v

theorem wpU3_op_set (c : CounterLens STc) (hc : ∀ σ v, coef (c.set σ v) = coef σ)
    (σ : STc) (v : ℕ) : (wpU3 x hx M hM).op (c.set σ v) = (wpU3 x hx M hM).op σ :=
  wpSuffix_op_set (rungT x hx) (wpU4 x hx M hM) c
    (fun k A hA σ' v' => rungT_op_set x hx c hc k A hA σ' v')
    (fun σ' v' => wpU4_op_set x hx M hM c hc σ' v') 0 σ v

theorem prepLoopWp :
    SourceDerivTot (SourceAssertion.ofAssn (wpU2 x hx M hM) (fun _ => True))
      (countedProg (CounterLens.fst3 ST) (fun _ => HubbardLCU.NT x - 1) (prepBody x hx))
      (SourceAssertion.ofAssn (wpU3 x hx M hM) (fun _ => True)) := by
  refine .conseq (SourceAssertion.entails_refl _)
    (SourceDerivTot.countedWpChain (CounterLens.fst3 ST) (HubbardLCU.NT x - 1)
      (fun _ => True) (prepRegE x hx) (prepGateE x hx) (prepT x hx) (wpU3 x hx M hM)
      (fun _ _ => Iff.rfl)
      (fun k A hA σ v => prepT_op_set x hx (CounterLens.fst3 ST)
        (fun _ _ => rfl) k A hA σ v)
      (fun σ v => wpU3_op_set x hx M hM (CounterLens.fst3 ST) (fun _ _ => rfl) σ v)
      (fun _ _ _ => (prepReg x _).inj)
      (fun k _ σ _ hget A => by subst hget; rfl)) ?_
  exact SourceAssertion.entails_ofAssn _ _ _ _ (fun _ _ => trivial) (fun _ _ => le_rfl)

/-- UNPREPARE's weakest-precondition loop derived from source rules. -/
theorem unprepLoopWp :
    SourceDerivTot (SourceAssertion.ofAssn (wpU4 x hx M hM) (fun _ => True))
      (countedProg (CounterLens.fst3 ST) (fun _ => HubbardLCU.NT x - 1) (unprepBody x hx))
      (SourceAssertion.ofAssn (wpU5 x hx M hM) (fun _ => True)) := by
  refine .conseq (SourceAssertion.entails_refl _)
    (SourceDerivTot.countedWpChain (CounterLens.fst3 ST) (HubbardLCU.NT x - 1)
      (fun _ => True) (unprepRegE x hx) (unprepGateE x hx) (unprepT x hx) (wpU5 x hx M hM)
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
        (wpSuffix (rungT x hx) (HubbardLCU.NT x) (wpU4 x hx M hM)))
        (fun σ => True ∧ σ.1 < HubbardLCU.NT x))
      (rungBody x hx)
      (SourceAssertion.ofAssn (Assn.ofFam (CounterLens.fst3 ST).get
        (fun k => wpSuffix (rungT x hx) (HubbardLCU.NT x) (wpU4 x hx M hM) (k + 1)))
        (fun σ => True ∧ σ.1 < HubbardLCU.NT x)) := by
  let J : ℕ → Assn STc (QubitCells (WL x)) := fun m =>
    Assn.ofFam (CounterLens.fst3 ST).get fun k =>
      wpSuffix (letterT x hx k) (2 ^ x)
        (wpSuffix (rungT x hx) (HubbardLCU.NT x) (wpU4 x hx M hM) (k + 1)) m
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
        (wpSuffix (rungT x hx) (HubbardLCU.NT x) (wpU4 x hx M hM) (σ.1 + 1)) m).op
          ((CounterLens.snd3 ST).set σ v) = _
      apply wpSuffix_op_set (letterT x hx σ.1) _ (CounterLens.snd3 ST)
        (fun k A hA σ' v' => letterT_op_set x hx (CounterLens.snd3 ST) σ.1 k A hA σ' v')
      intro σ' v'
      exact wpSuffix_op_set (rungT x hx) (wpU4 x hx M hM) (CounterLens.snd3 ST)
        (fun k A hA τ w => rungT_op_set x hx (CounterLens.snd3 ST)
          (fun _ _ => rfl) k A hA τ w)
        (fun τ w => wpU4_op_set x hx M hM (CounterLens.snd3 ST) (fun _ _ => rfl) τ w)
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
    SourceDerivTot (SourceAssertion.ofAssn (wpU3 x hx M hM) (fun _ => True))
      (selProg x hx) (SourceAssertion.ofAssn (wpU4 x hx M hM) (fun _ => True)) := by
  refine .conseq (SourceAssertion.entails_refl _)
    (SourceDerivTot.countedWpBody (CounterLens.fst3 ST) (HubbardLCU.NT x)
      (fun _ => True) (rungT x hx) (wpU4 x hx M hM) (rungBody x hx)
      (fun _ _ => Iff.rfl)
      (fun k A hA σ v => rungT_op_set x hx (CounterLens.fst3 ST)
        (fun _ _ => rfl) k A hA σ v)
      (fun σ v => wpU4_op_set x hx M hM (CounterLens.fst3 ST) (fun _ _ => rfl) σ v)
      (selectWpStep x hx M hM)
      (fun _ => HubbardLCU.Source.rungIdentity x hx _ (fun _ _ => Iff.rfl))) ?_
  exact SourceAssertion.entails_ofAssn _ _ _ _ (fun _ _ => trivial) (fun _ _ => le_rfl)

/-- The source weakest-precondition derivation for the literal entire LCU circuit. -/
theorem lcuWp :
    SourceDerivTot (SourceAssertion.ofAssn (wpLCU x hx M hM) (fun _ => True))
      (lcuProg x hx) (SourceAssertion.ofAssn (post x M hM) (fun _ => True)) := by
  refine .seq (.seq ?_ (prepLoopWp x hx M hM))
    (.seq (selectWp x hx M hM) (.seq (unprepLoopWp x hx M hM) ?_))
  · exact SourceDerivTot.unitary_ofAssn _ _ _ _ _ _ (fun _ h => h)
      (fun _ _ => (Reg.single _).inj) (fun _ _ => le_rfl)
  · exact SourceDerivTot.unitary_ofAssn _ _ _ _ _ _ (fun _ h => h)
      (fun _ _ => (Reg.single _).inj) (fun _ _ => le_rfl)

theorem wpU5_op (σ : STc) :
    (wpU5 x hx M hM).op σ
      = LinearMap.adjoint (xLift x hx) ∘ₗ (post x M hM).op σ ∘ₗ xLift x hx :=
  Assn.unitaryPre_const_op (post x M hM) (Reg.single (aC x (a0 x hx)))
    (fun _ => singleGate (QubitCells (WL x)) (aC x (a0 x hx)) X) σ

theorem wpU4_op (σ : STc) :
    (wpU4 x hx M hM).op σ
      = LinearMap.adjoint (unprepChain x hx (coef σ)) ∘ₗ (wpU5 x hx M hM).op σ ∘ₗ
          unprepChain x hx (coef σ) := by
  refine (wpSuffix_zero_op_conj (unprepT x hx) (HubbardLCU.NT x - 1) (wpU5 x hx M hM)
    (unprepG x hx (coef σ)) σ (fun j _ A => unprepT_op x hx j A σ)).trans ?_
  rw [chainOp_unprepG x hx (coef σ)]

theorem wpU3_op (σ : STc) :
    (wpU3 x hx M hM).op σ
      = LinearMap.adjoint (selOp x (coef σ)) ∘ₗ (wpU4 x hx M hM).op σ ∘ₗ
          selOp x (coef σ) := by
  refine (wpSuffix_zero_op_conj (rungT x hx) (HubbardLCU.NT x) (wpU4 x hx M hM)
    (fun k => rungOp x (coef σ) (lCell x hx k)) σ
    (fun k _ A => rungT_op x hx k A σ)).trans ?_
  rw [chainOp_rungG x hx (coef σ)]

theorem wpU2_op (σ : STc) :
    (wpU2 x hx M hM).op σ
      = LinearMap.adjoint (prepChain x hx (coef σ)) ∘ₗ (wpU3 x hx M hM).op σ ∘ₗ
          prepChain x hx (coef σ) := by
  refine (wpSuffix_zero_op_conj (prepT x hx) (HubbardLCU.NT x - 1) (wpU3 x hx M hM)
    (prepG x hx (coef σ)) σ (fun j _ A => prepT_op x hx j A σ)).trans ?_
  rw [chainOp_prepG x hx (coef σ)]

/-- **The wp display**: the folded (Ax-Uni) precondition of the whole circuit
is the single conjugation `W† M W` by the circuit operator
at the stored coefficients. -/
theorem wpLCU_op (σ : STc) :
    (wpLCU x hx M hM).op σ
      = LinearMap.adjoint (lcuOp x hx (coef σ)) ∘ₗ (post x M hM).op σ ∘ₗ
          lcuOp x hx (coef σ) := by
  have h1 : (wpLCU x hx M hM).op σ
      = LinearMap.adjoint (xLift x hx) ∘ₗ (wpU2 x hx M hM).op σ ∘ₗ xLift x hx :=
    Assn.unitaryPre_const_op (wpU2 x hx M hM) (Reg.single (aC x (a0 x hx)))
      (fun _ => singleGate (QubitCells (WL x)) (aC x (a0 x hx)) X) σ
  rw [h1, wpU2_op x hx M hM σ, wpU3_op x hx M hM σ, wpU4_op x hx M hM σ, wpU5_op x hx M hM σ,
    show lcuOp x hx (coef σ)
      = ((xLift x hx ∘ₗ unprepChain x hx (coef σ)) ∘ₗ selOp x (coef σ)) ∘ₗ
          (prepChain x hx (coef σ) ∘ₗ xLift x hx) from rfl]
  rw [LinearMap.adjoint_comp, LinearMap.adjoint_comp, LinearMap.adjoint_comp,
    LinearMap.adjoint_comp]
  simp only [LinearMap.comp_assoc]



include hM in
theorem complementEffect : IsEffect (1 - M) := (post x M hM).compl.isEffect (0, 0, 0, 0)

/-- Full-register complement propagated through the entire circuit. -/
theorem wpLCU_compl :
    wpLCU x hx (1 - M) (complementEffect x M hM) =
      (wpLCU x hx M hM).compl := by
  apply Assn.ext
  funext σ
  rw [wpLCU_op, Assn.compl_op, wpLCU_op]
  change LinearMap.adjoint (lcuOp x hx (coef σ)) ∘ₗ (1 - M) ∘ₗ lcuOp x hx (coef σ) = _
  rw [LinearMap.sub_comp, LinearMap.comp_sub, Module.End.one_eq_id,
    LinearMap.id_comp, (isUnitary_lcuOp x hx (coef σ)).1]
  rfl

noncomputable def pre : Assn STc (QubitCells (WL x)) :=
  (wpLCU x hx M hM).initPre (fun _ => ancS x)

theorem deriv : SourceDerivTot
    (SourceAssertion.ofAssn (pre x hx M hM) (fun _ => True)) (lcuInitProg x hx)
    (SourceAssertion.ofAssn (post x M hM) (fun _ => True)) :=
by
  exact .seq (.initProg (fun _ => ancS x)
    (SourceAssertion.ofAssn (wpLCU x hx M hM) (fun _ => True))) (lcuWp x hx M hM)

theorem exact_expectation (s : CQState STc (QubitCells (WL x))) :
    PostH (Config.init (lcuInitProg x hx) s) (post x M hM).op =
      expectE (pre x hx M hM).op s := by
  apply PostH_eq_of_complement
  · simpa only [SourceAssertion.toAssn_ofAssn_true] using (deriv x hx M hM).sound
  · have h := (deriv x hx (1 - M) (complementEffect x M hM)).sound
    simp only [SourceAssertion.toAssn_ofAssn_true, pre] at h
    rw [wpLCU_compl x hx M hM, Assn.initPre_compl] at h
    exact h

end Qhl.HubbardLCUFullPredicate

#print axioms Qhl.HubbardLCUFullPredicate.deriv
#print axioms Qhl.HubbardLCUFullPredicate.exact_expectation
