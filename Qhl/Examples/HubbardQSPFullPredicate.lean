import Qhl.Examples.HubbardQSPBK
import Qhl.Logic.ExactExpectation

/-! Full-register complementary effects for the actual initialized BK-QSP program. -/
namespace Qhl.HubbardQSPFullPredicate
open Qhl Qhl.HubbardLCU Qhl.HubbardQSP Qhl.HubbardQSPSuccess
open Qhl.BravyiKitaev Qhl.HubbardLCUSuccess Finset
open scoped ComplexInnerProductSpace ComplexOrder
variable (x : ℕ) (hx : 0 < x) (d : ℕ)
variable (M : EndM (QubitCells (WL x)) (univ : Finset (WL x))) (hM : IsEffect M)
noncomputable def post : Assn (STQc d) (QubitCells (WL x)) := ⟨fun _ => M, fun _ => hM⟩
include d hM in
theorem complementEffect : IsEffect (1 - M) :=
  (post x d M hM).compl.isEffect ((0, 0, 0, 0), (fun _ => 0), 0)

noncomputable def invariant : Assn (STQc d) (QubitCells (WL x)) where
  op σ := LinearMap.adjoint (walkRem x hx d σ) ∘ₗ
    (post x d M hM).op σ ∘ₗ walkRem x hx d σ
  isEffect σ := isEffect_conj ((post x d M hM).isEffect σ)
    (le_of_eq (isUnitary_walkN x hx (coefQ d σ) (phiSeq d (phis d σ)) _ _).1)

theorem invariant_op (σ : STQc d) : (invariant x hx d M hM).op σ =
    LinearMap.adjoint (walkRem x hx d σ) ∘ₗ
      M ∘ₗ walkRem x hx d σ := rfl

noncomputable def pre : Assn (STQc d) (QubitCells (WL x)) :=
  ((invariant x hx d M hM).comp fun σ : STQc d => (σ.1, σ.2.1, 0)).initPre
    (fun _ => ancS x)

/-- Source-rule preservation of the arbitrary-effect backward invariant. -/
theorem bodyInvariant : SourceDerivTot
    (SourceAssertion.ofAssn (invariant x hx d M hM) (fun σ => True ∧ gdQ d σ = true))
    (bodyProg x hx d) (SourceAssertion.ofAssn (invariant x hx d M hM) (fun _ => True)) := by
  refine .conseq ?_ (HubbardQSPSuccess.Source.bodyWp x hx d (invariant x hx d M hM)
    (fun _ _ => rfl) (fun _ _ => rfl)) (SourceAssertion.entails_refl _)
  apply SourceAssertion.entails_ofAssn _ _ _ _ (fun _ _ => trivial)
  intro σ hσ
  have hlt : cnt d σ < d := by simpa [gdQ] using hσ.2
  apply le_of_eq
  rw [wpBody_op, invariant_op, invariant_op, walkRem_split x hx d σ hlt,
    adjoint_comp_conj]

theorem loop : SourceDerivTot
    (SourceAssertion.ofAssn (invariant x hx d M hM) (fun _ => True))
    (.while (gdQ d) (bodyProg x hx d))
    (SourceAssertion.ofAssn (invariant x hx d M hM) (fun σ => True ∧ gdQ d σ = false)) := by
  exact .whileLoop (gdQ d) (fun σ => (rank d σ : Int))
    (fun _ _ => Int.natCast_nonneg _) (bodyInvariant x hx d M hM)
    (HubbardQSP.Source.bodyIdentityRank x hx d)

theorem circuit : SourceDerivTot
    (SourceAssertion.ofAssn ((invariant x hx d M hM).comp
      fun σ : STQc d => (σ.1, σ.2.1, 0)) (fun _ => True))
    (qspProg x hx d) (SourceAssertion.ofAssn (post x d M hM) (fun _ => True)) := by
  refine .conseq (SourceAssertion.entails_refl _)
    (.seq (.assign _ (SourceAssertion.ofAssn (invariant x hx d M hM) (fun _ => True)))
      (loop x hx d M hM)) ?_
  apply SourceAssertion.entails_ofAssn _ _ _ _ (fun _ _ => trivial)
  intro σ hσ
  have hge : d ≤ cnt d σ := by simpa [gdQ] using hσ.2
  have hw : walkRem x hx d σ = 1 := by
    unfold walkRem
    rw [Nat.sub_eq_zero_of_le hge]
    rfl
  change LinearMap.adjoint (walkRem x hx d σ) ∘ₗ _ ∘ₗ walkRem x hx d σ ≤ _
  rw [hw, LinearMap.adjoint_one, Module.End.one_eq_id, LinearMap.id_comp, LinearMap.comp_id]


theorem invariant_compl :
    invariant x hx d (1 - M) (complementEffect x d M hM) =
      (invariant x hx d M hM).compl := by
  apply Assn.ext
  funext σ
  rw [invariant_op, Assn.compl_op, invariant_op]
  rw [LinearMap.sub_comp, LinearMap.comp_sub, Module.End.one_eq_id,
    LinearMap.id_comp]
  have hu := (isUnitary_walkN x hx (coefQ d σ) (phiSeq d (phis d σ))
    (d - cnt d σ) (cnt d σ)).1
  change _ = 1 - _
  rw [show LinearMap.adjoint (walkRem x hx d σ) ∘ₗ walkRem x hx d σ = 1 from hu]

/-- The initialized QSP circuit at a full-register effect. -/
theorem deriv : SourceDerivTot
    (SourceAssertion.ofAssn (pre x hx d M hM) (fun _ => True)) (qspInitProg x hx d)
    (SourceAssertion.ofAssn (post x d M hM) (fun _ => True)) := by
  exact .seq (.initProg (fun _ => ancS x)
    (SourceAssertion.ofAssn ((invariant x hx d M hM).comp
      fun σ : STQc d => (σ.1, σ.2.1, 0)) (fun _ => True))) (circuit x hx d M hM)

theorem exact_expectation (s : CQState (STQc d) (QubitCells (WL x))) :
    PostH (Config.init (qspInitProg x hx d) s) (post x d M hM).op =
      expectE (pre x hx d M hM).op s := by
  have hp : pre x hx d (1 - M) (complementEffect x d M hM) =
      (pre x hx d M hM).compl := by
    unfold pre
    rw [invariant_compl x hx d M hM]
    have hc : (invariant x hx d M hM).compl.comp
        (fun σ : STQc d => (σ.1, σ.2.1, 0)) =
        ((invariant x hx d M hM).comp fun σ : STQc d => (σ.1, σ.2.1, 0)).compl := by
      apply Assn.ext
      funext σ
      rfl
    rw [hc, Assn.initPre_compl]
  apply PostH_eq_of_complement
  · simpa only [SourceAssertion.toAssn_ofAssn_true] using (deriv x hx d M hM).sound
  · have h := (deriv x hx d (1 - M) (complementEffect x d M hM)).sound
    simp only [SourceAssertion.toAssn_ofAssn_true] at h
    rw [hp] at h
    exact h

noncomputable def entry : Assn (STQc d) (QubitCells (WL x)) :=
  (invariant x hx d M hM).comp fun σ : STQc d => (σ.1, σ.2.1, 0)
noncomputable def bkPre : Assn (STQc d) (QubitCells (WL x)) :=
  (BKTransformWp.pre x Function.Embedding.inl (entry x hx d M hM)).initPre
    (fun _ => ancS x)

theorem prefix_compl (Y : Assn (STQc d) (QubitCells (WL x))) :
    BKTransformWp.pre x Function.Embedding.inl Y.compl =
      (BKTransformWp.pre x Function.Embedding.inl Y).compl := by
  apply Assn.ext
  funext σ
  simp only [HubbardQSPBK.prefixPre_op, Assn.compl_op]
  rw [LinearMap.sub_comp, LinearMap.comp_sub,
    Module.End.one_eq_id, LinearMap.id_comp]
  rw [adjoint_sysLift, ← sysLift_comp, (BKTransform.bkUnitary x).isUnitary.1,
    sysLift_one]
  rfl

theorem bkPre_compl :
    bkPre x hx d (1 - M) (complementEffect x d M hM) = (bkPre x hx d M hM).compl := by
  have he : entry x hx d (1 - M) (complementEffect x d M hM) =
      (entry x hx d M hM).compl := by
    unfold entry
    rw [invariant_compl x hx d M hM]
    rfl
  unfold bkPre
  rw [he, prefix_compl, Assn.initPre_compl]

theorem bkDeriv : SourceDerivTot
    (SourceAssertion.ofAssn (bkPre x hx d M hM) (fun _ => True))
    (HubbardQSPBK.qspBKProg x hx d)
    (SourceAssertion.ofAssn (post x d M hM) (fun _ => True)) := by
  exact .seq (.initProg (fun _ => ancS x)
    (SourceAssertion.ofAssn (BKTransformWp.pre x Function.Embedding.inl
      (entry x hx d M hM)) (fun _ => True)))
    (.seq (HubbardQSPBK.prefixDeriv x d (entry x hx d M hM)
      (fun _ _ => rfl) (fun _ _ => rfl)) (circuit x hx d M hM))

/-- Equality for every full-register effect on the actual initialized BK-QSP program. -/
theorem bk_exact_expectation (s : CQState (STQc d) (QubitCells (WL x))) :
    PostH (Config.init (HubbardQSPBK.qspBKProg x hx d) s) (post x d M hM).op =
      expectE (bkPre x hx d M hM).op s := by
  apply PostH_eq_of_complement
  · simpa only [SourceAssertion.toAssn_ofAssn_true] using (bkDeriv x hx d M hM).sound
  · have h := (bkDeriv x hx d (1 - M) (complementEffect x d M hM)).sound
    simp only [SourceAssertion.toAssn_ofAssn_true] at h
    rw [bkPre_compl x hx d M hM] at h
    exact h

end Qhl.HubbardQSPFullPredicate

#print axioms Qhl.HubbardQSPFullPredicate.deriv
#print axioms Qhl.HubbardQSPFullPredicate.bkDeriv
#print axioms Qhl.HubbardQSPFullPredicate.bk_exact_expectation
