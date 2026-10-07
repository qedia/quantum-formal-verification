import Qhl.Logic.HeraldedRUS
import Qhl.Logic.Source.BasicDerived
import Qhl.Program.FrameParameters

/-! # Bounded RUS using derived selected-outcome measurement

The invariant and the identity ranking premise are separate source derivations.
The quantitative invariant selects only success on the final attempt: the omitted
failure branch has zero quantitative effect, not zero physical probability.
-/

namespace Qhl.HeraldedRUS

open Qhl TwoQubits Finset
open scoped ComplexInnerProductSpace ComplexOrder

/-- The measured Boolean cell, read as a two-element outcome type. -/
def outcomeVariable : SourceVariable Store (Fin 2) where
  get σ := finTwoEquiv.symm σ.1
  set := updM
  get_set i σ := finTwoEquiv.symm_apply_apply i
  set_get σ := by simp [updM]
  set_set i j σ := rfl

/-- Source backward chain for a selected measurement, followed by counter increment. -/
noncomputable def bodySelectedPre
    (W : UnitaryOp (EuclideanSpace ℂ (Bool × Bool)))
    (B : SourceAssertion Store D) (S : Store → Fin 2 → Bool) : SourceAssertion Store D :=
  (((B.subst incK).measureSelectedPreSource rA measA outcomeVariable.set S).unitaryPreSource
    rAT (gateW W)).initPreSource (fun _ => regA.sig)

/-- The source rules and derived selected measurement, with explicit operand domains. -/
theorem bodySelectedDeriv
    (W : UnitaryOp (EuclideanSpace ℂ (Bool × Bool)))
    (B : SourceAssertion Store D) (S : Store → Fin 2 → Bool)
    (hS : ∀ i σ, S (outcomeVariable.set i σ) = S σ)
    (hdom : ∀ σ,
      ((B.subst incK).measureSelectedPreSource rA measA outcomeVariable.set S).classical σ →
      (∀ i, S σ i = true → B.defined (incK (outcomeVariable.set i σ))) →
      ∀ i, B.defined (incK (outcomeVariable.set i σ))) :
    SourceDerivTot (bodySelectedPre W B S) (heraldBody W) B := by
  refine .seq (.initProg _ _) (.seq (.unitary _ _ _) (.seq ?_ (.assign incK B)))
  exact .conseq (SourceAssertion.entails_refl _)
    (.measureSelected rA measA outcomeVariable S (B.subst incK) hS hdom)
    ⟨fun _ h => h.1, fun _ _ => ⟨Iff.rfl, fun _ => le_rfl⟩⟩

/-- Selected and complete backward effects agree when every omitted operand is zero. -/
theorem bodySelectedPre_op
    (W : UnitaryOp (EuclideanSpace ℂ (Bool × Bool)))
    (B : Assn Store D) (ψ : Store → Prop) (S : Store → Fin 2 → Bool) (σ : Store)
    (hz : ∀ i, S σ i ≠ true → B.op (incK (updM i σ)) = 0) :
    (bodySelectedPre W (SourceAssertion.ofAssn B ψ) S).quantum.op σ =
      (bodyBackward W B).op σ := by
  classical
  have hm :
      ((SourceAssertion.ofAssn B ψ).subst incK |>.measureSelectedPreSource
        rA measA outcomeVariable.set S).quantum.op σ =
      ((B.comp incK).measurePre rA measA updM).op σ := by
    rw [Assn.measurePre_op_of_dist _ _ _ _ (distA σ)]
    dsimp only [SourceAssertion.measureSelectedPreSource]
    rw [dif_pos (distA σ)]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : S σ i = true
    · simp only [hi, if_true]
      rfl
    · rw [if_neg hi, Assn.comp_op, hz i hi]
  change (((((SourceAssertion.ofAssn B ψ).subst incK).measureSelectedPreSource
    rA measA outcomeVariable.set S).quantum.unitaryPre rAT (gateW W)).initPre
      (fun _ => regA.sig)).op σ = _
  simp only [bodyBackward, Assn.initPre_op,
    Assn.unitaryPre_op_of_dist _ _ _ (distAT σ), hm]

/-- A source body proof from classical selected-outcome implications and operator algebra. -/
theorem bodySource_ofAssn
    (W : UnitaryOp (EuclideanSpace ℂ (Bool × Bool)))
    (A B : Assn Store D) (φ ψ : Store → Prop) (S : Store → Fin 2 → Bool)
    (hS : ∀ i σ, S (outcomeVariable.set i σ) = S σ)
    (hc : ∀ σ, φ σ → ∀ i, S σ i = true → ψ (incK (updM i σ)))
    (hz : ∀ σ, φ σ → ∀ i, S σ i ≠ true → B.op (incK (updM i σ)) = 0)
    (hq : ∀ σ, φ σ → A.op σ ≤ (bodyBackward W B).op σ) :
    SourceDerivTot (SourceAssertion.ofAssn A φ) (heraldBody W)
      (SourceAssertion.ofAssn B ψ) := by
  refine .conseq ?_ (bodySelectedDeriv W (SourceAssertion.ofAssn B ψ) S hS (fun _ _ _ _ => trivial))
    (SourceAssertion.entails_refl _)
  refine ⟨hc, ?_⟩
  intro σ hφ
  refine ⟨⟨fun _ => ⟨distAT σ, distA σ, fun _ _ => trivial⟩,
    fun _ => trivial⟩, ?_⟩
  intro _
  rw [bodySelectedPre_op W B ψ S σ (hz σ hφ)]
  exact hq σ hφ

/-- The independent identity-predicate rank premise uses every measurement outcome. -/
theorem bodyIdentityRankSource
    (W : UnitaryOp (EuclideanSpace ℂ (Bool × Bool))) (N : ℕ)
    (φ : Store → Prop) (z : ℤ) :
    SourceDerivTot
      (SourceAssertion.identity (D := D)
        (fun σ => φ σ ∧ guard N σ = true ∧ (rank N σ : ℤ) = z))
      (heraldBody W)
      (SourceAssertion.identity (D := D) (fun σ => (rank N σ : ℤ) < z)) := by
  apply bodySource_ofAssn W Assn.one Assn.one _ _ (fun _ _ => true)
    (fun _ _ => rfl)
  · intro σ h i _
    have hk : σ.2 < N := by
      by_contra hn
      simp [guard, hn] at h
    change (↑(N - (σ.2 + 1)) : ℤ) < z
    have hr : (↑(N - σ.2) : ℤ) = z := h.2.2
    omega
  · intro σ _ i hi
    exact (hi rfl).elim
  · intro σ _
    rw [bodyBackward_one]

/-- The ordinary source invariant keeps a trivial classical condition. -/
noncomputable def sourceInvariant (V : UnitaryOp 𝕢) (ψ₀ : 𝕢) (hψ₀ : ‖ψ₀‖ = 1) :
    SourceAssertion Store D := SourceAssertion.ofAssn (Jher V ψ₀ hψ₀) (fun _ => True)

/-- Invariant preservation uses the all-outcomes instance of the source axiom. -/
theorem bodyInvariantSource
    (W : UnitaryOp (EuclideanSpace ℂ (Bool × Bool))) (V : UnitaryOp 𝕢)
    {a b : ℂ} {ψ₀ : 𝕢} (hψ₀ : ‖ψ₀‖ = 1) (hB : HeraldedBlock W V a b) (N : ℕ) :
    SourceDerivTot
      ((sourceInvariant V ψ₀ hψ₀).withClassical fun σ => True ∧ guard N σ = true)
      (heraldBody W) (sourceInvariant V ψ₀ hψ₀) := by
  apply bodySource_ofAssn W (Jher V ψ₀ hψ₀) (Jher V ψ₀ hψ₀)
    _ _ (fun _ _ => true) (fun _ _ => rfl)
  · intro σ _ i _
    trivial
  · intro σ _ i hi
    exact (hi rfl).elim
  · intro σ h
    have hk : σ.2 < N := by
      by_contra hn
      simp [guard, hn] at h
    have hp := premise W V hψ₀ hB N (rank N σ) σ
    rw [Assn.mask_op_of_pos (φ := fun τ => rank N τ = rank N σ) (σ := σ) rfl,
      Assn.mand_op_of_true h.2] at hp
    apply hp.trans (le_of_eq ?_)
    change (bodyBackward W ((Jher V ψ₀ hψ₀).mask _)).op σ = _
    apply bodyBackward_op_congr
    intro i
    apply Assn.mask_op_of_pos
    change N - (σ.2 + 1) < N - σ.2
    omega

/-- First RUS triple, now a genuine source-rule derivation. -/
theorem heraldedRusSourceDeriv
    (W : UnitaryOp (EuclideanSpace ℂ (Bool × Bool))) (V : UnitaryOp 𝕢)
    {a b : ℂ} {ψ₀ : 𝕢} (hψ₀ : ‖ψ₀‖ = 1) (hB : HeraldedBlock W V a b) (N : ℕ) :
    SourceDerivTot (SourceAssertion.ofAssn (heraldPre ψ₀ hψ₀) (fun _ => True))
      (heraldProg N W)
      ((sourceInvariant V ψ₀ hψ₀).withClassical
        (fun σ => True ∧ guard N σ = false)) := by
  have hl := SourceDerivTot.whileLoop (A := sourceInvariant V ψ₀ hψ₀)
    (guard N) (fun σ => (rank N σ : ℤ)) (fun _ _ => Int.natCast_nonneg _)
    (bodyInvariantSource W V hψ₀ hB N) (bodyIdentityRankSource W N (fun _ => True))
  refine .conseq ?_
    (.seq (.assign initM ((sourceInvariant V ψ₀ hψ₀).subst initK))
      (.seq (.assign initK _) hl)) (SourceAssertion.entails_refl _)
  exact SourceAssertion.entails_ofAssn _ _ _ _ (fun _ _ => trivial)
    (fun σ _ => pre_le V hψ₀ σ)

/-- Classical quantitative invariant: success, or another attempt remains. -/
def successClassical (N : ℕ) (σ : Store) : Prop := σ.1 = false ∨ σ.2 < N

/-- The selected outcomes before increment: success is always included. -/
def successSelector (N : ℕ) (σ : Store) (i : Fin 2) : Bool :=
  decide (σ.2 + 1 < N ∨ i = 0)

/-- Quantitative source invariant with the original effect family. -/
noncomputable def sourceInvariantQ (V : UnitaryOp 𝕢) (ψ₀ : 𝕢) (b : ℂ) (hb : ‖b‖ ≤ 1)
    (hψ₀ : ‖ψ₀‖ = 1) (N : ℕ) : SourceAssertion Store D :=
  SourceAssertion.ofAssn (Jq V ψ₀ b hb hψ₀ N) (successClassical N)

/-- The selector omits only an exhausted failure branch, whose effect is zero. -/
theorem successSelector_zero (V : UnitaryOp 𝕢) (ψ₀ : 𝕢) (b : ℂ)
    (hb : ‖b‖ ≤ 1) (hψ₀ : ‖ψ₀‖ = 1) (N : ℕ) (σ : Store) (i : Fin 2)
    (hi : successSelector N σ i ≠ true) :
    (Jq V ψ₀ b hb hψ₀ N).op (incK (updM i σ)) = 0 := by
  have hs : ¬ (σ.2 + 1 < N ∨ i = 0) := by simpa [successSelector] using hi
  have hi1 : i = 1 := by omega
  have hn : N - (σ.2 + 1) = 0 := by omega
  subst i
  rw [Jq_op, JqOp_true V (show (incK (updM 1 σ)).1 = true from rfl)]
  change (↑(succFloor b (N - (σ.2 + 1))) : ℂ) • _ = 0
  rw [hn, succFloor_zero, Complex.ofReal_zero, zero_smul]

/-- Quantitative preservation selects success alone at the final attempt. -/
theorem bodyInvariantSourceQ
    (W : UnitaryOp (EuclideanSpace ℂ (Bool × Bool))) (V : UnitaryOp 𝕢)
    {a b : ℂ} {ψ₀ : 𝕢} (hb : ‖b‖ ≤ 1) (hψ₀ : ‖ψ₀‖ = 1)
    (hB : HeraldedBlock W V a b) (N : ℕ) :
    SourceDerivTot
      ((sourceInvariantQ V ψ₀ b hb hψ₀ N).withClassical
        fun σ => successClassical N σ ∧ guard N σ = true)
      (heraldBody W) (sourceInvariantQ V ψ₀ b hb hψ₀ N) := by
  apply bodySource_ofAssn W (Jq V ψ₀ b hb hψ₀ N) (Jq V ψ₀ b hb hψ₀ N)
    _ _ (successSelector N) (fun _ _ => rfl)
  · intro σ _ i hi
    have hs : σ.2 + 1 < N ∨ i = 0 := by simpa [successSelector] using hi
    rcases hs with hk | rfl
    · exact Or.inr hk
    · exact Or.inl rfl
  · intro σ _ i hi
    exact successSelector_zero V ψ₀ b hb hψ₀ N σ i hi
  · intro σ h
    have hk : σ.2 < N := by
      by_contra hn
      simp [guard, hn] at h
    have hp := premiseQ W V hb hψ₀ hB N (rank N σ) σ
    rw [Assn.mask_op_of_pos (φ := fun τ => rank N τ = rank N σ) (σ := σ) rfl,
      Assn.mand_op_of_true h.2] at hp
    apply hp.trans (le_of_eq ?_)
    change (bodyBackward W ((Jq V ψ₀ b hb hψ₀ N).mask _)).op σ = _
    apply bodyBackward_op_congr
    intro i
    apply Assn.mask_op_of_pos
    change N - (σ.2 + 1) < N - σ.2
    omega

/-- The quantitative source postcondition explicitly asserts success. -/
noncomputable def sourceSuccessPost (V : UnitaryOp 𝕢) (ψ₀ : 𝕢) (hψ₀ : ‖ψ₀‖ = 1) :
    SourceAssertion Store D := SourceAssertion.ofAssn
      ⟨fun _ => outerLM (gv q0 ((V : 𝕢 →ₗ[ℂ] 𝕢) ψ₀))
          (gv q0 ((V : 𝕢 →ₗ[ℂ] 𝕢) ψ₀)),
        fun _ => isEffect_outerLM_self (norm_gv_w V hψ₀)⟩ (fun σ => σ.1 = false)

/-- Second RUS triple for a positive retry cap, using classical exit consequence. -/
theorem heraldedRusSuccessSourceDeriv
    (W : UnitaryOp (EuclideanSpace ℂ (Bool × Bool))) (V : UnitaryOp 𝕢)
    {a b : ℂ} {ψ₀ : 𝕢} (hb : ‖b‖ ≤ 1) (hψ₀ : ‖ψ₀‖ = 1)
    (hB : HeraldedBlock W V a b) (N : ℕ) (hN : 0 < N) :
    SourceDerivTot
      (SourceAssertion.ofAssn (heraldPreQ b hb N ψ₀ hψ₀) (fun _ => True))
      (heraldProg N W) (sourceSuccessPost V ψ₀ hψ₀) := by
  have hl := SourceDerivTot.whileLoop (A := sourceInvariantQ V ψ₀ b hb hψ₀ N)
    (guard N) (fun σ => (rank N σ : ℤ)) (fun _ _ => Int.natCast_nonneg _)
    (bodyInvariantSourceQ W V hb hψ₀ hB N)
    (bodyIdentityRankSource W N (successClassical N))
  refine .conseq ?_
    (.seq (.assign initM ((sourceInvariantQ V ψ₀ b hb hψ₀ N).subst initK))
      (.seq (.assign initK _) hl)) ?_
  · exact SourceAssertion.entails_ofAssn _ _ _ _
      (fun _ _ => Or.inr hN) (fun σ _ => preQ_le V hb hψ₀ N σ)
  · apply SourceAssertion.entails_ofAssn
    · intro σ h
      rcases h.1 with hm | hk
      · exact hm
      · cases hm : σ.1 with
        | false => rfl
        | true => simp [guard, hm, hk] at h
    · intro σ h
      have hm : σ.1 = false := by
        rcases h.1 with hm | hk
        · exact hm
        · cases hm : σ.1 with
          | false => rfl
          | true => simp [guard, hm, hk] at h
      exact le_of_eq (JqOp_false V hm)


/-! ## Read-only classical retry bound

The historical fixed-bound exports above remain available, including their zero
bound cases. Here the input bound is a cell of the store, and the rank is integer
subtraction; its nonnegativity follows from the explicit counter bound.
-/
namespace ClassicalInput

/-- `(N, m, k)`: retry bound, Boolean outcome, and natural counter. -/
abbrev Store := ℕ × HeraldedRUS.Store

def guard (σ : Store) : Bool := HeraldedRUS.guard σ.1 σ.2
def rank (σ : Store) : ℤ := (σ.1 : ℤ) - σ.2.2
def initM (σ : Store) : Store := (σ.1, HeraldedRUS.initM σ.2)
def initK (σ : Store) : Store := (σ.1, HeraldedRUS.initK σ.2)
def updM (i : Fin 2) (σ : Store) : Store := (σ.1, HeraldedRUS.updM i σ.2)
def incK (σ : Store) : Store := (σ.1, HeraldedRUS.incK σ.2)
abbrev rA : RegExpr Store L 1 := fun σ => HeraldedRUS.rA σ.2
abbrev rAT : RegExpr Store L 2 := fun σ => HeraldedRUS.rAT σ.2
noncomputable def measA := fun σ : Store => HeraldedRUS.measA σ.2
noncomputable def gateW (W : UnitaryOp (EuclideanSpace ℂ (Bool × Bool))) :=
  fun σ : Store => HeraldedRUS.gateW W σ.2

noncomputable def body (W : UnitaryOp (EuclideanSpace ℂ (Bool × Bool))) : Prog Store D :=
  .seq (.init fun _ => regA.sig) (.seq (.unitary 2 rAT (gateW W))
    (.seq (.measure 2 1 rA measA updM) (.assign incK)))

/-- The program reads N from its input store and never assigns to it. -/
noncomputable def prog (W : UnitaryOp (EuclideanSpace ℂ (Bool × Bool))) : Prog Store D :=
  .seq (.assign initM) (.seq (.assign initK) (.while guard (body W)))

theorem preserves_bound (W : UnitaryOp (EuclideanSpace ℂ (Bool × Bool))) :
    (prog W).PreservesParameters Prod.fst := by
  exact ⟨fun _ => rfl, fun _ => rfl, trivial, trivial, (fun _ _ => rfl), fun _ => rfl⟩

/-- Evaluate an existing effect family at the stored bound. -/
noncomputable def effect (A : ℕ → Assn HeraldedRUS.Store D) : Assn Store D where
  op σ := (A σ.1).op σ.2
  isEffect σ := (A σ.1).isEffect σ.2

def outcomeVariable : SourceVariable Store (Fin 2) where
  get σ := finTwoEquiv.symm σ.2.1
  set := updM
  get_set i σ := finTwoEquiv.symm_apply_apply i
  set_get σ := by simp [updM, HeraldedRUS.updM]
  set_set i j σ := rfl

noncomputable def selectedPre
    (W : UnitaryOp (EuclideanSpace ℂ (Bool × Bool)))
    (B : SourceAssertion Store D) (S : Store → Fin 2 → Bool) : SourceAssertion Store D :=
  (((B.subst incK).measureSelectedPreSource rA measA outcomeVariable.set S).unitaryPreSource
    rAT (gateW W)).initPreSource (fun _ => regA.sig)

/-- Source body proof on the enlarged store. All operands are defined; selected
measurement is derived from all-outcome measurement and Rule-Mask. Only the
pointwise backward operator from the fixed-bound development is reused. -/
theorem bodySource
    (W : UnitaryOp (EuclideanSpace ℂ (Bool × Bool)))
    (A B : ℕ → Assn HeraldedRUS.Store D) (φ ψ : Store → Prop)
    (S : Store → Fin 2 → Bool)
    (hS : ∀ i σ, S (updM i σ) = S σ)
    (hc : ∀ σ, φ σ → ∀ i, S σ i = true → ψ (incK (updM i σ)))
    (hz : ∀ σ, φ σ → ∀ i, S σ i ≠ true →
      (B σ.1).op (HeraldedRUS.incK (HeraldedRUS.updM i σ.2)) = 0)
    (hq : ∀ σ, φ σ → (A σ.1).op σ.2 ≤ (bodyBackward W (B σ.1)).op σ.2) :
    SourceDerivTot (SourceAssertion.ofAssn (effect A) φ) (body W)
      (SourceAssertion.ofAssn (effect B) ψ) := by
  have hd : SourceDerivTot (selectedPre W (SourceAssertion.ofAssn (effect B) ψ) S)
      (body W) (SourceAssertion.ofAssn (effect B) ψ) := by
    refine .seq (.initProg _ _) (.seq (.unitary _ _ _) (.seq ?_ (.assign incK _)))
    exact .conseq (SourceAssertion.entails_refl _)
      (.measureSelected rA measA outcomeVariable S _ hS (fun _ _ _ _ => trivial))
      ⟨fun _ h => h.1, fun _ _ => ⟨Iff.rfl, fun _ => le_rfl⟩⟩
  refine .conseq ?_ hd (SourceAssertion.entails_refl _)
  refine ⟨hc, ?_⟩
  intro σ hφ
  refine ⟨⟨fun _ => ⟨distAT σ.2, distA σ.2, fun _ _ => trivial⟩,
    fun _ => trivial⟩, ?_⟩
  intro _
  have hm :
      (((SourceAssertion.ofAssn (effect B) ψ).subst incK).measureSelectedPreSource
        rA measA outcomeVariable.set S).quantum.op σ =
      (((B σ.1).comp HeraldedRUS.incK).measurePre HeraldedRUS.rA
        HeraldedRUS.measA HeraldedRUS.updM).op σ.2 := by
    rw [Assn.measurePre_op_of_dist _ _ _ _ (distA σ.2)]
    dsimp only [SourceAssertion.measureSelectedPreSource]
    rw [dif_pos (distA σ.2)]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : S σ i = true
    · simp only [hi, if_true]
      rfl
    · rw [if_neg hi, Assn.comp_op, hz σ hφ i hi]
      rfl
  have he : (selectedPre W (SourceAssertion.ofAssn (effect B) ψ) S).quantum.op σ =
      (bodyBackward W (B σ.1)).op σ.2 := by
    change (((((SourceAssertion.ofAssn (effect B) ψ).subst incK).measureSelectedPreSource
      rA measA outcomeVariable.set S).quantum.unitaryPre rAT (gateW W)).initPre
        (fun _ => regA.sig)).op σ = _
    simp only [bodyBackward, Assn.initPre_op,
      Assn.unitaryPre_op_of_dist _ _ _ (show Function.Injective (rAT σ) from regAT.inj),
      Assn.unitaryPre_op_of_dist _ _ _ (distAT σ.2), hm]
    rfl
  rw [he]
  exact hq σ hφ

noncomputable def invariant (V : UnitaryOp 𝕢) (ψ₀ : 𝕢) (hψ₀ : ‖ψ₀‖ = 1) :=
  SourceAssertion.ofAssn (effect (fun _ => Jher V ψ₀ hψ₀))
    (fun σ => σ.2.2 ≤ σ.1)

noncomputable def invariantQ (V : UnitaryOp 𝕢) (ψ₀ : 𝕢) (b : ℂ) (hb : ‖b‖ ≤ 1)
    (hψ₀ : ‖ψ₀‖ = 1) :=
  SourceAssertion.ofAssn (effect (Jq V ψ₀ b hb hψ₀))
    (fun σ => σ.2.2 ≤ σ.1 ∧ successClassical σ.1 σ.2)

/-- Independent identity decrease includes all physical outcomes. -/
theorem identityRank (W : UnitaryOp (EuclideanSpace ℂ (Bool × Bool)))
    (φ : Store → Prop) (z : ℤ) :
    SourceDerivTot (SourceAssertion.identity (D := D)
      (fun σ => φ σ ∧ guard σ = true ∧ rank σ = z)) (body W)
      (SourceAssertion.identity (D := D) (fun σ => rank σ < z)) := by
  apply bodySource W (fun _ => Assn.one) (fun _ => Assn.one) _ _ (fun _ _ => true)
    (fun _ _ => rfl)
  · intro σ h i _
    change (σ.1 : ℤ) - ↑(σ.2.2 + 1) < z
    have hr : (σ.1 : ℤ) - σ.2.2 = z := h.2.2
    omega
  · intro σ _ i hi
    exact (hi rfl).elim
  · intro σ _
    rw [bodyBackward_one]


/-- Drop only the rank mask in an existing mathematical body premise. -/
theorem backward_unmask (W : UnitaryOp (EuclideanSpace ℂ (Bool × Bool)))
    (A : Assn HeraldedRUS.Store D) (N : ℕ) (σ : HeraldedRUS.Store)
    (hg : HeraldedRUS.guard N σ = true)
    (hp : ((A.mand (HeraldedRUS.guard N)).mask
      (fun τ => HeraldedRUS.rank N τ = HeraldedRUS.rank N σ)).op σ ≤
      (bodyBackward W (A.mask (fun τ => HeraldedRUS.rank N τ < HeraldedRUS.rank N σ))).op σ) :
    A.op σ ≤ (bodyBackward W A).op σ := by
  have hk : σ.2 < N := by
    by_contra hn
    simp [HeraldedRUS.guard, hn] at hg
  rw [Assn.mask_op_of_pos (φ := fun τ => HeraldedRUS.rank N τ = HeraldedRUS.rank N σ) rfl,
    Assn.mand_op_of_true hg] at hp
  apply hp.trans (le_of_eq ?_)
  apply bodyBackward_op_congr
  intro i
  apply Assn.mask_op_of_pos
  change N - (σ.2 + 1) < N - σ.2
  omega

theorem invariantBody (W : UnitaryOp (EuclideanSpace ℂ (Bool × Bool)))
    (V : UnitaryOp 𝕢) {a b : ℂ} {ψ₀ : 𝕢} (hψ₀ : ‖ψ₀‖ = 1)
    (hB : HeraldedBlock W V a b) :
    SourceDerivTot ((invariant V ψ₀ hψ₀).withClassical
      (fun σ => σ.2.2 ≤ σ.1 ∧ guard σ = true)) (body W) (invariant V ψ₀ hψ₀) := by
  apply bodySource W (fun _ => Jher V ψ₀ hψ₀) (fun _ => Jher V ψ₀ hψ₀)
    _ _ (fun _ _ => true) (fun _ _ => rfl)
  · intro σ h i _
    have hk : σ.2.2 < σ.1 := by
      by_contra hn
      simp [guard, HeraldedRUS.guard, hn] at h
    change σ.2.2 + 1 ≤ σ.1
    omega
  · intro σ _ i hi
    exact (hi rfl).elim
  · intro σ h
    exact backward_unmask W _ σ.1 σ.2 h.2
      (premise W V hψ₀ hB σ.1 (HeraldedRUS.rank σ.1 σ.2) σ.2)

theorem invariantBodyQ (W : UnitaryOp (EuclideanSpace ℂ (Bool × Bool)))
    (V : UnitaryOp 𝕢) {a b : ℂ} {ψ₀ : 𝕢} (hb : ‖b‖ ≤ 1) (hψ₀ : ‖ψ₀‖ = 1)
    (hB : HeraldedBlock W V a b) :
    SourceDerivTot ((invariantQ V ψ₀ b hb hψ₀).withClassical
      (fun σ => (σ.2.2 ≤ σ.1 ∧ successClassical σ.1 σ.2) ∧ guard σ = true))
      (body W) (invariantQ V ψ₀ b hb hψ₀) := by
  apply bodySource W (Jq V ψ₀ b hb hψ₀) (Jq V ψ₀ b hb hψ₀)
    _ _ (fun σ => successSelector σ.1 σ.2) (fun _ _ => rfl)
  · intro σ h i hi
    have hk : σ.2.2 < σ.1 := by
      by_contra hn
      simp [guard, HeraldedRUS.guard, hn] at h
    refine ⟨by change σ.2.2 + 1 ≤ σ.1; omega, ?_⟩
    have hs : σ.2.2 + 1 < σ.1 ∨ i = 0 := by simpa [successSelector] using hi
    rcases hs with hk | rfl
    · exact Or.inr hk
    · exact Or.inl rfl
  · intro σ _ i hi
    exact successSelector_zero V ψ₀ b hb hψ₀ σ.1 σ.2 i hi
  · intro σ h
    exact backward_unmask W _ σ.1 σ.2 h.2
      (premiseQ W V hb hψ₀ hB σ.1 (HeraldedRUS.rank σ.1 σ.2) σ.2)

noncomputable def pre (ψ₀ : 𝕢) (hψ₀ : ‖ψ₀‖ = 1) :=
  SourceAssertion.ofAssn (effect (fun _ => heraldPre ψ₀ hψ₀)) (fun σ => 1 ≤ σ.1)
noncomputable def post (V : UnitaryOp 𝕢) (ψ₀ : 𝕢) (hψ₀ : ‖ψ₀‖ = 1) :=
  SourceAssertion.ofAssn (effect (fun _ => Jher V ψ₀ hψ₀))
    (fun σ => σ.2.1 = false ∨ σ.1 ≤ σ.2.2)
noncomputable def preQ (b : ℂ) (hb : ‖b‖ ≤ 1) (ψ₀ : 𝕢) (hψ₀ : ‖ψ₀‖ = 1) :=
  SourceAssertion.ofAssn (effect (fun N => heraldPreQ b hb N ψ₀ hψ₀)) (fun σ => 1 ≤ σ.1)
noncomputable def postQ (V : UnitaryOp 𝕢) (ψ₀ : 𝕢) (hψ₀ : ‖ψ₀‖ = 1) :=
  SourceAssertion.ofAssn (effect (fun _ => (sourceSuccessPost V ψ₀ hψ₀).quantum))
    (fun σ => σ.2.1 = false)

/-- Positive stored-bound first triple, with an explicit classical exit disjunction. -/
theorem sourceDeriv (W : UnitaryOp (EuclideanSpace ℂ (Bool × Bool)))
    (V : UnitaryOp 𝕢) {a b : ℂ} {ψ₀ : 𝕢} (hψ₀ : ‖ψ₀‖ = 1)
    (hB : HeraldedBlock W V a b) :
    SourceDerivTot (pre ψ₀ hψ₀) (prog W) (post V ψ₀ hψ₀) := by
  have hl := SourceDerivTot.whileLoop (A := invariant V ψ₀ hψ₀) guard rank
    (fun σ h => by dsimp [rank]; exact sub_nonneg.mpr (Int.ofNat_le.mpr h))
    (invariantBody W V hψ₀ hB) (identityRank W _)
  refine .conseq ?_ (.seq (.assign initM ((invariant V ψ₀ hψ₀).subst initK))
    (.seq (.assign initK _) hl)) ?_
  · exact SourceAssertion.entails_ofAssn _ _ _ _ (fun σ _ => Nat.zero_le _)
      (fun σ _ => pre_le V hψ₀ σ.2)
  · apply SourceAssertion.entails_ofAssn
    · intro σ h
      by_cases hm : σ.2.1 = false
      · exact Or.inl hm
      · exact Or.inr (by
          by_contra hn
          have hk : σ.2.2 < σ.1 := by omega
          simp [guard, HeraldedRUS.guard, hk, Bool.eq_true_of_not_eq_false hm] at h)
    · intro σ _
      exact le_rfl

/-- Quantitative source derivation with stored-bound success coefficient. -/
theorem sourceDerivQ (W : UnitaryOp (EuclideanSpace ℂ (Bool × Bool)))
    (V : UnitaryOp 𝕢) {a b : ℂ} {ψ₀ : 𝕢} (hb : ‖b‖ ≤ 1) (hψ₀ : ‖ψ₀‖ = 1)
    (hB : HeraldedBlock W V a b) :
    SourceDerivTot (preQ b hb ψ₀ hψ₀) (prog W) (postQ V ψ₀ hψ₀) := by
  have hl := SourceDerivTot.whileLoop (A := invariantQ V ψ₀ b hb hψ₀) guard rank
    (fun σ h => by dsimp [rank]; exact sub_nonneg.mpr (Int.ofNat_le.mpr h.1))
    (invariantBodyQ W V hb hψ₀ hB) (identityRank W _)
  have hexit (σ : Store)
      (h : (σ.2.2 ≤ σ.1 ∧ successClassical σ.1 σ.2) ∧ guard σ = false) :
      σ.2.1 = false := by
    rcases h.1.2 with hm | hk
    · exact hm
    · by_contra hm
      simp [guard, HeraldedRUS.guard, hk, Bool.eq_true_of_not_eq_false hm] at h
  refine .conseq ?_ (.seq (.assign initM ((invariantQ V ψ₀ b hb hψ₀).subst initK))
    (.seq (.assign initK _) hl)) ?_
  · exact SourceAssertion.entails_ofAssn _ _ _ _
      (fun σ h => ⟨Nat.zero_le _, Or.inr h⟩) (fun σ _ => preQ_le V hb hψ₀ σ.1 σ.2)
  · apply SourceAssertion.entails_ofAssn
    · exact hexit
    · intro σ h
      exact le_of_eq (JqOp_false V (hexit σ h))


end ClassicalInput

end Qhl.HeraldedRUS
