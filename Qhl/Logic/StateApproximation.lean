import Qhl.Logic.Approximation

/-! # Approximation with preserved classical parameters

The scaling rule below is derived from the existing proof constructors. Its
syntactic preservation premise covers every assignment and measurement update;
quantum operations may still read the preserved parameter. -/

namespace Qhl
open Finset
open scoped ComplexOrder ComplexInnerProductSpace

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable {σT : Type*} [∀ i, Inhabited (D i)]

/-- Every classical update in a program preserves the given observation. -/
def Prog.Preserves {α : Type*} (P : Prog σT D) (f : σT → α) : Prop :=
  match P with
  | .skip | .init _ | .unitary _ _ _ => True
  | .assign g => ∀ σ, f (g σ) = f σ
  | .measure _ _ _ _ upd => ∀ i σ, f (upd i σ) = f σ
  | .seq P Q | .ite _ P Q => P.Preserves f ∧ Q.Preserves f
  | .while _ P => P.Preserves f

omit [Fintype L] [DecidableEq L] [∀ i, Inhabited (D i)] in
theorem Prog.Preserves.comp {α β : Type*} {P : Prog σT D} {f : σT → α}
    (h : P.Preserves f) (g : α → β) : P.Preserves (fun σ => g (f σ)) := by
  induction P with
  | skip | init | unitary => trivial
  | assign a => exact fun σ => congrArg g (h σ)
  | measure m k r M upd => exact fun i σ => congrArg g (h i σ)
  | seq P Q ihP ihQ | ite b P Q ihP ihQ => exact ⟨ihP h.1, ihQ h.2⟩
  | «while» b P ih => exact ih h

omit [Fintype L] [DecidableEq L] [∀ i, Inhabited (D i)] in
/-- A constant observation is preserved by every program. -/
theorem Prog.preserves_const {α : Type*} (P : Prog σT D) (a : α) :
    P.Preserves (fun _ => a) := by
  induction P with
  | skip | init | unitary => trivial
  | assign => exact fun _ => rfl
  | measure => exact fun _ _ => rfl
  | seq P Q ihP ihQ | ite b P Q ihP ihQ => exact ⟨ihP, ihQ⟩
  | «while» b P ih => exact ih

namespace Assn

/-- Scale an effect by a coefficient read from the classical store. -/
noncomputable def scaledBy (A : Assn σT D) (c : σT → ℝ)
    (h0 : ∀ σ, 0 ≤ c σ) (h1 : ∀ σ, c σ ≤ 1) : Assn σT D where
  op σ := (c σ : ℂ) • A.op σ
  isEffect σ := (A.scaled (c σ) (h0 σ) (h1 σ)).isEffect σ

omit [∀ i, Inhabited (D i)] in
@[simp] theorem scaledBy_op (A : Assn σT D) (c : σT → ℝ)
    (h0 : ∀ σ, 0 ≤ c σ) (h1 : ∀ σ, c σ ≤ 1) (σ : σT) :
    (A.scaledBy c h0 h1).op σ = (c σ : ℂ) • A.op σ := rfl

@[simp] theorem scaledBy_comp (A : Assn σT D) (c : σT → ℝ)
    (h0 : ∀ σ, 0 ≤ c σ) (h1 : ∀ σ, c σ ≤ 1)
    (f : σT → σT) (hf : ∀ σ, c (f σ) = c σ) :
    (A.comp f).scaledBy c h0 h1 = (A.scaledBy c h0 h1).comp f := by
  ext σ
  simp [scaledBy_op, hf]

@[simp] theorem scaledBy_mask (A : Assn σT D) (c : σT → ℝ)
    (h0 : ∀ σ, 0 ≤ c σ) (h1 : ∀ σ, c σ ≤ 1) (φ : σT → Prop) :
    (A.mask φ).scaledBy c h0 h1 = (A.scaledBy c h0 h1).mask φ := by
  ext σ
  by_cases h : φ σ <;> simp [scaledBy_op, h]

@[simp] theorem scaledBy_guard (A B : Assn σT D) (c : σT → ℝ)
    (h0 : ∀ σ, 0 ≤ c σ) (h1 : ∀ σ, c σ ≤ 1) (b : σT → Bool) :
    (guard b A B).scaledBy c h0 h1 =
      guard b (A.scaledBy c h0 h1) (B.scaledBy c h0 h1) := by
  ext σ
  cases hb : b σ <;> simp [scaledBy_op, hb]

omit [∀ i, Inhabited (D i)] in
theorem scaledBy_mono {A B : Assn σT D} (h : A ≤ B) (c : σT → ℝ)
    (h0 : ∀ σ, 0 ≤ c σ) (h1 : ∀ σ, c σ ≤ 1) :
    A.scaledBy c h0 h1 ≤ B.scaledBy c h0 h1 :=
  fun σ => real_smul_operator_mono (h σ) (h0 σ)

@[simp] theorem scaledBy_initPre (A : Assn σT D) (c : σT → ℝ)
    (h0 : ∀ σ, 0 ≤ c σ) (h1 : ∀ σ, c σ ≤ 1) (S : σT → Finset L) :
    (A.initPre S).scaledBy c h0 h1 = (A.scaledBy c h0 h1).initPre S := by
  ext σ
  simp [scaledBy_op]

@[simp] theorem scaledBy_unitaryPre (A : Assn σT D) (c : σT → ℝ)
    (h0 : ∀ σ, 0 ≤ c σ) (h1 : ∀ σ, c σ ≤ 1)
    {k : ℕ} (r : RegExpr σT L k) (U : ∀ σ, UnitaryOp (TSpace D (r σ))) :
    (A.unitaryPre r U).scaledBy c h0 h1 = (A.scaledBy c h0 h1).unitaryPre r U := by
  ext σ
  by_cases h : Function.Injective (r σ)
  · simp [scaledBy_op, unitaryPre_op_of_dist _ _ _ h, LinearMap.comp_smul,
      LinearMap.smul_comp]
  · simp [scaledBy_op, unitaryPre_op_of_not_dist _ _ _ h]

@[simp] theorem scaledBy_measurePre (A : Assn σT D) (c : σT → ℝ)
    (h0 : ∀ σ, 0 ≤ c σ) (h1 : ∀ σ, c σ ≤ 1)
    {m k : ℕ} (r : RegExpr σT L k) (M : ∀ σ, QMeasure m (TSpace D (r σ)))
    (upd : Fin m → σT → σT) (hp : ∀ i σ, c (upd i σ) = c σ) :
    (A.measurePre r M upd).scaledBy c h0 h1 =
      (A.scaledBy c h0 h1).measurePre r M upd := by
  ext σ
  by_cases h : Function.Injective (r σ)
  · simp [scaledBy_op, measurePre_op_of_dist _ _ _ _ h, hp, LinearMap.comp_smul,
      LinearMap.smul_comp, Finset.smul_sum]
  · simp [scaledBy_op, measurePre_op_of_not_dist _ _ _ _ h]

end Assn

/-- Preserved store-dependent scaling, derived using the existing rules.
The independent identity-rank premise of the source loop is retained. -/
theorem DerivTot.scaledBy {A B : Assn σT D} {P : Prog σT D}
    (h : DerivTot A P B) (c : σT → ℝ)
    (h0 : ∀ σ, 0 ≤ c σ) (h1 : ∀ σ, c σ ≤ 1) (hp : P.Preserves c) :
    DerivTot (A.scaledBy c h0 h1) P (B.scaledBy c h0 h1) := by
  induction h with
  | skip A => exact .skip _
  | assign f A => simpa only [Assn.scaledBy_comp A c h0 h1 f hp] using
      DerivTot.assign f (A.scaledBy c h0 h1)
  | initProg S A => simpa using DerivTot.initProg S (A.scaledBy c h0 h1)
  | unitary r U A => simpa using DerivTot.unitary r U (A.scaledBy c h0 h1)
  | measure r M upd A =>
      simpa only [Assn.scaledBy_measurePre A c h0 h1 r M upd hp] using
        DerivTot.measure r M upd (A.scaledBy c h0 h1)
  | seq _ _ ih₁ ih₂ => exact (ih₁ hp.1).seq (ih₂ hp.2)
  | cond _ _ ih₁ ih₀ => simpa using DerivTot.cond (ih₁ hp.1) (ih₀ hp.2)
  | whileLoop t _ ih =>
      simpa [Assn.mand, Assn.mandNot] using
        DerivTot.whileLoop t (fun n => by simpa [Assn.mand] using ih n hp)
  | whileLoopSource t hbound hInv hRank ihInv ihRank =>
      simpa [Assn.mand, Assn.mandNot] using
        DerivTot.whileLoopSource t hbound
          (by simpa [Assn.mand] using ihInv hp) hRank
  | conseq hpre _ hpost ih =>
      exact .conseq (Assn.scaledBy_mono hpre c h0 h1) (ih hp)
        (Assn.scaledBy_mono hpost c h0 h1)

/-- Approximate effect with a nonnegative tolerance read from the store. -/
noncomputable def Assn.approxBy (A : Assn σT D) (ε : σT → ℝ)
    (hε : ∀ σ, 0 ≤ ε σ) : Assn σT D where
  op σ := (((1 + ε σ)⁻¹ : ℝ) : ℂ) • A.op σ +
    ((ε σ / (1 + ε σ) : ℝ) : ℂ) • 1
  isEffect σ := isEffect_approx (A.isEffect σ) (hε σ)

omit [∀ i, Inhabited (D i)] in
@[simp] theorem Assn.approxBy_op (A : Assn σT D) (ε : σT → ℝ)
    (hε : ∀ σ, 0 ≤ ε σ) (σ : σT) :
    (A.approxBy ε hε).op σ = (((1 + ε σ)⁻¹ : ℝ) : ℂ) • A.op σ +
      ((ε σ / (1 + ε σ) : ℝ) : ℂ) • 1 := rfl

omit [∀ i, Inhabited (D i)] in
theorem Assn.approxBy_op_eq (A : Assn σT D) (ε : σT → ℝ)
    (hε : ∀ σ, 0 ≤ ε σ) (σ : σT) :
    (A.approxBy ε hε).op σ = (((1 + ε σ)⁻¹ : ℝ) : ℂ) •
      (A.op σ + (ε σ : ℂ) • 1) := by
  rw [approxBy_op, smul_add, smul_smul]
  congr 1
  congr 1
  push_cast
  ring

/-- Pointwise operator error gives a store-dependent approximation triple. -/
theorem DerivTot.approxBy_of_le {A B : Assn σT D} {P : Prog σT D}
    (h : DerivTot A P B) (C : Assn σT D) (ε : σT → ℝ)
    (hε : ∀ σ, 0 ≤ ε σ) (hp : P.Preserves ε)
    (hle : ∀ σ, B.op σ ≤ C.op σ + (ε σ : ℂ) • 1) :
    DerivTot (A.scaledBy (fun σ => (1 + ε σ)⁻¹)
      (fun σ => approxCoeff_nonneg (hε σ)) (fun σ => approxCoeff_le_one (hε σ)))
      P (C.approxBy ε hε) := by
  refine .conseq (fun _ => le_rfl)
    (h.scaledBy _ _ _ (hp.comp (fun e => (1 + e)⁻¹))) ?_
  intro σ
  rw [Assn.scaledBy_op, Assn.approxBy_op_eq]
  exact real_smul_operator_mono (hle σ) (approxCoeff_nonneg (hε σ))

/-- A genuine store predicate supplies the pointwise error-bound hypothesis. -/
theorem DerivTot.approxBy_mask_of_le {A B : Assn σT D} {P : Prog σT D}
    {φ : σT → Prop} (h : DerivTot A P (B.mask φ)) (C : Assn σT D)
    (ε : σT → ℝ) (hε : ∀ σ, 0 ≤ ε σ) (hp : P.Preserves ε)
    (hle : ∀ σ, φ σ → B.op σ ≤ C.op σ + (ε σ : ℂ) • 1) :
    DerivTot (A.scaledBy (fun σ => (1 + ε σ)⁻¹)
      (fun σ => approxCoeff_nonneg (hε σ)) (fun σ => approxCoeff_le_one (hε σ)))
      P (C.approxBy ε hε) := by
  apply h.approxBy_of_le C ε hε hp
  intro σ
  by_cases hφ : φ σ
  · rw [Assn.mask_op_of_pos hφ]
    exact hle σ hφ
  · rw [Assn.mask_op_of_neg hφ]
    have he := real_smul_operator_mono
      (show (0 : EndM D (univ : Finset L)) ≤ 1 from isEffect_one.1) (hε σ)
    simpa using add_le_add (C.isEffect σ).1 he

/-- Transfer a store-indexed exact output to a pointwise nearby target. -/
theorem DerivTot.approxBy_stateFam {A : Assn σT D} {P : Prog σT D}
    {u v : σT → HS D (univ : Finset L)}
    {hu : ∀ σ, ‖u σ‖ = 1} {hv : ∀ σ, ‖v σ‖ = 1} {φ : σT → Prop}
    (h : DerivTot A P ((Assn.ofStateFam u hu).mask φ))
    (ε : σT → ℝ) (hε : ∀ σ, 0 ≤ ε σ) (hp : P.Preserves ε)
    (hdist : ∀ σ, φ σ → ‖u σ - v σ‖ ≤ ε σ) :
    DerivTot (A.scaledBy (fun σ => (1 + ε σ)⁻¹)
      (fun σ => approxCoeff_nonneg (hε σ)) (fun σ => approxCoeff_le_one (hε σ)))
      P ((Assn.ofStateFam v hv).approxBy ε hε) := by
  apply h.approxBy_mask_of_le (Assn.ofStateFam v hv) ε hε hp
  intro σ hφ
  exact outerLM_self_le_add_of_norm_sub_le (u σ) (v σ) (hu σ) (hv σ) (hε σ) (hdist σ hφ)

end Qhl
