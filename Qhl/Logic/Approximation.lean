import Qhl.Logic.InitBlock
import Qhl.HSpace.ProjectorDistance

/-! # Effect-valued approximation of verified quantum programs

Scaling is derived by induction on the encoded proof rules. Approximate
postconditions remain effects, so the resulting triples retain validity for
all input density operators through the existing soundness theorem.
-/

namespace Qhl
open Finset
open scoped ComplexOrder ComplexInnerProductSpace

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable {σT : Type*}
variable [∀ i, Inhabited (D i)]

namespace Assn

@[simp] theorem scaled_comp (A : Assn σT D) (c : ℝ) (h0 : 0 ≤ c) (h1 : c ≤ 1)
    (f : σT → σT) : (A.comp f).scaled c h0 h1 = (A.scaled c h0 h1).comp f := by
  ext σ
  rfl

@[simp] theorem scaled_mask (A : Assn σT D) (c : ℝ) (h0 : 0 ≤ c) (h1 : c ≤ 1)
    (φ : σT → Prop) : (A.mask φ).scaled c h0 h1 = (A.scaled c h0 h1).mask φ := by
  ext σ
  by_cases h : φ σ <;> simp [scaled_op, h]

@[simp] theorem scaled_guard (A B : Assn σT D) (c : ℝ) (h0 : 0 ≤ c) (h1 : c ≤ 1)
    (b : σT → Bool) : (guard b A B).scaled c h0 h1 =
      guard b (A.scaled c h0 h1) (B.scaled c h0 h1) := by
  ext σ
  cases hb : b σ <;> simp [scaled_op, hb]

omit [∀ i, Inhabited (D i)] in
theorem scaled_mono {A B : Assn σT D} (h : A ≤ B) (c : ℝ)
    (h0 : 0 ≤ c) (h1 : c ≤ 1) : A.scaled c h0 h1 ≤ B.scaled c h0 h1 := by
  intro σ
  rw [scaled_op, scaled_op, le_iff_inner_le]
  intro v
  simp only [LinearMap.smul_apply, inner_smul_right]
  exact mul_le_mul_of_nonneg_left ((le_iff_inner_le _ _).mp (h σ) v)
    (Complex.zero_le_real.mpr h0)



@[simp] theorem scaled_initPre (A : Assn σT D) (c : ℝ) (h0 : 0 ≤ c) (h1 : c ≤ 1)
    (S : σT → Finset L) : (A.initPre S).scaled c h0 h1 =
      (A.scaled c h0 h1).initPre S := by
  ext σ
  simp [scaled_op]

@[simp] theorem scaled_unitaryPre (A : Assn σT D) (c : ℝ) (h0 : 0 ≤ c) (h1 : c ≤ 1)
    {k : ℕ} (r : RegExpr σT L k) (U : ∀ σ, UnitaryOp (TSpace D (r σ))) :
    (A.unitaryPre r U).scaled c h0 h1 = (A.scaled c h0 h1).unitaryPre r U := by
  ext σ
  by_cases h : Function.Injective (r σ)
  · simp [scaled_op, unitaryPre_op_of_dist _ _ _ h, LinearMap.comp_smul,
      LinearMap.smul_comp]
  · simp [scaled_op, unitaryPre_op_of_not_dist _ _ _ h]

@[simp] theorem scaled_measurePre (A : Assn σT D) (c : ℝ) (h0 : 0 ≤ c) (h1 : c ≤ 1)
    {m k : ℕ} (r : RegExpr σT L k) (M : ∀ σ, QMeasure m (TSpace D (r σ)))
    (upd : Fin m → σT → σT) : (A.measurePre r M upd).scaled c h0 h1 =
      (A.scaled c h0 h1).measurePre r M upd := by
  ext σ
  by_cases h : Function.Injective (r σ)
  · simp [scaled_op, measurePre_op_of_dist _ _ _ _ h, LinearMap.comp_smul,
      LinearMap.smul_comp, Finset.smul_sum]
  · simp [scaled_op, measurePre_op_of_not_dist _ _ _ _ h]

end Assn



/-- Multiplying both assertions by the same constant in `[0,1]` preserves
constructor derivability, including genuine loops. -/
theorem DerivTot.scaled {A B : Assn σT D} {P : Prog σT D}
    (h : DerivTot A P B) (c : ℝ) (h0 : 0 ≤ c) (h1 : c ≤ 1) :
    DerivTot (A.scaled c h0 h1) P (B.scaled c h0 h1) := by
  induction h with
  | skip A => exact .skip _
  | assign f A => simpa using DerivTot.assign f (A.scaled c h0 h1)
  | initProg S A => simpa using DerivTot.initProg S (A.scaled c h0 h1)
  | unitary r U A => simpa using DerivTot.unitary r U (A.scaled c h0 h1)
  | measure r M upd A => simpa using DerivTot.measure r M upd (A.scaled c h0 h1)
  | seq _ _ ih₁ ih₂ => exact ih₁.seq ih₂
  | cond _ _ ih₁ ih₀ => simpa using DerivTot.cond ih₁ ih₀
  | whileLoop t _ ih =>
      simpa [Assn.mand, Assn.mandNot] using
        DerivTot.whileLoop t (fun n => by simpa [Assn.mand] using ih n)
  | whileLoopSource t hbound hInv hRank ihInv ihRank =>
      simpa [Assn.mand, Assn.mandNot] using
        DerivTot.whileLoopSource t hbound
          (by simpa [Assn.mand] using ihInv) hRank
  | conseq hpre _ hpost ih =>
      exact .conseq (Assn.scaled_mono hpre c h0 h1) ih (Assn.scaled_mono hpost c h0 h1)

/-- The normalization used by approximate postconditions lies in `[0,1]`. -/
theorem approxCoeff_nonneg {ε : ℝ} (hε : 0 ≤ ε) : 0 ≤ (1 + ε)⁻¹ :=
  inv_nonneg.mpr (by linarith)

theorem approxCoeff_le_one {ε : ℝ} (hε : 0 ≤ ε) : (1 + ε)⁻¹ ≤ 1 := by
  exact (inv_le_one₀ (by linarith)).mpr (by linarith)

section OperatorOrder
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Multiplication by a nonnegative real preserves the operator order. -/
theorem real_smul_operator_mono {X Y : E →ₗ[ℂ] E} (h : X ≤ Y)
    {c : ℝ} (hc : 0 ≤ c) : (c : ℂ) • X ≤ (c : ℂ) • Y := by
  rw [le_iff_inner_le] at h ⊢
  intro v
  simp only [LinearMap.smul_apply, inner_smul_right]
  exact mul_le_mul_of_nonneg_left (h v) (Complex.zero_le_real.mpr hc)

/-- Adding an identity error and dividing by `1+ε` gives an effect. -/
theorem isEffect_approx {X : E →ₗ[ℂ] E} (hX : IsEffect X)
    {ε : ℝ} (hε : 0 ≤ ε) :
    IsEffect ((((1 + ε)⁻¹ : ℝ) : ℂ) • X + ((ε / (1 + ε) : ℝ) : ℂ) • 1) := by
  have hden : 0 < 1 + ε := by linarith
  have hc := approxCoeff_nonneg hε
  have he : 0 ≤ ε / (1 + ε) := div_nonneg hε hden.le
  have hs : ((1 + ε)⁻¹ : ℝ) + ε / (1 + ε) = 1 := by
    field_simp
  have hid : ((((1 + ε)⁻¹ : ℝ) : ℂ) • (1 : E →ₗ[ℂ] E) +
      ((ε / (1 + ε) : ℝ) : ℂ) • 1) = 1 := by
    rw [← add_smul, ← Complex.ofReal_add, hs, Complex.ofReal_one, one_smul]
  constructor
  · have h₁ := real_smul_operator_mono hX.1 hc
    have h₂ := real_smul_operator_mono (show (0 : E →ₗ[ℂ] E) ≤ 1 from isEffect_one.1) he
    simpa using add_le_add h₁ h₂
  · calc
      _ ≤ (((1 + ε)⁻¹ : ℝ) : ℂ) • (1 : E →ₗ[ℂ] E) +
          ((ε / (1 + ε) : ℝ) : ℂ) • 1 :=
        add_le_add (real_smul_operator_mono hX.2 hc) le_rfl
      _ = 1 := hid
end OperatorOrder

/-- The effect `(A+ε I)/(1+ε)` used for approximate specifications. -/
noncomputable def Assn.approx (A : Assn σT D) (ε : ℝ) (hε : 0 ≤ ε) : Assn σT D where
  op σ := (((1 + ε)⁻¹ : ℝ) : ℂ) • A.op σ + ((ε / (1 + ε) : ℝ) : ℂ) • 1
  isEffect σ := isEffect_approx (A.isEffect σ) hε

omit [∀ i, Inhabited (D i)] in
@[simp] theorem Assn.approx_op (A : Assn σT D) (ε : ℝ) (hε : 0 ≤ ε) (σ : σT) :
    (A.approx ε hε).op σ = (((1 + ε)⁻¹ : ℝ) : ℂ) • A.op σ +
      ((ε / (1 + ε) : ℝ) : ℂ) • 1 := rfl

omit [∀ i, Inhabited (D i)] in
/-- The normalized form of the approximate postcondition. -/
theorem Assn.approx_op_eq (A : Assn σT D) (ε : ℝ) (hε : 0 ≤ ε) (σ : σT) :
    (A.approx ε hε).op σ = (((1 + ε)⁻¹ : ℝ) : ℂ) •
      (A.op σ + (ε : ℂ) • 1) := by
  rw [approx_op, smul_add, smul_smul]
  congr 1
  congr 1
  push_cast
  ring

/-- An operator-error entailment transfers any constructor derivation to a
normalized approximate postcondition. No restriction on input states is used. -/
theorem DerivTot.approx_of_le {A B : Assn σT D} {P : Prog σT D}
    (h : DerivTot A P B) (C : Assn σT D) (ε : ℝ) (hε : 0 ≤ ε)
    (hle : ∀ σ, B.op σ ≤ C.op σ + (ε : ℂ) • 1) :
    DerivTot (A.scaled (1 + ε)⁻¹ (approxCoeff_nonneg hε) (approxCoeff_le_one hε))
      P (C.approx ε hε) := by
  refine .conseq (fun _ => le_rfl)
    (h.scaled (1 + ε)⁻¹ (approxCoeff_nonneg hε) (approxCoeff_le_one hε)) ?_
  intro σ
  rw [Assn.scaled_op, Assn.approx_op_eq]
  exact real_smul_operator_mono (hle σ) (approxCoeff_nonneg hε)

/-- A postcondition mask restricts the states on which the error entailment
must be established. Outputs outside the mask contribute zero. -/
theorem DerivTot.approx_mask_of_le {A B : Assn σT D} {P : Prog σT D}
    {φ : σT → Prop} (h : DerivTot A P (B.mask φ))
    (C : Assn σT D) (ε : ℝ) (hε : 0 ≤ ε)
    (hle : ∀ σ, φ σ → B.op σ ≤ C.op σ + (ε : ℂ) • 1) :
    DerivTot (A.scaled (1 + ε)⁻¹ (approxCoeff_nonneg hε) (approxCoeff_le_one hε))
      P (C.approx ε hε) := by
  apply h.approx_of_le C ε hε
  intro σ
  by_cases hφ : φ σ
  · rw [Assn.mask_op_of_pos hφ]
    exact hle σ hφ
  · rw [Assn.mask_op_of_neg hφ]
    have he := real_smul_operator_mono
      (show (0 : EndM D (univ : Finset L)) ≤ 1 from isEffect_one.1) hε
    simpa using add_le_add (C.isEffect σ).1 he

/-- Transfer a verified exact pure-state output to a nearby target state.
The error is represented in the postcondition effect, not by restricting
validity to the particular pure input used to state the exact specification. -/
theorem DerivTot.approx_state {A : Assn σT D} {P : Prog σT D}
    {u v : HS D (univ : Finset L)} {hu : ‖u‖ = 1} {hv : ‖v‖ = 1}
    (h : DerivTot A P (Assn.ofState u hu)) (ε : ℝ) (hε : 0 ≤ ε)
    (hdist : ‖u - v‖ ≤ ε) :
    DerivTot (A.scaled (1 + ε)⁻¹ (approxCoeff_nonneg hε) (approxCoeff_le_one hε))
      P ((Assn.ofState v hv).approx ε hε) := by
  apply h.approx_of_le (Assn.ofState v hv) ε hε
  intro σ
  exact outerLM_self_le_add_of_norm_sub_le u v hu hv hε hdist

/-- The state-family version allows the output mask to supply the hypotheses
needed for the approximation estimate. -/
theorem DerivTot.approx_stateFam {A : Assn σT D} {P : Prog σT D}
    {u v : σT → HS D (univ : Finset L)}
    {hu : ∀ σ, ‖u σ‖ = 1} {hv : ∀ σ, ‖v σ‖ = 1} {φ : σT → Prop}
    (h : DerivTot A P ((Assn.ofStateFam u hu).mask φ))
    (ε : ℝ) (hε : 0 ≤ ε) (hdist : ∀ σ, φ σ → ‖u σ - v σ‖ ≤ ε) :
    DerivTot (A.scaled (1 + ε)⁻¹ (approxCoeff_nonneg hε) (approxCoeff_le_one hε))
      P ((Assn.ofStateFam v hv).approx ε hε) := by
  apply h.approx_mask_of_le (Assn.ofStateFam v hv) ε hε
  intro σ hφ
  exact outerLM_self_le_add_of_norm_sub_le (u σ) (v σ) (hu σ) (hv σ) hε (hdist σ hφ)

end Qhl
