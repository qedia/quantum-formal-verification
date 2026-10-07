import Qhl.Logic.Source.Rules

/-! # Classical preservation along executions that do not measure

These operational executions do not inspect quantum values or assertion domains.
Classical preservation for arbitrary source derivations is not asserted: empty
Convex2 permits vacuous zero-precondition derivations.
-/

namespace Qhl

universe u

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)] {σT : Type u}

/-- A finite classical execution traversing no measurement command. Quantum
initialization and unitary commands leave the classical store unchanged. -/
inductive MeasurementFreeExec : Prog σT D → σT → σT → Prop where
  | skip (σ : σT) : MeasurementFreeExec .skip σ σ
  | assign (f : σT → σT) (σ : σT) : MeasurementFreeExec (.assign f) σ (f σ)
  | initProg (S : σT → Finset L) (σ : σT) : MeasurementFreeExec (.init S) σ σ
  | unitary {k : ℕ} (r : RegExpr σT L k)
      (U : ∀ σ, UnitaryOp (TSpace D (r σ))) (σ : σT) :
      MeasurementFreeExec (.unitary k r U) σ σ
  | seq {P Q : Prog σT D} {σ τ υ : σT} :
      MeasurementFreeExec P σ τ → MeasurementFreeExec Q τ υ →
      MeasurementFreeExec (.seq P Q) σ υ
  | condTrue {P Q : Prog σT D} {b : σT → Bool} {σ τ : σT} :
      b σ = true → MeasurementFreeExec P σ τ → MeasurementFreeExec (.ite b P Q) σ τ
  | condFalse {P Q : Prog σT D} {b : σT → Bool} {σ τ : σT} :
      b σ = false → MeasurementFreeExec Q σ τ → MeasurementFreeExec (.ite b P Q) σ τ
  | whileFalse {P : Prog σT D} {b : σT → Bool} {σ : σT} :
      b σ = false → MeasurementFreeExec (.while b P) σ σ
  | whileTrue {P : Prog σT D} {b : σT → Bool} {σ τ υ : σT} :
      b σ = true → MeasurementFreeExec P σ τ → MeasurementFreeExec (.while b P) τ υ →
      MeasurementFreeExec (.while b P) σ υ

/-- Classical invariant preservation for a finite measurement-free loop execution. -/
theorem MeasurementFreeExec.while_invariant {P : Prog σT D} {b : σT → Bool}
    {φ : σT → Prop} (hbody : ∀ σ τ, MeasurementFreeExec P σ τ →
      φ σ ∧ b σ = true → φ τ) {σ τ : σT}
    (h : MeasurementFreeExec (.while b P) σ τ) (hφ : φ σ) : φ τ ∧ b τ = false := by
  generalize he : Prog.while b P = W at h
  induction h with
  | whileFalse hb => cases he; exact ⟨hφ, hb⟩
  | whileTrue hb hstep _ _ ih =>
      cases he
      exact ih (hbody _ _ hstep ⟨hφ, hb⟩) rfl
  | _ => cases he

/-- Equality normalization makes a Kraus family nonempty. -/
theorem normalized_kraus_nonempty {ι : Type} [Fintype ι]
    (K : ι → EndM D (Finset.univ : Finset L))
    (hK : ∑ i, LinearMap.adjoint (K i) ∘ₗ K i = 1) : Nonempty ι := by
  classical
  by_contra h
  haveI : IsEmpty ι := not_nonempty_iff.mp h
  have hz : (0 : EndM D (Finset.univ : Finset L)) = 1 := by simp at hK
  exact zero_ne_one hz

/- Empty Convex2 can derive a zero-precondition triple with false classical
postcondition. Consequently classical preservation is not a property of all
source derivations; only the operational execution relation is retained here. -/

end Qhl
