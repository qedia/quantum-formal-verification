import Qhl.Logic.Source.AccumulationParameters
import Qhl.Logic.Source.Domain
import Qhl.Logic.Source.AccumulationOneOrder

/-! # Kraus modifiers on possibly aliased register expressions

The total operator extension outside the distinct-register domain is arbitrary.
That domain is retained separately in the source assertion, so the fallback
operators never give an interpretation to an ill-defined source predicate.
-/

namespace Qhl

open Finset

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)] {σT E : Type*}

/-- A normalized family on a nonzero tuple space has an index. -/
theorem QMeasure.index_nonempty {m k : ℕ} {r : Fin k → L}
    (M : QMeasure m (TSpace D r)) : Nonempty (Fin m) := by
  classical
  by_contra h
  haveI : IsEmpty (Fin m) := not_nonempty_iff.mp h
  have he : (0 : TSpace D r →ₗ[ℂ] TSpace D r) = 1 := by
    simpa using M.complete
  exact zero_ne_one he

/-- A total normalized extension of the source operators on a raw register.
The identity/zero family outside Dist is ignored by the source domain. -/
noncomputable def registerKrausOps {m k : ℕ} (r : E → Fin k → L)
    (M : ∀ a, QMeasure m (TSpace D (r a))) (a : E) (i : Fin m) :
    EndM D (univ : Finset L) :=
  if hr : Function.Injective (r a) then regLift ⟨r a, hr⟩ ((M a).M i)
  else if i = Classical.choice (M a).index_nonempty then 1 else 0

/-- The fallback preserves normalization even outside the source domain. -/
theorem registerKrausOps_normalized {m k : ℕ} (r : E → Fin k → L)
    (M : ∀ a, QMeasure m (TSpace D (r a))) (a : E) :
    ∑ i, LinearMap.adjoint (registerKrausOps r M a i) ∘ₗ registerKrausOps r M a i = 1 := by
  classical
  by_cases hr : Function.Injective (r a)
  · simp only [registerKrausOps, dif_pos hr]
    exact isQMeasure_regLift ⟨r a, hr⟩ (M a)
  · simp only [registerKrausOps, dif_neg hr]
    rw [Finset.sum_eq_single (Classical.choice (M a).index_nonempty)]
    · simp [Module.End.one_eq_id]
    · intro i _ hi
      simp [hi]
    · simp

/-- The source modifier explicitly retains Dist as part of its quantum domain. -/
noncomputable def SourceAssertion.registerKraus {m k : ℕ}
    (φ : σT → Prop) (A : Fin m → SourceAssertion σT D) (e : σT → E)
    (r : E → Fin k → L) (M : ∀ a, QMeasure m (TSpace D (r a))) :
    SourceAssertion σT D :=
  (SourceAssertion.kraus φ A (fun σ => registerKrausOps r M (e σ))
    (fun σ => registerKrausOps_normalized r M (e σ))).onDomain
      (fun σ => Function.Injective (r (e σ)))

/-- The domain is exactly distinct operands and every component being defined. -/
theorem SourceAssertion.registerKraus_defined {m k : ℕ}
    (φ : σT → Prop) (A : Fin m → SourceAssertion σT D) (e : σT → E)
    (r : E → Fin k → L) (M : ∀ a, QMeasure m (TSpace D (r a))) (σ : σT) :
    (SourceAssertion.registerKraus φ A e r M).defined σ ↔
      Function.Injective (r (e σ)) ∧ ∀ i, (A i).defined σ := Iff.rfl

/-- Even the unused fallback has a local representation on the register image. -/
noncomputable def registerKrausLocal {m k : ℕ} (r : E → Fin k → L)
    (M : ∀ a, QMeasure m (TSpace D (r a))) (a : E) (i : Fin m) :
    EndM D (univ.image (r a)) :=
  if hr : Function.Injective (r a) then (⟨r a, hr⟩ : Reg L k).op D ((M a).M i)
  else if i = Classical.choice (M a).index_nonempty then 1 else 0

/-- The total full-space family is the cylindrical extension of the local one. -/
theorem registerKrausOps_eq_lift {m k : ℕ} (r : E → Fin k → L)
    (M : ∀ a, QMeasure m (TSpace D (r a))) (a : E) (i : Fin m) :
    registerKrausOps r M a i =
      liftF D (subset_univ (univ.image (r a))) (registerKrausLocal r M a i) := by
  classical
  by_cases hr : Function.Injective (r a)
  · simp [registerKrausOps, registerKrausLocal, Reg.sig, hr, regLift]
  · simp [registerKrausOps, registerKrausLocal, hr]
    split_ifs <;> simp

/-- Unchanged source parameters and disjoint operands establish the raw-register frame. -/
theorem Prog.krausFrame_register {m k : ℕ} (P : Prog σT D) (e : σT → E)
    (r : E → Fin k → L) (M : ∀ a, QMeasure m (TSpace D (r a)))
    (hp : P.PreservesParameters e)
    (hq : P.AvoidsRegister (fun σ => univ.image (r (e σ)))) (i : Fin m) :
    P.KrausFrame (fun σ => registerKrausOps r M (e σ) i) := by
  simp_rw [registerKrausOps_eq_lift]
  exact P.krausFrame_of_parameters e (fun a => univ.image (r a))
    (fun a => registerKrausLocal r M a i) hp hq

/-- Total extension of a singleton modifier; the fallback is ignored by Dist. -/
noncomputable def registerSingletonOps {k : ℕ} (r : E → Fin k → L)
    (J : ∀ a, TSpace D (r a) →ₗ[ℂ] TSpace D (r a)) (a : E) :
    EndM D (univ : Finset L) :=
  if hr : Function.Injective (r a) then regLift ⟨r a, hr⟩ (J a) else 1

/-- Ordered-register lifting preserves the singleton contraction bound. -/
theorem registerSingletonOps_contraction {k : ℕ} (r : E → Fin k → L)
    (J : ∀ a, TSpace D (r a) →ₗ[ℂ] TSpace D (r a))
    (hJ : ∀ a, LinearMap.adjoint (J a) ∘ₗ J a ≤ 1) (a : E) :
    LinearMap.adjoint (registerSingletonOps r J a) ∘ₗ registerSingletonOps r J a ≤ 1 := by
  classical
  by_cases hr : Function.Injective (r a)
  · simp only [registerSingletonOps, dif_pos hr, regLift, adjoint_liftF,
      ← liftF_comp, Reg.adjoint_op, ← Reg.op_comp]
    rw [← liftF_one D (subset_univ _)]
    apply (liftF_le_liftF_iff D _ _ _).mpr
    rw [LinearMap.le_def]
    have hp := (⟨r a, hr⟩ : Reg L k).op_isPositive ((LinearMap.le_def _ _).mp (hJ a))
    have he : (⟨r a, hr⟩ : Reg L k).op D
        (1 - LinearMap.adjoint (J a) ∘ₗ J a) =
        1 - (⟨r a, hr⟩ : Reg L k).op D (LinearMap.adjoint (J a) ∘ₗ J a) := by
      change ((Reg.encode D ⟨r a, hr⟩).toLinearEquiv.conj _) = _
      rw [map_sub]
      rw [show (Reg.encode D ⟨r a, hr⟩).toLinearEquiv.conj 1 = 1 from Reg.op_one _]
      rfl
    rw [he] at hp
    exact hp
  · simp [registerSingletonOps, hr, Module.End.one_eq_id]

/-- A singleton subnormalized modifier retains its child's domain and Dist. -/
noncomputable def SourceAssertion.registerKrausOne {k : ℕ}
    (ψ : σT → Prop) (B : SourceAssertion σT D) (e : σT → E)
    (r : E → Fin k → L)
    (J : ∀ a, TSpace D (r a) →ₗ[ℂ] TSpace D (r a))
    (hJ : ∀ a, LinearMap.adjoint (J a) ∘ₗ J a ≤ 1) : SourceAssertion σT D :=
  (SourceAssertion.krausOne ψ B (fun σ => registerSingletonOps r J (e σ))
    (fun σ => registerSingletonOps_contraction r J hJ (e σ))).onDomain
      (fun σ => Function.Injective (r (e σ)))

end Qhl
