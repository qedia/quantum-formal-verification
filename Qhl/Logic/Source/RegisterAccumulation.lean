import Qhl.Logic.Source.RegisterKraus
import Qhl.Logic.Source.RulesSoundness
import Qhl.Logic.Source.RegisterDomination
import Qhl.HSpace.DensityDomination

/-! # Accumulation rules for raw register expressions with explicit Dist domains -/

namespace Qhl

open Finset

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)] {σT E : Type*}

namespace SourceAssertion

/-- The sole raw-register branch satisfies singleton normalization. -/
theorem registerKrausOps_one_normalized {k : ℕ} (e : σT → E)
    (r : E → Fin k → L) (J : ∀ a, QMeasure 1 (TSpace D (r a))) (σ : σT) :
    LinearMap.adjoint (registerKrausOps r J (e σ) 0) ∘ₗ
      registerKrausOps r J (e σ) 0 = 1 := by
  simpa using registerKrausOps_normalized r J (e σ)

/-- The Fin 1 raw-register source predicate is the singleton constructor with
its Dist domain retained. -/
theorem registerKraus_one_eq_krausOne {k : ℕ} (ψ : σT → Prop)
    (B : SourceAssertion σT D) (e : σT → E) (r : E → Fin k → L)
    (J : ∀ a, QMeasure 1 (TSpace D (r a))) :
    registerKraus ψ (fun _ : Fin 1 => B) e r J =
      (krausOne ψ B (fun σ => registerKrausOps r J (e σ) 0)
        (fun σ => le_of_eq (registerKrausOps_one_normalized e r J σ))).onDomain
          (fun σ => Function.Injective (r (e σ))) := by
  simp [registerKraus, krausOne, kraus, krausSubnormalized, onDomain]

end SourceAssertion

namespace SourceDerivTot

/-- Corrected Accum2 on a raw register: the compound quantum domain records
Dist, while the component source derivations remain unchanged. -/
theorem accum2_register {m k : ℕ} (φ ψ : σT → Prop)
    (A B : Fin m → SourceAssertion σT D) (e : σT → E)
    (r : E → Fin k → L) (M : ∀ a, QMeasure m (TSpace D (r a)))
    (P : Prog σT D) (hp : P.PreservesParameters e)
    (hq : P.AvoidsRegister (fun σ => univ.image (r (e σ))))
    (hdom : ∀ σ, ψ σ → ∀ i, (B i).defined σ)
    (hcomp : ∀ i, SourceDerivTot ((A i).withClassical φ) P
      ((B i).withClassical ψ)) :
    SourceDerivTot (SourceAssertion.registerKraus φ A e r M) P
      (SourceAssertion.registerKraus ψ B e r M) := by
  change SourceDerivTot
    ((SourceAssertion.kraus φ A (fun σ => registerKrausOps r M (e σ))
      (fun σ => registerKrausOps_normalized r M (e σ))).onDomain
      (fun σ => Function.Injective (r (e σ)))) P
    ((SourceAssertion.kraus ψ B (fun σ => registerKrausOps r M (e σ))
      (fun σ => registerKrausOps_normalized r M (e σ))).onDomain
      (fun σ => Function.Injective (r (e σ))))
  exact .accum2Domain φ ψ A B (fun σ => registerKrausOps r M (e σ))
    (fun σ => registerKrausOps_normalized r M (e σ)) P
    (fun i => P.krausFrame_register e r M hp hq i)
    (fun σ => Function.Injective (r (e σ)))
    (hp.comp fun a => Function.Injective (r a)) hdom hcomp

/-- Accum1 on a raw register, using local density-operator domination to
establish domination for every full-world density. -/
theorem accum1_register {m k : ℕ} (φ : σT → Prop) (ψ : Fin m → σT → Prop)
    (A : Fin m → SourceAssertion σT D) (B : SourceAssertion σT D)
    (e : σT → E) (r : E → Fin k → L)
    (M : ∀ a, QMeasure m (TSpace D (r a)))
    (J : ∀ a, QMeasure 1 (TSpace D (r a)))
    (P : Prog σT D) (hp : P.PreservesParameters e)
    (hq : P.AvoidsRegister (fun σ => univ.image (r (e σ))))
    (hexcl : ∀ σ i j, i ≠ j → ψ i σ → ¬ ψ j σ)
    (hdom : ∀ a i (ρ : TSpace D (r a) →ₗ[ℂ] TSpace D (r a)),
      IsDensity1 ρ → (M a).M i ∘ₗ ρ ∘ₗ LinearMap.adjoint ((M a).M i) ≤
        (J a).M 0 ∘ₗ ρ ∘ₗ LinearMap.adjoint ((J a).M 0))
    (hcomp : ∀ i, SourceDerivTot ((A i).withClassical φ) P
      (B.withClassical (ψ i))) :
    SourceDerivTot (SourceAssertion.registerKraus φ A e r M) P
      (SourceAssertion.registerKraus (fun σ => ∃ i, ψ i σ)
        (fun _ : Fin 1 => B) e r J) := by
  change SourceDerivTot
    ((SourceAssertion.kraus φ A (fun σ => registerKrausOps r M (e σ))
      (fun σ => registerKrausOps_normalized r M (e σ))).onDomain
      (fun σ => Function.Injective (r (e σ)))) P
    (SourceAssertion.registerKraus (fun σ => ∃ i, ψ i σ)
      (fun _ : Fin 1 => B) e r J)
  rw [SourceAssertion.registerKraus_one_eq_krausOne]
  exact .accum1Domain φ ψ A B _ _ _ _ P
    (fun i => P.krausFrame_register e r M hp hq i)
    _ (hp.comp fun a => Function.Injective (r a)) hexcl
    (fun σ i ρ => registerKrausOps_domination r M J
      (fun a j R hR => conj_le_of_density1_domination _ _ (hdom a j) R hR)
      (e σ) i ρ) hcomp

/-- Accum1 with a general contractive output modifier and the source's local
normalized-density domination premise. -/
theorem accum1_register_contraction {m k : ℕ} (φ : σT → Prop) (ψ : Fin m → σT → Prop)
    (A : Fin m → SourceAssertion σT D) (B : SourceAssertion σT D)
    (e : σT → E) (r : E → Fin k → L)
    (M : ∀ a, QMeasure m (TSpace D (r a)))
    (J : ∀ a, TSpace D (r a) →ₗ[ℂ] TSpace D (r a))
    (hJ : ∀ a, LinearMap.adjoint (J a) ∘ₗ J a ≤ 1)
    (P : Prog σT D) (hp : P.PreservesParameters e)
    (hq : P.AvoidsRegister (fun σ => univ.image (r (e σ))))
    (hexcl : ∀ σ i j, i ≠ j → ψ i σ → ¬ ψ j σ)
    (hdom : ∀ a i (ρ : TSpace D (r a) →ₗ[ℂ] TSpace D (r a)),
      IsDensity1 ρ → (M a).M i ∘ₗ ρ ∘ₗ LinearMap.adjoint ((M a).M i) ≤
        J a ∘ₗ ρ ∘ₗ LinearMap.adjoint (J a))
    (hcomp : ∀ i, SourceDerivTot ((A i).withClassical φ) P
      (B.withClassical (ψ i))) :
    SourceDerivTot (SourceAssertion.registerKraus φ A e r M) P
      (SourceAssertion.registerKrausOne (fun σ => ∃ i, ψ i σ) B e r J hJ) := by
  exact .accum1Domain φ ψ A B _ _ _ _ P
    (fun i => P.krausFrame_register e r M hp hq i)
    _ (hp.comp fun a => Function.Injective (r a)) hexcl
    (fun σ i ρ => registerSingletonOps_domination r M J
      (fun a j R hR => conj_le_of_density1_domination _ _ (hdom a j) R hR)
      (e σ) i ρ) hcomp

end SourceDerivTot

namespace SourceDerivPar

/-- Partial Accum2 with every postpredicate defined under `ψ` and the source Dist domain. -/
theorem accum2_register {m k : ℕ} (φ ψ : σT → Prop)
    (A B : Fin m → SourceAssertion σT D) (e : σT → E)
    (r : E → Fin k → L) (M : ∀ a, QMeasure m (TSpace D (r a)))
    (P : Prog σT D) (hp : P.PreservesParameters e)
    (hq : P.AvoidsRegister (fun σ => univ.image (r (e σ))))
    (hdom : ∀ σ, ψ σ → ∀ i, (B i).defined σ)
    (hcomp : ∀ i, SourceDerivPar ((A i).withClassical φ) P
      ((B i).withClassical ψ)) :
    SourceDerivPar (SourceAssertion.registerKraus φ A e r M) P
      (SourceAssertion.registerKraus ψ B e r M) := by
  change SourceDerivPar
    ((SourceAssertion.kraus φ A (fun σ => registerKrausOps r M (e σ))
      (fun σ => registerKrausOps_normalized r M (e σ))).onDomain
      (fun σ => Function.Injective (r (e σ)))) P
    ((SourceAssertion.kraus ψ B (fun σ => registerKrausOps r M (e σ))
      (fun σ => registerKrausOps_normalized r M (e σ))).onDomain
      (fun σ => Function.Injective (r (e σ))))
  exact .accum2Domain φ ψ A B (fun σ => registerKrausOps r M (e σ))
    (fun σ => registerKrausOps_normalized r M (e σ)) P
    (fun i => P.krausFrame_register e r M hp hq i)
    (fun σ => Function.Injective (r (e σ)))
    (hp.comp fun a => Function.Injective (r a)) hdom hcomp

/-- Partial Accum1 on a raw register with the same concrete domination
premise and unchanged component derivations. -/
theorem accum1_register {m k : ℕ} (φ : σT → Prop) (ψ : Fin m → σT → Prop)
    (A : Fin m → SourceAssertion σT D) (B : SourceAssertion σT D)
    (e : σT → E) (r : E → Fin k → L)
    (M : ∀ a, QMeasure m (TSpace D (r a)))
    (J : ∀ a, QMeasure 1 (TSpace D (r a)))
    (P : Prog σT D) (hp : P.PreservesParameters e)
    (hq : P.AvoidsRegister (fun σ => univ.image (r (e σ))))
    (hexcl : ∀ σ i j, i ≠ j → ψ i σ → ¬ ψ j σ)
    (hdom : ∀ a i (ρ : TSpace D (r a) →ₗ[ℂ] TSpace D (r a)),
      IsDensity1 ρ → (M a).M i ∘ₗ ρ ∘ₗ LinearMap.adjoint ((M a).M i) ≤
        (J a).M 0 ∘ₗ ρ ∘ₗ LinearMap.adjoint ((J a).M 0))
    (hcomp : ∀ i, SourceDerivPar ((A i).withClassical φ) P
      (B.withClassical (ψ i))) :
    SourceDerivPar (SourceAssertion.registerKraus φ A e r M) P
      (SourceAssertion.registerKraus (fun σ => ∃ i, ψ i σ)
        (fun _ : Fin 1 => B) e r J) := by
  change SourceDerivPar
    ((SourceAssertion.kraus φ A (fun σ => registerKrausOps r M (e σ))
      (fun σ => registerKrausOps_normalized r M (e σ))).onDomain
      (fun σ => Function.Injective (r (e σ)))) P
    (SourceAssertion.registerKraus (fun σ => ∃ i, ψ i σ)
      (fun _ : Fin 1 => B) e r J)
  rw [SourceAssertion.registerKraus_one_eq_krausOne]
  exact .accum1Domain φ ψ A B _ _ _ _ P
    (fun i => P.krausFrame_register e r M hp hq i)
    _ (hp.comp fun a => Function.Injective (r a)) hexcl
    (fun σ i ρ => registerKrausOps_domination r M J
      (fun a j R hR => conj_le_of_density1_domination _ _ (hdom a j) R hR)
      (e σ) i ρ) hcomp

/-- Accum1 with a general contractive output modifier and the source's local
normalized-density domination premise. -/
theorem accum1_register_contraction {m k : ℕ} (φ : σT → Prop) (ψ : Fin m → σT → Prop)
    (A : Fin m → SourceAssertion σT D) (B : SourceAssertion σT D)
    (e : σT → E) (r : E → Fin k → L)
    (M : ∀ a, QMeasure m (TSpace D (r a)))
    (J : ∀ a, TSpace D (r a) →ₗ[ℂ] TSpace D (r a))
    (hJ : ∀ a, LinearMap.adjoint (J a) ∘ₗ J a ≤ 1)
    (P : Prog σT D) (hp : P.PreservesParameters e)
    (hq : P.AvoidsRegister (fun σ => univ.image (r (e σ))))
    (hexcl : ∀ σ i j, i ≠ j → ψ i σ → ¬ ψ j σ)
    (hdom : ∀ a i (ρ : TSpace D (r a) →ₗ[ℂ] TSpace D (r a)),
      IsDensity1 ρ → (M a).M i ∘ₗ ρ ∘ₗ LinearMap.adjoint ((M a).M i) ≤
        J a ∘ₗ ρ ∘ₗ LinearMap.adjoint (J a))
    (hcomp : ∀ i, SourceDerivPar ((A i).withClassical φ) P
      (B.withClassical (ψ i))) :
    SourceDerivPar (SourceAssertion.registerKraus φ A e r M) P
      (SourceAssertion.registerKrausOne (fun σ => ∃ i, ψ i σ) B e r J hJ) := by
  exact .accum1Domain φ ψ A B _ _ _ _ P
    (fun i => P.krausFrame_register e r M hp hq i)
    _ (hp.comp fun a => Function.Injective (r a)) hexcl
    (fun σ i ρ => registerSingletonOps_domination r M J
      (fun a j R hR => conj_le_of_density1_domination _ _ (hdom a j) R hR)
      (e σ) i ρ) hcomp

end SourceDerivPar

end Qhl
