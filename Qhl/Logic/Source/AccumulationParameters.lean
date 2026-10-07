import Qhl.Logic.Source.Accumulation
import Qhl.Program.FrameParameters

/-! # Source accumulation for local operators with preserved parameters -/

namespace Qhl

open Finset

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)] {σT E : Type*}

namespace SourceAssertion

/-- Normalization of a local Kraus family persists after lifting it to the
whole quantum world at each classical parameter value. -/
theorem localKraus_normalized {ι : Type*} [Fintype ι]
    (e : σT → E) (S : E → Finset L) (f : ∀ a, ι → EndM D (S a))
    (hlocal : ∀ a, ∑ i, LinearMap.adjoint (f a i) ∘ₗ f a i = 1) (σ : σT) :
    ∑ i, LinearMap.adjoint (liftF D (subset_univ (S (e σ))) (f (e σ) i)) ∘ₗ
      liftF D (subset_univ (S (e σ))) (f (e σ) i) = 1 := by
  exact isQMeasure_liftF (subset_univ (S (e σ))) (hlocal (e σ))

/-- Corrected total accumulation for local Kraus operators whose classical
parameters are unchanged and whose register is disjoint from program operations. -/
theorem validTot_localKraus {ι : Type*} [Fintype ι]
    (φ ψ : σT → Prop) (A B : ι → SourceAssertion σT D)
    (e : σT → E) (S : E → Finset L) (f : ∀ a, ι → EndM D (S a))
    (hlocal : ∀ a, ∑ i, LinearMap.adjoint (f a i) ∘ₗ f a i = 1)
    (P : Prog σT D) (hp : P.PreservesParameters e)
    (hq : P.AvoidsRegister (fun σ => S (e σ)))
    (hdom : ∀ σ, ψ σ → ∀ i j, (B i).defined σ ↔ (B j).defined σ)
    (hcomp : ∀ i, validTot ((A i).withClassical φ).toAssn P
      ((B i).withClassical ψ).toAssn) :
    validTot (kraus φ A
      (fun σ i => liftF D (subset_univ (S (e σ))) (f (e σ) i))
      (localKraus_normalized e S f hlocal)).toAssn P
      (kraus ψ B
        (fun σ i => liftF D (subset_univ (S (e σ))) (f (e σ) i))
        (localKraus_normalized e S f hlocal)).toAssn := by
  apply validTot_kraus φ ψ A B _ _ P
  · intro i
    exact P.krausFrame_of_parameters e S (fun a => f a i) hp hq
  · exact hdom
  · exact hcomp

/-- Corrected partial accumulation under the same concrete parameter and
register conditions. -/
theorem validPar_localKraus {ι : Type*} [Fintype ι]
    (φ ψ : σT → Prop) (A B : ι → SourceAssertion σT D)
    (e : σT → E) (S : E → Finset L) (f : ∀ a, ι → EndM D (S a))
    (hlocal : ∀ a, ∑ i, LinearMap.adjoint (f a i) ∘ₗ f a i = 1)
    (P : Prog σT D) (hp : P.PreservesParameters e)
    (hq : P.AvoidsRegister (fun σ => S (e σ)))
    (hdom : ∀ σ, ψ σ → ∀ i j, (B i).defined σ ↔ (B j).defined σ)
    (hcomp : ∀ i, validPar ((A i).withClassical φ).toAssn P
      ((B i).withClassical ψ).toAssn) :
    validPar (kraus φ A
      (fun σ i => liftF D (subset_univ (S (e σ))) (f (e σ) i))
      (localKraus_normalized e S f hlocal)).toAssn P
      (kraus ψ B
        (fun σ i => liftF D (subset_univ (S (e σ))) (f (e σ) i))
        (localKraus_normalized e S f hlocal)).toAssn := by
  apply validPar_kraus φ ψ A B _ _ P
  · intro i
    exact P.krausFrame_of_parameters e S (fun a => f a i) hp hq
  · exact hdom
  · exact hcomp

end SourceAssertion

end Qhl
