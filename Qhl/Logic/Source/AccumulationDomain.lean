import Qhl.Logic.Source.Domain
import Qhl.Logic.Source.Accumulation
import Qhl.Logic.Source.AccumulationOne
import Qhl.History.PreservedCondition

/-! # A preserved extra domain on accumulated source predicates

The Accum2 semantic helpers here allow pairwise domain agreement. The source
constructors and register adapters impose the stronger approved post-definedness
premise; these helpers alone do not certify an application of the source rule.
-/

namespace Qhl

open Finset

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)] {σT : Type*}

namespace SourceAssertion

/-- Total Accum2 with a preserved additional domain on the compound predicates.
The component premises retain their original classical formulas and domains. -/
theorem validTot_kraus_onDomain {ι : Type*} [Fintype ι]
    (φ ψ : σT → Prop) (A B : ι → SourceAssertion σT D)
    (K : σT → ι → EndM D (univ : Finset L))
    (hK : ∀ σ, ∑ i, LinearMap.adjoint (K σ i) ∘ₗ K σ i = 1)
    (P : Prog σT D) (hframe : ∀ i, P.KrausFrame (fun σ => K σ i))
    (d : σT → Prop) (hp : P.PreservesParameters d)
    (hdom : ∀ σ, ψ σ → ∀ i j, (B i).defined σ ↔ (B j).defined σ)
    (hcomp : ∀ i, validTot ((A i).withClassical φ).toAssn P
      ((B i).withClassical ψ).toAssn) :
    validTot ((kraus φ A K hK).onDomain d).toAssn P
      ((kraus ψ B K hK).onDomain d).toAssn := by
  simpa only [onDomain_toAssn] using
    validTot_mask_preserved hp (validTot_kraus φ ψ A B K hK P hframe hdom hcomp)

/-- Partial Accum2 with the same preserved compound domain. -/
theorem validPar_kraus_onDomain {ι : Type*} [Fintype ι]
    (φ ψ : σT → Prop) (A B : ι → SourceAssertion σT D)
    (K : σT → ι → EndM D (univ : Finset L))
    (hK : ∀ σ, ∑ i, LinearMap.adjoint (K σ i) ∘ₗ K σ i = 1)
    (P : Prog σT D) (hframe : ∀ i, P.KrausFrame (fun σ => K σ i))
    (d : σT → Prop) (hp : P.PreservesParameters d)
    (hdom : ∀ σ, ψ σ → ∀ i j, (B i).defined σ ↔ (B j).defined σ)
    (hcomp : ∀ i, validPar ((A i).withClassical φ).toAssn P
      ((B i).withClassical ψ).toAssn) :
    validPar ((kraus φ A K hK).onDomain d).toAssn P
      ((kraus ψ B K hK).onDomain d).toAssn := by
  simpa only [onDomain_toAssn] using
    validPar_mask_preserved hp (validPar_kraus φ ψ A B K hK P hframe hdom hcomp)

/-- Total Accum1 with a shared preserved domain only on its compound
precondition and singleton postcondition. -/
theorem validTot_accumOne_onDomain {ι : Type*} [Fintype ι]
    (φ : σT → Prop) (ψ : ι → σT → Prop)
    (A : ι → SourceAssertion σT D) (B : SourceAssertion σT D)
    (K : σT → ι → EndM D (univ : Finset L))
    (J : σT → EndM D (univ : Finset L))
    (hK : ∀ σ, ∑ i, LinearMap.adjoint (K σ i) ∘ₗ K σ i = 1)
    (hJ : ∀ σ, LinearMap.adjoint (J σ) ∘ₗ J σ ≤ 1)
    (P : Prog σT D) (hframe : ∀ i, P.KrausFrame (fun σ => K σ i))
    (d : σT → Prop) (hp : P.PreservesParameters d)
    (hexcl : ∀ σ i j, i ≠ j → ψ i σ → ¬ ψ j σ)
    (hdom : ∀ σ i (ρ : PDensity D), (ρ.conj (K σ i)).op ≤ (ρ.conj (J σ)).op)
    (hcomp : ∀ i, validTot ((A i).withClassical φ).toAssn P
      (B.withClassical (ψ i)).toAssn) :
    validTot ((kraus φ A K hK).onDomain d).toAssn P
      ((krausOne (fun σ => ∃ i, ψ i σ) B J hJ).onDomain d).toAssn := by
  simpa only [onDomain_toAssn] using
    validTot_mask_preserved hp
      (validTot_accumOne φ ψ A B K J hK hJ P hframe hexcl hdom hcomp)

/-- Partial Accum1 under the same preserved domain, with unchanged component
premises and explicit state-side domination. -/
theorem validPar_accumOne_onDomain {ι : Type*} [Fintype ι]
    (φ : σT → Prop) (ψ : ι → σT → Prop)
    (A : ι → SourceAssertion σT D) (B : SourceAssertion σT D)
    (K : σT → ι → EndM D (univ : Finset L))
    (J : σT → EndM D (univ : Finset L))
    (hK : ∀ σ, ∑ i, LinearMap.adjoint (K σ i) ∘ₗ K σ i = 1)
    (hJ : ∀ σ, LinearMap.adjoint (J σ) ∘ₗ J σ ≤ 1)
    (P : Prog σT D) (hframe : ∀ i, P.KrausFrame (fun σ => K σ i))
    (d : σT → Prop) (hp : P.PreservesParameters d)
    (hexcl : ∀ σ i j, i ≠ j → ψ i σ → ¬ ψ j σ)
    (hdom : ∀ σ i (ρ : PDensity D), (ρ.conj (K σ i)).op ≤ (ρ.conj (J σ)).op)
    (hcomp : ∀ i, validPar ((A i).withClassical φ).toAssn P
      (B.withClassical (ψ i)).toAssn) :
    validPar ((kraus φ A K hK).onDomain d).toAssn P
      ((krausOne (fun σ => ∃ i, ψ i σ) B J hJ).onDomain d).toAssn := by
  simpa only [onDomain_toAssn] using
    validPar_mask_preserved hp
      (validPar_accumOne φ ψ A B K J hK hJ P hframe hexcl hdom hcomp)

end SourceAssertion

end Qhl
