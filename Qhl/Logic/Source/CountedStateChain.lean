import Qhl.Logic.Source.CountedWhile

/-! # Source counted loops at pure-state family endpoints -/
namespace Qhl
open Finset
variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)] {σT : Type*}
namespace SourceDerivTot

/-- A state-family counted loop with its classical frame and exact exit counter.
The quantum step and independent identity-predicate rank premise are source derivations. -/
theorem countedStateChain (c : CounterLens σT) (N : σT → ℕ) (φ : σT → Prop)
    (hφ : ∀ σ k, φ (c.set σ k) ↔ φ σ)
    (hN : ∀ σ k, N (c.set σ k) = N σ)
    (fam : ℕ → σT → HS D (univ : Finset L)) (hnorm : ∀ m σ, ‖fam m σ‖ = 1)
    {v₀ v₁ : σT → HS D (univ : Finset L)}
    {hv₀ : ∀ σ, ‖v₀ σ‖ = 1} {hv₁ : ∀ σ, ‖v₁ σ‖ = 1}
    (hins : ∀ m σ k, fam m (c.set σ k) = fam m σ)
    (hzero : ∀ σ, φ σ → fam 0 σ = v₀ σ)
    (hfull : ∀ σ, φ σ → fam (N σ) σ = v₁ σ)
    {BODY : Prog σT D}
    (step : SourceDerivTot
      (SourceAssertion.ofAssn
        (Assn.ofStateFam (fun σ => fam (c.get σ) σ) (fun σ => hnorm _ σ))
        (fun σ => φ σ ∧ c.get σ < N σ)) BODY
      (SourceAssertion.ofAssn
        (Assn.ofStateFam (fun σ => fam (c.get σ + 1) σ) (fun σ => hnorm _ σ))
        (fun σ => φ σ ∧ c.get σ < N σ)))
    (hrank : ∀ z : Int, SourceDerivTot
      (SourceAssertion.identity (D := D)
        (fun σ => φ σ ∧ c.get σ < N σ ∧ (↑(N σ - c.get σ) : Int) = z)) BODY
      (SourceAssertion.identity (D := D)
        (fun σ => φ σ ∧ c.get σ < N σ ∧ (↑(N σ - c.get σ) : Int) = z))) :
    SourceDerivTot (SourceAssertion.ofAssn (Assn.ofStateFam v₀ hv₀) φ)
      (countedProg c N BODY)
      (SourceAssertion.ofAssn (Assn.ofStateFam v₁ hv₁)
        (fun σ => φ σ ∧ c.get σ = N σ)) := by
  let A := Assn.ofStateFam (fun σ => fam (c.get σ) σ) (fun σ => hnorm _ σ)
  have body : SourceDerivTot (SourceAssertion.ofAssn A (fun σ => φ σ ∧ c.get σ < N σ))
      BODY (SourceAssertion.ofAssn (A.comp (fun σ => c.set σ (c.get σ + 1)))
        (fun σ => φ σ ∧ c.get σ < N σ)) := by
    refine .conseq (SourceAssertion.entails_refl _) step ?_
    apply SourceAssertion.entails_ofAssn
    · intro _ h; exact h
    · intro σ _
      apply le_of_eq
      change outerLM (fam (c.get σ + 1) σ) (fam (c.get σ + 1) σ) =
        outerLM (fam (c.get (c.set σ (c.get σ + 1))) (c.set σ (c.get σ + 1)))
          (fam (c.get (c.set σ (c.get σ + 1))) (c.set σ (c.get σ + 1)))
      rw [c.get_set, hins]
  refine .conseq ?_ (countedWhile c N φ hφ hN A BODY body hrank) ?_
  · apply SourceAssertion.entails_ofAssn
    · intro _ h; exact h
    · intro σ hσ
      apply le_of_eq
      change outerLM (v₀ σ) (v₀ σ) =
        outerLM (fam (c.get (c.set σ 0)) (c.set σ 0))
          (fam (c.get (c.set σ 0)) (c.set σ 0))
      rw [c.get_set, hins, hzero σ hσ]
  · apply SourceAssertion.entails_ofAssn
    · intro _ h; exact h
    · intro σ hσ
      apply le_of_eq
      change outerLM (fam (c.get σ) σ) (fam (c.get σ) σ) = outerLM (v₁ σ) (v₁ σ)
      rw [hσ.2, hfull σ hσ.1]

/-- The state-family chain with only the preserved classical frame at exit. -/
theorem countedStateChainVar (c : CounterLens σT) (N : σT → ℕ) (φ : σT → Prop)
    (hφ : ∀ σ k, φ (c.set σ k) ↔ φ σ)
    (hN : ∀ σ k, N (c.set σ k) = N σ)
    (fam : ℕ → σT → HS D (univ : Finset L)) (hnorm : ∀ m σ, ‖fam m σ‖ = 1)
    {v₀ v₁ : σT → HS D (univ : Finset L)}
    {hv₀ : ∀ σ, ‖v₀ σ‖ = 1} {hv₁ : ∀ σ, ‖v₁ σ‖ = 1}
    (hins : ∀ m σ k, fam m (c.set σ k) = fam m σ)
    (hzero : ∀ σ, φ σ → fam 0 σ = v₀ σ)
    (hfull : ∀ σ, φ σ → fam (N σ) σ = v₁ σ)
    {BODY : Prog σT D}
    (step : SourceDerivTot
      (SourceAssertion.ofAssn
        (Assn.ofStateFam (fun σ => fam (c.get σ) σ) (fun σ => hnorm _ σ))
        (fun σ => φ σ ∧ c.get σ < N σ)) BODY
      (SourceAssertion.ofAssn
        (Assn.ofStateFam (fun σ => fam (c.get σ + 1) σ) (fun σ => hnorm _ σ))
        (fun σ => φ σ ∧ c.get σ < N σ)))
    (hrank : ∀ z : Int, SourceDerivTot
      (SourceAssertion.identity (D := D)
        (fun σ => φ σ ∧ c.get σ < N σ ∧ (↑(N σ - c.get σ) : Int) = z)) BODY
      (SourceAssertion.identity (D := D)
        (fun σ => φ σ ∧ c.get σ < N σ ∧ (↑(N σ - c.get σ) : Int) = z))) :
    SourceDerivTot (SourceAssertion.ofAssn (Assn.ofStateFam v₀ hv₀) φ)
      (countedProg c N BODY)
      (SourceAssertion.ofAssn (Assn.ofStateFam v₁ hv₁)
        φ) := by
  refine .conseq (SourceAssertion.entails_refl _)
    (countedStateChain c N φ hφ hN fam hnorm (hv₁ := hv₁) hins hzero hfull step hrank) ?_
  exact SourceAssertion.entails_ofAssn _ _ _ _ (fun _ h => h.1) (fun _ _ => le_rfl)

/-- A counted loop preserves its classical frame on the identity predicate,
using independent source body preservation for the integer rank. -/
theorem countedIdentity (c : CounterLens σT) (N : σT → ℕ) (φ : σT → Prop)
    (hφ : ∀ σ k, φ (c.set σ k) ↔ φ σ)
    (hN : ∀ σ k, N (c.set σ k) = N σ) (BODY : Prog σT D)
    (body : SourceDerivTot
      (SourceAssertion.identity (D := D) (fun σ => φ σ ∧ c.get σ < N σ)) BODY
      (SourceAssertion.identity (D := D) (fun σ => φ σ ∧ c.get σ < N σ)))
    (hrank : ∀ z : Int, SourceDerivTot
      (SourceAssertion.identity (D := D)
        (fun σ => φ σ ∧ c.get σ < N σ ∧ (↑(N σ - c.get σ) : Int) = z)) BODY
      (SourceAssertion.identity (D := D)
        (fun σ => φ σ ∧ c.get σ < N σ ∧ (↑(N σ - c.get σ) : Int) = z))) :
    SourceDerivTot (SourceAssertion.identity (D := D) φ) (countedProg c N BODY)
      (SourceAssertion.identity (D := D) φ) := by
  refine .conseq ?_ (countedWhile c N φ hφ hN Assn.one BODY ?_ hrank) ?_
  · exact SourceAssertion.entails_ofAssn _ _ _ _ (fun _ h => h) (fun _ _ => le_rfl)
  · exact body
  · exact SourceAssertion.entails_ofAssn _ _ _ _ (fun _ h => h.1) (fun _ _ => le_rfl)

end SourceDerivTot
end Qhl

#print axioms Qhl.SourceDerivTot.countedStateChain

#print axioms Qhl.SourceDerivTot.countedStateChainVar
#print axioms Qhl.SourceDerivTot.countedIdentity
