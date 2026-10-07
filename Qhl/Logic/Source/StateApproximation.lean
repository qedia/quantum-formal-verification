import Qhl.Logic.Source.CountedStateChain
import Qhl.Logic.Source.ProductStateFam
import Qhl.Logic.StateApproximation

/-! # Scaled source state-family loops and approximate endpoint consequence -/
namespace Qhl
open Finset
variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)] {σT : Type*}
namespace SourceDerivTot

/-- A pure-state unitary rung with a store-dependent scalar coefficient. -/
theorem countedRung_fam_scaled {k : ℕ} (rE : RegExpr σT L k)
    (gE : ∀ σ, UnitaryOp (TSpace D (rE σ))) {φ : σT → Prop}
    (a : σT → ℝ) (ha0 : ∀ σ, 0 ≤ a σ) (ha1 : ∀ σ, a σ ≤ 1)
    {v w : σT → HS D (univ : Finset L)}
    (hv : ∀ σ, ‖v σ‖ = 1) (hw : ∀ σ, ‖w σ‖ = 1)
    (hact : ∀ σ, φ σ → ∃ hinj : Function.Injective (rE σ),
      regLift ⟨rE σ, hinj⟩ (gE σ) (v σ) = w σ) :
    SourceDerivTot
      (SourceAssertion.ofAssn ((Assn.ofStateFam v hv).scaledBy a ha0 ha1) φ)
      (.unitary k rE gE)
      (SourceAssertion.ofAssn ((Assn.ofStateFam w hw).scaledBy a ha0 ha1) φ) := by
  apply unitary_ofAssn _ _ _ _ _ _ (fun _ h => h)
    (fun σ h => (hact σ h).choose)
  intro σ hσ
  rw [← Assn.scaledBy_unitaryPre, Assn.scaledBy_op, Assn.scaledBy_op]
  apply real_smul_operator_mono _ (ha0 σ)
  obtain ⟨hd, hU⟩ := hact σ hσ
  apply le_of_eq
  rw [Assn.unitaryPre_op_of_dist _ _ _ hd, Assn.ofStateFam_op, Assn.ofStateFam_op,
    adjoint_conj_outerLM_state ⟨rE σ, hd⟩ (gE σ) hU]

theorem countedStateChain_scaled (c : CounterLens σT) (N : σT → ℕ) (φ : σT → Prop)
    (hφ : ∀ σ k, φ (c.set σ k) ↔ φ σ)
    (hN : ∀ σ k, N (c.set σ k) = N σ)
    (a : σT → ℝ) (ha0 : ∀ σ, 0 ≤ a σ) (ha1 : ∀ σ, a σ ≤ 1)
    (ha : ∀ σ k, a (c.set σ k) = a σ)
    (fam : ℕ → σT → HS D (univ : Finset L)) (hnorm : ∀ m σ, ‖fam m σ‖ = 1)
    {v₀ v₁ : σT → HS D (univ : Finset L)}
    {hv₀ : ∀ σ, ‖v₀ σ‖ = 1} {hv₁ : ∀ σ, ‖v₁ σ‖ = 1}
    (hins : ∀ m σ k, fam m (c.set σ k) = fam m σ)
    (hzero : ∀ σ, φ σ → fam 0 σ = v₀ σ)
    (hfull : ∀ σ, φ σ → fam (N σ) σ = v₁ σ)
    {BODY : Prog σT D}
    (step : SourceDerivTot
      (SourceAssertion.ofAssn
        ((Assn.ofStateFam (fun σ => fam (c.get σ) σ) (fun σ => hnorm _ σ)).scaledBy a ha0 ha1)
        (fun σ => φ σ ∧ c.get σ < N σ)) BODY
      (SourceAssertion.ofAssn
        ((Assn.ofStateFam (fun σ => fam (c.get σ + 1) σ) (fun σ => hnorm _ σ)).scaledBy a ha0 ha1)
        (fun σ => φ σ ∧ c.get σ < N σ)))
    (hrank : ∀ z : Int, SourceDerivTot
      (SourceAssertion.identity (D := D)
        (fun σ => φ σ ∧ c.get σ < N σ ∧ (↑(N σ - c.get σ) : Int) = z)) BODY
      (SourceAssertion.identity (D := D)
        (fun σ => φ σ ∧ c.get σ < N σ ∧ (↑(N σ - c.get σ) : Int) = z))) :
    SourceDerivTot (SourceAssertion.ofAssn ((Assn.ofStateFam v₀ hv₀).scaledBy a ha0 ha1) φ)
      (countedProg c N BODY)
      (SourceAssertion.ofAssn ((Assn.ofStateFam v₁ hv₁).scaledBy a ha0 ha1)
        φ) := by
  let A := (Assn.ofStateFam (fun σ => fam (c.get σ) σ) (fun σ => hnorm _ σ)).scaledBy a ha0 ha1
  have body : SourceDerivTot (SourceAssertion.ofAssn A (fun σ => φ σ ∧ c.get σ < N σ))
      BODY (SourceAssertion.ofAssn (A.comp (fun σ => c.set σ (c.get σ + 1)))
        (fun σ => φ σ ∧ c.get σ < N σ)) := by
    refine .conseq (SourceAssertion.entails_refl _) step ?_
    apply SourceAssertion.entails_ofAssn
    · intro _ h; exact h
    · intro σ _
      apply le_of_eq
      simp only [A, Assn.comp_op, Assn.scaledBy_op, Assn.ofStateFam_op,
        c.get_set, hins, ha]
  refine .conseq ?_ (countedWhile c N φ hφ hN A BODY body hrank) ?_
  · apply SourceAssertion.entails_ofAssn
    · intro _ h; exact h
    · intro σ hσ
      apply le_of_eq
      simp only [A, Assn.comp_op, Assn.scaledBy_op, Assn.ofStateFam_op,
        c.get_set, hins, ha, hzero σ hσ]
  · apply SourceAssertion.entails_ofAssn
    · intro _ h; exact h.1
    · intro σ hσ
      apply le_of_eq
      simp only [A, Assn.scaledBy_op, Assn.ofStateFam_op, hσ.2, hfull σ hσ.1]

end SourceDerivTot
end Qhl

#print axioms Qhl.SourceDerivTot.countedStateChain_scaled
