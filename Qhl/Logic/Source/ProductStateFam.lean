import Qhl.Logic.Source.BasicDerived
import Qhl.Logic.ProductStateFam

/-! # Source unitary rungs at classical-state-indexed product predicates -/
namespace Qhl
open Finset
variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)] {σT : Type*}

/-- A source pure-state rung with an explicit classical predicate. -/
theorem SourceDerivTot.countedRung_fam {k : ℕ} (rE : RegExpr σT L k)
    (gE : ∀ σ, UnitaryOp (TSpace D (rE σ))) {φ : σT → Prop}
    {v w : σT → HS D (univ : Finset L)}
    (hv : ∀ σ, ‖v σ‖ = 1) (hw : ∀ σ, ‖w σ‖ = 1)
    (hact : ∀ σ, φ σ → ∃ hinj : Function.Injective (rE σ),
      regLift ⟨rE σ, hinj⟩ (gE σ) (v σ) = w σ) :
    SourceDerivTot (SourceAssertion.ofAssn (Assn.ofStateFam v hv) φ)
      (.unitary k rE gE) (SourceAssertion.ofAssn (Assn.ofStateFam w hw) φ) := by
  apply SourceDerivTot.unitary_stateFam_guard rE gE v w hv hw φ
    (fun σ hσ => (hact σ hσ).choose)
  intro σ hσ
  exact (hact σ hσ).choose_spec

/-- Single-cell action at a classical-state-indexed product family. -/
theorem SourceDerivTot.countedRung_single_fam (rE : RegExpr σT L 1)
    (gE : ∀ σ, UnitaryOp (TSpace D (rE σ))) {φ : σT → Prop}
    (a : σT → L) (U : ∀ σ, UnitaryOp (EuclideanSpace ℂ (D (a σ))))
    {v w : σT → ∀ i, EuclideanSpace ℂ (D i)}
    (hv : ∀ σ i, ‖v σ i‖ = 1) (hw : ∀ σ i, ‖w σ i‖ = 1)
    (hlift : ∀ σ, φ σ → ∃ hinj : Function.Injective (rE σ),
      regLift ⟨rE σ, hinj⟩ (gE σ)
        = regLift (D := D) (Reg.single (a σ)) (singleGate D (a σ) (U σ)))
    (hstep : ∀ σ, φ σ → Function.update (v σ) (a σ)
        ((U σ : EuclideanSpace ℂ (D (a σ)) →ₗ[ℂ] EuclideanSpace ℂ (D (a σ)))
          (v σ (a σ))) = w σ) :
    SourceDerivTot
      (SourceAssertion.ofAssn (Assn.ofStateFam (fun σ => prodV D (W := univ) (v σ))
        (fun σ => norm_prodV_eq_one _ (hv σ))) φ) (.unitary 1 rE gE)
      (SourceAssertion.ofAssn (Assn.ofStateFam (fun σ => prodV D (W := univ) (w σ))
        (fun σ => norm_prodV_eq_one _ (hw σ))) φ) :=
  SourceDerivTot.countedRung_fam rE gE _ _ fun σ hσ => by
    obtain ⟨hinj, hK⟩ := hlift σ hσ
    exact ⟨hinj, by rw [hK, regLift_singleGate_prodV, hstep σ hσ]⟩

/-- Two-cell action at a classical-state-indexed product family. -/
theorem SourceDerivTot.countedRung_pair_fam (rE : RegExpr σT L 2)
    (gE : ∀ σ, UnitaryOp (TSpace D (rE σ))) {φ : σT → Prop}
    (a b : σT → L) (hab : ∀ σ, φ σ → a σ ≠ b σ)
    (G : ∀ σ, UnitaryOp (EuclideanSpace ℂ (D (a σ) × D (b σ))))
    {v w : σT → ∀ i, EuclideanSpace ℂ (D i)}
    (hv : ∀ σ i, ‖v σ i‖ = 1) (hw : ∀ σ i, ‖w σ i‖ = 1)
    (hlift : ∀ σ (hσ : φ σ), ∃ hinj : Function.Injective (rE σ),
      regLift ⟨rE σ, hinj⟩ (gE σ)
        = regLift (D := D) (Reg.pair (a σ) (b σ) (hab σ hσ))
            (pairGate (a σ) (b σ) (hab σ hσ) (G σ)))
    (hact : ∀ σ, φ σ →
      ∃ (u' : EuclideanSpace ℂ (D (a σ))) (v' : EuclideanSpace ℂ (D (b σ))),
        (G σ : EuclideanSpace ℂ (D (a σ) × D (b σ)) →ₗ[ℂ]
          EuclideanSpace ℂ (D (a σ) × D (b σ))) (vpair (v σ (a σ)) (v σ (b σ))) = vpair u' v' ∧
        Function.update (Function.update (v σ) (a σ) u') (b σ) v' = w σ) :
    SourceDerivTot
      (SourceAssertion.ofAssn (Assn.ofStateFam (fun σ => prodV D (W := univ) (v σ))
        (fun σ => norm_prodV_eq_one _ (hv σ))) φ) (.unitary 2 rE gE)
      (SourceAssertion.ofAssn (Assn.ofStateFam (fun σ => prodV D (W := univ) (w σ))
        (fun σ => norm_prodV_eq_one _ (hw σ))) φ) :=
  SourceDerivTot.countedRung_fam rE gE _ _ fun σ hσ => by
    obtain ⟨hinj, hK⟩ := hlift σ hσ
    obtain ⟨u', v', hG, hupd⟩ := hact σ hσ
    exact ⟨hinj, by
      rw [hK, regLift_pairGate_prodV (a σ) (b σ) (hab σ hσ) (G σ) (v σ) hG, hupd]⟩
end Qhl

#print axioms Qhl.SourceDerivTot.countedRung_fam
#print axioms Qhl.SourceDerivTot.countedRung_single_fam
#print axioms Qhl.SourceDerivTot.countedRung_pair_fam
