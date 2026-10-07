import Qhl.Logic.CountedStateChain
import Qhl.Logic.CountedProdChain

namespace Qhl
open Finset
variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)] {σT : Type*}

/-- Reading a product-assertion family at the current classical index. -/
theorem Assn.ofFam_prodA (g : σT → ℕ)
    (fam : ℕ → ∀ i, EuclideanSpace ℂ (D i)) (hnorm : ∀ m i, ‖fam m i‖ = 1) :
    Assn.ofFam g (fun m => prodA D (fam m) (hnorm m)) =
      Assn.ofStateFam (fun σ => prodV D (W := univ) (fam (g σ)))
        (fun σ => norm_prodV_eq_one _ (hnorm (g σ))) := by
  ext σ
  rfl

/-- Single-cell action at a classical-state-indexed product family. -/
theorem DerivTot.countedRung_single_fam (rE : RegExpr σT L 1)
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
    DerivTot
      ((Assn.ofStateFam (fun σ => prodV D (W := univ) (v σ))
        (fun σ => norm_prodV_eq_one _ (hv σ))).mask φ) (.unitary 1 rE gE)
      ((Assn.ofStateFam (fun σ => prodV D (W := univ) (w σ))
        (fun σ => norm_prodV_eq_one _ (hw σ))).mask φ) :=
  DerivTot.countedRung_fam rE gE _ _ fun σ hσ => by
    obtain ⟨hinj, hK⟩ := hlift σ hσ
    exact ⟨hinj, by rw [hK, regLift_singleGate_prodV, hstep σ hσ]⟩

/-- Two-cell action at a classical-state-indexed product family. -/
theorem DerivTot.countedRung_pair_fam (rE : RegExpr σT L 2)
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
    DerivTot
      ((Assn.ofStateFam (fun σ => prodV D (W := univ) (v σ))
        (fun σ => norm_prodV_eq_one _ (hv σ))).mask φ) (.unitary 2 rE gE)
      ((Assn.ofStateFam (fun σ => prodV D (W := univ) (w σ))
        (fun σ => norm_prodV_eq_one _ (hw σ))).mask φ) :=
  DerivTot.countedRung_fam rE gE _ _ fun σ hσ => by
    obtain ⟨hinj, hK⟩ := hlift σ hσ
    obtain ⟨u', v', hG, hupd⟩ := hact σ hσ
    exact ⟨hinj, by
      rw [hK, regLift_pairGate_prodV (a σ) (b σ) (hab σ hσ) (G σ) (v σ) hG, hupd]⟩
end Qhl
