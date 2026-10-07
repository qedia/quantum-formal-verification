import Qhl.Logic.Source.CountedWhile
import Qhl.Logic.Source.ProductStateFam
import Qhl.Logic.Subroutine

/-! Source derivations for pure-state families placed in a larger qubit register. -/
namespace Qhl.SourceDerivTot
open Finset
variable {L₁ L₂ : Type*} [Fintype L₁] [DecidableEq L₁] [Fintype L₂] [DecidableEq L₂]
variable (emb : L₁ ↪ L₂) {σT : Type*}
variable (R : EndM (QubitCells L₂) (univ \ embRange emb)) (hR : IsEffect R)

noncomputable def framedFam (v : σT → HS (QubitCells L₁) (univ : Finset L₁))
    (hv : ∀ σ, ‖v σ‖ = 1) : Assn σT (QubitCells L₂) :=
  (Assn.ofStateFam v hv).embFrame (emb := emb) R hR

/-- A placed gate uses the original small-world action and an unchanged frame effect. -/
theorem framedRung {k : ℕ} (r : RegExpr σT L₁ k)
    (U : ∀ σ, UnitaryOp (TSpace (QubitCells L₁) (r σ))) {φ : σT → Prop}
    {v w : σT → HS (QubitCells L₁) (univ : Finset L₁)}
    (hv : ∀ σ, ‖v σ‖ = 1) (hw : ∀ σ, ‖w σ‖ = 1)
    (hact : ∀ σ, φ σ → ∃ hd : Function.Injective (r σ),
      regLift ⟨r σ, hd⟩ (U σ) (v σ) = w σ) :
    SourceDerivTot (SourceAssertion.ofAssn (framedFam emb R hR v hv) φ)
      (.unitary k (fun σ j => emb (r σ j)) U)
      (SourceAssertion.ofAssn (framedFam emb R hR w hw) φ) := by
  apply SourceDerivTot.unitary_ofAssn _ _ _ _ _ _ (fun _ h => h)
    (fun σ h => (emb).injective.comp (hact σ h).choose)
  intro σ hσ
  apply le_of_eq
  change ((Assn.ofStateFam v hv).embFrame R hR).op σ =
    (((Assn.ofStateFam w hw).embFrame R hR).unitaryPre _ U).op σ
  calc
    _ = (((Assn.ofStateFam w hw).unitaryPre r U).embFrame
        (emb := emb) R hR).op σ := by
      rw [Assn.embFrame_op, Assn.embFrame_op]
      obtain ⟨hd, hU⟩ := hact σ hσ
      rw [Assn.unitaryPre_op_of_dist _ _ _ hd, Assn.ofStateFam_op, Assn.ofStateFam_op,
        adjoint_conj_outerLM_state ⟨r σ, hd⟩ (U σ) hU]
    _ = _ := congrArg (fun A => A.op σ)
      (Assn.embFrame_unitaryPre (emb := emb) (R := R) (hR := hR)
        (Assn.ofStateFam w hw) r U)

/-- The placed unitary preserves a classical identity predicate independently of the frame. -/
theorem framedIdentity {k : ℕ} (r : RegExpr σT L₁ k)
    (U : ∀ σ, UnitaryOp (TSpace (QubitCells L₁) (r σ))) (φ : σT → Prop)
    (hd : ∀ σ, φ σ → Function.Injective (r σ)) :
    SourceDerivTot (SourceAssertion.identity (D := QubitCells L₂) φ)
      (.unitary k (fun σ j => emb (r σ j)) U)
      (SourceAssertion.identity (D := QubitCells L₂) φ) :=
  SourceDerivTot.unitary_identity _ _ _ (fun σ h => (emb).injective.comp (hd σ h))

theorem framedCounted (c : CounterLens σT) (N : σT → ℕ) (φ : σT → Prop)
    (hφ : ∀ σ k, φ (c.set σ k) ↔ φ σ)
    (hN : ∀ σ k, N (c.set σ k) = N σ)
    (fam : ℕ → σT → HS (QubitCells L₁) (univ : Finset L₁)) (hnorm : ∀ m σ, ‖fam m σ‖ = 1)
    {v₀ v₁ : σT → HS (QubitCells L₁) (univ : Finset L₁)}
    {hv₀ : ∀ σ, ‖v₀ σ‖ = 1} {hv₁ : ∀ σ, ‖v₁ σ‖ = 1}
    (hins : ∀ m σ k, fam m (c.set σ k) = fam m σ)
    (hzero : ∀ σ, φ σ → fam 0 σ = v₀ σ)
    (hfull : ∀ σ, φ σ → fam (N σ) σ = v₁ σ)
    {BODY : Prog σT (QubitCells L₂)}
    (step : SourceDerivTot
      (SourceAssertion.ofAssn
        (framedFam emb R hR (fun σ => fam (c.get σ) σ) (fun σ => hnorm _ σ))
        (fun σ => φ σ ∧ c.get σ < N σ)) BODY
      (SourceAssertion.ofAssn
        (framedFam emb R hR (fun σ => fam (c.get σ + 1) σ) (fun σ => hnorm _ σ))
        (fun σ => φ σ ∧ c.get σ < N σ)))
    (hrank : ∀ z : Int, SourceDerivTot
      (SourceAssertion.identity (D := QubitCells L₂)
        (fun σ => φ σ ∧ c.get σ < N σ ∧ (↑(N σ - c.get σ) : Int) = z)) BODY
      (SourceAssertion.identity (D := QubitCells L₂)
        (fun σ => φ σ ∧ c.get σ < N σ ∧ (↑(N σ - c.get σ) : Int) = z))) :
    SourceDerivTot (SourceAssertion.ofAssn (framedFam emb R hR v₀ hv₀) φ)
      (countedProg c N BODY)
      (SourceAssertion.ofAssn (framedFam emb R hR v₁ hv₁)
        φ) := by
  let A := framedFam emb R hR (fun σ => fam (c.get σ) σ) (fun σ => hnorm _ σ)
  have body : SourceDerivTot (SourceAssertion.ofAssn A (fun σ => φ σ ∧ c.get σ < N σ))
      BODY (SourceAssertion.ofAssn (A.comp (fun σ => c.set σ (c.get σ + 1)))
        (fun σ => φ σ ∧ c.get σ < N σ)) := by
    refine .conseq (SourceAssertion.entails_refl _) step ?_
    apply SourceAssertion.entails_ofAssn
    · intro _ h; exact h
    · intro σ _
      apply le_of_eq
      simp only [A, framedFam, Assn.comp_op, Assn.embFrame_op, Assn.ofStateFam_op,
        c.get_set, hins]
  refine .conseq ?_ (SourceDerivTot.countedWhile c N φ hφ hN A BODY body hrank) ?_
  · apply SourceAssertion.entails_ofAssn
    · intro _ h; exact h
    · intro σ hσ
      apply le_of_eq
      simp only [A, framedFam, Assn.comp_op, Assn.embFrame_op, Assn.ofStateFam_op,
        c.get_set, hins, hzero σ hσ]
  · apply SourceAssertion.entails_ofAssn
    · intro _ h; exact h.1
    · intro σ hσ
      apply le_of_eq
      simp only [A, framedFam, Assn.embFrame_op, Assn.ofStateFam_op, hσ.2, hfull σ hσ.1]

/-- Single-cell action at a classical-state-indexed product family. -/
theorem framedSingle (rE : RegExpr σT L₁ 1)
    (gE : ∀ σ, UnitaryOp (TSpace (QubitCells L₁) (rE σ))) {φ : σT → Prop}
    (a : σT → L₁) (U : ∀ σ, UnitaryOp (EuclideanSpace ℂ (QubitCells L₁ (a σ))))
    {v w : σT → ∀ i, EuclideanSpace ℂ (QubitCells L₁ i)}
    (hv : ∀ σ i, ‖v σ i‖ = 1) (hw : ∀ σ i, ‖w σ i‖ = 1)
    (hlift : ∀ σ, φ σ → ∃ hinj : Function.Injective (rE σ),
      regLift ⟨rE σ, hinj⟩ (gE σ)
        = regLift (D := QubitCells L₁) (Reg.single (a σ)) (singleGate (QubitCells L₁) (a σ) (U σ)))
    (hstep : ∀ σ, φ σ → Function.update (v σ) (a σ)
        ((U σ : EuclideanSpace ℂ (QubitCells L₁ (a σ)) →ₗ[ℂ] EuclideanSpace ℂ (QubitCells L₁ (a σ)))
          (v σ (a σ))) = w σ) :
    SourceDerivTot
      (SourceAssertion.ofAssn (framedFam emb R hR (fun σ => prodV (QubitCells L₁) (W := univ) (v σ))
        (fun σ => norm_prodV_eq_one _ (hv σ))) φ) (.unitary 1 (fun σ j => emb (rE σ j)) gE)
      (SourceAssertion.ofAssn (framedFam emb R hR (fun σ => prodV (QubitCells L₁) (W := univ) (w σ))
        (fun σ => norm_prodV_eq_one _ (hw σ))) φ) :=
  framedRung emb R hR rE gE _ _ fun σ hσ => by
    obtain ⟨hinj, hK⟩ := hlift σ hσ
    exact ⟨hinj, by rw [hK, regLift_singleGate_prodV, hstep σ hσ]⟩

/-- Two-cell action at a classical-state-indexed product family. -/
theorem framedPair (rE : RegExpr σT L₁ 2)
    (gE : ∀ σ, UnitaryOp (TSpace (QubitCells L₁) (rE σ))) {φ : σT → Prop}
    (a b : σT → L₁) (hab : ∀ σ, φ σ → a σ ≠ b σ)
    (G : ∀ σ, UnitaryOp (EuclideanSpace ℂ (QubitCells L₁ (a σ) × QubitCells L₁ (b σ))))
    {v w : σT → ∀ i, EuclideanSpace ℂ (QubitCells L₁ i)}
    (hv : ∀ σ i, ‖v σ i‖ = 1) (hw : ∀ σ i, ‖w σ i‖ = 1)
    (hlift : ∀ σ (hσ : φ σ), ∃ hinj : Function.Injective (rE σ),
      regLift ⟨rE σ, hinj⟩ (gE σ)
        = regLift (D := QubitCells L₁) (Reg.pair (a σ) (b σ) (hab σ hσ))
            (pairGate (a σ) (b σ) (hab σ hσ) (G σ)))
    (hact : ∀ σ, φ σ →
      ∃ (u' : EuclideanSpace ℂ (QubitCells L₁ (a σ))) (v' : EuclideanSpace ℂ (QubitCells L₁ (b σ))),
        (G σ : EuclideanSpace ℂ (QubitCells L₁ (a σ) × QubitCells L₁ (b σ)) →ₗ[ℂ]
          EuclideanSpace ℂ (QubitCells L₁ (a σ) × QubitCells L₁ (b σ)))
            (vpair (v σ (a σ)) (v σ (b σ))) =
        vpair u' v' ∧
        Function.update (Function.update (v σ) (a σ) u') (b σ) v' = w σ) :
    SourceDerivTot
      (SourceAssertion.ofAssn (framedFam emb R hR (fun σ => prodV (QubitCells L₁) (W := univ) (v σ))
        (fun σ => norm_prodV_eq_one _ (hv σ))) φ) (.unitary 2 (fun σ j => emb (rE σ j)) gE)
      (SourceAssertion.ofAssn (framedFam emb R hR (fun σ => prodV (QubitCells L₁) (W := univ) (w σ))
        (fun σ => norm_prodV_eq_one _ (hw σ))) φ) :=
  framedRung emb R hR rE gE _ _ fun σ hσ => by
    obtain ⟨hinj, hK⟩ := hlift σ hσ
    obtain ⟨u', v', hG, hupd⟩ := hact σ hσ
    exact ⟨hinj, by
      rw [hK, regLift_pairGate_prodV (a σ) (b σ) (hab σ hσ) (G σ) (v σ) hG, hupd]⟩

end Qhl.SourceDerivTot
