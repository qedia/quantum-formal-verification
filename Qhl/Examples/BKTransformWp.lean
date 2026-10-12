import Qhl.Examples.BKTransformTriple
import Qhl.Logic.Source.CountedWp
import Qhl.Logic.WpSuffixCongr

namespace Qhl.BKTransformWp
open Finset BravyiKitaev BKTransform
variable {L S : Type*} [Fintype L] [DecidableEq L]
variable (x : ℕ) (emb : QubitL (2 ^ x) ↪ L)

noncomputable def gateOp (l k : ℕ) (h : liveG x l k) :
    EndM (QubitCells L) (univ : Finset L) :=
  regLift ⟨fun j => emb (regE x (l,k) j),
    emb.injective.comp (distE_of_live x (σ := (l,k)) h)⟩ (gateE x (l,k))

theorem gateOp_unitary (l k : ℕ) (h : liveG x l k) :
    IsUnitary (gateOp x emb l k h) :=
  isUnitary_regLift (D := QubitCells L)
    ⟨fun j => emb (regE x (l,k) j),
      emb.injective.comp (distE_of_live x (σ := (l,k)) h)⟩ (gateE x (l,k))

noncomputable def stepWp (lev : S → ℕ) (k : ℕ) (A : Assn S (QubitCells L)) :
    Assn S (QubitCells L) where
  op σ := if h : liveG x (lev σ) k then
    LinearMap.adjoint (gateOp x emb (lev σ) k h) ∘ₗ A.op σ ∘ₗ
      gateOp x emb (lev σ) k h else A.op σ
  isEffect σ := by
    split
    · rename_i h
      exact isEffect_conj (A.isEffect σ) (le_of_eq (gateOp_unitary x emb (lev σ) k h).1)
    · exact A.isEffect σ

noncomputable def rung (lev : S → ℕ) (c : CounterLens S) : Prog S (QubitCells L) :=
  .ite (fun σ => decide (liveG x (lev σ) (c.get σ)))
    (.unitary 2 (fun σ j => emb (regE x (lev σ,c.get σ) j))
      (fun σ => gateE x (lev σ,c.get σ))) .skip

noncomputable def level (lev : S → ℕ) (c : CounterLens S) : Prog S (QubitCells L) :=
  countedProg c (fun _ => 2 ^ x) (rung x emb lev c)

theorem stepWp_op (lev : S → ℕ) (k : ℕ) (A : Assn S (QubitCells L)) (σ : S) :
    (stepWp x emb lev k A).op σ = if h : liveG x (lev σ) k then
      LinearMap.adjoint (gateOp x emb (lev σ) k h) ∘ₗ A.op σ ∘ₗ
        gateOp x emb (lev σ) k h else A.op σ := rfl

theorem stepWp_set (lev : S → ℕ) (c : CounterLens S)
    (hl : ∀ σ v, lev (c.set σ v) = lev σ) (k : ℕ) (A : Assn S (QubitCells L))
    (hA : ∀ σ v, A.op (c.set σ v) = A.op σ) (σ : S) (v : ℕ) :
    (stepWp x emb lev k A).op (c.set σ v) = (stepWp x emb lev k A).op σ := by
  simp only [stepWp_op, hl, hA]

theorem rungIdentity (lev : S → ℕ) (c : CounterLens S) (φ : S → Prop) :
    SourceDerivTot (SourceAssertion.identity (D := QubitCells L) φ)
      (rung x emb lev c) (SourceAssertion.identity φ) := by
  apply SourceDerivTot.cond
  · refine .conseq (SourceAssertion.entails_refl _)
      (SourceDerivTot.unitary_identity _ _ _
        (fun σ h => emb.injective.comp
          (distE_of_live x (σ := (lev σ,c.get σ)) (of_decide_eq_true h.2)))) ?_
    exact SourceAssertion.entails_ofAssn _ _ _ _ (fun _ h => h.1) (fun _ _ => le_rfl)
  · refine .conseq ?_ (.skip _) (SourceAssertion.entails_refl _)
    exact SourceAssertion.entails_ofAssn _ _ _ _ (fun _ h => h.1) (fun _ _ => le_rfl)

theorem levelIdentity (lev : S → ℕ) (c : CounterLens S) (φ : S → Prop)
    (hφ : ∀ σ v, φ (c.set σ v) ↔ φ σ) :
    SourceDerivTot (SourceAssertion.identity (D := QubitCells L) φ)
      (level x emb lev c) (SourceAssertion.identity φ) := by
  apply SourceDerivTot.countedIdentity c (fun _ => 2 ^ x) φ hφ (fun _ _ => rfl)
  · exact rungIdentity x emb lev c _
  · intro z; exact rungIdentity x emb lev c _

theorem levelDeriv (lev : S → ℕ) (c : CounterLens S) (φ : S → Prop)
    (hl : ∀ σ v, lev (c.set σ v) = lev σ)
    (hφ : ∀ σ v, φ (c.set σ v) ↔ φ σ)
    (Y : Assn S (QubitCells L)) (hY : ∀ σ v, Y.op (c.set σ v) = Y.op σ) :
    SourceDerivTot
      (SourceAssertion.ofAssn (wpSuffix (stepWp x emb lev) (2 ^ x) Y 0) φ)
      (level x emb lev c) (SourceAssertion.ofAssn Y φ) := by
  refine .conseq (SourceAssertion.entails_refl _)
    (SourceDerivTot.countedWpBody c (2 ^ x) φ (stepWp x emb lev) Y _ hφ
      (stepWp_set x emb lev c hl) hY ?_ ?_) ?_
  · apply SourceDerivTot.cond
    · apply SourceDerivTot.unitary_ofAssn _ _ _ _ _ _ (fun _ h => h.1)
        (fun σ h => emb.injective.comp
          (distE_of_live x (σ := (lev σ,c.get σ)) (of_decide_eq_true h.2)))
      intro σ h
      have hd := emb.injective.comp (distE_of_live x (σ := (lev σ,c.get σ)) (of_decide_eq_true h.2))
      apply le_of_eq
      change (wpSuffix (stepWp x emb lev) (2 ^ x) Y (c.get σ)).op σ = _
      rw [wpSuffix_of_lt h.1.2, stepWp_op]
      rw [dif_pos (of_decide_eq_true h.2)]
      exact (Assn.unitaryPre_op_of_dist (D := QubitCells L)
        (Assn.ofFam c.get (fun k => wpSuffix (stepWp x emb lev) (2 ^ x) Y (k+1)))
        (fun τ => emb ∘ regE x (lev τ,c.get τ))
        (fun τ => gateE x (lev τ,c.get τ)) hd).symm
    · refine .conseq ?_ (.skip _) (SourceAssertion.entails_refl _)
      apply SourceAssertion.entails_ofAssn
      · intro _ h; exact h.1
      · intro σ h
        apply le_of_eq
        change (wpSuffix (stepWp x emb lev) (2 ^ x) Y (c.get σ)).op σ = _
        rw [wpSuffix_of_lt h.1.2, stepWp_op,
          dif_neg (of_decide_eq_false h.2), Assn.ofFam_op]
  · intro z; exact rungIdentity x emb lev c _
  · exact SourceAssertion.entails_ofAssn _ _ _ _ (fun _ h => h.1) (fun _ _ => le_rfl)

noncomputable def levelWp (l : ℕ) (Y : Assn S (QubitCells L)) : Assn S (QubitCells L) :=
  wpSuffix (stepWp x emb (fun _ => l)) (2 ^ x) Y 0

noncomputable def pre (Y : Assn S (QubitCells L)) : Assn S (QubitCells L) :=
  wpSuffix (levelWp x emb) x Y 0

noncomputable def prog (cl ck : CounterLens S) : Prog S (QubitCells L) :=
  countedProg cl (fun _ => x) (level x emb cl.get ck)

theorem levelWp_set (c : CounterLens S) (l : ℕ) (A : Assn S (QubitCells L))
    (hA : ∀ σ v, A.op (c.set σ v) = A.op σ) (σ : S) (v : ℕ) :
    (levelWp x emb l A).op (c.set σ v) = (levelWp x emb l A).op σ :=
  wpSuffix_op_set _ A c (stepWp_set x emb _ c (fun _ _ => rfl)) hA 0 σ v

theorem sourceDeriv (cl ck : CounterLens S)
    (hlk : ∀ σ v, cl.get (ck.set σ v) = cl.get σ)
    (φ : S → Prop) (hφl : ∀ σ v, φ (cl.set σ v) ↔ φ σ)
    (hφk : ∀ σ v, φ (ck.set σ v) ↔ φ σ)
    (Y : Assn S (QubitCells L))
    (hYl : ∀ σ v, Y.op (cl.set σ v) = Y.op σ)
    (hYk : ∀ σ v, Y.op (ck.set σ v) = Y.op σ) :
    SourceDerivTot (SourceAssertion.ofAssn (pre x emb Y) φ)
      (prog x emb cl ck) (SourceAssertion.ofAssn Y φ) := by
  let F := wpSuffix (levelWp x emb) x Y
  let Z := Assn.ofFam cl.get (fun l => F (l+1))
  have hZ : ∀ σ v, Z.op (ck.set σ v) = Z.op σ := by
    intro σ v
    simp only [Z, Assn.ofFam_op, hlk]
    exact wpSuffix_op_set _ Y ck (levelWp_set x emb ck) hYk _ σ v
  refine .conseq (SourceAssertion.entails_refl _)
    (SourceDerivTot.countedWpBody cl x φ (levelWp x emb) Y _ hφl
      (levelWp_set x emb cl) hYl ?_ ?_) ?_
  · refine .conseq ?_ (levelDeriv x emb cl.get ck
      (fun σ => φ σ ∧ cl.get σ < x) hlk
      (fun σ v => by rw [hlk, hφk]) Z hZ) (SourceAssertion.entails_refl _)
    apply SourceAssertion.entails_ofAssn
    · intro _ h; exact h
    · intro σ hσ
      apply le_of_eq
      change (F (cl.get σ)).op σ = _
      dsimp [F]
      rw [wpSuffix_of_lt hσ.2]
      unfold levelWp
      apply wpSuffix_op_congr
      · intro j _ A B hAB
        simp only [stepWp_op, hAB]
      · rfl
  · intro z
    exact levelIdentity x emb cl.get ck _ (fun σ v => by rw [hlk, hφk])
  · exact SourceAssertion.entails_ofAssn _ _ _ _ (fun _ h => h.1) (fun _ _ => le_rfl)

end Qhl.BKTransformWp


#print axioms Qhl.BKTransformWp.sourceDeriv
