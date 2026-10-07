import Qhl.Logic.Source.Rules

/-! # Semantic soundness of source derivations -/

namespace Qhl

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)] {σT : Type*}

namespace SourceAssertion

/-- Source initialization agrees with the semantic initialization precondition. -/
theorem initPreSource_toAssn (A : SourceAssertion σT D) (S : σT → Finset L) :
    (A.initPreSource S).toAssn = A.toAssn.initPre S := by
  apply Assn.ext
  funext σ
  by_cases h : A.classical σ ∧ A.defined σ
  · change ((A.quantum.initPre S).mask
        (fun τ => A.classical τ ∧ A.defined τ)).op σ =
        ((A.quantum.mask (fun τ => A.classical τ ∧ A.defined τ)).initPre S).op σ
    simp only [Assn.initPre_op,
      Assn.mask_op_of_pos (φ := fun τ => A.classical τ ∧ A.defined τ) h]
  · change ((A.quantum.initPre S).mask
        (fun τ => A.classical τ ∧ A.defined τ)).op σ =
        ((A.quantum.mask (fun τ => A.classical τ ∧ A.defined τ)).initPre S).op σ
    simp only [Assn.initPre_op,
      Assn.mask_op_of_neg (φ := fun τ => A.classical τ ∧ A.defined τ) h,
      map_zero]

/-- Source unitary agrees with the semantic unitary precondition. -/
theorem unitaryPreSource_toAssn (A : SourceAssertion σT D) {k : ℕ}
    (r : RegExpr σT L k) (U : ∀ σ, UnitaryOp (TSpace D (r σ))) :
    (A.unitaryPreSource r U).toAssn = A.toAssn.unitaryPre r U := by
  apply Assn.ext
  funext σ
  by_cases hc : A.classical σ
  · by_cases hd : A.defined σ
    · by_cases hi : Function.Injective (r σ)
      · simp [toAssn, unitaryPreSource, Assn.unitaryPre, Assn.mask, hc, hd, hi]
      · simp [toAssn, unitaryPreSource, Assn.unitaryPre, Assn.mask, hc, hd, hi]
    · simp [toAssn, unitaryPreSource, Assn.unitaryPre, Assn.mask, hc, hd]
  · simp [toAssn, unitaryPreSource, Assn.unitaryPre, Assn.mask, hc]

/-- Source conditionals agree with the semantic guard. -/
theorem cond_toAssn (A : SourceAssertion σT D) (b : σT → Bool) :
    Assn.guard b
      (A.withClassical fun σ => A.classical σ ∧ b σ = true).toAssn
      (A.withClassical fun σ => A.classical σ ∧ b σ = false).toAssn =
      A.toAssn := by
  classical
  apply Assn.ext
  funext σ
  cases hb : b σ
  · rw [Assn.guard_op_of_false hb]
    simp only [toAssn, withClassical, Assn.mask]
    simp [hb]
  · rw [Assn.guard_op_of_true hb]
    simp only [toAssn, withClassical, Assn.mask]
    simp [hb]

end SourceAssertion

/-- Every source partial derivation is semantically valid. -/
theorem SourceDerivPar.sound {A B : SourceAssertion σT D} {P : Prog σT D}
    (h : SourceDerivPar A P B) : validPar A.toAssn P B.toAssn := by
  induction h with
  | skip A => exact (validTot_skip A.toAssn).validPar
  | assign f A =>
      rw [SourceAssertion.toAssn_subst]
      exact (validTot_assign f A.toAssn).validPar
  | initProg S A =>
      rw [SourceAssertion.initPreSource_toAssn]
      exact (validTot_init S A.toAssn).validPar
  | unitary r U A =>
      rw [SourceAssertion.unitaryPreSource_toAssn]
      exact (validTot_unitary r U A.toAssn).validPar
  | measureAll r M x A =>
      exact (DerivPar.conseq (SourceAssertion.measureAllPreSource_le A r M x.set)
        (.measure r M x.set A.toAssn) (fun _ => le_rfl)).sound
  | mask b h ih =>
      rw [SourceAssertion.quantumMask_toAssn] at ih
      exact ih
  | seq h₁ h₂ ih₁ ih₂ => exact validPar_seq ih₁ ih₂
  | cond b h₁ h₀ ih₁ ih₀ =>
      rw [← SourceAssertion.cond_toAssn]
      exact validPar_cond ih₁ ih₀
  | whileLoop b h ih =>
      rw [SourceAssertion.guard_toAssn, SourceAssertion.toAssn_eq_nested_mask] at ih
      rw [SourceAssertion.toAssn_eq_nested_mask, SourceAssertion.exit_toAssn]
      exact validPar_while ih
  | conseq hA h hB ih =>
      exact validPar_sourceConseq hA ih hB
  | accum2 φ ψ A B K hK P hframe hdom hcomp ih =>
      exact SourceAssertion.validPar_kraus φ ψ A B K hK P hframe
        (fun σ hψ i j => ⟨fun _ => hdom σ hψ j, fun _ => hdom σ hψ i⟩) ih
  | accum1 φ ψ A B K J hK hJ P hframe hexcl hdom hcomp ih =>
      exact SourceAssertion.validPar_accumOne φ ψ A B K J hK hJ P
        hframe hexcl hdom ih
  | accum2Domain φ ψ A B K hK P hframe d hd hdom hcomp ih =>
      exact SourceAssertion.validPar_kraus_onDomain φ ψ A B K hK P hframe d hd
        (fun σ hψ i j => ⟨fun _ => hdom σ hψ j, fun _ => hdom σ hψ i⟩) ih
  | accum1Domain φ ψ A B K J hK hJ P hframe d hd hexcl hdom hcomp ih =>
      exact SourceAssertion.validPar_accumOne_onDomain φ ψ A B K J hK hJ P hframe
        d hd hexcl hdom ih
  | convex1 φ ψ A B p hp P hexcl hcomp ih =>
      exact SourceAssertion.validPar_convex1 φ ψ A B p hp P hexcl ih
  | convex2 φ ψ A B p hp P hdom hcomp ih =>
      exact SourceAssertion.validPar_convex2 φ ψ A B p hp P hdom ih

/-- Every source total derivation is semantically valid. -/
theorem SourceDerivTot.sound {A B : SourceAssertion σT D} {P : Prog σT D}
    (h : SourceDerivTot A P B) : validTot A.toAssn P B.toAssn := by
  induction h with
  | skip A => exact validTot_skip A.toAssn
  | assign f A =>
      rw [SourceAssertion.toAssn_subst]
      exact validTot_assign f A.toAssn
  | initProg S A =>
      rw [SourceAssertion.initPreSource_toAssn]
      exact validTot_init S A.toAssn
  | unitary r U A =>
      rw [SourceAssertion.unitaryPreSource_toAssn]
      exact validTot_unitary r U A.toAssn
  | measureAll r M x A =>
      exact (DerivTot.conseq (SourceAssertion.measureAllPreSource_le A r M x.set)
        (.measure r M x.set A.toAssn) (fun _ => le_rfl)).sound
  | mask b h ih =>
      rw [SourceAssertion.quantumMask_toAssn] at ih
      exact ih
  | seq h₁ h₂ ih₁ ih₂ => exact validTot_seq ih₁ ih₂
  | cond b h₁ h₀ ih₁ ih₀ =>
      rw [← SourceAssertion.cond_toAssn]
      exact validTot_cond ih₁ ih₀
  | whileLoop b t hbound hInv hRank ihInv ihRank =>
      rw [SourceAssertion.guard_toAssn, SourceAssertion.toAssn_eq_nested_mask] at ihInv
      rw [SourceAssertion.toAssn_eq_nested_mask, SourceAssertion.exit_toAssn]
      exact validTot_while_source t hbound ihInv (fun z => by
        simpa only [SourceAssertion.identity_toAssn] using ihRank z)
  | whileLoopGhost b t hbound hInv hRank ihInv ihRank =>
      exact validTot_sourceWhile_ghost t hbound ihInv ihRank
  | conseq hA h hB ih =>
      exact validTot_sourceConseq hA ih hB
  | accum2 φ ψ A B K hK P hframe hdom hcomp ih =>
      exact SourceAssertion.validTot_kraus φ ψ A B K hK P hframe
        (fun σ hψ i j => ⟨fun _ => hdom σ hψ j, fun _ => hdom σ hψ i⟩) ih
  | accum1 φ ψ A B K J hK hJ P hframe hexcl hdom hcomp ih =>
      exact SourceAssertion.validTot_accumOne φ ψ A B K J hK hJ P
        hframe hexcl hdom ih
  | accum2Domain φ ψ A B K hK P hframe d hd hdom hcomp ih =>
      exact SourceAssertion.validTot_kraus_onDomain φ ψ A B K hK P hframe d hd
        (fun σ hψ i j => ⟨fun _ => hdom σ hψ j, fun _ => hdom σ hψ i⟩) ih
  | accum1Domain φ ψ A B K J hK hJ P hframe d hd hexcl hdom hcomp ih =>
      exact SourceAssertion.validTot_accumOne_onDomain φ ψ A B K J hK hJ P hframe
        d hd hexcl hdom ih
  | convex1 φ ψ A B p hp P hexcl hcomp ih =>
      exact SourceAssertion.validTot_convex1 φ ψ A B p hp P hexcl ih
  | convex2 φ ψ A B p hp P hdom hcomp ih =>
      exact SourceAssertion.validTot_convex2 φ ψ A B p hp P hdom ih

/-- The source derivation rank premises imply validity of the genuine ghost program. -/
theorem SourceDerivTot.rankGhost_sound (A : SourceAssertion σT D)
    (b : σT → Bool) (t : σT → Int) (P : Prog σT D)
    (hRank : ∀ z : Int, SourceDerivTot
      (SourceAssertion.identity (D := D)
        (fun σ => A.classical σ ∧ b σ = true ∧ t σ = z)) P
      (SourceAssertion.identity (D := D) (fun σ => t σ < z))) :
    validTot (A.rankGhostPre b t).toAssn
      (P.mapStore (StoreLens.fst (R := Int)))
      (SourceAssertion.rankGhostPost (D := D) t).toAssn := by
  apply (validTot_rankGhost_iff A b t P).2
  intro z
  exact (hRank z).sound

#print axioms SourceDerivTot.rankGhost_sound
#print axioms SourceDerivPar.sound
#print axioms SourceDerivTot.sound

end Qhl
