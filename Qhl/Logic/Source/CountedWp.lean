import Qhl.Logic.Source.CountedWhile
import Qhl.Logic.CountedWp

/-! Counted weakest-precondition chains derived in the source proof system.
The classical condition and exit counter are retained separately from the quantum predicate.
-/
namespace Qhl
variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)] {σT : Type*}

namespace SourceDerivTot

/-- A constant-length suffix family, with source body and independent rank proofs. -/
theorem countedWpBody (c : CounterLens σT) (n : ℕ) (φ : σT → Prop)
    (g : ℕ → Assn σT D → Assn σT D) (Y : Assn σT D) (BODY : Prog σT D)
    (hφ : ∀ σ k, φ (c.set σ k) ↔ φ σ)
    (hg : ∀ k (A : Assn σT D), (∀ σ v, A.op (c.set σ v) = A.op σ) →
      ∀ σ v, (g k A).op (c.set σ v) = (g k A).op σ)
    (hY : ∀ σ v, Y.op (c.set σ v) = Y.op σ)
    (hbody : SourceDerivTot
      (SourceAssertion.ofAssn (Assn.ofFam c.get (wpSuffix g n Y))
        (fun σ => φ σ ∧ c.get σ < n)) BODY
      (SourceAssertion.ofAssn (Assn.ofFam c.get (fun k => wpSuffix g n Y (k + 1)))
        (fun σ => φ σ ∧ c.get σ < n)))
    (hrank : ∀ z : Int, SourceDerivTot
      (SourceAssertion.identity (D := D)
        (fun σ => φ σ ∧ c.get σ < n ∧ (↑(n - c.get σ) : Int) = z)) BODY
      (SourceAssertion.identity (D := D)
        (fun σ => φ σ ∧ c.get σ < n ∧ (↑(n - c.get σ) : Int) = z))) :
    SourceDerivTot (SourceAssertion.ofAssn (wpSuffix g n Y 0) φ)
      (countedProg c (fun _ => n) BODY)
      (SourceAssertion.ofAssn Y (fun σ => φ σ ∧ c.get σ = n)) := by
  let A := Assn.ofFam c.get (wpSuffix g n Y)
  have hb : SourceDerivTot
      (SourceAssertion.ofAssn A (fun σ => φ σ ∧ c.get σ < n)) BODY
      (SourceAssertion.ofAssn (A.comp (fun σ => c.set σ (c.get σ + 1)))
        (fun σ => φ σ ∧ c.get σ < n)) := by
    refine .conseq (SourceAssertion.entails_refl _) hbody ?_
    apply SourceAssertion.entails_ofAssn _ _ _ _ (fun _ h => h)
    intro σ _
    apply le_of_eq
    simp only [A, Assn.ofFam_op, Assn.comp_op, c.get_set]
    exact (wpSuffix_op_set g Y c hg hY _ σ _).symm
  have h := countedWhile c (fun _ => n) φ hφ (fun _ _ => rfl) A BODY hb hrank
  refine .conseq ?_ h ?_
  · apply SourceAssertion.entails_ofAssn _ _ _ _ (fun _ h => h)
    intro σ _
    apply le_of_eq
    simp only [A, Assn.comp_op, Assn.ofFam_op, c.get_set]
    exact (wpSuffix_op_set g Y c hg hY 0 σ 0).symm
  · apply SourceAssertion.entails_ofAssn _ _ _ _ (fun _ h => h)
    intro σ hσ
    exact le_of_eq (by simp only [A, Assn.ofFam_op, hσ.2, wpSuffix_full])

/-- A unitary suffix chain, using source unitary, consequence, and total loop. -/
theorem countedWpChain (c : CounterLens σT) (n : ℕ) (φ : σT → Prop)
    {k : ℕ} (r : RegExpr σT L k) (U : ∀ σ, UnitaryOp (TSpace D (r σ)))
    (g : ℕ → Assn σT D → Assn σT D) (Y : Assn σT D)
    (hφ : ∀ σ j, φ (c.set σ j) ↔ φ σ)
    (hg : ∀ j (A : Assn σT D), (∀ σ v, A.op (c.set σ v) = A.op σ) →
      ∀ σ v, (g j A).op (c.set σ v) = (g j A).op σ)
    (hY : ∀ σ v, Y.op (c.set σ v) = Y.op σ)
    (hdist : ∀ σ, φ σ → c.get σ < n → Function.Injective (r σ))
    (hagree : ∀ j, j < n → ∀ σ, φ σ → c.get σ = j → ∀ B : Assn σT D,
      (g j B).op σ = (B.unitaryPre r U).op σ) :
    SourceDerivTot (SourceAssertion.ofAssn (wpSuffix g n Y 0) φ)
      (countedProg c (fun _ => n) (.unitary k r U))
      (SourceAssertion.ofAssn Y (fun σ => φ σ ∧ c.get σ = n)) := by
  refine countedWpBody c n φ g Y _ hφ hg hY ?_ ?_
  · apply unitary_ofAssn _ _ _ _ _ _ (fun _ h => h)
      (fun σ h => hdist σ h.1 h.2)
    intro σ hσ
    apply le_of_eq
    rw [Assn.ofFam_op, wpSuffix_of_lt hσ.2,
      hagree (c.get σ) hσ.2 σ hσ.1 rfl]
    rw [Assn.unitaryPre_op_of_dist _ r U (hdist σ hσ.1 hσ.2),
      Assn.unitaryPre_op_of_dist _ r U (hdist σ hσ.1 hσ.2), Assn.ofFam_op]
  · intro z
    exact unitary_identity r U _ (fun σ h => hdist σ h.1 h.2.1)

end SourceDerivTot
end Qhl
