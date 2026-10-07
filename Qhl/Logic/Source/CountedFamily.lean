import Qhl.Logic.Source.CountedWhile

/-! Counted iteration of arbitrary quantum-predicate families in the source system. -/
namespace Qhl
variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)] {σT : Type*}
namespace SourceDerivTot

theorem countedFamily (c : CounterLens σT) (n : ℕ) (φ : σT → Prop)
    (J : ℕ → Assn σT D) (BODY : Prog σT D)
    (hφ : ∀ σ k, φ (c.set σ k) ↔ φ σ)
    (hJ : ∀ k σ v, (J k).op (c.set σ v) = (J k).op σ)
    (hbody : SourceDerivTot
      (SourceAssertion.ofAssn (Assn.ofFam c.get J) (fun σ => φ σ ∧ c.get σ < n)) BODY
      (SourceAssertion.ofAssn (Assn.ofFam c.get (fun k => J (k + 1)))
        (fun σ => φ σ ∧ c.get σ < n)))
    (hrank : ∀ z : Int, SourceDerivTot
      (SourceAssertion.identity (D := D)
        (fun σ => φ σ ∧ c.get σ < n ∧ (↑(n - c.get σ) : Int) = z)) BODY
      (SourceAssertion.identity (D := D)
        (fun σ => φ σ ∧ c.get σ < n ∧ (↑(n - c.get σ) : Int) = z))) :
    SourceDerivTot (SourceAssertion.ofAssn (J 0) φ)
      (countedProg c (fun _ => n) BODY)
      (SourceAssertion.ofAssn (J n) (fun σ => φ σ ∧ c.get σ = n)) := by
  let A := Assn.ofFam c.get J
  have hb : SourceDerivTot
      (SourceAssertion.ofAssn A (fun σ => φ σ ∧ c.get σ < n)) BODY
      (SourceAssertion.ofAssn (A.comp (fun σ => c.set σ (c.get σ + 1)))
        (fun σ => φ σ ∧ c.get σ < n)) := by
    refine .conseq (SourceAssertion.entails_refl _) hbody ?_
    apply SourceAssertion.entails_ofAssn _ _ _ _ (fun _ h => h)
    intro σ _
    exact le_of_eq (by simp only [A, Assn.ofFam_op, Assn.comp_op, c.get_set, hJ])
  refine .conseq ?_
    (countedWhile c (fun _ => n) φ hφ (fun _ _ => rfl) A BODY hb hrank) ?_
  · apply SourceAssertion.entails_ofAssn _ _ _ _ (fun _ h => h)
    intro σ _
    exact le_of_eq (by simp only [A, Assn.comp_op, Assn.ofFam_op, c.get_set, hJ])
  · apply SourceAssertion.entails_ofAssn _ _ _ _ (fun _ h => h)
    intro σ hσ
    exact le_of_eq (by simp only [A, Assn.ofFam_op, hσ.2])

end SourceDerivTot
end Qhl
