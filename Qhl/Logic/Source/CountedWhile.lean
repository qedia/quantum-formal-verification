import Qhl.Logic.Source.BasicDerived
import Qhl.Logic.CountedWhile

/-! Source counted iteration with explicit classical conditions and independent rank proofs. -/
namespace Qhl
variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)] {σT : Type*}

namespace SourceDerivTot
/-- A counted program retains its classical input condition and establishes the exact
exit counter. The quantum body and identity-rank body are separate source derivations. -/
theorem countedWhile (c : CounterLens σT) (N : σT → ℕ) (φ : σT → Prop)
    (hφ : ∀ σ k, φ (c.set σ k) ↔ φ σ)
    (hN : ∀ σ k, N (c.set σ k) = N σ)
    (A : Assn σT D) (BODY : Prog σT D)
    (hbody : SourceDerivTot
      (SourceAssertion.ofAssn A (fun σ => φ σ ∧ c.get σ < N σ)) BODY
      (SourceAssertion.ofAssn (A.comp (fun σ => c.set σ (c.get σ + 1)))
        (fun σ => φ σ ∧ c.get σ < N σ)))
    (hrank : ∀ z : Int, SourceDerivTot
      (SourceAssertion.identity (D := D)
        (fun σ => φ σ ∧ c.get σ < N σ ∧ (↑(N σ - c.get σ) : Int) = z)) BODY
      (SourceAssertion.identity (D := D)
        (fun σ => φ σ ∧ c.get σ < N σ ∧ (↑(N σ - c.get σ) : Int) = z))) :
    SourceDerivTot
      (SourceAssertion.ofAssn (A.comp (fun σ => c.set σ 0)) φ)
      (countedProg c N BODY)
      (SourceAssertion.ofAssn A (fun σ => φ σ ∧ c.get σ = N σ)) := by
  classical
  let I := SourceAssertion.ofAssn A (fun σ => φ σ ∧ c.get σ ≤ N σ)
  let b := fun σ => decide (c.get σ < N σ)
  let inc := fun σ => c.set σ (c.get σ + 1)
  have hi : SourceDerivTot
      (I.withClassical fun σ => I.classical σ ∧ b σ = true)
      (BODY.seq (.assign inc)) I := by
    refine .seq (.conseq ?_ hbody (SourceAssertion.entails_refl _))
      (.conseq ?_ (.assign inc I) (SourceAssertion.entails_refl _))
    · apply SourceAssertion.entails_ofAssn
      · intro σ h
        exact ⟨h.1.1, of_decide_eq_true h.2⟩
      · intro σ _; exact le_rfl
    · refine ⟨?_, fun σ _ => ⟨Iff.rfl, fun _ => le_rfl⟩⟩
      intro σ h
      exact ⟨(hφ σ _).mpr h.1, by simpa [inc, c.get_set, hN] using h.2⟩
  have hd (z : Int) : SourceDerivTot
      (SourceAssertion.identity (D := D)
        (fun σ => I.classical σ ∧ b σ = true ∧ (↑(N σ - c.get σ) : Int) = z))
      (BODY.seq (.assign inc))
      (SourceAssertion.identity (D := D) (fun σ => (↑(N σ - c.get σ) : Int) < z)) := by
    refine .seq (.conseq ?_ (hrank z) (SourceAssertion.entails_refl _))
      (.conseq ?_ (.assign inc _) (SourceAssertion.entails_refl _))
    · refine ⟨?_, fun σ _ => ⟨Iff.rfl, fun _ => le_rfl⟩⟩
      intro σ h
      exact ⟨h.1.1, of_decide_eq_true h.2.1, h.2.2⟩
    · refine ⟨?_, fun σ _ => ⟨Iff.rfl, fun _ => le_rfl⟩⟩
      intro σ h
      dsimp [SourceAssertion.subst, SourceAssertion.identity, inc]
      rw [hN, c.get_set]
      change φ σ ∧ c.get σ < N σ ∧ (↑(N σ - c.get σ) : Int) = z at h
      omega
  have hw := SourceDerivTot.whileLoop b (fun σ => (↑(N σ - c.get σ) : Int))
    (A := I) (fun _ _ => Int.natCast_nonneg _) hi hd
  refine .seq (.conseq ?_ (.assign (fun σ => c.set σ 0) I)
    (SourceAssertion.entails_refl _)) (.conseq (SourceAssertion.entails_refl _) hw ?_)
  · refine ⟨?_, fun σ _ => ⟨Iff.rfl, fun _ => le_rfl⟩⟩
    intro σ h
    exact ⟨(hφ σ 0).mpr h, by simp [c.get_set]⟩
  · apply SourceAssertion.entails_ofAssn
    · intro σ h
      have hn : ¬ c.get σ < N σ := of_decide_eq_false h.2
      exact ⟨h.1.1, Nat.le_antisymm h.1.2 (Nat.le_of_not_gt hn)⟩
    · intro σ _; exact le_rfl
end SourceDerivTot
end Qhl
