import Qhl.Logic.Source.Assertion
import Qhl.Logic.Soundness

/-! # Source consequence as an interface to the existing derivations -/

namespace Qhl

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)]
variable {σT : Type*}

/-- Source (R-Conseq) for partial derivations. The source entailment premises
are stronger than their masked-effect interpretations. -/
theorem DerivPar.sourceConseq {A A' B' B : SourceAssertion σT D} {P : Prog σT D}
    (hA : SourceAssertion.Entails A A')
    (h : DerivPar A'.toAssn P B'.toAssn)
    (hB : SourceAssertion.Entails B' B) : DerivPar A.toAssn P B.toAssn :=
  DerivPar.conseq (SourceAssertion.entails_toAssn_le hA) h
    (SourceAssertion.entails_toAssn_le hB)

/-- Source (R-Conseq) for total derivations. -/
theorem DerivTot.sourceConseq {A A' B' B : SourceAssertion σT D} {P : Prog σT D}
    (hA : SourceAssertion.Entails A A')
    (h : DerivTot A'.toAssn P B'.toAssn)
    (hB : SourceAssertion.Entails B' B) : DerivTot A.toAssn P B.toAssn :=
  DerivTot.conseq (SourceAssertion.entails_toAssn_le hA) h
    (SourceAssertion.entails_toAssn_le hB)

/-- Source consequence preserves semantic partial correctness. -/
theorem validPar_sourceConseq {A A' B' B : SourceAssertion σT D} {P : Prog σT D}
    (hA : SourceAssertion.Entails A A')
    (h : validPar A'.toAssn P B'.toAssn)
    (hB : SourceAssertion.Entails B' B) : validPar A.toAssn P B.toAssn :=
  validPar_conseq (SourceAssertion.entails_toAssn_le hA) h
    (SourceAssertion.entails_toAssn_le hB)

/-- Source consequence preserves semantic total correctness. -/
theorem validTot_sourceConseq {A A' B' B : SourceAssertion σT D} {P : Prog σT D}
    (hA : SourceAssertion.Entails A A')
    (h : validTot A'.toAssn P B'.toAssn)
    (hB : SourceAssertion.Entails B' B) : validTot A.toAssn P B.toAssn :=
  validTot_conseq (SourceAssertion.entails_toAssn_le hA) h
    (SourceAssertion.entails_toAssn_le hB)

/-- Masked inequality cannot recover source entailment: zero effects conceal
a failed classical implication, even when both predicates are defined. -/
theorem masked_le_not_source_entails_classical :
    ∃ A B : SourceAssertion Unit D,
      A.toAssn ≤ B.toAssn ∧ ¬ SourceAssertion.Entails A B := by
  let A : SourceAssertion Unit D :=
    ⟨fun _ => True, fun _ => True, Assn.zero⟩
  let B : SourceAssertion Unit D :=
    ⟨fun _ => False, fun _ => True, Assn.zero⟩
  refine ⟨A, B, ?_, ?_⟩
  · intro σ
    simp [SourceAssertion.toAssn, A, B]
  · intro h
    exact (h.1 () trivial).elim

/-- A zero effect also conceals disagreement about definedness under an
identical, everywhere-true classical condition. -/
theorem masked_le_not_source_entails_defined :
    ∃ A B : SourceAssertion Unit D,
      A.toAssn ≤ B.toAssn ∧ ¬ SourceAssertion.Entails A B := by
  let A : SourceAssertion Unit D :=
    ⟨fun _ => True, fun _ => True, Assn.zero⟩
  let B : SourceAssertion Unit D :=
    ⟨fun _ => True, fun _ => False, Assn.zero⟩
  refine ⟨A, B, ?_, ?_⟩
  · intro σ
    simp [SourceAssertion.toAssn, A, B]
  · intro h
    exact (h.2 () trivial).1.mp trivial

end Qhl
