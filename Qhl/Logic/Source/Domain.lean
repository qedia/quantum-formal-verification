import Qhl.Logic.Source.Assertion

/-! # An explicit additional domain for a source quantum predicate -/

namespace Qhl

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)] {σT : Type*}

/-- Restrict the quantum domain without changing the classical formula. -/
def SourceAssertion.onDomain (A : SourceAssertion σT D) (d : σT → Prop) :
    SourceAssertion σT D := { A with defined := fun σ => d σ ∧ A.defined σ }

/-- Domain restriction interprets as an effect mask, while remaining distinct
from a change to the classical condition at the source level. -/
theorem SourceAssertion.onDomain_toAssn (A : SourceAssertion σT D) (d : σT → Prop) :
    (A.onDomain d).toAssn = A.toAssn.mask d := by
  apply Assn.ext
  funext σ
  by_cases hc : A.classical σ <;> by_cases hd : A.defined σ <;> by_cases h : d σ <;>
    simp [SourceAssertion.toAssn, SourceAssertion.onDomain, Assn.mask, hc, hd, h]

end Qhl
