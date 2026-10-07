import Qhl.Logic.Source.TotalLoop

/-! # Strict quantum masking and its interpretation -/
namespace Qhl
variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)] {σT : Type*}
namespace SourceAssertion
/-- Multiplication by a classical indicator retains the operand's domain,
including where the indicator is false. -/
noncomputable def quantumMask (A : SourceAssertion σT D) (b : σT → Prop) :
    SourceAssertion σT D := { A with quantum := A.quantum.mask b }

/-- Moving a quantum mask to the classical postcondition preserves interpretation. -/
theorem quantumMask_toAssn (A : SourceAssertion σT D) (b : σT → Prop) :
    (A.quantumMask b).toAssn =
      (A.withClassical fun σ => A.classical σ ∧ b σ).toAssn := by
  classical
  apply Assn.ext
  funext σ
  by_cases hc : A.classical σ <;> by_cases hd : A.defined σ <;> by_cases hb : b σ <;>
    simp [quantumMask, toAssn, withClassical, Assn.mask, hc, hd, hb]
end SourceAssertion
end Qhl
