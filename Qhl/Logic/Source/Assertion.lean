import Qhl.Logic.Rules

/-! # Classical-quantum assertions with explicit definedness

Source: QHL+ Definitions of quantum entailment and cq entailment.
This module retains the classical formula and definedness separately from
its interpretation as a masked effect. The converse of the interpretation's
monotonicity is deliberately not asserted.
-/

namespace Qhl

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)]
variable {σT : Type*}

/-- A source cq assertion retains the classical condition and the domain of its
quantum predicate formula. The effect outside that domain is semantically unused. -/
structure SourceAssertion (σT : Type*) {L : Type*} [Fintype L] [DecidableEq L]
    (D : L → Type*) [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)] where
  /-- Interpretation of the classical formula. -/
  classical : σT → Prop
  /-- States where the quantum predicate formula is well-defined. -/
  defined : σT → Prop
  /-- The quantum effect, relevant only where `defined` holds. -/
  quantum : Assn σT D

namespace SourceAssertion

/-- Paper Definition `qp-entail`: quantum entailment under a classical condition. -/
def QuantumEntails (φ : σT → Prop) (A B : SourceAssertion σT D) : Prop :=
  ∀ σ, φ σ → (A.defined σ ↔ B.defined σ) ∧
    (A.defined σ → A.quantum.op σ ≤ B.quantum.op σ)

/-- Paper Definition `cq-entail`: classical entailment together with quantum
entailment under the source classical formula. -/
def Entails (A B : SourceAssertion σT D) : Prop :=
  (∀ σ, A.classical σ → B.classical σ) ∧ QuantumEntails A.classical A B

/-- Source entailment is reflexive. -/
theorem entails_refl (A : SourceAssertion σT D) : Entails A A := by
  constructor
  · intro σ h
    exact h
  · intro σ _
    exact ⟨Iff.rfl, fun _ => le_rfl⟩

/-- Source entailment is transitive, including its definedness obligation. -/
theorem entails_trans {A B C : SourceAssertion σT D}
    (hAB : Entails A B) (hBC : Entails B C) : Entails A C := by
  constructor
  · intro σ hA
    exact hBC.1 σ (hAB.1 σ hA)
  · intro σ hA
    obtain ⟨hABd, hABq⟩ := hAB.2 σ hA
    obtain ⟨hBCd, hBCq⟩ := hBC.2 σ (hAB.1 σ hA)
    exact ⟨hABd.trans hBCd, fun hd => (hABq hd).trans (hBCq (hABd.mp hd))⟩

/-- Interpret a source assertion as an assertion for the existing semantic
rules, masking states failing either the classical formula or definedness. -/
noncomputable def toAssn (A : SourceAssertion σT D) : Assn σT D :=
  A.quantum.mask fun σ => A.classical σ ∧ A.defined σ

/-- Source entailment implies order of the interpreted assertions. -/
theorem entails_toAssn_le {A B : SourceAssertion σT D}
    (h : Entails A B) : A.toAssn ≤ B.toAssn := by
  apply Assn.mask_le_mask
  · intro σ hσ
    exact ⟨h.1 σ hσ.1, (h.2 σ hσ.1).1.mp hσ.2⟩
  · intro σ hσ
    exact (h.2 σ hσ.1).2 hσ.2

/-- Substitute a classical-state transformation into all three components. -/
def subst (A : SourceAssertion σT D) (f : σT → σT) : SourceAssertion σT D where
  classical σ := A.classical (f σ)
  defined σ := A.defined (f σ)
  quantum := A.quantum.comp f

/-- Substitution preserves source entailment. -/
theorem entails_subst {A B : SourceAssertion σT D} (f : σT → σT)
    (h : Entails A B) : Entails (A.subst f) (B.subst f) := by
  constructor
  · intro σ hσ
    exact h.1 (f σ) hσ
  · intro σ hσ
    exact h.2 (f σ) hσ

/-- Interpretation commutes with substitution of classical states. -/
theorem toAssn_subst (A : SourceAssertion σT D) (f : σT → σT) :
    (A.subst f).toAssn = A.toAssn.comp f := by
  apply Assn.ext
  funext σ
  rfl

/-- Source equivalence is mutual source entailment. -/
def Eqv (A B : SourceAssertion σT D) : Prop := Entails A B ∧ Entails B A

/-- Source equivalence has exactly the paper's classical, definedness, and
on-domain quantum equality clauses. -/
theorem eqv_iff (A B : SourceAssertion σT D) : Eqv A B ↔
    (∀ σ, A.classical σ ↔ B.classical σ) ∧
      (∀ σ, A.classical σ → (A.defined σ ↔ B.defined σ) ∧
        (A.defined σ → A.quantum.op σ = B.quantum.op σ)) := by
  constructor
  · rintro ⟨hAB, hBA⟩
    constructor
    · intro σ
      exact ⟨hAB.1 σ, hBA.1 σ⟩
    · intro σ hA
      obtain ⟨hd, hle⟩ := hAB.2 σ hA
      obtain ⟨_, hge⟩ := hBA.2 σ (hAB.1 σ hA)
      exact ⟨hd, fun hdef => le_antisymm (hle hdef) (hge (hd.mp hdef))⟩
  · rintro ⟨hc, hq⟩
    constructor
    · constructor
      · intro σ hA
        exact (hc σ).mp hA
      · intro σ hA
        obtain ⟨hd, heq⟩ := hq σ hA
        exact ⟨hd, fun hdef => (heq hdef).le⟩
    · constructor
      · intro σ hB
        exact (hc σ).mpr hB
      · intro σ hB
        obtain ⟨hd, heq⟩ := hq σ ((hc σ).mpr hB)
        exact ⟨hd.symm, fun hdef => (heq (hd.mpr hdef)).ge⟩

end SourceAssertion

end Qhl
