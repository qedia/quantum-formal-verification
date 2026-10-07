import Qhl.Logic.Source.Assertion

/-! # Kraus combinations with the source definedness convention -/

namespace Qhl

open Finset

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)]
variable {σT : Type*}

namespace SourceAssertion

/-- A subnormalized Kraus family sends effects to effects. -/
theorem isEffect_sum_conj_le {ι : Type*} [Fintype ι]
    {A K : ι → EndM D (univ : Finset L)}
    (hA : ∀ i, IsEffect (A i))
    (hK : ∑ i, LinearMap.adjoint (K i) ∘ₗ K i ≤ 1) :
    IsEffect (∑ i, LinearMap.adjoint (K i) ∘ₗ A i ∘ₗ K i) := by
  refine ⟨(LinearMap.nonneg_iff_isPositive _).mpr
    (LinearMap.isPositive_sum _ fun i _ => (hA i).isPositive.adjoint_conj (K i)), ?_⟩
  calc
    _ ≤ ∑ i, LinearMap.adjoint (K i) ∘ₗ (1 : EndM D (univ : Finset L)) ∘ₗ K i :=
      Finset.sum_le_sum fun i _ => conj_le_conj (K i) (hA i).2
    _ = ∑ i, LinearMap.adjoint (K i) ∘ₗ K i := by simp [Module.End.one_eq_id]
    _ ≤ 1 := hK

/-- General assertion-language Kraus combination. Every child must be defined,
including children whose operator is zero. -/
noncomputable def krausSubnormalized {ι : Type*} [Fintype ι] (φ : σT → Prop)
    (A : ι → SourceAssertion σT D)
    (K : σT → ι → EndM D (univ : Finset L))
    (hK : ∀ σ, ∑ i, LinearMap.adjoint (K σ i) ∘ₗ K σ i ≤ 1) :
    SourceAssertion σT D where
  classical := φ
  defined σ := ∀ i, (A i).defined σ
  quantum := {
    op σ := ∑ i, LinearMap.adjoint (K σ i) ∘ₗ (A i).quantum.op σ ∘ₗ K σ i
    isEffect σ := isEffect_sum_conj_le (fun i => (A i).quantum.isEffect σ) (hK σ)
  }

/-- Subnormalization never removes a child's definedness obligation. -/
theorem krausSubnormalized_defined_iff {ι : Type*} [Fintype ι] (φ : σT → Prop)
    (A : ι → SourceAssertion σT D)
    (K : σT → ι → EndM D (univ : Finset L))
    (hK : ∀ σ, ∑ i, LinearMap.adjoint (K σ i) ∘ₗ K σ i ≤ 1) (σ : σT) :
    (krausSubnormalized φ A K hK).defined σ ↔ ∀ i, (A i).defined σ := Iff.rfl

/-- A finite normalized Kraus combination of source quantum predicates.
Its classical formula is supplied separately, as in the paper's common-condition
rules. The component assertions' classical fields do not affect this quantum
predicate constructor; every component's definedness does, even if its Kraus
operator is zero. Normalization is an explicit premise. -/
noncomputable def kraus {ι : Type*} [Fintype ι] (φ : σT → Prop)
    (A : ι → SourceAssertion σT D)
    (K : σT → ι → EndM D (univ : Finset L))
    (hK : ∀ σ, ∑ i, LinearMap.adjoint (K σ i) ∘ₗ K σ i = 1) :
    SourceAssertion σT D where
  classical := φ
  defined σ := ∀ i, (A i).defined σ
  quantum := {
    op σ := ∑ i, LinearMap.adjoint (K σ i) ∘ₗ (A i).quantum.op σ ∘ₗ K σ i
    isEffect σ := isEffect_sum_conj (fun i => (A i).quantum.isEffect σ) (hK σ)
  }

/-- The normalized constructor is the specialization used by accumulation. -/
theorem kraus_eq_subnormalized {ι : Type*} [Fintype ι] (φ : σT → Prop)
    (A : ι → SourceAssertion σT D)
    (K : σT → ι → EndM D (univ : Finset L))
    (hK : ∀ σ, ∑ i, LinearMap.adjoint (K σ i) ∘ₗ K σ i = 1) :
    kraus φ A K hK = krausSubnormalized φ A K (fun σ => le_of_eq (hK σ)) := rfl

/-- The resulting domain requires every component's domain, independently of
its Kraus weight. -/
theorem kraus_defined_iff {ι : Type*} [Fintype ι] (φ : σT → Prop)
    (A : ι → SourceAssertion σT D)
    (K : σT → ι → EndM D (univ : Finset L))
    (hK : ∀ σ, ∑ i, LinearMap.adjoint (K σ i) ∘ₗ K σ i = 1) (σ : σT) :
    (kraus φ A K hK).defined σ ↔ ∀ i, (A i).defined σ := Iff.rfl

/-- The normalized two-component family `(I, 0)`, with `false` selecting
the identity branch and `true` selecting the zero branch. -/
noncomputable def firstWithZero (φ : σT → Prop)
    (A : Bool → SourceAssertion σT D) : SourceAssertion σT D :=
  kraus φ A (fun _ b => if b then 0 else 1) (by
    intro σ
    simp [Module.End.one_eq_id])

/-- The zero-weight child still has to be defined for `(I, 0)` to be defined. -/
theorem firstWithZero_defined_iff (φ : σT → Prop)
    (A : Bool → SourceAssertion σT D) (σ : σT) :
    (firstWithZero φ A).defined σ ↔
      (A false).defined σ ∧ (A true).defined σ := by
  simp [firstWithZero, kraus, Bool.forall_bool]

/-- On its domain the `(I, 0)` combination has the first child's effect. -/
theorem firstWithZero_quantum_op (φ : σT → Prop)
    (A : Bool → SourceAssertion σT D) (σ : σT) :
    (firstWithZero φ A).quantum.op σ = (A false).quantum.op σ := by
  simp [firstWithZero, kraus, Module.End.one_eq_id]

/-- If both children are defined everywhere, interpreting `(I, 0)` amounts to
masking the first child's effect by the supplied classical condition. -/
theorem firstWithZero_toAssn_of_total (φ : σT → Prop)
    (A : Bool → SourceAssertion σT D)
    (hdef : ∀ σ b, (A b).defined σ) :
    (firstWithZero φ A).toAssn = (A false).quantum.mask φ := by
  apply Assn.ext
  funext σ
  simp only [toAssn]
  by_cases hφ : φ σ
  · rw [Assn.mask_op_of_pos hφ]
    rw [Assn.mask_op_of_pos]
    · exact firstWithZero_quantum_op φ A σ
    · exact ⟨hφ, (firstWithZero_defined_iff φ A σ).mpr
        ⟨hdef σ false, hdef σ true⟩⟩
  · rw [Assn.mask_op_of_neg hφ]
    rw [Assn.mask_op_of_neg]
    exact fun h => hφ h.1

end SourceAssertion

end Qhl
