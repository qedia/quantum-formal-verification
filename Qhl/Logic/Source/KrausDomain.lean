import Qhl.Logic.Source.Kraus

/-! # Domain behavior of interpreted source Kraus combinations -/

namespace Qhl

open Finset

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)]
variable {σT : Type*}

namespace SourceAssertion

/-- The interpreted compound precondition is bounded by the weighted sum of
individually masked child effects. The child classical fields play no role. -/
theorem kraus_toAssn_op_le_sum_mask {ι : Type*} [Fintype ι]
    (φ : σT → Prop) (A : ι → SourceAssertion σT D)
    (K : σT → ι → EndM D (univ : Finset L))
    (hK : ∀ σ, ∑ i, LinearMap.adjoint (K σ i) ∘ₗ K σ i = 1) (σ : σT) :
    (kraus φ A K hK).toAssn.op σ ≤
      ∑ i, LinearMap.adjoint (K σ i) ∘ₗ
        ((A i).quantum.mask fun τ => φ τ ∧ (A i).defined τ).op σ ∘ₗ K σ i := by
  classical
  change ((kraus φ A K hK).quantum.mask
    (fun τ => φ τ ∧ ∀ i, (A i).defined τ)).op σ ≤ _
  by_cases hφ : φ σ
  · by_cases hd : ∀ i, (A i).defined σ
    · rw [Assn.mask_op_of_pos (φ := fun τ => φ τ ∧ ∀ i, (A i).defined τ)
        (show φ σ ∧ (∀ i, (A i).defined σ)
          from ⟨hφ, hd⟩)]
      change (∑ i, LinearMap.adjoint (K σ i) ∘ₗ (A i).quantum.op σ ∘ₗ K σ i) ≤ _
      apply le_of_eq
      apply Finset.sum_congr rfl
      intro i _
      rw [Assn.mask_op_of_pos (φ := fun τ => φ τ ∧ (A i).defined τ)
        (show φ σ ∧ (A i).defined σ from ⟨hφ, hd i⟩)]
    · rw [Assn.mask_op_of_neg (φ := fun τ => φ τ ∧ ∀ i, (A i).defined τ)
        (show ¬ (φ σ ∧ ∀ i, (A i).defined σ)
          from fun h => hd h.2)]
      apply Finset.sum_nonneg
      intro i _
      by_cases hi : (A i).defined σ
      · rw [Assn.mask_op_of_pos (φ := fun τ => φ τ ∧ (A i).defined τ)
        (show φ σ ∧ (A i).defined σ from ⟨hφ, hi⟩)]
        simpa using conj_le_conj (K σ i) ((A i).quantum.isEffect σ).1
      · rw [Assn.mask_op_of_neg (φ := fun τ => φ τ ∧ (A i).defined τ)
          (show ¬ (φ σ ∧ (A i).defined σ)
            from fun h => hi h.2)]
        simp
  · rw [Assn.mask_op_of_neg (φ := fun τ => φ τ ∧ ∀ i, (A i).defined τ)
        (show ¬ (φ σ ∧ ∀ i, (A i).defined σ)
        from fun h => hφ h.1)]
    apply Finset.sum_nonneg
    intro i _
    rw [Assn.mask_op_of_neg (φ := fun τ => φ τ ∧ (A i).defined τ)
          (show ¬ (φ σ ∧ (A i).defined σ)
      from fun h => hφ h.1)]
    simp

/-- Under a common classical condition, pairwise agreement of all child domains
makes interpretation of a source Kraus combination commute with the weighted sum. -/
theorem kraus_toAssn_op_eq_sum_mask_of_domains {ι : Type*} [Fintype ι]
    (ψ : σT → Prop) (B : ι → SourceAssertion σT D)
    (K : σT → ι → EndM D (univ : Finset L))
    (hK : ∀ σ, ∑ i, LinearMap.adjoint (K σ i) ∘ₗ K σ i = 1)
    (hdom : ∀ σ, ψ σ → ∀ i j, (B i).defined σ ↔ (B j).defined σ)
    (σ : σT) :
    (kraus ψ B K hK).toAssn.op σ =
      ∑ i, LinearMap.adjoint (K σ i) ∘ₗ
        ((B i).quantum.mask fun τ => ψ τ ∧ (B i).defined τ).op σ ∘ₗ K σ i := by
  classical
  change ((kraus ψ B K hK).quantum.mask
    (fun τ => ψ τ ∧ ∀ i, (B i).defined τ)).op σ = _
  by_cases hψ : ψ σ
  · by_cases hd : ∀ i, (B i).defined σ
    · rw [Assn.mask_op_of_pos (φ := fun τ => ψ τ ∧ ∀ i, (B i).defined τ)
        (show ψ σ ∧ (∀ i, (B i).defined σ)
          from ⟨hψ, hd⟩)]
      change (∑ i, LinearMap.adjoint (K σ i) ∘ₗ (B i).quantum.op σ ∘ₗ K σ i) = _
      apply Finset.sum_congr rfl
      intro i _
      rw [Assn.mask_op_of_pos (φ := fun τ => ψ τ ∧ (B i).defined τ)
        (show ψ σ ∧ (B i).defined σ from ⟨hψ, hd i⟩)]
    · obtain ⟨j, hj⟩ := not_forall.mp hd
      rw [Assn.mask_op_of_neg (φ := fun τ => ψ τ ∧ ∀ i, (B i).defined τ)
        (show ¬ (ψ σ ∧ ∀ i, (B i).defined σ)
        from fun h => hd h.2)]
      symm
      apply Finset.sum_eq_zero
      intro i _
      have hi : ¬ (B i).defined σ := fun h => hj ((hdom σ hψ i j).mp h)
      rw [Assn.mask_op_of_neg (φ := fun τ => ψ τ ∧ (B i).defined τ)
        (show ¬ (ψ σ ∧ (B i).defined σ)
        from fun h => hi h.2)]
      simp
  · rw [Assn.mask_op_of_neg (φ := fun τ => ψ τ ∧ ∀ i, (B i).defined τ)
        (show ¬ (ψ σ ∧ ∀ i, (B i).defined σ)
        from fun h => hψ h.1)]
    symm
    apply Finset.sum_eq_zero
    intro i _
    rw [Assn.mask_op_of_neg (φ := fun τ => ψ τ ∧ (B i).defined τ)
        (show ¬ (ψ σ ∧ (B i).defined σ)
      from fun h => hψ h.1)]
    simp

/-- Total child definedness under the postcondition is sufficient for the
common-domain equality. -/
theorem kraus_toAssn_op_eq_sum_mask_of_defined {ι : Type*} [Fintype ι]
    (ψ : σT → Prop) (B : ι → SourceAssertion σT D)
    (K : σT → ι → EndM D (univ : Finset L))
    (hK : ∀ σ, ∑ i, LinearMap.adjoint (K σ i) ∘ₗ K σ i = 1)
    (hdef : ∀ σ, ψ σ → ∀ i, (B i).defined σ) (σ : σT) :
    (kraus ψ B K hK).toAssn.op σ =
      ∑ i, LinearMap.adjoint (K σ i) ∘ₗ
        ((B i).quantum.mask fun τ => ψ τ ∧ (B i).defined τ).op σ ∘ₗ K σ i := by
  apply kraus_toAssn_op_eq_sum_mask_of_domains ψ B K hK
  intro τ hψ i j
  exact iff_of_true (hdef τ hψ i) (hdef τ hψ j)

end SourceAssertion

end Qhl
