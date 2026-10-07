import Qhl.Logic.Source.KrausDomain
import Qhl.Logic.Source.TotalLoop
import Qhl.History.KrausSum

/-! # The disjoint-postcondition bound for source Accum1 -/

namespace Qhl

open Finset
open scoped ENNReal

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)] {σT : Type*}

namespace SourceAssertion

/-- Rank-one Kraus combination used in the conclusion of Accum1. -/
noncomputable def krausOne (ψ : σT → Prop) (B : SourceAssertion σT D)
    (J : σT → EndM D (univ : Finset L))
    (hJ : ∀ σ, LinearMap.adjoint (J σ) ∘ₗ J σ ≤ 1) : SourceAssertion σT D :=
  krausSubnormalized ψ (fun _ : Unit => B) (fun σ _ => J σ) (fun σ => by simpa using hJ σ)

/-- The singleton's domain is precisely the child's domain. -/
theorem krausOne_toAssn_op (ψ : σT → Prop) (B : SourceAssertion σT D)
    (J : σT → EndM D (univ : Finset L))
    (hJ : ∀ σ, LinearMap.adjoint (J σ) ∘ₗ J σ ≤ 1) (σ : σT) :
    (krausOne ψ B J hJ).toAssn.op σ =
      LinearMap.adjoint (J σ) ∘ₗ (B.withClassical ψ).toAssn.op σ ∘ₗ J σ := by
  by_cases h : ψ σ ∧ B.defined σ
  · simp [krausOne, krausSubnormalized, withClassical, toAssn, Assn.mask_op_of_pos, h]
  · simp [krausOne, krausSubnormalized, withClassical, toAssn, Assn.mask_op_of_neg, h]

/-- State-side source domination bounds the expectation of any positive effect. -/
theorem expectE_conj_le_of_state_le (B : Assn σT D)
    (K J : EndM D (univ : Finset L)) (s : CQState σT D)
    (h : (s.q.conj K).op ≤ (s.q.conj J).op) :
    expectE B.op ⟨s.cls, s.q.conj K⟩ ≤ expectE B.op ⟨s.cls, s.q.conj J⟩ := by
  apply ENNReal.ofReal_le_ofReal
  have ht := (Complex.le_def.mp (trace_comp_mono (B.isPositive s.cls) h)).1
  unfold expect
  simp only [LinearMap.trace_comp_comm' (B.op s.cls)]
  exact ht

/-- At most one classical postcondition contributes at any terminal state.
The source domination condition then bounds that contribution by the singleton. -/
theorem accumOne_expect_le {ι : Type*} [Fintype ι]
    (ψ : ι → σT → Prop) (B : SourceAssertion σT D)
    (K : σT → ι → EndM D (univ : Finset L))
    (J : σT → EndM D (univ : Finset L))
    (hJ : ∀ σ, LinearMap.adjoint (J σ) ∘ₗ J σ ≤ 1)
    (hexcl : ∀ σ i j, i ≠ j → ψ i σ → ¬ ψ j σ)
    (hdom : ∀ σ i (ρ : PDensity D), (ρ.conj (K σ i)).op ≤ (ρ.conj (J σ)).op)
    (s : CQState σT D) :
    (∑ i, expectE (B.withClassical (ψ i)).toAssn.op
        ⟨s.cls, s.q.conj (K s.cls i)⟩) ≤
      expectE (krausOne (fun σ => ∃ i, ψ i σ) B J hJ).toAssn.op s := by
  classical
  have hone : expectE (krausOne (fun σ => ∃ i, ψ i σ) B J hJ).toAssn.op s =
      expectE (B.withClassical (fun σ => ∃ i, ψ i σ)).toAssn.op
        ⟨s.cls, s.q.conj (J s.cls)⟩ := by
    unfold expectE
    have he := expect_conj (B.withClassical (fun σ => ∃ i, ψ i σ)).toAssn.op
      (J s.cls) s.cls s
    rw [← he]
    unfold expect
    rw [krausOne_toAssn_op]
  rw [hone]
  by_cases ha : ∃ i, ψ i s.cls ∧ B.defined s.cls
  · obtain ⟨j, hj, hd⟩ := ha
    rw [Finset.sum_eq_single j]
    · change expectE (B.quantum.mask (fun σ => ψ j σ ∧ B.defined σ)).op _ ≤
        expectE (B.quantum.mask (fun σ => (∃ i, ψ i σ) ∧ B.defined σ)).op _
      rw [expectE_mask_of_pos ⟨hj, hd⟩, expectE_mask_of_pos ⟨⟨j, hj⟩, hd⟩]
      exact expectE_conj_le_of_state_le B.quantum _ _ s (hdom s.cls j s.q)
    · intro i _ hij
      change expectE (B.quantum.mask (fun σ => ψ i σ ∧ B.defined σ)).op _ = 0
      exact expectE_mask_of_neg (fun h => hexcl s.cls i j hij h.1 hj)
    · simp
  · have hz : ∀ i, expectE (B.withClassical (ψ i)).toAssn.op
        ⟨s.cls, s.q.conj (K s.cls i)⟩ = 0 := by
      intro i
      change expectE (B.quantum.mask (fun σ => ψ i σ ∧ B.defined σ)).op _ = 0
      exact expectE_mask_of_neg (fun h => ha ⟨i, h⟩)
    simp only [hz, Finset.sum_const_zero, zero_le]

/-- The history form of the exclusive-postcondition bound. -/
theorem accumOne_PostH_le {ι : Type*} [Fintype ι]
    (ψ : ι → σT → Prop) (B : SourceAssertion σT D)
    (K : σT → ι → EndM D (univ : Finset L))
    (J : σT → EndM D (univ : Finset L))
    (hJ : ∀ σ, LinearMap.adjoint (J σ) ∘ₗ J σ ≤ 1)
    (hexcl : ∀ σ i j, i ≠ j → ψ i σ → ¬ ψ j σ)
    (hdom : ∀ σ i (ρ : PDensity D), (ρ.conj (K σ i)).op ≤ (ρ.conj (J σ)).op)
    (c : Config σT D) (hc : ∀ i, c.ctrl.KrausFrame (fun σ => K σ i)) :
    (∑ i, PostH (c.krausMap (fun σ => K σ i)) (B.withClassical (ψ i)).toAssn.op) ≤
      PostH c (krausOne (fun σ => ∃ i, ψ i σ) B J hJ).toAssn.op := by
  rw [sum_PostH_krausMap]
  · rw [PostH_eq_tsum (fun σ => LinearMap.isPositive_sum _
        (fun i _ => ((B.withClassical (ψ i)).toAssn.isPositive σ).adjoint_conj (K σ i))),
      PostH_eq_tsum (krausOne (fun σ => ∃ i, ψ i σ) B J hJ).toAssn.isPositive]
    apply ENNReal.tsum_le_tsum
    intro n
    apply dSum_mono
    intro s
    rw [expectE_kraus_sum _ (fun i => (B.withClassical (ψ i)).toAssn.isPositive)]
    exact accumOne_expect_le ψ B K J hJ hexcl hdom s
  · exact hc

end SourceAssertion
end Qhl
