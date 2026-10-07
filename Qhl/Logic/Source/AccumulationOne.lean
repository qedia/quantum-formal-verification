import Qhl.Logic.Source.AccumulationOneOrder

/-! # General finite-Kraus Accum1 soundness

The frame premise is structural and is proved through operational histories.
The domination premise is the source's state-side `F ∝ F'` condition, in the
library's adjoint orientation. The conclusion only evaluates the singleton
operator at output states; its program-frame property is not needed by this
semantic core. A source parameter/index adapter may additionally supply it.
-/

namespace Qhl

open Finset
open scoped ENNReal

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)] {σT : Type*}

namespace SourceAssertion

private theorem accumOne_pre_le {ι : Type*} [Fintype ι]
    (φ : σT → Prop) (A : ι → SourceAssertion σT D)
    (K : σT → ι → EndM D (univ : Finset L))
    (hK : ∀ σ, ∑ i, LinearMap.adjoint (K σ i) ∘ₗ K σ i = 1)
    (s : CQState σT D) :
    expectE (kraus φ A K hK).toAssn.op s ≤
      ∑ i, expectE ((A i).withClassical φ).toAssn.op
        ⟨s.cls, s.q.conj (K s.cls i)⟩ := by
  calc
    expectE (kraus φ A K hK).toAssn.op s ≤
        expectE (fun σ => ∑ i, LinearMap.adjoint (K σ i) ∘ₗ
          ((A i).withClassical φ).toAssn.op σ ∘ₗ K σ i) s :=
      expectE_mono (kraus_toAssn_op_le_sum_mask φ A K hK) s
    _ = _ := expectE_kraus_sum _ (fun i => ((A i).withClassical φ).toAssn.isPositive) K s

/-- Total Accum1 combines exclusive classical postconditions and general
finite Kraus operators under the printed domination premise. -/
theorem validTot_accumOne {ι : Type*} [Fintype ι]
    (φ : σT → Prop) (ψ : ι → σT → Prop)
    (A : ι → SourceAssertion σT D) (B : SourceAssertion σT D)
    (K : σT → ι → EndM D (univ : Finset L))
    (J : σT → EndM D (univ : Finset L))
    (hK : ∀ σ, ∑ i, LinearMap.adjoint (K σ i) ∘ₗ K σ i = 1)
    (hJ : ∀ σ, LinearMap.adjoint (J σ) ∘ₗ J σ ≤ 1)
    (P : Prog σT D) (hframe : ∀ i, P.KrausFrame (fun σ => K σ i))
    (hexcl : ∀ σ i j, i ≠ j → ψ i σ → ¬ ψ j σ)
    (hdom : ∀ σ i (ρ : PDensity D), (ρ.conj (K σ i)).op ≤ (ρ.conj (J σ)).op)
    (hcomp : ∀ i, validTot ((A i).withClassical φ).toAssn P
      (B.withClassical (ψ i)).toAssn) :
    validTot (kraus φ A K hK).toAssn P
      (krausOne (fun σ => ∃ i, ψ i σ) B J hJ).toAssn := by
  intro s
  calc
    expectE (kraus φ A K hK).toAssn.op s ≤ _ := accumOne_pre_le φ A K hK s
    _ ≤ ∑ i, PostH ((Config.init P s).krausMap (fun σ => K σ i))
        (B.withClassical (ψ i)).toAssn.op := by
      apply Finset.sum_le_sum
      intro i _
      exact hcomp i ⟨s.cls, s.q.conj (K s.cls i)⟩
    _ ≤ _ := accumOne_PostH_le ψ B K J hJ hexcl hdom (Config.init P s) hframe

/-- Partial Accum1 sums transformed-input nontermination exactly once, using
normalization, rather than charging the original nontermination per branch. -/
theorem validPar_accumOne {ι : Type*} [Fintype ι]
    (φ : σT → Prop) (ψ : ι → σT → Prop)
    (A : ι → SourceAssertion σT D) (B : SourceAssertion σT D)
    (K : σT → ι → EndM D (univ : Finset L))
    (J : σT → EndM D (univ : Finset L))
    (hK : ∀ σ, ∑ i, LinearMap.adjoint (K σ i) ∘ₗ K σ i = 1)
    (hJ : ∀ σ, LinearMap.adjoint (J σ) ∘ₗ J σ ≤ 1)
    (P : Prog σT D) (hframe : ∀ i, P.KrausFrame (fun σ => K σ i))
    (hexcl : ∀ σ i j, i ≠ j → ψ i σ → ¬ ψ j σ)
    (hdom : ∀ σ i (ρ : PDensity D), (ρ.conj (K σ i)).op ≤ (ρ.conj (J σ)).op)
    (hcomp : ∀ i, validPar ((A i).withClassical φ).toAssn P
      (B.withClassical (ψ i)).toAssn) :
    validPar (kraus φ A K hK).toAssn P
      (krausOne (fun σ => ∃ i, ψ i σ) B J hJ).toAssn := by
  intro s
  let c : Config σT D := Config.init P s
  calc
    expectE (kraus φ A K hK).toAssn.op s ≤ _ := accumOne_pre_le φ A K hK s
    _ ≤ ∑ i, (PostH (c.krausMap (fun σ => K σ i))
        (B.withClassical (ψ i)).toAssn.op + NTH (c.krausMap (fun σ => K σ i))) := by
      apply Finset.sum_le_sum
      intro i _
      exact hcomp i ⟨s.cls, s.q.conj (K s.cls i)⟩
    _ = (∑ i, PostH (c.krausMap (fun σ => K σ i))
        (B.withClassical (ψ i)).toAssn.op) + NTH c := by
      rw [Finset.sum_add_distrib, sum_NTH_krausMap K hK c hframe]
    _ ≤ _ := add_le_add (accumOne_PostH_le ψ B K J hJ hexcl hdom c hframe) le_rfl

end SourceAssertion
end Qhl
