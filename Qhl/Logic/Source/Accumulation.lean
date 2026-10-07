import Qhl.Logic.Source.KrausDomain
import Qhl.Logic.Source.TotalLoop
import Qhl.History.KrausSum

/-! # Semantic accumulation with common post domains

These semantic helpers generalize the approved source rule: they require pairwise
domain agreement, while the source constructors require every postpredicate to be
defined under the common classical postcondition. They are not source derivations.
-/

namespace Qhl

open Finset
open scoped ENNReal

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)] {σT : Type*}

namespace SourceAssertion

/-- Semantic total accumulation: common post-definedness permits recombining
component postconditions under an actual structural program frame. -/
theorem validTot_kraus {ι : Type*} [Fintype ι]
    (φ ψ : σT → Prop) (A B : ι → SourceAssertion σT D)
    (K : σT → ι → EndM D (univ : Finset L))
    (hK : ∀ σ, ∑ i, LinearMap.adjoint (K σ i) ∘ₗ K σ i = 1)
    (P : Prog σT D) (hframe : ∀ i, P.KrausFrame (fun σ => K σ i))
    (hdom : ∀ σ, ψ σ → ∀ i j, (B i).defined σ ↔ (B j).defined σ)
    (hcomp : ∀ i, validTot ((A i).withClassical φ).toAssn P
      ((B i).withClassical ψ).toAssn) :
    validTot (kraus φ A K hK).toAssn P (kraus ψ B K hK).toAssn := by
  intro s
  let c : Config σT D := Config.init P s
  let C : ι → Assn σT D := fun i => ((B i).withClassical ψ).toAssn
  have hpre : expectE (kraus φ A K hK).toAssn.op s ≤
      ∑ i, expectE ((A i).withClassical φ).toAssn.op
        ⟨s.cls, s.q.conj (K s.cls i)⟩ := by
    calc
      expectE (kraus φ A K hK).toAssn.op s ≤
          expectE (fun σ => ∑ i, LinearMap.adjoint (K σ i) ∘ₗ
            ((A i).withClassical φ).toAssn.op σ ∘ₗ K σ i) s := by
        apply expectE_mono
        intro σ
        exact kraus_toAssn_op_le_sum_mask φ A K hK σ
      _ = _ := by
        apply expectE_kraus_sum
        intro i σ
        exact ((A i).withClassical φ).toAssn.isPositive σ
  have hpost : PostH c (kraus ψ B K hK).toAssn.op =
      ∑ i, PostH (c.krausMap (fun σ => K σ i)) (C i).op := by
    calc
      PostH c (kraus ψ B K hK).toAssn.op =
          PostH c (fun σ => ∑ i, LinearMap.adjoint (K σ i) ∘ₗ
            (C i).op σ ∘ₗ K σ i) := by
        congr 1
        funext σ
        exact kraus_toAssn_op_eq_sum_mask_of_domains ψ B K hK hdom σ
      _ = _ := (sum_PostH_krausMap K C c (fun i => hframe i)).symm
  calc
    expectE (kraus φ A K hK).toAssn.op s ≤ _ := hpre
    _ ≤ ∑ i, PostH (c.krausMap (fun σ => K σ i)) (C i).op := by
      apply Finset.sum_le_sum
      intro i _
      exact hcomp i ⟨s.cls, s.q.conj (K s.cls i)⟩
    _ = PostH c (kraus ψ B K hK).toAssn.op := hpost.symm

/-- Semantic partial accumulation, retaining branch nontermination through
normalization and the actual framed operational semantics. -/
theorem validPar_kraus {ι : Type*} [Fintype ι]
    (φ ψ : σT → Prop) (A B : ι → SourceAssertion σT D)
    (K : σT → ι → EndM D (univ : Finset L))
    (hK : ∀ σ, ∑ i, LinearMap.adjoint (K σ i) ∘ₗ K σ i = 1)
    (P : Prog σT D) (hframe : ∀ i, P.KrausFrame (fun σ => K σ i))
    (hdom : ∀ σ, ψ σ → ∀ i j, (B i).defined σ ↔ (B j).defined σ)
    (hcomp : ∀ i, validPar ((A i).withClassical φ).toAssn P
      ((B i).withClassical ψ).toAssn) :
    validPar (kraus φ A K hK).toAssn P (kraus ψ B K hK).toAssn := by
  intro s
  let c : Config σT D := Config.init P s
  let C : ι → Assn σT D := fun i => ((B i).withClassical ψ).toAssn
  have hpre : expectE (kraus φ A K hK).toAssn.op s ≤
      ∑ i, expectE ((A i).withClassical φ).toAssn.op
        ⟨s.cls, s.q.conj (K s.cls i)⟩ := by
    calc
      expectE (kraus φ A K hK).toAssn.op s ≤
          expectE (fun σ => ∑ i, LinearMap.adjoint (K σ i) ∘ₗ
            ((A i).withClassical φ).toAssn.op σ ∘ₗ K σ i) s := by
        apply expectE_mono
        intro σ
        exact kraus_toAssn_op_le_sum_mask φ A K hK σ
      _ = _ := by
        apply expectE_kraus_sum
        intro i σ
        exact ((A i).withClassical φ).toAssn.isPositive σ
  have hpost : PostH c (kraus ψ B K hK).toAssn.op =
      ∑ i, PostH (c.krausMap (fun σ => K σ i)) (C i).op := by
    calc
      PostH c (kraus ψ B K hK).toAssn.op =
          PostH c (fun σ => ∑ i, LinearMap.adjoint (K σ i) ∘ₗ
            (C i).op σ ∘ₗ K σ i) := by
        congr 1
        funext σ
        exact kraus_toAssn_op_eq_sum_mask_of_domains ψ B K hK hdom σ
      _ = _ := (sum_PostH_krausMap K C c (fun i => hframe i)).symm
  have hnt : (∑ i, NTH (c.krausMap (fun σ => K σ i))) = NTH c := by
    apply sum_NTH_krausMap K
    · exact hK
    · intro i
      exact hframe i
  calc
    expectE (kraus φ A K hK).toAssn.op s ≤ _ := hpre
    _ ≤ ∑ i, (PostH (c.krausMap (fun σ => K σ i)) (C i).op +
        NTH (c.krausMap (fun σ => K σ i))) := by
      apply Finset.sum_le_sum
      intro i _
      exact hcomp i ⟨s.cls, s.q.conj (K s.cls i)⟩
    _ = PostH c (kraus ψ B K hK).toAssn.op + NTH c := by
      rw [Finset.sum_add_distrib, ← hpost, hnt]

end SourceAssertion

end Qhl
