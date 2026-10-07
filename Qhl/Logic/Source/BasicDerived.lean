import Qhl.Logic.Source.RulesSoundness
import Qhl.Logic.UnitaryFull
import Qhl.Logic.AncillaEmbed

/-! # Elementary source derivations for defined quantum predicates

Classical conditions remain explicit. The helpers derive source rules directly
from source constructors and operator facts, without reflecting semantic validity.
-/

namespace Qhl

open Finset

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)] {σT : Type*}

namespace SourceAssertion

/-- A total quantum predicate paired with an explicit classical condition. -/
def ofAssn (A : Assn σT D) (φ : σT → Prop) : SourceAssertion σT D where
  classical := φ
  defined _ := True
  quantum := A

@[simp] theorem toAssn_ofAssn (A : Assn σT D) (φ : σT → Prop) :
    (ofAssn A φ).toAssn = A.mask φ := by
  apply Assn.ext
  funext σ
  change (A.mask (fun τ => φ τ ∧ True)).op σ = (A.mask φ).op σ
  by_cases hφ : φ σ
  · rw [Assn.mask_op_of_pos hφ, Assn.mask_op_of_pos ⟨hφ, trivial⟩]
  · rw [Assn.mask_op_of_neg hφ, Assn.mask_op_of_neg (fun h => hφ h.1)]

@[simp] theorem toAssn_ofAssn_true (A : Assn σT D) :
    (ofAssn A (fun _ => True)).toAssn = A := by
  apply Assn.ext
  funext σ
  exact Assn.mask_op_of_pos ⟨True.intro, True.intro⟩

/-- Entailment between total quantum predicates retains its classical premise. -/
theorem entails_ofAssn (A B : Assn σT D) (φ ψ : σT → Prop)
    (hc : ∀ σ, φ σ → ψ σ) (hq : ∀ σ, φ σ → A.op σ ≤ B.op σ) :
    Entails (ofAssn A φ) (ofAssn B ψ) :=
  ⟨hc, fun σ hφ => ⟨Iff.rfl, fun _ => hq σ hφ⟩⟩

end SourceAssertion

namespace SourceDerivTot

/-- Source unitary and consequence, with distinctness required under the
actual input classical condition. -/
theorem unitary_ofAssn {k : ℕ} (r : RegExpr σT L k)
    (U : ∀ σ, UnitaryOp (TSpace D (r σ)))
    (A B : Assn σT D) (φ ψ : σT → Prop)
    (hc : ∀ σ, φ σ → ψ σ)
    (hdist : ∀ σ, φ σ → Function.Injective (r σ))
    (hq : ∀ σ, φ σ → A.op σ ≤ (B.unitaryPre r U).op σ) :
    SourceDerivTot (SourceAssertion.ofAssn A φ) (.unitary k r U)
      (SourceAssertion.ofAssn B ψ) := by
  refine .conseq ?_ (.unitary r U (SourceAssertion.ofAssn B ψ))
    (SourceAssertion.entails_refl _)
  refine ⟨hc, ?_⟩
  intro σ hφ
  exact ⟨⟨fun _ => ⟨hdist σ hφ, True.intro⟩, fun _ => True.intro⟩,
    fun _ => hq σ hφ⟩

/-- Pure-state unitary rule derived from the source constructors and the
projector conjugation identity. -/
theorem unitary_state {k : ℕ} (r : Reg L k) (U : UnitaryOp (TSpace D r.toFun))
    {v w : HS D (univ : Finset L)} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hU : regLift r (U : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun) v = w) :
    SourceDerivTot (σT := σT)
      (SourceAssertion.ofAssn (Assn.ofState v hv) (fun _ => True))
      (.unitary k (RegExpr.const r) fun _ => U)
      (SourceAssertion.ofAssn (Assn.ofState w hw) (fun _ => True)) := by
  apply unitary_ofAssn _ _ _ _ _ _ (fun _ h => h) (fun _ _ => r.inj)
  intro σ _
  refine le_of_eq (Eq.symm (Eq.trans
    (Assn.unitaryPre_op_of_dist _ _ _ (σ := σ) r.inj) ?_))
  rw [Assn.ofState_op]
  exact adjoint_conj_outerLM_state r U hU

/-- A store-dependent gate transports pure-state families where the classical
condition holds, with register distinctness under that same condition. -/
theorem unitary_stateFam_guard {k : ℕ} (r : RegExpr σT L k)
    (U : ∀ σ, UnitaryOp (TSpace D (r σ)))
    (v w : σT → HS D (univ : Finset L))
    (hv : ∀ σ, ‖v σ‖ = 1) (hw : ∀ σ, ‖w σ‖ = 1) (φ : σT → Prop)
    (hdist : ∀ σ, φ σ → Function.Injective (r σ))
    (hU : ∀ σ (hφ : φ σ),
      regLift ⟨r σ, hdist σ hφ⟩ (U σ) (v σ) = w σ) :
    SourceDerivTot (SourceAssertion.ofAssn (Assn.ofStateFam v hv) φ)
      (.unitary k r U) (SourceAssertion.ofAssn (Assn.ofStateFam w hw) φ) := by
  apply unitary_ofAssn _ _ _ _ _ _ (fun _ h => h) hdist
  intro σ hφ
  refine le_of_eq (Eq.symm (Eq.trans
    (Assn.unitaryPre_op_of_dist _ _ _ (σ := σ) (hdist σ hφ)) ?_))
  rw [Assn.ofStateFam_op]
  exact adjoint_conj_outerLM_state ⟨r σ, hdist σ hφ⟩ (U σ) (hU σ hφ)

/-- Unitary execution preserves an identity predicate and its classical condition. -/
theorem unitary_identity {k : ℕ} (r : RegExpr σT L k)
    (U : ∀ σ, UnitaryOp (TSpace D (r σ))) (φ : σT → Prop)
    (hdist : ∀ σ, φ σ → Function.Injective (r σ)) :
    SourceDerivTot (SourceAssertion.identity (D := D) φ) (.unitary k r U)
      (SourceAssertion.identity (D := D) φ) := by
  apply unitary_ofAssn r U Assn.one Assn.one φ φ (fun _ h => h) hdist
  intro σ hφ
  rw [Assn.unitaryPre_one_op r U (hdist σ hφ), Assn.one_op]

end SourceDerivTot
end Qhl
