import Qhl.Logic.Source.BasicDerived

/-! # The zero-precondition instance of the source convex rule

An empty Convex2 family has zero quantum precondition and postcondition.
It is semantically vacuous and does not establish an algorithmic guarantee.
-/
namespace Qhl
variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)] {σT : Type*}

private def emptyAssertion (φ : σT → Prop) : SourceAssertion σT D :=
  SourceAssertion.ofAssn Assn.zero φ

private theorem emptyConvex_eq (φ : σT → Prop) :
    SourceAssertion.convex φ (fun i : Fin 0 => i.elim0)
      (fun i : Fin 0 => i.elim0) (by simp) = emptyAssertion (D := D) φ := by
  unfold SourceAssertion.convex emptyAssertion SourceAssertion.ofAssn
  congr 1
  · funext σ
    simp

/-- Empty Convex2 followed by source consequence. This statement is vacuous:
the input effect is zero, irrespective of the classical condition. -/
theorem SourceDerivTot.zeroPre (φ : σT → Prop) (P : Prog σT D)
    (B : SourceAssertion σT D) :
    SourceDerivTot (SourceAssertion.ofAssn Assn.zero φ) P B := by
  have h := SourceDerivTot.convex2 φ (fun _ => False)
    (fun i : Fin 0 => i.elim0) (fun i : Fin 0 => i.elim0)
    (fun i : Fin 0 => i.elim0) (by simp) P
    (fun _ _ i => i.elim0) (fun i => i.elim0)
  rw [emptyConvex_eq, emptyConvex_eq] at h
  exact .conseq (SourceAssertion.entails_refl _) h
    ⟨fun _ h => h.elim, fun _ h => h.elim⟩

theorem SourceDerivPar.zeroPre (φ : σT → Prop) (P : Prog σT D)
    (B : SourceAssertion σT D) :
    SourceDerivPar (SourceAssertion.ofAssn Assn.zero φ) P B := by
  have h := SourceDerivPar.convex2 φ (fun _ => False)
    (fun i : Fin 0 => i.elim0) (fun i : Fin 0 => i.elim0)
    (fun i : Fin 0 => i.elim0) (by simp) P
    (fun _ _ i => i.elim0) (fun i => i.elim0)
  rw [emptyConvex_eq, emptyConvex_eq] at h
  exact .conseq (SourceAssertion.entails_refl _) h
    ⟨fun _ h => h.elim, fun _ h => h.elim⟩
end Qhl
