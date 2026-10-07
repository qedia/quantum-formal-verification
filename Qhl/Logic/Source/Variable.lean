import Qhl.Logic.Source.Assertion

/-! # Classical assignment and freshness in the shallow source language -/

namespace Qhl

/-- A classical variable interpreted by a lawful read and ordinary assignment. -/
structure SourceVariable (σT V : Type*) where
  get : σT → V
  set : V → σT → σT
  get_set : ∀ v σ, get (set v σ) = v
  set_get : ∀ σ, set (get σ) σ = σ
  set_set : ∀ v w σ, set v (set w σ) = set v σ

namespace SourceVariable

/-- Two distinct variable interpretations have independent reads and writes. -/
def Independent {σT V W : Type*} (x : SourceVariable σT V)
    (y : SourceVariable σT W) : Prop :=
  (∀ v σ, y.get (x.set v σ) = y.get σ) ∧
  (∀ w σ, x.get (y.set w σ) = x.get σ) ∧
  (∀ v w σ, x.set v (y.set w σ) = y.set w (x.set v σ))

/-- Ordinary assignment in a store of variable values. -/
def named {V N : Type*} [DecidableEq N] (name : N) : SourceVariable (N → V) V where
  get σ := σ name
  set v σ := Function.update σ name v
  get_set v σ := Function.update_self name v σ
  set_get σ := Function.update_eq_self name σ
  set_set v w σ := Function.update_idem w v σ

/-- Distinct names give independent classical variables. -/
theorem independent_named {V N : Type*} [DecidableEq N] {x y : N} (h : x ≠ y) :
    Independent (named (V := V) x) (named (V := V) y) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v σ
    exact Function.update_of_ne h.symm v σ
  · intro w σ
    exact Function.update_of_ne h w σ
  · intro v w σ
    exact (Function.update_comm h v w σ).symm

/-- First variable of a product store. -/
def fst {V W : Type*} : SourceVariable (V × W) V where
  get := Prod.fst
  set v σ := (v, σ.2)
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- Second variable of a product store, usable as a fresh ghost. -/
def snd {V W : Type*} : SourceVariable (V × W) W where
  get := Prod.snd
  set w σ := (σ.1, w)
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- Product components have independent reads and writes. -/
theorem independent_fst_snd {V W : Type*} :
    Independent (fst : SourceVariable (V × W) V) snd :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩

end SourceVariable

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable {σT V : Type*}

/-- Semantic interpretation of a variable being absent from the classical and
quantum assertion: writing it changes neither truth nor domain nor on-domain effect. -/
def SourceAssertion.FreshFor (A : SourceAssertion σT D) (y : SourceVariable σT V) : Prop :=
  ∀ v σ, (A.classical (y.set v σ) ↔ A.classical σ) ∧
    (A.defined (y.set v σ) ↔ A.defined σ) ∧
    (A.defined σ → A.quantum.op (y.set v σ) = A.quantum.op σ)

/-- Extend an assertion by an unused product component. -/
def SourceAssertion.withGhost (A : SourceAssertion σT D) (V : Type*) :
    SourceAssertion (σT × V) D where
  classical σ := A.classical σ.1
  defined σ := A.defined σ.1
  quantum := ⟨fun σ => A.quantum.op σ.1, fun σ => A.quantum.isEffect σ.1⟩

/-- The added product component is fresh for the extended assertion. -/
theorem SourceAssertion.withGhost_fresh (A : SourceAssertion σT D) (V : Type*) :
    (A.withGhost V).FreshFor SourceVariable.snd :=
  fun _ _ => ⟨Iff.rfl, Iff.rfl, fun _ => rfl⟩

end Qhl
