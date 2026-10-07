import Qhl.Examples.MeasureLoop
import Qhl.Logic.Source.RulesSoundness

/-! Independent regressions for strict masking and all-outcome source measurement.
Run with `python3 scripts/prover_check.py lean scripts/measurement_mask_check.lean`.
-/

namespace Qhl.MeasurementMaskCheck

abbrev Store := Fin 2 × Bool
abbrev D := MeasureLoop.D

def r : RegExpr Store MeasureLoop.L 1 := fun _ => MeasureLoop.rq false

noncomputable def M (σ : Store) : QMeasure 2 (TSpace D (r σ)) :=
  MeasureLoop.meas false

def x : SourceVariable Store (Fin 2) := SourceVariable.fst

def selected (_ : Store) (i : Fin 2) : Bool := decide (i = 0)

/-- This operand is undefined at outcome one, regardless of its ghost bit. -/
def partialOperand : SourceAssertion Store D :=
  { SourceAssertion.identity (fun _ => True) with defined := fun σ => σ.1 = 0 }

/-- Zero multiplication does not repair an undefined source operand. -/
theorem falseMask_undefined :
    ¬ (partialOperand.quantumMask (fun _ => False)).defined (1, true) := by
  change (1 : Fin 2) ≠ 0
  decide

/-- The same undefined masked source predicate nevertheless interprets as zero. -/
theorem falseMask_zero :
    (partialOperand.quantumMask (fun _ => False)).toAssn.op (1, true) = 0 := by
  simp [SourceAssertion.toAssn, SourceAssertion.quantumMask,
    partialOperand, SourceAssertion.identity, Assn.mask]

/-- The old selected rule's precondition has a genuine domain at this store. -/
theorem selected_defined :
    (partialOperand.measureSelectedPreSource r M x.set selected).defined (0, true) := by
  constructor
  · exact MeasureLoop.distQ false
  · intro i hi
    have heq : i = 0 := of_decide_eq_true hi
    subst i
    rfl

/-- Masking unselected outcomes leaves the all-outcome classical premise true. -/
theorem allMasked_classical :
    ((partialOperand.quantumMask (fun σ => σ.1 = 0)).measureAllPreSource
      r M x.set).classical (0, true) := by
  intro i
  trivial

/-- Strict all-outcome measurement still sees the undefined unselected operand. -/
theorem allMasked_undefined :
    ¬ ((partialOperand.quantumMask (fun σ => σ.1 = 0)).measureAllPreSource
      r M x.set).defined (0, true) := by
  intro h
  have impossible : (1 : Fin 2) = 0 := h.2 1
  exact (by decide : (1 : Fin 2) ≠ 0) impossible

/-- A partial domain that is preserved by every outcome update. -/
def post : SourceAssertion Store D :=
  { SourceAssertion.identity (fun _ => True) with defined := fun σ => σ.2 = true }

noncomputable def pre : SourceAssertion Store D :=
  (post.quantumMask (fun σ => σ.1 = 0)).measureAllPreSource r M x.set

noncomputable def program : Prog Store D := .measure 2 1 r M x.set

def finalPost : SourceAssertion Store D :=
  post.withClassical (fun σ => post.classical σ ∧ σ.1 = 0)

/-- The soundness fixture has a nonempty domain, so it is not vacuous everywhere. -/
theorem pre_defined : pre.defined (1, true) :=
  ⟨MeasureLoop.distQ false, fun _ => rfl⟩

/-- The same fixture retains its missing domain on the false ghost bit. -/
theorem pre_undefined : ¬ pre.defined (1, false) := by
  intro h
  have impossible : false = true := h.2 0
  cases impossible

/-- Both new principal rules occur in this partial-correctness derivation. -/
theorem derivPar : SourceDerivPar pre program finalPost :=
  .mask (fun σ : Store => σ.1 = 0)
    (.measureAll r M x (post.quantumMask (fun σ => σ.1 = 0)))

/-- Both new principal rules occur in this total-correctness derivation. -/
theorem derivTot : SourceDerivTot pre program finalPost :=
  .mask (fun σ : Store => σ.1 = 0)
    (.measureAll r M x (post.quantumMask (fun σ => σ.1 = 0)))

theorem soundPar : validPar pre.toAssn program finalPost.toAssn := derivPar.sound

theorem soundTot : validTot pre.toAssn program finalPost.toAssn := derivTot.sound

#print axioms falseMask_undefined
#print axioms falseMask_zero
#print axioms selected_defined
#print axioms allMasked_undefined
#print axioms soundPar
#print axioms soundTot

end Qhl.MeasurementMaskCheck
