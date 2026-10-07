import Qhl.Logic.Source.Kraus
import Qhl.Logic.Soundness
import Qhl.Logic.WpChain

/-! # Semantic counterexample to source accumulation with strict definedness -/

namespace Qhl.SourceAccumulationDomainTest

open Qhl

/-- A one-qubit index family for a nonzero density state. -/
abbrev Cell := Fin 1
/-- Each cell has a two-dimensional basis. -/
abbrev Basis (_ : Cell) := Bool
/-- The classical state has one point. -/
abbrev Store := Unit
/-- The identity branch carries the unit effect. -/
noncomputable def input (b : Bool) : SourceAssertion Store Basis :=
  if b then ⟨fun _ => True, fun _ => True, Assn.zero⟩
  else ⟨fun _ => True, fun _ => True, Assn.one⟩
/-- The zero Kraus branch becomes undefined after `skip`. -/
noncomputable def output (b : Bool) : SourceAssertion Store Basis :=
  if b then ⟨fun _ => True, fun _ => False, Assn.zero⟩
  else input false
/-- Accumulated input, with normalized Kraus family `(I, 0)`. -/
noncomputable def accumulatedInput : SourceAssertion Store Basis :=
  SourceAssertion.firstWithZero (fun _ => True) input
/-- Accumulated output with the same normalized Kraus family. -/
noncomputable def accumulatedOutput : SourceAssertion Store Basis :=
  SourceAssertion.firstWithZero (fun _ => True) output
/-- Each component triple is totally valid for `skip`. -/
theorem component_validTot (b : Bool) :
    validTot (input b).toAssn (.skip : Prog Store Basis) (output b).toAssn := by
  cases b <;> simp only [input, output, Bool.false_eq_true, ite_false, ite_true]
  · exact validTot_skip _
  · have hzero :
        (⟨fun _ => True, fun _ => True, Assn.zero⟩ : SourceAssertion Store Basis).toAssn =
          (⟨fun _ => True, fun _ => False, Assn.zero⟩ :
            SourceAssertion Store Basis).toAssn := by
      apply Assn.ext
      funext σ
      simp [SourceAssertion.toAssn, Assn.mask_op_of_pos, Assn.mask_op_of_neg]
    rw [hzero]
    exact validTot_skip _
/-- Every component is also partially valid. -/
theorem component_validPar (b : Bool) :
    validPar (input b).toAssn (.skip : Prog Store Basis) (output b).toAssn :=
  (component_validTot b).validPar
/-- The accumulated precondition is the unit effect. -/
theorem accumulatedInput_eq_one : accumulatedInput.toAssn = Assn.one := by
  apply Assn.ext
  funext σ
  rw [SourceAssertion.toAssn, Assn.mask_op_of_pos]
  · change (SourceAssertion.firstWithZero (fun _ => True) input).quantum.op σ = _
    rw [SourceAssertion.firstWithZero_quantum_op]
    rfl
  · exact ⟨trivial, (SourceAssertion.firstWithZero_defined_iff _ _ _).mpr
      ⟨trivial, trivial⟩⟩
/-- The accumulated postcondition is zero because its zero-weight child is undefined. -/
theorem accumulatedOutput_eq_zero : accumulatedOutput.toAssn = Assn.zero := by
  apply Assn.ext
  funext σ
  rw [SourceAssertion.toAssn, Assn.mask_op_of_neg]
  · rfl
  · intro h
    have hd := (SourceAssertion.firstWithZero_defined_iff _ _ _).mp h.2
    exact hd.2
/-- A concrete normalized one-qubit state. -/
noncomputable def state : CQState Store Basis :=
  ⟨(), PDensity.pure (deltav Basis (default : QIdx Basis (Finset.univ : Finset Cell)))⟩
/-- The concrete witness has unit mass. -/
theorem state_mass : state.q.mass = 1 := by
  apply PDensity.mass_pure
  refine norm_eq_one_of_inner_self ?_
  exact (by simpa using
    (dv_dot (D := Basis) (default : QIdx Basis (Finset.univ : Finset Cell))
      (default : QIdx Basis (Finset.univ : Finset Cell))))
/-- At `skip`, a zero postcondition receives zero terminal expectation. -/
theorem post_zero : PostH (Config.init (.skip : Prog Store Basis) state) Assn.zero.op = 0 := by
  rw [PostH_of_all_done (Config.isDone_init _ _) (fun c' hc' => ?_)
    (fun σ => Assn.zero.isPositive σ)]
  · rw [next_init, stepProg_skip]
    simp [expectE_zero_op, Assn.zero_op]
  · rw [next_init, stepProg_skip] at hc'
    rw [List.mem_singleton.mp hc']
    rfl
/-- `skip` leaves no nontermination mass on the witness. -/
theorem skip_NT_zero : NT (Config.init (.skip : Prog Store Basis) state) = 0 := by
  have hterm := TermH_of_all_done (Config.isDone_init (.skip : Prog Store Basis) state)
    (fun c' hc' => by
      rw [next_init, stepProg_skip] at hc'
      rw [List.mem_singleton.mp hc']
      rfl)
  rw [next_init, stepProg_skip] at hterm
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hterm
  have hbalance := TermH_add_NTH (Config.init (.skip : Prog Store Basis) state)
  rw [hterm] at hbalance
  have hm : (Config.init (.skip : Prog Store Basis) state).mass = state.q.mass := rfl
  rw [hm, state_mass] at hbalance
  change NTH (Config.init (.skip : Prog Store Basis) state) = 0
  simpa using hbalance
/-- The accumulated total-correctness conclusion is false. -/
theorem accumulated_not_validTot :
    ¬ validTot accumulatedInput.toAssn (.skip : Prog Store Basis)
      accumulatedOutput.toAssn := by
  rw [accumulatedInput_eq_one, accumulatedOutput_eq_zero]
  intro h
  have hs := h state
  rw [expectE_one, state_mass, post_zero] at hs
  norm_num at hs
/-- The accumulated partial-correctness conclusion is false as well. -/
theorem accumulated_not_validPar :
    ¬ validPar accumulatedInput.toAssn (.skip : Prog Store Basis)
      accumulatedOutput.toAssn := by
  rw [accumulatedInput_eq_one, accumulatedOutput_eq_zero]
  intro h
  have hs := h state
  rw [expectE_one, state_mass, post_zero, skip_NT_zero] at hs
  norm_num at hs

/-- The semantic total-correctness accumulation inference has a counterexample. -/
theorem semantic_accumulation_total_fails :
    ¬ ((∀ b : Bool, validTot (input b).toAssn (.skip : Prog Store Basis)
        (output b).toAssn) →
      validTot accumulatedInput.toAssn (.skip : Prog Store Basis)
        accumulatedOutput.toAssn) := by
  intro h
  exact accumulated_not_validTot (h component_validTot)

/-- The same component family refutes partial-correctness accumulation. -/
theorem semantic_accumulation_partial_fails :
    ¬ ((∀ b : Bool, validPar (input b).toAssn (.skip : Prog Store Basis)
        (output b).toAssn) →
      validPar accumulatedInput.toAssn (.skip : Prog Store Basis)
        accumulatedOutput.toAssn) := by
  intro h
  exact accumulated_not_validPar (h component_validPar)

#print axioms component_validTot
#print axioms accumulated_not_validTot
#print axioms accumulated_not_validPar
#print axioms semantic_accumulation_total_fails
#print axioms semantic_accumulation_partial_fails

end Qhl.SourceAccumulationDomainTest
