import Qhl.Logic.Source.Nonvacuity
import Qhl.Examples.BellStateTriple
import Qhl.Examples.ParallelHadamardTriple
import Qhl.Examples.ClusterStateTriple
import Qhl.Examples.BKTransformTriple

/-! # Explicit input witnesses for state-preparation examples

These specialize the library projector witness to the unchanged source
preconditions. Existing witnesses for other examples remain in their modules.
-/
namespace Qhl.ExampleNonvacuity
open Finset

/-- The Bell precondition has a mass-one input with positive expectation. -/
theorem bell :
    let A := SourceAssertion.ofAssn BellProgram.P00 (fun _ => True)
    ∃ s : CQState Unit BellProgram.D, A.classical s.cls ∧ A.defined s.cls ∧
      s.q.mass = 1 ∧ 0 < expectE A.quantum.op s :=
  SourceAssertion.ofState_nonvacuous BellProgram.ket00 BellProgram.norm_ket00
    (fun _ => True) () trivial

/-- The parallel-Hadamard precondition accepts the all-zero input. -/
theorem parallelHadamard (n : ℕ) :
    let A := SourceAssertion.ofAssn (ParallelHadamardTriple.P0 n) (fun _ => True)
    ∃ s : CQState ℕ (QubitD n), A.classical s.cls ∧ A.defined s.cls ∧
      s.q.mass = 1 ∧ 0 < expectE A.quantum.op s :=
  SourceAssertion.ofState_nonvacuous (allZerosOn (QubitL n))
    (norm_allZerosOn (QubitL n)) (fun _ => True) 0 trivial

/-- Cluster preparation has the same all-zero input precondition. -/
theorem cluster (n : ℕ) :
    let A := SourceAssertion.ofAssn (allZerosA (QubitL n) ℕ) (fun _ => True)
    ∃ s : CQState ℕ (QubitD n), A.classical s.cls ∧ A.defined s.cls ∧
      s.q.mass = 1 ∧ 0 < expectE A.quantum.op s :=
  SourceAssertion.ofState_nonvacuous (allZerosOn (QubitL n))
    (norm_allZerosOn (QubitL n)) (fun _ => True) 0 trivial

/-- The coherent BK precondition accepts the intended arbitrary input state. -/
theorem bkCoherent (x : ℕ) (ψ : HS (QubitD (2 ^ x)) univ) (hψ : ‖ψ‖ = 1) :
    let A := SourceAssertion.ofAssn (Assn.ofState ψ hψ) (fun _ : ℕ × ℕ => True)
    ∃ s : CQState (ℕ × ℕ) (QubitD (2 ^ x)),
      A.classical s.cls ∧ A.defined s.cls ∧ s.q.mass = 1 ∧
        0 < expectE A.quantum.op s :=
  SourceAssertion.ofState_nonvacuous ψ hψ (fun _ => True) (0, 0) trivial

end Qhl.ExampleNonvacuity

#print axioms Qhl.ExampleNonvacuity.bell
#print axioms Qhl.ExampleNonvacuity.parallelHadamard
#print axioms Qhl.ExampleNonvacuity.cluster
#print axioms Qhl.ExampleNonvacuity.bkCoherent
