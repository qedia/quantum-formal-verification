import Qhl.Logic.Source.BasicDerived
import Qhl.Logic.WpChain

/-! # Pure-state witnesses for source assertions -/
namespace Qhl
open Finset
open scoped ComplexInnerProductSpace
variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)] {σT : Type*}

/-- A unit-state projector has expectation one on the same state. -/
theorem expectE_ofState_self (v : HS D (univ : Finset L)) (hv : ‖v‖ = 1)
    (σ : σT) :
    expectE (Assn.ofState (σT := σT) v hv).op ⟨σ, PDensity.pure v⟩ = 1 := by
  rw [expectE_pure, Assn.ofState_op, outerLM_apply]
  simp [inner_self_eq_norm_sq_to_K, hv]

/-- A classical witness and a unit state establish source definedness and
positive expectation, without weakening the classical condition. -/
theorem SourceAssertion.ofState_nonvacuous
    (v : HS D (univ : Finset L)) (hv : ‖v‖ = 1)
    (φ : σT → Prop) (σ : σT) (hφ : φ σ) :
    let A := SourceAssertion.ofAssn (Assn.ofState v hv) φ
    ∃ s : CQState σT D, A.classical s.cls ∧ A.defined s.cls ∧
      s.q.mass = 1 ∧ 0 < expectE A.quantum.op s := by
  refine ⟨⟨σ, PDensity.pure v⟩, hφ, trivial, PDensity.mass_pure hv, ?_⟩
  change 0 < expectE (Assn.ofState v hv).op ⟨σ, PDensity.pure v⟩
  rw [expectE_ofState_self v hv σ]
  exact zero_lt_one
end Qhl
