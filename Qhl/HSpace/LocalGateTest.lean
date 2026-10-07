import Qhl.HSpace.LocalGate
import Qhl.Gate.Qubit

/-!
# Smoke test: the block bridge at arity two, with an entangling gate

This file is the committed evidence that the arity-general block bridge of
`Qhl.HSpace.LocalGate` really is arity-general and really tolerates operators
that **entangle** the cells of the block: it instantiates
`liftF_regGate_prodV` at a two-cell register with `CNOT` on it.

No general theory lives here — the two theorems below are pure
instantiations, kept as named `theorem`s so that `#print axioms` can target
them.
-/

namespace Qhl

namespace LocalGateTest

open Finset

/-- A world of three qubit cells: the gate acts on cells 0 and 1; cell 2 is the
fixed complement. -/
abbrev L3 : Type := Fin 3

/-- Every cell of the test world is a qubit. -/
abbrev D3 : L3 → Type := fun _ => Bool

/-- The two-cell register on cells 0 and 1. -/
def r01 : Reg L3 2 := Reg.pair 0 1 (by decide)

/-- `CNOT` moved onto the tuple space of the two-cell register — a genuinely
ENTANGLING two-cell gate. -/
noncomputable def cnot01 : UnitaryOp (TSpace D3 r01.toFun) :=
  euclCongrOp (finTwoArrowEquiv Bool).symm CNOT

/-- The block bridge at arity two with an entangling gate: lifted to any
ambient set `W` containing both cells, `cnot01` acts on the two-cell block of a
product state and fixes every other cell. The right-hand side keeps the split
form because `CNOT` entangles the block. -/
theorem blockBridge_pair {W : Finset L3} (h : r01.sig ⊆ W)
    (ψ : ∀ i, EuclideanSpace ℂ (D3 i)) :
    liftF D3 h (r01.op D3 (cnot01 : TSpace D3 r01.toFun →ₗ[ℂ] TSpace D3 r01.toFun))
        (prodV D3 (W := W) ψ)
      = castH D3 (union_sdiff_of_subset h)
          (tenv D3
            (r01.op D3 (cnot01 : TSpace D3 r01.toFun →ₗ[ℂ] TSpace D3 r01.toFun)
              (prodV D3 (W := r01.sig) ψ))
            (prodV D3 (W := W \ r01.sig) ψ)) :=
  liftF_regGate_prodV D3 r01 h cnot01 ψ

/-- The whole-world instance of `blockBridge_pair`: this is the shape the
program semantics needs, since its `regLift r A` is
`liftF D (subset_univ r.sig) (r.op D A)` definitionally. -/
theorem blockBridge_pair_univ (ψ : ∀ i, EuclideanSpace ℂ (D3 i)) :
    liftF D3 (subset_univ r01.sig)
        (r01.op D3 (cnot01 : TSpace D3 r01.toFun →ₗ[ℂ] TSpace D3 r01.toFun))
        (prodV D3 (W := (univ : Finset L3)) ψ)
      = castH D3 (union_sdiff_of_subset (subset_univ r01.sig))
          (tenv D3
            (r01.op D3 (cnot01 : TSpace D3 r01.toFun →ₗ[ℂ] TSpace D3 r01.toFun)
              (prodV D3 (W := r01.sig) ψ))
            (prodV D3 (W := (univ : Finset L3) \ r01.sig) ψ)) :=
  blockBridge_pair (subset_univ r01.sig) ψ

end LocalGateTest

end Qhl
