import Qhl.Gate.ControlledU

/-!
# The repeat-until-success dilation block `(X ⊗ 1) · control V · (H ⊗ 1)`

The gate-level layer of a repeat-until-success (RUS) circuit: the two-wire
block that *attempts* a one-shot application of a gate `V` to a target wire,
flagging success on an ancilla wire.

```
uRus V := (X ⊗ 1) · (control V) · (H ⊗ 1)
```

with the ancilla as the **first** (control) factor of
`EuclideanSpace ℂ (Bool × β)` and the target as the second. Everything is
generic in the target space `EuclideanSpace ℂ β` and in the gate `V`; the
control wire is a single qubit, so the product states are the `vpair`s of
`Qhl/Gate/Phase.lean` and the two constituents are the library gates
`fstU` (`G ⊗ 1`) and `control` (CoqQ `BControl`) of `Qhl/Gate/ControlledU.lean`
— whose own docstring already names this block as the intended use.

The three action laws below are the entire quantum content of an RUS circuit,
and each is a three-step chain of the *named* action lemmas of the gate layer
(`fstU_vpair`, `H_qbit`-family, `control_vpair_q0`/`control_vpair_q1`,
`X_q0`/`X_q1`) — no matrix entry is ever evaluated:

* `uRus_vpair_qminus` — the **success** profile read backwards: the ancilla
  factor `∣-⟩` is the one the block sends to `∣0⟩` with `V` applied to the
  target (`H∣-⟩ = ∣1⟩`, so the controlled gate fires, and `X∣1⟩ = ∣0⟩`);
* `uRus_vpair_qplus` — the **retry** profile read backwards: the ancilla factor
  `∣+⟩` is the one the block sends to `∣1⟩` with the target *untouched*
  (`H∣+⟩ = ∣0⟩`, the controlled gate is the identity, `X∣0⟩ = ∣1⟩`);
* `uRus_vpair_q0` — the forward reading the algorithm is usually stated with:
  `uRus V (∣0⟩ ⊗ χ) = 2^{-1/2}(∣0⟩ ⊗ Vχ + ∣1⟩ ⊗ χ)`, so a computational-basis
  measurement of the ancilla yields the outcome `0` — "success", target now
  `Vχ` — with probability `½`, and otherwise restores `χ` exactly.

Nothing here mentions a program, a register, a world or a Hoare triple: this is
the gate algebra only (ownership test), exactly as `Qhl/Gate/ControlledU.lean`
is the gate algebra of phase estimation.
-/

namespace Qhl

section RUSBlock

variable {β : Type*} [Fintype β] [DecidableEq β]

/-- The RUS dilation block `(X ⊗ 1) · (control V) · (H ⊗ 1)` on
`EuclideanSpace ℂ (Bool × β)`: the ancilla (first factor) is put in `∣+⟩`, the
target gets `V` when the ancilla reads `∣1⟩`, and the final `X` on the ancilla
makes the *successful* outcome the computational-basis outcome `0`.

In matrix form (ancilla-major blocks) `2^{-1/2} [[V, −V], [1, 1]]`. -/
noncomputable def uRus (V : UnitaryOp (EuclideanSpace ℂ β)) :
    UnitaryOp (EuclideanSpace ℂ (Bool × β)) :=
  fstU (β := β) X * control V * fstU (β := β) H

/-- **The success profile.** `∣-⟩ ⊗ χ` is the input the block sends to
`∣0⟩ ⊗ Vχ`: `H∣-⟩ = ∣1⟩` fires the controlled gate, and the closing `X` turns
the ancilla `∣1⟩` into `∣0⟩`. Read backwards, this is the branch a measurement
outcome `0` on the ancilla selects. -/
theorem uRus_vpair_qminus (V : UnitaryOp (EuclideanSpace ℂ β)) (χ : EuclideanSpace ℂ β) :
    (uRus V : EuclideanSpace ℂ (Bool × β) →ₗ[ℂ] EuclideanSpace ℂ (Bool × β))
        (vpair qminus χ)
      = vpair q0 ((V : EuclideanSpace ℂ β →ₗ[ℂ] EuclideanSpace ℂ β) χ) := by
  rw [uRus, UnitaryOp.coe_mul, UnitaryOp.coe_mul, LinearMap.comp_apply, LinearMap.comp_apply,
    fstU_vpair, H_qminus, control_vpair_q1, fstU_vpair, X_q1]

/-- **The retry profile.** `∣+⟩ ⊗ χ` is the input the block sends to
`∣1⟩ ⊗ χ`: `H∣+⟩ = ∣0⟩` leaves the controlled gate idle, so the target is
restored *exactly*, and the closing `X` turns the ancilla `∣0⟩` into `∣1⟩`. -/
theorem uRus_vpair_qplus (V : UnitaryOp (EuclideanSpace ℂ β)) (χ : EuclideanSpace ℂ β) :
    (uRus V : EuclideanSpace ℂ (Bool × β) →ₗ[ℂ] EuclideanSpace ℂ (Bool × β))
        (vpair qplus χ) = vpair q1 χ := by
  rw [uRus, UnitaryOp.coe_mul, UnitaryOp.coe_mul, LinearMap.comp_apply, LinearMap.comp_apply,
    fstU_vpair, H_qplus, control_vpair_q0, fstU_vpair, X_q0]

/-- **The forward reading**, the one the algorithm is usually stated with:

```
uRus V (∣0⟩ ⊗ χ) = 2^{-1/2} (∣0⟩ ⊗ Vχ + ∣1⟩ ⊗ χ).
```

Measuring the ancilla in the computational basis therefore yields `0` — the
success flag, with the target now carrying `Vχ` — with probability `½`, and
otherwise leaves the target in `χ` unchanged, ready for another attempt. -/
theorem uRus_vpair_q0 (V : UnitaryOp (EuclideanSpace ℂ β)) (χ : EuclideanSpace ℂ β) :
    (uRus V : EuclideanSpace ℂ (Bool × β) →ₗ[ℂ] EuclideanSpace ℂ (Bool × β)) (vpair q0 χ)
      = (Real.sqrt 2 : ℂ)⁻¹ •
          (vpair q0 ((V : EuclideanSpace ℂ β →ₗ[ℂ] EuclideanSpace ℂ β) χ) + vpair q1 χ) := by
  rw [uRus, UnitaryOp.coe_mul, UnitaryOp.coe_mul, LinearMap.comp_apply, LinearMap.comp_apply,
    fstU_vpair, H_q0, qplus, vpair_smul_left, vpair_add_left, map_smul, map_add,
    control_vpair_q0, control_vpair_q1, map_smul, map_add, fstU_vpair, fstU_vpair, X_q0, X_q1]
  rw [add_comm (vpair q1 χ)]

end RUSBlock

end Qhl
