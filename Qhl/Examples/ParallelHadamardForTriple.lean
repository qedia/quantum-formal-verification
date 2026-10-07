import Qhl.Logic.Soundness
import Qhl.Register.Qubits
import Qhl.Gate.Qubit

/-! CoqQ `RS_ParaHadamard_tuple0` (`example.v`): `{⊗ᵢ∣0⟩} [for i do [ut i := H]] {⊗ᵢ∣+⟩}` by one
`AxV_UTFP` call; the counted-`while` version is `Qhl/Examples/ParallelHadamardTriple.lean`.

The fixture — the standard `n`-qubit world `QubitD n`, the endpoint states
`allZeros n`/`allPlus n` and their assertion forms `allZerosA`/`allPlusA` — is
the library module `Qhl/Register/Qubits.lean`; all this file adds is the
`H`-instance of the full-coverage `applyOn` collapse and the one rule call. -/

namespace Qhl.ParallelHadamardForTriple

open Finset

variable (n : ℕ)

/-- The `H`-instance of the library's `applyOn_finRange`: the loop list touches
every cell, so hitting each `∣0⟩` factor with `H` gives `∣+⟩` everywhere. -/
theorem applyOn_H :
    applyOn (D := QubitD n) (List.finRange n) (fun _ => H) (fun _ => q0) = fun _ => qplus := by
  rw [applyOn_finRange]
  funext a
  exact H_q0

theorem phForDeriv :
    DerivTot (σT := Unit) (D := QubitD n)
      (allZerosA (QubitL n) Unit)
      [for a < n do [ut a := H]]
      (allPlusA (QubitL n) Unit) :=
  DerivTot.conseq (Assn.ofState_le_ofState rfl)
    (DerivTot.forProg_parallelUnitary (List.finRange n) (List.nodup_finRange n)
      (fun _ => H) (fun _ => q0) fun _ => norm_q0)
    (Assn.ofState_le_ofState (congrArg (prodV (QubitD n)) (applyOn_H n)))

theorem phForValid :
    validTot (σT := Unit) (D := QubitD n)
      (allZerosA (QubitL n) Unit)
      [for a < n do [ut a := H]]
      (allPlusA (QubitL n) Unit) :=
  (phForDeriv n).sound

end Qhl.ParallelHadamardForTriple
