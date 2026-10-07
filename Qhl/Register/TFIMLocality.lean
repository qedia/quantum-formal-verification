import Qhl.Register.TFIM
import Qhl.Register.PauliString

/-! # Locality of the transverse-field Ising Hamiltonian terms -/

namespace Qhl.TrotterTFIM
open Qhl Finset

/-- An `X` term commutes with a `ZZ` term when their cells are disjoint. -/
theorem gateAt_X_comm_regLift_ZZ (n : ℕ) (i a b : QubitL n)
    (hab : a ≠ b) (hia : i ≠ a) (hib : i ≠ b) :
    gateAt (QubitL n) i X *
        regLift (Reg.pair a b hab) (pairGate (D := QubitD n) a b hab ZZ) =
      regLift (Reg.pair a b hab) (pairGate (D := QubitD n) a b hab ZZ) *
        gateAt (QubitL n) i X := by
  classical
  refine linM_ext (QubitD n) fun m => ?_
  let f := bitAt n m
  have hm : m = qbIdx (QubitL n) f := by
    funext j
    exact congrArg m (Subtype.ext rfl)
  have hx (g : QubitL n → Bool) :
      gateAt (QubitL n) i X (deltav (QubitD n) (qbIdx (QubitL n) g)) =
        deltav (QubitD n) (qbIdx (QubitL n) (Function.update g i (!(g i)))) := by
    simpa using gateAt_deltav i X g (c := 1) (by simpa using X_single (g i))
  rw [hm, Module.End.mul_apply, Module.End.mul_apply, regLift_ZZ_deltav,
    map_smul, hx, regLift_ZZ_deltav]
  simp [bitAt, qbIdx, Function.update_of_ne hia.symm, Function.update_of_ne hib.symm]

end Qhl.TrotterTFIM
