import Qhl.Register.Basic
import Qhl.Dirac.Products
import Qhl.Dirac.WF

/-!
# R-4: register-indexed Dirac constructors

Subgoal R-4 of spec 06: the assertion-side interface of registers. A ket of
the ordered tuple space of a register becomes a `Dirac` element supported on
the register's cells, and a gate becomes a square `Dirac` element there —
the Lean counterparts of CoqQ's `'∣v;x⟩` and `'[A;x]` (`qmem.v:224`).

The step semantics of P-3 never touches `Dirac`: it stays on layer 1
(`EndM D univ`). These constructors are for *stating* assertions and for the
worked examples (E-*), where the well-formedness witnesses below feed the
`WFAt` lemmas of spec 03 directly (rather than typeclass inference — see the
risk register of spec 06 §9).
-/

namespace Qhl

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable {k : ℕ}

namespace Reg

/-- R-4: the ket of a register state, `'∣v;x⟩` of CoqQ `qmem.v:224`. -/
noncomputable def ketD (r : Reg L k) (v : TSpace D r.toFun) : Dirac D := ∣r.vec D v⟩ᴰ

/-- R-4: the bra of a register state. -/
noncomputable def braD (r : Reg L k) (v : TSpace D r.toFun) : Dirac D := ⟨r.vec D v∣ᴰ

/-- R-4: a gate on a register as a Dirac element, `'[A;x]` of CoqQ. -/
noncomputable def linD (r : Reg L k) (A : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun) :
    Dirac D := ⌈r.op D A⌉ᴰ

variable (r : Reg L k)

@[simp]
theorem wf_ketD (v : TSpace D r.toFun) : Dirac.IsKetOn r.sig (r.ketD v) :=
  Dirac.wf_ket _

@[simp]
theorem wf_braD (v : TSpace D r.toFun) : Dirac.IsBraOn r.sig (r.braD v) :=
  Dirac.wf_bra _

@[simp]
theorem wf_linD (A : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun) :
    Dirac.IsSqOn r.sig (r.linD A) :=
  Dirac.wf_ofBlock _

@[simp]
theorem adj_ketD (v : TSpace D r.toFun) : (r.ketD v)†ᴰ = r.braD v :=
  Dirac.adj_ket _

@[simp]
theorem adj_braD (v : TSpace D r.toFun) : (r.braD v)†ᴰ = r.ketD v :=
  Dirac.adj_bra _

@[simp]
theorem adj_linD (A : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun) :
    (r.linD A)†ᴰ = r.linD (LinearMap.adjoint A) := by
  rw [linD, Dirac.adj_ofBlock, adjoint_op, linD]

@[simp]
theorem linD_one : r.linD (1 : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun) = 𝟙ᴰ r.sig := by
  rw [linD, op_one, Dirac.one_eq_ofBlock]

/-- Composition of register gates is composition of Dirac elements. -/
theorem linD_comp (A B : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun) :
    r.linD (A ∘ₗ B) = r.linD A ∘ᴰ r.linD B := by
  rw [linD, linD, linD, op_comp, Dirac.ofBlock_comp]

/-- Applying a register gate to a register ket. -/
theorem linD_comp_ketD (A : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun)
    (v : TSpace D r.toFun) : r.linD A ∘ᴰ r.ketD v = r.ketD (A v) := by
  rw [linD, ketD, ketD, Dirac.ket, Dirac.ket, Dirac.ofBlock_comp, vec, vec,
    comp_toKetM]
  congr 1
  rw [op_apply]
  simp

end Reg

end Qhl
