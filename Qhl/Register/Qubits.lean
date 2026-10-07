import Qhl.Logic.ForRule
import Qhl.Gate.Qubit

/-!
# The standard labelled qubit system

The fixture every qubit example of this library repeats, packaged once. Nothing
here is new mathematics: it is assembled purely from the existing atoms
`prodV`/`⨂ᵥ` (`Qhl/HSpace/LocalGate.lean`), `Assn.ofState`/`applyOn`
(`Qhl/Logic/ForRule.lean`), the qubit kets `q0`/`qplus` (`Qhl/Gate/Qubit.lean`)
and the one-site register lift `regLift ∘ singleGate` (`Qhl/Register/Basic.lean`,
`Qhl/Program/Step.lean`).

* **Layer 1**, generic in the label type `L`: the all-qubit world
  `QubitCells L = fun _ => Bool`, the two product states `allZerosOn`
  (`⊗ᵢ ∣0⟩`) and `allPlusOn` (`⊗ᵢ ∣+⟩`) with their norms and coordinates, their
  assertion forms `allZerosA`/`allPlusA`, and the one-site gate `gateAt a U`
  with its unitarity and its action on a product state.
* **Layer 2**, the standard concrete `n`-qubit world `QubitL n = Fin n`: the
  same objects with `Fintype.card` already collapsed to `n`, kept concrete so
  that a reader can inspect them.

CoqQ flavour: `allZerosOn`/`allPlusOn` are CoqQ's `tuple_i ∣0⟩` idiom — the
`tentv`/`tenvm` product of a constant family (`hstensor.v:950`), the very state
`RS_ParaHadamard_tuple0` (`example/coqq_paper/example.v`) starts and ends in —
and `gateAt` is `lift_lf` (`hstensor.v:3390`) of `tf2f` (`qmem.v:157`) at a
one-site register, i.e. CoqQ's `[ut x.[i] := U]` operator.

Everything is generic in the gate `U`: no particular gate, and no example
fixture, occurs anywhere in this file.
-/

namespace Qhl

open Finset

/-! ## Layer 1: the generic all-qubit world -/

/-- Every site of the world carries a qubit: the constant cell-type family
`fun _ => Bool`, whose labelled space `HS (QubitCells L) univ` is the
`Fintype.card L`-qubit space. -/
abbrev QubitCells (L : Type*) : L → Type := fun _ => Bool

section Generic

variable (L : Type*) [Fintype L] [DecidableEq L]

/-- The all-zero product state `⊗ᵢ ∣0⟩` of the world `L` (CoqQ's
`tentv_tuple`/`tuple_i ∣0⟩`). -/
noncomputable def allZerosOn : HS (QubitCells L) (univ : Finset L) := ⨂ᵥ _, q0

/-- The all-plus product state `⊗ᵢ ∣+⟩` of the world `L`. -/
noncomputable def allPlusOn : HS (QubitCells L) (univ : Finset L) := ⨂ᵥ _, qplus

/-- `⊗ᵢ ∣0⟩` is a unit vector (library `norm_prodV`, CoqQ `tenvm_norm`). -/
@[simp]
theorem norm_allZerosOn : ‖allZerosOn L‖ = 1 := norm_prodV_eq_one _ fun _ => norm_q0

/-- `⊗ᵢ ∣+⟩` is a unit vector (library `norm_prodV`, CoqQ `tenvm_norm`). -/
@[simp]
theorem norm_allPlusOn : ‖allPlusOn L‖ = 1 := norm_prodV_eq_one _ fun _ => norm_qplus

/-- `⊗ᵢ ∣0⟩` is the computational basis state at the all-`false` classical
state: a product of `∣0⟩`-indicators is a delta (library `prodV_single`, CoqQ
`t2tv_tuple`). -/
theorem allZerosOn_eq_deltav :
    allZerosOn L = deltav (QubitCells L) fun _ => false :=
  prodV_single (QubitCells L) _

/-- Every coordinate of `⊗ᵢ ∣+⟩` is `2^{-card L/2}`: the uniform
superposition. -/
theorem allPlusOn_apply (l : QIdx (QubitCells L) (univ : Finset L)) :
    allPlusOn L l = ((Real.sqrt 2 : ℂ)⁻¹) ^ Fintype.card L := by
  rw [allPlusOn, prodV_apply,
    Finset.prod_congr rfl (g := fun _ => (Real.sqrt 2 : ℂ)⁻¹) fun i _ => by
      cases l i <;> simp [qplus]]
  simp

/-- The assertion "the world is in `⊗ᵢ ∣0⟩`". -/
noncomputable def allZerosA (σT : Type*) : Assn σT (QubitCells L) :=
  Assn.ofState (allZerosOn L) (norm_allZerosOn L)

/-- The assertion "the world is in `⊗ᵢ ∣+⟩`". -/
noncomputable def allPlusA (σT : Type*) : Assn σT (QubitCells L) :=
  Assn.ofState (allPlusOn L) (norm_allPlusOn L)

@[simp]
theorem allZerosA_op (σT : Type*) (σ : σT) :
    (allZerosA L σT).op σ = outerLM (allZerosOn L) (allZerosOn L) := rfl

@[simp]
theorem allPlusA_op (σT : Type*) (σ : σT) :
    (allPlusA L σT).op σ = outerLM (allPlusOn L) (allPlusOn L) := rfl

/-- The gate `U` applied at the site `a` and extended to the whole world: the
one-site register lift `regLift (Reg.single a) ∘ singleGate`, CoqQ's `lift_lf`
of `tf2f` at a one-site register. -/
noncomputable def gateAt (a : L) (U : UnitaryOp 𝕢) :
    EndM (QubitCells L) (univ : Finset L) :=
  regLift (Reg.single a) (singleGate (QubitCells L) a U)

/-- A one-site gate is unitary on the whole world (R-3 + W6). -/
theorem isUnitary_gateAt (a : L) (U : UnitaryOp 𝕢) : IsUnitary (gateAt L a U) :=
  isUnitary_regLift _ _

/-- **The one-site bridge**, in the qubit fixture: `gateAt a U` acts on the one
factor of a product state that it names and fixes every other factor. Library
`regLift_singleGate_prodV`, CoqQ `tentf_tuple_apply` under `lift_lf`. -/
theorem gateAt_prodV (a : L) (U : UnitaryOp 𝕢)
    (ψ : ∀ i : L, EuclideanSpace ℂ (QubitCells L i)) :
    gateAt L a U (prodV (QubitCells L) ψ)
      = prodV (QubitCells L) (Function.update ψ a ((U : 𝕢 →ₗ[ℂ] 𝕢) (ψ a))) :=
  regLift_singleGate_prodV (D := QubitCells L) a U ψ

omit [Fintype L] in
/-- Full coverage collapses `applyOn`: if the list touches every site, the
transformed family is the gate applied at every site — CoqQ's
`\ten_i '[Uf i; x i]` with no site left out. -/
theorem applyOn_of_forall_mem {D : L → Type*} [∀ i, Fintype (D i)] {l : List L}
    (hl : ∀ a, a ∈ l) (U : ∀ a : L, UnitaryOp (EuclideanSpace ℂ (D a)))
    (ψ : ∀ a : L, EuclideanSpace ℂ (D a)) :
    applyOn l U ψ
      = fun a => (U a : EuclideanSpace ℂ (D a) →ₗ[ℂ] EuclideanSpace ℂ (D a)) (ψ a) :=
  funext fun a => if_pos (hl a)

end Generic

/-! ## Layer 2: the standard `n`-qubit world -/

/-- The labels of the standard `n`-qubit world. -/
abbrev QubitL (n : ℕ) : Type := Fin n

/-- The cell types of the standard `n`-qubit world: `n` qubits. -/
abbrev QubitD (n : ℕ) : QubitL n → Type := fun _ => Bool

variable (n : ℕ)

/-- The all-zero state `⊗ᵢ ∣0⟩` of the standard `n`-qubit world. -/
noncomputable def allZeros : HS (QubitD n) (univ : Finset (QubitL n)) :=
  allZerosOn (QubitL n)

/-- The all-plus state `⊗ᵢ ∣+⟩` of the standard `n`-qubit world. -/
noncomputable def allPlus : HS (QubitD n) (univ : Finset (QubitL n)) :=
  allPlusOn (QubitL n)

/-- `⊗ᵢ ∣0⟩` is a unit vector. -/
@[simp]
theorem norm_allZeros : ‖allZeros n‖ = 1 := norm_allZerosOn (QubitL n)

/-- `⊗ᵢ ∣+⟩` is a unit vector. -/
@[simp]
theorem norm_allPlus : ‖allPlus n‖ = 1 := norm_allPlusOn (QubitL n)

/-- `⊗ᵢ ∣0⟩` is the computational basis state at the all-`false` classical
state. -/
theorem allZeros_eq_deltav : allZeros n = deltav (QubitD n) fun _ => false :=
  allZerosOn_eq_deltav (QubitL n)

/-- Every coordinate of the `n`-qubit `⊗ᵢ ∣+⟩` is `2^{-n/2}`. -/
theorem allPlus_apply (l : QIdx (QubitD n) (univ : Finset (QubitL n))) :
    allPlus n l = ((Real.sqrt 2 : ℂ)⁻¹) ^ n :=
  (allPlusOn_apply (QubitL n) l).trans (by rw [Fintype.card_fin])

/-- The standard `n`-qubit loop list touches every site, so `applyOn` over it
is the gate family applied everywhere. -/
theorem applyOn_finRange (U : QubitL n → UnitaryOp 𝕢) (ψ : QubitL n → 𝕢) :
    applyOn (D := QubitD n) (List.finRange n) U ψ
      = fun a => (U a : 𝕢 →ₗ[ℂ] 𝕢) (ψ a) :=
  applyOn_of_forall_mem (QubitL n) List.mem_finRange U ψ

/-! ## Layer 3: the counter-to-cell reading of a counted loop

A counted `while` loop (`Qhl/Logic/CountedWhile.lean`) stores its counter in
the classical store as an unbounded `ℕ`, so the store-dependent register
expression of its body must read a **cell** off an arbitrary counter value.
`cell n k` is that reading: the `k`-th cell for the counter values the loop
guard lets through (`k < n`), with wrap-around keeping the register expression
total — which is what forces `n ≥ 1` (`[NeZero n]`). -/

section Cell

variable [NeZero n]

/-- The cell a counted loop touches at counter value `k`. -/
def cell (k : ℕ) : QubitL n := ⟨k % n, Nat.mod_lt _ (NeZero.pos n)⟩

/-- Below the loop bound the reading is the counter itself. -/
theorem cell_val {k : ℕ} (hk : k < n) : ((cell n k : QubitL n) : ℕ) = k :=
  Nat.mod_eq_of_lt hk

theorem cell_eq_mk {k : ℕ} (hk : k < n) : cell n k = ⟨k, hk⟩ :=
  Fin.ext (cell_val n hk)

/-- Distinct in-range counter values touch distinct cells. -/
theorem cell_ne {a b : ℕ} (ha : a < n) (hb : b < n) (hab : a ≠ b) :
    cell n a ≠ cell n b := by
  intro h
  refine hab ?_
  have hv := congrArg Fin.val h
  rwa [cell_val n ha, cell_val n hb] at hv

end Cell

/-! ## Layer 4: the `∣+⟩`-staircase family of a cell-by-cell Hadamard pass

The generic invariant of any cell-by-cell Hadamard pass on the standard
`n`-qubit world: after `k` passes the first `k` cells are `∣+⟩`, the rest
still `∣0⟩`.  Names no program — the loop-invariant family every
Hadamard-layer counted `while` reuses. -/

section Staircase

/-- The staircase family: after `k` passes the first `k` cells are `∣+⟩`, the
rest still `∣0⟩`. -/
noncomputable def hadFam (k : ℕ) : QubitL n → 𝕢 :=
  fun i => if (i : ℕ) < k then qplus else q0

theorem norm_hadFam (m : ℕ) (i : QubitL n) : ‖hadFam n m i‖ = 1 := by
  unfold hadFam
  split_ifs
  · exact norm_qplus
  · exact norm_q0

theorem hadFam_zero : hadFam n 0 = fun _ => q0 :=
  funext fun _ => if_neg (Nat.not_lt_zero _)

theorem hadFam_full : hadFam n n = fun _ => qplus :=
  funext fun i => if_pos i.isLt

variable [NeZero n]

/-- The cell the `k`-th pass touches is still `∣0⟩`. -/
theorem hadFam_ctrl {k : ℕ} (hk : k < n) : hadFam n k (cell n k) = q0 :=
  if_neg (by rw [cell_val n hk]; omega)

/-- One pass advances the staircase by one cell. -/
theorem hadFam_step {k : ℕ} (hk : k < n) :
    Function.update (hadFam n k) (cell n k) qplus = hadFam n (k + 1) := by
  funext i
  by_cases hik : i = cell n k
  · subst hik
    rw [Function.update_self]
    exact (if_pos (by rw [cell_val n hk]; omega)).symm
  · rw [Function.update_of_ne hik]
    have hne : (i : ℕ) ≠ k := fun hc => hik (Fin.ext (hc.trans (cell_val n hk).symm))
    simp only [hadFam]
    rcases Nat.lt_or_ge (i : ℕ) k with h | h
    · rw [if_pos h, if_pos (Nat.lt_succ_of_lt h)]
    · rw [if_neg (Nat.not_lt.mpr h), if_neg (by omega)]

end Staircase

end Qhl
