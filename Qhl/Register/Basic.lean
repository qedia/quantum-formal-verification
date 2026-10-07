import Qhl.Gate.Unitary
import Qhl.HSpace.LiftF
import Qhl.SuperOp.Basic

/-!
# R-1…R-3: ordered quantum registers over the labelled world

Subgoals R-1, R-2, R-3 of spec 06. A register is an *ordered* tuple of
distinct cells, `r : Fin k ↪ L` presented as a structure (`Reg L k`). Gates
live on the ordered tuple space `TSpace D f = EuclideanSpace ℂ (∀ i, D (f i))`
(so `CNOT` is an operator on a two-factor space), while the semantics lives on
the set-indexed spaces `HS D S` of spec 02. The bridge is the reindexing
isometry

`Reg.encode : TSpace D r.toFun ≃ₗᵢ[ℂ] HS D r.sig`

built exactly like `castH` (Decision H1: casts are reindexings, never
`Eq.rec`), together with the transport of operators `Reg.op` (conjugation by
`encode`) and of vectors `Reg.vec`.

Counterparts: master `QArray.lean:25`; CoqQ `qmem.v` (`tv2v`/`tf2f`, the
`vec_proj` mixin) with the register *path* syntax of `qreg.v` flattened away —
here a register is already the list of its cells.
-/

namespace Qhl

open Finset

/-! ## Ordered tuples of cells -/

section Tuple

variable {L : Type*} (D : L → Type*) [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable {k : ℕ}

/-- The classical states of an ordered tuple of cells. -/
abbrev TIdx (f : Fin k → L) : Type _ := ∀ i, D (f i)

/-- The Hilbert space of an ordered tuple of cells — where concrete gates
live. CoqQ: the `'H[T]` of `qtype.v` before the register mapping. -/
abbrev TSpace (f : Fin k → L) : Type _ := EuclideanSpace ℂ (TIdx D f)

end Tuple

/-! ## R-1: registers -/

/-- An ordered quantum register of `k` cells of the world `L`: an injective
map `Fin k → L`. CoqQ `qreg` (`qreg.v`), master `QArray`. -/
structure Reg (L : Type*) (k : ℕ) where
  /-- The `i`-th cell of the register. -/
  toFun : Fin k → L
  /-- The cells are pairwise distinct — the paper's `Dist(q̄)` (eq (2)). -/
  inj : Function.Injective toFun

namespace Reg

variable {L : Type*} {k : ℕ}

instance : CoeFun (Reg L k) fun _ => Fin k → L := ⟨Reg.toFun⟩

@[simp]
theorem coe_mk (f : Fin k → L) (h : Function.Injective f) : ⇑(Reg.mk f h) = f := rfl

@[ext]
theorem ext {r s : Reg L k} (h : ∀ i, r i = s i) : r = s := by
  cases r; cases s; simpa using funext h

section DecEq

variable [DecidableEq L]

/-- The set of cells the register occupies. -/
def sig (r : Reg L k) : Finset L := univ.image r.toFun

@[simp]
theorem mem_sig {r : Reg L k} {a : L} : a ∈ r.sig ↔ ∃ i, r i = a := by
  simp [sig]

theorem apply_mem_sig (r : Reg L k) (i : Fin k) : r i ∈ r.sig := mem_sig.mpr ⟨i, rfl⟩

/-- R-1: a register of `k` cells occupies `k` cells. -/
@[simp]
theorem card_sig (r : Reg L k) : #r.sig = k := by
  rw [sig, Finset.card_image_of_injective _ r.inj, Finset.card_univ, Fintype.card_fin]

/-- The single-cell register. -/
def single (a : L) : Reg L 1 := ⟨fun _ => a, fun i j _ => Subsingleton.elim i j⟩

omit [DecidableEq L] in
@[simp]
theorem single_apply (a : L) (i : Fin 1) : single a i = a := rfl

@[simp]
theorem sig_single (a : L) : (single a).sig = {a} := by
  ext b; simp [Reg.sig]

/-- The two-cell register of two distinct cells. -/
def pair (a b : L) (h : a ≠ b) : Reg L 2 :=
  ⟨![a, b], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all⟩

omit [DecidableEq L] in
@[simp]
theorem pair_apply (a b : L) (h : a ≠ b) (i : Fin 2) : pair a b h i = ![a, b] i := rfl

@[simp]
theorem sig_pair (a b : L) (h : a ≠ b) : (pair a b h).sig = {a, b} := by
  ext c
  constructor
  · rintro hc
    obtain ⟨i, rfl⟩ := mem_sig.mp hc
    fin_cases i <;> simp
  · intro hc
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact apply_mem_sig _ 0
    · rw [Finset.mem_singleton.mp hc]; exact apply_mem_sig _ 1

/-- The index bijection `Fin k ≃ ↥r.sig` induced by a register. -/
noncomputable def equivSig (r : Reg L k) : Fin k ≃ ↥r.sig :=
  Equiv.ofBijective (fun i => ⟨r i, r.apply_mem_sig i⟩)
    ⟨fun _ _ h => r.inj (congrArg Subtype.val h), fun j => by
      obtain ⟨i, hi⟩ := mem_sig.mp j.2
      exact ⟨i, Subtype.ext hi⟩⟩

@[simp]
theorem coe_equivSig (r : Reg L k) (i : Fin k) : (r.equivSig i : L) = r i := rfl

@[simp]
theorem apply_equivSig_symm (r : Reg L k) (j : ↥r.sig) : r (r.equivSig.symm j) = (j : L) :=
  congrArg Subtype.val (r.equivSig.apply_symm_apply j)

/-! ## R-2: the tuple ↔ set bridge -/

variable (D : L → Type*) [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]

/-- R-2: the reindexing of classical states, `TIdx D r ≃ QIdx D r.sig`.
CoqQ `qmem.v` `vec_proj` mixin. -/
noncomputable def idxEquiv (r : Reg L k) : TIdx D r.toFun ≃ QIdx D r.sig :=
  (Equiv.piCongrLeft' (fun i => D (r i)) r.equivSig).trans
    (Equiv.piCongrRight fun j => Equiv.cast (congrArg D (r.apply_equivSig_symm j)))

/-- R-2: the tuple space of a register is the labelled space of its cells, by
reindexing (same device as `castH`, spec 02 H-7). CoqQ `tv2v` (`qmem.v:157`). -/
noncomputable def encode (r : Reg L k) : TSpace D r.toFun ≃ₗᵢ[ℂ] HS D r.sig :=
  euclCongr (r.idxEquiv D)

@[simp]
theorem encode_apply (r : Reg L k) (v : TSpace D r.toFun) (x : QIdx D r.sig) :
    r.encode D v x = v ((r.idxEquiv D).symm x) := rfl

/-- R-2: `encode` sends basis vectors to basis vectors. -/
@[simp]
theorem encode_single (r : Reg L k) (x : TIdx D r.toFun) (c : ℂ) :
    r.encode D (EuclideanSpace.single x c) = EuclideanSpace.single (r.idxEquiv D x) c :=
  euclCongr_single _ _ _

theorem encode_deltav (r : Reg L k) (x : TIdx D r.toFun) :
    r.encode D (EuclideanSpace.single x 1) = deltav D (r.idxEquiv D x) :=
  encode_single D r x 1

/-! ## R-3: transport of vectors and operators -/

/-- R-3: a vector of the tuple space as a vector of the labelled space. -/
noncomputable def vec (r : Reg L k) (v : TSpace D r.toFun) : HS D r.sig := r.encode D v

/-- R-3: a gate on the tuple space as an operator on the labelled space,
by conjugation with `encode`. CoqQ `tf2f` (`qmem.v:157`). -/
noncomputable def op (r : Reg L k) (A : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun) :
    EndM D r.sig :=
  (r.encode D).toLinearEquiv.conj A

variable {D}

theorem op_apply (r : Reg L k) (A : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun)
    (v : HS D r.sig) : r.op D A v = r.encode D (A ((r.encode D).symm v)) := rfl

/-- R-3, entry form: in the `idxEquiv` coordinates `Reg.op r A` has `A`'s
matrix. -/
theorem op_deltav_apply (r : Reg L k)
    (A : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun) (x y : TIdx D r.toFun) :
    r.op D A (deltav D (r.idxEquiv D x)) (r.idxEquiv D y)
      = A (EuclideanSpace.single x 1) y := by
  have h : (r.encode D).symm (deltav D (r.idxEquiv D x)) = EuclideanSpace.single x 1 := by
    rw [deltav, ← Reg.encode_single, LinearIsometryEquiv.symm_apply_apply]
  rw [Reg.op_apply, h, Reg.encode_apply, Equiv.symm_apply_apply]

@[simp]
theorem op_one (r : Reg L k) : r.op D 1 = 1 := by
  refine LinearMap.ext fun v => ?_
  simp [op_apply]

theorem op_comp (r : Reg L k) (A B : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun) :
    r.op D (A ∘ₗ B) = r.op D A ∘ₗ r.op D B := by
  refine LinearMap.ext fun v => ?_
  simp [op_apply]

theorem op_add (r : Reg L k) (A B : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun) :
    r.op D (A + B) = r.op D A + r.op D B := map_add _ _ _

theorem op_smul (r : Reg L k) (c : ℂ) (A : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun) :
    r.op D (c • A) = c • r.op D A := map_smul _ _ _

theorem op_sum {ι : Type*} (r : Reg L k) (s : Finset ι)
    (A : ι → TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun) :
    r.op D (∑ i ∈ s, A i) = ∑ i ∈ s, r.op D (A i) := map_sum _ _ _

/-- R-3: `Reg.op` commutes with the adjoint. -/
@[simp]
theorem adjoint_op (r : Reg L k) (A : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun) :
    LinearMap.adjoint (r.op D A) = r.op D (LinearMap.adjoint A) :=
  adjoint_conj_isometryEquiv _ _

/-- R-3: `Reg.op` preserves positivity. -/
theorem op_isPositive (r : Reg L k) {A : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun}
    (hA : A.IsPositive) : (r.op D A).IsPositive :=
  isPositive_conj_isometryEquiv hA _

/-- R-3: `Reg.op` preserves unitarity. -/
theorem op_isUnitary (r : Reg L k) {A : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun}
    (hA : IsUnitary A) : IsUnitary (r.op D A) := by
  constructor
  · rw [adjoint_op, ← op_comp, hA.1, op_one]
  · rw [adjoint_op, ← op_comp, hA.2, op_one]

/-- R-3: `Reg.op` sends a bundled unitary to a bundled unitary. -/
noncomputable def unitary (r : Reg L k) (U : UnitaryOp (TSpace D r.toFun)) :
    UnitaryOp (HS D r.sig) :=
  UnitaryOp.mk' _ (r.op_isUnitary U.2)

@[simp]
theorem coe_unitary (r : Reg L k) (U : UnitaryOp (TSpace D r.toFun)) :
    (r.unitary U : EndM D r.sig) = r.op D (U : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun) :=
  rfl

/-- R-3: `Reg.op` preserves measurement families (G-4 support). -/
theorem op_isQMeasure {κ : Type*} [Fintype κ] (r : Reg L k)
    {M : κ → TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun}
    (hM : ∑ i, LinearMap.adjoint (M i) ∘ₗ M i = 1) :
    IsQMeasure D fun i => r.op D (M i) := by
  change ∑ i, LinearMap.adjoint (r.op D (M i)) ∘ₗ r.op D (M i) = 1
  have h : ∀ i, LinearMap.adjoint (r.op D (M i)) ∘ₗ r.op D (M i)
      = r.op D (LinearMap.adjoint (M i) ∘ₗ M i) := fun i => by
    rw [adjoint_op, ← op_comp]
  simp only [h]
  rw [← op_sum, hM, op_one]

end DecEq

end Reg

end Qhl
