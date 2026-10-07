import Qhl.SuperOp.Basic
import Qhl.HSpace.KetBra
import Mathlib.Analysis.Matrix.Order

/-!
# Super-operators: the Choi matrix, complete positivity, quantum operations

Spec 04 §2, milestone M6 phase 2 (items Q-4, and the CP halves of Q-5), over
the fixtures of `Qhl/HSpace/Basic.lean` and the phase-1 API of
`Qhl/SuperOp/Basic.lean`.

* `choiMatrix E` / `choiMatrixₗ` — Q-4, CoqQ `so2choi` (`quantum.v:3089`)
* `ofChoiMatrix M` — the inverse, CoqQ `choi2so` (`quantum.v:3089-3095`), with
  round trips `ofChoiMatrix_choiMatrix`/`choiMatrix_ofChoiMatrix`
  (CoqQ `so2choiK`/`choi2soK`) and `choiMatrix_injective`
* `IsCP E := (choiMatrix E).PosSemidef` — Q-4, CoqQ `cpmap` (`quantum.v:3180`);
  the Choi–Kraus theorem `isCP_iff_exists_kraus` (CoqQ `choi2kraus:3095`)
* `IsQO`/`IsQC` — the CP halves of Q-5, CoqQ `'QO`/`'QC` (`quantum.v:3497-3527`)

## Choi-matrix entry convention (fixed here)

The Choi matrix is indexed by `QIdx D S × QIdx D T`, and the entry at row `p`,
column `q` is
`choiMatrix E p q = ⟪δ_{p.2}, E |δ_{p.1}⟩⟨δ_{q.1}| δ_{q.2}⟫`
(with `p.1, q.1 : QIdx D S`, `p.2, q.2 : QIdx D T`). Equivalently `p = (i,k)`,
`q = (j,l)` and the entry is `⟨k| E(|i⟩⟨j|) |l⟩`, i.e.
`C = ∑_{i,j} |i⟩⟨j| ⊗ E(|i⟩⟨j|)` in the standard Choi–Jamiołkowski form. With
this row convention the Choi matrix of a Kraus map `kraussoOf f` comes out as
`Bᴴ * B` (see `choiMatrix_kraussoOf`), where `B i q = ⟪f i δ_{q.1}, δ_{q.2}⟫`,
so complete positivity is immediate from `posSemidef_conjTranspose_mul_self`.
Per spec 04 (Q-4) this is deliberately NOT mathlib's `CompletelyPositiveMap`
(which is C⋆/`CStarMatrix`-based); we keep the plain `Matrix.PosSemidef` def.
-/

namespace Qhl

open Finset
open scoped ComplexInnerProductSpace ComplexOrder MatrixOrder Matrix

variable {L : Type*} [DecidableEq L]
variable (D : L → Type*) [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable {S T U : Finset L}
variable {κ κ₁ κ₂ : Type*} [Fintype κ] [Fintype κ₁] [Fintype κ₂]

/-! ## Q-4: the Choi matrix -/

/-- The Choi matrix of a super-operator (CoqQ `so2choi`, `quantum.v:3089`),
indexed by `QIdx D S × QIdx D T`. Entry convention (see the module docstring):
`choiMatrix E p q = ⟪δ_{p.2}, E |δ_{p.1}⟩⟨δ_{q.1}| δ_{q.2}⟫`. -/
noncomputable def choiMatrix (E : SuperOp D S T) :
    Matrix (QIdx D S × QIdx D T) (QIdx D S × QIdx D T) ℂ := fun p q =>
  ⟪deltav D p.2, E (outerLM (deltav D p.1) (deltav D q.1)) (deltav D q.2)⟫

theorem choiMatrix_apply (E : SuperOp D S T) (p q : QIdx D S × QIdx D T) :
    choiMatrix D E p q =
      ⟪deltav D p.2, E (outerLM (deltav D p.1) (deltav D q.1)) (deltav D q.2)⟫ := rfl

theorem choiMatrix_add (E F : SuperOp D S T) :
    choiMatrix D (E + F) = choiMatrix D E + choiMatrix D F := by
  ext p q
  simp only [choiMatrix_apply, LinearMap.add_apply, inner_add_right, Matrix.add_apply]

theorem choiMatrix_smul (c : ℂ) (E : SuperOp D S T) :
    choiMatrix D (c • E) = c • choiMatrix D E := by
  ext p q
  simp only [choiMatrix_apply, LinearMap.smul_apply, inner_smul_right, Matrix.smul_apply,
    smul_eq_mul]

@[simp]
theorem choiMatrix_zero : choiMatrix D (0 : SuperOp D S T) = 0 := by
  ext p q
  simp [choiMatrix_apply]

theorem choiMatrix_sum {ι : Type*} (s : Finset ι) (E : ι → SuperOp D S T) :
    choiMatrix D (∑ i ∈ s, E i) = ∑ i ∈ s, choiMatrix D (E i) := by
  induction s using Finset.cons_induction with
  | empty => simp only [Finset.sum_empty, choiMatrix_zero]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, choiMatrix_add, ih]

/-- The Choi matrix bundled as a ℂ-linear map (Q-4). -/
noncomputable def choiMatrixₗ :
    SuperOp D S T →ₗ[ℂ] Matrix (QIdx D S × QIdx D T) (QIdx D S × QIdx D T) ℂ where
  toFun := choiMatrix D
  map_add' := choiMatrix_add D
  map_smul' := choiMatrix_smul D

@[simp]
theorem choiMatrixₗ_apply (E : SuperOp D S T) : choiMatrixₗ D E = choiMatrix D E := rfl

/-! ## The inverse: `ofChoiMatrix` (CoqQ `choi2so`, `quantum.v:3089-3095`) -/

/-- The super-operator reconstructed from a Choi matrix (CoqQ `choi2so`,
`quantum.v:3089`): with the convention above, `ofChoiMatrix M` acts on
`x` by `x ↦ ∑_{p,q} (M p q · ⟪δ_{p.1}, x δ_{q.1}⟫) • |δ_{p.2}⟩⟨δ_{q.2}|`. It is
the inverse of `choiMatrix` (`ofChoiMatrix_choiMatrix`,
`choiMatrix_ofChoiMatrix`). -/
noncomputable def ofChoiMatrix
    (M : Matrix (QIdx D S × QIdx D T) (QIdx D S × QIdx D T) ℂ) : SuperOp D S T where
  toFun x := ∑ p, ∑ q, (M p q * ⟪deltav D p.1, x (deltav D q.1)⟫) •
    outerLM (deltav D p.2) (deltav D q.2)
  map_add' x y := by
    simp only [LinearMap.add_apply, inner_add_right, mul_add, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [LinearMap.smul_apply, inner_smul_right, RingHom.id_apply, Finset.smul_sum,
      smul_smul, mul_left_comm]

theorem ofChoiMatrix_apply
    (M : Matrix (QIdx D S × QIdx D T) (QIdx D S × QIdx D T) ℂ) (x : EndM D S) :
    ofChoiMatrix D M x = ∑ p, ∑ q, (M p q * ⟪deltav D p.1, x (deltav D q.1)⟫) •
      outerLM (deltav D p.2) (deltav D q.2) := rfl

/-- Any operator on `HS D T` is its `deltav`-matrix-unit expansion. -/
theorem eq_sum_outerLM_deltav (Y : EndM D T) :
    Y = ∑ k, ∑ l, ⟪deltav D k, Y (deltav D l)⟫ • outerLM (deltav D k) (deltav D l) := by
  refine linM_ext D fun m => ?_
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, outerLM_apply, dv_dot, smul_smul]
  rw [Finset.sum_comm, Fintype.sum_eq_single m fun l hl =>
    Finset.sum_eq_zero fun k _ => by rw [if_neg hl, mul_zero, zero_smul]]
  simp only [if_pos, mul_one]
  conv_lhs => rw [dec_dv D (Y (deltav D m))]
  exact Finset.sum_congr rfl fun k _ => by rw [cdv_apply, inner_deltav]

/-- `ofChoiMatrix` on a matrix unit `|δ_a⟩⟨δ_b|` collapses to the `(a,·),(b,·)`
sub-block, read off as an operator on `HS D T`. -/
theorem ofChoiMatrix_outerLM
    (M : Matrix (QIdx D S × QIdx D T) (QIdx D S × QIdx D T) ℂ) (a b : QIdx D S) :
    ofChoiMatrix D M (outerLM (deltav D a) (deltav D b))
      = ∑ k, ∑ l, M (a, k) (b, l) • outerLM (deltav D k) (deltav D l) := by
  rw [ofChoiMatrix_apply]
  simp only [outerLM_apply, inner_smul_right, dv_dot]
  rw [Fintype.sum_prod_type, Fintype.sum_eq_single a fun i hi => by simp [hi]]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fintype.sum_prod_type, Fintype.sum_eq_single b fun j hj => by simp [Ne.symm hj]]
  exact Finset.sum_congr rfl fun l _ => by simp

/-- **Round trip** (CoqQ `so2choiK`, `quantum.v:3095`): `ofChoiMatrix` inverts
`choiMatrix`. -/
theorem ofChoiMatrix_choiMatrix (E : SuperOp D S T) :
    ofChoiMatrix D (choiMatrix D E) = E := by
  refine endM_ext_outer D fun a b => ?_
  rw [ofChoiMatrix_outerLM]
  conv_rhs => rw [eq_sum_outerLM_deltav D (E (outerLM (deltav D a) (deltav D b)))]
  rfl

/-- **Round trip** (CoqQ `choi2soK`, `quantum.v:3095`): `choiMatrix` inverts
`ofChoiMatrix`. -/
theorem choiMatrix_ofChoiMatrix
    (M : Matrix (QIdx D S × QIdx D T) (QIdx D S × QIdx D T) ℂ) :
    choiMatrix D (ofChoiMatrix D M) = M := by
  ext p q
  rw [choiMatrix_apply, ofChoiMatrix_outerLM]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, outerLM_apply, inner_sum,
    inner_smul_right, dv_dot, smul_smul]
  rw [Fintype.sum_eq_single p.2 fun k hk => Finset.sum_eq_zero fun l _ => by simp [Ne.symm hk]]
  rw [Fintype.sum_eq_single q.2 fun l hl => by simp [hl]]
  simp

/-- `choiMatrix` is injective (CoqQ `so2choi_inj`, from the round trips). -/
theorem choiMatrix_injective :
    Function.Injective (choiMatrix D : SuperOp D S T → _) := fun E F h => by
  rw [← ofChoiMatrix_choiMatrix D E, ← ofChoiMatrix_choiMatrix D F, h]

/-! ## Q-4: the Choi matrix of a Kraus map, complete positivity -/

/-- The row-vector matrix reading off a Kraus family: `kraussB f i q =
⟪f i δ_{q.1}, δ_{q.2}⟫`, so `choiMatrix (kraussoOf f) = (kraussB f)ᴴ * kraussB f`
(`choiMatrix_kraussoOf`). -/
noncomputable def kraussB (f : κ → LinM D S T) :
    Matrix κ (QIdx D S × QIdx D T) ℂ := fun i q =>
  ⟪f i (deltav D q.1), deltav D q.2⟫

@[simp]
theorem kraussB_apply (f : κ → LinM D S T) (i : κ) (q : QIdx D S × QIdx D T) :
    kraussB D f i q = ⟪f i (deltav D q.1), deltav D q.2⟫ := rfl

/-- The Choi matrix of a Kraus map factors as `Bᴴ * B` (CoqQ `krausso2choi`,
`quantum.v:3095`); with the fixed row convention this is exactly the shape that
makes complete positivity immediate. -/
theorem choiMatrix_kraussoOf (f : κ → LinM D S T) :
    choiMatrix D (kraussoOf D f) = (kraussB D f)ᴴ * kraussB D f := by
  ext p q
  rw [choiMatrix_apply, kraussoOf_apply, Matrix.mul_apply]
  simp only [LinearMap.sum_apply, inner_sum, LinearMap.comp_apply, outerLM_apply, map_smul,
    inner_smul_right, LinearMap.adjoint_inner_right, Matrix.conjTranspose_apply, kraussB_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← starRingEnd_apply, inner_conj_symm, mul_comm]

/-- **Complete positivity** (Q-4, CoqQ `cpmap`, `quantum.v:3180`): `IsCP E`
holds when the Choi matrix is positive semidefinite. Per spec 04 (Q-4) this is
deliberately NOT mathlib's `CompletelyPositiveMap`. -/
def IsCP (E : SuperOp D S T) : Prop := (choiMatrix D E).PosSemidef

/-- Easy direction of Choi–Kraus (CoqQ `krausso_cp`): every Kraus map is CP. -/
theorem isCP_kraussoOf (f : κ → LinM D S T) : IsCP D (kraussoOf D f) := by
  rw [IsCP, choiMatrix_kraussoOf]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- **Hard direction of Choi–Kraus** (Q-4, CoqQ `choi2kraus`, `quantum.v:3095`):
a CP super-operator is a Kraus map, with Kraus index `QIdx D S × QIdx D T`.
The Kraus operators are read off a factorization `choiMatrix E = Bᴴ * B` of the
(PSD) Choi matrix. -/
theorem IsCP.exists_kraus {E : SuperOp D S T} (hE : IsCP D E) :
    ∃ f : (QIdx D S × QIdx D T) → LinM D S T, E = kraussoOf D f := by
  have hps : (choiMatrix D E).PosSemidef := hE
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hps.nonneg
  rw [Matrix.star_eq_conjTranspose] at hB
  set f : (QIdx D S × QIdx D T) → LinM D S T := fun r =>
    (EuclideanSpace.basisFun (QIdx D S) ℂ).toBasis.constr ℂ
      fun j => (WithLp.toLp 2 fun k => star (B r (j, k)) : HS D T) with hfdef
  have hf : ∀ (r : QIdx D S × QIdx D T) (j : QIdx D S),
      f r (deltav D j) = (WithLp.toLp 2 fun k => star (B r (j, k)) : HS D T) := by
    intro r j
    have hj : deltav D j = (EuclideanSpace.basisFun (QIdx D S) ℂ).toBasis j := by
      simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, deltav_def]
    rw [hfdef, hj]
    exact Module.Basis.constr_basis _ ℂ _ j
  have hinner : ∀ (w : HS D T) (k : QIdx D T), ⟪w, deltav D k⟫ = star (w k) := by
    intro w k
    rw [deltav_def, EuclideanSpace.inner_single_right, one_mul, RCLike.star_def]
  have hBmat : kraussB D f = B := by
    ext r q
    rw [kraussB_apply, hinner, hf, star_star]
  refine ⟨f, (choiMatrix_injective D ?_).symm⟩
  rw [choiMatrix_kraussoOf, hBmat, ← hB]

/-- **Choi–Kraus** (Q-4, CoqQ `choi2kraus`, `quantum.v:3095`): complete
positivity is equivalent to being a Kraus map. The fixed Kraus index
`QIdx D S × QIdx D T` keeps this free of type quantifiers (a deviation from
CoqQ's `sigma`-typed statement). -/
theorem isCP_iff_exists_kraus {E : SuperOp D S T} :
    IsCP D E ↔ ∃ f : (QIdx D S × QIdx D T) → LinM D S T, E = kraussoOf D f :=
  ⟨IsCP.exists_kraus D, fun ⟨_, hf⟩ => hf ▸ isCP_kraussoOf D _⟩

/-! ## CP corollaries (Q-4) -/

/-- CP is closed under composition (CoqQ `comp_cpmap`). -/
theorem IsCP.comp {E : SuperOp D T U} {F : SuperOp D S T}
    (hE : IsCP D E) (hF : IsCP D F) : IsCP D (E ∘ₗ F) := by
  obtain ⟨g, rfl⟩ := hE.exists_kraus
  obtain ⟨h, rfl⟩ := hF.exists_kraus
  rw [kraussoOf_comp]
  exact isCP_kraussoOf D _

/-- CP is closed under addition (CoqQ `add_cpmap`). -/
theorem IsCP.add {E F : SuperOp D S T} (hE : IsCP D E) (hF : IsCP D F) :
    IsCP D (E + F) := by
  rw [IsCP, choiMatrix_add]; exact Matrix.PosSemidef.add hE hF

/-- CP is closed under nonnegative scaling (CoqQ `scale_cpmap`). -/
theorem IsCP.smul {c : ℂ} (hc : 0 ≤ c) {E : SuperOp D S T} (hE : IsCP D E) :
    IsCP D (c • E) := by
  rw [IsCP, choiMatrix_smul]; exact Matrix.PosSemidef.smul hE hc

/-- The zero super-operator is CP. -/
theorem isCP_zero : IsCP D (0 : SuperOp D S T) := by
  rw [IsCP, choiMatrix_zero]; exact Matrix.PosSemidef.zero

/-- CP is closed under finite sums. -/
theorem IsCP.sum {ι : Type*} {s : Finset ι} {E : ι → SuperOp D S T}
    (h : ∀ i ∈ s, IsCP D (E i)) : IsCP D (∑ i ∈ s, E i) := by
  rw [IsCP, choiMatrix_sum]; exact Matrix.posSemidef_sum s h

/-- The identity super-operator is CP (CoqQ `idso_cp`). -/
theorem isCP_id : IsCP D (LinearMap.id : SuperOp D S S) := by
  rw [← formsoOf_one D]; exact isCP_kraussoOf D _

/-- Every single-operator (form) super-operator is CP (CoqQ `formso_cp`). -/
theorem isCP_formsoOf (g : LinM D S T) : IsCP D (formsoOf D g) :=
  isCP_kraussoOf D _

/-- A CP map preserves positivity (CoqQ `cpmap_psd`). -/
theorem IsCP.isPositive_map {E : SuperOp D S T} (hE : IsCP D E) {x : EndM D S}
    (hx : x.IsPositive) : (E x).IsPositive := by
  obtain ⟨f, rfl⟩ := hE.exists_kraus
  exact kraussoOf_isPositive D f hx

/-- The dual of a CP map is CP (CoqQ `dualso_cp`); one line via Kraus. -/
theorem IsCP.dualSO {E : SuperOp D S T} (hE : IsCP D E) : IsCP D (dualSO D E) := by
  obtain ⟨f, rfl⟩ := hE.exists_kraus
  rw [dualSO_kraussoOf]; exact isCP_kraussoOf D _

/-! ## Q-5 (CP halves): quantum operations and channels -/

/-- Quantum operation: completely positive and trace-nonincreasing.
CoqQ: `'QO` (`quantum.v:3497`). -/
def IsQO (E : SuperOp D S T) : Prop := IsCP D E ∧ IsTN D E

/-- Quantum channel: completely positive and trace-preserving.
CoqQ: `'QC` (`quantum.v:3527`). -/
def IsQC (E : SuperOp D S T) : Prop := IsCP D E ∧ IsTP D E

theorem IsQC.isQO {E : SuperOp D S T} (h : IsQC D E) : IsQO D E :=
  ⟨h.1, IsTP.isTN D h.2⟩

/-- Quantum operations compose (CoqQ `comp_qo`); the trace-nonincreasing side
condition is discharged by `IsCP.isPositive_map`. -/
theorem IsQO.comp {E : SuperOp D T U} {F : SuperOp D S T}
    (hE : IsQO D E) (hF : IsQO D F) : IsQO D (E ∘ₗ F) :=
  ⟨IsCP.comp D hE.1 hF.1,
    IsTN.comp D hE.2 hF.2 fun _ hx => IsCP.isPositive_map D hF.1 hx⟩

/-- Quantum channels compose (CoqQ `comp_qc`). -/
theorem IsQC.comp {E : SuperOp D T U} {F : SuperOp D S T}
    (hE : IsQC D E) (hF : IsQC D F) : IsQC D (E ∘ₗ F) :=
  ⟨IsCP.comp D hE.1 hF.1, IsTP.comp D hE.2 hF.2⟩

/-- The identity super-operator is a quantum channel (CoqQ `idso_qc`). -/
theorem isQC_id : IsQC D (LinearMap.id : SuperOp D S S) :=
  ⟨isCP_id D, isTP_id D⟩

/-- Kraus characterization of channels (CoqQ `krausso_qc`): a Kraus map is a
channel iff its family satisfies the completeness relation. -/
theorem isQC_kraussoOf_iff (f : κ → LinM D S T) :
    IsQC D (kraussoOf D f) ↔ ∑ i, LinearMap.adjoint (f i) ∘ₗ f i = 1 :=
  ⟨fun h => (kraussoOf_isTP_iff D f).mp h.2,
    fun h => ⟨isCP_kraussoOf D f, (kraussoOf_isTP_iff D f).mpr h⟩⟩

/-- Kraus characterization of quantum operations (CoqQ `krausso_qo`). -/
theorem isQO_kraussoOf_iff (f : κ → LinM D S T) :
    IsQO D (kraussoOf D f) ↔ ∑ i, LinearMap.adjoint (f i) ∘ₗ f i ≤ 1 :=
  ⟨fun h => (kraussoOf_isTN_iff D f).mp h.2,
    fun h => ⟨isCP_kraussoOf D f, (kraussoOf_isTN_iff D f).mpr h⟩⟩

/-- The dual of a channel is unital (CoqQ `qc_dualso_qu`, `quantum.v:3556`). -/
theorem IsQC.dualSO_unital {E : SuperOp D S T} (h : IsQC D E) :
    IsUnital D (dualSO D E) := IsTP.isUnital_dualSO D h.2

end Qhl
