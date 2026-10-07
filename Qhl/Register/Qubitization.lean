import Qhl.Foundations.Basic
import Qhl.Foundations.UnitNorm
import Mathlib.Data.Matrix.Basic

/-!
# Qubitization: the 2×2 invariant-block structure of a phased walk

The abstract linear algebra of qubitization (Low–Chuang, *Hamiltonian
simulation by qubitization*, Quantum 3, 163 (2019), arXiv:1610.06546;
Gilyén–Su–Low–Wiebe, *Quantum singular value transformation*, STOC 2019,
arXiv:1806.01838): given

* an isometric embedding `E : H₁ →ₗ H₂` of the system space into the
  system-plus-ancilla space (`E† E = 1`),
* a walk operator `Uop` on `H₂`,
* a reflection `R` fixing the embedded sector,
* a phase family `Ph φ` fixing the embedded sector and multiplying the
  walker's orthogonal component by `e^{iφ}`, and
* a unit vector `v` with block value `E† (Uop (E v)) = c • v` and
  `Uop (Uop (E v)) = E v`,

the two-dimensional subspace spanned by `u₀ = E v` and the orthogonal partner
`δ = Uop (E v) − c • E v` is invariant under `R`, `Uop` and `Ph φ`, and on the
orthonormal basis `(u₀, u₁ = δ/‖δ‖)` the reflected walk `R ∘ Uop` acts as the
rotation with `cos = c`.  Consequently the alternating product of phased
passes `R ∘ Uop ∘ Ph φₖ` acts blockwise as the 2×2 matrix product

```
∏ₖ ( R(c) · diag(1, e^{iφₖ}) ),      R(c) = [[c, s], [−s, c]],  s = √(1−c²),
```

the quantum-signal-processing product.  (Conventions in the literature write
the phase factor as `e^{iφZ}`; `diag(1, e^{iφ}) = e^{iφ/2}·e^{-iφ/2·Z}`-style
global phases per pass are exactly the convention slack between the published
forms, and the polynomial entry below is defined by the recursive product
itself, so no convention translation is assumed.)

Deliverables:

* `walk_emb` / `walk_u1` / `refl_u1` — the block invariance and the rotation
  action on the orthonormal block basis;
* `qsp_product` — the blockwise matrix identity for an arbitrary phase
  sequence: the iterate of phased passes applied to `E v` has block
  coordinates given by the recursive 2×2 product `qspProd`;
* `qspMat_eq_rot_mul_phase` — each pass factor is the rotation times the
  diagonal phase;
* `emb_adj_qspIter` / `qsp_transfer` — the post-selected component of the
  iterate is `P_φ(c) • v` where `P_φ(c) = (qspProd …) 0 0`, and any bound
  `‖P_φ(c) − target‖ ≤ ε` transfers to the output component.

Nothing here names a program or a particular Hamiltonian: the data is a
handful of operator identities that a concrete block encoding discharges.
-/

namespace Qhl.Qubitization

open scoped ComplexInnerProductSpace

variable {H₁ H₂ : Type*}
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [FiniteDimensional ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [FiniteDimensional ℂ H₂]

variable (E : H₁ →ₗ[ℂ] H₂) (Uop R : H₂ →ₗ[ℂ] H₂) (Ph : ℝ → H₂ →ₗ[ℂ] H₂)
variable (v : H₁) (c : ℝ)

/-! ## §1. The qubitization data -/

/-- The hypotheses a concrete block encoding discharges: `E` is an isometry,
`v` is a unit block vector of the walk with block value `c`, the walk squares
to the identity on the embedded vector, the reflection fixes the embedded
sector and reflects the walker's image, and the phase family fixes the
embedded sector and phases the walker's orthogonal component. -/
structure IsQubitization : Prop where
  /-- `E† E = 1` pointwise. -/
  emb_adj : ∀ w, LinearMap.adjoint E (E w) = w
  /-- The block vector is a unit vector. -/
  norm_v : ‖v‖ = 1
  /-- The walk preserves the norm of the embedded block vector. -/
  norm_walk : ‖Uop (E v)‖ = 1
  /-- The block value: `E† (Uop (E v)) = c • v`. -/
  block : LinearMap.adjoint E (Uop (E v)) = (c : ℂ) • v
  /-- The walk squares to the identity on the embedded block vector. -/
  walk_sq : Uop (Uop (E v)) = E v
  /-- The reflection fixes the embedded sector. -/
  refl_emb : ∀ w, R (E w) = E w
  /-- The reflection reflects the walk image through the embedded sector. -/
  refl_walk : R (Uop (E v)) = ((2 * c : ℝ) : ℂ) • E v - Uop (E v)
  /-- The phase family fixes the embedded sector. -/
  ph_emb : ∀ φ w, Ph φ (E w) = E w
  /-- The phase family phases the walker's non-embedded component. -/
  ph_walk : ∀ φ, Ph φ (Uop (E v))
    = (c : ℂ) • E v
      + Complex.exp (φ * Complex.I) • (Uop (E v) - (c : ℂ) • E v)

/-! ## §2. The orthogonal partner and the invariant block -/

/-- The orthogonal partner of the embedded block vector inside the walker
plane: `δ = Uop (E v) − c • E v`. -/
noncomputable def delta : H₂ := Uop (E v) - (c : ℂ) • E v

omit [FiniteDimensional ℂ H₁] [FiniteDimensional ℂ H₂] in
theorem uEv_eq : Uop (E v) = (c : ℂ) • E v + delta E Uop v c := by
  rw [delta]
  module

variable {E Uop R Ph v c}

theorem emb_adj_delta (h : IsQubitization E Uop R Ph v c) :
    LinearMap.adjoint E (delta E Uop v c) = 0 := by
  rw [delta, map_sub, map_smul, h.block, h.emb_adj, sub_self]

theorem ph_delta (h : IsQubitization E Uop R Ph v c) (φ : ℝ) :
    Ph φ (delta E Uop v c)
      = Complex.exp (φ * Complex.I) • delta E Uop v c := by
  rw [delta, map_sub, map_smul, h.ph_walk φ, h.ph_emb φ v]
  module

theorem refl_delta (h : IsQubitization E Uop R Ph v c) :
    R (delta E Uop v c) = -delta E Uop v c := by
  rw [delta, map_sub, map_smul, h.refl_walk, h.refl_emb v]
  push_cast
  module

theorem walk_delta (h : IsQubitization E Uop R Ph v c) :
    Uop (delta E Uop v c)
      = ((1 - c ^ 2 : ℝ) : ℂ) • E v - (c : ℂ) • delta E Uop v c := by
  rw [delta, map_sub, map_smul, h.walk_sq]
  rw [show Uop (E v) = (c : ℂ) • E v + delta E Uop v c from uEv_eq E Uop v c]
  push_cast
  module

/-- The reflected walk sends the embedded block vector to `c • E v − δ`. -/
theorem walk_emb (h : IsQubitization E Uop R Ph v c) :
    R (Uop (E v)) = (c : ℂ) • E v - delta E Uop v c := by
  rw [h.refl_walk,
    show Uop (E v) = (c : ℂ) • E v + delta E Uop v c from uEv_eq E Uop v c]
  push_cast
  module

/-- The reflected walk sends `δ` to `(1−c²) • E v + c • δ`: together with
`walk_emb` this is the invariance of the plane `span{E v, δ}` under the
reflected walk. -/
theorem refl_walk_delta (h : IsQubitization E Uop R Ph v c) :
    R (Uop (delta E Uop v c))
      = ((1 - c ^ 2 : ℝ) : ℂ) • E v + (c : ℂ) • delta E Uop v c := by
  rw [walk_delta h, map_sub, map_smul, map_smul, h.refl_emb v, refl_delta h]
  module

/-! ## §3. Inner products and the norm of the partner -/

theorem inner_emb_self (h : IsQubitization E Uop R Ph v c) :
    (⟪E v, E v⟫ : ℂ) = 1 := by
  have h1 : (⟪v, LinearMap.adjoint E (E v)⟫ : ℂ) = ⟪E v, E v⟫ :=
    LinearMap.adjoint_inner_right E v (E v)
  rw [h.emb_adj v] at h1
  rw [← h1, inner_self_eq_norm_sq_to_K (𝕜 := ℂ), h.norm_v]
  norm_num

theorem norm_emb (h : IsQubitization E Uop R Ph v c) : ‖E v‖ = 1 :=
  norm_eq_one_of_inner_self (inner_emb_self h)

theorem inner_emb_walk (h : IsQubitization E Uop R Ph v c) :
    (⟪E v, Uop (E v)⟫ : ℂ) = (c : ℂ) := by
  have h1 : (⟪v, LinearMap.adjoint E (Uop (E v))⟫ : ℂ) = ⟪E v, Uop (E v)⟫ :=
    LinearMap.adjoint_inner_right E v (Uop (E v))
  rw [h.block, inner_smul_right, inner_self_eq_norm_sq_to_K (𝕜 := ℂ), h.norm_v] at h1
  rw [← h1]
  norm_num

theorem inner_emb_delta (h : IsQubitization E Uop R Ph v c) :
    (⟪E v, delta E Uop v c⟫ : ℂ) = 0 := by
  rw [delta, inner_sub_right, inner_emb_walk h, inner_smul_right,
    inner_emb_self h, mul_one, sub_self]

theorem norm_delta_sq (h : IsQubitization E Uop R Ph v c) :
    ‖delta E Uop v c‖ ^ 2 = 1 - c ^ 2 := by
  have hpyth : ‖(c : ℂ) • E v + delta E Uop v c‖ * ‖(c : ℂ) • E v + delta E Uop v c‖
      = ‖(c : ℂ) • E v‖ * ‖(c : ℂ) • E v‖
        + ‖delta E Uop v c‖ * ‖delta E Uop v c‖ := by
    refine norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ)
      ((c : ℂ) • E v) (delta E Uop v c) ?_
    rw [inner_smul_left, inner_emb_delta h, mul_zero]
  rw [← uEv_eq E Uop v c, h.norm_walk] at hpyth
  have hcv : ‖(c : ℂ) • E v‖ = |c| := by
    rw [norm_smul, norm_emb h, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [hcv, abs_mul_abs_self] at hpyth
  rw [pow_two]
  nlinarith [hpyth]

/-! ## §4. The normalized block basis and the rotation -/

variable (E Uop v c) in
/-- The sine of the block angle: `s = √(1 − c²)`. -/
noncomputable def sVal : ℝ := Real.sqrt (1 - c ^ 2)

variable (E Uop v c) in
/-- The normalized orthogonal partner `u₁ = δ / s`. -/
noncomputable def u1 : H₂ := (((sVal c)⁻¹ : ℝ) : ℂ) • delta E Uop v c

section Nondegenerate

variable (hc : c ^ 2 < 1)

include hc in
theorem sVal_pos : 0 < sVal c :=
  Real.sqrt_pos.mpr (by nlinarith)

include hc in
theorem sVal_sq : sVal c ^ 2 = 1 - c ^ 2 :=
  Real.sq_sqrt (by nlinarith)

theorem norm_delta (h : IsQubitization E Uop R Ph v c) :
    ‖delta E Uop v c‖ = sVal c := by
  rw [sVal, ← norm_delta_sq h, Real.sqrt_sq (norm_nonneg _)]

include hc in
theorem delta_eq_s_smul (_h : IsQubitization E Uop R Ph v c) :
    delta E Uop v c = ((sVal c : ℝ) : ℂ) • u1 E Uop v c := by
  rw [u1, smul_smul, ← Complex.ofReal_mul,
    mul_inv_cancel₀ (ne_of_gt (sVal_pos hc)), Complex.ofReal_one, one_smul]

include hc in
theorem norm_u1 (h : IsQubitization E Uop R Ph v c) : ‖u1 E Uop v c‖ = 1 := by
  rw [u1, norm_smul, norm_delta h, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (sVal_pos hc)), inv_mul_cancel₀ (ne_of_gt (sVal_pos hc))]

/-- The block basis is orthonormal: `⟪E v, u₁⟫ = 0` (with `‖E v‖ = ‖u₁‖ = 1`
from `norm_emb` / `norm_u1`): the block is genuinely two-dimensional. -/
theorem inner_emb_u1 (h : IsQubitization E Uop R Ph v c) :
    (⟪E v, u1 E Uop v c⟫ : ℂ) = 0 := by
  rw [u1, inner_smul_right, inner_emb_delta h, mul_zero]

theorem emb_adj_u1 (h : IsQubitization E Uop R Ph v c) :
    LinearMap.adjoint E (u1 E Uop v c) = 0 := by
  rw [u1, map_smul, emb_adj_delta h, smul_zero]

/-- The reflection acts as `diag(1, −1)` on the block basis (`refl_emb` gives
the `+1`; this is the `−1`). -/
theorem refl_u1 (h : IsQubitization E Uop R Ph v c) :
    R (u1 E Uop v c) = -u1 E Uop v c := by
  rw [u1, map_smul, refl_delta h, smul_neg]

theorem ph_u1 (h : IsQubitization E Uop R Ph v c) (φ : ℝ) :
    Ph φ (u1 E Uop v c)
      = Complex.exp (φ * Complex.I) • u1 E Uop v c := by
  rw [u1, map_smul, ph_delta h φ, smul_comm]

include hc in
/-- **The rotation, first column**: `(R ∘ Uop) (E v) = c • E v − s • u₁`. -/
theorem walk_rot_emb (h : IsQubitization E Uop R Ph v c) :
    R (Uop (E v)) = (c : ℂ) • E v - ((sVal c : ℝ) : ℂ) • u1 E Uop v c := by
  rw [walk_emb h, delta_eq_s_smul hc h]

include hc in
/-- **The rotation, second column**: `(R ∘ Uop) u₁ = s • E v + c • u₁`.
Together with `walk_rot_emb` (and `refl_u1`, `refl_emb`) this is the 2×2
invariant-block statement: the plane `span{E v, u₁}` is invariant under both
the reflection and the walk, and the reflected walk acts on it as the
rotation with `cos = c`, `sin = s`. -/
theorem walk_rot_u1 (h : IsQubitization E Uop R Ph v c) :
    R (Uop (u1 E Uop v c))
      = ((sVal c : ℝ) : ℂ) • E v + (c : ℂ) • u1 E Uop v c := by
  have hs := sVal_pos hc
  have key : (((sVal c)⁻¹ : ℝ) : ℂ) * ((1 - c ^ 2 : ℝ) : ℂ) = ((sVal c : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    rw [← sVal_sq hc]
    field_simp
  rw [u1, map_smul, map_smul, refl_walk_delta h, smul_add, smul_smul, key,
    smul_smul, mul_comm, ← smul_smul, ← u1]

end Nondegenerate

/-! ## §5. The phased pass and its iterate -/

variable (Uop R Ph) in
/-- One phased pass of the walk: the phase gate, then the walk, then the
reflection (rightmost acts first). -/
noncomputable def passOp (φ : ℝ) : H₂ →ₗ[ℂ] H₂ := R ∘ₗ Uop ∘ₗ Ph φ

variable (E Uop R Ph v) in
/-- The iterate of phased passes on the embedded block vector: after `m`
passes with phases `φs 0, …, φs (m−1)`. -/
noncomputable def qspIter (φs : ℕ → ℝ) : ℕ → H₂
  | 0 => E v
  | m + 1 => passOp Uop R Ph (φs m) (qspIter φs m)

omit [FiniteDimensional ℂ H₁] [FiniteDimensional ℂ H₂] in
@[simp]
theorem qspIter_zero (φs : ℕ → ℝ) : qspIter E Uop R Ph v φs 0 = E v := rfl

omit [FiniteDimensional ℂ H₁] [FiniteDimensional ℂ H₂] in
theorem qspIter_succ (φs : ℕ → ℝ) (m : ℕ) :
    qspIter E Uop R Ph v φs (m + 1)
      = passOp Uop R Ph (φs m) (qspIter E Uop R Ph v φs m) := rfl

theorem pass_emb (h : IsQubitization E Uop R Ph v c) (φ : ℝ) :
    passOp Uop R Ph φ (E v) = (c : ℂ) • E v - delta E Uop v c := by
  rw [passOp, LinearMap.comp_apply, LinearMap.comp_apply, h.ph_emb φ v, walk_emb h]

theorem pass_emb_n (hc : c ^ 2 < 1) (h : IsQubitization E Uop R Ph v c) (φ : ℝ) :
    passOp Uop R Ph φ (E v)
      = (c : ℂ) • E v - ((sVal c : ℝ) : ℂ) • u1 E Uop v c := by
  rw [pass_emb h φ, delta_eq_s_smul hc h]

theorem pass_u1 (hc : c ^ 2 < 1) (h : IsQubitization E Uop R Ph v c) (φ : ℝ) :
    passOp Uop R Ph φ (u1 E Uop v c)
      = Complex.exp (φ * Complex.I) •
          (((sVal c : ℝ) : ℂ) • E v + (c : ℂ) • u1 E Uop v c) := by
  rw [passOp, LinearMap.comp_apply, LinearMap.comp_apply, ph_u1 h φ, map_smul,
    map_smul, walk_rot_u1 hc h]

/-! ## §6. The 2×2 QSP product -/

/-- The 2×2 block matrix of one phased pass on the basis `(E v, u₁)`:
`R(c) · diag(1, e^{iφ})`. -/
noncomputable def qspMat (c : ℝ) (φ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i j =>
    if i = 0 then
      (if j = 0 then (c : ℂ) else Complex.exp (φ * Complex.I) * (sVal c : ℂ))
    else
      (if j = 0 then -(sVal c : ℂ) else Complex.exp (φ * Complex.I) * (c : ℂ))

/-- The rotation with `cos = c`, `sin = s = √(1−c²)`. -/
noncomputable def rotMat (c : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i j =>
    if i = 0 then (if j = 0 then (c : ℂ) else (sVal c : ℂ))
    else (if j = 0 then -(sVal c : ℂ) else (c : ℂ))

/-- The diagonal phase factor of one pass. -/
noncomputable def phaseMat (φ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i j =>
    if i = 0 then (if j = 0 then 1 else 0)
    else (if j = 0 then 0 else Complex.exp (φ * Complex.I))

/-- **The SU(2)-product reading**: each pass factor is the rotation times the
diagonal phase — the alternating QSP product `∏ₖ (R(c) · diag(1, e^{iφₖ}))`. -/
theorem qspMat_eq_rot_mul_phase (c φ : ℝ) :
    qspMat c φ = rotMat c * phaseMat φ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qspMat, rotMat, phaseMat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The recursive 2×2 QSP product: pass `m` multiplies on the left. -/
noncomputable def qspProd (c : ℝ) (φs : ℕ → ℝ) : ℕ → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => 1
  | m + 1 => qspMat c (φs m) * qspProd c φs m

/-- **The QSP polynomial entry** `P_φ(c)`: the `(0,0)` entry of the recursive
2×2 product — the amplitude the phased walk leaves on the embedded block
vector. -/
noncomputable def qspPoly (c : ℝ) (φs : ℕ → ℝ) (m : ℕ) : ℂ :=
  qspProd c φs m 0 0

theorem qspProd_succ_00 (c : ℝ) (φs : ℕ → ℝ) (m : ℕ) :
    qspProd c φs (m + 1) 0 0
      = (c : ℂ) * qspProd c φs m 0 0
        + Complex.exp (φs m * Complex.I) * (sVal c : ℂ) * qspProd c φs m 1 0 := by
  show (qspMat c (φs m) * qspProd c φs m) 0 0 = _
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  simp [qspMat]

theorem qspProd_succ_10 (c : ℝ) (φs : ℕ → ℝ) (m : ℕ) :
    qspProd c φs (m + 1) 1 0
      = -(sVal c : ℂ) * qspProd c φs m 0 0
        + Complex.exp (φs m * Complex.I) * (c : ℂ) * qspProd c φs m 1 0 := by
  show (qspMat c (φs m) * qspProd c φs m) 1 0 = _
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  simp [qspMat]

/-! ## §7. The blockwise product identity and the transfer bound -/

/-- **The blockwise QSP matrix identity, for an arbitrary phase sequence**:
the iterate of phased passes applied to the embedded block vector has block
coordinates given by the recursive 2×2 product,

```
(∏ₖ (R ∘ Uop ∘ Ph φₖ)) (E v)  =  (∏ₖ qspMat c φₖ)₀₀ • E v + (∏ₖ qspMat c φₖ)₁₀ • u₁.
```
-/
theorem qsp_product (h : IsQubitization E Uop R Ph v c) (hc : c ^ 2 < 1)
    (φs : ℕ → ℝ) (m : ℕ) :
    qspIter E Uop R Ph v φs m
      = qspProd c φs m 0 0 • E v + qspProd c φs m 1 0 • u1 E Uop v c := by
  induction m with
  | zero =>
      rw [qspIter_zero]
      rw [show qspProd c φs 0 = 1 from rfl, Matrix.one_apply_eq,
        Matrix.one_apply_ne (by decide), one_smul, zero_smul, add_zero]
  | succ m ih =>
      rw [qspIter_succ, ih, map_add, map_smul, map_smul, pass_emb_n hc h,
        pass_u1 hc h, qspProd_succ_00, qspProd_succ_10]
      module

/-- The post-selected (embedded-sector) component of the iterate is the QSP
polynomial entry times the block vector: `E† (iterate) = P_φ(c) • v`. -/
theorem emb_adj_qspIter (h : IsQubitization E Uop R Ph v c) (hc : c ^ 2 < 1)
    (φs : ℕ → ℝ) (m : ℕ) :
    LinearMap.adjoint E (qspIter E Uop R Ph v φs m)
      = qspPoly c φs m • v := by
  rw [qsp_product h hc φs m, map_add, map_smul, map_smul, h.emb_adj v,
    emb_adj_u1 h, smul_zero, add_zero, qspPoly]

/-- **The transfer bound**: any approximation bound on the QSP polynomial
entry transfers to the post-selected output component — if
`‖P_φ(c) − target‖ ≤ ε` then the embedded-sector component of the iterate is
`ε`-close to `target • v`. -/
theorem qsp_transfer (h : IsQubitization E Uop R Ph v c) (hc : c ^ 2 < 1)
    (φs : ℕ → ℝ) (m : ℕ) (target : ℂ) (ε : ℝ)
    (hP : ‖qspPoly c φs m - target‖ ≤ ε) :
    ‖LinearMap.adjoint E (qspIter E Uop R Ph v φs m) - target • v‖ ≤ ε := by
  rw [emb_adj_qspIter h hc φs m, ← sub_smul, norm_smul, h.norm_v, mul_one]
  exact hP

end Qhl.Qubitization

/-! ## §8. Axiom audit -/

#print axioms Qhl.Qubitization.walk_rot_emb
#print axioms Qhl.Qubitization.walk_rot_u1
#print axioms Qhl.Qubitization.refl_u1
#print axioms Qhl.Qubitization.qsp_product
#print axioms Qhl.Qubitization.qspMat_eq_rot_mul_phase
#print axioms Qhl.Qubitization.emb_adj_qspIter
#print axioms Qhl.Qubitization.qsp_transfer
