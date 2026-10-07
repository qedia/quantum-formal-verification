import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Qhl.Foundations.Basic

/-!
# G-1: unitary operators

Subgoal G-1 of spec 06. `IsUnitary` is the two-sided condition
`f† ∘ f = 1 ∧ f ∘ f† = 1`; it is *definitionally* membership in mathlib's
`unitary (E →ₗ[ℂ] E)` submonoid (the star operation on endomorphisms of a
finite-dimensional inner-product space is the adjoint), so `UnitaryOp E` is
that submonoid and inherits its `Monoid`/`Star`/`Group` structure — no
transport boilerplate.

Constructions of unitaries used by the gate library (G-2/G-3):

* `unitaryOfMat`: from a matrix with `Mᴴ * M = 1` (`Matrix.toEuclideanLin`);
* `permOp`: from a permutation of the basis index (reindexing isometry);
* `diagOp`: from a family of unit-modulus scalars.

CoqQ counterpart: the `'FU` structure of `quantum.v` (`unitarylf`).
-/

namespace Qhl

open scoped ComplexInnerProductSpace Matrix

section IsUnitary

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- A unitary operator: `f† ∘ f = 1` and `f ∘ f† = 1`. CoqQ `unitarylf`
(`quantum.v:1554`). -/
def IsUnitary (f : E →ₗ[ℂ] E) : Prop :=
  LinearMap.adjoint f ∘ₗ f = 1 ∧ f ∘ₗ LinearMap.adjoint f = 1

/-- `IsUnitary` is membership in mathlib's `unitary` submonoid. -/
theorem isUnitary_iff_mem_unitary (f : E →ₗ[ℂ] E) :
    IsUnitary f ↔ f ∈ unitary (E →ₗ[ℂ] E) := Iff.rfl

theorem isUnitary_one : IsUnitary (1 : E →ₗ[ℂ] E) :=
  (isUnitary_iff_mem_unitary _).mpr (one_mem _)

theorem IsUnitary.comp {f g : E →ₗ[ℂ] E} (hf : IsUnitary f) (hg : IsUnitary g) :
    IsUnitary (f ∘ₗ g) :=
  (isUnitary_iff_mem_unitary _).mpr (mul_mem hf hg)

theorem IsUnitary.adjoint {f : E →ₗ[ℂ] E} (hf : IsUnitary f) :
    IsUnitary (LinearMap.adjoint f) := by
  refine ⟨?_, ?_⟩ <;> rw [LinearMap.adjoint_adjoint]
  · exact hf.2
  · exact hf.1

/-- In finite dimension one side of the unitarity condition suffices. -/
theorem isUnitary_of_adjoint_comp_self {f : E →ₗ[ℂ] E}
    (h : LinearMap.adjoint f ∘ₗ f = 1) : IsUnitary f := by
  have key : ∀ u, LinearMap.adjoint f (f u) = u := fun u => by
    have := congrArg (fun g : E →ₗ[ℂ] E => g u) h
    simpa using this
  have hinj : Function.Injective f := fun u v huv => by
    rw [← key u, ← key v, huv]
  refine ⟨h, ?_⟩
  ext v
  obtain ⟨w, rfl⟩ := LinearMap.surjective_of_injective hinj v
  simp [key w]

/-- G-1 bridge: a unitary preserves inner products. -/
theorem IsUnitary.isIsometryOp {f : E →ₗ[ℂ] E} (hf : IsUnitary f) : IsIsometryOp f := by
  intro u v
  have h := congrArg (fun g : E →ₗ[ℂ] E => g v) hf.1
  simp only [LinearMap.comp_apply, Module.End.one_apply] at h
  rw [← LinearMap.adjoint_inner_right, h]

/-- The underlying map of a linear isometry equivalence is unitary. -/
theorem isUnitary_of_isometryEquiv (e : E ≃ₗᵢ[ℂ] E) :
    IsUnitary (e.toLinearEquiv.toLinearMap) := by
  constructor <;>
    · rw [show e.toLinearEquiv.toLinearMap = e.toLinearMap from rfl,
        LinearIsometryEquiv.adjoint_toLinearMap_eq_symm]
      ext v
      simp

/-- Conjugating a unitary by an isometry equivalence is unitary — the device
behind `Reg.op` (R-3) and gate reindexing. -/
theorem IsUnitary.conj_isometryEquiv {f : E →ₗ[ℂ] E} (hf : IsUnitary f) (e : E ≃ₗᵢ[ℂ] F) :
    IsUnitary (e.toLinearEquiv.toLinearMap ∘ₗ f ∘ₗ e.symm.toLinearEquiv.toLinearMap) := by
  have hadj : LinearMap.adjoint
      (e.toLinearEquiv.toLinearMap ∘ₗ f ∘ₗ e.symm.toLinearEquiv.toLinearMap)
      = e.toLinearEquiv.toLinearMap ∘ₗ LinearMap.adjoint f ∘ₗ
          e.symm.toLinearEquiv.toLinearMap := by
    rw [LinearMap.adjoint_comp, LinearMap.adjoint_comp,
      show e.symm.toLinearEquiv.toLinearMap = e.symm.toLinearMap from rfl,
      show e.toLinearEquiv.toLinearMap = e.toLinearMap from rfl,
      LinearIsometryEquiv.adjoint_toLinearMap_eq_symm,
      LinearIsometryEquiv.adjoint_toLinearMap_eq_symm, e.symm_symm]
    rfl
  constructor
  · rw [hadj]
    ext v
    have := congrArg (fun g : E →ₗ[ℂ] E => g (e.symm v)) hf.1
    simp only [LinearMap.comp_apply, Module.End.one_apply] at this ⊢
    simp [this]
  · rw [hadj]
    ext v
    have := congrArg (fun g : E →ₗ[ℂ] E => g (e.symm v)) hf.2
    simp only [LinearMap.comp_apply, Module.End.one_apply] at this ⊢
    simp [this]

/-! ### Conjugation by an isometry equivalence

The device behind `Reg.op` (R-3): transporting an operator along the
reindexing isometry between an ordered tuple space and a labelled space. -/

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] in
theorem conj_isometryEquiv_apply (e : E ≃ₗᵢ[ℂ] F) (A : E →ₗ[ℂ] E) (v : F) :
    e.toLinearEquiv.conj A v = e (A (e.symm v)) := rfl

theorem adjoint_conj_isometryEquiv (e : E ≃ₗᵢ[ℂ] F) (A : E →ₗ[ℂ] E) :
    LinearMap.adjoint (e.toLinearEquiv.conj A)
      = e.toLinearEquiv.conj (LinearMap.adjoint A) := by
  refine LinearMap.ext fun v => ?_
  refine ext_inner_left ℂ fun w => ?_
  rw [LinearMap.adjoint_inner_right]
  calc ⟪e (A (e.symm w)), v⟫
      = ⟪e (A (e.symm w)), e (e.symm v)⟫ := by rw [LinearIsometryEquiv.apply_symm_apply]
    _ = ⟪A (e.symm w), e.symm v⟫ := e.inner_map_map _ _
    _ = ⟪e.symm w, LinearMap.adjoint A (e.symm v)⟫ :=
        (LinearMap.adjoint_inner_right A _ _).symm
    _ = ⟪e (e.symm w), e (LinearMap.adjoint A (e.symm v))⟫ := (e.inner_map_map _ _).symm
    _ = ⟪w, e (LinearMap.adjoint A (e.symm v))⟫ := by rw [LinearIsometryEquiv.apply_symm_apply]

theorem isPositive_conj_isometryEquiv {A : E →ₗ[ℂ] E} (hA : A.IsPositive)
    (e : E ≃ₗᵢ[ℂ] F) : (e.toLinearEquiv.conj A).IsPositive := by
  have h : e.toLinearEquiv.conj A
      = e.toLinearMap ∘ₗ A ∘ₗ LinearMap.adjoint e.toLinearMap := by
    rw [LinearIsometryEquiv.adjoint_toLinearMap_eq_symm]
    rfl
  rw [h]
  exact hA.conj_adjoint e.toLinearMap

/-- A unitary fixes the unit sphere. -/
theorem norm_eq_one_of_isUnitary {K : E →ₗ[ℂ] E} (hK : IsUnitary K) {v : E}
    (hv : ‖v‖ = 1) : ‖K v‖ = 1 := by
  refine norm_eq_one_of_inner_self ?_
  rw [hK.isIsometryOp, show (⟪v, v⟫ : ℂ) = ((‖v‖ : ℝ) : ℂ) ^ 2 from
    inner_self_eq_norm_sq_to_K v, hv]
  norm_num

/-- Unitaries are invertible pointwise. -/
theorem adjoint_apply_apply {K : E →ₗ[ℂ] E} (hK : IsUnitary K) (v : E) :
    LinearMap.adjoint K (K v) = v := by
  have h := congrArg (fun f : E →ₗ[ℂ] E => f v) hK.1
  simpa only [LinearMap.comp_apply, Module.End.one_apply] using h

end IsUnitary

/-! ## The bundled type of unitaries -/

/-- Bundled unitary operators: mathlib's `unitary` submonoid of `E →ₗ[ℂ] E`
(so `1`, `*`, `star` and the `Group` structure come for free). CoqQ `'FU`. -/
abbrev UnitaryOp (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] : Type _ := ↥(unitary (E →ₗ[ℂ] E))

namespace UnitaryOp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- Smart constructor from an `IsUnitary` proof. -/
def mk' (f : E →ₗ[ℂ] E) (hf : IsUnitary f) : UnitaryOp E := ⟨f, hf⟩

@[simp]
theorem coe_mk' (f : E →ₗ[ℂ] E) (hf : IsUnitary f) : (mk' f hf : E →ₗ[ℂ] E) = f := rfl

theorem isUnitary (U : UnitaryOp E) : IsUnitary (U : E →ₗ[ℂ] E) := U.2

@[simp]
theorem coe_one : ((1 : UnitaryOp E) : E →ₗ[ℂ] E) = 1 := rfl

@[simp]
theorem coe_mul (U V : UnitaryOp E) :
    ((U * V : UnitaryOp E) : E →ₗ[ℂ] E) = (U : E →ₗ[ℂ] E) ∘ₗ (V : E →ₗ[ℂ] E) := rfl

/-- Transport a bundled unitary along an isometry equivalence — used to move
a gate from its natural index type to a register's tuple space. -/
noncomputable def congr {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F] (e : E ≃ₗᵢ[ℂ] F) (U : UnitaryOp E) : UnitaryOp F :=
  mk' _ (IsUnitary.conj_isometryEquiv U.isUnitary e)

@[simp]
theorem coe_congr {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F] (e : E ≃ₗᵢ[ℂ] F) (U : UnitaryOp E) :
    (congr e U : F →ₗ[ℂ] F)
      = e.toLinearEquiv.toLinearMap ∘ₗ (U : E →ₗ[ℂ] E) ∘ₗ e.symm.toLinearEquiv.toLinearMap :=
  rfl

theorem congr_apply {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F] (e : E ≃ₗᵢ[ℂ] F) (U : UnitaryOp E) (v : F) :
    (congr e U : F →ₗ[ℂ] F) v = e ((U : E →ₗ[ℂ] E) (e.symm v)) := rfl

end UnitaryOp

/-! ## G-1 constructions: matrices, permutations, diagonals -/

section Constructions

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The operator on `EuclideanSpace ℂ α` given by a matrix. -/
noncomputable def matOp (M : Matrix α α ℂ) :
    EuclideanSpace ℂ α →ₗ[ℂ] EuclideanSpace ℂ α :=
  Matrix.toEuclideanLin M

theorem matOp_apply (M : Matrix α α ℂ) (v : EuclideanSpace ℂ α) (i : α) :
    matOp M v i = ∑ j, M i j * v j := by
  simp [matOp, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]

@[simp]
theorem matOp_one : matOp (1 : Matrix α α ℂ) = 1 := by
  ext v i
  simp [matOp_apply, Matrix.one_apply, Finset.sum_ite_eq]

theorem matOp_mul (M N : Matrix α α ℂ) : matOp (M * N) = matOp M ∘ₗ matOp N := by
  ext v i
  simp only [matOp_apply, LinearMap.comp_apply, Matrix.mul_apply, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

@[simp]
theorem adjoint_matOp (M : Matrix α α ℂ) :
    LinearMap.adjoint (matOp M) = matOp Mᴴ :=
  (Matrix.toEuclideanLin_conjTranspose_eq_adjoint M).symm

/-- Unitarity of a matrix operator reduces to a matrix identity. -/
theorem isUnitary_matOp {M : Matrix α α ℂ} (h : Mᴴ * M = 1) : IsUnitary (matOp M) := by
  refine isUnitary_of_adjoint_comp_self ?_
  rw [adjoint_matOp, ← matOp_mul, h, matOp_one]

/-- Bundled unitary from a matrix. -/
noncomputable def unitaryOfMat (M : Matrix α α ℂ) (h : Mᴴ * M = 1) :
    UnitaryOp (EuclideanSpace ℂ α) := UnitaryOp.mk' _ (isUnitary_matOp h)

@[simp]
theorem coe_unitaryOfMat (M : Matrix α α ℂ) (h : Mᴴ * M = 1) :
    (unitaryOfMat M h : EuclideanSpace ℂ α →ₗ[ℂ] EuclideanSpace ℂ α) = matOp M := rfl

/-- The reindexing isometry of a bijection of the basis index. -/
noncomputable def euclCongr {β : Type*} [Fintype β] [DecidableEq β] (e : α ≃ β) :
    EuclideanSpace ℂ α ≃ₗᵢ[ℂ] EuclideanSpace ℂ β :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e

omit [DecidableEq α] in
@[simp]
theorem euclCongr_apply {β : Type*} [Fintype β] [DecidableEq β] (e : α ≃ β)
    (v : EuclideanSpace ℂ α) (j : β) : euclCongr e v j = v (e.symm j) := rfl

@[simp]
theorem euclCongr_single {β : Type*} [Fintype β] [DecidableEq β] (e : α ≃ β) (i : α)
    (c : ℂ) : euclCongr e (EuclideanSpace.single i c) = EuclideanSpace.single (e i) c :=
  EuclideanSpace.piLpCongrLeft_single e i c

/-- Reindexing of a gate along a bijection of the basis index. -/
noncomputable def euclCongrOp {β : Type*} [Fintype β] [DecidableEq β] (e : α ≃ β)
    (U : UnitaryOp (EuclideanSpace ℂ α)) : UnitaryOp (EuclideanSpace ℂ β) :=
  UnitaryOp.congr (euclCongr e) U

/-- G-1: a reindexed gate on a basis ket is the gate on the reindexed ket. -/
theorem euclCongrOp_single {β : Type*} [Fintype β] [DecidableEq β] (e : α ≃ β)
    (U : UnitaryOp (EuclideanSpace ℂ α)) (x : β) :
    (euclCongrOp e U : EuclideanSpace ℂ β →ₗ[ℂ] EuclideanSpace ℂ β)
        (EuclideanSpace.single x 1)
      = euclCongr e ((U : EuclideanSpace ℂ α →ₗ[ℂ] EuclideanSpace ℂ α)
          (EuclideanSpace.single (e.symm x) 1)) := by
  have h : (euclCongr e).symm (EuclideanSpace.single x (1 : ℂ))
      = EuclideanSpace.single (e.symm x) 1 := by
    apply (euclCongr e).injective
    rw [LinearIsometryEquiv.apply_symm_apply, euclCongr_single, Equiv.apply_symm_apply]
  exact congrArg (euclCongr e) (congrArg _ h)

/-- The permutation gate of a bijection of the basis index (`X`, `CNOT`,
`SWAP` are of this shape). -/
noncomputable def permOp (e : α ≃ α) : UnitaryOp (EuclideanSpace ℂ α) :=
  UnitaryOp.mk' _ (isUnitary_of_isometryEquiv (euclCongr e))

@[simp]
theorem permOp_apply (e : α ≃ α) (v : EuclideanSpace ℂ α) (i : α) :
    (permOp e : EuclideanSpace ℂ α →ₗ[ℂ] EuclideanSpace ℂ α) v i = v (e.symm i) := rfl

/-- The diagonal gate of a family of unit-modulus scalars (`Z`, `S`, `phase`,
`Rz`, `CZ` are of this shape). -/
noncomputable def diagOp (d : α → ℂ) (hd : ∀ a, ‖d a‖ = 1) :
    UnitaryOp (EuclideanSpace ℂ α) :=
  unitaryOfMat (Matrix.diagonal d) <| by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    refine congrArg Matrix.diagonal (funext fun a => ?_)
    have h : (starRingEnd ℂ) (d a) * d a = 1 := by
      rw [RCLike.conj_mul, hd a]
      norm_num
    simpa [Pi.star_apply] using h

end Constructions

end Qhl
