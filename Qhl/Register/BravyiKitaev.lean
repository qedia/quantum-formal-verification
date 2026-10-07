import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The Bravyi–Kitaev basis-change matrix and its Fenwick CNOT network

The classical layer of the Bravyi–Kitaev transform, after Seeley–Richard–Love,
*The Bravyi–Kitaev transformation for quantum computation of electronic
structure* (arXiv:1208.5986), Fig. 2 and the `β₈` display of §III.B.

**Ascending-index convention.** Throughout, bit/row/column index `0` is the
*first* orbital/qubit and index `2^x - 1` the last, so the recursion of Fig. 2
reads (`fromBlocks A B C D` places `A` on the low indices):

* `β₁ = (1)`;
* `β_{2^{x+1}} = fromBlocks β_{2^x} 0 C β_{2^x}` where `C` is zero except its
  **last row** (global row `2^{x+1} - 1`), which is all ones.

In this convention `β` is **unit lower triangular** — `b_i = Σ_{j ≤ i} β_{ij}
f_j (mod 2)` — matching the `β₈` display of arXiv:1208.5986 §III.B read with
ascending indices (`b_0 = f_0`, `b_1 = f_1 + f_0`, …, `b_7 = f_7 + ⋯ + f_0`).

Contents:

* `bkMat x` — the matrix `β_{2^x}` over `ZMod 2`, by the block recursion;
* unit lower triangularity (`bkMat_diag`, `bkMat_eq_zero_of_lt`), the all-ones
  last row (`bkMat_lastF_row`), `det = 1` (`bkMat_det`) hence invertibility
  (`bkMat_isUnit_det`, `bkMatInvertible`), and the **inverse recursion**
  `bkMat_inv_succ`: the corner block of `(β_{2^{x+1}})⁻¹` is the single
  bottom-right `1` (`cornerOne`), as in Fig. 2 of arXiv:1208.5986;
* `bkVec x f` — the action on bit vectors, *defined* as the mod-2
  matrix–vector product (`bkVec_eq_mulVec` is `rfl`), with the half-split
  recursion `bkVec_lowE`/`bkVec_uppE_ne`/`bkVec_uppE_lastF` (upper-half
  unchanged pattern: the low half transforms by `β_{2^x}`; the high half
  transforms by `β_{2^x}` except that the last coordinate also absorbs the
  parity of the low half) and `bkVec_lastF` (the last coordinate is the total
  parity);
* the **Fenwick parity network**: `cnotBit c t` is the classical action of a
  `CNOT` with control `c` and target `t` on bit vectors; level `ℓ`
  (`0 ≤ ℓ < x`, block size `2^{ℓ+1}`) applies, for each block `k` with
  `(k+1)·2^{ℓ+1} ≤ 2^x`, the gate with control `k·2^{ℓ+1} + 2^ℓ - 1` and
  target `k·2^{ℓ+1} + 2^{ℓ+1} - 1` (`ctrlN`/`tgtN`);
  `levelPart`/`levelApply`/`netVec` fold the network level by level, small
  blocks first;
* the **program-vs-matrix agreement** `netVec_top : netVec x x f = bkVec x f`
  — the full network computes exactly the Bravyi–Kitaev basis change.
-/

namespace Qhl.BravyiKitaev

open Finset Matrix

/-! ## §1. Halving `Fin (2^(x+1))` -/

/-- `2^x + 2^x = 2^(x+1)`. -/
theorem two_pow_succ (x : ℕ) : 2 ^ x + 2 ^ x = 2 ^ (x + 1) := by
  rw [pow_succ, mul_two]

theorem two_pow_pos (x : ℕ) : 0 < 2 ^ x := pow_pos two_pos x

/-- The halving equivalence `Fin (2^x) ⊕ Fin (2^x) ≃ Fin (2^(x+1))`:
`finSumFinEquiv` transported along `2^x + 2^x = 2^(x+1)`. -/
def sumEquiv (x : ℕ) : Fin (2 ^ x) ⊕ Fin (2 ^ x) ≃ Fin (2 ^ (x + 1)) :=
  finSumFinEquiv.trans (finCongr (two_pow_succ x))

/-- The low-half embedding `Fin (2^x) → Fin (2^(x+1))` (value `i`). -/
def lowE (x : ℕ) (i : Fin (2 ^ x)) : Fin (2 ^ (x + 1)) := sumEquiv x (Sum.inl i)

/-- The high-half embedding `Fin (2^x) → Fin (2^(x+1))` (value `2^x + i`). -/
def uppE (x : ℕ) (i : Fin (2 ^ x)) : Fin (2 ^ (x + 1)) := sumEquiv x (Sum.inr i)

@[simp] theorem lowE_val (x : ℕ) (i : Fin (2 ^ x)) : (lowE x i : ℕ) = (i : ℕ) := by
  simp [lowE, sumEquiv]

@[simp] theorem uppE_val (x : ℕ) (i : Fin (2 ^ x)) :
    (uppE x i : ℕ) = 2 ^ x + (i : ℕ) := by
  simp [uppE, sumEquiv]
  omega

@[simp] theorem sumEquiv_symm_lowE (x : ℕ) (i : Fin (2 ^ x)) :
    (sumEquiv x).symm (lowE x i) = Sum.inl i := (sumEquiv x).symm_apply_apply _

@[simp] theorem sumEquiv_symm_uppE (x : ℕ) (i : Fin (2 ^ x)) :
    (sumEquiv x).symm (uppE x i) = Sum.inr i := (sumEquiv x).symm_apply_apply _

theorem lowE_injective (x : ℕ) : Function.Injective (lowE x) := fun _ _ h =>
  Sum.inl.inj ((sumEquiv x).injective h)

theorem uppE_injective (x : ℕ) : Function.Injective (uppE x) := fun _ _ h =>
  Sum.inr.inj ((sumEquiv x).injective h)

theorem lowE_ne_uppE (x : ℕ) (i j : Fin (2 ^ x)) : lowE x i ≠ uppE x j := fun h =>
  Sum.inl_ne_inr ((sumEquiv x).injective h)

/-- Every index of the doubled world is in exactly one half. -/
theorem lowE_or_uppE (x : ℕ) (m : Fin (2 ^ (x + 1))) :
    (∃ i, m = lowE x i) ∨ ∃ i, m = uppE x i := by
  obtain ⟨s, rfl⟩ := (sumEquiv x).surjective m
  cases s with
  | inl i => exact Or.inl ⟨i, rfl⟩
  | inr i => exact Or.inr ⟨i, rfl⟩

/-- The last index `2^x - 1` of `Fin (2^x)`. -/
def lastF (x : ℕ) : Fin (2 ^ x) := ⟨2 ^ x - 1, by have := two_pow_pos x; omega⟩

@[simp] theorem lastF_val (x : ℕ) : (lastF x : ℕ) = 2 ^ x - 1 := rfl

/-- The last index of the doubled world is the image of the last index of the
high half. -/
theorem uppE_lastF (x : ℕ) : uppE x (lastF x) = lastF (x + 1) := by
  apply Fin.ext
  rw [uppE_val, lastF_val, lastF_val]
  have h1 := two_pow_pos x
  have h2 := two_pow_succ x
  omega

/-! ## §2. The matrix `β_{2^x}` -/

/-- The connecting block `C` of the recursion of Fig. 2 (arXiv:1208.5986,
ascending-index convention): zero except the last row, which is all ones. -/
def cornerRow (x : ℕ) : Matrix (Fin (2 ^ x)) (Fin (2 ^ x)) (ZMod 2) :=
  Matrix.of fun i _ => if i = lastF x then 1 else 0

/-- The corner block of the *inverse* recursion (Fig. 2 of arXiv:1208.5986):
a single `1` in the bottom-right entry. -/
def cornerOne (x : ℕ) : Matrix (Fin (2 ^ x)) (Fin (2 ^ x)) (ZMod 2) :=
  Matrix.of fun i j => if i = lastF x ∧ j = lastF x then 1 else 0

/-- **The Bravyi–Kitaev basis-change matrix** `β_{2^x}` over `ZMod 2`
(arXiv:1208.5986 Fig. 2, ascending-index convention): `β₁ = (1)` and
`β_{2^{x+1}} = fromBlocks β_{2^x} 0 C β_{2^x}` with `C = cornerRow x`. -/
def bkMat : (x : ℕ) → Matrix (Fin (2 ^ x)) (Fin (2 ^ x)) (ZMod 2)
  | 0 => 1
  | x + 1 =>
      Matrix.reindex (sumEquiv x) (sumEquiv x)
        (Matrix.fromBlocks (bkMat x) 0 (cornerRow x) (bkMat x))

@[simp] theorem bkMat_zero : bkMat 0 = 1 := rfl

theorem bkMat_succ (x : ℕ) :
    bkMat (x + 1)
      = Matrix.reindex (sumEquiv x) (sumEquiv x)
          (Matrix.fromBlocks (bkMat x) 0 (cornerRow x) (bkMat x)) := rfl

@[simp] theorem bkMat_low_low (x : ℕ) (i j : Fin (2 ^ x)) :
    bkMat (x + 1) (lowE x i) (lowE x j) = bkMat x i j := by
  rw [bkMat_succ, Matrix.reindex_apply, Matrix.submatrix_apply,
    sumEquiv_symm_lowE, sumEquiv_symm_lowE, Matrix.fromBlocks_apply₁₁]

@[simp] theorem bkMat_low_upp (x : ℕ) (i j : Fin (2 ^ x)) :
    bkMat (x + 1) (lowE x i) (uppE x j) = 0 := by
  rw [bkMat_succ, Matrix.reindex_apply, Matrix.submatrix_apply,
    sumEquiv_symm_lowE, sumEquiv_symm_uppE, Matrix.fromBlocks_apply₁₂,
    Matrix.zero_apply]

@[simp] theorem bkMat_upp_low (x : ℕ) (i j : Fin (2 ^ x)) :
    bkMat (x + 1) (uppE x i) (lowE x j) = if i = lastF x then 1 else 0 := by
  rw [bkMat_succ, Matrix.reindex_apply, Matrix.submatrix_apply,
    sumEquiv_symm_uppE, sumEquiv_symm_lowE, Matrix.fromBlocks_apply₂₁]
  rfl

@[simp] theorem bkMat_upp_upp (x : ℕ) (i j : Fin (2 ^ x)) :
    bkMat (x + 1) (uppE x i) (uppE x j) = bkMat x i j := by
  rw [bkMat_succ, Matrix.reindex_apply, Matrix.submatrix_apply,
    sumEquiv_symm_uppE, sumEquiv_symm_uppE, Matrix.fromBlocks_apply₂₂]

/-! ## §3. Unit lower triangularity, the last row, determinant, inverse -/

/-- `β` has unit diagonal. -/
theorem bkMat_diag : ∀ x (i : Fin (2 ^ x)), bkMat x i i = 1
  | 0, i => by rw [bkMat_zero, Matrix.one_apply_eq]
  | x + 1, m => by
      rcases lowE_or_uppE x m with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · rw [bkMat_low_low]; exact bkMat_diag x i
      · rw [bkMat_upp_upp]; exact bkMat_diag x i

/-- `β` is lower triangular: entries strictly above the diagonal vanish. -/
theorem bkMat_eq_zero_of_lt :
    ∀ x (i j : Fin (2 ^ x)), (i : ℕ) < (j : ℕ) → bkMat x i j = 0
  | 0, i, j, hij => absurd hij (by have h1 := i.isLt; have h2 := j.isLt; omega)
  | x + 1, m, m', hij => by
      rcases lowE_or_uppE x m with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
        rcases lowE_or_uppE x m' with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · rw [bkMat_low_low]
        exact bkMat_eq_zero_of_lt x i j (by simpa using hij)
      · rw [bkMat_low_upp]
      · -- `i` in the high half, `j` in the low half: `i < j` is impossible
        rw [lowE_val, uppE_val] at hij
        have := j.isLt
        omega
      · rw [bkMat_upp_upp]
        exact bkMat_eq_zero_of_lt x i j (by simpa using hij)

/-- The last row of `β` is all ones: the last Bravyi–Kitaev bit is the total
parity (arXiv:1208.5986: the top qubit stores the parity of all orbitals). -/
theorem bkMat_lastF_row : ∀ x (j : Fin (2 ^ x)), bkMat x (lastF x) j = 1
  | 0, j => by
      have h : lastF 0 = j := Fin.ext (by have := j.isLt; omega)
      rw [h, bkMat_diag]
  | x + 1, m => by
      rw [← uppE_lastF]
      rcases lowE_or_uppE x m with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · rw [bkMat_upp_low, if_pos rfl]
      · rw [bkMat_upp_upp]; exact bkMat_lastF_row x j

/-- The last *column* of `β` is the last standard basis vector (unit diagonal
plus lower triangularity). -/
theorem bkMat_col_lastF (x : ℕ) (i : Fin (2 ^ x)) :
    bkMat x i (lastF x) = if i = lastF x then 1 else 0 := by
  by_cases h : i = lastF x
  · rw [if_pos h, h, bkMat_diag]
  · rw [if_neg h]
    refine bkMat_eq_zero_of_lt x i (lastF x) ?_
    have h1 : (i : ℕ) < 2 ^ x := i.isLt
    have h2 : (i : ℕ) ≠ 2 ^ x - 1 := fun hc => h (Fin.ext (by rw [hc, lastF_val]))
    rw [lastF_val]
    omega

/-- `det β = 1`. -/
theorem bkMat_det : ∀ x, (bkMat x).det = 1
  | 0 => by rw [bkMat_zero, Matrix.det_one]
  | x + 1 => by
      rw [bkMat_succ, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₁₂,
        bkMat_det x, one_mul]

/-- `β` is invertible. -/
theorem bkMat_isUnit_det (x : ℕ) : IsUnit (bkMat x).det := by
  rw [bkMat_det]; exact isUnit_one

set_option warn.classDefReducibility false in
/-- `β` is invertible (the bundled `Invertible` structure). -/
noncomputable def bkMatInvertible (x : ℕ) : Invertible (bkMat x) :=
  (bkMat x).invertibleOfIsUnitDet (bkMat_isUnit_det x)

theorem bkMat_mul_inv (x : ℕ) : bkMat x * (bkMat x)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (bkMat_isUnit_det x)

theorem bkMat_inv_mul (x : ℕ) : (bkMat x)⁻¹ * bkMat x = 1 :=
  Matrix.nonsing_inv_mul _ (bkMat_isUnit_det x)

/-- Doubled entries vanish mod 2. -/
theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := by revert a; decide

/-- Reindexing along the same equivalence on both sides commutes with matrix
multiplication. -/
theorem reindex_mul {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (e : m ≃ n) (M N : Matrix m m (ZMod 2)) :
    Matrix.reindex e e M * Matrix.reindex e e N = Matrix.reindex e e (M * N) := by
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.submatrix_mul_equiv]

/-- `C · β⁻¹ = cornerOne`: the ones-row times the inverse is the last row of
`β · β⁻¹ = 1`, because the last row of `β` is all ones. -/
theorem cornerRow_mul_inv (x : ℕ) : cornerRow x * (bkMat x)⁻¹ = cornerOne x := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hi : i = lastF x
  · subst hi
    have h1 : ∀ k, cornerRow x (lastF x) k * (bkMat x)⁻¹ k j
        = bkMat x (lastF x) k * (bkMat x)⁻¹ k j := fun k => by
      rw [cornerRow, Matrix.of_apply, if_pos rfl, bkMat_lastF_row]
    rw [Finset.sum_congr rfl fun k _ => h1 k, ← Matrix.mul_apply, bkMat_mul_inv,
      Matrix.one_apply, cornerOne, Matrix.of_apply]
    by_cases hj : j = lastF x
    · rw [if_pos hj.symm, if_pos ⟨rfl, hj⟩]
    · rw [if_neg fun hc => hj hc.symm, if_neg fun hc => hj hc.2]
  · have h1 : ∀ k, cornerRow x i k * (bkMat x)⁻¹ k j = 0 := fun k => by
      rw [cornerRow, Matrix.of_apply, if_neg hi, zero_mul]
    rw [Finset.sum_congr rfl fun k _ => h1 k, Finset.sum_const_zero, cornerOne,
      Matrix.of_apply, if_neg fun hc => hi hc.1]

/-- `β · cornerOne = cornerOne`: the last column of `β` is the last basis
vector. -/
theorem bkMat_mul_cornerOne (x : ℕ) : bkMat x * cornerOne x = cornerOne x := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hj : j = lastF x
  · subst hj
    have h1 : ∀ k, bkMat x i k * cornerOne x k (lastF x)
        = if k = lastF x then bkMat x i k else 0 := fun k => by
      rw [cornerOne, Matrix.of_apply]
      by_cases hk : k = lastF x
      · rw [if_pos ⟨hk, rfl⟩, if_pos hk, mul_one]
      · rw [if_neg fun hc => hk hc.1, if_neg hk, mul_zero]
    rw [Finset.sum_congr rfl fun k _ => h1 k,
      Finset.sum_ite_eq' Finset.univ (lastF x) fun k => bkMat x i k,
      if_pos (Finset.mem_univ _), bkMat_col_lastF, cornerOne, Matrix.of_apply]
    by_cases hi : i = lastF x
    · rw [if_pos hi, if_pos ⟨hi, rfl⟩]
    · rw [if_neg hi, if_neg fun hc => hi hc.1]
  · have h1 : ∀ k, bkMat x i k * cornerOne x k j = 0 := fun k => by
      rw [cornerOne, Matrix.of_apply, if_neg fun hc => hj hc.2, mul_zero]
    rw [Finset.sum_congr rfl fun k _ => h1 k, Finset.sum_const_zero, cornerOne,
      Matrix.of_apply, if_neg fun hc => hj hc.2]

/-- **The inverse recursion** (Fig. 2 of arXiv:1208.5986, ascending-index
convention): `(β_{2^{x+1}})⁻¹ = fromBlocks (β_{2^x})⁻¹ 0 K (β_{2^x})⁻¹` where
the corner block `K = cornerOne x` is zero except a single `1` in its
bottom-right entry. -/
theorem bkMat_inv_succ (x : ℕ) :
    (bkMat (x + 1))⁻¹
      = Matrix.reindex (sumEquiv x) (sumEquiv x)
          (Matrix.fromBlocks (bkMat x)⁻¹ 0 (cornerOne x) (bkMat x)⁻¹) := by
  refine Matrix.inv_eq_right_inv ?_
  rw [bkMat_succ, reindex_mul, Matrix.fromBlocks_multiply]
  have h11 : bkMat x * (bkMat x)⁻¹ + 0 * cornerOne x = 1 := by
    rw [bkMat_mul_inv, Matrix.zero_mul, add_zero]
  have h12 : bkMat x * 0 + (0 : Matrix _ _ (ZMod 2)) * (bkMat x)⁻¹ = 0 := by
    rw [Matrix.mul_zero, Matrix.zero_mul, add_zero]
  have h21 : cornerRow x * (bkMat x)⁻¹ + bkMat x * cornerOne x = 0 := by
    rw [cornerRow_mul_inv, bkMat_mul_cornerOne]
    ext i j
    rw [Matrix.add_apply, Matrix.zero_apply]
    exact zmod2_add_self _
  have h22 : cornerRow x * 0 + bkMat x * (bkMat x)⁻¹ = 1 := by
    rw [Matrix.mul_zero, bkMat_mul_inv, zero_add]
  rw [h11, h12, h21, h22, Matrix.fromBlocks_one, Matrix.reindex_apply,
    Matrix.submatrix_one_equiv]

/-! ## §4. The action on bit vectors -/

/-- A bit as an element of `ZMod 2`. -/
def bitZ (b : Bool) : ZMod 2 := if b then 1 else 0

@[simp] theorem bitZ_true : bitZ true = 1 := rfl
@[simp] theorem bitZ_false : bitZ false = 0 := rfl

theorem bitZ_eq_one_iff (b : Bool) : bitZ b = 1 ↔ b = true := by
  cases b <;> simp [bitZ]

theorem decide_bitZ_eq (b : Bool) : decide (bitZ b = 1) = b := by
  cases b <;> decide

/-- `bitZ` turns `xor` into addition mod 2. -/
theorem bitZ_xor (a b : Bool) : bitZ (xor a b) = bitZ a + bitZ b := by
  cases a <;> cases b <;> decide

/-- Reading a sum mod 2 back as a `Bool` `xor`. -/
theorem decide_add_eq_one (a b : ZMod 2) :
    decide (a + b = 1) = xor (decide (a = 1)) (decide (b = 1)) := by
  revert a b; decide

/-- The mod-2 matrix–vector reading of the transform: `β_{2^x} ⬝ f`. -/
def bkVecZ (x : ℕ) (f : Fin (2 ^ x) → Bool) : Fin (2 ^ x) → ZMod 2 :=
  (bkMat x).mulVec fun j => bitZ (f j)

/-- **The Bravyi–Kitaev transform on bit vectors**: `bkVec x f i` is bit `i`
of `β_{2^x} · f (mod 2)` — arXiv:1208.5986, `b_i = Σ_j [β_n]_{ij} f_j`,
ascending-index convention. -/
def bkVec (x : ℕ) (f : Fin (2 ^ x) → Bool) : Fin (2 ^ x) → Bool :=
  fun i => decide (bkVecZ x f i = 1)

/-- `bkVec` *is* the mod-2 matrix–vector reading (definitional). -/
theorem bkVec_eq_mulVec (x : ℕ) (f : Fin (2 ^ x) → Bool) (i : Fin (2 ^ x)) :
    bkVec x f i = decide ((bkMat x).mulVec (fun j => bitZ (f j)) i = 1) := rfl

/-- The parity (mod-2 sum) of a bit vector. -/
def parityZ (x : ℕ) (f : Fin (2 ^ x) → Bool) : ZMod 2 := ∑ j, bitZ (f j)

/-- At `x = 0` the transform is the identity. -/
theorem bkVec_zero_eq (f : Fin (2 ^ 0) → Bool) : bkVec 0 f = f := by
  funext i
  rw [bkVec, bkVecZ, bkMat_zero, Matrix.one_mulVec, decide_bitZ_eq]

/-- `mulVec` through `reindex` along an equivalence. -/
theorem mulVec_reindex {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (e : m ≃ n) (M : Matrix m m (ZMod 2)) (w : n → ZMod 2) (s : m) :
    (Matrix.reindex e e M).mulVec w (e s) = M.mulVec (w ∘ e) s := by
  rw [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv, Equiv.symm_symm,
    Function.comp_apply, Equiv.symm_apply_apply]

/-- The `bkVecZ` recursion, low half: the low half of the output is the
transform of the low half of the input. -/
theorem bkVecZ_lowE (x : ℕ) (g : Fin (2 ^ (x + 1)) → Bool) (i : Fin (2 ^ x)) :
    bkVecZ (x + 1) g (lowE x i) = bkVecZ x (g ∘ lowE x) i := by
  simp only [bkVecZ, bkMat_succ, lowE]
  rw [mulVec_reindex, Matrix.fromBlocks_mulVec, Sum.elim_inl, Pi.add_apply,
    Matrix.zero_mulVec, Pi.zero_apply, add_zero]
  rfl

/-- The connecting block's `mulVec`: the total parity, concentrated on the
last coordinate. -/
theorem cornerRow_mulVec (x : ℕ) (u : Fin (2 ^ x) → ZMod 2) (i : Fin (2 ^ x)) :
    (cornerRow x).mulVec u i = if i = lastF x then ∑ j, u j else 0 := by
  rw [Matrix.mulVec_eq_sum]
  by_cases hi : i = lastF x
  · subst hi
    rw [if_pos rfl, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Pi.smul_apply, Matrix.transpose_apply, cornerRow, Matrix.of_apply,
      if_pos rfl]
    simp [MulOpposite.smul_eq_mul_unop]
  · rw [if_neg hi, Finset.sum_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Pi.smul_apply, Matrix.transpose_apply, cornerRow, Matrix.of_apply,
      if_neg hi]
    simp

/-- The `bkVecZ` recursion, high half: the transform of the high half, plus —
on the last coordinate only — the parity of the low half. -/
theorem bkVecZ_uppE (x : ℕ) (g : Fin (2 ^ (x + 1)) → Bool) (i : Fin (2 ^ x)) :
    bkVecZ (x + 1) g (uppE x i)
      = (if i = lastF x then parityZ x (g ∘ lowE x) else 0)
          + bkVecZ x (g ∘ uppE x) i := by
  simp only [bkVecZ, bkMat_succ, uppE]
  rw [mulVec_reindex, Matrix.fromBlocks_mulVec, Sum.elim_inr, Pi.add_apply,
    cornerRow_mulVec]
  rfl

/-- The `bkVec` recursion, low half. -/
theorem bkVec_lowE (x : ℕ) (g : Fin (2 ^ (x + 1)) → Bool) (i : Fin (2 ^ x)) :
    bkVec (x + 1) g (lowE x i) = bkVec x (g ∘ lowE x) i := by
  rw [bkVec, bkVec, bkVecZ_lowE]

/-- The `bkVec` recursion, high half off the last coordinate: unchanged
pattern. -/
theorem bkVec_uppE_ne (x : ℕ) (g : Fin (2 ^ (x + 1)) → Bool) (i : Fin (2 ^ x))
    (hi : i ≠ lastF x) :
    bkVec (x + 1) g (uppE x i) = bkVec x (g ∘ uppE x) i := by
  rw [bkVec, bkVec, bkVecZ_uppE, if_neg hi, zero_add]

/-- The `bkVec` recursion, last coordinate: the transformed high half absorbs
the parity of the low half. -/
theorem bkVec_uppE_lastF (x : ℕ) (g : Fin (2 ^ (x + 1)) → Bool) :
    bkVec (x + 1) g (uppE x (lastF x))
      = xor (decide (parityZ x (g ∘ lowE x) = 1))
          (bkVec x (g ∘ uppE x) (lastF x)) := by
  rw [bkVec, bkVec, bkVecZ_uppE, if_pos rfl, decide_add_eq_one]

/-- The last output bit is the total parity of the input (the all-ones last
row of `β`). -/
theorem bkVec_lastF (x : ℕ) (f : Fin (2 ^ x) → Bool) :
    bkVec x f (lastF x) = decide (parityZ x f = 1) := by
  have h : bkVecZ x f (lastF x) = parityZ x f := by
    rw [bkVecZ, Matrix.mulVec_eq_sum, Finset.sum_apply, parityZ]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Pi.smul_apply, Matrix.transpose_apply, bkMat_lastF_row]
    simp [MulOpposite.smul_eq_mul_unop]
  rw [bkVec, h]

/-! ## §5. The Fenwick parity network -/

/-- The classical action of a `CNOT` with control `c` and target `t`:
`v ↦ v[t ← v c ⊕ v t]`. -/
def cnotBit {n : ℕ} (c t : Fin n) (v : Fin n → Bool) : Fin n → Bool :=
  Function.update v t (xor (v c) (v t))

/-- The control wire of block `k` at level `ℓ`: `k·2^{ℓ+1} + 2^ℓ - 1` (the
top of the lower half-block). -/
def ctrlN (ℓ k : ℕ) : ℕ := k * 2 ^ (ℓ + 1) + (2 ^ ℓ - 1)

/-- The target wire of block `k` at level `ℓ`: `k·2^{ℓ+1} + 2^{ℓ+1} - 1` (the
top of the block). -/
def tgtN (ℓ k : ℕ) : ℕ := k * 2 ^ (ℓ + 1) + (2 ^ (ℓ + 1) - 1)

/-- A natural number as a cell of the `2^x`-cell world (clamped mod `2^x`;
the network only ever uses it in range, where the clamp is the identity). -/
def bkCell (x m : ℕ) : Fin (2 ^ x) := ⟨m % 2 ^ x, Nat.mod_lt _ (two_pow_pos x)⟩

/-- The control cell of block `k` at level `ℓ`. -/
def cellC (x ℓ k : ℕ) : Fin (2 ^ x) := bkCell x (ctrlN ℓ k)

/-- The target cell of block `k` at level `ℓ`. -/
def cellT (x ℓ k : ℕ) : Fin (2 ^ x) := bkCell x (tgtN ℓ k)

/-- Block `k` of level `ℓ` fits in the world: the guard of the network. -/
def liveG (x ℓ k : ℕ) : Prop := (k + 1) * 2 ^ (ℓ + 1) ≤ 2 ^ x

instance (x ℓ k : ℕ) : Decidable (liveG x ℓ k) := Nat.decLe _ _

theorem tgtN_lt_of_live {x ℓ k : ℕ} (h : liveG x ℓ k) : tgtN ℓ k < 2 ^ x := by
  have hP := two_pow_pos (ℓ + 1)
  rw [liveG, Nat.succ_mul] at h
  rw [tgtN]
  omega

theorem ctrlN_lt_tgtN (ℓ k : ℕ) : ctrlN ℓ k < tgtN ℓ k := by
  have h : 2 ^ ℓ < 2 ^ (ℓ + 1) := Nat.pow_lt_pow_succ one_lt_two
  have hP := two_pow_pos ℓ
  rw [ctrlN, tgtN]
  omega

theorem ctrlN_lt_of_live {x ℓ k : ℕ} (h : liveG x ℓ k) : ctrlN ℓ k < 2 ^ x :=
  (ctrlN_lt_tgtN ℓ k).trans (tgtN_lt_of_live h)

theorem cellC_val_of_live {x ℓ k : ℕ} (h : liveG x ℓ k) :
    (cellC x ℓ k : ℕ) = ctrlN ℓ k := Nat.mod_eq_of_lt (ctrlN_lt_of_live h)

theorem cellT_val_of_live {x ℓ k : ℕ} (h : liveG x ℓ k) :
    (cellT x ℓ k : ℕ) = tgtN ℓ k := Nat.mod_eq_of_lt (tgtN_lt_of_live h)

/-- A live gate's control and target are distinct cells. -/
theorem cellC_ne_cellT_of_live {x ℓ k : ℕ} (h : liveG x ℓ k) :
    cellC x ℓ k ≠ cellT x ℓ k := fun hc => absurd (congrArg Fin.val hc)
  (by rw [cellC_val_of_live h, cellT_val_of_live h]
      exact Nat.ne_of_lt (ctrlN_lt_tgtN ℓ k))

/-- One (guarded) gate of the network: apply the `CNOT` of block `k` at level
`ℓ` if the block fits, else do nothing. -/
def rungBit (x ℓ k : ℕ) (v : Fin (2 ^ x) → Bool) : Fin (2 ^ x) → Bool :=
  if liveG x ℓ k then cnotBit (cellC x ℓ k) (cellT x ℓ k) v else v

theorem rungBit_of_live {x ℓ k : ℕ} (h : liveG x ℓ k) (v : Fin (2 ^ x) → Bool) :
    rungBit x ℓ k v = cnotBit (cellC x ℓ k) (cellT x ℓ k) v := if_pos h

theorem rungBit_of_dead {x ℓ k : ℕ} (h : ¬ liveG x ℓ k) (v : Fin (2 ^ x) → Bool) :
    rungBit x ℓ k v = v := if_neg h

/-- The first `K` (guarded) gates of level `ℓ`. -/
def levelPart (x ℓ : ℕ) : ℕ → (Fin (2 ^ x) → Bool) → Fin (2 ^ x) → Bool
  | 0, v => v
  | K + 1, v => rungBit x ℓ K (levelPart x ℓ K v)

@[simp] theorem levelPart_zero (x ℓ : ℕ) (v : Fin (2 ^ x) → Bool) :
    levelPart x ℓ 0 v = v := rfl

theorem levelPart_succ (x ℓ K : ℕ) (v : Fin (2 ^ x) → Bool) :
    levelPart x ℓ (K + 1) v = rungBit x ℓ K (levelPart x ℓ K v) := rfl

/-- The whole of level `ℓ` (`2^x` guarded gate slots cover every block). -/
def levelApply (x ℓ : ℕ) (v : Fin (2 ^ x) → Bool) : Fin (2 ^ x) → Bool :=
  levelPart x ℓ (2 ^ x) v

/-- The network state after levels `0, …, ℓ - 1` (small blocks first). -/
def netVec (x : ℕ) : ℕ → (Fin (2 ^ x) → Bool) → Fin (2 ^ x) → Bool
  | 0, f => f
  | ℓ + 1, f => levelApply x ℓ (netVec x ℓ f)

@[simp] theorem netVec_zero (x : ℕ) (f : Fin (2 ^ x) → Bool) :
    netVec x 0 f = f := rfl

theorem netVec_succ (x ℓ : ℕ) (f : Fin (2 ^ x) → Bool) :
    netVec x (ℓ + 1) f = levelApply x ℓ (netVec x ℓ f) := rfl

/-! ### Saturation: a level `ℓ ≥ x` is entirely dead

At a level `ℓ ≥ x` the block guard `(k+1)·2^{ℓ+1} ≤ 2^x` fails already for
`k = 0` (`2^{ℓ+1} > 2^x`), so the whole level acts as the identity and the
network fold is stable beyond level `x`: `netVec x m f = netVec x x f` for
every `m ≥ x`. -/

/-- Every block of a level `ℓ ≥ x` is dead: the guard fails outright. -/
theorem dead_of_level_ge {x ℓ : ℕ} (h : x ≤ ℓ) (k : ℕ) : ¬ liveG x ℓ k := by
  intro hc
  rw [liveG] at hc
  have h1 : 2 ^ (ℓ + 1) ≤ (k + 1) * 2 ^ (ℓ + 1) :=
    Nat.le_mul_of_pos_left _ (Nat.succ_pos k)
  have h2 : 2 ^ x < 2 ^ (ℓ + 1) :=
    Nat.pow_lt_pow_right one_lt_two (by omega)
  omega

/-- A level prefix at a level `ℓ ≥ x` is the identity: every rung is dead. -/
theorem levelPart_of_level_ge {x ℓ : ℕ} (h : x ≤ ℓ) (v : Fin (2 ^ x) → Bool) :
    ∀ K, levelPart x ℓ K v = v
  | 0 => rfl
  | K + 1 => by
      rw [levelPart_succ, levelPart_of_level_ge h v K,
        rungBit_of_dead (dead_of_level_ge h K)]

/-- **A whole level `ℓ ≥ x` is the identity.** -/
theorem levelApply_of_ge {x ℓ : ℕ} (h : x ≤ ℓ) (v : Fin (2 ^ x) → Bool) :
    levelApply x ℓ v = v :=
  levelPart_of_level_ge h v (2 ^ x)

/-- **The network fold saturates at level `x`**: the levels beyond `x` are
identities, so running the fold to any `m ≥ x` gives the level-`x` state. -/
theorem netVec_of_ge (x : ℕ) (f : Fin (2 ^ x) → Bool) :
    ∀ m, x ≤ m → netVec x m f = netVec x x f := by
  intro m
  induction m with
  | zero => intro h; obtain rfl : x = 0 := Nat.le_zero.mp h; rfl
  | succ m ih =>
      intro h
      rcases Nat.lt_or_ge x (m + 1) with hlt | hge
      · have hm : x ≤ m := by omega
        rw [netVec_succ, ih hm, levelApply_of_ge hm]
      · obtain rfl : x = m + 1 := by omega
        rfl

/-! ## §6. Splitting the network across the halves -/

/-- A gate inside the low half, read on the low half. -/
theorem cnotBit_lowE_comp_lowE (x : ℕ) (c t : Fin (2 ^ x))
    (v : Fin (2 ^ (x + 1)) → Bool) :
    cnotBit (lowE x c) (lowE x t) v ∘ lowE x = cnotBit c t (v ∘ lowE x) := by
  simp only [cnotBit]
  rw [Function.update_comp_eq_of_injective _ (lowE_injective x)]
  rfl

/-- A gate inside the low half fixes the high half. -/
theorem cnotBit_lowE_comp_uppE (x : ℕ) (c t : Fin (2 ^ x))
    (v : Fin (2 ^ (x + 1)) → Bool) :
    cnotBit (lowE x c) (lowE x t) v ∘ uppE x = v ∘ uppE x := by
  simp only [cnotBit]
  exact Function.update_comp_eq_of_forall_ne _ _ fun i => (lowE_ne_uppE x t i).symm

/-- A gate inside the high half, read on the high half. -/
theorem cnotBit_uppE_comp_uppE (x : ℕ) (c t : Fin (2 ^ x))
    (v : Fin (2 ^ (x + 1)) → Bool) :
    cnotBit (uppE x c) (uppE x t) v ∘ uppE x = cnotBit c t (v ∘ uppE x) := by
  simp only [cnotBit]
  rw [Function.update_comp_eq_of_injective _ (uppE_injective x)]
  rfl

/-- A gate inside the high half fixes the low half. -/
theorem cnotBit_uppE_comp_lowE (x : ℕ) (c t : Fin (2 ^ x))
    (v : Fin (2 ^ (x + 1)) → Bool) :
    cnotBit (uppE x c) (uppE x t) v ∘ lowE x = v ∘ lowE x := by
  simp only [cnotBit]
  exact Function.update_comp_eq_of_forall_ne _ _ fun i => lowE_ne_uppE x i t

section Split

variable {x ℓ d : ℕ}

/-- `2^d · 2^{ℓ+1} = 2^x` when `d + (ℓ+1) = x`. -/
theorem pow_mul_of_add (hd : d + (ℓ + 1) = x) : 2 ^ d * 2 ^ (ℓ + 1) = 2 ^ x := by
  rw [← pow_add, hd]

/-- Blocks `k < 2^d` are live in the world `x`. -/
theorem live_of_lt (hd : d + (ℓ + 1) = x) (hk : k < 2 ^ d) : liveG x ℓ k := by
  rw [liveG, ← pow_mul_of_add hd]
  exact Nat.mul_le_mul_right _ hk

/-- Blocks `k ≥ 2^d` are dead in the world `x`. -/
theorem dead_of_ge (hd : d + (ℓ + 1) = x) (hk : 2 ^ d ≤ k) : ¬ liveG x ℓ k := by
  intro hc
  rw [liveG, ← pow_mul_of_add hd] at hc
  have h1 : k + 1 ≤ 2 ^ d := Nat.le_of_mul_le_mul_right hc (two_pow_pos (ℓ + 1))
  omega

/-- In the doubled world, a block `k < 2^d` of level `ℓ` (`d + (ℓ+1) = x`) is
the corresponding low-half gate, embedded. -/
theorem rungBit_succ_low (hd : d + (ℓ + 1) = x) (hk : k < 2 ^ d)
    (v : Fin (2 ^ (x + 1)) → Bool) :
    rungBit (x + 1) ℓ k v
      = cnotBit (lowE x (cellC x ℓ k)) (lowE x (cellT x ℓ k)) v := by
  have hlive : liveG x ℓ k := live_of_lt hd hk
  have hlive' : liveG (x + 1) ℓ k :=
    hlive.trans (Nat.pow_le_pow_right two_pos (Nat.le_succ x))
  rw [rungBit_of_live hlive']
  have hc : cellC (x + 1) ℓ k = lowE x (cellC x ℓ k) :=
    Fin.ext (by rw [cellC_val_of_live hlive', lowE_val, cellC_val_of_live hlive])
  have ht : cellT (x + 1) ℓ k = lowE x (cellT x ℓ k) :=
    Fin.ext (by rw [cellT_val_of_live hlive', lowE_val, cellT_val_of_live hlive])
  rw [hc, ht]

/-- In the doubled world, block `2^d + k` of level `ℓ` (`d + (ℓ+1) = x`) is
block `k` of the high half: the embedded high-half gate when `k` is live
there, nothing when it is dead. -/
theorem rungBit_succ_upp (hd : d + (ℓ + 1) = x) (k : ℕ)
    (v : Fin (2 ^ (x + 1)) → Bool) :
    rungBit (x + 1) ℓ (2 ^ d + k) v
      = if liveG x ℓ k then
          cnotBit (uppE x (cellC x ℓ k)) (uppE x (cellT x ℓ k)) v
        else v := by
  have hsplit : (2 ^ d + k + 1) * 2 ^ (ℓ + 1)
      = 2 ^ x + (k + 1) * 2 ^ (ℓ + 1) := by
    rw [add_assoc, add_mul, pow_mul_of_add hd]
  have hguard : liveG (x + 1) ℓ (2 ^ d + k) ↔ liveG x ℓ k := by
    rw [liveG, liveG, ← two_pow_succ x, hsplit]
    omega
  by_cases h : liveG x ℓ k
  · rw [if_pos h, rungBit_of_live (hguard.mpr h)]
    have hcn : ctrlN ℓ (2 ^ d + k) = 2 ^ x + ctrlN ℓ k := by
      rw [ctrlN, ctrlN, add_mul, pow_mul_of_add hd, add_assoc]
    have htn : tgtN ℓ (2 ^ d + k) = 2 ^ x + tgtN ℓ k := by
      rw [tgtN, tgtN, add_mul, pow_mul_of_add hd, add_assoc]
    have hc : cellC (x + 1) ℓ (2 ^ d + k) = uppE x (cellC x ℓ k) :=
      Fin.ext (by
        rw [cellC_val_of_live (hguard.mpr h), uppE_val, cellC_val_of_live h, hcn])
    have ht : cellT (x + 1) ℓ (2 ^ d + k) = uppE x (cellT x ℓ k) :=
      Fin.ext (by
        rw [cellT_val_of_live (hguard.mpr h), uppE_val, cellT_val_of_live h, htn])
    rw [hc, ht]
  · rw [if_neg h]
    exact rungBit_of_dead (fun hc => h (hguard.mp hc)) v

/-- The low-half split of a level prefix in the doubled world: gates `k < 2^d`
are the embedded low-half gates, and every later gate fixes the low half, so
the fold projects onto the low-half fold — for **every** prefix length. -/
theorem levelPart_succ_comp_lowE (hd : d + (ℓ + 1) = x)
    (v : Fin (2 ^ (x + 1)) → Bool) :
    ∀ K, levelPart (x + 1) ℓ K v ∘ lowE x = levelPart x ℓ K (v ∘ lowE x)
  | 0 => rfl
  | K + 1 => by
      rw [levelPart_succ, levelPart_succ]
      by_cases hK : K < 2 ^ d
      · rw [rungBit_succ_low hd hK, cnotBit_lowE_comp_lowE,
          levelPart_succ_comp_lowE hd v K, rungBit_of_live (live_of_lt hd hK)]
      · have hK' : 2 ^ d ≤ K := Nat.le_of_not_lt hK
        rw [rungBit_of_dead (dead_of_ge hd hK') (levelPart x ℓ K (v ∘ lowE x)),
          ← levelPart_succ_comp_lowE hd v K]
        obtain ⟨k, rfl⟩ : ∃ k, K = 2 ^ d + k := ⟨K - 2 ^ d, by omega⟩
        rw [rungBit_succ_upp hd]
        by_cases h : liveG x ℓ k
        · rw [if_pos h, cnotBit_uppE_comp_lowE]
        · rw [if_neg h]

/-- Gates `k < 2^d` of a level in the doubled world fix the high half: the
prefix of low-half gates is invisible there. -/
theorem levelPart_succ_comp_uppE_prefix (hd : d + (ℓ + 1) = x)
    (v : Fin (2 ^ (x + 1)) → Bool) :
    ∀ K, K ≤ 2 ^ d → levelPart (x + 1) ℓ K v ∘ uppE x = v ∘ uppE x
  | 0, _ => rfl
  | K + 1, hK => by
      rw [levelPart_succ, rungBit_succ_low hd (by omega), cnotBit_lowE_comp_uppE,
        levelPart_succ_comp_uppE_prefix hd v K (by omega)]

/-- The high-half split of a level in the doubled world: after the `2^d`
low-half gates, gate `2^d + k` is the embedded high-half gate `k`, so the
offset fold projects onto the high-half fold. -/
theorem levelPart_succ_comp_uppE (hd : d + (ℓ + 1) = x)
    (v : Fin (2 ^ (x + 1)) → Bool) :
    ∀ K, levelPart (x + 1) ℓ (2 ^ d + K) v ∘ uppE x
      = levelPart x ℓ K (v ∘ uppE x)
  | 0 => levelPart_succ_comp_uppE_prefix hd v (2 ^ d) le_rfl
  | K + 1 => by
      rw [show 2 ^ d + (K + 1) = (2 ^ d + K) + 1 from rfl, levelPart_succ,
        levelPart_succ, rungBit_succ_upp hd K]
      by_cases h : liveG x ℓ K
      · rw [if_pos h, cnotBit_uppE_comp_uppE, levelPart_succ_comp_uppE hd v K,
          rungBit_of_live h]
      · rw [if_neg h, levelPart_succ_comp_uppE hd v K, rungBit_of_dead h]

/-- The level fold is stable once every block is covered: gate slots
`K ≥ 2^x` are dead. -/
theorem levelPart_stable (x ℓ : ℕ) (v : Fin (2 ^ x) → Bool) :
    ∀ K, 2 ^ x ≤ K → levelPart x ℓ K v = levelApply x ℓ v := by
  intro K
  induction K with
  | zero => intro h; have := two_pow_pos x; omega
  | succ K ih =>
      intro h
      rcases Nat.lt_or_ge K (2 ^ x) with hK | hK
      · have hKx : K + 1 = 2 ^ x := by omega
        rw [hKx, levelApply]
      · have hdead : ¬ liveG x ℓ K := by
          intro hc
          rw [liveG] at hc
          have h1 : K + 1 ≤ (K + 1) * 2 ^ (ℓ + 1) :=
            Nat.le_mul_of_pos_right _ (two_pow_pos (ℓ + 1))
          omega
        rw [levelPart_succ, rungBit_of_dead hdead, ih hK]

/-- The low-half split of a whole level. -/
theorem levelApply_succ_comp_lowE (hd : d + (ℓ + 1) = x)
    (v : Fin (2 ^ (x + 1)) → Bool) :
    levelApply (x + 1) ℓ v ∘ lowE x = levelApply x ℓ (v ∘ lowE x) := by
  rw [levelApply, levelPart_succ_comp_lowE hd v (2 ^ (x + 1)),
    levelPart_stable x ℓ _ (2 ^ (x + 1))
      (Nat.pow_le_pow_right two_pos (Nat.le_succ x))]

/-- The high-half split of a whole level. -/
theorem levelApply_succ_comp_uppE (hd : d + (ℓ + 1) = x)
    (v : Fin (2 ^ (x + 1)) → Bool) :
    levelApply (x + 1) ℓ v ∘ uppE x = levelApply x ℓ (v ∘ uppE x) := by
  have hdx : 2 ^ d ≤ 2 ^ x := Nat.pow_le_pow_right two_pos (by omega)
  have h2 := two_pow_succ x
  have hdx' : 2 ^ d ≤ 2 ^ (x + 1) :=
    hdx.trans (Nat.pow_le_pow_right two_pos (Nat.le_succ x))
  have h3 : 2 ^ x ≤ 2 ^ (x + 1) - 2 ^ d :=
    Nat.le_sub_of_add_le (by rw [← h2]; exact Nat.add_le_add_left hdx _)
  have key := levelPart_succ_comp_uppE hd v (2 ^ (x + 1) - 2 ^ d)
  rw [Nat.add_sub_cancel' hdx'] at key
  rw [levelApply, key, levelPart_stable x ℓ _ _ h3]

end Split

/-- The network split: through level `ℓ ≤ x`, the doubled network acts as the
half-size network on each half independently. -/
theorem netVec_succ_comp (x : ℕ) (g : Fin (2 ^ (x + 1)) → Bool) :
    ∀ ℓ, ℓ ≤ x →
      netVec (x + 1) ℓ g ∘ lowE x = netVec x ℓ (g ∘ lowE x)
        ∧ netVec (x + 1) ℓ g ∘ uppE x = netVec x ℓ (g ∘ uppE x)
  | 0, _ => ⟨rfl, rfl⟩
  | ℓ + 1, hℓ => by
      have hd : (x - (ℓ + 1)) + (ℓ + 1) = x := by omega
      obtain ⟨hlow, hupp⟩ := netVec_succ_comp x g ℓ (by omega)
      constructor
      · rw [netVec_succ, netVec_succ, levelApply_succ_comp_lowE hd, hlow]
      · rw [netVec_succ, netVec_succ, levelApply_succ_comp_uppE hd, hupp]

/-- The top level of the doubled network is the single cross-half `CNOT` from
the last cell of the low half into the last cell of the world. -/
theorem levelApply_top (x : ℕ) (v : Fin (2 ^ (x + 1)) → Bool) :
    levelApply (x + 1) x v = cnotBit (lowE x (lastF x)) (uppE x (lastF x)) v := by
  have hlive : liveG (x + 1) x 0 := by
    rw [liveG]
    omega
  have hone : levelPart (x + 1) x 1 v
      = cnotBit (lowE x (lastF x)) (uppE x (lastF x)) v := by
    rw [levelPart_succ, levelPart_zero, rungBit_of_live hlive]
    have h1 := two_pow_pos x
    have h2 := two_pow_succ x
    have hc : cellC (x + 1) x 0 = lowE x (lastF x) :=
      Fin.ext (by rw [cellC_val_of_live hlive, lowE_val, lastF_val, ctrlN]; omega)
    have ht : cellT (x + 1) x 0 = uppE x (lastF x) :=
      Fin.ext (by rw [cellT_val_of_live hlive, uppE_val, lastF_val, tgtN]; omega)
    rw [hc, ht]
  have hstable : ∀ K, 1 ≤ K → levelPart (x + 1) x K v = levelPart (x + 1) x 1 v := by
    intro K
    induction K with
    | zero => omega
    | succ K ih =>
        intro h
        rcases Nat.lt_or_ge K 1 with hK | hK
        · have : K = 0 := by omega
          rw [this]
        · have hdead : ¬ liveG (x + 1) x K := by
            intro hc
            rw [liveG] at hc
            have hP := two_pow_pos (x + 1)
            have h1 : 2 * 2 ^ (x + 1) ≤ (K + 1) * 2 ^ (x + 1) :=
              Nat.mul_le_mul_right _ (by omega)
            omega
          rw [levelPart_succ, rungBit_of_dead hdead, ih hK]
  rw [levelApply, hstable (2 ^ (x + 1)) (two_pow_pos (x + 1)), hone]

/-- **Program-vs-matrix agreement**: the level-by-level Fenwick `CNOT` network
computes exactly the Bravyi–Kitaev basis change `β_{2^x}` of arXiv:1208.5986
(Fig. 2, ascending-index convention). -/
theorem netVec_top : ∀ x (f : Fin (2 ^ x) → Bool), netVec x x f = bkVec x f
  | 0, f => (bkVec_zero_eq f).symm
  | x + 1, g => by
      obtain ⟨hlow, hupp⟩ := netVec_succ_comp x g x le_rfl
      have hlow' : netVec (x + 1) x g ∘ lowE x = bkVec x (g ∘ lowE x) := by
        rw [hlow, netVec_top x]
      have hupp' : netVec (x + 1) x g ∘ uppE x = bkVec x (g ∘ uppE x) := by
        rw [hupp, netVec_top x]
      rw [netVec_succ, levelApply_top]
      funext m
      rcases lowE_or_uppE x m with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · rw [cnotBit, Function.update_of_ne (lowE_ne_uppE x j (lastF x)),
          bkVec_lowE]
        exact congrFun hlow' j
      · by_cases hj : j = lastF x
        · subst hj
          rw [cnotBit, Function.update_self, bkVec_uppE_lastF, ← bkVec_lastF,
            ← congrFun hlow' (lastF x), ← congrFun hupp' (lastF x)]
          rfl
        · rw [cnotBit,
            Function.update_of_ne fun hc => hj (uppE_injective x hc),
            bkVec_uppE_ne x g j hj]
          exact congrFun hupp' j

end Qhl.BravyiKitaev
