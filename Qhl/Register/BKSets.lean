import Qhl.Register.BravyiKitaev

/-!
# The Bravyi–Kitaev index sets: parity, update, flip, remainder

The qubit index sets of Seeley–Richard–Love (arXiv:1208.5986 §IV), in the
ascending-index convention of `Qhl/Register/BravyiKitaev.lean`, each defined by
its matrix characterization from that paper and each given its Fenwick block
recursion, its `O(log n)` cardinality bound, and its *semantic* content:

* `piMat` — the strictly-lower-triangular all-ones parity matrix `π_n`
  (`(π f)_i = Σ_{k<i} f_k`), with its block recursion `piMat_succ`;
* `pMat = π_n · β_n⁻¹` — the Bravyi–Kitaev-to-parity transformation; the
  **parity set** `pSet x j = P(j)` is the support of its row `j`
  (strictly lower triangular, `pMat_eq_zero_of_le`);
* the **update set** `uSet x j = U(j)`: the nonzero entries of column `j` of
  `β_n` above the diagonal;
* the **flip set** `fSet x j = F(j)`: the nonzero entries of row `j` of
  `β_n⁻¹` off the diagonal (`bkInv_diag`/`bkInv_eq_zero_of_lt`: `β⁻¹` is unit
  lower triangular);
* the combined set `rhoSet x j = ρ(j)`: `P(j)` for even `j`, the remainder set
  `R(j) = P(j) \ F(j)` for odd `j`.

Block recursions (`pSet_lowE`/`pSet_uppE`, `uSet_lowE`/`uSet_uppE`,
`fSet_lowE`/`fSet_uppE`/`fSet_uppE_lastF`) drive the structural facts
`fSet_of_even` (`F(j) = ∅` for even `j`), `fSet_subset_pSet_of_odd`
(`F(j) ⊆ P(j)` for odd `j`) and the support bounds
`card_pSet_le`/`card_uSet_le`/`card_fSet_le` (each set has at most
`x = log₂ n` elements).

Semantic lemmas, all pure mod-2 matrix algebra:

* `pSet_parityZ` — the parity of the Bravyi–Kitaev bits on `P(j)` is the
  parity of the occupation bits below `j`;
* `fSet_parityZ` — the Bravyi–Kitaev bit at `j` plus the parity on `F(j)`
  is the occupation bit at `j`;
* `bkVec_flip` — flipping occupation bit `j` flips exactly the Bravyi–Kitaev
  bits on `{j} ∪ U(j)`;
* `rho_parity` — the combined sign rule the Bravyi–Kitaev ladder operators
  use: `b_j + Σ_{ρ(j)} b + Σ_{P(j)} b = f_j`;
* `bkEquiv` — the transform is a bijection on bit vectors.
-/

namespace Qhl.BravyiKitaev

open Finset Matrix

/-! ## §1. Entry lemmas and triangularity of the inverse -/

@[simp] theorem bkInv_low_low (x : ℕ) (i j : Fin (2 ^ x)) :
    (bkMat (x + 1))⁻¹ (lowE x i) (lowE x j) = (bkMat x)⁻¹ i j := by
  rw [bkMat_inv_succ, Matrix.reindex_apply, Matrix.submatrix_apply,
    sumEquiv_symm_lowE, sumEquiv_symm_lowE, Matrix.fromBlocks_apply₁₁]

@[simp] theorem bkInv_low_upp (x : ℕ) (i j : Fin (2 ^ x)) :
    (bkMat (x + 1))⁻¹ (lowE x i) (uppE x j) = 0 := by
  rw [bkMat_inv_succ, Matrix.reindex_apply, Matrix.submatrix_apply,
    sumEquiv_symm_lowE, sumEquiv_symm_uppE, Matrix.fromBlocks_apply₁₂,
    Matrix.zero_apply]

@[simp] theorem bkInv_upp_low (x : ℕ) (i j : Fin (2 ^ x)) :
    (bkMat (x + 1))⁻¹ (uppE x i) (lowE x j)
      = if i = lastF x ∧ j = lastF x then 1 else 0 := by
  rw [bkMat_inv_succ, Matrix.reindex_apply, Matrix.submatrix_apply,
    sumEquiv_symm_uppE, sumEquiv_symm_lowE, Matrix.fromBlocks_apply₂₁]
  rfl

@[simp] theorem bkInv_upp_upp (x : ℕ) (i j : Fin (2 ^ x)) :
    (bkMat (x + 1))⁻¹ (uppE x i) (uppE x j) = (bkMat x)⁻¹ i j := by
  rw [bkMat_inv_succ, Matrix.reindex_apply, Matrix.submatrix_apply,
    sumEquiv_symm_uppE, sumEquiv_symm_uppE, Matrix.fromBlocks_apply₂₂]

/-- `β⁻¹` has unit diagonal. -/
theorem bkInv_diag : ∀ x (i : Fin (2 ^ x)), (bkMat x)⁻¹ i i = 1
  | 0, i => by
      have h : (bkMat 0)⁻¹ = 1 := by
        rw [bkMat_zero]
        exact Matrix.inv_eq_right_inv (by rw [one_mul])
      rw [h, Matrix.one_apply_eq]
  | x + 1, m => by
      rcases lowE_or_uppE x m with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · rw [bkInv_low_low]; exact bkInv_diag x i
      · rw [bkInv_upp_upp]; exact bkInv_diag x i

/-- `β⁻¹` is lower triangular. -/
theorem bkInv_eq_zero_of_lt :
    ∀ x (i j : Fin (2 ^ x)), (i : ℕ) < (j : ℕ) → (bkMat x)⁻¹ i j = 0
  | 0, i, j, hij => absurd hij (by have h1 := i.isLt; have h2 := j.isLt; omega)
  | x + 1, m, m', hij => by
      rcases lowE_or_uppE x m with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
        rcases lowE_or_uppE x m' with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · rw [bkInv_low_low]
        exact bkInv_eq_zero_of_lt x i j (by simpa using hij)
      · rw [bkInv_low_upp]
      · rw [lowE_val, uppE_val] at hij
        have := j.isLt
        omega
      · rw [bkInv_upp_upp]
        exact bkInv_eq_zero_of_lt x i j (by simpa using hij)

/-! ## §2. The parity matrix `π` and the composition `π · β⁻¹` -/

/-- The strictly-lower-triangular all-ones parity matrix `π_n`:
`(π f)_i = Σ_{k < i} f_k`, the strict-prefix parity. -/
def piMat (x : ℕ) : Matrix (Fin (2 ^ x)) (Fin (2 ^ x)) (ZMod 2) :=
  Matrix.of fun i j => if (j : ℕ) < (i : ℕ) then 1 else 0

/-- The all-ones matrix (the lower-left block of the `π` recursion). -/
def onesM (x : ℕ) : Matrix (Fin (2 ^ x)) (Fin (2 ^ x)) (ZMod 2) :=
  Matrix.of fun _ _ => 1

/-- The matrix with every row equal to the last standard basis row (the
lower-left block of the `π·β⁻¹` recursion). -/
def lastColM (x : ℕ) : Matrix (Fin (2 ^ x)) (Fin (2 ^ x)) (ZMod 2) :=
  Matrix.of fun _ j => if j = lastF x then 1 else 0

/-- The block recursion of the parity matrix. -/
theorem piMat_succ (x : ℕ) :
    piMat (x + 1)
      = Matrix.reindex (sumEquiv x) (sumEquiv x)
          (Matrix.fromBlocks (piMat x) 0 (onesM x) (piMat x)) := by
  ext m m'
  rw [Matrix.reindex_apply, Matrix.submatrix_apply]
  rcases lowE_or_uppE x m with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
    rcases lowE_or_uppE x m' with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [sumEquiv_symm_lowE, sumEquiv_symm_lowE, Matrix.fromBlocks_apply₁₁]
    simp only [piMat, Matrix.of_apply, lowE_val]
  · rw [sumEquiv_symm_lowE, sumEquiv_symm_uppE, Matrix.fromBlocks_apply₁₂,
      Matrix.zero_apply]
    simp only [piMat, Matrix.of_apply, lowE_val, uppE_val]
    rw [if_neg (by have := i.isLt; omega)]
  · rw [sumEquiv_symm_uppE, sumEquiv_symm_lowE, Matrix.fromBlocks_apply₂₁]
    simp only [piMat, Matrix.of_apply, uppE_val, lowE_val, onesM]
    rw [if_pos (by have := j.isLt; omega)]
  · rw [sumEquiv_symm_uppE, sumEquiv_symm_uppE, Matrix.fromBlocks_apply₂₂]
    simp only [piMat, Matrix.of_apply, uppE_val, Nat.add_lt_add_iff_left]

/-- **The Bravyi–Kitaev-to-parity matrix** `π_n · β_n⁻¹` (arXiv:1208.5986
§IV.A): its row `j` names the Bravyi–Kitaev qubits whose parity is the parity
of the occupations below `j`. -/
noncomputable def pMat (x : ℕ) : Matrix (Fin (2 ^ x)) (Fin (2 ^ x)) (ZMod 2) :=
  piMat x * (bkMat x)⁻¹

/-- `π · cornerOne = 0` (the last index is maximal). -/
theorem piMat_mul_cornerOne (x : ℕ) : piMat x * cornerOne x = 0 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [cornerOne, Matrix.of_apply]
  by_cases hm : m = lastF x ∧ j = lastF x
  · rw [if_pos hm, mul_one, hm.1, piMat, Matrix.of_apply, if_neg]
    rw [lastF_val]
    have := i.isLt
    omega
  · rw [if_neg hm, mul_zero]

/-- The column sums of `β⁻¹` mod 2: `1` exactly in the last column (the
all-ones last row of `β`). -/
theorem bkInv_colSum (x : ℕ) (k : Fin (2 ^ x)) :
    ∑ m, (bkMat x)⁻¹ m k = if k = lastF x then 1 else 0 := by
  have h1 : ∀ m, (bkMat x)⁻¹ m k = bkMat x (lastF x) m * (bkMat x)⁻¹ m k :=
    fun m => by rw [bkMat_lastF_row, one_mul]
  rw [Finset.sum_congr rfl fun m _ => h1 m, ← Matrix.mul_apply, bkMat_mul_inv,
    Matrix.one_apply]
  by_cases hk : k = lastF x
  · rw [if_pos hk.symm, if_pos hk]
  · rw [if_neg fun hc => hk hc.symm, if_neg hk]

/-- `onesM · β⁻¹ = lastColM`. -/
theorem onesM_mul_bkInv (x : ℕ) : onesM x * (bkMat x)⁻¹ = lastColM x := by
  ext i j
  rw [Matrix.mul_apply, lastColM, Matrix.of_apply, ← bkInv_colSum x j]
  exact Finset.sum_congr rfl fun m _ => by rw [onesM, Matrix.of_apply, one_mul]

/-- The block recursion of `π · β⁻¹`. -/
theorem pMat_succ (x : ℕ) :
    pMat (x + 1)
      = Matrix.reindex (sumEquiv x) (sumEquiv x)
          (Matrix.fromBlocks (pMat x) 0 (lastColM x) (pMat x)) := by
  rw [pMat, piMat_succ, bkMat_inv_succ, reindex_mul, Matrix.fromBlocks_multiply]
  have h11 : piMat x * (bkMat x)⁻¹ + (0 : Matrix _ _ (ZMod 2)) * cornerOne x
      = pMat x := by
    rw [Matrix.zero_mul, add_zero, pMat]
  have h12 : piMat x * 0 + (0 : Matrix _ _ (ZMod 2)) * (bkMat x)⁻¹ = 0 := by
    rw [Matrix.mul_zero, Matrix.zero_mul, add_zero]
  have h21 : onesM x * (bkMat x)⁻¹ + piMat x * cornerOne x = lastColM x := by
    rw [onesM_mul_bkInv, piMat_mul_cornerOne, add_zero]
  have h22 : onesM x * 0 + piMat x * (bkMat x)⁻¹ = pMat x := by
    rw [Matrix.mul_zero, zero_add, pMat]
  rw [h11, h12, h21, h22]

@[simp] theorem pMat_low_low (x : ℕ) (i j : Fin (2 ^ x)) :
    pMat (x + 1) (lowE x i) (lowE x j) = pMat x i j := by
  rw [pMat_succ, Matrix.reindex_apply, Matrix.submatrix_apply,
    sumEquiv_symm_lowE, sumEquiv_symm_lowE, Matrix.fromBlocks_apply₁₁]

@[simp] theorem pMat_low_upp (x : ℕ) (i j : Fin (2 ^ x)) :
    pMat (x + 1) (lowE x i) (uppE x j) = 0 := by
  rw [pMat_succ, Matrix.reindex_apply, Matrix.submatrix_apply,
    sumEquiv_symm_lowE, sumEquiv_symm_uppE, Matrix.fromBlocks_apply₁₂,
    Matrix.zero_apply]

@[simp] theorem pMat_upp_low (x : ℕ) (i j : Fin (2 ^ x)) :
    pMat (x + 1) (uppE x i) (lowE x j) = if j = lastF x then 1 else 0 := by
  rw [pMat_succ, Matrix.reindex_apply, Matrix.submatrix_apply,
    sumEquiv_symm_uppE, sumEquiv_symm_lowE, Matrix.fromBlocks_apply₂₁]
  rfl

@[simp] theorem pMat_upp_upp (x : ℕ) (i j : Fin (2 ^ x)) :
    pMat (x + 1) (uppE x i) (uppE x j) = pMat x i j := by
  rw [pMat_succ, Matrix.reindex_apply, Matrix.submatrix_apply,
    sumEquiv_symm_uppE, sumEquiv_symm_uppE, Matrix.fromBlocks_apply₂₂]

/-- `π · β⁻¹` is strictly lower triangular. -/
theorem pMat_eq_zero_of_le (x : ℕ) (j k : Fin (2 ^ x)) (h : (j : ℕ) ≤ (k : ℕ)) :
    pMat x j k = 0 := by
  rw [pMat, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun m _ => ?_
  by_cases hm : (m : ℕ) < (j : ℕ)
  · rw [bkInv_eq_zero_of_lt x m k (by omega), mul_zero]
  · rw [piMat, Matrix.of_apply, if_neg hm, zero_mul]

/-! ## §3. The sets `P(j)`, `U(j)`, `F(j)`, `ρ(j)` -/

/-- **The parity set** `P(j)`: the support of row `j` of `π_n β_n⁻¹`
(arXiv:1208.5986 §IV.A; the entries right of the diagonal — strictness is
automatic by `pMat_eq_zero_of_le`). -/
noncomputable def pSet (x : ℕ) (j : Fin (2 ^ x)) : Finset (Fin (2 ^ x)) :=
  univ.filter fun k => pMat x j k = 1

/-- **The update set** `U(j)`: the nonzero entries of column `j` of `β_n`
above the main diagonal (arXiv:1208.5986 §IV.B). -/
def uSet (x : ℕ) (j : Fin (2 ^ x)) : Finset (Fin (2 ^ x)) :=
  univ.filter fun k => bkMat x k j = 1 ∧ (j : ℕ) < (k : ℕ)

/-- **The flip set** `F(j)`: the nonzero entries of row `j` of `β_n⁻¹` right
of the main diagonal (arXiv:1208.5986 §IV.C). -/
noncomputable def fSet (x : ℕ) (j : Fin (2 ^ x)) : Finset (Fin (2 ^ x)) :=
  univ.filter fun k => (bkMat x)⁻¹ j k = 1 ∧ (k : ℕ) < (j : ℕ)

/-- **The set `ρ(j)`** (arXiv:1208.5986 eq. (28)): the parity set for even
`j`, the remainder set `R(j) = P(j) \ F(j)` for odd `j`. -/
noncomputable def rhoSet (x : ℕ) (j : Fin (2 ^ x)) : Finset (Fin (2 ^ x)) :=
  if Even (j : ℕ) then pSet x j else pSet x j \ fSet x j

theorem mem_pSet {x : ℕ} {j k : Fin (2 ^ x)} :
    k ∈ pSet x j ↔ pMat x j k = 1 := by
  rw [pSet, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨mem_univ k, h⟩⟩

theorem mem_uSet {x : ℕ} {j k : Fin (2 ^ x)} :
    k ∈ uSet x j ↔ bkMat x k j = 1 ∧ (j : ℕ) < (k : ℕ) := by
  rw [uSet, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨mem_univ k, h⟩⟩

theorem mem_fSet {x : ℕ} {j k : Fin (2 ^ x)} :
    k ∈ fSet x j ↔ (bkMat x)⁻¹ j k = 1 ∧ (k : ℕ) < (j : ℕ) := by
  rw [fSet, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨mem_univ k, h⟩⟩

/-- Parity-set members lie strictly below `j`. -/
theorem lt_of_mem_pSet {x : ℕ} {j k : Fin (2 ^ x)} (h : k ∈ pSet x j) :
    (k : ℕ) < (j : ℕ) := by
  by_contra hc
  rw [mem_pSet, pMat_eq_zero_of_le x j k (by omega)] at h
  exact absurd h (by decide)

/-- Update-set members lie strictly above `j`. -/
theorem lt_of_mem_uSet {x : ℕ} {j k : Fin (2 ^ x)} (h : k ∈ uSet x j) :
    (j : ℕ) < (k : ℕ) := (mem_uSet.mp h).2

/-- Flip-set members lie strictly below `j`. -/
theorem lt_of_mem_fSet {x : ℕ} {j k : Fin (2 ^ x)} (h : k ∈ fSet x j) :
    (k : ℕ) < (j : ℕ) := (mem_fSet.mp h).2

theorem rhoSet_subset_pSet (x : ℕ) (j : Fin (2 ^ x)) : rhoSet x j ⊆ pSet x j := by
  rw [rhoSet]
  split_ifs
  · exact Finset.Subset.rfl
  · exact Finset.sdiff_subset

/-! ## §4. Base cases and block recursions -/

theorem pSet_zero (j : Fin (2 ^ 0)) : pSet 0 j = ∅ := by
  ext k
  rw [mem_pSet, pMat_eq_zero_of_le 0 j k
    (by have := j.isLt; have := k.isLt; omega)]
  simp only [Finset.notMem_empty, iff_false]
  decide +kernel

theorem uSet_zero (j : Fin (2 ^ 0)) : uSet 0 j = ∅ := by
  ext k
  rw [mem_uSet]
  have h1 := j.isLt
  have h2 := k.isLt
  simp only [Finset.notMem_empty, iff_false, not_and]
  omega

theorem fSet_zero (j : Fin (2 ^ 0)) : fSet 0 j = ∅ := by
  ext k
  rw [mem_fSet]
  have h1 := j.isLt
  have h2 := k.isLt
  simp only [Finset.notMem_empty, iff_false, not_and]
  omega

/-- `(0 : ZMod 2) ≠ 1`, in rewriting form. -/
theorem zmod2_zero_ne_one : (0 : ZMod 2) ≠ 1 := by decide

theorem pSet_lowE (x : ℕ) (i : Fin (2 ^ x)) :
    pSet (x + 1) (lowE x i) = (pSet x i).image (lowE x) := by
  ext k
  rw [mem_pSet, Finset.mem_image]
  constructor
  · intro hk
    rcases lowE_or_uppE x k with ⟨k', rfl⟩ | ⟨k', rfl⟩
    · rw [pMat_low_low] at hk
      exact ⟨k', mem_pSet.mpr hk, rfl⟩
    · rw [pMat_low_upp] at hk
      exact absurd hk zmod2_zero_ne_one
  · rintro ⟨k', hk', rfl⟩
    rw [pMat_low_low]
    exact mem_pSet.mp hk'

theorem pSet_uppE (x : ℕ) (i : Fin (2 ^ x)) :
    pSet (x + 1) (uppE x i)
      = insert (lowE x (lastF x)) ((pSet x i).image (uppE x)) := by
  ext k
  rw [mem_pSet, Finset.mem_insert, Finset.mem_image]
  constructor
  · intro hk
    rcases lowE_or_uppE x k with ⟨k', rfl⟩ | ⟨k', rfl⟩
    · rw [pMat_upp_low] at hk
      by_cases hk' : k' = lastF x
      · exact Or.inl (by rw [hk'])
      · rw [if_neg hk'] at hk
        exact absurd hk zmod2_zero_ne_one
    · rw [pMat_upp_upp] at hk
      exact Or.inr ⟨k', mem_pSet.mpr hk, rfl⟩
  · intro hk
    rcases hk with hk | ⟨k', hk', rfl⟩
    · rw [hk, pMat_upp_low, if_pos rfl]
    · rw [pMat_upp_upp]
      exact mem_pSet.mp hk'

theorem uSet_lowE (x : ℕ) (j : Fin (2 ^ x)) :
    uSet (x + 1) (lowE x j)
      = insert (uppE x (lastF x)) ((uSet x j).image (lowE x)) := by
  ext k
  rw [mem_uSet, Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro ⟨h1, h2⟩
    rcases lowE_or_uppE x k with ⟨k', rfl⟩ | ⟨k', rfl⟩
    · rw [bkMat_low_low] at h1
      rw [lowE_val, lowE_val] at h2
      exact Or.inr ⟨k', mem_uSet.mpr ⟨h1, h2⟩, rfl⟩
    · rw [bkMat_upp_low] at h1
      by_cases hk' : k' = lastF x
      · exact Or.inl (by rw [hk'])
      · rw [if_neg hk'] at h1
        exact absurd h1 zmod2_zero_ne_one
  · intro hk
    rcases hk with hk | ⟨k', hk', rfl⟩
    · subst hk
      refine ⟨by rw [bkMat_upp_low, if_pos rfl], ?_⟩
      rw [lowE_val, uppE_val, lastF_val]
      have := j.isLt
      omega
    · obtain ⟨h1, h2⟩ := mem_uSet.mp hk'
      refine ⟨by rwa [bkMat_low_low], ?_⟩
      rwa [lowE_val, lowE_val]

theorem uSet_uppE (x : ℕ) (j : Fin (2 ^ x)) :
    uSet (x + 1) (uppE x j) = (uSet x j).image (uppE x) := by
  ext k
  rw [mem_uSet, Finset.mem_image]
  constructor
  · rintro ⟨h1, h2⟩
    rcases lowE_or_uppE x k with ⟨k', rfl⟩ | ⟨k', rfl⟩
    · rw [bkMat_low_upp] at h1
      exact absurd h1 zmod2_zero_ne_one
    · rw [bkMat_upp_upp] at h1
      rw [uppE_val, uppE_val] at h2
      exact ⟨k', mem_uSet.mpr ⟨h1, by omega⟩, rfl⟩
  · rintro ⟨k', hk', rfl⟩
    obtain ⟨h1, h2⟩ := mem_uSet.mp hk'
    refine ⟨by rwa [bkMat_upp_upp], ?_⟩
    rw [uppE_val, uppE_val]
    omega

theorem fSet_lowE (x : ℕ) (i : Fin (2 ^ x)) :
    fSet (x + 1) (lowE x i) = (fSet x i).image (lowE x) := by
  ext k
  rw [mem_fSet, Finset.mem_image]
  constructor
  · rintro ⟨h1, h2⟩
    rcases lowE_or_uppE x k with ⟨k', rfl⟩ | ⟨k', rfl⟩
    · rw [bkInv_low_low] at h1
      rw [lowE_val, lowE_val] at h2
      exact ⟨k', mem_fSet.mpr ⟨h1, h2⟩, rfl⟩
    · rw [bkInv_low_upp] at h1
      exact absurd h1 zmod2_zero_ne_one
  · rintro ⟨k', hk', rfl⟩
    obtain ⟨h1, h2⟩ := mem_fSet.mp hk'
    refine ⟨by rwa [bkInv_low_low], ?_⟩
    rwa [lowE_val, lowE_val]

theorem fSet_uppE (x : ℕ) (i : Fin (2 ^ x)) (hi : i ≠ lastF x) :
    fSet (x + 1) (uppE x i) = (fSet x i).image (uppE x) := by
  ext k
  rw [mem_fSet, Finset.mem_image]
  constructor
  · rintro ⟨h1, h2⟩
    rcases lowE_or_uppE x k with ⟨k', rfl⟩ | ⟨k', rfl⟩
    · rw [bkInv_upp_low, if_neg (fun hc => hi hc.1)] at h1
      exact absurd h1 zmod2_zero_ne_one
    · rw [bkInv_upp_upp] at h1
      rw [uppE_val, uppE_val] at h2
      exact ⟨k', mem_fSet.mpr ⟨h1, by omega⟩, rfl⟩
  · rintro ⟨k', hk', rfl⟩
    obtain ⟨h1, h2⟩ := mem_fSet.mp hk'
    refine ⟨by rwa [bkInv_upp_upp], ?_⟩
    rw [uppE_val, uppE_val]
    omega

theorem fSet_uppE_lastF (x : ℕ) :
    fSet (x + 1) (uppE x (lastF x))
      = insert (lowE x (lastF x)) ((fSet x (lastF x)).image (uppE x)) := by
  ext k
  rw [mem_fSet, Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro ⟨h1, h2⟩
    rcases lowE_or_uppE x k with ⟨k', rfl⟩ | ⟨k', rfl⟩
    · rw [bkInv_upp_low] at h1
      by_cases hk' : k' = lastF x
      · exact Or.inl (by rw [hk'])
      · rw [if_neg (fun hc => hk' hc.2)] at h1
        exact absurd h1 zmod2_zero_ne_one
    · rw [bkInv_upp_upp] at h1
      rw [uppE_val, uppE_val] at h2
      exact Or.inr ⟨k', mem_fSet.mpr ⟨h1, by omega⟩, rfl⟩
  · intro hk
    rcases hk with hk | ⟨k', hk', rfl⟩
    · subst hk
      refine ⟨by rw [bkInv_upp_low, if_pos ⟨rfl, rfl⟩], ?_⟩
      rw [lowE_val, uppE_val, lastF_val]
      have := two_pow_pos x
      omega
    · obtain ⟨h1, h2⟩ := mem_fSet.mp hk'
      refine ⟨by rwa [bkInv_upp_upp], ?_⟩
      rw [uppE_val, uppE_val]
      omega

/-! ## §5. Even/odd structure of the flip set -/

/-- `2^x` is even for `x ≥ 1`. -/
theorem even_two_pow {x : ℕ} (hx : 0 < x) : Even ((2 : ℕ) ^ x) :=
  (Nat.even_pow).mpr ⟨even_two, by omega⟩

/-- The last index `2^x - 1` is odd for `x ≥ 1`. -/
theorem not_even_lastF {x : ℕ} (hx : 0 < x) : ¬ Even ((lastF x : ℕ)) := by
  rw [lastF_val]
  obtain ⟨d, hd⟩ := even_two_pow hx
  rintro ⟨c, hc⟩
  have := two_pow_pos x
  omega

/-- **The flip set of an even index is empty** (arXiv:1208.5986 §IV.C: even
qubits store only their own orbital). -/
theorem fSet_of_even : ∀ x (j : Fin (2 ^ x)), Even (j : ℕ) → fSet x j = ∅
  | 0, j, _ => fSet_zero j
  | x + 1, m, hm => by
      rcases lowE_or_uppE x m with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · rw [lowE_val] at hm
        rw [fSet_lowE, fSet_of_even x i hm, Finset.image_empty]
      · rw [uppE_val] at hm
        rcases Nat.eq_zero_or_pos x with hx | hx
        · exfalso
          subst hx
          have hi : (i : ℕ) = 0 := by have := i.isLt; omega
          rw [hi] at hm
          exact (Nat.not_even_iff.mpr rfl) hm
        · have hie : Even (i : ℕ) :=
            (Nat.even_add.mp hm).mp (even_two_pow hx)
          have hlast : i ≠ lastF x := fun hc =>
            not_even_lastF hx (hc ▸ hie)
          rw [fSet_uppE x i hlast, fSet_of_even x i hie, Finset.image_empty]

/-- **The flip set of an odd index is contained in its parity set**
(arXiv:1208.5986: for odd `j`, `P(j) \ ρ(j) = F(j)`). -/
theorem fSet_subset_pSet_of_odd :
    ∀ x (j : Fin (2 ^ x)), ¬ Even (j : ℕ) → fSet x j ⊆ pSet x j
  | 0, j, hj => by
      exfalso
      have : (j : ℕ) = 0 := by have := j.isLt; omega
      rw [this] at hj
      exact hj ⟨0, rfl⟩
  | x + 1, m, hm => by
      rcases lowE_or_uppE x m with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · rw [lowE_val] at hm
        rw [fSet_lowE, pSet_lowE]
        exact Finset.image_subset_image (fSet_subset_pSet_of_odd x i hm)
      · rw [uppE_val] at hm
        by_cases hlast : i = lastF x
        · subst hlast
          rw [fSet_uppE_lastF, pSet_uppE]
          refine Finset.insert_subset_insert _ (Finset.image_subset_image ?_)
          rcases Nat.eq_zero_or_pos x with hx | hx
          · subst hx
            rw [fSet_zero]
            exact Finset.empty_subset _
          · exact fSet_subset_pSet_of_odd x (lastF x) (not_even_lastF hx)
        · rw [fSet_uppE x i hlast, pSet_uppE]
          have hsub : fSet x i ⊆ pSet x i := by
            refine fSet_subset_pSet_of_odd x i ?_
            rcases Nat.eq_zero_or_pos x with hx | hx
            · exfalso
              refine hlast (Fin.ext ?_)
              subst hx
              have := i.isLt
              rw [lastF_val]
              omega
            · intro hc
              obtain ⟨d, hd⟩ := even_two_pow hx
              obtain ⟨c, hcc⟩ := hc
              exact hm ⟨d + c, by omega⟩
          exact Finset.Subset.trans (Finset.image_subset_image hsub)
            (Finset.subset_insert _ _)

/-! ## §6. The `O(log n)` support bounds -/

/-- `|P(j)| ≤ x = log₂ n`: at most one qubit joins the parity set per
doubling. -/
theorem card_pSet_le : ∀ x (j : Fin (2 ^ x)), (pSet x j).card ≤ x
  | 0, j => by rw [pSet_zero]; exact Nat.le_refl 0
  | x + 1, m => by
      rcases lowE_or_uppE x m with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · rw [pSet_lowE, Finset.card_image_of_injective _ (lowE_injective x)]
        exact (card_pSet_le x i).trans (Nat.le_succ x)
      · rw [pSet_uppE]
        refine (Finset.card_insert_le _ _).trans ?_
        rw [Finset.card_image_of_injective _ (uppE_injective x)]
        exact Nat.succ_le_succ (card_pSet_le x i)

/-- `|U(j)| ≤ x = log₂ n`: at most one qubit joins the update set per
doubling. -/
theorem card_uSet_le : ∀ x (j : Fin (2 ^ x)), (uSet x j).card ≤ x
  | 0, j => by rw [uSet_zero]; exact Nat.le_refl 0
  | x + 1, m => by
      rcases lowE_or_uppE x m with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · rw [uSet_lowE]
        refine (Finset.card_insert_le _ _).trans ?_
        rw [Finset.card_image_of_injective _ (lowE_injective x)]
        exact Nat.succ_le_succ (card_uSet_le x j)
      · rw [uSet_uppE, Finset.card_image_of_injective _ (uppE_injective x)]
        exact (card_uSet_le x j).trans (Nat.le_succ x)

/-- `|F(j)| ≤ x = log₂ n`: at most one qubit joins the flip set per
doubling. -/
theorem card_fSet_le : ∀ x (j : Fin (2 ^ x)), (fSet x j).card ≤ x
  | 0, j => by rw [fSet_zero]; exact Nat.le_refl 0
  | x + 1, m => by
      rcases lowE_or_uppE x m with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · rw [fSet_lowE, Finset.card_image_of_injective _ (lowE_injective x)]
        exact (card_fSet_le x i).trans (Nat.le_succ x)
      · by_cases hlast : i = lastF x
        · subst hlast
          rw [fSet_uppE_lastF]
          refine (Finset.card_insert_le _ _).trans ?_
          rw [Finset.card_image_of_injective _ (uppE_injective x)]
          exact Nat.succ_le_succ (card_fSet_le x (lastF x))
        · rw [fSet_uppE x i hlast,
            Finset.card_image_of_injective _ (uppE_injective x)]
          exact (card_fSet_le x i).trans (Nat.le_succ x)

/-- `|ρ(j)| ≤ x` (a subset of the parity set). -/
theorem card_rhoSet_le (x : ℕ) (j : Fin (2 ^ x)) : (rhoSet x j).card ≤ x :=
  (Finset.card_le_card (rhoSet_subset_pSet x j)).trans (card_pSet_le x j)

/-! ## §7. Semantic content: the three parity lemmas -/

/-- Every element of `ZMod 2` is `0` or `1`. -/
theorem zmod2_dichotomy (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

/-- A `0/1`-weighted sum is the sum over the weight's support. -/
theorem sum_filter_entry_eq {n : ℕ} (A v : Fin n → ZMod 2) :
    ∑ k ∈ univ.filter (fun k => A k = 1), v k = ∑ k, A k * v k := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  rcases zmod2_dichotomy (A k) with h | h <;> rw [h]
  · rw [if_neg zmod2_zero_ne_one, zero_mul]
  · rw [if_pos rfl, one_mul]

/-- `mulVec` unfolded to a sum of entry products. -/
theorem mulVec_apply_sum {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (v : Fin n → ZMod 2) (i : Fin n) :
    M.mulVec v i = ∑ m, M i m * v m := by
  rw [Matrix.mulVec_eq_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Pi.smul_apply, Matrix.transpose_apply]
  simp [MulOpposite.smul_eq_mul_unop, mul_comm]

/-- **The parity-set lemma** (arXiv:1208.5986 §IV.A): the parity of the
Bravyi–Kitaev bits on `P(j)` is the parity of the occupation bits strictly
below `j`. -/
theorem pSet_parityZ (x : ℕ) (j : Fin (2 ^ x)) (f : Fin (2 ^ x) → Bool) :
    ∑ k ∈ pSet x j, bkVecZ x f k
      = ∑ k ∈ univ.filter (fun k : Fin (2 ^ x) => (k : ℕ) < (j : ℕ)),
          bitZ (f k) := by
  have h2 : (pMat x).mulVec (bkVecZ x f) j
      = (piMat x).mulVec (fun k => bitZ (f k)) j := by
    rw [bkVecZ, Matrix.mulVec_mulVec, pMat, mul_assoc, bkMat_inv_mul, mul_one]
  rw [pSet, sum_filter_entry_eq, ← mulVec_apply_sum, h2, mulVec_apply_sum,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [piMat, Matrix.of_apply]
  by_cases hk : (k : ℕ) < (j : ℕ)
  · rw [if_pos hk, if_pos hk, one_mul]
  · rw [if_neg hk, if_neg hk, zero_mul]

/-- **The flip-set lemma** (arXiv:1208.5986 §IV.C): the Bravyi–Kitaev bit at
`j` plus the parity of the Bravyi–Kitaev bits on `F(j)` is the occupation bit
at `j`. -/
theorem fSet_parityZ (x : ℕ) (j : Fin (2 ^ x)) (f : Fin (2 ^ x) → Bool) :
    bkVecZ x f j + ∑ k ∈ fSet x j, bkVecZ x f k = bitZ (f j) := by
  have h0 : (fun k => bitZ (f k)) = (bkMat x)⁻¹.mulVec (bkVecZ x f) := by
    rw [bkVecZ, Matrix.mulVec_mulVec, bkMat_inv_mul, Matrix.one_mulVec]
  have h1 : bitZ (f j) = ∑ k, (bkMat x)⁻¹ j k * bkVecZ x f k := by
    rw [show bitZ (f j) = (fun k => bitZ (f k)) j from rfl, h0,
      mulVec_apply_sum]
  rw [h1, ← Finset.add_sum_erase Finset.univ
    (fun k => (bkMat x)⁻¹ j k * bkVecZ x f k) (Finset.mem_univ j),
    bkInv_diag, one_mul]
  congr 1
  rw [fSet, Finset.sum_filter,
    ← Finset.add_sum_erase Finset.univ
      (fun k => if (bkMat x)⁻¹ j k = 1 ∧ (k : ℕ) < (j : ℕ) then bkVecZ x f k else 0)
      (Finset.mem_univ j),
    if_neg (fun hc => lt_irrefl _ hc.2), zero_add]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkj : k ≠ j := Finset.ne_of_mem_erase hk
  rcases Nat.lt_trichotomy (k : ℕ) (j : ℕ) with h | h | h
  · rcases zmod2_dichotomy ((bkMat x)⁻¹ j k) with h2 | h2
    · rw [if_neg (fun hc => zmod2_zero_ne_one (h2.symm.trans hc.1)), h2,
        zero_mul]
    · rw [if_pos ⟨h2, h⟩, h2, one_mul]
  · exact absurd (Fin.ext h) hkj
  · rw [bkInv_eq_zero_of_lt x j k h, zero_mul,
      if_neg (fun hc => zmod2_zero_ne_one hc.1)]

/-- Flipping occupation bit `j` adds column `j` of `β` to the mod-2
transform. -/
theorem bkVecZ_update (x : ℕ) (j : Fin (2 ^ x)) (f : Fin (2 ^ x) → Bool)
    (k : Fin (2 ^ x)) :
    bkVecZ x (Function.update f j (!(f j))) k = bkVecZ x f k + bkMat x k j := by
  have h1 : (fun m => bitZ (Function.update f j (!(f j)) m))
      = (fun m => bitZ (f m)) + fun m => if m = j then 1 else 0 := by
    funext m
    rw [Pi.add_apply]
    by_cases hm : m = j
    · subst hm
      rw [Function.update_self, if_pos rfl]
      cases f m <;> decide
    · rw [Function.update_of_ne hm, if_neg hm, add_zero]
  have h2 : (bkMat x).mulVec (fun m => if m = j then 1 else 0) k
      = bkMat x k j := by
    rw [mulVec_apply_sum,
      Finset.sum_congr rfl (g := fun m => if m = j then bkMat x k m else 0)
        (fun m _ => by
          by_cases hm : m = j
          · rw [if_pos hm, if_pos hm, mul_one]
          · rw [if_neg hm, if_neg hm, mul_zero]),
      Finset.sum_ite_eq' Finset.univ j fun m => bkMat x k m,
      if_pos (Finset.mem_univ j)]
  rw [bkVecZ, bkVecZ, h1, Matrix.mulVec_add, Pi.add_apply, h2]

/-- The column of `β` at `j` is supported exactly on `{j} ∪ U(j)`. -/
theorem bkMat_col_eq_one_iff (x : ℕ) (j k : Fin (2 ^ x)) :
    bkMat x k j = 1 ↔ k ∈ insert j (uSet x j) := by
  rw [Finset.mem_insert]
  constructor
  · intro h
    rcases Nat.lt_trichotomy (k : ℕ) (j : ℕ) with hk | hk | hk
    · rw [bkMat_eq_zero_of_lt x k j hk] at h
      exact absurd h zmod2_zero_ne_one
    · exact Or.inl (Fin.ext hk)
    · exact Or.inr (mem_uSet.mpr ⟨h, hk⟩)
  · intro h
    rcases h with h | h
    · rw [h, bkMat_diag]
    · exact (mem_uSet.mp h).1

/-- **The update-set lemma** (arXiv:1208.5986 §IV.B): flipping occupation bit
`j` flips exactly the Bravyi–Kitaev bits on `{j} ∪ U(j)`. -/
theorem bkVec_flip (x : ℕ) (j : Fin (2 ^ x)) (f : Fin (2 ^ x) → Bool)
    (k : Fin (2 ^ x)) :
    bkVec x (Function.update f j (!(f j))) k
      = xor (decide (k ∈ insert j (uSet x j))) (bkVec x f k) := by
  rw [bkVec, bkVec, bkVecZ_update, decide_add_eq_one, Bool.xor_comm]
  congr 1
  exact decide_eq_decide.mpr (bkMat_col_eq_one_iff x j k)

/-- **The combined sign rule** behind the Bravyi–Kitaev ladder operators: the
Bravyi–Kitaev bit at `j` plus the parities on `ρ(j)` and on `P(j)` is the
occupation bit at `j` — for even `j` because `ρ(j) = P(j)` and `F(j) = ∅`,
for odd `j` because `P(j) \ ρ(j) = F(j)`. -/
theorem rho_parity (x : ℕ) (j : Fin (2 ^ x)) (f : Fin (2 ^ x) → Bool) :
    bkVecZ x f j + ∑ k ∈ rhoSet x j, bkVecZ x f k
        + ∑ k ∈ pSet x j, bkVecZ x f k
      = bitZ (f j) := by
  by_cases hj : Even (j : ℕ)
  · rw [rhoSet, if_pos hj, add_assoc, zmod2_add_self, add_zero]
    have h2 := fSet_parityZ x j f
    rw [fSet_of_even x j hj, Finset.sum_empty, add_zero] at h2
    exact h2
  · rw [rhoSet, if_neg hj]
    have h1 : ∑ k ∈ pSet x j \ fSet x j, bkVecZ x f k
          + ∑ k ∈ fSet x j, bkVecZ x f k
        = ∑ k ∈ pSet x j, bkVecZ x f k :=
      Finset.sum_sdiff (fSet_subset_pSet_of_odd x j hj)
    rw [← h1]
    have h3 : ∀ a b c : ZMod 2, a + b + (b + c) = a + c := by decide
    rw [h3, fSet_parityZ]

/-! ## §8. The transform is a bijection on bit vectors -/

/-- `bitZ` reads back `decide (· = 1)`. -/
theorem bitZ_decide (a : ZMod 2) : bitZ (decide (a = 1)) = a := by
  revert a; decide

/-- `bitZ` of a Bravyi–Kitaev bit is the mod-2 transform value. -/
theorem bitZ_bkVec (x : ℕ) (f : Fin (2 ^ x) → Bool) (k : Fin (2 ^ x)) :
    bitZ (bkVec x f k) = bkVecZ x f k := bitZ_decide _

/-- The inverse transform on bit vectors, via `β⁻¹`. -/
noncomputable def bkInvVec (x : ℕ) (g : Fin (2 ^ x) → Bool) : Fin (2 ^ x) → Bool :=
  fun i => decide ((bkMat x)⁻¹.mulVec (fun j => bitZ (g j)) i = 1)

theorem bkVec_bkInvVec (x : ℕ) (g : Fin (2 ^ x) → Bool) :
    bkVec x (bkInvVec x g) = g := by
  funext i
  have h1 : (fun j => bitZ (bkInvVec x g j))
      = (bkMat x)⁻¹.mulVec (fun j => bitZ (g j)) := by
    funext j
    rw [bkInvVec, bitZ_decide]
  rw [bkVec, bkVecZ, h1, Matrix.mulVec_mulVec, bkMat_mul_inv,
    Matrix.one_mulVec, decide_bitZ_eq]

theorem bkInvVec_bkVec (x : ℕ) (f : Fin (2 ^ x) → Bool) :
    bkInvVec x (bkVec x f) = f := by
  funext i
  have h1 : (fun j => bitZ (bkVec x f j)) = bkVecZ x f := by
    funext j
    rw [bitZ_bkVec]
  rw [bkInvVec, h1, bkVecZ, Matrix.mulVec_mulVec, bkMat_inv_mul,
    Matrix.one_mulVec, decide_bitZ_eq]

/-- **The Bravyi–Kitaev transform is a bijection on bit vectors** (`β` is
invertible). -/
noncomputable def bkEquiv (x : ℕ) : (Fin (2 ^ x) → Bool) ≃ (Fin (2 ^ x) → Bool) where
  toFun := bkVec x
  invFun := bkInvVec x
  left_inv := bkInvVec_bkVec x
  right_inv := bkVec_bkInvVec x

end Qhl.BravyiKitaev
