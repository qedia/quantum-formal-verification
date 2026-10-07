import Qhl.Register.PauliString
import Qhl.Register.BKSets

/-!
# The Bravyi–Kitaev fermionic ladder operators and their CAR

The Seeley–Richard–Love form of the Bravyi–Kitaev-encoded annihilation and
creation operators (arXiv:1208.5986 eqs. (30)–(31)), on the `2^x`-qubit world:

* `annOp x j = ½ (X_{U(j)} X_j Z_{P(j)} + i · X_{U(j)} Y_j Z_{ρ(j)})`
  (the SRL `a_j`) and `creOp x j` with the opposite sign (the SRL `a†_j`),
  each a linear combination of two `pauliString`s built from the index sets of
  `Qhl/Register/BKSets.lean`.

**Convention.** `Y∣b⟩ = i(-1)^b ∣¬b⟩` (`Qhl/Gate/PauliAlgebra.lean`), so at
`x = 0` (one qubit, all index sets empty) `annOp = (X + iY)/2 = ∣0⟩⟨1∣`:
`annOp` annihilates and `creOp = ∣1⟩⟨0∣` creates, matching SRL's
Jordan–Wigner consistency check `a_0 = Q⁻`.

The proof route is conjugation transport from the Jordan–Wigner action: the
encoded basis ket `bkKet x f` is the computational ket at the *Bravyi–Kitaev
transform* of the occupation vector `f`, and the master action lemmas

* `annOp_bkKet : annOp x j (bkKet x f)
    = if f j then signBelow x j f • bkKet x (f[j := false]) else 0`
* `creOp_bkKet : creOp x j (bkKet x f)
    = if f j then 0 else signBelow x j f • bkKet x (f[j := true])`

show the SRL Pauli strings act on the encoded basis exactly as the abstract
fermionic ladder operators act on occupation vectors, with the Jordan–Wigner
sign `signBelow x j f = (-1)^{#occupied below j}`.  The three parity lemmas of
`BKSets` (`pSet_parityZ`, `rho_parity`, `bkVec_flip`) are precisely what makes
the phases and bit flips come out right.  Since `bkVec` is a bijection
(`bkEquiv`), the encoded kets exhaust the basis, and the **canonical
anticommutation relations** follow by two-line occupation-vector
combinatorics:

* `bk_car_ann  : a_j a_k + a_k a_j = 0`
* `bk_car_cre  : a†_j a†_k + a†_k a†_j = 0`
* `bk_car_mixed: a_j a†_k + a†_k a_j = δ_{jk} · 1`

together with `creOp_eq_adjoint : a†_j = (a_j)†`.  Finally the **number
operator** `numOp x j = a†_j a_j` is the SRL `Z`-string formula
`numOp_eq_zString : n_j = ½ (1 − Z_{F(j) ∪ {j}})` (arXiv:1208.5986 eq. (39)),
ready for Hubbard-type Hamiltonians.
-/

namespace Qhl.BravyiKitaev

open Finset
open scoped ComplexInnerProductSpace

/-! ## §1. Signs: `ZMod 2` parities as `±1` scalars -/

/-- The sign `(-1)^a` of a mod-2 parity. -/
noncomputable def signZ (a : ZMod 2) : ℂ := if a = 1 then -1 else 1

theorem signZ_zero : signZ 0 = 1 := if_neg zmod2_zero_ne_one

theorem signZ_one : signZ 1 = -1 := if_pos rfl

theorem signZ_add (a b : ZMod 2) : signZ (a + b) = signZ a * signZ b := by
  rcases zmod2_dichotomy a with ha | ha <;> rcases zmod2_dichotomy b with hb | hb <;>
    rw [ha, hb] <;> simp +decide [signZ]

/-- A product of per-bit signs is the sign of the mod-2 parity. -/
theorem prod_bsign_eq_signZ {α : Type*} [DecidableEq α] (S : Finset α)
    (g : α → Bool) :
    (∏ k ∈ S, if g k then (-1 : ℂ) else 1) = signZ (∑ k ∈ S, bitZ (g k)) := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, signZ_zero]
  | insert a S ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, signZ_add]
      congr 1
      cases g a <;> simp +decide [signZ, bitZ]

/-! ## §2. The SRL letter assignments -/

variable (x : ℕ)

/-- The letters of the `X`-type SRL string: `X` on `U(j) ∪ {j}`, `Z` on
`P(j)`, identity elsewhere. -/
noncomputable def xStr (j : Fin (2 ^ x)) : Fin (2 ^ x) → PLetter := fun k =>
  if k ∈ insert j (uSet x j) then PLetter.x
  else if k ∈ pSet x j then PLetter.z
  else PLetter.one

/-- The letters of the `Y`-type SRL string: `Y` at `j`, `X` on `U(j)`, `Z` on
`ρ(j)`, identity elsewhere. -/
noncomputable def yStr (j : Fin (2 ^ x)) : Fin (2 ^ x) → PLetter := fun k =>
  if k = j then PLetter.y
  else if k ∈ uSet x j then PLetter.x
  else if k ∈ rhoSet x j then PLetter.z
  else PLetter.one

/-- Both strings flip exactly the bits on `{j} ∪ U(j)`. -/
theorem xStr_flips (j k : Fin (2 ^ x)) :
    (xStr x j k).flips = decide (k ∈ insert j (uSet x j)) := by
  simp only [xStr]
  by_cases h1 : k ∈ insert j (uSet x j)
  · simp [h1, PLetter.flips]
  · by_cases h2 : k ∈ pSet x j <;> simp [h1, h2, PLetter.flips]

/-- Both strings flip exactly the bits on `{j} ∪ U(j)`. -/
theorem yStr_flips (j k : Fin (2 ^ x)) :
    (yStr x j k).flips = decide (k ∈ insert j (uSet x j)) := by
  simp only [yStr]
  by_cases h1 : k = j
  · subst h1
    simp [PLetter.flips]
  · by_cases h2 : k ∈ uSet x j
    · simp [h1, h2, PLetter.flips]
    · by_cases h3 : k ∈ rhoSet x j <;>
        simp [h1, h2, h3, PLetter.flips]

/-- The phase of the `X`-type string on a basis ket: the parity sign of the
bits on `P(j)`. -/
theorem xStr_phase (j : Fin (2 ^ x)) (g : Fin (2 ^ x) → Bool) :
    (∏ k, (xStr x j k).ph (g k)) = signZ (∑ k ∈ pSet x j, bitZ (g k)) := by
  rw [← prod_bsign_eq_signZ]
  have h1 : ∀ k, (xStr x j k).ph (g k)
      = if k ∈ pSet x j then (if g k then (-1 : ℂ) else 1) else 1 := fun k => by
    simp only [xStr]
    by_cases hu : k ∈ insert j (uSet x j)
    · rw [if_pos hu]
      have hp : k ∉ pSet x j := by
        intro hc
        have hlt := lt_of_mem_pSet hc
        rcases Finset.mem_insert.mp hu with h | h
        · subst h
          exact absurd hlt (lt_irrefl _)
        · have := lt_of_mem_uSet h
          omega
      rw [if_neg hp]
      rfl
    · rw [if_neg hu]
      by_cases hp : k ∈ pSet x j
      · rw [if_pos hp, if_pos hp]
        rfl
      · rw [if_neg hp, if_neg hp]
        rfl
  rw [Finset.prod_congr rfl fun k _ => h1 k, Finset.prod_ite_mem,
    Finset.univ_inter]

/-- The phase of the `Y`-type string on a basis ket: `i(-1)^{g j}` from the
`Y` site times the parity sign of the bits on `ρ(j)`. -/
theorem yStr_phase (j : Fin (2 ^ x)) (g : Fin (2 ^ x) → Bool) :
    (∏ k, (yStr x j k).ph (g k))
      = (if g j then -Complex.I else Complex.I)
          * signZ (∑ k ∈ rhoSet x j, bitZ (g k)) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
  have hj : (yStr x j j).ph (g j) = if g j then -Complex.I else Complex.I := by
    simp only [yStr, if_pos rfl]
    rfl
  rw [hj]
  congr 1
  rw [← prod_bsign_eq_signZ]
  have h1 : ∀ k ∈ Finset.univ.erase j, (yStr x j k).ph (g k)
      = if k ∈ rhoSet x j then (if g k then (-1 : ℂ) else 1) else 1 := fun k hk => by
    have hkj : k ≠ j := Finset.ne_of_mem_erase hk
    simp only [yStr, if_neg hkj]
    by_cases hu : k ∈ uSet x j
    · rw [if_pos hu]
      have hr : k ∉ rhoSet x j := by
        intro hc
        have h2 := lt_of_mem_pSet (rhoSet_subset_pSet x j hc)
        have h3 := lt_of_mem_uSet hu
        omega
      rw [if_neg hr]
      rfl
    · rw [if_neg hu]
      by_cases hr : k ∈ rhoSet x j
      · rw [if_pos hr, if_pos hr]
        rfl
      · rw [if_neg hr, if_neg hr]
        rfl
  rw [Finset.prod_congr rfl h1, Finset.prod_ite_mem]
  have h2 : Finset.univ.erase j ∩ rhoSet x j = rhoSet x j := by
    refine Finset.inter_eq_right.mpr fun k hk => ?_
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ k⟩
    intro hc
    subst hc
    exact absurd (lt_of_mem_pSet (rhoSet_subset_pSet x k hk)) (lt_irrefl _)
  rw [h2]

/-! ## §3. The ladder operators and the encoded basis -/

/-- **The SRL annihilation operator** `a_j` (arXiv:1208.5986 eq. (31)):
`½ (X_{U(j)} X_j Z_{P(j)} + i · X_{U(j)} Y_j Z_{ρ(j)})`. -/
noncomputable def annOp (j : Fin (2 ^ x)) :
    EndM (QubitCells (Fin (2 ^ x))) (univ : Finset (Fin (2 ^ x))) :=
  (2 : ℂ)⁻¹ • (pauliString (xStr x j) + Complex.I • pauliString (yStr x j))

/-- **The SRL creation operator** `a†_j` (arXiv:1208.5986 eq. (30)):
`½ (X_{U(j)} X_j Z_{P(j)} − i · X_{U(j)} Y_j Z_{ρ(j)})`. -/
noncomputable def creOp (j : Fin (2 ^ x)) :
    EndM (QubitCells (Fin (2 ^ x))) (univ : Finset (Fin (2 ^ x))) :=
  (2 : ℂ)⁻¹ • (pauliString (xStr x j) - Complex.I • pauliString (yStr x j))

/-- The Bravyi–Kitaev **encoded basis ket** of an occupation vector `f`: the
computational ket at the transform `β f`. -/
noncomputable def bkKet (f : Fin (2 ^ x) → Bool) :
    HS (QubitCells (Fin (2 ^ x))) (univ : Finset (Fin (2 ^ x))) :=
  deltav (QubitCells (Fin (2 ^ x))) (qbIdx (Fin (2 ^ x)) (bkVec x f))

/-- The Jordan–Wigner sign: `(-1)^{#occupied orbitals below j}`. -/
noncomputable def signBelow (j : Fin (2 ^ x)) (f : Fin (2 ^ x) → Bool) : ℂ :=
  ∏ k ∈ univ.filter (fun k : Fin (2 ^ x) => (k : ℕ) < (j : ℕ)),
    if f k then -1 else 1

theorem signBelow_mul_self (j : Fin (2 ^ x)) (f : Fin (2 ^ x) → Bool) :
    signBelow x j f * signBelow x j f = 1 := by
  rw [signBelow, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun m _ => by cases f m <;> norm_num

/-- The sign is untouched by updates at or above `j`. -/
theorem signBelow_update_of_le (j k : Fin (2 ^ x)) (hjk : (j : ℕ) ≤ (k : ℕ))
    (f : Fin (2 ^ x) → Bool) (b : Bool) :
    signBelow x j (Function.update f k b) = signBelow x j f := by
  rw [signBelow, signBelow]
  refine Finset.prod_congr rfl fun m hm => ?_
  have hmj : (m : ℕ) < (j : ℕ) := (Finset.mem_filter.mp hm).2
  rw [Function.update_of_ne (fun hc => by rw [hc] at hmj; omega)]

/-- The sign under an update strictly below `j`. -/
theorem signBelow_update_of_lt (j k : Fin (2 ^ x)) (hkj : (k : ℕ) < (j : ℕ))
    (f : Fin (2 ^ x) → Bool) (b : Bool) :
    signBelow x j (Function.update f k b)
      = (if b then (-1 : ℂ) else 1) * (if f k then (-1 : ℂ) else 1)
          * signBelow x j f := by
  rw [signBelow, signBelow]
  have hk : k ∈ univ.filter (fun m : Fin (2 ^ x) => (m : ℕ) < (j : ℕ)) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ k, hkj⟩
  rw [← Finset.mul_prod_erase _ _ hk, ← Finset.mul_prod_erase _ _ hk,
    Function.update_self,
    Finset.prod_congr rfl fun m hm => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hm)]]
  cases f k <;> cases b <;> simp <;> ring

/-! ## §4. The master action lemmas -/

/-- The scalar identity behind `annOp_bkKet`. -/
theorem ann_coeff (j : Fin (2 ^ x)) (f : Fin (2 ^ x) → Bool) :
    (2 : ℂ)⁻¹ * (signZ (∑ k ∈ pSet x j, bitZ (bkVec x f k))
        + Complex.I * ((if bkVec x f j then -Complex.I else Complex.I)
            * signZ (∑ k ∈ rhoSet x j, bitZ (bkVec x f k))))
      = if f j then signBelow x j f else 0 := by
  have hsb : (∑ k ∈ pSet x j, bitZ (bkVec x f k))
      = ∑ k ∈ pSet x j, bkVecZ x f k :=
    Finset.sum_congr rfl fun k _ => bitZ_bkVec x f k
  have hsr : (∑ k ∈ rhoSet x j, bitZ (bkVec x f k))
      = ∑ k ∈ rhoSet x j, bkVecZ x f k :=
    Finset.sum_congr rfl fun k _ => bitZ_bkVec x f k
  have hy : (if bkVec x f j then -Complex.I else Complex.I)
      = Complex.I * signZ (bkVecZ x f j) := by
    rw [← bitZ_bkVec x f j]
    cases bkVec x f j
    · rw [bitZ_false, signZ_zero]
      simp
    · rw [bitZ_true, signZ_one]
      simp
  have key : bkVecZ x f j + ∑ k ∈ rhoSet x j, bkVecZ x f k
      = bitZ (f j) + ∑ k ∈ pSet x j, bkVecZ x f k := by
    have h := rho_parity x j f
    have h4 : ∀ a b c d : ZMod 2, a + b + c = d → a + b = d + c := by decide
    exact h4 _ _ _ _ h
  have hsplit : signZ (bkVecZ x f j) * signZ (∑ k ∈ rhoSet x j, bkVecZ x f k)
      = signZ (bitZ (f j)) * signZ (∑ k ∈ pSet x j, bkVecZ x f k) := by
    rw [← signZ_add, ← signZ_add, key]
  have hbelow : signZ (∑ k ∈ pSet x j, bkVecZ x f k) = signBelow x j f := by
    rw [pSet_parityZ, signBelow, prod_bsign_eq_signZ]
  rw [hsb, hsr, hy]
  have hstep : (2 : ℂ)⁻¹ * (signZ (∑ k ∈ pSet x j, bkVecZ x f k)
        + Complex.I * (Complex.I * signZ (bkVecZ x f j)
            * signZ (∑ k ∈ rhoSet x j, bkVecZ x f k)))
      = (2 : ℂ)⁻¹ * (signZ (∑ k ∈ pSet x j, bkVecZ x f k)
        - signZ (bkVecZ x f j) * signZ (∑ k ∈ rhoSet x j, bkVecZ x f k)) := by
    rw [show Complex.I * (Complex.I * signZ (bkVecZ x f j)
        * signZ (∑ k ∈ rhoSet x j, bkVecZ x f k))
      = (Complex.I * Complex.I) * (signZ (bkVecZ x f j)
        * signZ (∑ k ∈ rhoSet x j, bkVecZ x f k)) from by ring,
      Complex.I_mul_I]
    ring
  rw [hstep, hsplit, hbelow]
  cases hfj : f j
  · rw [bitZ_false, signZ_zero]
    simp only [Bool.false_eq_true, if_false]
    ring
  · rw [bitZ_true, signZ_one, if_pos rfl]
    ring

/-- The scalar identity behind `creOp_bkKet`. -/
theorem cre_coeff (j : Fin (2 ^ x)) (f : Fin (2 ^ x) → Bool) :
    (2 : ℂ)⁻¹ * (signZ (∑ k ∈ pSet x j, bitZ (bkVec x f k))
        - Complex.I * ((if bkVec x f j then -Complex.I else Complex.I)
            * signZ (∑ k ∈ rhoSet x j, bitZ (bkVec x f k))))
      = if f j then 0 else signBelow x j f := by
  have hsb : (∑ k ∈ pSet x j, bitZ (bkVec x f k))
      = ∑ k ∈ pSet x j, bkVecZ x f k :=
    Finset.sum_congr rfl fun k _ => bitZ_bkVec x f k
  have hsr : (∑ k ∈ rhoSet x j, bitZ (bkVec x f k))
      = ∑ k ∈ rhoSet x j, bkVecZ x f k :=
    Finset.sum_congr rfl fun k _ => bitZ_bkVec x f k
  have hy : (if bkVec x f j then -Complex.I else Complex.I)
      = Complex.I * signZ (bkVecZ x f j) := by
    rw [← bitZ_bkVec x f j]
    cases bkVec x f j
    · rw [bitZ_false, signZ_zero]
      simp
    · rw [bitZ_true, signZ_one]
      simp
  have key : bkVecZ x f j + ∑ k ∈ rhoSet x j, bkVecZ x f k
      = bitZ (f j) + ∑ k ∈ pSet x j, bkVecZ x f k := by
    have h := rho_parity x j f
    have h4 : ∀ a b c d : ZMod 2, a + b + c = d → a + b = d + c := by decide
    exact h4 _ _ _ _ h
  have hsplit : signZ (bkVecZ x f j) * signZ (∑ k ∈ rhoSet x j, bkVecZ x f k)
      = signZ (bitZ (f j)) * signZ (∑ k ∈ pSet x j, bkVecZ x f k) := by
    rw [← signZ_add, ← signZ_add, key]
  have hbelow : signZ (∑ k ∈ pSet x j, bkVecZ x f k) = signBelow x j f := by
    rw [pSet_parityZ, signBelow, prod_bsign_eq_signZ]
  rw [hsb, hsr, hy]
  have hstep : (2 : ℂ)⁻¹ * (signZ (∑ k ∈ pSet x j, bkVecZ x f k)
        - Complex.I * (Complex.I * signZ (bkVecZ x f j)
            * signZ (∑ k ∈ rhoSet x j, bkVecZ x f k)))
      = (2 : ℂ)⁻¹ * (signZ (∑ k ∈ pSet x j, bkVecZ x f k)
        + signZ (bkVecZ x f j) * signZ (∑ k ∈ rhoSet x j, bkVecZ x f k)) := by
    rw [show Complex.I * (Complex.I * signZ (bkVecZ x f j)
        * signZ (∑ k ∈ rhoSet x j, bkVecZ x f k))
      = (Complex.I * Complex.I) * (signZ (bkVecZ x f j)
        * signZ (∑ k ∈ rhoSet x j, bkVecZ x f k)) from by ring,
      Complex.I_mul_I]
    ring
  rw [hstep, hsplit, hbelow]
  cases hfj : f j
  · rw [bitZ_false, signZ_zero]
    simp only [Bool.false_eq_true, if_false]
    ring
  · rw [bitZ_true, signZ_one, if_pos rfl]
    ring

/-- **The annihilation action** on the encoded basis: exactly the abstract
fermionic annihilation on occupation vectors, with the Jordan–Wigner sign. -/
theorem annOp_bkKet (j : Fin (2 ^ x)) (f : Fin (2 ^ x) → Bool) :
    annOp x j (bkKet x f)
      = if f j then signBelow x j f • bkKet x (Function.update f j false)
        else 0 := by
  have hketX : (fun k => xor ((xStr x j k)).flips (bkVec x f k))
      = bkVec x (Function.update f j (!(f j))) := by
    funext k
    rw [xStr_flips, ← bkVec_flip]
  have hketY : (fun k => xor ((yStr x j k)).flips (bkVec x f k))
      = bkVec x (Function.update f j (!(f j))) := by
    funext k
    rw [yStr_flips, ← bkVec_flip]
  rw [annOp, bkKet, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.smul_apply, pauliString_deltav, pauliString_deltav,
    hketX, hketY, xStr_phase, yStr_phase, smul_smul, ← add_smul, smul_smul]
  rw [ann_coeff]
  by_cases hfj : f j = true
  · rw [hfj, if_pos rfl, if_pos rfl]
    rfl
  · have hf : f j = false := (Bool.not_eq_true _).mp hfj
    rw [hf, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, zero_smul]

/-- **The creation action** on the encoded basis: exactly the abstract
fermionic creation on occupation vectors, with the Jordan–Wigner sign. -/
theorem creOp_bkKet (j : Fin (2 ^ x)) (f : Fin (2 ^ x) → Bool) :
    creOp x j (bkKet x f)
      = if f j then 0
        else signBelow x j f • bkKet x (Function.update f j true) := by
  have hketX : (fun k => xor ((xStr x j k)).flips (bkVec x f k))
      = bkVec x (Function.update f j (!(f j))) := by
    funext k
    rw [xStr_flips, ← bkVec_flip]
  have hketY : (fun k => xor ((yStr x j k)).flips (bkVec x f k))
      = bkVec x (Function.update f j (!(f j))) := by
    funext k
    rw [yStr_flips, ← bkVec_flip]
  rw [creOp, bkKet, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, pauliString_deltav, pauliString_deltav,
    hketX, hketY, xStr_phase, yStr_phase, smul_smul, ← sub_smul, smul_smul]
  rw [cre_coeff]
  by_cases hfj : f j = true
  · rw [hfj, if_pos rfl, if_pos rfl, zero_smul]
  · have hf : f j = false := (Bool.not_eq_true _).mp hfj
    rw [hf, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
    rfl

/-- An operator on the world is determined by its values on the encoded
basis (the transform is a bijection). -/
theorem bkEndM_ext {A B : EndM (QubitCells (Fin (2 ^ x))) (univ : Finset (Fin (2 ^ x)))}
    (h : ∀ f, A (bkKet x f) = B (bkKet x f)) : A = B := by
  refine qubitEndM_ext fun g => ?_
  have h2 := h (bkInvVec x g)
  rwa [bkKet, bkVec_bkInvVec] at h2

/-- Updating a bit strictly below `j` to the *opposite* value flips the
Jordan–Wigner sign. -/
theorem signBelow_update_flip (j k : Fin (2 ^ x)) (hkj : (k : ℕ) < (j : ℕ))
    (f : Fin (2 ^ x) → Bool) (b : Bool) (hb : f k = !b) :
    signBelow x j (Function.update f k b) = -signBelow x j f := by
  rw [signBelow_update_of_lt x j k hkj f b, hb]
  cases b <;> simp

/-! ## §5. The canonical anticommutation relations -/

/-- **CAR, annihilation–annihilation**: `a_j a_k + a_k a_j = 0`. -/
theorem bk_car_ann (j k : Fin (2 ^ x)) :
    annOp x j ∘ₗ annOp x k + annOp x k ∘ₗ annOp x j = 0 := by
  refine bkEndM_ext x fun f => ?_
  rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearMap.zero_apply, annOp_bkKet, annOp_bkKet]
  by_cases hjk : j = k
  · subst hjk
    by_cases hfj : f j
    · rw [if_pos hfj, map_smul, annOp_bkKet, Function.update_self]
      simp
    · rw [if_neg hfj, map_zero, zero_add]
  · by_cases hfj : f j <;> by_cases hfk : f k
    · -- both occupied: the two orders carry opposite signs
      rw [if_pos hfj, if_pos hfk, map_smul, map_smul, annOp_bkKet, annOp_bkKet,
        Function.update_of_ne hjk, Function.update_of_ne (Ne.symm hjk),
        if_pos hfj, if_pos hfk, smul_smul, smul_smul]
      have hket : Function.update (Function.update f k false) j false
          = Function.update (Function.update f j false) k false :=
        (Function.update_comm hjk false false f).symm
      rw [hket, ← add_smul]
      have hcoef : signBelow x k f * signBelow x j (Function.update f k false)
            + signBelow x j f * signBelow x k (Function.update f j false)
          = 0 := by
        rcases Nat.lt_trichotomy (j : ℕ) (k : ℕ) with h | h | h
        · rw [signBelow_update_of_le x j k (le_of_lt h),
            signBelow_update_flip x k j h f false hfj]
          ring
        · exact absurd (Fin.ext h) hjk
        · rw [signBelow_update_flip x j k h f false hfk,
            signBelow_update_of_le x k j (le_of_lt h)]
          ring
      rw [hcoef, zero_smul]
    · rw [if_pos hfj, if_neg hfk, map_zero, map_smul, annOp_bkKet,
        Function.update_of_ne (Ne.symm hjk), if_neg hfk, smul_zero, add_zero]
    · rw [if_neg hfj, if_pos hfk, map_zero, map_smul, annOp_bkKet,
        Function.update_of_ne hjk, if_neg hfj, smul_zero, zero_add]
    · rw [if_neg hfj, if_neg hfk, map_zero, map_zero, add_zero]

/-- **CAR, mixed**: `a_j a†_k + a†_k a_j = δ_{jk} · 1` — "fermions genuinely
simulated": the encoded modes satisfy the canonical anticommutation
relations. -/
theorem bk_car_mixed (j k : Fin (2 ^ x)) :
    annOp x j ∘ₗ creOp x k + creOp x k ∘ₗ annOp x j
      = if j = k
        then (1 : EndM (QubitCells (Fin (2 ^ x))) (univ : Finset (Fin (2 ^ x))))
        else 0 := by
  refine bkEndM_ext x fun f => ?_
  rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    creOp_bkKet, annOp_bkKet]
  by_cases hjk : j = k
  · subst hjk
    rw [if_pos rfl, Module.End.one_apply]
    by_cases hfj : f j
    · -- occupied: a† gives 0, a then a† restores the ket
      rw [if_pos hfj, if_pos hfj, map_zero, map_smul, creOp_bkKet,
        Function.update_self]
      have hs : signBelow x j (Function.update f j false) = signBelow x j f :=
        signBelow_update_of_le x j j (le_refl _) f false
      have hket : Function.update (Function.update f j false) j true = f := by
        rw [Function.update_idem, show true = f j from hfj.symm,
          Function.update_eq_self]
      simp only [Bool.false_eq_true, if_false, hs, hket, smul_smul,
        signBelow_mul_self, one_smul, zero_add]
    · -- empty: a gives 0, a† then a restores the ket
      rw [if_neg hfj, if_neg hfj, map_zero, map_smul, annOp_bkKet,
        Function.update_self]
      have hs : signBelow x j (Function.update f j true) = signBelow x j f :=
        signBelow_update_of_le x j j (le_refl _) f true
      have hket : Function.update (Function.update f j true) j false = f := by
        rw [Function.update_idem,
          show false = f j from ((Bool.not_eq_true _).mp hfj).symm,
          Function.update_eq_self]
      simp only [if_true, hs, hket, smul_smul, signBelow_mul_self, one_smul,
        add_zero]
  · rw [if_neg hjk, LinearMap.zero_apply]
    by_cases hfj : f j <;> by_cases hfk : f k
    · rw [if_pos hfj, if_pos hfk, map_zero, map_smul, creOp_bkKet,
        Function.update_of_ne (Ne.symm hjk), if_pos hfk, smul_zero, add_zero]
    · -- the crossing case: opposite signs cancel
      rw [if_pos hfj, if_neg hfk, map_smul, map_smul, annOp_bkKet, creOp_bkKet,
        Function.update_of_ne hjk, Function.update_of_ne (Ne.symm hjk),
        if_pos hfj, if_neg hfk, smul_smul, smul_smul]
      have hket : Function.update (Function.update f k true) j false
          = Function.update (Function.update f j false) k true :=
        (Function.update_comm hjk false true f).symm
      rw [hket, ← add_smul]
      have hcoef : signBelow x k f * signBelow x j (Function.update f k true)
            + signBelow x j f * signBelow x k (Function.update f j false)
          = 0 := by
        rcases Nat.lt_trichotomy (j : ℕ) (k : ℕ) with h | h | h
        · rw [signBelow_update_of_le x j k (le_of_lt h),
            signBelow_update_flip x k j h f false hfj]
          ring
        · exact absurd (Fin.ext h) hjk
        · rw [signBelow_update_flip x j k h f true ((Bool.not_eq_true _).mp hfk),
            signBelow_update_of_le x k j (le_of_lt h)]
          ring
      rw [hcoef, zero_smul]
    · rw [if_neg hfj, if_pos hfk, map_zero, map_zero, add_zero]
    · rw [if_neg hfj, if_neg hfk, map_zero, map_smul, annOp_bkKet,
        Function.update_of_ne hjk, if_neg hfj, smul_zero, zero_add]

/-! ## §6. Adjointness and the creation–creation CAR -/

/-- The creation operator is the adjoint of the annihilation operator (Pauli
strings are self-adjoint; conjugating the scalar `i` flips the sign). -/
theorem creOp_eq_adjoint (j : Fin (2 ^ x)) :
    creOp x j = LinearMap.adjoint (annOp x j) := by
  rw [← LinearMap.star_eq_adjoint, annOp, creOp, star_smul, star_add,
    star_smul, LinearMap.star_eq_adjoint, LinearMap.star_eq_adjoint,
    adjoint_pauliString, adjoint_pauliString,
    show star ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ from by norm_num,
    show star Complex.I = -Complex.I from by
      simp [Complex.star_def, Complex.conj_I],
    neg_smul, ← sub_eq_add_neg]

/-- **CAR, creation–creation**: `a†_j a†_k + a†_k a†_j = 0` (the adjoint of
the annihilation–annihilation relation). -/
theorem bk_car_cre (j k : Fin (2 ^ x)) :
    creOp x j ∘ₗ creOp x k + creOp x k ∘ₗ creOp x j = 0 := by
  rw [creOp_eq_adjoint, creOp_eq_adjoint, ← LinearMap.adjoint_comp,
    ← LinearMap.adjoint_comp, ← map_add, bk_car_ann, map_zero]

/-! ## §7. The number operator as a `Z`-string (SRL eq. (39)) -/

/-- The number operator `n_j = a†_j a_j`. -/
noncomputable def numOp (j : Fin (2 ^ x)) :
    EndM (QubitCells (Fin (2 ^ x))) (univ : Finset (Fin (2 ^ x))) :=
  creOp x j ∘ₗ annOp x j

/-- The number operator reads the occupation of orbital `j` on the encoded
basis. -/
theorem numOp_bkKet (j : Fin (2 ^ x)) (f : Fin (2 ^ x) → Bool) :
    numOp x j (bkKet x f) = if f j then bkKet x f else 0 := by
  rw [numOp, LinearMap.comp_apply, annOp_bkKet]
  cases hfj : f j
  · simp only [Bool.false_eq_true, if_false]
    exact map_zero _
  · rw [if_pos rfl, map_smul, creOp_bkKet, Function.update_self]
    have hs : signBelow x j (Function.update f j false) = signBelow x j f :=
      signBelow_update_of_le x j j (le_refl _) f false
    have hket : Function.update (Function.update f j false) j true = f := by
      rw [Function.update_idem, show true = f j from hfj.symm,
        Function.update_eq_self]
    simp only [Bool.false_eq_true, if_false, if_true, hs, hket, smul_smul,
      signBelow_mul_self, one_smul]

/-- **The number operator is the SRL `Z`-string** (arXiv:1208.5986 eq. (39)):
`n_j = ½ (1 − Z_{F(j) ∪ {j}})`. -/
theorem numOp_eq_zString (j : Fin (2 ^ x)) :
    numOp x j
      = (2 : ℂ)⁻¹ •
          ((1 : EndM (QubitCells (Fin (2 ^ x))) (univ : Finset (Fin (2 ^ x))))
            - pauliString (zOn (insert j (fSet x j)))) := by
  refine bkEndM_ext x fun f => ?_
  rw [numOp_bkKet, LinearMap.smul_apply, LinearMap.sub_apply,
    Module.End.one_apply, bkKet, pauliString_zOn_deltav]
  have hj : j ∉ fSet x j := fun hc => absurd (lt_of_mem_fSet hc) (lt_irrefl _)
  rw [Finset.prod_insert hj, prod_bsign_eq_signZ]
  have h1 : (if bkVec x f j then (-1 : ℂ) else 1) = signZ (bkVecZ x f j) := by
    rw [← bitZ_bkVec x f j]
    cases bkVec x f j
    · rw [bitZ_false, signZ_zero]
      simp
    · rw [bitZ_true, signZ_one]
      simp
  have h2 : (∑ k ∈ fSet x j, bitZ (bkVec x f k))
      = ∑ k ∈ fSet x j, bkVecZ x f k :=
    Finset.sum_congr rfl fun k _ => bitZ_bkVec x f k
  rw [h1, h2, ← signZ_add, fSet_parityZ]
  cases hfj : f j
  · rw [bitZ_false, signZ_zero, one_smul, sub_self, smul_zero]
    simp
  · rw [bitZ_true, signZ_one, if_pos rfl, neg_one_smul, sub_neg_eq_add,
      ← two_smul ℂ, smul_smul]
    norm_num

/-! ## §8. Axiom audit -/

#print axioms bk_car_ann
#print axioms bk_car_cre
#print axioms bk_car_mixed
#print axioms creOp_eq_adjoint
#print axioms numOp_eq_zString
#print axioms card_pSet_le
#print axioms card_uSet_le
#print axioms card_fSet_le

end Qhl.BravyiKitaev
