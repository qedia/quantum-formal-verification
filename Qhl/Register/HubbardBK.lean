import Qhl.Register.BKOperators

/-!
# The 1D spinless Fermi–Hubbard Hamiltonian under the Bravyi–Kitaev encoding

The Hamiltonian on `n = 2^x` fermionic modes (open chain, coefficients
`t U : ℝ`):

```
H  =  -t · ∑_{j<n-1} (a†_j a_{j+1} + a†_{j+1} a_j)  +  U · ∑_{j<n-1} n_j n_{j+1}
```

with the Bravyi–Kitaev ladder operators `annOp`/`creOp` and number operators
`numOp` of `Qhl/Register/BKOperators.lean`.  This file expresses `H` as an
explicit finite linear combination of `pauliString`s with **real**
coefficients — the shape an LCU block-encoding consumes — and proves the
**fermionic faithfulness theorem** `hubbardBK_eq` identifying the two.

The route avoids any Bravyi–Kitaev index-set combinatorics beyond what
`BKOperators` already established:

* **§1** the single-site Pauli **letter multiplication table**
  `PLetter.mul`/`PLetter.mulPh` (`p · q = mulPh p q • mul p q` as one-qubit
  operators), verified per case against the basis action `PLetter.ph`;
* **§2** the **string composition lemma** `pauliString_comp`: the composition
  of two Pauli strings is a global phase (the product of the per-site phases)
  times the sitewise-product string;
* **§3** every Pauli string is nonzero, and — when two strings anticommute —
  `i` times their composition phase is **real** (`phSign_spec`): the
  composition is anti-self-adjoint while the product string is self-adjoint;
* **§4** the SRL strings are the **Majorana operators** of the encoded modes,
  `X_{U(j)}X_jZ_{P(j)} = a_j + a†_j` and
  `X_{U(j)}Y_jZ_{ρ(j)} = i(a†_j − a_j)`, with uniform basis actions; their
  pairwise **anticommutation** follows from those actions exactly as the CAR
  did (no new set combinatorics);
* **§5** the **hopping identity**
  `a†_j a_k + a†_k a_j = (i/2)(γ_j γ̄_k − γ̄_j γ_k)` (`j < k`), proved on the
  encoded basis; combined with §2–§3 each hopping pair contributes **two**
  Pauli strings with real coefficients `±t/2` (`hop_strings`);
* **§6** each **interaction** pair contributes four `Z`-type strings with
  coefficients `±U/4`, from `numOp_eq_zString` and the fact that `Z`-strings
  compose without phase (`zNum_comp`);
* **§7** the term family `termString`/`termCoef` over the index
  `Fin (2^x - 1) × Fin 6` (per adjacent pair: the two hopping strings, the
  identity string, and the three `Z`-strings) and the faithfulness theorem
  `hubbardBK_eq`.

Constants: the interaction's identity part is kept as an explicit
identity-string term (index `2` of each pair), not dropped — the sum of the
six terms of pair `j` is *exactly* `-t·(hop pair) + U·(n_j n_{j+1})`.
-/

namespace Qhl

open Finset
open scoped ComplexInnerProductSpace

/-! ## §1. The single-site letter multiplication table -/

namespace PLetter

/-- The letter of the one-qubit operator product `p · q` (apply `q` first). -/
def mul : PLetter → PLetter → PLetter
  | one, q => q
  | p, one => p
  | x, x => one
  | x, y => z
  | x, z => y
  | y, x => z
  | y, y => one
  | y, z => x
  | z, x => y
  | z, y => x
  | z, z => one

/-- The phase of the one-qubit operator product `p · q` relative to its
letter: `p · q = mulPh p q • mul p q` (e.g. `X·Y = i Z`, `Y·X = -i Z`). -/
noncomputable def mulPh : PLetter → PLetter → ℂ
  | x, y => Complex.I
  | y, z => Complex.I
  | z, x => Complex.I
  | y, x => -Complex.I
  | z, y => -Complex.I
  | x, z => -Complex.I
  | _, _ => 1

/-- The product letter flips iff exactly one factor flips. -/
theorem flips_mul (p q : PLetter) : (mul p q).flips = xor p.flips q.flips := by
  cases p <;> cases q <;> rfl

/-- The product letter is symmetric (only the phase is order-sensitive). -/
theorem mul_comm' (p q : PLetter) : mul p q = mul q p := by
  cases p <;> cases q <;> rfl

/-- Every product phase is a unit. -/
theorem norm_mulPh (p q : PLetter) : ‖mulPh p q‖ = 1 := by
  cases p <;> cases q <;> simp [mulPh]

/-- **The per-site composition identity**: applying `q` then `p` to `∣b⟩`
accumulates exactly the product phase and the product letter's scalar. -/
theorem ph_comp (p q : PLetter) (b : Bool) :
    q.ph b * p.ph (xor q.flips b) = mulPh p q * (mul p q).ph b := by
  cases p <;> cases q <;> cases b <;>
    simp [ph, flips, mul, mulPh, Complex.I_mul_I]

end PLetter

/-! ## §2. Composition of Pauli strings -/

section Comp

variable {L : Type*} [Fintype L] [DecidableEq L]

/-- The all-identity string is the identity operator. -/
theorem pauliString_one :
    pauliString (fun _ : L => PLetter.one) = 1 := by
  refine qubitEndM_ext fun f => ?_
  rw [pauliString_deltav, Module.End.one_apply]
  simp [PLetter.ph, PLetter.flips]

/-- **String composition**: the composition of two Pauli strings is the
product of the per-site phases times the sitewise-product string. -/
theorem pauliString_comp (P Q : L → PLetter) :
    pauliString P ∘ₗ pauliString Q
      = (∏ k, PLetter.mulPh (P k) (Q k)) •
          pauliString (fun k => PLetter.mul (P k) (Q k)) := by
  refine qubitEndM_ext fun f => ?_
  rw [LinearMap.comp_apply, pauliString_deltav, map_smul, pauliString_deltav,
    LinearMap.smul_apply, pauliString_deltav, smul_smul, smul_smul]
  have hket : (fun k => xor (P k).flips (xor (Q k).flips (f k)))
      = fun k => xor ((PLetter.mul (P k) (Q k)).flips) (f k) := by
    funext k
    rw [PLetter.flips_mul, Bool.xor_assoc]
  rw [hket]
  refine congrArg (· • _) ?_
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => PLetter.ph_comp (P k) (Q k) (f k)

/-- No Pauli string is the zero operator (each is an involution). -/
theorem pauliString_ne_zero (P : L → PLetter) : pauliString P ≠ 0 := by
  intro hc
  have h1 := pauliString_comp_self P
  rw [hc, LinearMap.zero_comp] at h1
  have h2 := congrArg (fun M : EndM (QubitCells L) (univ : Finset L) =>
    M (deltav (QubitCells L) (qbIdx L fun _ => false))) h1
  simp only [LinearMap.zero_apply, Module.End.one_apply] at h2
  have h3 : ‖deltav (QubitCells L) (qbIdx L fun _ => false)‖ = 1 := by
    rw [deltav_def]
    rw [show (EuclideanSpace.single (qbIdx L fun _ => false) (1 : ℂ))
        = PiLp.single 2 (qbIdx L fun _ => false) (1 : ℂ) from rfl, PiLp.norm_single]
    norm_num
  rw [← h2] at h3
  simp at h3

end Comp

/-! ## §3. The composition phase of anticommuting strings is `±i` -/

section Phase

variable {L : Type*} [Fintype L] [DecidableEq L]

/-- The global composition phase of a pair of strings. -/
noncomputable def phFactor (P Q : L → PLetter) : ℂ :=
  ∏ k, PLetter.mulPh (P k) (Q k)

theorem norm_phFactor (P Q : L → PLetter) : ‖phFactor P Q‖ = 1 := by
  rw [phFactor, norm_prod]
  exact Finset.prod_eq_one fun k _ => PLetter.norm_mulPh _ _

/-- Scalars are cancellable against a fixed Pauli string. -/
theorem smul_pauliString_injective (R : L → PLetter) {c d : ℂ}
    (h : c • pauliString R = d • pauliString R) : c = d := by
  have h2 : (c - d) • pauliString R = 0 := by
    rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact sub_eq_zero.mp h3
  · exact absurd h3 (pauliString_ne_zero R)

/-- If two strings anticommute, their composition phase is purely
imaginary: the composition is anti-self-adjoint while the product string is
self-adjoint. -/
theorem phFactor_re_eq_zero (P Q : L → PLetter)
    (hac : pauliString P ∘ₗ pauliString Q + pauliString Q ∘ₗ pauliString P = 0) :
    (phFactor P Q).re = 0 := by
  have hPQ := pauliString_comp P Q
  have hQP := pauliString_comp Q P
  have hmul : (fun k => PLetter.mul (Q k) (P k))
      = fun k => PLetter.mul (P k) (Q k) := by
    funext k
    rw [PLetter.mul_comm']
  rw [hmul] at hQP
  -- anticommutation gives `∏ mulPh Q P = -∏ mulPh P Q`
  have hneg : (∏ k, PLetter.mulPh (Q k) (P k)) = -∏ k, PLetter.mulPh (P k) (Q k) := by
    have h2 : ((∏ k, PLetter.mulPh (P k) (Q k)) + ∏ k, PLetter.mulPh (Q k) (P k)) •
        pauliString (fun k => PLetter.mul (P k) (Q k))
        = (0 : ℂ) • pauliString (fun k => PLetter.mul (P k) (Q k)) := by
      rw [add_smul, ← hPQ, ← hQP, zero_smul]
      exact hac
    have h3 := smul_pauliString_injective _ h2
    linear_combination h3
  -- adjointness gives `∏ mulPh Q P = conj (∏ mulPh P Q)`
  have hadj : (starRingEnd ℂ) (∏ k, PLetter.mulPh (P k) (Q k))
      = ∏ k, PLetter.mulPh (Q k) (P k) := by
    have h1 : LinearMap.adjoint (pauliString P ∘ₗ pauliString Q)
        = pauliString Q ∘ₗ pauliString P := by
      rw [LinearMap.adjoint_comp, adjoint_pauliString, adjoint_pauliString]
    rw [hPQ, hQP, ← LinearMap.star_eq_adjoint, star_smul,
      LinearMap.star_eq_adjoint, adjoint_pauliString] at h1
    exact smul_pauliString_injective _ h1
  have h4 := congrArg Complex.re (hadj.trans hneg)
  simp only [Complex.conj_re, Complex.neg_re] at h4
  show (∏ k, PLetter.mulPh (P k) (Q k)).re = 0
  linarith

/-- The **real sign** of an anticommuting string composition:
`i · phFactor P Q`, as a real number. -/
noncomputable def phSign (P Q : L → PLetter) : ℝ :=
  (Complex.I * phFactor P Q).re

/-- Under anticommutation, `i · phFactor P Q` *is* the real `phSign P Q`. -/
theorem phSign_spec (P Q : L → PLetter)
    (hac : pauliString P ∘ₗ pauliString Q + pauliString Q ∘ₗ pauliString P = 0) :
    (phSign P Q : ℂ) = Complex.I * phFactor P Q := by
  have him : (Complex.I * phFactor P Q).im = 0 := by
    rw [Complex.mul_im]
    simp [phFactor_re_eq_zero P Q hac]
  exact Complex.ext (by simp [phSign]) (by simp [him])

end Phase

/-! ## §4. The Majorana operators of the encoded modes -/

namespace BravyiKitaev

variable (x : ℕ)

/-- The `X`-type Majorana string `γ_j = X_{U(j)} X_j Z_{P(j)}`. -/
noncomputable abbrev majX (j : Fin (2 ^ x)) :
    EndM (QubitCells (Fin (2 ^ x))) (univ : Finset (Fin (2 ^ x))) :=
  pauliString (xStr x j)

/-- The `Y`-type Majorana string `γ̄_j = X_{U(j)} Y_j Z_{ρ(j)}`. -/
noncomputable abbrev majY (j : Fin (2 ^ x)) :
    EndM (QubitCells (Fin (2 ^ x))) (univ : Finset (Fin (2 ^ x))) :=
  pauliString (yStr x j)

/-- `γ_j = a_j + a†_j`. -/
theorem majX_eq (j : Fin (2 ^ x)) : majX x j = annOp x j + creOp x j := by
  rw [annOp, creOp, ← smul_add]
  have h : (pauliString (xStr x j) + Complex.I • pauliString (yStr x j))
      + (pauliString (xStr x j) - Complex.I • pauliString (yStr x j))
      = (2 : ℂ) • pauliString (xStr x j) := by
    module
  rw [h, smul_smul]
  norm_num

/-- `γ̄_j = i (a†_j − a_j)`. -/
theorem majY_eq (j : Fin (2 ^ x)) :
    majY x j = Complex.I • (creOp x j - annOp x j) := by
  rw [annOp, creOp, ← smul_sub]
  have h : (pauliString (xStr x j) - Complex.I • pauliString (yStr x j))
      - (pauliString (xStr x j) + Complex.I • pauliString (yStr x j))
      = (-2 * Complex.I) • pauliString (yStr x j) := by
    module
  rw [h, smul_smul, smul_smul]
  have hone : Complex.I * (2 : ℂ)⁻¹ * (-2 * Complex.I) = 1 := by
    linear_combination (-1 : ℂ) * Complex.I_mul_I
  rw [hone, one_smul]

/-- The uniform basis action of `γ_j`: flip the occupation of orbital `j`,
with the Jordan–Wigner sign. -/
theorem majX_bkKet (j : Fin (2 ^ x)) (f : Fin (2 ^ x) → Bool) :
    majX x j (bkKet x f)
      = signBelow x j f • bkKet x (Function.update f j (!(f j))) := by
  rw [majX_eq, LinearMap.add_apply, annOp_bkKet, creOp_bkKet]
  cases hfj : f j
  · simp
  · simp

/-- The uniform basis action of `γ̄_j`: flip the occupation of orbital `j`,
with the Jordan–Wigner sign and the `Y`-phase `∓i`. -/
theorem majY_bkKet (j : Fin (2 ^ x)) (f : Fin (2 ^ x) → Bool) :
    majY x j (bkKet x f)
      = ((if f j then -Complex.I else Complex.I) * signBelow x j f) •
          bkKet x (Function.update f j (!(f j))) := by
  rw [majY_eq, LinearMap.smul_apply, LinearMap.sub_apply, annOp_bkKet, creOp_bkKet]
  cases hfj : f j
  · simp [smul_smul]
  · simp [smul_smul, ← neg_smul]

/-- Two `X`-type Majoranas of distinct modes anticommute (from the uniform
actions and the Jordan–Wigner sign algebra, exactly as the CAR). -/
theorem majX_majX_anticomm (j k : Fin (2 ^ x)) (hjk : j ≠ k) :
    majX x j ∘ₗ majX x k + majX x k ∘ₗ majX x j = 0 := by
  refine bkEndM_ext x fun f => ?_
  rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearMap.zero_apply, majX_bkKet, majX_bkKet, map_smul, map_smul,
    majX_bkKet, majX_bkKet]
  rw [Function.update_of_ne hjk, Function.update_of_ne (Ne.symm hjk),
    smul_smul, smul_smul]
  have hket : Function.update (Function.update f k (!(f k))) j (!(f j))
      = Function.update (Function.update f j (!(f j))) k (!(f k)) :=
    (Function.update_comm hjk _ _ f).symm
  rw [hket, ← add_smul]
  have hcoef : signBelow x k f * signBelow x j (Function.update f k (!(f k)))
        + signBelow x j f * signBelow x k (Function.update f j (!(f j)))
      = 0 := by
    rcases Nat.lt_trichotomy (j : ℕ) (k : ℕ) with h | h | h
    · rw [signBelow_update_of_le x j k (le_of_lt h),
        signBelow_update_flip x k j h f (!(f j)) (by cases f j <;> rfl)]
      ring
    · exact absurd (Fin.ext h) hjk
    · rw [signBelow_update_flip x j k h f (!(f k)) (by cases f k <;> rfl),
        signBelow_update_of_le x k j (le_of_lt h)]
      ring
  rw [hcoef, zero_smul]

/-- Two `Y`-type Majoranas of distinct modes anticommute. -/
theorem majY_majY_anticomm (j k : Fin (2 ^ x)) (hjk : j ≠ k) :
    majY x j ∘ₗ majY x k + majY x k ∘ₗ majY x j = 0 := by
  refine bkEndM_ext x fun f => ?_
  rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearMap.zero_apply, majY_bkKet, majY_bkKet, map_smul, map_smul,
    majY_bkKet, majY_bkKet]
  rw [Function.update_of_ne hjk, Function.update_of_ne (Ne.symm hjk),
    smul_smul, smul_smul]
  have hket : Function.update (Function.update f k (!(f k))) j (!(f j))
      = Function.update (Function.update f j (!(f j))) k (!(f k)) :=
    (Function.update_comm hjk _ _ f).symm
  rw [hket, ← add_smul]
  have hcoef : (if f k then -Complex.I else Complex.I) * signBelow x k f
        * ((if f j then -Complex.I else Complex.I)
            * signBelow x j (Function.update f k (!(f k))))
        + (if f j then -Complex.I else Complex.I) * signBelow x j f
          * ((if f k then -Complex.I else Complex.I)
              * signBelow x k (Function.update f j (!(f j))))
      = 0 := by
    rcases Nat.lt_trichotomy (j : ℕ) (k : ℕ) with h | h | h
    · rw [signBelow_update_of_le x j k (le_of_lt h),
        signBelow_update_flip x k j h f (!(f j)) (by cases f j <;> rfl)]
      ring
    · exact absurd (Fin.ext h) hjk
    · rw [signBelow_update_flip x j k h f (!(f k)) (by cases f k <;> rfl),
        signBelow_update_of_le x k j (le_of_lt h)]
      ring
  rw [hcoef, zero_smul]

/-- An `X`-type and a `Y`-type Majorana **always** anticommute (also at the
same mode: there the two orders carry the phases `∓i` and `±i`). -/
theorem majX_majY_anticomm (j k : Fin (2 ^ x)) :
    majX x j ∘ₗ majY x k + majY x k ∘ₗ majX x j = 0 := by
  refine bkEndM_ext x fun f => ?_
  rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearMap.zero_apply, majY_bkKet, majX_bkKet, map_smul, map_smul,
    majX_bkKet, majY_bkKet]
  by_cases hjk : j = k
  · subst hjk
    have hs : signBelow x j (Function.update f j (!(f j))) = signBelow x j f :=
      signBelow_update_of_le x j j (le_refl _) f _
    rw [hs, smul_smul, smul_smul, Function.update_self]
    have h1 : Function.update (Function.update f j (!(f j))) j (!!(f j)) = f := by
      rw [Function.update_idem, Bool.not_not, Function.update_eq_self]
    rw [h1, ← add_smul]
    have hcoef : (if f j = true then -Complex.I else Complex.I) * signBelow x j f
          * signBelow x j f
          + signBelow x j f
            * ((if (!(f j)) = true then -Complex.I else Complex.I) * signBelow x j f)
        = 0 := by
      cases f j <;> simp <;> ring
    rw [hcoef, zero_smul]
  · rw [Function.update_of_ne hjk, Function.update_of_ne (Ne.symm hjk),
      smul_smul, smul_smul]
    have hket : Function.update (Function.update f k (!(f k))) j (!(f j))
        = Function.update (Function.update f j (!(f j))) k (!(f k)) :=
      (Function.update_comm hjk _ _ f).symm
    rw [hket, ← add_smul]
    have hcoef : (if f k then -Complex.I else Complex.I) * signBelow x k f
          * signBelow x j (Function.update f k (!(f k)))
          + signBelow x j f
            * ((if f k then -Complex.I else Complex.I)
                * signBelow x k (Function.update f j (!(f j))))
        = 0 := by
      rcases Nat.lt_trichotomy (j : ℕ) (k : ℕ) with h | h | h
      · rw [signBelow_update_of_le x j k (le_of_lt h),
          signBelow_update_flip x k j h f (!(f j)) (by cases f j <;> rfl)]
        ring
      · exact absurd (Fin.ext h) hjk
      · rw [signBelow_update_flip x j k h f (!(f k)) (by cases f k <;> rfl),
          signBelow_update_of_le x k j (le_of_lt h)]
        ring
    rw [hcoef, zero_smul]

/-! ## §5. The hopping identity and its two Pauli strings -/

/-- **The hopping identity** on the encoded basis (`j < k`):
`a†_j a_k + a†_k a_j = (i/2)(γ_j γ̄_k − γ̄_j γ_k)`. -/
theorem hop_pair_eq (j k : Fin (2 ^ x)) (hjk : (j : ℕ) < (k : ℕ)) :
    creOp x j ∘ₗ annOp x k + creOp x k ∘ₗ annOp x j
      = (Complex.I / 2) • (majX x j ∘ₗ majY x k)
        - (Complex.I / 2) • (majY x j ∘ₗ majX x k) := by
  have hne : j ≠ k := fun hc => by rw [hc] at hjk; omega
  refine bkEndM_ext x fun f => ?_
  rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.add_apply,
    LinearMap.comp_apply, LinearMap.comp_apply,
    majY_bkKet, majX_bkKet, map_smul, map_smul, majX_bkKet, majY_bkKet,
    annOp_bkKet, annOp_bkKet, signBelow_update_of_le x j k (le_of_lt hjk)]
  by_cases hfj : f j = true <;> by_cases hfk : f k = true
  · -- both occupied: both hopping orders die, and the two Majorana orders
    -- cancel by the `Y`-phases alone
    rw [if_pos hfk, if_pos hfj, map_smul, map_smul, creOp_bkKet, creOp_bkKet]
    simp [Function.update_of_ne hne, Function.update_of_ne (Ne.symm hne),
      hfj, hfk, smul_smul]
    try module
  · -- `j` occupied, `k` empty: only `a†_k a_j` fires
    have hfk' : f k = false := by simpa using hfk
    rw [if_neg hfk, if_pos hfj, map_zero, zero_add, map_smul, creOp_bkKet,
      Function.update_of_ne (Ne.symm hne), if_neg hfk,
      signBelow_update_flip x k j hjk f false (by rw [hfj]; rfl),
      Function.update_comm (Ne.symm hne : k ≠ j)]
    simp [Function.update_of_ne hne, hfj, hfk', smul_smul]
    rw [← neg_smul, ← add_smul]
    congr 1
    linear_combination (-(signBelow x j f * signBelow x k f)) * Complex.I_mul_I
  · -- `j` empty, `k` occupied: only `a†_j a_k` fires
    have hfj' : f j = false := by simpa using hfj
    rw [if_pos hfk, if_neg hfj, map_zero, map_smul, creOp_bkKet,
      Function.update_of_ne hne, if_neg hfj, add_zero,
      signBelow_update_of_le x j k (le_of_lt hjk)]
    simp [Function.update_of_ne hne, hfj', hfk, smul_smul]
    rw [← neg_smul, ← sub_smul]
    congr 1
    linear_combination (signBelow x k f * signBelow x j f) * Complex.I_mul_I
  · -- both empty: both hopping orders die, phases cancel again
    have hfj' : f j = false := by simpa using hfj
    have hfk' : f k = false := by simpa using hfk
    rw [if_neg hfk, if_neg hfj, map_zero, map_zero, add_zero]
    simp [Function.update_of_ne hne, Function.update_of_ne (Ne.symm hne),
      hfj', hfk', smul_smul]
    try module

/-! ## §6. The interaction pair as four `Z`-type strings -/

/-- The support of the number operator's `Z`-string: `F(j) ∪ {j}`. -/
noncomputable def nSet (j : Fin (2 ^ x)) : Finset (Fin (2 ^ x)) :=
  insert j (fSet x j)

/-- The number operator's `Z`-string. -/
noncomputable abbrev zNum (j : Fin (2 ^ x)) :
    EndM (QubitCells (Fin (2 ^ x))) (univ : Finset (Fin (2 ^ x))) :=
  pauliString (zOn (nSet x j))

/-- `Z`-strings compose without phase, on the symmetric difference of their
supports. -/
theorem zNum_comp (j k : Fin (2 ^ x)) :
    zNum x j ∘ₗ zNum x k = pauliString (zOn (symmDiff (nSet x j) (nSet x k))) := by
  rw [pauliString_comp]
  have hph : (∏ i, PLetter.mulPh (zOn (nSet x j) i) (zOn (nSet x k) i)) = 1 :=
    Finset.prod_eq_one fun i _ => by
      by_cases h1 : i ∈ nSet x j <;> by_cases h2 : i ∈ nSet x k <;>
        simp [zOn, h1, h2, PLetter.mulPh]
  have hmul : (fun i => PLetter.mul (zOn (nSet x j) i) (zOn (nSet x k) i))
      = zOn (symmDiff (nSet x j) (nSet x k)) := by
    funext i
    by_cases h1 : i ∈ nSet x j <;> by_cases h2 : i ∈ nSet x k <;>
      simp [zOn, h1, h2, PLetter.mul, Finset.mem_symmDiff]
  rw [hph, hmul, one_smul]

/-- **The interaction identity**: `n_j n_k` is the four-term `Z`-string
combination `¼(1 - Z_{S_j} - Z_{S_k} + Z_{S_j Δ S_k})`. -/
theorem numOp_pair_eq (j k : Fin (2 ^ x)) :
    numOp x j ∘ₗ numOp x k
      = (4⁻¹ : ℂ) • (1 : EndM (QubitCells (Fin (2 ^ x))) (univ : Finset (Fin (2 ^ x))))
        - (4⁻¹ : ℂ) • zNum x j - (4⁻¹ : ℂ) • zNum x k
        + (4⁻¹ : ℂ) • pauliString (zOn (symmDiff (nSet x j) (nSet x k))) := by
  have hj := numOp_eq_zString x j
  have hk := numOp_eq_zString x k
  have hjn : numOp x j = (2 : ℂ)⁻¹ • (1 - zNum x j) := hj
  have hkn : numOp x k = (2 : ℂ)⁻¹ • (1 - zNum x k) := hk
  rw [hjn, hkn, LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]
  have hcomp : (1 - zNum x j) ∘ₗ (1 - zNum x k)
      = 1 - zNum x k - zNum x j + zNum x j ∘ₗ zNum x k := by
    simp only [LinearMap.sub_comp, LinearMap.comp_sub, Module.End.one_eq_id,
      LinearMap.id_comp, LinearMap.comp_id]
    abel
  rw [hcomp, zNum_comp]
  have h2 : ((2 : ℂ)⁻¹ * (2 : ℂ)⁻¹) = (4⁻¹ : ℂ) := by norm_num
  rw [h2]
  module

/-! ## §7. The term family and the faithfulness theorem -/

/-- The number of adjacent pairs of the open chain. -/
abbrev nPairs : ℕ := 2 ^ x - 1

/-- The left mode of pair `j`. -/
def pL (j : Fin (nPairs x)) : Fin (2 ^ x) :=
  ⟨(j : ℕ), by have h := j.isLt; unfold nPairs at h; omega⟩

/-- The right mode of pair `j`. -/
def pR (j : Fin (nPairs x)) : Fin (2 ^ x) :=
  ⟨(j : ℕ) + 1, by have h := j.isLt; unfold nPairs at h; omega⟩

theorem pL_lt_pR (j : Fin (nPairs x)) : ((pL x j : Fin (2 ^ x)) : ℕ) < (pR x j : ℕ) := by
  simp [pL, pR]

/-- The first hopping string of pair `j`: the sitewise product of
`γ_{j}`'s and `γ̄_{j+1}`'s letters. -/
noncomputable def hopStrA (j : Fin (nPairs x)) : Fin (2 ^ x) → PLetter :=
  fun i => PLetter.mul (xStr x (pL x j) i) (yStr x (pR x j) i)

/-- The second hopping string of pair `j`: the sitewise product of
`γ̄_{j}`'s and `γ_{j+1}`'s letters. -/
noncomputable def hopStrB (j : Fin (nPairs x)) : Fin (2 ^ x) → PLetter :=
  fun i => PLetter.mul (yStr x (pL x j) i) (xStr x (pR x j) i)

/-- The real sign of the first hopping string (`±1`). -/
noncomputable def hopSignA (j : Fin (nPairs x)) : ℝ :=
  phSign (xStr x (pL x j)) (yStr x (pR x j))

/-- The real sign of the second hopping string (`±1`). -/
noncomputable def hopSignB (j : Fin (nPairs x)) : ℝ :=
  phSign (yStr x (pL x j)) (xStr x (pR x j))

theorem hopSignA_spec (j : Fin (nPairs x)) :
    ((hopSignA x j : ℝ) : ℂ)
      = Complex.I * phFactor (xStr x (pL x j)) (yStr x (pR x j)) :=
  phSign_spec _ _ (majX_majY_anticomm x (pL x j) (pR x j))

theorem hopSignB_spec (j : Fin (nPairs x)) :
    ((hopSignB x j : ℝ) : ℂ)
      = Complex.I * phFactor (yStr x (pL x j)) (xStr x (pR x j)) := by
  refine phSign_spec _ _ ?_
  rw [add_comm]
  exact majX_majY_anticomm x (pR x j) (pL x j)

/-- **The hopping pair as two Pauli strings with real coefficients.** -/
theorem hop_strings (j : Fin (nPairs x)) :
    creOp x (pL x j) ∘ₗ annOp x (pR x j) + creOp x (pR x j) ∘ₗ annOp x (pL x j)
      = ((hopSignA x j / 2 : ℝ) : ℂ) • pauliString (hopStrA x j)
        - ((hopSignB x j / 2 : ℝ) : ℂ) • pauliString (hopStrB x j) := by
  rw [hop_pair_eq x (pL x j) (pR x j) (pL_lt_pR x j)]
  rw [show majX x (pL x j) ∘ₗ majY x (pR x j)
      = phFactor (xStr x (pL x j)) (yStr x (pR x j)) • pauliString (hopStrA x j) from
    pauliString_comp _ _]
  rw [show majY x (pL x j) ∘ₗ majX x (pR x j)
      = phFactor (yStr x (pL x j)) (xStr x (pR x j)) • pauliString (hopStrB x j) from
    pauliString_comp _ _]
  rw [smul_smul, smul_smul]
  have hA : Complex.I / 2 * phFactor (xStr x (pL x j)) (yStr x (pR x j))
      = ((hopSignA x j / 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_div, hopSignA_spec]
    push_cast
    ring
  have hB : Complex.I / 2 * phFactor (yStr x (pL x j)) (xStr x (pR x j))
      = ((hopSignB x j / 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_div, hopSignB_spec]
    push_cast
    ring
  rw [hA, hB]

/-- The letter assignment of term `(j, i)`: per adjacent pair `j`, the two
hopping strings, the identity string, and the three interaction `Z`-strings. -/
noncomputable def termString (l : Fin (nPairs x) × Fin 6) : Fin (2 ^ x) → PLetter :=
  if (l.2 : ℕ) = 0 then hopStrA x l.1
  else if (l.2 : ℕ) = 1 then hopStrB x l.1
  else if (l.2 : ℕ) = 2 then fun _ => PLetter.one
  else if (l.2 : ℕ) = 3 then zOn (nSet x (pL x l.1))
  else if (l.2 : ℕ) = 4 then zOn (nSet x (pR x l.1))
  else zOn (symmDiff (nSet x (pL x l.1)) (nSet x (pR x l.1)))

/-- The real coefficient of term `(j, i)` at hopping strength `t` and
interaction strength `U`. -/
noncomputable def termCoef (t U : ℝ) (l : Fin (nPairs x) × Fin 6) : ℝ :=
  if (l.2 : ℕ) = 0 then -(t * hopSignA x l.1) / 2
  else if (l.2 : ℕ) = 1 then t * hopSignB x l.1 / 2
  else if (l.2 : ℕ) = 2 then U / 4
  else if (l.2 : ℕ) = 3 then -(U / 4)
  else if (l.2 : ℕ) = 4 then -(U / 4)
  else U / 4

/-- **The 1D spinless Fermi–Hubbard Hamiltonian** on the `2^x`-mode open
chain, built from the Bravyi–Kitaev ladder and number operators. -/
noncomputable def hubbardOp (t U : ℝ) :
    EndM (QubitCells (Fin (2 ^ x))) (univ : Finset (Fin (2 ^ x))) :=
  (-(t : ℂ)) • ∑ j : Fin (nPairs x),
      (creOp x (pL x j) ∘ₗ annOp x (pR x j) + creOp x (pR x j) ∘ₗ annOp x (pL x j))
    + (U : ℂ) • ∑ j : Fin (nPairs x), numOp x (pL x j) ∘ₗ numOp x (pR x j)

/-- The six terms of one pair sum to that pair's Hamiltonian contribution. -/
theorem pair_sum_eq (t U : ℝ) (j : Fin (nPairs x)) :
    (∑ i : Fin 6, ((termCoef x t U (j, i) : ℝ) : ℂ) • pauliString (termString x (j, i)))
      = (-(t : ℂ)) •
          (creOp x (pL x j) ∘ₗ annOp x (pR x j) + creOp x (pR x j) ∘ₗ annOp x (pL x j))
        + (U : ℂ) • (numOp x (pL x j) ∘ₗ numOp x (pR x j)) := by
  rw [Fin.sum_univ_six, hop_strings x j, numOp_pair_eq x (pL x j) (pR x j)]
  simp only [termCoef, termString]
  norm_num [pauliString_one]
  push_cast
  module

/-- **The fermionic faithfulness theorem of the lane**: the explicit real
Pauli-string family `termCoef`/`termString` *is* the Bravyi–Kitaev-encoded
Fermi–Hubbard Hamiltonian. -/
theorem hubbardBK_eq (t U : ℝ) :
    (∑ l : Fin (nPairs x) × Fin 6,
        ((termCoef x t U l : ℝ) : ℂ) • pauliString (termString x l))
      = hubbardOp x t U := by
  rw [Fintype.sum_prod_type, hubbardOp, Finset.smul_sum, Finset.smul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => pair_sum_eq x t U j

end BravyiKitaev

end Qhl

#print axioms Qhl.BravyiKitaev.hubbardBK_eq
#print axioms Qhl.BravyiKitaev.hop_pair_eq
#print axioms Qhl.BravyiKitaev.numOp_pair_eq
#print axioms Qhl.pauliString_comp
