import Qhl.Logic.Source.CountedStateChain
import Qhl.Logic.Soundness
import Qhl.Logic.CountedStateChain
import Qhl.Gate.Givens
import Qhl.Register.HubbardBK
import Qhl.Register.PauliChain

/-!
# The LCU block encoding of the Bravyi–Kitaev Fermi–Hubbard Hamiltonian

The 1D spinless Fermi–Hubbard Hamiltonian on `n = 2^x` modes was expressed in
`Qhl/Register/HubbardBK.lean` as the real Pauli-string family
`H = ∑_l c_l · P_l` (`hubbardBK_eq`).  This example builds its **LCU block
encoding** as a genuine `qWhile⁺` program on the sum world of `n` system
qubit cells and `N = 6(n-1)` **unary (one-hot) ancilla** cells.  Every loop
is a genuine counted `while` (the printed system has no `for` rule); the
classical store `STc = ℕ × ℕ × (ℝ × ℝ)` carries the outer counter, the inner
counter and the Hamiltonian coefficients `(t, U)`:

```
prepProg   =  X(a₀) ;
              c := 0 ; while c < N-1 do (a_c, a_{c+1}) *= Givens(θ_c(σ)) ; c := c+1 od
selProg    =  c := 0 ; while c < N do
                a_c *= sgn(c_c(σ)) ;
                (i := 0 ; while i < n do (a_c, q_i) *= C-(P_c)_i ; i := i+1 od) ;
                c := c+1 od
unprepProg =  (c := 0 ; while c < N-1 do
                 (a_{N-2-c}, a_{N-1-c}) *= Givens(-θ_{N-2-c}(σ)) ; c := c+1 od) ;
              X(a₀)
```

Every gate is **constant-arity** (one or two cells); all `n`-dependence lives
in the loop structure, and the rotation angles `θⱼ(σ) = arccos(aⱼ/tailⱼ)`,
the coefficient signs and the controlled letters are **computed from the
classical store** (the paper's parameterized-gate feature): each loop body
reads its register and its gate from the counters through the total
conversions `jCell`/`lCell`/`sCell`.  The amplitudes are `a_l = √(|c_l|/λ)`,
`λ = ∑|c_l|` (with the normalized fallback one-hot profile when `λ = 0`, so
every state family is a genuine unit family for every store value).

Deliverables (all closed by the printed `QHL⁺_tot` rules only —
(Ax-Uni), (Ax-Ski), (Ax-Ass), (R-Seq), (R-Cond), (R-Conseq), (R-Loop-tot) —
through `DerivTot.unitary_stateFam` and the counted-`while` layer
`DerivTot.countedStateChain` / `countedStateChain_rel` /
`countedRung_fam`, each loop ONE packaged-rule call along its
store-indexed invariant family; the UNPREPARE invariant `unprepSt` is the
prefix-chain operator `chainPre` applied to the post-SELECT state):

* `lcuDeriv` / `lcuValid` — the exact evolution triple
  `{ ∣0⟩ₐ ⊗ ψ }  prep ; select ; unprep  { ∣Φ_out⟩ }` for an arbitrary unit
  system state `ψ`, the output the named state `outSt`;
* `blockEncoding` — the **block-encoding identity**
  `(⟨0∣ₐ ⊗ 1) Φ_out = λ⁻¹ · H ψ` (the ancilla-vacuum block of the circuit
  applies `H/λ`), for every store with `λ > 0`;
* `effect_reading` — the Born reading: the expectation of the
  ancilla-all-zero **effect** in the output state is `‖H ψ‖² / λ²`;
* `pre_expect_one` — non-vacuity: the precondition holds with expectation `1`
  on the concrete pure input `∣0⟩ₐ ⊗ ψ`.
-/

namespace Qhl.HubbardLCU

open Qhl Qhl.BravyiKitaev Finset
open scoped ComplexInnerProductSpace ComplexOrder NNReal ENNReal

section

variable (x : ℕ)

/-! ## §1. The world and the LCU term data -/

/-- The number of LCU terms: six Pauli strings per adjacent pair. -/
abbrev NT : ℕ := nPairs x * 6

/-- The system labels. -/
abbrev SysL : Type := Fin (2 ^ x)

/-- The ancilla labels: one one-hot cell per LCU term. -/
abbrev AncL : Type := Fin (NT x)

/-- The world: system block ⊕ ancilla block, every cell a qubit. -/
abbrev WL : Type := SysL x ⊕ AncL x

/-- The classical store: the Hamiltonian coefficients `(t, U)`. -/
abbrev ST : Type := ℝ × ℝ

/-- The widened classical store of the counted loops: outer counter, inner
counter, Hamiltonian coefficients.  The outer counter is
`CounterLens.fst3 ST`, the inner (letter) counter `CounterLens.snd3 ST`. -/
abbrev STc : Type := ℕ × ℕ × ST

/-- The named accessor of the coefficient block of the widened store: every
state family and every semantic fact below reads the store only through
`coef`. -/
abbrev coef (σ : STc) : ST := σ.2.2

/-- The linear indexing of the term family. -/
def tIdx : Fin (NT x) ≃ Fin (nPairs x) × Fin 6 := finProdFinEquiv.symm

/-- The `i`-th Pauli string of the Hamiltonian. -/
noncomputable def str (i : Fin (NT x)) : Fin (2 ^ x) → PLetter :=
  termString x (tIdx x i)

/-- The `i`-th real coefficient, read from the store. -/
noncomputable def cf (σ : ST) (i : Fin (NT x)) : ℝ :=
  termCoef x σ.1 σ.2 (tIdx x i)

/-- The one-norm `λ = ∑ |c_l|` of the coefficient family. -/
noncomputable def lam (σ : ST) : ℝ := ∑ i : Fin (NT x), |cf x σ i|

/-- The sign of the `i`-th coefficient. -/
noncomputable def sg (σ : ST) (i : Fin (NT x)) : ℝ :=
  if cf x σ i < 0 then -1 else 1

theorem sg_mul_abs (σ : ST) (i : Fin (NT x)) :
    sg x σ i * |cf x σ i| = cf x σ i := by
  rw [sg]
  rcases lt_or_ge (cf x σ i) 0 with h | h
  · rw [if_pos h, abs_of_neg h]
    ring
  · rw [if_neg (not_lt.mpr h), abs_of_nonneg h, one_mul]

theorem sg_sq (σ : ST) (i : Fin (NT x)) : sg x σ i * sg x σ i = 1 := by
  rw [sg]
  split_ifs <;> norm_num

/-- The linear-index form of the faithfulness theorem `hubbardBK_eq`. -/
theorem hubbard_sum_eq (σ : ST) :
    (∑ i : Fin (NT x), ((cf x σ i : ℝ) : ℂ) • pauliString (str x i))
      = hubbardOp x σ.1 σ.2 := by
  rw [← hubbardBK_eq]
  exact Equiv.sum_comp (tIdx x)
    (fun l => ((termCoef x σ.1 σ.2 l : ℝ) : ℂ) • pauliString (termString x l))

theorem NT_pos (hx : 0 < x) : 0 < NT x := by
  have h1 : 1 < 2 ^ x := Nat.one_lt_two_pow_iff.mpr (by omega)
  have h2 : 0 < nPairs x := by
    unfold nPairs
    omega
  exact Nat.mul_pos h2 (by norm_num)

theorem NT_gt_one (hx : 0 < x) : 1 < NT x := by
  have h1 : 1 < 2 ^ x := Nat.one_lt_two_pow_iff.mpr (by omega)
  have h2 : 0 < nPairs x := by
    unfold nPairs
    omega
  show 1 < nPairs x * 6
  omega

variable (hx : 0 < x)

/-! ## §2. The amplitude profile, tails, and rotation angles -/

/-- The preparation amplitudes `a_i = √(|c_i|/λ)`, with the normalized
one-hot fallback at `λ = 0` (so the profile is a unit vector for **every**
store value). -/
noncomputable def am (σ : ST) (i : Fin (NT x)) : ℝ :=
  if 0 < lam x σ then Real.sqrt (|cf x σ i| / lam x σ)
  else if i = ⟨0, NT_pos x hx⟩ then 1 else 0

theorem am_nonneg (σ : ST) (i : Fin (NT x)) : 0 ≤ am x hx σ i := by
  rw [am]
  split_ifs <;> first | exact Real.sqrt_nonneg _ | norm_num

theorem sum_am_sq (σ : ST) : ∑ i : Fin (NT x), am x hx σ i ^ 2 = 1 := by
  by_cases h : 0 < lam x σ
  · simp only [am, if_pos h]
    have hterm : ∀ i : Fin (NT x),
        Real.sqrt (|cf x σ i| / lam x σ) ^ 2 = |cf x σ i| / lam x σ := fun i =>
      Real.sq_sqrt (div_nonneg (abs_nonneg _) (le_of_lt h))
    rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.sum_div, ← lam,
      div_self (ne_of_gt h)]
  · simp only [am, if_neg h]
    rw [Finset.sum_congr rfl (g := fun i => if i = ⟨0, NT_pos x hx⟩ then 1 else 0)
      fun i _ => by split_ifs <;> norm_num]
    rw [Finset.sum_ite_eq' univ (⟨0, NT_pos x hx⟩ : Fin (NT x)) (fun _ => (1 : ℝ)),
      if_pos (mem_univ _)]

/-- The tail norm `tail_k = √(∑_{i ≥ k} a_i²)`. -/
noncomputable def tl (σ : ST) (k : ℕ) : ℝ :=
  Real.sqrt (∑ i : Fin (NT x), if k ≤ (i : ℕ) then am x hx σ i ^ 2 else 0)

theorem tl_nonneg (σ : ST) (k : ℕ) : 0 ≤ tl x hx σ k := Real.sqrt_nonneg _

theorem tl_sum_nonneg (σ : ST) (k : ℕ) :
    0 ≤ ∑ i : Fin (NT x), if k ≤ (i : ℕ) then am x hx σ i ^ 2 else 0 :=
  Finset.sum_nonneg fun i _ => by
    split_ifs
    · positivity
    · exact le_refl 0

theorem tl_zero (σ : ST) : tl x hx σ 0 = 1 := by
  rw [tl]
  rw [Finset.sum_congr rfl (g := fun i => am x hx σ i ^ 2)
    fun i _ => if_pos (Nat.zero_le _)]
  rw [sum_am_sq x hx σ, Real.sqrt_one]

/-- The tail recursion: `tail_k² = a_k² + tail_{k+1}²`. -/
theorem tl_sq_succ (σ : ST) (k : ℕ) (hk : k < NT x) :
    tl x hx σ k ^ 2 = am x hx σ ⟨k, hk⟩ ^ 2 + tl x hx σ (k + 1) ^ 2 := by
  rw [tl, tl, Real.sq_sqrt (tl_sum_nonneg x hx σ k),
    Real.sq_sqrt (tl_sum_nonneg x hx σ (k + 1))]
  have hsplit : ∀ i : Fin (NT x),
      (if k ≤ (i : ℕ) then am x hx σ i ^ 2 else 0)
        = (if i = ⟨k, hk⟩ then am x hx σ ⟨k, hk⟩ ^ 2 else 0)
          + (if k + 1 ≤ (i : ℕ) then am x hx σ i ^ 2 else 0) := by
    intro i
    by_cases h1 : i = ⟨k, hk⟩
    · subst h1
      simp
    · have h2 : (i : ℕ) ≠ k := fun hc => h1 (Fin.ext hc)
      by_cases h3 : k ≤ (i : ℕ)
      · rw [if_pos h3, if_neg h1, if_pos (by omega), zero_add]
      · rw [if_neg h3, if_neg h1, if_neg (by omega), zero_add]
  rw [Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_add_distrib,
    Finset.sum_ite_eq' univ (⟨k, hk⟩ : Fin (NT x)), if_pos (mem_univ _)]

theorem tl_top (σ : ST) : tl x hx σ (NT x) = 0 := by
  rw [tl]
  rw [Finset.sum_congr rfl (g := fun _ => (0 : ℝ))
    fun i _ => if_neg (by have := i.isLt; omega)]
  rw [Finset.sum_const_zero, Real.sqrt_zero]

theorem am_le_tl (σ : ST) (k : ℕ) (hk : k < NT x) :
    am x hx σ ⟨k, hk⟩ ≤ tl x hx σ k := by
  rw [tl, show am x hx σ ⟨k, hk⟩ = Real.sqrt (am x hx σ ⟨k, hk⟩ ^ 2) from
    (Real.sqrt_sq (am_nonneg x hx σ _)).symm]
  refine Real.sqrt_le_sqrt ?_
  refine Finset.single_le_sum (f := fun i : Fin (NT x) =>
    if k ≤ (i : ℕ) then am x hx σ i ^ 2 else 0) (fun i _ => ?_) (mem_univ ⟨k, hk⟩)
    |>.trans_eq' ?_
  · split_ifs
    · positivity
    · exact le_refl 0
  · rw [if_pos (le_refl k)]

/-- The last tail is the last amplitude. -/
theorem tl_last (σ : ST) (hk : NT x - 1 < NT x) :
    tl x hx σ (NT x - 1) = am x hx σ ⟨NT x - 1, hk⟩ := by
  have h1 := tl_sq_succ x hx σ (NT x - 1) hk
  have h2 : NT x - 1 + 1 = NT x := by have := NT_pos x hx; omega
  rw [h2, tl_top] at h1
  have h3 : tl x hx σ (NT x - 1) ^ 2 = am x hx σ ⟨NT x - 1, hk⟩ ^ 2 := by
    rw [h1]
    ring
  calc tl x hx σ (NT x - 1) = Real.sqrt (tl x hx σ (NT x - 1) ^ 2) :=
        (Real.sqrt_sq (tl_nonneg x hx σ _)).symm
    _ = Real.sqrt (am x hx σ ⟨NT x - 1, hk⟩ ^ 2) := by rw [h3]
    _ = am x hx σ ⟨NT x - 1, hk⟩ := Real.sqrt_sq (am_nonneg x hx σ _)

/-- The chain angle of step `j`. -/
noncomputable def ang (σ : ST) (j : ℕ) (hj : j < NT x) : ℝ :=
  Real.arccos (am x hx σ ⟨j, hj⟩ / tl x hx σ j)

theorem div_am_tl_mem (σ : ST) (j : ℕ) (hj : j < NT x) :
    0 ≤ am x hx σ ⟨j, hj⟩ / tl x hx σ j ∧ am x hx σ ⟨j, hj⟩ / tl x hx σ j ≤ 1 := by
  rcases eq_or_lt_of_le (tl_nonneg x hx σ j) with h0 | h0
  · rw [← h0, div_zero]
    norm_num
  · exact ⟨div_nonneg (am_nonneg x hx σ _) (le_of_lt h0),
      (div_le_one h0).mpr (am_le_tl x hx σ j hj)⟩

/-- The cosine step law: `cos θⱼ · tailⱼ = aⱼ`. -/
theorem cos_ang_mul (σ : ST) (j : ℕ) (hj : j < NT x) :
    Real.cos (ang x hx σ j hj) * tl x hx σ j = am x hx σ ⟨j, hj⟩ := by
  rcases eq_or_lt_of_le (tl_nonneg x hx σ j) with h0 | h0
  · have ham : am x hx σ ⟨j, hj⟩ = 0 :=
      le_antisymm (by rw [h0]; exact am_le_tl x hx σ j hj) (am_nonneg x hx σ _)
    rw [← h0, mul_zero, ham]
  · rw [ang, Real.cos_arccos (by linarith [(div_am_tl_mem x hx σ j hj).1])
      (div_am_tl_mem x hx σ j hj).2]
    field_simp

/-- The sine step law: `sin θⱼ · tailⱼ = tailⱼ₊₁`. -/
theorem sin_ang_mul (σ : ST) (j : ℕ) (hj : j < NT x) :
    Real.sin (ang x hx σ j hj) * tl x hx σ j = tl x hx σ (j + 1) := by
  have hy := div_am_tl_mem x hx σ j hj
  have hsin : Real.sin (ang x hx σ j hj)
      = Real.sqrt (1 - (am x hx σ ⟨j, hj⟩ / tl x hx σ j) ^ 2) := by
    rw [ang, Real.sin_arccos]
  have hnn : 0 ≤ Real.sin (ang x hx σ j hj) * tl x hx σ j := by
    rw [hsin]
    exact mul_nonneg (Real.sqrt_nonneg _) (tl_nonneg x hx σ j)
  have hsq : (Real.sin (ang x hx σ j hj) * tl x hx σ j) ^ 2
      = tl x hx σ (j + 1) ^ 2 := by
    rw [mul_pow, hsin, Real.sq_sqrt (by nlinarith [hy.1, hy.2])]
    rcases eq_or_lt_of_le (tl_nonneg x hx σ j) with h0 | h0
    · have h1 := tl_sq_succ x hx σ j hj
      have ham : am x hx σ ⟨j, hj⟩ = 0 :=
        le_antisymm (by rw [h0]; exact am_le_tl x hx σ j hj) (am_nonneg x hx σ _)
      rw [← h0, ham] at h1
      rw [← h0]
      nlinarith [h1]
    · have h1 := tl_sq_succ x hx σ j hj
      field_simp
      nlinarith [h1]
  calc Real.sin (ang x hx σ j hj) * tl x hx σ j
      = Real.sqrt ((Real.sin (ang x hx σ j hj) * tl x hx σ j) ^ 2) :=
        (Real.sqrt_sq hnn).symm
    _ = Real.sqrt (tl x hx σ (j + 1) ^ 2) := by rw [hsq]
    _ = tl x hx σ (j + 1) := Real.sqrt_sq (tl_nonneg x hx σ _)

/-! ## §3. The registers and the program -/

/-- An ancilla cell, as a world label. -/
abbrev aC (i : AncL x) : WL x := Sum.inr i

/-- A system cell, as a world label. -/
abbrev sC (s : SysL x) : WL x := Sum.inl s

/-- The left cell of preparation step `j`. -/
def jA (j : Fin (NT x - 1)) : AncL x := ⟨(j : ℕ), by have := j.isLt; omega⟩

/-- The right cell of preparation step `j`. -/
def jB (j : Fin (NT x - 1)) : AncL x := ⟨(j : ℕ) + 1, by have := j.isLt; omega⟩

theorem jA_ne_jB (j : Fin (NT x - 1)) : aC x (jA x j) ≠ aC x (jB x j) := by
  intro hc
  have h1 := Sum.inr_injective hc
  have h2 : ((j : ℕ) : ℕ) = (j : ℕ) + 1 := congrArg Fin.val h1
  omega

theorem jB_lt (j : Fin (NT x - 1)) : (j : ℕ) + 1 < NT x := by
  have := j.isLt
  omega

theorem jA_lt (j : Fin (NT x - 1)) : (j : ℕ) < NT x := by
  have := j.isLt
  omega

/-! The total counter-to-cell conversions (the library `cell` pattern): each
loop body reads its register from the store counters through these, so the
register expressions are total; below the loop bound they read back the
counter exactly. -/

/-- The store-read preparation step: the `k % (N-1)`-th Givens position. -/
def jCell (k : ℕ) : Fin (NT x - 1) :=
  ⟨k % (NT x - 1), Nat.mod_lt _ (by have := NT_gt_one x hx; omega)⟩

theorem jCell_val {k : ℕ} (hk : k < NT x - 1) : ((jCell x hx k : Fin (NT x - 1)) : ℕ) = k :=
  Nat.mod_eq_of_lt hk

theorem jCell_eq_mk {k : ℕ} (hk : k < NT x - 1) : jCell x hx k = ⟨k, hk⟩ :=
  Fin.ext (jCell_val x hx hk)

/-- The store-read SELECT rung: the `k % N`-th term cell. -/
def lCell (k : ℕ) : AncL x := ⟨k % NT x, Nat.mod_lt _ (NT_pos x hx)⟩

theorem lCell_val {k : ℕ} (hk : k < NT x) : ((lCell x hx k : AncL x) : ℕ) = k :=
  Nat.mod_eq_of_lt hk

theorem lCell_eq_mk {k : ℕ} (hk : k < NT x) : lCell x hx k = ⟨k, hk⟩ :=
  Fin.ext (lCell_val x hx hk)

/-- The store-read system site: the `k % 2^x`-th mode. -/
def sCell (k : ℕ) : SysL x := ⟨k % 2 ^ x, Nat.mod_lt _ (Nat.pow_pos (by norm_num))⟩

theorem sCell_val {k : ℕ} (hk : k < 2 ^ x) : ((sCell x k : SysL x) : ℕ) = k :=
  Nat.mod_eq_of_lt hk

theorem sCell_eq_mk {k : ℕ} (hk : k < 2 ^ x) : sCell x k = ⟨k, hk⟩ :=
  Fin.ext (sCell_val x hk)

/-- The two-cell register of preparation step `j`. -/
noncomputable def prepReg (j : Fin (NT x - 1)) : Reg (WL x) 2 :=
  Reg.pair (aC x (jA x j)) (aC x (jB x j)) (jA_ne_jB x j)

/-- The `X` gate on ancilla cell `0`. -/
noncomputable def xProg0 : Prog STc (QubitCells (WL x)) :=
  Prog.unitary 1 (RegExpr.const (Reg.single (aC x ⟨0, NT_pos x hx⟩)))
    (fun _ => singleGate (QubitCells (WL x)) _ X)

/-- The PREPARE body's register expression: the Givens pair at the outer
counter. -/
noncomputable def prepRegE : RegExpr STc (WL x) 2 :=
  fun σ => (prepReg x (jCell x hx σ.1)).toFun

/-- The Givens gate at the outer counter, its angle computed from the
coefficient block of the store. -/
noncomputable def prepGateE (σ : STc) :
    UnitaryOp (TSpace (QubitCells (WL x)) (prepRegE x hx σ)) :=
  pairGate (D := QubitCells (WL x)) (aC x (jA x (jCell x hx σ.1)))
    (aC x (jB x (jCell x hx σ.1))) (jA_ne_jB x (jCell x hx σ.1))
    (givens (ang x hx (coef σ) ((jCell x hx σ.1 : Fin (NT x - 1)) : ℕ)
      (jA_lt x (jCell x hx σ.1))))

/-- The PREPARE loop body: one store-read Givens gate. -/
noncomputable def prepBody : Prog STc (QubitCells (WL x)) :=
  Prog.unitary 2 (prepRegE x hx) (prepGateE x hx)

/-- **PREPARE**: `X` on ancilla `0`, then the counted Givens chain. -/
noncomputable def prepProg : Prog STc (QubitCells (WL x)) :=
  (xProg0 x hx).seq
    (countedProg (CounterLens.fst3 ST) (fun _ => NT x - 1) (prepBody x hx))

/-- The sign body's register expression: the term cell at the outer
counter. -/
def sgnRegE : RegExpr STc (WL x) 1 :=
  fun σ => (Reg.single (aC x (lCell x hx σ.1))).toFun

/-- The sign gate at the outer counter, its sign computed from the
coefficient block of the store. -/
noncomputable def sgnGateE (σ : STc) :
    UnitaryOp (TSpace (QubitCells (WL x)) (sgnRegE x hx σ)) :=
  singleGate (QubitCells (WL x)) (aC x (lCell x hx σ.1))
    (sgnGate (cf x (coef σ) (lCell x hx σ.1)))

/-- The sign step of the SELECT rung. -/
noncomputable def sgnBody : Prog STc (QubitCells (WL x)) :=
  Prog.unitary 1 (sgnRegE x hx) (sgnGateE x hx)

/-- The controlled-letter register of rung `i` at system site `s`. -/
noncomputable def ctrlReg (i : AncL x) (s : SysL x) : Reg (WL x) 2 :=
  Reg.pair (aC x i) (sC x s) Sum.inr_ne_inl

/-- The controlled-letter body's register expression: the outer-counter term
cell paired with the inner-counter system site. -/
noncomputable def ctrlRegE : RegExpr STc (WL x) 2 :=
  fun σ => (ctrlReg x (lCell x hx σ.1) (sCell x σ.2.1)).toFun

/-- The controlled letter gate at the two counters. -/
noncomputable def ctrlGateE (σ : STc) :
    UnitaryOp (TSpace (QubitCells (WL x)) (ctrlRegE x hx σ)) :=
  pairGate (D := QubitCells (WL x)) (aC x (lCell x hx σ.1))
    (sC x (sCell x σ.2.1)) Sum.inr_ne_inl
    (control (str x (lCell x hx σ.1) (sCell x σ.2.1)).gate)

/-- The letter step of the SELECT rung. -/
noncomputable def ctrlBody : Prog STc (QubitCells (WL x)) :=
  Prog.unitary 2 (ctrlRegE x hx) (ctrlGateE x hx)

/-- **One SELECT rung**: the sign gate, then the counted letter loop over the
system sites (the inner counter). -/
noncomputable def rungBody : Prog STc (QubitCells (WL x)) :=
  (sgnBody x hx).seq
    (countedProg (CounterLens.snd3 ST) (fun _ => 2 ^ x) (ctrlBody x hx))

/-- **SELECT**: the counted rung loop over the term cells. -/
noncomputable def selProg : Prog STc (QubitCells (WL x)) :=
  countedProg (CounterLens.fst3 ST) (fun _ => NT x) (rungBody x hx)

/-- The UNPREPARE body's register expression: the Givens pair at the
**reversed** outer counter `N - 2 - c`. -/
noncomputable def unprepRegE : RegExpr STc (WL x) 2 :=
  fun σ => (prepReg x (jCell x hx (NT x - 2 - σ.1))).toFun

/-- The inverse Givens gate at the reversed outer counter. -/
noncomputable def unprepGateE (σ : STc) :
    UnitaryOp (TSpace (QubitCells (WL x)) (unprepRegE x hx σ)) :=
  pairGate (D := QubitCells (WL x)) (aC x (jA x (jCell x hx (NT x - 2 - σ.1))))
    (aC x (jB x (jCell x hx (NT x - 2 - σ.1)))) (jA_ne_jB x (jCell x hx (NT x - 2 - σ.1)))
    (givens (-(ang x hx (coef σ) ((jCell x hx (NT x - 2 - σ.1) : Fin (NT x - 1)) : ℕ)
      (jA_lt x (jCell x hx (NT x - 2 - σ.1))))))

/-- The UNPREPARE loop body: one store-read inverse Givens gate. -/
noncomputable def unprepBody : Prog STc (QubitCells (WL x)) :=
  Prog.unitary 2 (unprepRegE x hx) (unprepGateE x hx)

/-- **UNPREPARE**: the counted reversed inverse Givens chain, then `X` on
ancilla `0`. -/
noncomputable def unprepProg : Prog STc (QubitCells (WL x)) :=
  (countedProg (CounterLens.fst3 ST) (fun _ => NT x - 1) (unprepBody x hx)).seq
    (xProg0 x hx)

/-- **The LCU block-encoding program.** -/
noncomputable def lcuProg : Prog STc (QubitCells (WL x)) :=
  (prepProg x hx).seq ((selProg x hx).seq (unprepProg x hx))

/-! ## §4. The one-hot states and structural helpers -/

/-- The one-hot ancilla pattern. -/
def oneHot (i : AncL x) : AncL x → Bool := fun a => decide (a = i)

/-- The all-zero ancilla pattern. -/
def anc0 : AncL x → Bool := fun _ => false

theorem oneHot_self (i : AncL x) : oneHot x i i = true := by simp [oneHot]

theorem oneHot_ne {i a : AncL x} (h : a ≠ i) : oneHot x i a = false := by
  simp [oneHot, h]

theorem oneHot_injective : Function.Injective (oneHot x) := by
  intro i i' h
  have h2 := congrFun h i
  rw [oneHot_self] at h2
  have h3 : decide (i = i') = true := h2.symm
  exact of_decide_eq_true h3

/-- Sums agreeing off a pair of indices and in aggregate on the pair agree. -/
theorem sum_eq_of_eq_off_pair {V : Type*} [AddCommMonoid V] (a b : AncL x)
    (hab : a ≠ b) (G G' : AncL x → V)
    (hoff : ∀ i, i ≠ a → i ≠ b → G i = G' i)
    (hpair : G a + G b = G' a + G' b) :
    ∑ i : AncL x, G i = ∑ i : AncL x, G' i := by
  have hbm : b ∈ (univ : Finset (AncL x)).erase a :=
    Finset.mem_erase.mpr ⟨Ne.symm hab, mem_univ b⟩
  rw [← Finset.add_sum_erase _ G (mem_univ a), ← Finset.add_sum_erase _ G hbm,
    ← Finset.add_sum_erase _ G' (mem_univ a), ← Finset.add_sum_erase _ G' hbm]
  rw [← add_assoc, ← add_assoc, hpair]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have h1 := Finset.mem_erase.mp hi
  have h2 := Finset.mem_erase.mp h1.2
  exact hoff i h2.1 h1.1

/-- The inner product of two one-hot superpositions with per-branch system
vectors: branches are orthogonal, matching branches contract. -/
theorem inner_sum_emb (c d : AncL x → ℂ)
    (u v : AncL x → HS (QubitCells (SysL x)) (univ : Finset (SysL x))) :
    (⟪∑ i : AncL x, c i • ancEmbed (L₁ := SysL x) (oneHot x i) (u i),
      ∑ i : AncL x, d i • ancEmbed (L₁ := SysL x) (oneHot x i) (v i)⟫ : ℂ)
      = ∑ i : AncL x, (starRingEnd ℂ) (c i) * d i * ⟪u i, v i⟫ := by
  rw [sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_left, inner_sum]
  have hterm : ∀ i' : AncL x,
      (⟪ancEmbed (L₁ := SysL x) (oneHot x i) (u i),
        d i' • ancEmbed (L₁ := SysL x) (oneHot x i') (v i')⟫ : ℂ)
      = if i = i' then d i' * ⟪u i, v i'⟫ else 0 := by
    intro i'
    rw [inner_smul_right, inner_ancEmbed]
    by_cases h : i = i'
    · subst h
      rw [if_pos rfl, if_pos rfl]
    · rw [if_neg (fun hc => h (oneHot_injective x hc)), if_neg h, mul_zero]
  rw [Finset.sum_congr rfl fun i' _ => hterm i',
    Finset.sum_ite_eq univ i (fun i' => d i' * (⟪u i, v i'⟫ : ℂ)), if_pos (mem_univ i)]
  ring

/-- A one-hot superposition of unit branches with a unit coefficient profile
is a unit vector. -/
theorem norm_sum_emb (c : AncL x → ℝ)
    (u : AncL x → HS (QubitCells (SysL x)) (univ : Finset (SysL x)))
    (hu : ∀ i, ‖u i‖ = 1) (hc : ∑ i : AncL x, c i ^ 2 = 1) :
    ‖∑ i : AncL x, ((c i : ℝ) : ℂ) • ancEmbed (L₁ := SysL x) (oneHot x i) (u i)‖ = 1 := by
  refine norm_eq_one_of_inner_self ?_
  rw [inner_sum_emb]
  have hterm : ∀ i : AncL x,
      (starRingEnd ℂ) ((c i : ℝ) : ℂ) * ((c i : ℝ) : ℂ) * (⟪u i, u i⟫ : ℂ)
        = ((c i ^ 2 : ℝ) : ℂ) := by
    intro i
    rw [Complex.conj_ofReal, inner_self_eq_norm_sq_to_K (𝕜 := ℂ), hu i]
    push_cast
    ring
  rw [Finset.sum_congr rfl fun i _ => hterm i, ← Complex.ofReal_sum, hc,
    Complex.ofReal_one]

/-! ## §5. The PREPARE invariant states and gate evolutions -/

/-- Ancilla cell `0`. -/
def a0 : AncL x := ⟨0, NT_pos x hx⟩

theorem jA_ne_jB_fin (j : Fin (NT x - 1)) : jA x j ≠ jB x j := by
  intro hc
  have h2 : ((j : ℕ) : ℕ) = (j : ℕ) + 1 := congrArg Fin.val hc
  omega

/-- The chain coefficient profile after `k` Givens steps: the first `k`
amplitudes are planted, the remaining mass sits on cell `k`. -/
noncomputable def prepC (σ : ST) (k : ℕ) (i : AncL x) : ℝ :=
  if (i : ℕ) < k then am x hx σ i else if (i : ℕ) = k then tl x hx σ k else 0

/-- The chain state after `k` Givens steps, over an arbitrary system vector. -/
noncomputable def prepSt (w : HS (QubitCells (SysL x)) (univ : Finset (SysL x)))
    (σ : ST) (k : ℕ) : HS (QubitCells (WL x)) (univ : Finset (WL x)) :=
  ∑ i : AncL x, ((prepC x hx σ k i : ℝ) : ℂ) • ancEmbed (L₁ := SysL x) (oneHot x i) w

/-- The fully prepared one-hot superposition. -/
noncomputable def fullSt (w : HS (QubitCells (SysL x)) (univ : Finset (SysL x)))
    (σ : ST) : HS (QubitCells (WL x)) (univ : Finset (WL x)) :=
  ∑ i : AncL x, ((am x hx σ i : ℝ) : ℂ) • ancEmbed (L₁ := SysL x) (oneHot x i) w

theorem prepSt_zero (w : HS (QubitCells (SysL x)) (univ : Finset (SysL x))) (σ : ST) :
    prepSt x hx w σ 0 = ancEmbed (L₁ := SysL x) (oneHot x (a0 x hx)) w := by
  rw [prepSt]
  have hterm : ∀ i : AncL x,
      ((prepC x hx σ 0 i : ℝ) : ℂ) • ancEmbed (L₁ := SysL x) (oneHot x i) w
        = if i = a0 x hx then ancEmbed (L₁ := SysL x) (oneHot x i) w else 0 := by
    intro i
    rw [prepC]
    by_cases h : i = a0 x hx
    · subst h
      rw [if_pos rfl]
      have h0 : ((a0 x hx : AncL x) : ℕ) = 0 := rfl
      rw [if_neg (by omega), if_pos h0, tl_zero]
      norm_num
    · have h2 : (i : ℕ) ≠ 0 := fun hc => h (Fin.ext hc)
      rw [if_neg (by omega), if_neg h2, if_neg h]
      norm_num
  rw [Finset.sum_congr rfl fun i _ => hterm i,
    Finset.sum_ite_eq' univ (a0 x hx) (fun i => ancEmbed (L₁ := SysL x) (oneHot x i) w),
    if_pos (mem_univ _)]

theorem prepSt_full (w : HS (QubitCells (SysL x)) (univ : Finset (SysL x))) (σ : ST) :
    prepSt x hx w σ (NT x - 1) = fullSt x hx w σ := by
  rw [prepSt, fullSt]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [prepC]
  by_cases h1 : (i : ℕ) < NT x - 1
  · rw [if_pos h1]
  · have h2 : (i : ℕ) = NT x - 1 := by have := i.isLt; omega
    rw [if_neg h1, if_pos h2]
    have hlt : NT x - 1 < NT x := by have := i.isLt; omega
    have h4 : (⟨NT x - 1, hlt⟩ : Fin (NT x)) = i := by
      apply Fin.ext
      simp [h2]
    rw [← h4, tl_last x hx σ hlt]

/-- The `X` gate plants the flag: `∣0…0⟩ ↦ ∣e₀⟩` on the ancilla block. -/
theorem xGate_emb (w : HS (QubitCells (SysL x)) (univ : Finset (SysL x))) :
    regLift (Reg.single (aC x (a0 x hx)))
        ((singleGate (QubitCells (WL x)) (aC x (a0 x hx)) X :
          UnitaryOp (TSpace (QubitCells (WL x)) (Reg.single (aC x (a0 x hx))).toFun)) :
          TSpace (QubitCells (WL x)) (Reg.single (aC x (a0 x hx))).toFun →ₗ[ℂ] _)
        (ancEmbed (L₁ := SysL x) (anc0 x) w)
      = ancEmbed (L₁ := SysL x) (oneHot x (a0 x hx)) w := by
  have hU : (X : 𝕢 →ₗ[ℂ] 𝕢) (EuclideanSpace.single (anc0 x (a0 x hx)) 1)
      = (1 : ℂ) • EuclideanSpace.single true 1 := by
    rw [one_smul]
    exact X_q0
  have h := gateAt_inr_ancEmbed (L₁ := SysL x) (a0 x hx) X (anc0 x) hU w
  rw [one_smul] at h
  have hupd : Function.update (anc0 x) (a0 x hx) true = oneHot x (a0 x hx) := by
    funext a
    by_cases ha : a = a0 x hx
    · subst ha
      rw [Function.update_self, oneHot_self]
    · rw [Function.update_of_ne ha, oneHot_ne x ha]
      rfl
  rw [hupd] at h
  exact h

/-- The two-update collapse: writing the resting pattern back. -/
theorem upd_at_self (j : Fin (NT x - 1)) :
    Function.update (Function.update (oneHot x (jA x j)) (jA x j) true) (jB x j) false
      = oneHot x (jA x j) := by
  funext a
  rcases eq_or_ne a (jB x j) with rfl | h1
  · rw [Function.update_self, oneHot_ne x (Ne.symm (jA_ne_jB_fin x j))]
  · rw [Function.update_of_ne h1]
    rcases eq_or_ne a (jA x j) with rfl | h2
    · rw [Function.update_self, oneHot_self]
    · rw [Function.update_of_ne h2]

/-- The two-update collapse: moving the flag one cell down. -/
theorem upd_at_shift (j : Fin (NT x - 1)) :
    Function.update (Function.update (oneHot x (jA x j)) (jA x j) false) (jB x j) true
      = oneHot x (jB x j) := by
  funext a
  rcases eq_or_ne a (jB x j) with rfl | h1
  · rw [Function.update_self, oneHot_self]
  · rw [Function.update_of_ne h1, oneHot_ne x h1]
    rcases eq_or_ne a (jA x j) with rfl | h2
    · rw [Function.update_self]
    · rw [Function.update_of_ne h2, oneHot_ne x h2]

/-- The two-update collapse on an untouched pattern. -/
theorem upd_off (j : Fin (NT x - 1)) (i : AncL x) (hiA : i ≠ jA x j)
    (hiB : i ≠ jB x j) :
    Function.update (Function.update (oneHot x i) (jA x j) false) (jB x j) false
      = oneHot x i := by
  funext a
  rcases eq_or_ne a (jB x j) with rfl | h1
  · rw [Function.update_self, oneHot_ne x (Ne.symm hiB)]
  · rw [Function.update_of_ne h1]
    rcases eq_or_ne a (jA x j) with rfl | h2
    · rw [Function.update_self, oneHot_ne x (Ne.symm hiA)]
    · rw [Function.update_of_ne h2]

/-- A Givens step fixes every branch whose flag is away from its two cells. -/
theorem prep_gate_off (θ : ℝ) (j : Fin (NT x - 1)) (i : AncL x)
    (hiA : i ≠ jA x j) (hiB : i ≠ jB x j)
    (w : HS (QubitCells (SysL x)) (univ : Finset (SysL x))) :
    regLift (prepReg x j)
        ((pairGate (D := QubitCells (WL x)) (aC x (jA x j)) (aC x (jB x j))
          (jA_ne_jB x j) (givens θ)) :
          TSpace (QubitCells (WL x)) (prepReg x j).toFun →ₗ[ℂ] _)
        (ancEmbed (L₁ := SysL x) (oneHot x i) w)
      = ancEmbed (L₁ := SysL x) (oneHot x i) w := by
  have hbc : oneHot x i (jA x j) = false := oneHot_ne x (Ne.symm hiA)
  have hbd : oneHot x i (jB x j) = false := oneHot_ne x (Ne.symm hiB)
  have hG : (givens θ : EuclideanSpace ℂ (Bool × Bool) →ₗ[ℂ] EuclideanSpace ℂ (Bool × Bool))
      (vpair (qbit (oneHot x i (jA x j))) (qbit (oneHot x i (jB x j))))
      = ∑ q ∈ ({(false, false)} : Finset (Bool × Bool)),
          (1 : ℂ) • vpair (qbit (id q).1) (qbit (id q).2) := by
    rw [hbc, hbd, Finset.sum_singleton, one_smul]
    exact givens_vpair_00 θ
  have h := pairGate_anc_ancEmbed (L₁ := SysL x) (jA x j) (jB x j) (jA_ne_jB x j)
    (givens θ) (oneHot x i) ({(false, false)} : Finset (Bool × Bool))
    (fun _ => (1 : ℂ)) id hG w
  rw [Finset.sum_singleton, one_smul] at h
  rw [show Function.update (Function.update (oneHot x i) (jA x j)
      ((id ((false : Bool), (false : Bool))).1)) (jB x j) ((id ((false : Bool), (false : Bool))).2)
      = oneHot x i from upd_off x j i hiA hiB] at h
  exact h

/-- **The Givens step on the flag branch**: amplitude moves one cell down. -/
theorem prep_gate_at (θ : ℝ) (j : Fin (NT x - 1))
    (w : HS (QubitCells (SysL x)) (univ : Finset (SysL x))) :
    regLift (prepReg x j)
        ((pairGate (D := QubitCells (WL x)) (aC x (jA x j)) (aC x (jB x j))
          (jA_ne_jB x j) (givens θ)) :
          TSpace (QubitCells (WL x)) (prepReg x j).toFun →ₗ[ℂ] _)
        (ancEmbed (L₁ := SysL x) (oneHot x (jA x j)) w)
      = (Real.cos θ : ℂ) • ancEmbed (L₁ := SysL x) (oneHot x (jA x j)) w
        + (Real.sin θ : ℂ) • ancEmbed (L₁ := SysL x) (oneHot x (jB x j)) w := by
  have hbc : oneHot x (jA x j) (jA x j) = true := oneHot_self x _
  have hbd : oneHot x (jA x j) (jB x j) = false :=
    oneHot_ne x (Ne.symm (jA_ne_jB_fin x j))
  have hpair_ne : ((true, false) : Bool × Bool) ≠ (false, true) := by decide
  have hG : (givens θ : EuclideanSpace ℂ (Bool × Bool) →ₗ[ℂ] EuclideanSpace ℂ (Bool × Bool))
      (vpair (qbit (oneHot x (jA x j) (jA x j))) (qbit (oneHot x (jA x j) (jB x j))))
      = ∑ q ∈ ({(true, false), (false, true)} : Finset (Bool × Bool)),
          (if q.1 then (Real.cos θ : ℂ) else (Real.sin θ : ℂ)) •
            vpair (qbit (id q).1) (qbit (id q).2) := by
    rw [hbc, hbd, Finset.sum_pair hpair_ne]
    simp only [id_eq, if_true, if_false, Bool.false_eq_true]
    exact givens_vpair_10 θ
  have h := pairGate_anc_ancEmbed (L₁ := SysL x) (jA x j) (jB x j) (jA_ne_jB x j)
    (givens θ) (oneHot x (jA x j)) ({(true, false), (false, true)} : Finset (Bool × Bool))
    (fun q => if q.1 then (Real.cos θ : ℂ) else (Real.sin θ : ℂ)) id hG w
  rw [Finset.sum_pair hpair_ne] at h
  simp only [id_eq, if_true, if_false, Bool.false_eq_true] at h
  rw [show Function.update (Function.update (oneHot x (jA x j)) (jA x j) true)
        (jB x j) false = oneHot x (jA x j) from upd_at_self x j,
    show Function.update (Function.update (oneHot x (jA x j)) (jA x j) false)
        (jB x j) true = oneHot x (jB x j) from upd_at_shift x j] at h
  exact h

theorem prepC_off (σ : ST) (j : Fin (NT x - 1)) (i : AncL x)
    (hiA : i ≠ jA x j) (hiB : i ≠ jB x j) :
    prepC x hx σ ((j : ℕ) + 1) i = prepC x hx σ (j : ℕ) i := by
  have h1 : (i : ℕ) ≠ (j : ℕ) := fun hc => hiA (Fin.ext hc)
  have h2 : (i : ℕ) ≠ (j : ℕ) + 1 := fun hc => hiB (Fin.ext hc)
  rw [prepC, prepC]
  by_cases h3 : (i : ℕ) < (j : ℕ)
  · rw [if_pos h3, if_pos (by omega)]
  · rw [if_neg h3, if_neg (by omega), if_neg h1, if_neg h2]

/-- **One PREPARE step**: the Givens gate advances the chain profile. -/
theorem prep_step (σ : ST) (w : HS (QubitCells (SysL x)) (univ : Finset (SysL x)))
    (j : Fin (NT x - 1)) :
    regLift (prepReg x j)
        ((pairGate (D := QubitCells (WL x)) (aC x (jA x j)) (aC x (jB x j))
          (jA_ne_jB x j) (givens (ang x hx σ (j : ℕ) (jA_lt x j)))) :
          TSpace (QubitCells (WL x)) (prepReg x j).toFun →ₗ[ℂ] _)
        (prepSt x hx w σ (j : ℕ))
      = prepSt x hx w σ ((j : ℕ) + 1) := by
  rw [prepSt, prepSt, map_sum]
  refine sum_eq_of_eq_off_pair x (jA x j) (jB x j) (jA_ne_jB_fin x j) _ _ ?_ ?_
  · intro i hiA hiB
    rw [map_smul, prep_gate_off x (ang x hx σ (j : ℕ) (jA_lt x j)) j i hiA hiB w,
      prepC_off x hx σ j i hiA hiB]
  · have hcA : prepC x hx σ (j : ℕ) (jA x j) = tl x hx σ (j : ℕ) := by
      rw [prepC]
      have h1 : ((jA x j : AncL x) : ℕ) = (j : ℕ) := rfl
      rw [h1, if_neg (by omega), if_pos rfl]
    have hcB : prepC x hx σ (j : ℕ) (jB x j) = 0 := by
      rw [prepC]
      have h1 : ((jB x j : AncL x) : ℕ) = (j : ℕ) + 1 := rfl
      rw [h1, if_neg (by omega), if_neg (by omega)]
    have hcA' : prepC x hx σ ((j : ℕ) + 1) (jA x j) = am x hx σ (jA x j) := by
      rw [prepC]
      have h1 : ((jA x j : AncL x) : ℕ) = (j : ℕ) := rfl
      rw [h1, if_pos (by omega)]
    have hcB' : prepC x hx σ ((j : ℕ) + 1) (jB x j) = tl x hx σ ((j : ℕ) + 1) := by
      rw [prepC]
      have h1 : ((jB x j : AncL x) : ℕ) = (j : ℕ) + 1 := rfl
      rw [h1, if_neg (by omega), if_pos rfl]
    rw [map_smul, map_smul, prep_gate_at x _ j w, hcA, hcB, hcA', hcB']
    rw [smul_add, smul_smul, smul_smul, Complex.ofReal_zero, zero_smul, add_zero]
    rw [show ((tl x hx σ (j : ℕ) : ℝ) : ℂ)
          * ((Real.cos (ang x hx σ (j : ℕ) (jA_lt x j)) : ℝ) : ℂ)
        = ((am x hx σ (jA x j) : ℝ) : ℂ) from by
      rw [← Complex.ofReal_mul, mul_comm]
      norm_cast
      exact cos_ang_mul x hx σ (j : ℕ) (jA_lt x j)]
    rw [show ((tl x hx σ (j : ℕ) : ℝ) : ℂ)
          * ((Real.sin (ang x hx σ (j : ℕ) (jA_lt x j)) : ℝ) : ℂ)
        = ((tl x hx σ ((j : ℕ) + 1) : ℝ) : ℂ) from by
      rw [← Complex.ofReal_mul, mul_comm]
      norm_cast
      exact sin_ang_mul x hx σ (j : ℕ) (jA_lt x j)]

/-- `prep_step` at a decoupled `ℕ` chain position: the reading the counted
loop consumes (the position is the stored counter, the register the `jCell`
conversion of it). -/
theorem prep_step' (σ : ST) (w : HS (QubitCells (SysL x)) (univ : Finset (SysL x)))
    (j : Fin (NT x - 1)) (k : ℕ) (hjk : (j : ℕ) = k) :
    regLift (prepReg x j)
        ((pairGate (D := QubitCells (WL x)) (aC x (jA x j)) (aC x (jB x j))
          (jA_ne_jB x j) (givens (ang x hx σ (j : ℕ) (jA_lt x j)))) :
          TSpace (QubitCells (WL x)) (prepReg x j).toFun →ₗ[ℂ] _)
        (prepSt x hx w σ k)
      = prepSt x hx w σ (k + 1) := by
  subst hjk
  exact prep_step x hx σ w j

/-- The PREPARE chain evaluated: the semantic operator of the Givens chain
carries `∣e₀⟩ ⊗ w` to the full one-hot superposition. -/
theorem prep_chain (σ : ST) (w : HS (QubitCells (SysL x)) (univ : Finset (SysL x))) :
    chainOp (List.finRange (NT x - 1))
        (fun j => regLift (prepReg x j)
          ((pairGate (D := QubitCells (WL x)) (aC x (jA x j)) (aC x (jB x j))
            (jA_ne_jB x j) (givens (ang x hx σ (j : ℕ) (jA_lt x j)))) :
            TSpace (QubitCells (WL x)) (prepReg x j).toFun →ₗ[ℂ] _))
        (prepSt x hx w σ 0)
      = prepSt x hx w σ (NT x - 1) :=
  chainOp_finRange_family _ (fun k => prepSt x hx w σ k)
    (fun j => prep_step x hx σ w j)

/-! ## §6. The SELECT invariant states and gate evolutions -/

/-- The branch operator after `l` full rungs: the first `l` branches carry
their signed Pauli strings. -/
noncomputable def selW (σ : ST) (l : ℕ) (i : AncL x) :
    EndM (QubitCells (SysL x)) (univ : Finset (SysL x)) :=
  if (i : ℕ) < l then ((sg x σ i : ℝ) : ℂ) • pauliString (str x i) else 1

/-- The SELECT invariant state after `l` full rungs. -/
noncomputable def selSt (w : HS (QubitCells (SysL x)) (univ : Finset (SysL x)))
    (σ : ST) (l : ℕ) : HS (QubitCells (WL x)) (univ : Finset (WL x)) :=
  ∑ i : AncL x, ((am x hx σ i : ℝ) : ℂ) •
    ancEmbed (L₁ := SysL x) (oneHot x i) (selW x σ l i w)

/-- The branch operator inside rung `l`, after the sign gate and `m` letter
gates. -/
noncomputable def selMidW (σ : ST) (l : AncL x) (m : ℕ) (i : AncL x) :
    EndM (QubitCells (SysL x)) (univ : Finset (SysL x)) :=
  if (i : ℕ) < (l : ℕ) then ((sg x σ i : ℝ) : ℂ) • pauliString (str x i)
  else if i = l then ((sg x σ l : ℝ) : ℂ) • stringTake (str x l) m
  else 1

/-- The mid-rung invariant state. -/
noncomputable def selMid (w : HS (QubitCells (SysL x)) (univ : Finset (SysL x)))
    (σ : ST) (l : AncL x) (m : ℕ) : HS (QubitCells (WL x)) (univ : Finset (WL x)) :=
  ∑ i : AncL x, ((am x hx σ i : ℝ) : ℂ) •
    ancEmbed (L₁ := SysL x) (oneHot x i) (selMidW x σ l m i w)

theorem selSt_zero (w : HS (QubitCells (SysL x)) (univ : Finset (SysL x))) (σ : ST) :
    selSt x hx w σ 0 = fullSt x hx w σ := by
  rw [selSt, fullSt]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [selW, if_neg (by omega), Module.End.one_apply]

/-- **The sign-gate step of rung `l`.** -/
theorem sgn_step (σ : ST) (l : AncL x)
    (w : HS (QubitCells (SysL x)) (univ : Finset (SysL x))) :
    regLift (Reg.single (aC x l))
        ((singleGate (QubitCells (WL x)) (aC x l) (sgnGate (cf x σ l)) :
          UnitaryOp (TSpace (QubitCells (WL x)) (Reg.single (aC x l)).toFun)) :
          TSpace (QubitCells (WL x)) (Reg.single (aC x l)).toFun →ₗ[ℂ] _)
        (selSt x hx w σ (l : ℕ))
      = selMid x hx w σ l 0 := by
  rw [selSt, selMid, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]
  refine congrArg (_ • ·) ?_
  have hU : (sgnGate (cf x σ l) : 𝕢 →ₗ[ℂ] 𝕢)
      (EuclideanSpace.single (oneHot x i l) 1)
      = (if oneHot x i l then (if cf x σ l < 0 then (-1 : ℂ) else 1) else 1) •
          EuclideanSpace.single (oneHot x i l) 1 := sgnGate_single _ _
  have h := gateAt_inr_ancEmbed (L₁ := SysL x) l (sgnGate (cf x σ l)) (oneHot x i) hU
    (selW x σ (l : ℕ) i w)
  rw [Function.update_eq_self] at h
  refine h.trans ?_
  by_cases hil : i = l
  · subst hil
    have hW1 : selW x σ (i : ℕ) i w = w := by
      rw [selW, if_neg (lt_irrefl _), Module.End.one_apply]
    have hW2 : selMidW x σ i 0 i w = ((sg x σ i : ℝ) : ℂ) • w := by
      rw [selMidW, if_neg (lt_irrefl _), if_pos rfl, stringTake_zero,
        LinearMap.smul_apply, Module.End.one_apply]
    rw [hW1, hW2, map_smul, oneHot_self]
    congr 1
    rw [if_pos rfl, sg]
    split_ifs <;> norm_num
  · rw [oneHot_ne x (Ne.symm hil), if_neg Bool.false_ne_true, one_smul]
    refine congrArg _ ?_
    rw [selMidW, selW]
    by_cases h2 : (i : ℕ) < (l : ℕ)
    · rw [if_pos h2, if_pos h2]
    · rw [if_neg h2, if_neg h2, if_neg hil]

/-- `sgn_step` at a decoupled `ℕ` rung position — the reading the counted
loop consumes. -/
theorem sgn_step' (σ : ST) (w : HS (QubitCells (SysL x)) (univ : Finset (SysL x)))
    (l : AncL x) (k : ℕ) (hlk : (l : ℕ) = k) :
    regLift (Reg.single (aC x l))
        ((singleGate (QubitCells (WL x)) (aC x l) (sgnGate (cf x σ l)) :
          UnitaryOp (TSpace (QubitCells (WL x)) (Reg.single (aC x l)).toFun)) :
          TSpace (QubitCells (WL x)) (Reg.single (aC x l)).toFun →ₗ[ℂ] _)
        (selSt x hx w σ k)
      = selMid x hx w σ l 0 := by
  subst hlk
  exact sgn_step x hx σ l w

/-- **One controlled-letter step of rung `l`.** -/
theorem ctrl_step (σ : ST) (l : AncL x) (m : ℕ) (hm : m < 2 ^ x)
    (w : HS (QubitCells (SysL x)) (univ : Finset (SysL x))) :
    regLift (ctrlReg x l ⟨m, hm⟩)
        ((pairGate (D := QubitCells (WL x)) (aC x l) (sC x ⟨m, hm⟩) Sum.inr_ne_inl
          (control (str x l ⟨m, hm⟩).gate)) :
          TSpace (QubitCells (WL x)) (ctrlReg x l ⟨m, hm⟩).toFun →ₗ[ℂ] _)
        (selMid x hx w σ l m)
      = selMid x hx w σ l (m + 1) := by
  rw [selMid, selMid, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]
  refine congrArg (_ • ·) ?_
  have h := pairGate_ctrl_ancEmbed (L₁ := SysL x) l ⟨m, hm⟩ (str x l ⟨m, hm⟩).gate
    (oneHot x i) (selMidW x σ l m i w)
  refine h.trans ?_
  by_cases hil : i = l
  · subst hil
    rw [oneHot_self, if_pos rfl]
    refine congrArg _ ?_
    have hW1 : selMidW x σ i m i w = ((sg x σ i : ℝ) : ℂ) • stringTake (str x i) m w := by
      rw [selMidW, if_neg (lt_irrefl _), if_pos rfl, LinearMap.smul_apply]
    have hW2 : selMidW x σ i (m + 1) i w
        = ((sg x σ i : ℝ) : ℂ) • stringTake (str x i) (m + 1) w := by
      rw [selMidW, if_neg (lt_irrefl _), if_pos rfl, LinearMap.smul_apply]
    rw [hW1, hW2, map_smul]
    refine congrArg (_ • ·) ?_
    rw [stringTake_succ (str x i) m hm, LinearMap.comp_apply]
  · rw [oneHot_ne x (Ne.symm hil), if_neg Bool.false_ne_true]
    refine congrArg _ ?_
    rw [selMidW, selMidW]
    by_cases h2 : (i : ℕ) < (l : ℕ)
    · rw [if_pos h2, if_pos h2]
    · rw [if_neg h2, if_neg h2, if_neg hil, if_neg hil]

/-- `ctrl_step` at a decoupled `ℕ` letter position — the reading the counted
loop consumes (the site is the `sCell` conversion of the inner counter). -/
theorem ctrl_step' (σ : ST) (w : HS (QubitCells (SysL x)) (univ : Finset (SysL x)))
    (l : AncL x) (s : SysL x) (m : ℕ) (hsm : (s : ℕ) = m) :
    regLift (ctrlReg x l s)
        ((pairGate (D := QubitCells (WL x)) (aC x l) (sC x s) Sum.inr_ne_inl
          (control (str x l s).gate)) :
          TSpace (QubitCells (WL x)) (ctrlReg x l s).toFun →ₗ[ℂ] _)
        (selMid x hx w σ l m)
      = selMid x hx w σ l (m + 1) := by
  subst hsm
  have h := ctrl_step x hx σ l (s : ℕ) s.isLt w
  rw [show (⟨(s : ℕ), s.isLt⟩ : SysL x) = s from Fin.ext rfl] at h
  exact h

/-- The letter chain of rung `l` evaluated. -/
theorem rung_chain (σ : ST) (l : AncL x)
    (w : HS (QubitCells (SysL x)) (univ : Finset (SysL x))) :
    chainOp (List.finRange (2 ^ x))
        (fun s => regLift (ctrlReg x l s)
          ((pairGate (D := QubitCells (WL x)) (aC x l) (sC x s) Sum.inr_ne_inl
            (control (str x l s).gate)) :
            TSpace (QubitCells (WL x)) (ctrlReg x l s).toFun →ₗ[ℂ] _))
        (selMid x hx w σ l 0)
      = selMid x hx w σ l (2 ^ x) := by
  refine chainOp_finRange_family _ (fun m => selMid x hx w σ l m) ?_
  intro s
  have h := ctrl_step x hx σ l (s : ℕ) s.isLt w
  rw [show (⟨(s : ℕ), s.isLt⟩ : SysL x) = s from Fin.ext rfl] at h
  exact h

/-- The rung exit: the full letter chain completes the signed string. -/
theorem selMid_top (σ : ST) (l : AncL x)
    (w : HS (QubitCells (SysL x)) (univ : Finset (SysL x))) :
    selMid x hx w σ l (2 ^ x) = selSt x hx w σ ((l : ℕ) + 1) := by
  rw [selMid, selSt]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine congrArg (_ • ·) ?_
  refine congrArg _ ?_
  rw [selMidW, selW]
  by_cases h2 : (i : ℕ) < (l : ℕ)
  · rw [if_pos h2, if_pos (Nat.lt_succ_of_lt h2)]
  · by_cases hil : i = l
    · subst hil
      rw [if_neg h2, if_pos rfl, if_pos (Nat.lt_succ_self _), stringTake_top]
    · have h3 : ¬ (i : ℕ) < (l : ℕ) + 1 := by
        have : (i : ℕ) ≠ (l : ℕ) := fun hc => hil (Fin.ext hc)
        omega
      rw [if_neg h2, if_neg hil, if_neg h3]

/-- The SELECT exit state, in closed form: every branch carries its signed
Pauli string — the right-hand side of the paper's `Sel` stage-action display,
summed over the prepared branches. -/
theorem selSt_top (σ : ST) (w : HS (QubitCells (SysL x)) (univ : Finset (SysL x))) :
    selSt x hx w σ (NT x)
      = ∑ i : AncL x, ((am x hx σ i : ℝ) : ℂ) •
          ancEmbed (L₁ := SysL x) (oneHot x i)
            (((sg x σ i : ℝ) : ℂ) • pauliString (str x i) w) := by
  rw [selSt]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [selW, if_pos i.isLt, LinearMap.smul_apply]

/-- **The SELECT stage action** — the paper's `Sel` display, the counterpart of
`prep_chain`: the ordered composite of every gate the SELECT stage applies
(rung `l`: the sign gate on ancilla `l`, then its `2^x` controlled letter
gates, in program order) carries each prepared one-hot branch to its signed
Pauli string, `∣1_l⟩ ⊗ w ↦ ∣1_l⟩ ⊗ sg_l·P_l w` — read on the prepared
superposition, whose branches ride through the rungs of the other terms
untouched. Composed from the rung-level facts `sgn_step`, `rung_chain` and
`selMid_top` along the invariant `selSt`. -/
theorem sel_chain (σ : ST) (w : HS (QubitCells (SysL x)) (univ : Finset (SysL x))) :
    chainOp (List.finRange (NT x))
        (fun l =>
          chainOp (List.finRange (2 ^ x))
              (fun s => regLift (ctrlReg x l s)
                ((pairGate (D := QubitCells (WL x)) (aC x l) (sC x s) Sum.inr_ne_inl
                  (control (str x l s).gate)) :
                  TSpace (QubitCells (WL x)) (ctrlReg x l s).toFun →ₗ[ℂ] _))
            ∘ₗ regLift (Reg.single (aC x l))
              ((singleGate (QubitCells (WL x)) (aC x l) (sgnGate (cf x σ l)) :
                UnitaryOp (TSpace (QubitCells (WL x)) (Reg.single (aC x l)).toFun)) :
                TSpace (QubitCells (WL x)) (Reg.single (aC x l)).toFun →ₗ[ℂ] _))
        (fullSt x hx w σ)
      = ∑ i : AncL x, ((am x hx σ i : ℝ) : ℂ) •
          ancEmbed (L₁ := SysL x) (oneHot x i)
            (((sg x σ i : ℝ) : ℂ) • pauliString (str x i) w) := by
  have h := chainOp_finRange_family
    (fun l : Fin (NT x) =>
      chainOp (List.finRange (2 ^ x))
          (fun s => regLift (ctrlReg x l s)
            ((pairGate (D := QubitCells (WL x)) (aC x l) (sC x s) Sum.inr_ne_inl
              (control (str x l s).gate)) :
              TSpace (QubitCells (WL x)) (ctrlReg x l s).toFun →ₗ[ℂ] _))
        ∘ₗ regLift (Reg.single (aC x l))
          ((singleGate (QubitCells (WL x)) (aC x l) (sgnGate (cf x σ l)) :
            UnitaryOp (TSpace (QubitCells (WL x)) (Reg.single (aC x l)).toFun)) :
            TSpace (QubitCells (WL x)) (Reg.single (aC x l)).toFun →ₗ[ℂ] _))
    (fun m => selSt x hx w σ m)
    (fun l => by
      rw [LinearMap.comp_apply, sgn_step x hx σ l w, rung_chain x hx σ l w,
        selMid_top x hx σ l w])
  rw [selSt_zero x hx w σ] at h
  rw [h, selSt_top x hx σ w]

/-! ## §7. Norms, the assertion families, and the derivation -/

/-- Pure-state assertion families on equal state families entail each
other (generic in the store, so it serves the widened store too). -/
theorem ofStateFam_le {σT' : Type*}
    {v w : σT' → HS (QubitCells (WL x)) (univ : Finset (WL x))}
    {hv : ∀ σ, ‖v σ‖ = 1} {hw : ∀ σ, ‖w σ‖ = 1} (h : ∀ σ, v σ = w σ) :
    Assn.ofStateFam (σT := σT') v hv ≤ Assn.ofStateFam w hw := fun σ =>
  le_of_eq (by rw [Assn.ofStateFam_op, Assn.ofStateFam_op, h σ])

theorem sum_prepC_sq_lt (σ : ST) (k : ℕ) (hk : k < NT x) :
    ∑ i : AncL x, prepC x hx σ k i ^ 2 = 1 := by
  have hsplit : ∀ i : AncL x, prepC x hx σ k i ^ 2
      = (if (i : ℕ) < k then am x hx σ i ^ 2 else 0)
        + (if i = ⟨k, hk⟩ then tl x hx σ k ^ 2 else 0) := by
    intro i
    rw [prepC]
    by_cases h1 : (i : ℕ) < k
    · rw [if_pos h1, if_pos h1,
        if_neg (show i ≠ ⟨k, hk⟩ from fun hc => by
          rw [hc] at h1
          exact lt_irrefl k h1), add_zero]
    · rw [if_neg h1]
      by_cases h2 : (i : ℕ) = k
      · rw [if_pos h2, if_neg h1, if_pos (Fin.ext h2), zero_add]
      · rw [if_neg h2, if_neg h1,
          if_neg (show i ≠ ⟨k, hk⟩ from fun hc => h2 (congrArg Fin.val hc)), add_zero]
        norm_num
  rw [Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_add_distrib,
    Finset.sum_ite_eq' univ (⟨k, hk⟩ : Fin (NT x)), if_pos (mem_univ _)]
  have htl : tl x hx σ k ^ 2
      = ∑ i : AncL x, if k ≤ (i : ℕ) then am x hx σ i ^ 2 else 0 :=
    Real.sq_sqrt (tl_sum_nonneg x hx σ k)
  rw [htl, ← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (g := fun i => am x hx σ i ^ 2) fun i _ => by
    by_cases h : (i : ℕ) < k
    · rw [if_pos h, if_neg (show ¬ k ≤ (i : ℕ) by omega), add_zero]
    · rw [if_neg h, if_pos (show k ≤ (i : ℕ) by omega), zero_add]]
  exact sum_am_sq x hx σ

/-- The chain profile is a unit profile at **every** position (above the top
position it has stabilized at the amplitude profile) — the totality the
counted-loop invariant family needs. -/
theorem sum_prepC_sq (σ : ST) (k : ℕ) :
    ∑ i : AncL x, prepC x hx σ k i ^ 2 = 1 := by
  by_cases hk : k < NT x
  · exact sum_prepC_sq_lt x hx σ k hk
  · rw [Finset.sum_congr rfl (g := fun i => am x hx σ i ^ 2) fun i _ => by
      rw [prepC, if_pos (by have := i.isLt; omega)]]
    exact sum_am_sq x hx σ

variable (ψ : HS (QubitCells (SysL x)) (univ : Finset (SysL x)))

theorem norm_prepSt (hψ : ‖ψ‖ = 1) (σ : ST) (k : ℕ) :
    ‖prepSt x hx ψ σ k‖ = 1 :=
  norm_sum_emb x (prepC x hx σ k) (fun _ => ψ) (fun _ => hψ) (sum_prepC_sq x hx σ k)

theorem norm_sg_smul (σ : ST) (i : AncL x)
    (u : HS (QubitCells (SysL x)) (univ : Finset (SysL x))) (hu : ‖u‖ = 1) :
    ‖((sg x σ i : ℝ) : ℂ) • u‖ = 1 := by
  rw [norm_smul, Complex.norm_real, hu, mul_one, Real.norm_eq_abs, sg]
  split_ifs <;> norm_num

theorem norm_selW (hψ : ‖ψ‖ = 1) (σ : ST) (l : ℕ) (i : AncL x) : ‖selW x σ l i ψ‖ = 1 := by
  rw [selW]
  split_ifs with h
  · rw [LinearMap.smul_apply]
    exact norm_sg_smul x σ i _
      (norm_eq_one_of_isUnitary (isUnitary_pauliString _) hψ)
  · rw [Module.End.one_apply]
    exact hψ

theorem norm_selMidW (hψ : ‖ψ‖ = 1) (σ : ST) (l : AncL x) (m : ℕ) (i : AncL x) :
    ‖selMidW x σ l m i ψ‖ = 1 := by
  rw [selMidW]
  split_ifs with h1 h2
  · rw [LinearMap.smul_apply]
    exact norm_sg_smul x σ i _
      (norm_eq_one_of_isUnitary (isUnitary_pauliString _) hψ)
  · rw [LinearMap.smul_apply]
    exact norm_sg_smul x σ l _
      (norm_eq_one_of_isUnitary (isUnitary_stringOn _ _) hψ)
  · rw [Module.End.one_apply]
    exact hψ

theorem norm_selSt (hψ : ‖ψ‖ = 1) (σ : ST) (l : ℕ) : ‖selSt x hx ψ σ l‖ = 1 :=
  norm_sum_emb x (am x hx σ) (fun i => selW x σ l i ψ)
    (fun i => norm_selW x ψ hψ σ l i) (sum_am_sq x hx σ)

theorem norm_selMid (hψ : ‖ψ‖ = 1) (σ : ST) (l : AncL x) (m : ℕ) :
    ‖selMid x hx ψ σ l m‖ = 1 :=
  norm_sum_emb x (am x hx σ) (fun i => selMidW x σ l m i ψ)
    (fun i => norm_selMidW x ψ hψ σ l m i) (sum_am_sq x hx σ)

theorem norm_fullSt (hψ : ‖ψ‖ = 1) (σ : ST) : ‖fullSt x hx ψ σ‖ = 1 :=
  norm_sum_emb x (am x hx σ) (fun _ => ψ) (fun _ => hψ) (sum_am_sq x hx σ)

theorem norm_inS (hψ : ‖ψ‖ = 1) : ‖ancEmbed (L₁ := SysL x) (anc0 x) ψ‖ = 1 := by
  rw [norm_ancEmbed]
  exact hψ

/-- The un-preparation chain operator. -/
noncomputable def unprepChain (σ : ST) : EndM (QubitCells (WL x)) (univ : Finset (WL x)) :=
  chainOp ((List.finRange (NT x - 1)).reverse)
    (fun j => regLift (prepReg x j)
      ((pairGate (D := QubitCells (WL x)) (aC x (jA x j)) (aC x (jB x j))
        (jA_ne_jB x j) (givens (-(ang x hx σ (j : ℕ) (jA_lt x j))))) :
        TSpace (QubitCells (WL x)) (prepReg x j).toFun →ₗ[ℂ] _))

/-- The lifted `X` on ancilla cell `0`. -/
noncomputable def xLift : EndM (QubitCells (WL x)) (univ : Finset (WL x)) :=
  regLift (Reg.single (aC x (a0 x hx)))
    ((singleGate (QubitCells (WL x)) (aC x (a0 x hx)) X :
      UnitaryOp (TSpace (QubitCells (WL x)) (Reg.single (aC x (a0 x hx))).toFun)) :
      TSpace (QubitCells (WL x)) (Reg.single (aC x (a0 x hx))).toFun →ₗ[ℂ] _)

/-- **The named output state** of the block-encoding program. -/
noncomputable def outSt (σ : ST) : HS (QubitCells (WL x)) (univ : Finset (WL x)) :=
  xLift x hx (unprepChain x hx σ (selSt x hx ψ σ (NT x)))

theorem isUnitary_unprepChain (σ : ST) : IsUnitary (unprepChain x hx σ) :=
  isUnitary_chainOp _ _ fun _ => isUnitary_regLift _ _

theorem isUnitary_xLift : IsUnitary (xLift x hx) := isUnitary_regLift _ _

theorem norm_outSt (hψ : ‖ψ‖ = 1) (σ : ST) : ‖outSt x hx ψ σ‖ = 1 :=
  norm_eq_one_of_isUnitary (isUnitary_xLift x hx)
    (norm_eq_one_of_isUnitary (isUnitary_unprepChain x hx σ)
      (norm_selSt x hx ψ hψ σ (NT x)))

/-- **The UNPREPARE invariant family**: the prefix of the first `k` inverse
Givens gates (the `chainPre` prefix-chain operator of the reversed gate
list) applied to the post-SELECT state. -/
noncomputable def unprepSt (σ : ST) (k : ℕ) :
    HS (QubitCells (WL x)) (univ : Finset (WL x)) :=
  chainPre ((List.finRange (NT x - 1)).reverse)
    (fun j => regLift (prepReg x j)
      ((pairGate (D := QubitCells (WL x)) (aC x (jA x j)) (aC x (jB x j))
        (jA_ne_jB x j) (givens (-(ang x hx σ (j : ℕ) (jA_lt x j))))) :
        TSpace (QubitCells (WL x)) (prepReg x j).toFun →ₗ[ℂ] _))
    k (selSt x hx ψ σ (NT x))

theorem unprepSt_zero (σ : ST) : unprepSt x hx ψ σ 0 = selSt x hx ψ σ (NT x) := rfl

/-- The full prefix is the whole un-preparation chain. -/
theorem unprepSt_full (σ : ST) :
    unprepSt x hx ψ σ (NT x - 1) = unprepChain x hx σ (selSt x hx ψ σ (NT x)) := by
  have hlen : ((List.finRange (NT x - 1)).reverse).length = NT x - 1 := by
    rw [List.length_reverse, List.length_finRange]
  have h := chainPre_length ((List.finRange (NT x - 1)).reverse)
    (fun j => regLift (prepReg x j)
      ((pairGate (D := QubitCells (WL x)) (aC x (jA x j)) (aC x (jB x j))
        (jA_ne_jB x j) (givens (-(ang x hx σ (j : ℕ) (jA_lt x j))))) :
        TSpace (QubitCells (WL x)) (prepReg x j).toFun →ₗ[ℂ] _))
  rw [hlen] at h
  rw [unprepSt, unprepChain, h]

theorem norm_unprepSt (hψ : ‖ψ‖ = 1) (σ : ST) (k : ℕ) : ‖unprepSt x hx ψ σ k‖ = 1 :=
  norm_eq_one_of_isUnitary
    (isUnitary_chainOp (((List.finRange (NT x - 1)).reverse).take k) _
      fun _ => isUnitary_regLift _ _)
    (norm_selSt x hx ψ hψ σ (NT x))

/-- **One UNPREPARE pass**: the inverse Givens gate at the reversed position
`N - 2 - k` advances the prefix chain (the `k`-th gate of the reversed list
composes on the left of the prefix, `chainPre_succ`). -/
theorem unprep_step (σ : ST) (k : ℕ) (hk : k < NT x - 1) :
    regLift (prepReg x (jCell x hx (NT x - 2 - k)))
        ((pairGate (D := QubitCells (WL x)) (aC x (jA x (jCell x hx (NT x - 2 - k))))
          (aC x (jB x (jCell x hx (NT x - 2 - k)))) (jA_ne_jB x (jCell x hx (NT x - 2 - k)))
          (givens (-(ang x hx σ ((jCell x hx (NT x - 2 - k) : Fin (NT x - 1)) : ℕ)
            (jA_lt x (jCell x hx (NT x - 2 - k))))))) :
          TSpace (QubitCells (WL x)) (prepReg x (jCell x hx (NT x - 2 - k))).toFun →ₗ[ℂ] _)
        (unprepSt x hx ψ σ k)
      = unprepSt x hx ψ σ (k + 1) := by
  have hlen : ((List.finRange (NT x - 1)).reverse).length = NT x - 1 := by
    rw [List.length_reverse, List.length_finRange]
  have hklen : k < ((List.finRange (NT x - 1)).reverse).length := by
    rw [hlen]
    exact hk
  have hj : NT x - 2 - k < NT x - 1 := by
    have := NT_gt_one x hx
    omega
  have hget : ((List.finRange (NT x - 1)).reverse).get ⟨k, hklen⟩
      = jCell x hx (NT x - 2 - k) := by
    rw [jCell_eq_mk x hx hj]
    refine Fin.ext ?_
    rw [List.get_eq_getElem, List.getElem_reverse, List.getElem_finRange]
    simp only [Fin.val_cast, List.length_finRange]
    omega
  rw [unprepSt, unprepSt, chainPre_succ _ _ hklen, hget, LinearMap.comp_apply]

/-! The body-action facts: each loop body's store-read gate, evaluated on the
loop's invariant family where the step mask holds.  The counter equations are
consumed by `subst`, so every fact reduces to the §5/§6 step lemma at the
`Cell` conversion of the stored counter. -/

/-- The PREPARE body acts: one Givens pass advances the chain profile. -/
theorem prepBody_act (σ : STc) (k : ℕ) (hσ1 : σ.1 = k) (hk : k < NT x - 1) :
    ∃ hinj : Function.Injective (prepRegE x hx σ),
      regLift ⟨prepRegE x hx σ, hinj⟩ (prepGateE x hx σ)
        (prepSt x hx ψ (coef σ) k)
      = prepSt x hx ψ (coef σ) (k + 1) := by
  subst hσ1
  exact ⟨(prepReg x (jCell x hx σ.1)).inj,
    prep_step' x hx (coef σ) ψ (jCell x hx σ.1) σ.1 (jCell_val x hx hk)⟩

/-- The sign gate acts: rung `k` opens. -/
theorem sgnBody_act (σ : STc) (k : ℕ) (hσ1 : σ.1 = k) (hk : k < NT x) :
    ∃ hinj : Function.Injective (sgnRegE x hx σ),
      regLift ⟨sgnRegE x hx σ, hinj⟩ (sgnGateE x hx σ)
        (selSt x hx ψ (coef σ) k)
      = selMid x hx ψ (coef σ) (lCell x hx k) 0 := by
  subst hσ1
  exact ⟨(Reg.single (aC x (lCell x hx σ.1))).inj,
    sgn_step' x hx (coef σ) ψ (lCell x hx σ.1) σ.1 (lCell_val x hx hk)⟩

/-- The controlled letter acts: rung `k` advances one letter. -/
theorem ctrlBody_act (σ : STc) (k m : ℕ) (hσ1 : σ.1 = k) (hσ2 : σ.2.1 = m)
    (hm : m < 2 ^ x) :
    ∃ hinj : Function.Injective (ctrlRegE x hx σ),
      regLift ⟨ctrlRegE x hx σ, hinj⟩ (ctrlGateE x hx σ)
        (selMid x hx ψ (coef σ) (lCell x hx k) m)
      = selMid x hx ψ (coef σ) (lCell x hx k) (m + 1) := by
  subst hσ1
  subst hσ2
  exact ⟨(ctrlReg x (lCell x hx σ.1) (sCell x σ.2.1)).inj,
    ctrl_step' x hx (coef σ) ψ (lCell x hx σ.1) (sCell x σ.2.1) σ.2.1 (sCell_val x hm)⟩

/-- The UNPREPARE body acts: one reversed inverse Givens pass advances the
prefix chain. -/
theorem unprepBody_act (σ : STc) (k : ℕ) (hσ1 : σ.1 = k) (hk : k < NT x - 1) :
    ∃ hinj : Function.Injective (unprepRegE x hx σ),
      regLift ⟨unprepRegE x hx σ, hinj⟩ (unprepGateE x hx σ)
        (unprepSt x hx ψ (coef σ) k)
      = unprepSt x hx ψ (coef σ) (k + 1) := by
  subst hσ1
  exact ⟨(prepReg x (jCell x hx (NT x - 2 - σ.1))).inj,
    unprep_step x hx ψ (coef σ) σ.1 hk⟩

/-! The four loops, each ONE packaged counted-chain call
(`DerivTot.countedStateChain`, the inner letter loop through the relativised
`countedStateChain_rel` so its conclusion feeds the outer chain), every step
one masked rung (`DerivTot.countedRung_fam`). -/

/-- The SELECT rung preserves every classical predicate insensitive to the
inner-counter writes, independently of its quantum input. -/
theorem rungIdentity (φ : STc → Prop)
    (hφ : ∀ σ v, φ ((CounterLens.snd3 ST).set σ v) ↔ φ σ) :
    DerivTot ((Assn.one : Assn STc (QubitCells (WL x))).mask φ)
      (rungBody x hx) (Assn.one.mask φ) :=
  DerivTot.seq
    (DerivTot.unitary_identity_mask (sgnRegE x hx) (sgnGateE x hx)
      (fun σ _ => (Reg.single _).inj))
    (DerivTot.countedIdentitySource (CounterLens.snd3 ST)
      hφ (fun _ _ => rfl)
      (DerivTot.unitary_identity_mask (ctrlRegE x hx) (ctrlGateE x hx)
        (fun σ _ => (ctrlReg x _ _).inj))
      (fun _ => DerivTot.unitary_identity_mask (ctrlRegE x hx) (ctrlGateE x hx)
        (fun σ _ => (ctrlReg x _ _).inj)))

/-- One PREPARE pass, as the masked step obligation of the counted loop. -/
theorem prepStepDeriv (hψ : ‖ψ‖ = 1) (k : ℕ) :
    DerivTot (σT := STc)
      ((Assn.ofStateFam (fun σ => prepSt x hx ψ (coef σ) k)
        (fun σ => norm_prepSt x hx ψ hψ (coef σ) k)).mask
        fun σ => (CounterLens.fst3 ST).get σ = k ∧ k < NT x - 1)
      (prepBody x hx)
      ((Assn.ofStateFam (fun σ => prepSt x hx ψ (coef σ) (k + 1))
        (fun σ => norm_prepSt x hx ψ hψ (coef σ) (k + 1))).mask
        fun σ => (CounterLens.fst3 ST).get σ = k ∧ k < NT x - 1) :=
  DerivTot.countedRung_fam (prepRegE x hx) (prepGateE x hx)
    (fun σ => norm_prepSt x hx ψ hψ (coef σ) k)
    (fun σ => norm_prepSt x hx ψ hψ (coef σ) (k + 1))
    (fun σ hσ => prepBody_act x hx ψ σ k hσ.1 hσ.2)

/-- The PREPARE loop, in one `countedStateChain` call along `prepSt`. -/
theorem prepLoopDeriv (hψ : ‖ψ‖ = 1) :
    DerivTot (σT := STc)
      (Assn.ofStateFam (fun σ => prepSt x hx ψ (coef σ) 0)
        (fun σ => norm_prepSt x hx ψ hψ (coef σ) 0))
      (countedProg (CounterLens.fst3 ST) (fun _ => NT x - 1) (prepBody x hx))
      ((Assn.ofStateFam (fun σ => prepSt x hx ψ (coef σ) (NT x - 1))
        (fun σ => norm_prepSt x hx ψ hψ (coef σ) (NT x - 1))).mask
        fun σ => (CounterLens.fst3 ST).get σ = NT x - 1) :=
  DerivTot.countedStateChainSource (CounterLens.fst3 ST)
    (fun m σ => prepSt x hx ψ (coef σ) m)
    (fun m σ => norm_prepSt x hx ψ hψ (coef σ) m)
    (fun _ _ _ => rfl) rfl rfl
    (DerivTot.countedRung_fam (prepRegE x hx) (prepGateE x hx)
      (fun σ => norm_prepSt x hx ψ hψ (coef σ) σ.1)
      (fun σ => norm_prepSt x hx ψ hψ (coef σ) (σ.1 + 1))
      (fun σ hσ => prepBody_act x hx ψ σ σ.1 rfl hσ))
    (fun _ => DerivTot.unitary_identity_mask (prepRegE x hx) (prepGateE x hx)
      (fun σ _ => (prepReg x _).inj))

/-- **PREPARE derivation**: `{∣0⟩ₐ ⊗ ψ} prepProg {∑ aᵢ ∣eᵢ⟩ ⊗ ψ}`. -/
theorem prepDeriv (hψ : ‖ψ‖ = 1) :
    DerivTot (σT := STc)
      (Assn.ofStateFam (fun _ => ancEmbed (L₁ := SysL x) (anc0 x) ψ)
        (fun _ => norm_inS x ψ hψ))
      (prepProg x hx)
      (Assn.ofStateFam (fun σ => fullSt x hx ψ (coef σ))
        (fun σ => norm_fullSt x hx ψ hψ (coef σ))) := by
  refine DerivTot.seq (B := Assn.ofStateFam (fun σ => prepSt x hx ψ (coef σ) 0)
    (fun σ => norm_prepSt x hx ψ hψ (coef σ) 0)) ?_ ?_
  · exact DerivTot.unitary_stateFam _ _ _ _
      (fun σ => (xGate_emb x hx ψ).trans (prepSt_zero x hx ψ (coef σ)).symm)
  · refine DerivTot.conseq (Assn.le_refl' _) (prepLoopDeriv x hx ψ hψ) ?_
    refine Assn.mask_le_of_imp_le fun σ _ => le_of_eq ?_
    rw [Assn.ofStateFam_op, Assn.ofStateFam_op, prepSt_full]

/-- One letter pass, as the masked step obligation of the inner counted
loop (both counters pinned by the mask). -/
theorem ctrlStepDeriv (hψ : ‖ψ‖ = 1) (k m : ℕ) :
    DerivTot (σT := STc)
      ((Assn.ofStateFam (fun σ => selMid x hx ψ (coef σ) (lCell x hx k) m)
        (fun σ => norm_selMid x hx ψ hψ (coef σ) (lCell x hx k) m)).mask
        fun σ => ((CounterLens.fst3 ST).get σ = k ∧ k < NT x)
          ∧ (CounterLens.snd3 ST).get σ = m ∧ m < 2 ^ x)
      (ctrlBody x hx)
      ((Assn.ofStateFam (fun σ => selMid x hx ψ (coef σ) (lCell x hx k) (m + 1))
        (fun σ => norm_selMid x hx ψ hψ (coef σ) (lCell x hx k) (m + 1))).mask
        fun σ => ((CounterLens.fst3 ST).get σ = k ∧ k < NT x)
          ∧ (CounterLens.snd3 ST).get σ = m ∧ m < 2 ^ x) :=
  DerivTot.countedRung_fam (ctrlRegE x hx) (ctrlGateE x hx)
    (fun σ => norm_selMid x hx ψ hψ (coef σ) (lCell x hx k) m)
    (fun σ => norm_selMid x hx ψ hψ (coef σ) (lCell x hx k) (m + 1))
    (fun σ hσ => ctrlBody_act x hx ψ σ k m hσ.1.1 hσ.2.1 hσ.2.2)

/-- The letter loop of rung `k`, relativised at the outer mask: one
`countedStateChain_rel` call along `selMid`, whose conclusion is exactly the
shape the outer chain's step consumes. -/
theorem innerLoopDeriv (hψ : ‖ψ‖ = 1) (k : ℕ) :
    DerivTot (σT := STc)
      ((Assn.ofStateFam (fun σ => selMid x hx ψ (coef σ) (lCell x hx k) 0)
        (fun σ => norm_selMid x hx ψ hψ (coef σ) (lCell x hx k) 0)).mask
        fun σ => (CounterLens.fst3 ST).get σ = k ∧ k < NT x)
      (countedProg (CounterLens.snd3 ST) (fun _ => 2 ^ x) (ctrlBody x hx))
      ((Assn.ofStateFam (fun σ => selSt x hx ψ (coef σ) (k + 1))
        (fun σ => norm_selSt x hx ψ hψ (coef σ) (k + 1))).mask
        fun σ => (CounterLens.fst3 ST).get σ = k ∧ k < NT x) :=
  DerivTot.countedStateChain_relSource (CounterLens.snd3 ST) (2 ^ x)
    (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (fun m σ => selMid x hx ψ (coef σ) (lCell x hx k) m)
    (fun m σ => norm_selMid x hx ψ hψ (coef σ) (lCell x hx k) m)
    (fun _ _ _ => rfl)
    (fun _ _ => rfl)
    (fun σ hσ => by
      have h := selMid_top x hx (coef σ) (lCell x hx k) ψ
      rw [lCell_val x hx hσ.2] at h
      exact h)
    (DerivTot.countedRung_fam (ctrlRegE x hx) (ctrlGateE x hx)
      (fun σ => norm_selMid x hx ψ hψ (coef σ) (lCell x hx k) σ.2.1)
      (fun σ => norm_selMid x hx ψ hψ (coef σ) (lCell x hx k) (σ.2.1 + 1))
      (fun σ hσ => ctrlBody_act x hx ψ σ k σ.2.1 hσ.1.1 rfl hσ.2))
    (fun _ => DerivTot.unitary_identity_mask (ctrlRegE x hx) (ctrlGateE x hx)
      (fun σ _ => (ctrlReg x _ _).inj))

/-- **One SELECT rung**, as the masked step obligation of the outer counted
loop: the sign rung glued to the relativised letter loop by (R-Seq). -/
theorem selStepDeriv (hψ : ‖ψ‖ = 1) (k : ℕ) :
    DerivTot (σT := STc)
      ((Assn.ofStateFam (fun σ => selSt x hx ψ (coef σ) k)
        (fun σ => norm_selSt x hx ψ hψ (coef σ) k)).mask
        fun σ => (CounterLens.fst3 ST).get σ = k ∧ k < NT x)
      (rungBody x hx)
      ((Assn.ofStateFam (fun σ => selSt x hx ψ (coef σ) (k + 1))
        (fun σ => norm_selSt x hx ψ hψ (coef σ) (k + 1))).mask
        fun σ => (CounterLens.fst3 ST).get σ = k ∧ k < NT x) :=
  DerivTot.seq
    (DerivTot.countedRung_fam (sgnRegE x hx) (sgnGateE x hx)
      (fun σ => norm_selSt x hx ψ hψ (coef σ) k)
      (fun σ => norm_selMid x hx ψ hψ (coef σ) (lCell x hx k) 0)
      (fun σ hσ => sgnBody_act x hx ψ σ k hσ.1 hσ.2))
    (innerLoopDeriv x hx ψ hψ k)

/-- SELECT invariant preservation at the current outer counter. -/
theorem selStepSource (hψ : ‖ψ‖ = 1) :
    DerivTot
      ((Assn.ofStateFam (fun σ : STc => selSt x hx ψ (coef σ) σ.1)
        (fun σ => norm_selSt x hx ψ hψ (coef σ) σ.1)).mask fun σ => σ.1 < NT x)
      (rungBody x hx)
      ((Assn.ofStateFam (fun σ : STc => selSt x hx ψ (coef σ) (σ.1 + 1))
        (fun σ => norm_selSt x hx ψ hψ (coef σ) (σ.1 + 1))).mask fun σ => σ.1 < NT x) := by
  refine DerivTot.seq
    (DerivTot.countedRung_fam (sgnRegE x hx) (sgnGateE x hx)
      (fun σ => norm_selSt x hx ψ hψ (coef σ) σ.1)
      (fun σ => norm_selMid x hx ψ hψ (coef σ) (lCell x hx σ.1) 0)
      (fun σ hσ => sgnBody_act x hx ψ σ σ.1 rfl hσ)) ?_
  exact DerivTot.countedStateChain_relSource (CounterLens.snd3 ST) (2 ^ x)
    (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (fun m σ => selMid x hx ψ (coef σ) (lCell x hx σ.1) m)
    (fun m σ => norm_selMid x hx ψ hψ (coef σ) (lCell x hx σ.1) m)
    (fun _ _ _ => rfl) (fun _ _ => rfl)
    (fun σ hσ => by
      have h := selMid_top x hx (coef σ) (lCell x hx σ.1) ψ
      rw [lCell_val x hx hσ] at h
      exact h)
    (DerivTot.countedRung_fam (ctrlRegE x hx) (ctrlGateE x hx)
      (fun σ => norm_selMid x hx ψ hψ (coef σ) (lCell x hx σ.1) σ.2.1)
      (fun σ => norm_selMid x hx ψ hψ (coef σ) (lCell x hx σ.1) (σ.2.1 + 1))
      (fun σ hσ => ctrlBody_act x hx ψ σ σ.1 σ.2.1 rfl rfl hσ.2))
    (fun _ => DerivTot.unitary_identity_mask (ctrlRegE x hx) (ctrlGateE x hx)
      (fun σ _ => (ctrlReg x _ _).inj))

/-- **SELECT derivation**: one `countedStateChain` call along `selSt`. -/
theorem selDeriv (hψ : ‖ψ‖ = 1) :
    DerivTot (σT := STc)
      (Assn.ofStateFam (fun σ => selSt x hx ψ (coef σ) 0)
        (fun σ => norm_selSt x hx ψ hψ (coef σ) 0))
      (selProg x hx)
      (Assn.ofStateFam (fun σ => selSt x hx ψ (coef σ) (NT x))
        (fun σ => norm_selSt x hx ψ hψ (coef σ) (NT x))) :=
  DerivTot.conseq (Assn.le_refl' _)
    (DerivTot.countedStateChainSource (CounterLens.fst3 ST)
      (fun l σ => selSt x hx ψ (coef σ) l)
      (fun l σ => norm_selSt x hx ψ hψ (coef σ) l)
      (fun _ _ _ => rfl) rfl rfl
      (selStepSource x hx ψ hψ)
      (fun k => rungIdentity x hx _ (fun _ _ => Iff.rfl)))
    (Assn.mask_le_of_imp_le fun _ _ => le_rfl)

/-- One UNPREPARE pass, as the masked step obligation of the counted loop. -/
theorem unprepStepDeriv (hψ : ‖ψ‖ = 1) (k : ℕ) :
    DerivTot (σT := STc)
      ((Assn.ofStateFam (fun σ => unprepSt x hx ψ (coef σ) k)
        (fun σ => norm_unprepSt x hx ψ hψ (coef σ) k)).mask
        fun σ => (CounterLens.fst3 ST).get σ = k ∧ k < NT x - 1)
      (unprepBody x hx)
      ((Assn.ofStateFam (fun σ => unprepSt x hx ψ (coef σ) (k + 1))
        (fun σ => norm_unprepSt x hx ψ hψ (coef σ) (k + 1))).mask
        fun σ => (CounterLens.fst3 ST).get σ = k ∧ k < NT x - 1) :=
  DerivTot.countedRung_fam (unprepRegE x hx) (unprepGateE x hx)
    (fun σ => norm_unprepSt x hx ψ hψ (coef σ) k)
    (fun σ => norm_unprepSt x hx ψ hψ (coef σ) (k + 1))
    (fun σ hσ => unprepBody_act x hx ψ σ k hσ.1 hσ.2)

/-- The UNPREPARE loop, in one `countedStateChain` call along `unprepSt`. -/
theorem unprepLoopDeriv (hψ : ‖ψ‖ = 1) :
    DerivTot (σT := STc)
      (Assn.ofStateFam (fun σ => unprepSt x hx ψ (coef σ) 0)
        (fun σ => norm_unprepSt x hx ψ hψ (coef σ) 0))
      (countedProg (CounterLens.fst3 ST) (fun _ => NT x - 1) (unprepBody x hx))
      ((Assn.ofStateFam (fun σ => unprepSt x hx ψ (coef σ) (NT x - 1))
        (fun σ => norm_unprepSt x hx ψ hψ (coef σ) (NT x - 1))).mask
        fun σ => (CounterLens.fst3 ST).get σ = NT x - 1) :=
  DerivTot.countedStateChainSource (CounterLens.fst3 ST)
    (fun m σ => unprepSt x hx ψ (coef σ) m)
    (fun m σ => norm_unprepSt x hx ψ hψ (coef σ) m)
    (fun _ _ _ => rfl) rfl rfl
    (DerivTot.countedRung_fam (unprepRegE x hx) (unprepGateE x hx)
      (fun σ => norm_unprepSt x hx ψ hψ (coef σ) σ.1)
      (fun σ => norm_unprepSt x hx ψ hψ (coef σ) (σ.1 + 1))
      (fun σ hσ => unprepBody_act x hx ψ σ σ.1 rfl hσ))
    (fun _ => DerivTot.unitary_identity_mask (unprepRegE x hx) (unprepGateE x hx)
      (fun σ _ => (prepReg x _).inj))

/-- **UNPREPARE derivation**, into the named output state. -/
theorem unprepDeriv (hψ : ‖ψ‖ = 1) :
    DerivTot (σT := STc)
      (Assn.ofStateFam (fun σ => selSt x hx ψ (coef σ) (NT x))
        (fun σ => norm_selSt x hx ψ hψ (coef σ) (NT x)))
      (unprepProg x hx)
      (Assn.ofStateFam (fun σ => outSt x hx ψ (coef σ))
        (fun σ => norm_outSt x hx ψ hψ (coef σ))) := by
  refine DerivTot.seq (B := Assn.ofStateFam
    (fun σ => unprepChain x hx (coef σ) (selSt x hx ψ (coef σ) (NT x)))
    (fun σ => norm_eq_one_of_isUnitary (isUnitary_unprepChain x hx (coef σ))
      (norm_selSt x hx ψ hψ (coef σ) (NT x)))) ?_ ?_
  · refine DerivTot.conseq
      (ofStateFam_le x fun σ => (unprepSt_zero x hx ψ (coef σ)).symm)
      (unprepLoopDeriv x hx ψ hψ) ?_
    refine Assn.mask_le_of_imp_le fun σ _ => le_of_eq ?_
    rw [Assn.ofStateFam_op, Assn.ofStateFam_op, unprepSt_full]
  · exact DerivTot.unitary_stateFam _ _ _ _ (fun σ => rfl)

/-- **The exact evolution triple of the LCU block-encoding program**:
`{ ∣0⟩ₐ ⊗ ψ } prep ; select ; unprep { ∣Φ_out⟩ }`, generic in `x`, the store
coefficients `(t, U)` and the unit system state `ψ`. -/
theorem lcuDeriv (hψ : ‖ψ‖ = 1) :
    DerivTot (σT := STc)
      (Assn.ofStateFam (fun _ => ancEmbed (L₁ := SysL x) (anc0 x) ψ)
        (fun _ => norm_inS x ψ hψ))
      (lcuProg x hx)
      (Assn.ofStateFam (fun σ => outSt x hx ψ (coef σ))
        (fun σ => norm_outSt x hx ψ hψ (coef σ))) := by
  refine DerivTot.seq (B := Assn.ofStateFam (fun σ => selSt x hx ψ (coef σ) 0)
      (fun σ => norm_selSt x hx ψ hψ (coef σ) 0)) ?_
    (DerivTot.seq (B := Assn.ofStateFam (fun σ => selSt x hx ψ (coef σ) (NT x))
        (fun σ => norm_selSt x hx ψ hψ (coef σ) (NT x)))
      (selDeriv x hx ψ hψ) (unprepDeriv x hx ψ hψ))
  refine DerivTot.conseq (Assn.le_refl' _) (prepDeriv x hx ψ hψ) ?_
  exact ofStateFam_le x fun σ => (selSt_zero x hx ψ (coef σ)).symm

/-- **Soundness**: the semantic total-correctness statement. -/
theorem lcuValid (hψ : ‖ψ‖ = 1) :
    validTot
      (Assn.ofStateFam (fun _ => ancEmbed (L₁ := SysL x) (anc0 x) ψ)
        (fun _ => norm_inS x ψ hψ))
      (lcuProg x hx)
      (Assn.ofStateFam (fun σ => outSt x hx ψ (coef σ))
        (fun σ => norm_outSt x hx ψ hψ (coef σ))) :=
  (lcuDeriv x hx ψ hψ).sound

/-! ## §8. The block-encoding identity -/

theorem X_mul_X : (X : UnitaryOp 𝕢) * X = 1 := by
  refine Subtype.ext ?_
  rw [UnitaryOp.coe_mul, UnitaryOp.coe_one]
  exact X_comp_X

theorem xLift_comp_self : xLift x hx ∘ₗ xLift x hx = 1 := by
  rw [xLift, regLift_comp, singleGate_coe_comp, X_mul_X, singleGate_coe_one, regLift_one]

theorem adjoint_xLift : LinearMap.adjoint (xLift x hx) = xLift x hx :=
  adjoint_eq_of_comp_eq_one (isUnitary_xLift x hx) (xLift_comp_self x hx)

theorem unprep_gate_inv (σ : ST) (j : Fin (NT x - 1)) :
    regLift (prepReg x j)
        ((pairGate (D := QubitCells (WL x)) (aC x (jA x j)) (aC x (jB x j))
          (jA_ne_jB x j) (givens (ang x hx σ (j : ℕ) (jA_lt x j)))) :
          TSpace (QubitCells (WL x)) (prepReg x j).toFun →ₗ[ℂ] _)
      ∘ₗ regLift (prepReg x j)
        ((pairGate (D := QubitCells (WL x)) (aC x (jA x j)) (aC x (jB x j))
          (jA_ne_jB x j) (givens (-(ang x hx σ (j : ℕ) (jA_lt x j))))) :
          TSpace (QubitCells (WL x)) (prepReg x j).toFun →ₗ[ℂ] _)
      = 1 := by
  rw [regLift_comp, pairGate_coe_comp, givens_mul_neg, pairGate_coe_one, regLift_one]

theorem adjoint_unprep_gate (σ : ST) (j : Fin (NT x - 1)) :
    LinearMap.adjoint (regLift (prepReg x j)
        ((pairGate (D := QubitCells (WL x)) (aC x (jA x j)) (aC x (jB x j))
          (jA_ne_jB x j) (givens (-(ang x hx σ (j : ℕ) (jA_lt x j))))) :
          TSpace (QubitCells (WL x)) (prepReg x j).toFun →ₗ[ℂ] _))
      = regLift (prepReg x j)
        ((pairGate (D := QubitCells (WL x)) (aC x (jA x j)) (aC x (jB x j))
          (jA_ne_jB x j) (givens (ang x hx σ (j : ℕ) (jA_lt x j)))) :
          TSpace (QubitCells (WL x)) (prepReg x j).toFun →ₗ[ℂ] _) :=
  adjoint_eq_of_comp_eq_one (isUnitary_regLift _ _) (unprep_gate_inv x hx σ j)

/-- The adjoint of the un-preparation chain is the preparation chain. -/
theorem adjoint_unprepChain (σ : ST) :
    LinearMap.adjoint (unprepChain x hx σ)
      = chainOp (List.finRange (NT x - 1))
          (fun j => regLift (prepReg x j)
            ((pairGate (D := QubitCells (WL x)) (aC x (jA x j)) (aC x (jB x j))
              (jA_ne_jB x j) (givens (ang x hx σ (j : ℕ) (jA_lt x j)))) :
              TSpace (QubitCells (WL x)) (prepReg x j).toFun →ₗ[ℂ] _)) := by
  rw [unprepChain]
  refine (adjoint_chainOp _ _).trans ?_
  rw [List.reverse_reverse]
  exact congrArg (chainOp (List.finRange (NT x - 1)))
    (funext fun j => adjoint_unprep_gate x hx σ j)

/-- The vacuum-block vector of the output. -/
noncomputable def beVec (σ : ST) : HS (QubitCells (SysL x)) (univ : Finset (SysL x)) :=
  ∑ i : AncL x, ((am x hx σ i ^ 2 * sg x σ i : ℝ) : ℂ) • pauliString (str x i) ψ

/-- The vacuum-block amplitude of the output state against any test vector. -/
theorem inner_emb0_outSt (u : HS (QubitCells (SysL x)) (univ : Finset (SysL x)))
    (σ : ST) :
    (⟪ancEmbed (L₁ := SysL x) (anc0 x) u, outSt x hx ψ σ⟫ : ℂ)
      = ⟪u, beVec x hx ψ σ⟫ := by
  rw [outSt, ← LinearMap.adjoint_inner_left (xLift x hx), adjoint_xLift]
  have hx1 : xLift x hx (ancEmbed (L₁ := SysL x) (anc0 x) u)
      = ancEmbed (L₁ := SysL x) (oneHot x (a0 x hx)) u := xGate_emb x hx u
  rw [hx1, ← LinearMap.adjoint_inner_left (unprepChain x hx σ), adjoint_unprepChain]
  have hchain : chainOp (List.finRange (NT x - 1))
      (fun j => regLift (prepReg x j)
        ((pairGate (D := QubitCells (WL x)) (aC x (jA x j)) (aC x (jB x j))
          (jA_ne_jB x j) (givens (ang x hx σ (j : ℕ) (jA_lt x j)))) :
          TSpace (QubitCells (WL x)) (prepReg x j).toFun →ₗ[ℂ] _))
      (ancEmbed (L₁ := SysL x) (oneHot x (a0 x hx)) u) = fullSt x hx u σ := by
    rw [← prepSt_zero x hx u σ, prep_chain x hx σ u, prepSt_full]
  rw [hchain, fullSt, selSt, inner_sum_emb, beVec, inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_right, selW, if_pos i.isLt, LinearMap.smul_apply, inner_smul_right,
    Complex.conj_ofReal]
  push_cast
  ring

/-- The vacuum block of the output state. -/
theorem embAdj_outSt (σ : ST) :
    LinearMap.adjoint (ancEmbed (L₁ := SysL x) (anc0 x)) (outSt x hx ψ σ)
      = beVec x hx ψ σ := by
  refine ext_inner_left ℂ fun u => ?_
  rw [LinearMap.adjoint_inner_right]
  exact inner_emb0_outSt x hx ψ u σ

theorem beVec_eq (σ : ST) (hlam : 0 < lam x σ) :
    beVec x hx ψ σ = (((lam x σ)⁻¹ : ℝ) : ℂ) • hubbardOp x σ.1 σ.2 ψ := by
  rw [beVec, ← hubbard_sum_eq x σ, LinearMap.sum_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply, smul_smul]
  congr 1
  have ham : am x hx σ i ^ 2 = |cf x σ i| / lam x σ := by
    rw [am, if_pos hlam]
    exact Real.sq_sqrt (div_nonneg (abs_nonneg _) hlam.le)
  have hreal : am x hx σ i ^ 2 * sg x σ i = (lam x σ)⁻¹ * cf x σ i := by
    rw [ham, div_mul_eq_mul_div, mul_comm (|cf x σ i|) (sg x σ i), sg_mul_abs,
      div_eq_inv_mul]
  rw [show ((am x hx σ i ^ 2 * sg x σ i : ℝ) : ℂ)
      = (((lam x σ)⁻¹ * cf x σ i : ℝ) : ℂ) from congrArg _ hreal]
  push_cast
  ring

/-- **The block-encoding identity**: the ancilla-vacuum block of the output
is `λ⁻¹ · H ψ` — the circuit block-encodes the Bravyi–Kitaev Fermi–Hubbard
Hamiltonian with normalization `λ = ∑ |c_l|`. -/
theorem blockEncoding (σ : ST) (hlam : 0 < lam x σ) :
    LinearMap.adjoint (ancEmbed (L₁ := SysL x) (anc0 x)) (outSt x hx ψ σ)
      = (((lam x σ)⁻¹ : ℝ) : ℂ) • hubbardOp x σ.1 σ.2 ψ := by
  rw [embAdj_outSt, beVec_eq x hx ψ σ hlam]

/-! ## §9. The Born effect reading and non-vacuity -/

/-- The **effect** "the ancilla block reads all-zero". -/
noncomputable def ancZeroEff : EndM (QubitCells (WL x)) (univ : Finset (WL x)) :=
  ancEmbed (L₁ := SysL x) (anc0 x) ∘ₗ
    LinearMap.adjoint (ancEmbed (L₁ := SysL x) (anc0 x))

theorem adjoint_ancEmbed_comp_self :
    LinearMap.adjoint (ancEmbed (L₁ := SysL x) (anc0 x)) ∘ₗ
        ancEmbed (L₁ := SysL x) (anc0 x) = LinearMap.id := by
  refine LinearMap.ext fun w => ?_
  rw [LinearMap.comp_apply, LinearMap.id_apply]
  have h := adjoint_ancEmbed_comp (L₁ := SysL x) (anc0 x) (anc0 x) w
  rwa [if_pos rfl] at h

theorem isEffect_ancZeroEff : IsEffect (ancZeroEff x) := by
  refine isEffect_of_isProjOp ⟨?_, ?_⟩
  · change ancZeroEff x ∘ₗ ancZeroEff x = ancZeroEff x
    rw [ancZeroEff, LinearMap.comp_assoc, ← LinearMap.comp_assoc
      (LinearMap.adjoint (ancEmbed (L₁ := SysL x) (anc0 x))),
      adjoint_ancEmbed_comp_self, LinearMap.id_comp]
  · intro u v
    rw [ancZeroEff, LinearMap.comp_apply, LinearMap.comp_apply]
    calc (⟪ancEmbed (L₁ := SysL x) (anc0 x)
          (LinearMap.adjoint (ancEmbed (L₁ := SysL x) (anc0 x)) u), v⟫ : ℂ)
        = ⟪LinearMap.adjoint (ancEmbed (L₁ := SysL x) (anc0 x)) u,
            LinearMap.adjoint (ancEmbed (L₁ := SysL x) (anc0 x)) v⟫ := by
          rw [← LinearMap.adjoint_inner_right]
      _ = ⟪u, ancEmbed (L₁ := SysL x) (anc0 x)
            (LinearMap.adjoint (ancEmbed (L₁ := SysL x) (anc0 x)) v)⟫ := by
          rw [LinearMap.adjoint_inner_left]

/-- **The Born reading**: the expectation of the ancilla-all-zero effect in
the output state is `‖H ψ‖² / λ²` — stated at the widened store, the effect
and the number reading the coefficients through `coef`. -/
theorem effect_reading (σ : STc) (hlam : 0 < lam x (coef σ)) :
    expectE (fun _ : STc => ancZeroEff x)
        ⟨σ, PDensity.pure (outSt x hx ψ (coef σ))⟩
      = ENNReal.ofReal ((lam x (coef σ))⁻¹ ^ 2
          * ‖hubbardOp x (coef σ).1 (coef σ).2 ψ‖ ^ 2) := by
  rw [expectE_pure]
  congr 1
  rw [ancZeroEff, LinearMap.comp_apply, ← LinearMap.adjoint_inner_left,
    blockEncoding x hx ψ (coef σ) hlam,
    inner_smul_left, inner_smul_right, Complex.conj_ofReal,
    inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
  simp [Complex.mul_re, Complex.mul_im]
  norm_cast
  field_simp [ne_of_gt hlam]

/-- **Non-vacuity**: the precondition holds with expectation `1` on the
concrete pure input `∣0⟩ₐ ⊗ ψ`, at any (widened) store value. -/
theorem pre_expect_one (hψ : ‖ψ‖ = 1) (σ₀ : STc) :
    expectE (Assn.ofStateFam (σT := STc)
        (fun _ => ancEmbed (L₁ := SysL x) (anc0 x) ψ)
        (fun _ => norm_inS x ψ hψ)).op
      ⟨σ₀, PDensity.pure (ancEmbed (L₁ := SysL x) (anc0 x) ψ)⟩ = 1 := by
  rw [expectE_pure, Assn.ofStateFam_op, outerLM_apply]
  have hvv : (⟪ancEmbed (L₁ := SysL x) (anc0 x) ψ,
      ancEmbed (L₁ := SysL x) (anc0 x) ψ⟫ : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ), norm_inS x ψ hψ]
    norm_num
  rw [inner_smul_right, hvv]
  simp

end

end Qhl.HubbardLCU

/-! ## §10. Axiom audit -/

#print axioms Qhl.HubbardLCU.lcuDeriv
#print axioms Qhl.HubbardLCU.lcuValid
#print axioms Qhl.HubbardLCU.blockEncoding
#print axioms Qhl.HubbardLCU.effect_reading
#print axioms Qhl.HubbardLCU.pre_expect_one
#print axioms Qhl.HubbardLCU.hubbard_sum_eq
#print axioms Qhl.HubbardLCU.isEffect_ancZeroEff
#print axioms Qhl.HubbardLCU.prepDeriv
#print axioms Qhl.HubbardLCU.selDeriv
#print axioms Qhl.HubbardLCU.unprepDeriv
#print axioms Qhl.BravyiKitaev.hubbardBK_eq

namespace Qhl.HubbardLCU.Source
open Qhl.HubbardLCU Qhl.BravyiKitaev Finset
open scoped ComplexInnerProductSpace ComplexOrder
variable (x : ℕ) (hx : 0 < x)
variable (ψ : HS (QubitCells (SysL x)) (univ : Finset (SysL x))) (hψ : ‖ψ‖ = 1)

/-- Source identity preservation through one SELECT rung, including the inner loop. -/
theorem rungIdentity (φ : STc → Prop)
    (hφ : ∀ σ v, φ ((CounterLens.snd3 ST).set σ v) ↔ φ σ) :
    SourceDerivTot (SourceAssertion.identity (D := QubitCells (WL x)) φ)
      (rungBody x hx) (SourceAssertion.identity φ) := by
  refine .seq (SourceDerivTot.unitary_identity (sgnRegE x hx) (sgnGateE x hx)
    φ (fun _ _ => (Reg.single _).inj)) ?_
  exact SourceDerivTot.countedIdentity (CounterLens.snd3 ST) (fun _ => 2 ^ x) φ
    hφ (fun _ _ => rfl) _
    (SourceDerivTot.unitary_identity (ctrlRegE x hx) (ctrlGateE x hx) _
      (fun _ _ => (ctrlReg x _ _).inj))
    (fun _ => SourceDerivTot.unitary_identity (ctrlRegE x hx) (ctrlGateE x hx) _
      (fun _ _ => (ctrlReg x _ _).inj))

/-- PREPARE's counted loop in the source calculus. -/
theorem prepLoop :
    SourceDerivTot
      (SourceAssertion.ofAssn (Assn.ofStateFam (fun σ => prepSt x hx ψ (coef σ) 0)
        (fun σ => norm_prepSt x hx ψ hψ (coef σ) 0)) (fun _ => True))
      (countedProg (CounterLens.fst3 ST) (fun _ => HubbardLCU.NT x - 1) (prepBody x hx))
      (SourceAssertion.ofAssn
        (Assn.ofStateFam (fun σ => prepSt x hx ψ (coef σ) (HubbardLCU.NT x - 1))
        (fun σ => norm_prepSt x hx ψ hψ (coef σ) (HubbardLCU.NT x - 1))) (fun _ => True)) := by
  apply SourceDerivTot.countedStateChainVar (CounterLens.fst3 ST)
    (fun _ => HubbardLCU.NT x - 1) (fun _ => True) (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (fun m σ => prepSt x hx ψ (coef σ) m)
    (fun m σ => norm_prepSt x hx ψ hψ (coef σ) m)
    (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  · refine SourceDerivTot.unitary_stateFam_guard (prepRegE x hx) (prepGateE x hx) _ _ _ _ _
      (fun _ _ => (prepReg x _).inj) ?_
    intro σ hσ
    exact (prepBody_act x hx ψ σ σ.1 rfl hσ.2).choose_spec
  · intro z
    exact SourceDerivTot.unitary_identity (prepRegE x hx) (prepGateE x hx) _
      (fun _ _ => (prepReg x _).inj)

/-- SELECT's source invariant step with the actual current outer counter. -/
theorem selStep :
    SourceDerivTot
      (SourceAssertion.ofAssn
        (Assn.ofStateFam (fun σ : STc => selSt x hx ψ (coef σ) σ.1)
          (fun σ => norm_selSt x hx ψ hψ (coef σ) σ.1))
        (fun σ => True ∧ σ.1 < HubbardLCU.NT x))
      (rungBody x hx)
      (SourceAssertion.ofAssn
        (Assn.ofStateFam (fun σ : STc => selSt x hx ψ (coef σ) (σ.1 + 1))
          (fun σ => norm_selSt x hx ψ hψ (coef σ) (σ.1 + 1)))
        (fun σ => True ∧ σ.1 < HubbardLCU.NT x)) := by
  refine .seq (B := SourceAssertion.ofAssn
    (Assn.ofStateFam (fun σ => selMid x hx ψ (coef σ) (lCell x hx σ.1) 0)
      (fun σ => norm_selMid x hx ψ hψ (coef σ) (lCell x hx σ.1) 0))
    (fun σ => True ∧ σ.1 < HubbardLCU.NT x)) ?_ ?_
  · refine SourceDerivTot.unitary_stateFam_guard (sgnRegE x hx) (sgnGateE x hx) _ _ _ _ _
      (fun _ _ => (Reg.single _).inj) ?_
    intro σ hσ
    exact (sgnBody_act x hx ψ σ σ.1 rfl hσ.2).choose_spec
  · apply SourceDerivTot.countedStateChainVar (CounterLens.snd3 ST)
      (fun _ => 2 ^ x) (fun σ => True ∧ σ.1 < HubbardLCU.NT x)
      (fun _ _ => Iff.rfl) (fun _ _ => rfl)
      (fun m σ => selMid x hx ψ (coef σ) (lCell x hx σ.1) m)
      (fun m σ => norm_selMid x hx ψ hψ (coef σ) (lCell x hx σ.1) m)
      (fun _ _ _ => rfl) (fun _ _ => rfl)
    · intro σ hσ
      have h := selMid_top x hx (coef σ) (lCell x hx σ.1) ψ
      rw [lCell_val x hx hσ.2] at h
      exact h
    · refine SourceDerivTot.unitary_stateFam_guard (ctrlRegE x hx) (ctrlGateE x hx) _ _ _ _ _
        (fun _ _ => (ctrlReg x _ _).inj) ?_
      intro σ hσ
      exact (ctrlBody_act x hx ψ σ σ.1 σ.2.1 rfl rfl hσ.2).choose_spec
    · intro z
      exact SourceDerivTot.unitary_identity (ctrlRegE x hx) (ctrlGateE x hx) _
        (fun _ _ => (ctrlReg x _ _).inj)

/-- SELECT's outer counted loop. -/
theorem select :
    SourceDerivTot
      (SourceAssertion.ofAssn (Assn.ofStateFam (fun σ => selSt x hx ψ (coef σ) 0)
        (fun σ => norm_selSt x hx ψ hψ (coef σ) 0)) (fun _ => True))
      (selProg x hx)
      (SourceAssertion.ofAssn (Assn.ofStateFam (fun σ => selSt x hx ψ (coef σ) (HubbardLCU.NT x))
        (fun σ => norm_selSt x hx ψ hψ (coef σ) (HubbardLCU.NT x))) (fun _ => True)) := by
  exact SourceDerivTot.countedStateChainVar (CounterLens.fst3 ST)
    (fun _ => HubbardLCU.NT x) (fun _ => True) (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (fun m σ => selSt x hx ψ (coef σ) m)
    (fun m σ => norm_selSt x hx ψ hψ (coef σ) m)
    (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (selStep x hx ψ hψ) (fun _ => rungIdentity x hx _ (fun _ _ => Iff.rfl))

/-- UNPREPARE's counted loop. -/
theorem unprepLoop :
    SourceDerivTot
      (SourceAssertion.ofAssn (Assn.ofStateFam (fun σ => unprepSt x hx ψ (coef σ) 0)
        (fun σ => norm_unprepSt x hx ψ hψ (coef σ) 0)) (fun _ => True))
      (countedProg (CounterLens.fst3 ST) (fun _ => HubbardLCU.NT x - 1) (unprepBody x hx))
      (SourceAssertion.ofAssn
        (Assn.ofStateFam (fun σ => unprepSt x hx ψ (coef σ) (HubbardLCU.NT x - 1))
        (fun σ => norm_unprepSt x hx ψ hψ (coef σ) (HubbardLCU.NT x - 1))) (fun _ => True)) := by
  apply SourceDerivTot.countedStateChainVar (CounterLens.fst3 ST)
    (fun _ => HubbardLCU.NT x - 1) (fun _ => True) (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (fun m σ => unprepSt x hx ψ (coef σ) m)
    (fun m σ => norm_unprepSt x hx ψ hψ (coef σ) m)
    (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  · refine SourceDerivTot.unitary_stateFam_guard (unprepRegE x hx) (unprepGateE x hx) _ _ _ _ _
      (fun _ _ => (prepReg x _).inj) ?_
    intro σ hσ
    exact (unprepBody_act x hx ψ σ σ.1 rfl hσ.2).choose_spec
  · intro z
    exact SourceDerivTot.unitary_identity (unprepRegE x hx) (unprepGateE x hx) _
      (fun _ _ => (prepReg x _).inj)

/-- PREPARE from the original input state to its named coefficient-dependent state. -/
theorem prepare :
    SourceDerivTot
      (SourceAssertion.ofAssn
        (Assn.ofStateFam (fun _ => ancEmbed (L₁ := SysL x) (anc0 x) ψ)
          (fun _ => norm_inS x ψ hψ)) (fun _ => True))
      (prepProg x hx)
      (SourceAssertion.ofAssn (Assn.ofStateFam (fun σ => fullSt x hx ψ (coef σ))
        (fun σ => norm_fullSt x hx ψ hψ (coef σ))) (fun _ => True)) := by
  refine .seq (B := SourceAssertion.ofAssn
    (Assn.ofStateFam (fun σ => prepSt x hx ψ (coef σ) 0)
      (fun σ => norm_prepSt x hx ψ hψ (coef σ) 0)) (fun _ => True)) ?_ ?_
  · refine SourceDerivTot.unitary_stateFam_guard _ _ _ _ _ _ _
      (fun _ _ => (Reg.single _).inj) ?_
    intro σ _
    exact (xGate_emb x hx ψ).trans (prepSt_zero x hx ψ (coef σ)).symm
  · refine .conseq (SourceAssertion.entails_refl _) (prepLoop x hx ψ hψ) ?_
    apply SourceAssertion.entails_ofAssn _ _ _ _ (fun _ h => h)
    intro σ _
    apply le_of_eq
    rw [Assn.ofStateFam_op, Assn.ofStateFam_op, prepSt_full]

/-- UNPREPARE into the original named output-state family. -/
theorem unprepare :
    SourceDerivTot
      (SourceAssertion.ofAssn
        (Assn.ofStateFam (fun σ => selSt x hx ψ (coef σ) (HubbardLCU.NT x))
          (fun σ => norm_selSt x hx ψ hψ (coef σ) (HubbardLCU.NT x))) (fun _ => True))
      (unprepProg x hx)
      (SourceAssertion.ofAssn (Assn.ofStateFam (fun σ => outSt x hx ψ (coef σ))
        (fun σ => norm_outSt x hx ψ hψ (coef σ))) (fun _ => True)) := by
  refine .seq (B := SourceAssertion.ofAssn (Assn.ofStateFam
    (fun σ => unprepChain x hx (coef σ) (selSt x hx ψ (coef σ) (HubbardLCU.NT x)))
    (fun σ => norm_eq_one_of_isUnitary (isUnitary_unprepChain x hx (coef σ))
      (norm_selSt x hx ψ hψ (coef σ) (HubbardLCU.NT x)))) (fun _ => True)) ?_ ?_
  · refine .conseq ?_ (unprepLoop x hx ψ hψ) ?_
    · apply SourceAssertion.entails_ofAssn _ _ _ _ (fun _ h => h)
      intro σ _
      apply le_of_eq
      rw [Assn.ofStateFam_op, Assn.ofStateFam_op, unprepSt_zero]
    · apply SourceAssertion.entails_ofAssn _ _ _ _ (fun _ h => h)
      intro σ _
      apply le_of_eq
      rw [Assn.ofStateFam_op, Assn.ofStateFam_op, unprepSt_full]
  · exact SourceDerivTot.unitary_stateFam_guard _ _ _ _ _ _ _
      (fun _ _ => (Reg.single _).inj) (fun _ _ => rfl)

/-- The exact state-evolution triple, over the original program and stored `(t,U)`. -/
theorem lcuDeriv :
    SourceDerivTot
      (SourceAssertion.ofAssn
        (Assn.ofStateFam (fun _ => ancEmbed (L₁ := SysL x) (anc0 x) ψ)
          (fun _ => norm_inS x ψ hψ)) (fun _ => True))
      (lcuProg x hx)
      (SourceAssertion.ofAssn (Assn.ofStateFam (fun σ => outSt x hx ψ (coef σ))
        (fun σ => norm_outSt x hx ψ hψ (coef σ))) (fun _ => True)) := by
  refine .seq (B := SourceAssertion.ofAssn
    (Assn.ofStateFam (fun σ => selSt x hx ψ (coef σ) 0)
      (fun σ => norm_selSt x hx ψ hψ (coef σ) 0)) (fun _ => True)) ?_
    (.seq (select x hx ψ hψ) (unprepare x hx ψ hψ))
  refine .conseq (SourceAssertion.entails_refl _) (prepare x hx ψ hψ) ?_
  apply SourceAssertion.entails_ofAssn _ _ _ _ (fun _ h => h)
  intro σ _
  apply le_of_eq
  rw [Assn.ofStateFam_op, Assn.ofStateFam_op, selSt_zero]


/-- The original semantic state-evolution target follows from the source derivation. -/
theorem lcuValid :
    validTot
      (Assn.ofStateFam (fun _ => ancEmbed (L₁ := SysL x) (anc0 x) ψ)
        (fun _ => norm_inS x ψ hψ))
      (lcuProg x hx)
      (Assn.ofStateFam (fun σ => outSt x hx ψ (coef σ))
        (fun σ => norm_outSt x hx ψ hψ (coef σ))) := by
  simpa only [SourceAssertion.toAssn_ofAssn_true] using (lcuDeriv x hx ψ hψ).sound

end Qhl.HubbardLCU.Source

#print axioms Qhl.HubbardLCU.Source.lcuDeriv
#print axioms Qhl.HubbardLCU.Source.lcuValid
