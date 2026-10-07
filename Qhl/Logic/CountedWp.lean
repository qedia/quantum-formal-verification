import Qhl.Logic.CountedWhile
import Qhl.Logic.WpChain

/-!
# The `wp`-suffix family of a counted `while` loop

`Qhl/Logic/InitBlock.lean` §1 discharges a straight-line `for` fold backward:
`DerivTot.forProg_foldr` turns a per-iteration backward transformer into the
folded (Ax-Uni) precondition, and `foldr_unitaryPre_const_op` /
`foldr_op_conj` display that fold as one conjugation by the semantic chain
operator.  Under the while-only loop ruling the same circuits are counted
`while` loops (`countedProg`, `Qhl/Logic/CountedWhile.lean`), so this file
supplies the counted-`while` mirror of that layer:

* §1 — **`wpSuffix g n Y`**: the suffix weakest-precondition family of a
  transformer family `g : ℕ → Assn σT D → Assn σT D` against the
  postcondition `Y`, with `wpSuffix g n Y k = g k (wpSuffix g n Y (k+1))`
  for `k < n` and `= Y` for `k ≥ n` (defining lemmas `wpSuffix_of_lt`,
  `wpSuffix_of_ge`, `wpSuffix_full`); the transport principle
  `wpSuffix_prop` (any predicate preserved by every `g k` and satisfied by
  `Y` holds of the whole family) and its counter-write instance
  `wpSuffix_op_set` — the `hJ` obligation of the counted-`while` rule.
* §2 — the commutation `Assn.unitaryPre_mask_op`:
  `((B.mask φ).unitaryPre r U).op σ = ((B.unitaryPre r U).mask φ).op σ`,
  from the `mask`/`unitaryPre` `op` lemmas.
* §3 — **the packaged rules.**  `DerivTot.countedWpBody`(`_const`): the
  counted-`while` rule at the invariant family `J := wpSuffix g n Y`, for an
  arbitrary loop body — the step premises keep their `wpSuffix` endpoints
  and the exit collapses to `Y` by `wpSuffix_full`.
  `DerivTot.countedWpChain`(`_const`): the one-unitary-body instance — the
  body is a single `Prog.unitary` with store-read register/gate, each step
  is discharged internally by `DerivTot.unitary_stepMask`, and the only
  example-side obligation is the on-mask agreement of the store-read
  transformer with the literal-`k` transformer family `g`.  Both come flat
  and `φ`-relativised (the relativised form is what an outer counted loop
  consumes, as in `DerivTot.countedWhile`).
* §4 — the display `wpSuffix_op_conj` / `wpSuffix_zero_op_conj`: when every
  `g k` acts at `σ` as a conjugation by `G k`, the whole suffix family is
  one conjugation by `chainOp (List.range' k (n-k)) G` — at `k = 0` by
  `chainOp (List.range n) G`.  This is the ℕ-indexed analogue of
  `foldr_unitaryPre_const_op` / `foldr_op_conj`, and it is what keeps a
  success-probability precondition computable as a single conjugation.
* §5 — a composition test (`CountedWpTest`): a two-gate chain whose
  `wpSuffix` collapses to the double conjugation, plus the derived triple
  for the counted loop that runs it.

For a loop body that is not one unitary (e.g. a rung `unitary ; inner
chain`), consumers use `DerivTot.countedWpBody` directly and discharge each
step premise themselves (one (Ax-Uni)/(R-Seq) tree plus an on-mask
(R-Conseq)); no further packaging is provided here.

Everything is generic in the world `L`, the cell family `D` and the store
`σT` (ownership test); the rules are consumed through the counted-loop
helpers of `CountedWhile` and `DerivTot.unitary_stepMask`.

The helpers whose names end in `Source` use the source total-loop constructor.
They require an unranked invariant-preservation derivation and a separate
identity-predicate derivation. The older helpers retain their original
combined-premise extension for compatibility; they are not source-rule proofs.
For nested loops with a store-dependent bound, `countedStateChainVarSource`
uses the bound and state family at the current classical store.
-/

namespace Qhl

open Finset
open scoped ComplexInnerProductSpace

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)]
variable {σT : Type*}

/-! ## §1. The suffix weakest-precondition family -/

/-- Fuel-indexed helper of `wpSuffix`: `m` transformer applications starting
at counter value `k`.  Structural recursion on the fuel. -/
noncomputable def wpSuffixAux (g : ℕ → Assn σT D → Assn σT D) (Y : Assn σT D) :
    ℕ → ℕ → Assn σT D
  | 0, _ => Y
  | m + 1, k => g k (wpSuffixAux g Y m (k + 1))

/-- **The suffix weakest-precondition family**: `wpSuffix g n Y k` is the
backward composite `g k (g (k+1) (… (g (n-1) Y)))` — the precondition the
remaining passes `k, k+1, …, n-1` of a counted loop compute from the
postcondition `Y`, when the pass at counter value `j` transforms backward by
`g j`.  For `k ≥ n` it is `Y`. -/
noncomputable def wpSuffix (g : ℕ → Assn σT D → Assn σT D) (n : ℕ)
    (Y : Assn σT D) (k : ℕ) : Assn σT D :=
  wpSuffixAux g Y (n - k) k

omit [∀ i, Inhabited (D i)] in
/-- Defining equation below the bound. -/
theorem wpSuffix_of_lt {g : ℕ → Assn σT D → Assn σT D} {n : ℕ}
    {Y : Assn σT D} {k : ℕ} (h : k < n) :
    wpSuffix g n Y k = g k (wpSuffix g n Y (k + 1)) := by
  unfold wpSuffix
  rw [show n - k = (n - (k + 1)) + 1 from by omega]
  simp only [wpSuffixAux]

omit [∀ i, Inhabited (D i)] in
/-- Defining equation at and above the bound. -/
theorem wpSuffix_of_ge {g : ℕ → Assn σT D → Assn σT D} {n : ℕ}
    {Y : Assn σT D} {k : ℕ} (h : n ≤ k) : wpSuffix g n Y k = Y := by
  unfold wpSuffix
  rw [Nat.sub_eq_zero_of_le h]
  simp only [wpSuffixAux]

omit [∀ i, Inhabited (D i)] in
/-- At the exit counter value the family is the postcondition. -/
@[simp]
theorem wpSuffix_full (g : ℕ → Assn σT D → Assn σT D) (n : ℕ)
    (Y : Assn σT D) : wpSuffix g n Y n = Y :=
  wpSuffix_of_ge le_rfl

omit [∀ i, Inhabited (D i)] in
private theorem wpSuffixAux_prop (Q : Assn σT D → Prop)
    {g : ℕ → Assn σT D → Assn σT D} {Y : Assn σT D} {n : ℕ}
    (hg : ∀ j, j < n → ∀ A, Q A → Q (g j A)) (hY : Q Y) :
    ∀ m k, m + k ≤ n → Q (wpSuffixAux g Y m k)
  | 0, _, _ => hY
  | m + 1, k, h =>
      hg k (by omega) _ (wpSuffixAux_prop Q hg hY m (k + 1) (by omega))

omit [∀ i, Inhabited (D i)] in
/-- **Transport along the suffix family**: a predicate of assertions that is
preserved by every transformer `g k` (below the bound) and holds of `Y`
holds of every `wpSuffix g n Y k`.  The induction over the suffix lives
here, so a consumer never inducts over its own gate chain. -/
theorem wpSuffix_prop (Q : Assn σT D → Prop)
    {g : ℕ → Assn σT D → Assn σT D} {n : ℕ} {Y : Assn σT D}
    (hg : ∀ k, k < n → ∀ A, Q A → Q (g k A)) (hY : Q Y) (k : ℕ) :
    Q (wpSuffix g n Y k) := by
  rcases Nat.lt_or_ge k n with h | h
  · exact wpSuffixAux_prop Q hg hY (n - k) k (by omega)
  · rw [wpSuffix_of_ge h]
    exact hY

omit [∀ i, Inhabited (D i)] in
/-- The counter-write-insensitivity obligation (`hJ`) of the counted-`while`
rule, discharged for the whole suffix family: if every `g k` preserves
insensitivity to counter writes and `Y` is insensitive, so is every
`wpSuffix g n Y k`. -/
theorem wpSuffix_op_set (g : ℕ → Assn σT D → Assn σT D) {n : ℕ}
    (Y : Assn σT D) (c : CounterLens σT)
    (hg : ∀ k (A : Assn σT D), (∀ σ v, A.op (c.set σ v) = A.op σ) →
      ∀ σ v, (g k A).op (c.set σ v) = (g k A).op σ)
    (hY : ∀ σ v, Y.op (c.set σ v) = Y.op σ) (k : ℕ) (σ : σT) (v : ℕ) :
    (wpSuffix g n Y k).op (c.set σ v) = (wpSuffix g n Y k).op σ :=
  wpSuffix_prop (fun A => ∀ σ v, A.op (c.set σ v) = A.op σ)
    (fun j _ A hA => hg j A hA) hY k σ v

/-! ## §2. The `mask`/`unitaryPre` commutation -/

/-- The (Ax-Uni) transformer commutes with a classical mask, pointwise on
`op`: masking the postcondition before conjugating equals conjugating and
then masking.  Both sides are `0` off the mask and off the `Dist` branch. -/
theorem Assn.unitaryPre_mask_op (B : Assn σT D) (φ : σT → Prop) {k : ℕ}
    (r : RegExpr σT L k) (U : ∀ σ, UnitaryOp (TSpace D (r σ))) (σ : σT) :
    ((B.mask φ).unitaryPre r U).op σ = ((B.unitaryPre r U).mask φ).op σ := by
  by_cases hs : φ σ
  · by_cases h : Function.Injective (r σ)
    · rw [Assn.unitaryPre_op_of_dist _ r U h, Assn.mask_op_of_pos (A := B) hs,
        Assn.mask_op_of_pos (A := B.unitaryPre r U) hs,
        Assn.unitaryPre_op_of_dist _ r U h]
    · rw [Assn.unitaryPre_op_of_not_dist _ r U h,
        Assn.mask_op_of_pos (A := B.unitaryPre r U) hs,
        Assn.unitaryPre_op_of_not_dist _ r U h]
  · by_cases h : Function.Injective (r σ)
    · rw [Assn.unitaryPre_op_of_dist _ r U h, Assn.mask_op_of_neg hs,
        Assn.mask_op_of_neg hs, LinearMap.zero_comp, LinearMap.comp_zero]
    · rw [Assn.unitaryPre_op_of_not_dist _ r U h, Assn.mask_op_of_neg hs]

/-! ## §3. The packaged rules -/

/-- **The counted-`while` rule at the suffix `wp` invariant** (arbitrary
body, `φ`-relativised).  The invariant family is `J := wpSuffix g n Y`; its
counter-write insensitivity is derived from that of the transformers and of
`Y`, and the exit assertion collapses to the postcondition `Y` by
`wpSuffix_full`.  The step premises keep their `wpSuffix` endpoints — a
compound body (e.g. `unitary ; inner chain`) discharges them by its own
(Ax-Uni)/(R-Seq) tree plus an on-mask (R-Conseq). -/
theorem DerivTot.countedWpBody (c : CounterLens σT) {N : σT → ℕ} {n : ℕ}
    {φ : σT → Prop} {BODY : Prog σT D}
    (g : ℕ → Assn σT D → Assn σT D) (Y : Assn σT D)
    (hφ : ∀ σ v, φ (c.set σ v) ↔ φ σ)
    (hN : ∀ σ, φ σ → N σ = n)
    (hg : ∀ k (A : Assn σT D), (∀ σ v, A.op (c.set σ v) = A.op σ) →
      ∀ σ v, (g k A).op (c.set σ v) = (g k A).op σ)
    (hY : ∀ σ v, Y.op (c.set σ v) = Y.op σ)
    (hstep : ∀ k, DerivTot
      ((wpSuffix g n Y k).mask fun σ => φ σ ∧ c.get σ = k ∧ k < n) BODY
      ((wpSuffix g n Y (k + 1)).mask fun σ => φ σ ∧ c.get σ = k ∧ k < n)) :
    DerivTot ((wpSuffix g n Y 0).mask φ) (countedProg c N BODY)
      (Y.mask fun σ => φ σ ∧ c.get σ = n) := by
  have h := DerivTot.countedWhile (J := wpSuffix g n Y) c hφ hN
    (fun k σ v => wpSuffix_op_set g Y c hg hY k σ v) hstep
  rwa [wpSuffix_full] at h

/-- Flat form of `DerivTot.countedWpBody`: literal bound, no frame
predicate. -/
theorem DerivTot.countedWpBody_const (c : CounterLens σT) {n : ℕ}
    {BODY : Prog σT D}
    (g : ℕ → Assn σT D → Assn σT D) (Y : Assn σT D)
    (hg : ∀ k (A : Assn σT D), (∀ σ v, A.op (c.set σ v) = A.op σ) →
      ∀ σ v, (g k A).op (c.set σ v) = (g k A).op σ)
    (hY : ∀ σ v, Y.op (c.set σ v) = Y.op σ)
    (hstep : ∀ k, DerivTot
      ((wpSuffix g n Y k).mask fun σ => c.get σ = k ∧ k < n) BODY
      ((wpSuffix g n Y (k + 1)).mask fun σ => c.get σ = k ∧ k < n)) :
    DerivTot (wpSuffix g n Y 0) (countedProg c (fun _ => n) BODY)
      (Y.mask fun σ => c.get σ = n) := by
  have h := DerivTot.countedWhile_const (J := wpSuffix g n Y) c
    (fun k σ v => wpSuffix_op_set g Y c hg hY k σ v) hstep
  rwa [wpSuffix_full] at h

/-- **The counted `wp`-chain rule** (`φ`-relativised): a counted loop whose
body is **one unitary** with store-read register expression `rE` / gate
family `UE` is discharged against the suffix family of a literal-indexed
transformer family `g`.  The only per-loop obligation beyond the standard
counter bookkeeping is `hagree`: on the step mask (`φ`, counter `= k`,
`k < n`) the store-read (Ax-Uni) transformer agrees pointwise with `g k`.
Each step is closed internally by `DerivTot.unitary_stepMask`; steps at
`k ≥ n` have everywhere-false masks and close vacuously. -/
theorem DerivTot.countedWpChain (c : CounterLens σT) {N : σT → ℕ} {n : ℕ}
    {φ : σT → Prop} {kb : ℕ} (rE : RegExpr σT L kb)
    (UE : ∀ σ, UnitaryOp (TSpace D (rE σ)))
    (g : ℕ → Assn σT D → Assn σT D) (Y : Assn σT D)
    (hφ : ∀ σ v, φ (c.set σ v) ↔ φ σ)
    (hN : ∀ σ, φ σ → N σ = n)
    (hg : ∀ k (A : Assn σT D), (∀ σ v, A.op (c.set σ v) = A.op σ) →
      ∀ σ v, (g k A).op (c.set σ v) = (g k A).op σ)
    (hY : ∀ σ v, Y.op (c.set σ v) = Y.op σ)
    (hagree : ∀ k, k < n → ∀ σ, φ σ → c.get σ = k → ∀ A : Assn σT D,
      (g k A).op σ = (A.unitaryPre rE UE).op σ) :
    DerivTot ((wpSuffix g n Y 0).mask φ)
      (countedProg c N (.unitary kb rE UE))
      (Y.mask fun σ => φ σ ∧ c.get σ = n) := by
  refine DerivTot.countedWpBody c g Y hφ hN hg hY fun k =>
    DerivTot.unitary_stepMask rE UE fun σ hσ => ?_
  obtain ⟨hφσ, hget, hkn⟩ := hσ
  rw [Assn.unitaryPre_mask_op, Assn.mask_op_of_pos ⟨hφσ, hget, hkn⟩,
    wpSuffix_of_lt hkn]
  exact le_of_eq (hagree k hkn σ hφσ hget _)

/-- Flat form of `DerivTot.countedWpChain`: literal bound, no frame
predicate — the shape a single success-probability loop consumes. -/
theorem DerivTot.countedWpChain_const (c : CounterLens σT) {n : ℕ} {kb : ℕ}
    (rE : RegExpr σT L kb) (UE : ∀ σ, UnitaryOp (TSpace D (rE σ)))
    (g : ℕ → Assn σT D → Assn σT D) (Y : Assn σT D)
    (hg : ∀ k (A : Assn σT D), (∀ σ v, A.op (c.set σ v) = A.op σ) →
      ∀ σ v, (g k A).op (c.set σ v) = (g k A).op σ)
    (hY : ∀ σ v, Y.op (c.set σ v) = Y.op σ)
    (hagree : ∀ k, k < n → ∀ σ, c.get σ = k → ∀ A : Assn σT D,
      (g k A).op σ = (A.unitaryPre rE UE).op σ) :
    DerivTot (wpSuffix g n Y 0)
      (countedProg c (fun _ => n) (.unitary kb rE UE))
      (Y.mask fun σ => c.get σ = n) := by
  refine DerivTot.countedWpBody_const c g Y hg hY fun k =>
    DerivTot.unitary_stepMask rE UE fun σ hσ => ?_
  obtain ⟨hget, hkn⟩ := hσ
  rw [Assn.unitaryPre_mask_op, Assn.mask_op_of_pos ⟨hget, hkn⟩,
    wpSuffix_of_lt hkn]
  exact le_of_eq (hagree k hkn σ hget _)


/-- Source total-loop variant with a store-indexed invariant step and an
independent identity-predicate body derivation. -/
theorem DerivTot.countedWpBodySource (c : CounterLens σT) {N : σT → ℕ} {n : ℕ}
    {φ : σT → Prop} {BODY : Prog σT D}
    (g : ℕ → Assn σT D → Assn σT D) (Y : Assn σT D)
    (hφ : ∀ σ v, φ (c.set σ v) ↔ φ σ)
    (hN : ∀ σ, φ σ → N σ = n)
    (hg : ∀ k (A : Assn σT D), (∀ σ v, A.op (c.set σ v) = A.op σ) →
      ∀ σ v, (g k A).op (c.set σ v) = (g k A).op σ)
    (hY : ∀ σ v, Y.op (c.set σ v) = Y.op σ)
    (hstep : DerivTot
      ((Assn.ofFam c.get (wpSuffix g n Y)).mask fun σ => φ σ ∧ c.get σ < n) BODY
      ((Assn.ofFam c.get (fun m => wpSuffix g n Y (m + 1))).mask
        fun σ => φ σ ∧ c.get σ < n))
    (hidentity : ∀ k, DerivTot
      ((Assn.one : Assn σT D).mask fun σ => φ σ ∧ c.get σ = k ∧ k < n) BODY
      ((Assn.one : Assn σT D).mask fun σ => φ σ ∧ c.get σ = k ∧ k < n)) :
    DerivTot ((wpSuffix g n Y 0).mask φ) (countedProg c N BODY)
      (Y.mask fun σ => φ σ ∧ c.get σ = n) := by
  have h := DerivTot.countedWhileSource (J := wpSuffix g n Y) c hφ hN
    (fun k σ v => wpSuffix_op_set g Y c hg hY k σ v) hstep hidentity
  rwa [wpSuffix_full] at h

/-- Source total-loop variant with a store-indexed invariant step and an
independent identity-predicate body derivation. -/
theorem DerivTot.countedWpBody_constSource (c : CounterLens σT) {n : ℕ}
    {BODY : Prog σT D}
    (g : ℕ → Assn σT D → Assn σT D) (Y : Assn σT D)
    (hg : ∀ k (A : Assn σT D), (∀ σ v, A.op (c.set σ v) = A.op σ) →
      ∀ σ v, (g k A).op (c.set σ v) = (g k A).op σ)
    (hY : ∀ σ v, Y.op (c.set σ v) = Y.op σ)
    (hstep : DerivTot
      ((Assn.ofFam c.get (wpSuffix g n Y)).mask fun σ => c.get σ < n) BODY
      ((Assn.ofFam c.get (fun m => wpSuffix g n Y (m + 1))).mask
        fun σ => c.get σ < n))
    (hidentity : ∀ k, DerivTot
      ((Assn.one : Assn σT D).mask fun σ => c.get σ = k ∧ k < n) BODY
      ((Assn.one : Assn σT D).mask fun σ => c.get σ = k ∧ k < n)) :
    DerivTot (wpSuffix g n Y 0) (countedProg c (fun _ => n) BODY)
      (Y.mask fun σ => c.get σ = n) := by
  have h := DerivTot.countedWhile_constSource (J := wpSuffix g n Y) c
    (fun k σ v => wpSuffix_op_set g Y c hg hY k σ v) hstep hidentity
  rwa [wpSuffix_full] at h


/-- Source total-loop rule for a unitary suffix chain. Register distinctness
is required independently of the weighted weakest precondition. -/
theorem DerivTot.countedWpChainSource (c : CounterLens σT) {N : σT → ℕ} {n : ℕ}
    {φ : σT → Prop} {kb : ℕ} (rE : RegExpr σT L kb)
    (UE : ∀ σ, UnitaryOp (TSpace D (rE σ)))
    (g : ℕ → Assn σT D → Assn σT D) (Y : Assn σT D)
    (hφ : ∀ σ v, φ (c.set σ v) ↔ φ σ)
    (hN : ∀ σ, φ σ → N σ = n)
    (hg : ∀ k (A : Assn σT D), (∀ σ v, A.op (c.set σ v) = A.op σ) →
      ∀ σ v, (g k A).op (c.set σ v) = (g k A).op σ)
    (hY : ∀ σ v, Y.op (c.set σ v) = Y.op σ)
    (hdist : ∀ σ, φ σ → c.get σ < n → Function.Injective (rE σ))
    (hagree : ∀ k, k < n → ∀ σ, φ σ → c.get σ = k → ∀ A : Assn σT D,
      (g k A).op σ = (A.unitaryPre rE UE).op σ) :
    DerivTot ((wpSuffix g n Y 0).mask φ)
      (countedProg c N (.unitary kb rE UE))
      (Y.mask fun σ => φ σ ∧ c.get σ = n) := by
  refine DerivTot.countedWpBodySource c g Y hφ hN hg hY ?_ ?_
  · refine DerivTot.unitary_stepMask rE UE fun σ hσ => ?_
    rw [Assn.unitaryPre_mask_op,
      Assn.mask_op_of_pos (φ := fun σ => φ σ ∧ c.get σ < n) hσ,
      Assn.ofFam_op, wpSuffix_of_lt hσ.2,
      hagree (c.get σ) hσ.2 σ hσ.1 rfl]
    rw [Assn.unitaryPre_op_of_dist _ rE UE (hdist σ hσ.1 hσ.2),
      Assn.unitaryPre_op_of_dist _ rE UE (hdist σ hσ.1 hσ.2), Assn.ofFam_op]
  · intro k
    exact DerivTot.unitary_identityMask rE UE _ fun σ hσ =>
      hdist σ hσ.1 (by rcases hσ with ⟨_, hk, hn⟩; omega)


/-- Source total-loop rule for a unitary suffix chain. Register distinctness
is required independently of the weighted weakest precondition. -/
theorem DerivTot.countedWpChain_constSource (c : CounterLens σT) {n : ℕ} {kb : ℕ}
    (rE : RegExpr σT L kb) (UE : ∀ σ, UnitaryOp (TSpace D (rE σ)))
    (g : ℕ → Assn σT D → Assn σT D) (Y : Assn σT D)
    (hg : ∀ k (A : Assn σT D), (∀ σ v, A.op (c.set σ v) = A.op σ) →
      ∀ σ v, (g k A).op (c.set σ v) = (g k A).op σ)
    (hY : ∀ σ v, Y.op (c.set σ v) = Y.op σ)
    (hdist : ∀ σ, c.get σ < n → Function.Injective (rE σ))
    (hagree : ∀ k, k < n → ∀ σ, c.get σ = k → ∀ A : Assn σT D,
      (g k A).op σ = (A.unitaryPre rE UE).op σ) :
    DerivTot (wpSuffix g n Y 0)
      (countedProg c (fun _ => n) (.unitary kb rE UE))
      (Y.mask fun σ => c.get σ = n) := by
  refine DerivTot.countedWpBody_constSource c g Y hg hY ?_ ?_
  · refine DerivTot.unitary_stepMask rE UE fun σ hσ => ?_
    rw [Assn.unitaryPre_mask_op,
      Assn.mask_op_of_pos (φ := fun σ => c.get σ < n) hσ,
      Assn.ofFam_op, wpSuffix_of_lt hσ,
      hagree (c.get σ) hσ σ rfl]
    rw [Assn.unitaryPre_op_of_dist _ rE UE (hdist σ hσ),
      Assn.unitaryPre_op_of_dist _ rE UE (hdist σ hσ), Assn.ofFam_op]
  · intro k
    exact DerivTot.unitary_identityMask rE UE _ fun σ hσ =>
      hdist σ (by rcases hσ with ⟨hk, hn⟩; omega)

/-! ## §4. The suffix family displayed as one conjugation -/

private theorem wpSuffixAux_op_conj {g : ℕ → Assn σT D → Assn σT D}
    {Y : Assn σT D} {n : ℕ} (G : ℕ → EndM D (univ : Finset L)) (σ : σT)
    (hg : ∀ j, j < n → ∀ A : Assn σT D, (g j A).op σ
      = LinearMap.adjoint (G j) ∘ₗ A.op σ ∘ₗ G j) :
    ∀ m k, m + k ≤ n → (wpSuffixAux g Y m k).op σ
      = LinearMap.adjoint (chainOp (List.range' k m) G) ∘ₗ Y.op σ ∘ₗ
          chainOp (List.range' k m) G
  | 0, k, _ => by
      rw [List.range'_zero, chainOp_nil, LinearMap.adjoint_one,
        Module.End.one_eq_id, LinearMap.id_comp, LinearMap.comp_id]
      rfl
  | m + 1, k, h => by
      change (g k (wpSuffixAux g Y m (k + 1))).op σ = _
      rw [hg k (by omega), wpSuffixAux_op_conj G σ hg m (k + 1) (by omega),
        List.range'_succ, chainOp_cons, LinearMap.adjoint_comp]
      simp only [LinearMap.comp_assoc]

/-- **The suffix-family display**, general entry point: when every `g j`
acts at `σ` as a conjugation by `G j`, the suffix precondition at counter
value `k` is one conjugation by the semantic chain operator of the ordered
remaining passes `k, …, n-1`.  The ℕ-indexed analogue of `foldr_op_conj`. -/
theorem wpSuffix_op_conj (g : ℕ → Assn σT D → Assn σT D) (n : ℕ)
    (Y : Assn σT D) (G : ℕ → EndM D (univ : Finset L)) (σ : σT)
    (hg : ∀ j, j < n → ∀ A : Assn σT D, (g j A).op σ
      = LinearMap.adjoint (G j) ∘ₗ A.op σ ∘ₗ G j) (k : ℕ) :
    (wpSuffix g n Y k).op σ
      = LinearMap.adjoint (chainOp (List.range' k (n - k)) G) ∘ₗ Y.op σ ∘ₗ
          chainOp (List.range' k (n - k)) G := by
  rcases Nat.lt_or_ge k n with h | h
  · exact wpSuffixAux_op_conj G σ hg (n - k) k (by omega)
  · rw [wpSuffix_of_ge h, show n - k = 0 from by omega, List.range'_zero,
      chainOp_nil, LinearMap.adjoint_one, Module.End.one_eq_id,
      LinearMap.id_comp, LinearMap.comp_id]

/-- **The loop-entry display**: the full suffix precondition of a counted
loop of conjugating passes is the single conjugation by the semantic chain
operator of the whole ordered pass list — the counted-`while` mirror of
`foldr_unitaryPre_const_op`. -/
theorem wpSuffix_zero_op_conj (g : ℕ → Assn σT D → Assn σT D) (n : ℕ)
    (Y : Assn σT D) (G : ℕ → EndM D (univ : Finset L)) (σ : σT)
    (hg : ∀ j, j < n → ∀ A : Assn σT D, (g j A).op σ
      = LinearMap.adjoint (G j) ∘ₗ A.op σ ∘ₗ G j) :
    (wpSuffix g n Y 0).op σ
      = LinearMap.adjoint (chainOp (List.range n) G) ∘ₗ Y.op σ ∘ₗ
          chainOp (List.range n) G := by
  have h := wpSuffix_op_conj g n Y G σ hg 0
  rwa [Nat.sub_zero, ← List.range_eq_range'] at h

/-! ## §5. Composition test: a two-gate chain

Not an example (no program-specific content) — the witness that (i) the
suffix family of two unitary passes collapses to the double conjugation,
both directly and through the `chainOp` display, and (ii) the packaged rule
derives the counted loop that runs the two gates with a store-read gate
family.  `#print axioms` on `toyDeriv` reports
`[propext, Classical.choice, Quot.sound]` (checked out of file). -/

namespace CountedWpTest

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)]
variable {kb : ℕ} (r : Reg L kb) (U : ℕ → UnitaryOp (TSpace D r.toFun))
variable (Y : Assn ℕ D) (hY : ∀ σ τ : ℕ, Y.op σ = Y.op τ)

/-- The literal-`k` transformer family: (Ax-Uni) at the constant register
with the `k`-th gate. -/
noncomputable def toyT (k : ℕ) (A : Assn ℕ D) : Assn ℕ D :=
  A.unitaryPre (RegExpr.const r) fun _ => U k

theorem toyT_op (k : ℕ) (A : Assn ℕ D) (σ : ℕ) :
    (toyT r U k A).op σ
      = LinearMap.adjoint (regLift r (U k)) ∘ₗ A.op σ ∘ₗ regLift r (U k) :=
  A.unitaryPre_op_of_dist (RegExpr.const r) (fun _ => U k) r.inj

/-- The two-pass suffix precondition is the double conjugation, by
unrolling. -/
theorem toyWp_op (σ : ℕ) :
    (wpSuffix (toyT r U) 2 Y 0).op σ
      = LinearMap.adjoint (regLift r (U 0)) ∘ₗ
          (LinearMap.adjoint (regLift r (U 1)) ∘ₗ Y.op σ ∘ₗ regLift r (U 1))
            ∘ₗ regLift r (U 0) := by
  rw [wpSuffix_of_lt (by omega : (0 : ℕ) < 2), toyT_op,
    wpSuffix_of_lt (by omega : (1 : ℕ) < 2), toyT_op, wpSuffix_full]

/-- The same collapse through the `chainOp` display. -/
theorem toyWp_op_chain (σ : ℕ) :
    (wpSuffix (toyT r U) 2 Y 0).op σ
      = LinearMap.adjoint (chainOp (List.range 2) fun k => regLift r (U k))
          ∘ₗ Y.op σ ∘ₗ chainOp (List.range 2) fun k => regLift r (U k) :=
  wpSuffix_zero_op_conj (toyT r U) 2 Y (fun k => regLift r (U k)) σ
    (fun k _ A => toyT_op r U k A σ)

include hY in
/-- The packaged rule on the two-gate counted loop whose gate is read from
the store (`U` at the current counter value): the suffix precondition of the
literal family derives the loop against `Y` at exit. -/
theorem toyDeriv :
    DerivTot (wpSuffix (toyT r U) 2 Y 0)
      (countedProg .nat (fun _ => 2)
        (.unitary kb (RegExpr.const r) fun σ => U σ))
      (Y.mask fun σ => CounterLens.nat.get σ = 2) := by
  refine DerivTot.countedWpChain_const CounterLens.nat (RegExpr.const r)
    (fun σ => U σ) (toyT r U) Y ?_ ?_ ?_
  · intro k A hA σ v
    rw [toyT_op, toyT_op, hA σ v]
  · intro σ v
    exact hY _ _
  · intro k _ σ hget A
    have hσ : σ = k := hget
    subst hσ
    rw [toyT_op,
      Assn.unitaryPre_op_of_dist A (RegExpr.const r) (fun σ => U σ) r.inj]
    rfl

end CountedWpTest

end Qhl
