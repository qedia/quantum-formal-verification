import Qhl.Logic.Rules

/-!
# Derived rule: the counted `while` loop

The canonical bounded loop of `qWhile⁺`,

```
cnt := 0 ; while cnt < N do BODY ; cnt := cnt + 1 od
```

packaged as **one derived rule** (`DerivTot.countedWhile`), built
from (Ax-Ass) for the initialiser and the
trailing increment, (R-Seq), (R-Conseq), and the combined-premise total-loop extension
(`DerivTot.whileLoop`) with the ranking function `t σ = n - cnt σ`.  It factors
the hand-rolled derivation of `Qhl/Examples/ParallelHadamardTriple.lean` into
the library, so an example discharges a counted loop by supplying only the
**step family**: a derivation `{J k} BODY {J (k+1)}` (suitably masked) for each
counter value `k`. This weighted step family does not supply the source rule's
independent identity-predicate decrease derivation. The helper therefore remains
an extension; it must not be presented as derived using only the printed loop rule.

The source alternatives `countedWhileSource`, `countedWhile_constSource`, and
`countedWhileVarSource` take an unranked weighted body derivation and a separate
identity body derivation. They call `whileLoopSource` with an integer rank and
its nonnegativity proof. The variable-bound form allows nested loops whose bound
is read from a different counter. The older interfaces remain available for
retained developments.

Design decisions:

* **Counter lens.** The counter lives inside an arbitrary classical store
  `σT` through a `CounterLens` — `get`/`set` with the single law
  `get (set σ v) = v`.  Instances: `CounterLens.nat` (`σT = ℕ`),
  `CounterLens.fst`/`CounterLens.snd` (product stores, e.g. `σT = ℕ × ℕ` for a
  nested loop pair).  The invariant family must be insensitive to counter
  writes (`hJ : (J k).op (set σ v) = (J k).op σ`) — for the product lenses
  this is definitional when `J k` reads only the other component.

* **The increment is packaged.**  The step premise concerns `BODY` alone,
  pre-increment: both endpoints are masked to `get σ = k`; the rule appends
  the (Ax-Ass) instance for `cnt := cnt + 1` internally.

* **Exit by masking, not saturation.**  The loop invariant is
  `(Assn.ofFam get J).mask (fun σ => φ σ ∧ get σ ≤ n)`; at a false guard the
  mask pins `get σ = n`, so the conclusion's postcondition is
  `(J n).mask (fun σ => φ σ ∧ get σ = n)` with no `∀ k ≥ n, J k = J n`
  hypothesis.

* **Relativisation `φ` and a store-read bound `N`, for nesting.**  The
  program's guard reads a bound `N : σT → ℕ` from the store, and the whole
  rule is stated under a frame predicate `φ` (invariant under counter writes)
  that pins `N` to a literal `n`.  This is what lets the rule's conclusion be
  fed back as the step derivation of an **outer** counted loop: instantiating
  the inner rule at outer counter value `k` with
  `φ := fun σ => getOuter σ = k ∧ k < nOuter` handles both the
  outer-counter-dependent inner bound (QFT's ladder) and the vacuous outer
  ranking values (`φ` false makes every mask false, so the masked
  entailments close trivially).  The composition is exercised by the toy
  nested instance in the `CountedWhileTest` namespace below.

The flat corollary `DerivTot.countedWhile_const` (constant bound, `φ = True`)
is the shape a single loop (parallel Hadamard, QPE's accumulation) consumes;
`DerivTot.unitary_stepMask` discharges a one-gate step premise by
(Ax-Uni)+(R-Conseq) from a pointwise entailment under the mask.
-/

namespace Qhl

open Finset
open scoped NNReal ENNReal ComplexOrder

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)]
variable {σT : Type*}

/-! ## Counter lenses -/

/-- A counter lens: a `ℕ`-valued coordinate of the classical store, with the
read-after-write law.  This is the `StoreLens` idea specialised to the loop
counter, with the one law the counted-loop rule needs. -/
structure CounterLens (σT : Type*) where
  /-- Read the counter. -/
  get : σT → ℕ
  /-- Write the counter, keeping the rest of the store. -/
  set : σT → ℕ → σT
  /-- Read-after-write. -/
  get_set : ∀ σ v, get (set σ v) = v

namespace CounterLens

/-- The whole store is the counter (`σT = ℕ`). -/
def nat : CounterLens ℕ := ⟨fun σ => σ, fun _ v => v, fun _ _ => rfl⟩

/-- The left component of a product store is the counter. -/
def fst (R : Type*) : CounterLens (ℕ × R) :=
  ⟨Prod.fst, fun σ v => (v, σ.2), fun _ _ => rfl⟩

/-- The right component of a product store is the counter. -/
def snd (R : Type*) : CounterLens (R × ℕ) :=
  ⟨Prod.snd, fun σ v => (σ.1, v), fun _ _ => rfl⟩

/-- The first component of a triple store `ℕ × ℕ × R` is the counter. -/
def fst3 (R : Type*) : CounterLens (ℕ × ℕ × R) :=
  ⟨fun σ => σ.1, fun σ v => (v, σ.2), fun _ _ => rfl⟩

/-- The middle component of a triple store `ℕ × ℕ × R` is the counter. -/
def snd3 (R : Type*) : CounterLens (ℕ × ℕ × R) :=
  ⟨fun σ => σ.2.1, fun σ v => (σ.1, v, σ.2.2), fun _ _ => rfl⟩

end CounterLens

/-! ## The program shape -/

/-- The counted loop over the counter lens `c`:
`cnt := 0 ; while cnt < N do BODY ; cnt := cnt + 1 od`, with the bound `N`
read from the store (a literal bound is `N := fun _ => n`). -/
def countedProg (c : CounterLens σT) (N : σT → ℕ) (BODY : Prog σT D) :
    Prog σT D :=
  (Prog.assign fun σ => c.set σ 0).seq
    (Prog.while (fun σ => decide (c.get σ < N σ))
      (BODY.seq (Prog.assign fun σ => c.set σ (c.get σ + 1))))

/-! ## Assertion-side helpers -/

namespace Assn

/-- Read a counter-indexed assertion family at the counter value stored in
`σ` — the loop invariant of the counted-loop rule, before masking. -/
noncomputable def ofFam (g : σT → ℕ) (J : ℕ → Assn σT D) : Assn σT D :=
  ⟨fun σ => (J (g σ)).op σ, fun σ => (J (g σ)).isEffect σ⟩

omit [∀ i, Inhabited (D i)] in
@[simp] theorem ofFam_op (g : σT → ℕ) (J : ℕ → Assn σT D) (σ : σT) :
    (ofFam g J).op σ = (J (g σ)).op σ := rfl

/-- A unitary reads a counter-indexed assertion at the unchanged store. -/
theorem unitaryPre_ofFam_op (g : σT → ℕ) (J : ℕ → Assn σT D)
    {k : ℕ} (r : RegExpr σT L k) (U : ∀ σ, UnitaryOp (TSpace D (r σ))) (σ : σT) :
    ((ofFam g J).unitaryPre r U).op σ = ((J (g σ)).unitaryPre r U).op σ := by
  by_cases hd : Function.Injective (r σ)
  · rw [unitaryPre_op_of_dist _ r U hd, unitaryPre_op_of_dist _ r U hd, ofFam_op]
  · rw [unitaryPre_op_of_not_dist _ r U hd, unitaryPre_op_of_not_dist _ r U hd]

/-- Masks with pointwise-equivalent classical parts are equal. -/
theorem mask_congr {A : Assn σT D} {φ ψ : σT → Prop} (h : ∀ σ, φ σ ↔ ψ σ) :
    A.mask φ = A.mask ψ := by
  ext σ
  by_cases hσ : φ σ
  · rw [mask_op_of_pos hσ, mask_op_of_pos ((h σ).mp hσ)]
  · rw [mask_op_of_neg hσ, mask_op_of_neg fun hc => hσ ((h σ).mpr hc)]

/-- Drop a mask on the left of an entailment: it suffices to compare the
effects where the classical part holds (companion of `mask_le_mask`). -/
theorem mask_le_of_imp_le {A B : Assn σT D} {φ : σT → Prop}
    (h : ∀ σ, φ σ → A.op σ ≤ B.op σ) : A.mask φ ≤ B := by
  intro σ
  by_cases hσ : φ σ
  · rw [mask_op_of_pos hσ]; exact h σ hσ
  · exact op_zero_le (mask_op_of_neg hσ)

/-! The guard/mask bridges: inside a ranked loop body the assertions carry the
guard and the ranking mask as `(A.mand b).mask p`; the counted-chain layer
consumes a single conjunction mask.  The two shapes read the same effect at
every store, so they entail each other pointwise. -/

theorem mand_mask_le (A : Assn σT D) (b : σT → Bool) (p : σT → Prop) :
    (A.mand b).mask p ≤ A.mask fun σ => b σ = true ∧ p σ := by
  intro σ
  by_cases hp : p σ
  · by_cases hb : b σ = true
    · refine le_of_eq ?_
      rw [Assn.mask_op_of_pos (A := A.mand b) hp, Assn.mand_op_of_true hb,
        Assn.mask_op_of_pos (A := A) (show b σ = true ∧ p σ from ⟨hb, hp⟩)]
    · refine Assn.op_zero_le ?_
      rw [Assn.mask_op_of_pos (A := A.mand b) hp]
      exact Assn.mand_op_of_false (by simpa using hb)
  · exact Assn.op_zero_le (Assn.mask_op_of_neg (A := A.mand b) hp)

theorem le_mand_mask (A : Assn σT D) (b : σT → Bool) (p : σT → Prop) :
    (A.mask fun σ => b σ = true ∧ p σ) ≤ (A.mand b).mask p := by
  intro σ
  by_cases h : b σ = true ∧ p σ
  · refine le_of_eq ?_
    rw [Assn.mask_op_of_pos (A := A) h,
      Assn.mask_op_of_pos (A := A.mand b) h.2, Assn.mand_op_of_true h.1]
  · exact Assn.op_zero_le (Assn.mask_op_of_neg (A := A) h)

end Assn

/-! ## The proof obligations of the derived rule

Internals of `DerivTot.countedWhile`: the guard, the ranking function, the
masked loop invariant, and the four entailments (R-Conseq) consumes.  They are
stated over the rule's full hypothesis pack. -/

namespace CountedWhile

variable (c : CounterLens σT) (N : σT → ℕ) (n : ℕ) (φ : σT → Prop)
variable (J : ℕ → Assn σT D)

/-- The loop guard `cnt < N`. -/
def loopGuard : σT → Bool := fun σ => decide (c.get σ < N σ)

/-- The ranking function of the counted-loop extension: the passes still to run. -/
def rank : σT → ℕ := fun σ => n - c.get σ

/-- The loop invariant: the family read at the stored counter, masked to the
frame predicate and to `cnt ≤ n`. -/
noncomputable def inv : Assn σT D :=
  (Assn.ofFam c.get J).mask fun σ => φ σ ∧ c.get σ ≤ n

section Obligations

variable {c N n φ J}
variable (hφ : ∀ σ v, φ (c.set σ v) ↔ φ σ)
variable (hN : ∀ σ, φ σ → N σ = n)
variable (hJ : ∀ k σ v, (J k).op (c.set σ v) = (J k).op σ)

include hN in
/-- Entering the loop body at ranking value `m`: the masked invariant entails
the step premise at the counter value `n - m`. -/
private theorem front_le (m : ℕ) :
    ((inv c n φ J).mand (loopGuard c N)).mask (fun σ => rank c n σ = m)
      ≤ (J (n - m)).mask fun σ => φ σ ∧ c.get σ = n - m ∧ n - m < n := by
  intro σ
  by_cases hm : rank c n σ = m
  · rw [Assn.mask_op_of_pos (A := (inv c n φ J).mand (loopGuard c N))
      (φ := fun σ => rank c n σ = m) (σ := σ) hm]
    by_cases hg : loopGuard c N σ = true
    · rw [Assn.mand_op_of_true (A := inv c n φ J) (b := loopGuard c N)
        (σ := σ) hg]
      by_cases hj : φ σ ∧ c.get σ ≤ n
      · obtain ⟨hjφ, hjle⟩ := hj
        simp only [inv]
        rw [Assn.mask_op_of_pos (A := Assn.ofFam c.get J)
          (φ := fun σ => φ σ ∧ c.get σ ≤ n) (σ := σ) ⟨hjφ, hjle⟩,
          Assn.ofFam_op]
        have hgN : c.get σ < N σ := by
          simpa [loopGuard, decide_eq_true_eq] using hg
        have hlt : c.get σ < n := by rw [hN σ hjφ] at hgN; exact hgN
        simp only [rank] at hm
        have hget : c.get σ = n - m := by omega
        have hmn : n - m < n := by omega
        rw [Assn.mask_op_of_pos (A := J (n - m))
          (φ := fun σ => φ σ ∧ c.get σ = n - m ∧ n - m < n) (σ := σ)
          ⟨hjφ, hget, hmn⟩]
        exact le_of_eq (by rw [hget])
      · simp only [inv]
        exact Assn.op_zero_le (Assn.mask_op_of_neg (A := Assn.ofFam c.get J)
          (φ := fun σ => φ σ ∧ c.get σ ≤ n) (σ := σ) hj)
    · exact Assn.op_zero_le (Assn.mand_op_of_false (A := inv c n φ J)
        (b := loopGuard c N) (σ := σ) (by simpa using hg))
  · exact Assn.op_zero_le
      (Assn.mask_op_of_neg (A := (inv c n φ J).mand (loopGuard c N))
        (φ := fun σ => rank c n σ = m) (σ := σ) hm)

include hφ hJ in
/-- Leaving the loop body at ranking value `m`: the step conclusion entails
the (Ax-Ass) precondition of the trailing increment. -/
private theorem back_le (m : ℕ) :
    ((J (n - m + 1)).mask fun σ => φ σ ∧ c.get σ = n - m ∧ n - m < n)
      ≤ ((inv c n φ J).mask fun σ => rank c n σ < m).comp
          fun σ => c.set σ (c.get σ + 1) := by
  intro σ
  by_cases h : φ σ ∧ c.get σ = n - m ∧ n - m < n
  · obtain ⟨hφσ, hget, hmn⟩ := h
    rw [Assn.mask_op_of_pos (A := J (n - m + 1))
      (φ := fun σ => φ σ ∧ c.get σ = n - m ∧ n - m < n) (σ := σ)
      ⟨hφσ, hget, hmn⟩, Assn.comp_op]
    have hg' : c.get (c.set σ (c.get σ + 1)) = n - m + 1 := by
      rw [c.get_set, hget]
    have hr' : rank c n (c.set σ (c.get σ + 1)) < m := by
      simp only [rank, hg']; omega
    rw [Assn.mask_op_of_pos (A := inv c n φ J)
      (φ := fun σ => rank c n σ < m) (σ := c.set σ (c.get σ + 1)) hr']
    simp only [inv]
    have hle : c.get (c.set σ (c.get σ + 1)) ≤ n := by rw [hg']; omega
    rw [Assn.mask_op_of_pos (A := Assn.ofFam c.get J)
      (φ := fun σ => φ σ ∧ c.get σ ≤ n) (σ := c.set σ (c.get σ + 1))
      ⟨(hφ σ (c.get σ + 1)).mpr hφσ, hle⟩, Assn.ofFam_op, hg']
    exact le_of_eq (hJ (n - m + 1) σ (c.get σ + 1)).symm
  · exact Assn.op_zero_le (Assn.mask_op_of_neg (A := J (n - m + 1))
      (φ := fun σ => φ σ ∧ c.get σ = n - m ∧ n - m < n) (σ := σ) h)

include hφ hJ in
/-- Entering the loop: the relativised `J 0` entails the (Ax-Ass)
precondition of the initialiser `cnt := 0`. -/
private theorem entry_le :
    (J 0).mask φ ≤ (inv c n φ J).comp fun σ => c.set σ 0 := by
  intro σ
  by_cases hφσ : φ σ
  · rw [Assn.mask_op_of_pos (A := J 0) (φ := φ) (σ := σ) hφσ, Assn.comp_op]
    simp only [inv]
    have h0 : c.get (c.set σ 0) = 0 := c.get_set σ 0
    rw [Assn.mask_op_of_pos (A := Assn.ofFam c.get J)
      (φ := fun σ => φ σ ∧ c.get σ ≤ n) (σ := c.set σ 0)
      ⟨(hφ σ 0).mpr hφσ, by rw [h0]; exact Nat.zero_le n⟩,
      Assn.ofFam_op, h0]
    exact le_of_eq (hJ 0 σ 0).symm
  · exact Assn.op_zero_le
      (Assn.mask_op_of_neg (A := J 0) (φ := φ) (σ := σ) hφσ)

include hN in
/-- Leaving the loop: at a false guard the masked invariant pins the counter
to `n` exactly. -/
private theorem exit_le :
    (inv c n φ J).mandNot (loopGuard c N)
      ≤ (J n).mask fun σ => φ σ ∧ c.get σ = n := by
  intro σ
  by_cases hg : loopGuard c N σ = true
  · exact Assn.op_zero_le (Assn.mandNot_op_of_true (A := inv c n φ J)
      (b := loopGuard c N) (σ := σ) hg)
  · rw [Assn.mandNot_op_of_false (A := inv c n φ J) (b := loopGuard c N)
      (σ := σ) (by simpa using hg)]
    by_cases hj : φ σ ∧ c.get σ ≤ n
    · obtain ⟨hjφ, hjle⟩ := hj
      have hge : ¬ c.get σ < N σ := by
        simpa [loopGuard, decide_eq_true_eq] using hg
      have hn : c.get σ = n := by rw [hN σ hjφ] at hge; omega
      simp only [inv]
      rw [Assn.mask_op_of_pos (A := Assn.ofFam c.get J)
        (φ := fun σ => φ σ ∧ c.get σ ≤ n) (σ := σ) ⟨hjφ, hjle⟩,
        Assn.ofFam_op, hn,
        Assn.mask_op_of_pos (A := J n)
          (φ := fun σ => φ σ ∧ c.get σ = n) (σ := σ) ⟨hjφ, hn⟩]
    · simp only [inv]
      exact Assn.op_zero_le (Assn.mask_op_of_neg (A := Assn.ofFam c.get J)
        (φ := fun σ => φ σ ∧ c.get σ ≤ n) (σ := σ) hj)

end Obligations

end CountedWhile

/-! ## The derived rules -/

open CountedWhile in
/-- **The counted-`while` rule** (derived using the combined-premise extension):
for a counter lens `c`, a bound `N` read from the store but pinned to the
literal `n` under the frame predicate `φ`, and an invariant family `J`
insensitive to counter writes, the step family

`{(J k) ∧ φ ∧ cnt = k ∧ k < n} BODY {(J (k+1)) ∧ φ ∧ cnt = k ∧ k < n}`

derives

`{(J 0) ∧ φ} cnt := 0 ; while cnt < N do BODY ; cnt := cnt + 1 od
{(J n) ∧ φ ∧ cnt = n}`.

The trailing increment's (Ax-Ass) is packaged here, the ranking function is
`t σ = n - cnt σ`, and the loop is closed by the combined-premise extension
(`DerivTot.whileLoop`).  For `k ≥ n` the step masks are everywhere false, so
a step derivation ending in an axiom — or in this rule's own conclusion,
relativised through `φ` — discharges them without extra content. -/
theorem DerivTot.countedWhile (c : CounterLens σT) {N : σT → ℕ} {n : ℕ}
    {φ : σT → Prop} {J : ℕ → Assn σT D} {BODY : Prog σT D}
    (hφ : ∀ σ v, φ (c.set σ v) ↔ φ σ)
    (hN : ∀ σ, φ σ → N σ = n)
    (hJ : ∀ k σ v, (J k).op (c.set σ v) = (J k).op σ)
    (hstep : ∀ k, DerivTot ((J k).mask fun σ => φ σ ∧ c.get σ = k ∧ k < n)
      BODY ((J (k + 1)).mask fun σ => φ σ ∧ c.get σ = k ∧ k < n)) :
    DerivTot ((J 0).mask φ) (countedProg c N BODY)
      ((J n).mask fun σ => φ σ ∧ c.get σ = n) :=
  DerivTot.conseq (entry_le hφ hJ)
    (DerivTot.seq (DerivTot.assign _ (inv c n φ J))
      (DerivTot.whileLoop (rank c n) fun m =>
        DerivTot.seq
          (DerivTot.conseq (front_le hN m) (hstep (n - m)) (back_le hφ hJ m))
          (DerivTot.assign _ ((inv c n φ J).mask fun σ => rank c n σ < m))))
    (exit_le hN)

/-- The counted-`while` rule for a flat loop: literal bound, no frame
predicate.  The step family is

`{(J k) ∧ cnt = k ∧ k < n} BODY {(J (k+1)) ∧ cnt = k ∧ k < n}`

and the conclusion is
`{J 0} cnt := 0 ; while cnt < n do BODY ; cnt := cnt + 1 od
{(J n) ∧ cnt = n}`. -/
theorem DerivTot.countedWhile_const (c : CounterLens σT) {n : ℕ}
    {J : ℕ → Assn σT D} {BODY : Prog σT D}
    (hJ : ∀ k σ v, (J k).op (c.set σ v) = (J k).op σ)
    (hstep : ∀ k, DerivTot ((J k).mask fun σ => c.get σ = k ∧ k < n)
      BODY ((J (k + 1)).mask fun σ => c.get σ = k ∧ k < n)) :
    DerivTot (J 0) (countedProg c (fun _ => n) BODY)
      ((J n).mask fun σ => c.get σ = n) := by
  have h := DerivTot.countedWhile (φ := fun _ => True) (N := fun _ => n) c
    (fun _ _ => Iff.rfl) (fun _ _ => rfl) hJ
    (fun k => DerivTot.conseq
      (Assn.mask_le_mask (A := J k) (B := J k)
        (φ := fun σ => True ∧ c.get σ = k ∧ k < n)
        (ψ := fun σ => c.get σ = k ∧ k < n)
        (fun _ hσ => hσ.2) (fun _ _ => le_rfl))
      (hstep k)
      (Assn.mask_le_mask (A := J (k + 1)) (B := J (k + 1))
        (φ := fun σ => c.get σ = k ∧ k < n)
        (ψ := fun σ => True ∧ c.get σ = k ∧ k < n)
        (fun _ hσ => ⟨trivial, hσ⟩) (fun _ _ => le_rfl)))
  refine DerivTot.conseq (fun σ => ?_) h (fun σ => ?_)
  · exact le_of_eq (Assn.mask_op_of_pos trivial).symm
  · by_cases hn : c.get σ = n
    · exact le_of_eq
        (by rw [Assn.mask_op_of_pos ⟨trivial, hn⟩,
          Assn.mask_op_of_pos (A := J n) (φ := fun σ => c.get σ = n)
            (σ := σ) hn])
    · exact Assn.op_zero_le (Assn.mask_op_of_neg fun hc => hn hc.2)

/-- Discharge a one-gate step premise of the counted-`while` rule by
(Ax-Uni)+(R-Conseq): it suffices to check the transformed effect where the
step mask holds. -/
theorem DerivTot.unitary_stepMask {k : ℕ} (r : RegExpr σT L k)
    (U : ∀ σ, UnitaryOp (TSpace D (r σ))) {A B : Assn σT D} {φ : σT → Prop}
    (h : ∀ σ, φ σ → A.op σ ≤ ((B.mask φ).unitaryPre r U).op σ) :
    DerivTot (A.mask φ) (.unitary k r U) (B.mask φ) :=
  DerivTot.conseq (Assn.mask_le_of_imp_le h)
    (DerivTot.unitary r U (B.mask φ)) (Assn.le_refl' _)

/-- A unitary preserves an identity assertion masked by a classical predicate.
Only register distinctness on that predicate is required. -/
theorem DerivTot.unitary_identityMask {k : ℕ} (r : RegExpr σT L k)
    (U : ∀ σ, UnitaryOp (TSpace D (r σ))) (φ : σT → Prop)
    (hd : ∀ σ, φ σ → Function.Injective (r σ)) :
    DerivTot ((Assn.one : Assn σT D).mask φ) (.unitary k r U)
      (Assn.one.mask φ) := by
  refine DerivTot.conseq (Assn.mask_le_of_imp_le ?_)
    (DerivTot.unitary r U _) (Assn.le_refl' _)
  intro σ hσ
  refine Assn.le_op_of_eq_one ?_
  rw [Assn.unitaryPre_op_of_dist _ r U (hd σ hσ), Assn.mask_op_of_pos hσ,
    Assn.one_op, Module.End.one_eq_id, LinearMap.id_comp]
  exact (isUnitary_regLift ⟨r σ, hd σ hσ⟩ (U σ)).1

/-- Identity-mask preservation for a unitary, with an implicit predicate. -/
theorem DerivTot.unitary_identity_mask {k : ℕ} {φ : σT → Prop}
    (r : RegExpr σT L k) (U : ∀ σ, UnitaryOp (TSpace D (r σ)))
    (hdist : ∀ σ, φ σ → Function.Injective (r σ)) :
    DerivTot ((Assn.one : Assn σT D).mask φ) (.unitary k r U)
      (Assn.one.mask φ) :=
  DerivTot.unitary_identityMask r U φ hdist

open CountedWhile in
/-- Counted iteration derived from the source total-loop constructor.
The weighted body premise uses the family at the current counter; the separate
identity premise preserves the classical frame and counter on every input. -/
theorem DerivTot.countedWhileSource (c : CounterLens σT) {N : σT → ℕ} {n : ℕ}
    {φ : σT → Prop} {J : ℕ → Assn σT D} {BODY : Prog σT D}
    (hφ : ∀ σ v, φ (c.set σ v) ↔ φ σ)
    (hN : ∀ σ, φ σ → N σ = n)
    (hJ : ∀ k σ v, (J k).op (c.set σ v) = (J k).op σ)
    (hstep : DerivTot ((Assn.ofFam c.get J).mask fun σ => φ σ ∧ c.get σ < n)
      BODY ((Assn.ofFam c.get (fun k => J (k + 1))).mask
        fun σ => φ σ ∧ c.get σ < n))
    (hidentity : ∀ k, DerivTot ((Assn.one : Assn σT D).mask
        fun σ => φ σ ∧ c.get σ = k ∧ k < n)
      BODY (Assn.one.mask fun σ => φ σ ∧ c.get σ = k ∧ k < n)) :
    DerivTot ((J 0).mask φ) (countedProg c N BODY)
      ((J n).mask fun σ => φ σ ∧ c.get σ = n) := by
  have hi : DerivTot ((inv c n φ J).mand (loopGuard c N))
      (BODY.seq (.assign fun σ => c.set σ (c.get σ + 1))) (inv c n φ J) := by
    refine DerivTot.seq (DerivTot.conseq ?_ hstep ?_) (DerivTot.assign _ _)
    · intro σ
      by_cases hg : loopGuard c N σ = true
      · rw [Assn.mand_op_of_true hg]
        by_cases hσ : φ σ ∧ c.get σ ≤ n
        · have hlt : c.get σ < n := by
            have hg : c.get σ < N σ := by simpa [loopGuard] using hg
            simpa [hN σ hσ.1] using hg
          change ((Assn.ofFam c.get J).mask _).op σ ≤ _
          rw [Assn.mask_op_of_pos (φ := fun σ => φ σ ∧ c.get σ ≤ n) hσ,
            Assn.mask_op_of_pos (φ := fun σ => φ σ ∧ c.get σ < n) ⟨hσ.1, hlt⟩]
        · exact Assn.op_zero_le (Assn.mask_op_of_neg hσ)
      · exact Assn.op_zero_le (Assn.mand_op_of_false (by simpa using hg))
    · apply Assn.mask_le_of_imp_le
      intro σ hσ
      rw [Assn.comp_op]
      change (J (c.get σ + 1)).op σ ≤
        ((Assn.ofFam c.get J).mask fun τ => φ τ ∧ c.get τ ≤ n).op _
      rw [Assn.mask_op_of_pos ⟨(hφ σ _).mpr hσ.1, by rw [c.get_set]; omega⟩,
        Assn.ofFam_op, c.get_set, hJ]
  have hr (z : Int) : DerivTot ((Assn.one : Assn σT D).mask fun σ =>
      (φ σ ∧ c.get σ ≤ n) ∧ loopGuard c N σ = true ∧ (rank c n σ : Int) = z)
      (BODY.seq (.assign fun σ => c.set σ (c.get σ + 1)))
      (Assn.one.mask fun σ => (rank c n σ : Int) < z) := by
    refine DerivTot.seq (DerivTot.conseq ?_ (hidentity (n - z.toNat)) ?_)
      (DerivTot.assign _ _)
    · apply Assn.mask_le_mask (A := (Assn.one : Assn σT D))
        (B := Assn.one) _ (fun _ _ => le_rfl)
      intro σ hσ
      have hg : c.get σ < n := by
        have hg : c.get σ < N σ := by simpa [loopGuard] using hσ.2.1
        simpa [hN σ hσ.1.1] using hg
      have he := hσ.2.2
      simp only [rank] at he
      exact ⟨hσ.1.1, by omega, by omega⟩
    · apply Assn.mask_le_of_imp_le
      intro σ hσ
      rw [Assn.comp_op, Assn.mask_op_of_pos (by
        simp only [rank, c.get_set]
        omega)]
      exact le_rfl
  exact DerivTot.conseq (entry_le hφ hJ)
    (DerivTot.seq (DerivTot.assign _ _)
      (DerivTot.whileLoopSource (A := Assn.ofFam c.get J)
        (φ := fun σ => φ σ ∧ c.get σ ≤ n) (fun σ => (rank c n σ : Int))
        (fun _ _ => Int.natCast_nonneg _) hi hr)) (exit_le hN)

/-- The source counted-loop rule with a constant bound and no frame predicate. -/
theorem DerivTot.countedWhile_constSource (c : CounterLens σT) {n : ℕ}
    {J : ℕ → Assn σT D} {BODY : Prog σT D}
    (hJ : ∀ k σ v, (J k).op (c.set σ v) = (J k).op σ)
    (hstep : DerivTot ((Assn.ofFam c.get J).mask fun σ => c.get σ < n)
      BODY ((Assn.ofFam c.get (fun k => J (k + 1))).mask fun σ => c.get σ < n))
    (hidentity : ∀ k, DerivTot ((Assn.one : Assn σT D).mask
        fun σ => c.get σ = k ∧ k < n)
      BODY (Assn.one.mask fun σ => c.get σ = k ∧ k < n)) :
    DerivTot (J 0) (countedProg c (fun _ => n) BODY)
      ((J n).mask fun σ => c.get σ = n) := by
  have h := DerivTot.countedWhileSource (φ := fun _ => True) (N := fun _ => n) c
    (fun _ _ => Iff.rfl) (fun _ _ => rfl) hJ
    (by simpa only [true_and] using hstep)
    (fun k => by simpa only [true_and] using hidentity k)
  have ht : (J 0).mask (fun _ => True) = J 0 := by ext σ; simp
  simpa only [true_and, ht] using h

/-- Assignment preserves an identity mask when its update preserves the
classical predicate. -/
theorem DerivTot.assign_identityMask (f : σT → σT) (φ : σT → Prop)
    (hφ : ∀ σ, φ σ → φ (f σ)) :
    DerivTot ((Assn.one : Assn σT D).mask φ) (.assign f) (Assn.one.mask φ) := by
  refine DerivTot.conseq (Assn.mask_le_of_imp_le ?_) (DerivTot.assign f _)
    (Assn.le_refl' _)
  intro σ hσ
  rw [Assn.comp_op, Assn.mask_op_of_pos (hφ σ hσ)]
  exact le_rfl

/-- The source counted-loop rule for a bound read from the store. The body
preserves the identity assertion at each integer value of the remaining count. -/
theorem DerivTot.countedWhileVarSource (c : CounterLens σT) {N : σT → ℕ}
    {φ : σT → Prop} {J : ℕ → Assn σT D} {BODY : Prog σT D}
    (hφ : ∀ σ v, φ (c.set σ v) ↔ φ σ)
    (hN : ∀ σ v, N (c.set σ v) = N σ)
    (hJ : ∀ k σ v, (J k).op (c.set σ v) = (J k).op σ)
    (hstep : DerivTot ((Assn.ofFam c.get J).mask fun σ => φ σ ∧ c.get σ < N σ)
      BODY ((Assn.ofFam c.get (fun k => J (k + 1))).mask
        fun σ => φ σ ∧ c.get σ < N σ))
    (hidentity : ∀ z : Int, DerivTot ((Assn.one : Assn σT D).mask
        fun σ => φ σ ∧ c.get σ < N σ ∧ ((N σ - c.get σ : ℕ) : Int) = z)
      BODY (Assn.one.mask
        fun σ => φ σ ∧ c.get σ < N σ ∧ ((N σ - c.get σ : ℕ) : Int) = z)) :
    DerivTot ((J 0).mask φ) (countedProg c N BODY)
      ((Assn.ofFam N J).mask fun σ => φ σ ∧ c.get σ = N σ) := by
  let I : Assn σT D := (Assn.ofFam c.get J).mask fun σ => φ σ ∧ c.get σ ≤ N σ
  let b := CountedWhile.loopGuard c N
  let t : σT → Int := fun σ => (N σ - c.get σ : ℕ)
  have hi : DerivTot (I.mand b)
      (BODY.seq (.assign fun σ => c.set σ (c.get σ + 1))) I := by
    refine DerivTot.seq (DerivTot.conseq ?_ hstep ?_) (DerivTot.assign _ _)
    · intro σ
      by_cases hg : b σ = true
      · rw [Assn.mand_op_of_true hg]
        have hlt : c.get σ < N σ := by simpa [b, CountedWhile.loopGuard] using hg
        by_cases hσ : φ σ ∧ c.get σ ≤ N σ
        · change ((Assn.ofFam c.get J).mask _).op σ ≤ _
          rw [Assn.mask_op_of_pos (φ := fun σ => φ σ ∧ c.get σ ≤ N σ) hσ,
            Assn.mask_op_of_pos (φ := fun σ => φ σ ∧ c.get σ < N σ) ⟨hσ.1, hlt⟩]
        · exact Assn.op_zero_le (Assn.mask_op_of_neg hσ)
      · exact Assn.op_zero_le (Assn.mand_op_of_false (by simpa using hg))
    · apply Assn.mask_le_of_imp_le
      intro σ hσ
      rw [Assn.comp_op]
      change (J (c.get σ + 1)).op σ ≤
        ((Assn.ofFam c.get J).mask fun τ => φ τ ∧ c.get τ ≤ N τ).op _
      rw [Assn.mask_op_of_pos ⟨(hφ σ _).mpr hσ.1, by rw [c.get_set, hN]; omega⟩,
        Assn.ofFam_op, c.get_set, hJ]
  have hr (z : Int) : DerivTot ((Assn.one : Assn σT D).mask fun σ =>
      (φ σ ∧ c.get σ ≤ N σ) ∧ b σ = true ∧ t σ = z)
      (BODY.seq (.assign fun σ => c.set σ (c.get σ + 1)))
      (Assn.one.mask fun σ => t σ < z) := by
    refine DerivTot.seq (DerivTot.conseq ?_ (hidentity z) ?_) (DerivTot.assign _ _)
    · apply Assn.mask_le_mask (A := (Assn.one : Assn σT D))
        (B := Assn.one) _ (fun _ _ => le_rfl)
      intro σ hσ
      exact ⟨hσ.1.1, by simpa [b, CountedWhile.loopGuard] using hσ.2.1, hσ.2.2⟩
    · apply Assn.mask_le_of_imp_le
      intro σ hσ
      rw [Assn.comp_op, Assn.mask_op_of_pos (by
        simp only [t, c.get_set, hN]
        omega)]
      exact le_rfl
  refine DerivTot.conseq ?_
    (DerivTot.seq (DerivTot.assign _ I)
      (DerivTot.whileLoopSource (A := Assn.ofFam c.get J)
        (φ := fun σ => φ σ ∧ c.get σ ≤ N σ) t
        (fun _ _ => Int.natCast_nonneg _) hi hr)) ?_
  · apply Assn.mask_le_of_imp_le
    intro σ hσ
    rw [Assn.comp_op]
    change (J 0).op σ ≤
      ((Assn.ofFam c.get J).mask fun τ => φ τ ∧ c.get τ ≤ N τ).op _
    rw [Assn.mask_op_of_pos ⟨(hφ σ 0).mpr hσ, by rw [c.get_set]; exact Nat.zero_le _⟩,
      Assn.ofFam_op, c.get_set, hJ]
  · intro σ
    change (I.mandNot b).op σ ≤ _
    by_cases hg : b σ = true
    · exact Assn.op_zero_le (Assn.mandNot_op_of_true hg)
    · rw [Assn.mandNot_op_of_false (b := b) (by simpa using hg)]
      by_cases hσ : φ σ ∧ c.get σ ≤ N σ
      · have he : c.get σ = N σ := by
          have hge : ¬ c.get σ < N σ := by simpa [b, CountedWhile.loopGuard] using hg
          omega
        change ((Assn.ofFam c.get J).mask _).op σ ≤ _
        rw [Assn.mask_op_of_pos (φ := fun σ => φ σ ∧ c.get σ ≤ N σ) hσ,
          Assn.mask_op_of_pos (φ := fun σ => φ σ ∧ c.get σ = N σ) ⟨hσ.1, he⟩,
          Assn.ofFam_op, Assn.ofFam_op, he]
      · exact Assn.op_zero_le (Assn.mask_op_of_neg hσ)

/-- A source-derived counted loop preserves an identity assertion on its
classical frame, when its body preserves that frame and the counter masks. -/
theorem DerivTot.countedIdentitySource (c : CounterLens σT) {N : σT → ℕ} {n : ℕ}
    {φ : σT → Prop} {BODY : Prog σT D}
    (hφ : ∀ σ v, φ (c.set σ v) ↔ φ σ)
    (hN : ∀ σ, φ σ → N σ = n)
    (hbody : DerivTot ((Assn.one : Assn σT D).mask fun σ => φ σ ∧ c.get σ < n)
      BODY (Assn.one.mask fun σ => φ σ ∧ c.get σ < n))
    (hrank : ∀ k, DerivTot ((Assn.one : Assn σT D).mask
        fun σ => φ σ ∧ c.get σ = k ∧ k < n)
      BODY (Assn.one.mask fun σ => φ σ ∧ c.get σ = k ∧ k < n)) :
    DerivTot ((Assn.one : Assn σT D).mask φ) (countedProg c N BODY)
      (Assn.one.mask φ) := by
  have h := DerivTot.countedWhileSource c (J := fun _ => (Assn.one : Assn σT D))
    hφ hN (fun _ _ _ => rfl) hbody hrank
  exact DerivTot.conseq (Assn.le_refl' _) h
    (Assn.mask_le_mask (fun _ h => h.1) (fun _ _ => le_rfl))

/-- Identity-frame preservation for a source-derived counted loop whose bound
is read from the store. -/
theorem DerivTot.countedIdentityVarSource (c : CounterLens σT) {N : σT → ℕ}
    {φ : σT → Prop} {BODY : Prog σT D}
    (hφ : ∀ σ v, φ (c.set σ v) ↔ φ σ)
    (hN : ∀ σ v, N (c.set σ v) = N σ)
    (hbody : DerivTot ((Assn.one : Assn σT D).mask fun σ => φ σ ∧ c.get σ < N σ)
      BODY (Assn.one.mask fun σ => φ σ ∧ c.get σ < N σ))
    (hrank : ∀ z : Int, DerivTot ((Assn.one : Assn σT D).mask
        fun σ => φ σ ∧ c.get σ < N σ ∧ ((N σ - c.get σ : ℕ) : Int) = z)
      BODY (Assn.one.mask
        fun σ => φ σ ∧ c.get σ < N σ ∧ ((N σ - c.get σ : ℕ) : Int) = z)) :
    DerivTot ((Assn.one : Assn σT D).mask φ) (countedProg c N BODY)
      (Assn.one.mask φ) := by
  have h := DerivTot.countedWhileVarSource c (J := fun _ => (Assn.one : Assn σT D))
    hφ hN (fun _ _ _ => rfl) hbody hrank
  exact DerivTot.conseq (Assn.le_refl' _) h
    (Assn.mask_le_mask (fun _ h => h.1) (fun _ _ => le_rfl))

/-! ## Composition test: two nested counted loops

Not an example (no program-specific content) — the witness that the rule's
conclusion feeds back as the step derivation of an outer counted loop, with
the inner bound read from the outer counter.  Store `σT = ℕ × ℕ`: the outer
counter is the left component, the inner counter the right, the inner bound
is the current outer counter value, both bodies `skip`, the invariant a
store-constant assertion.  `#print axioms CountedWhileTest.toyDeriv` reports
`[propext, Classical.choice, Quot.sound]`. -/

namespace CountedWhileTest

variable (A : Assn (ℕ × ℕ) D) (hA : ∀ σ τ : ℕ × ℕ, A.op σ = A.op τ)

/-- Two nested counted loops of `skip`s; the inner bound is the outer
counter. -/
def toyProg (n : ℕ) : Prog (ℕ × ℕ) D :=
  countedProg (.fst ℕ) (fun _ => n)
    (countedProg (.snd ℕ) (fun σ => σ.1) .skip)

include hA in
/-- The inner loop, derived at outer counter value `k`: the main rule with
frame predicate `φ σ = (σ.1 = k ∧ k < n)`, which pins the store-read inner
bound to the literal `k`. -/
theorem innerDeriv (n k : ℕ) :
    DerivTot (A.mask fun σ => σ.1 = k ∧ k < n)
      (countedProg (.snd ℕ) (fun σ : ℕ × ℕ => σ.1) .skip)
      (A.mask fun σ => (σ.1 = k ∧ k < n) ∧ σ.2 = k) :=
  DerivTot.countedWhile (CounterLens.snd ℕ) (n := k)
    (φ := fun σ => σ.1 = k ∧ k < n) (J := fun _ => A)
    (fun _ _ => Iff.rfl) (fun _ hσ => hσ.1) (fun _ _ _ => hA _ _)
    (fun _ => DerivTot.skip _)

include hA in
/-- The nested composition: the outer loop consumes `innerDeriv` as its step
derivation, adjusted by one (R-Conseq). -/
theorem toyDeriv (n : ℕ) :
    DerivTot A (toyProg n) (A.mask fun σ => σ.1 = n) :=
  DerivTot.countedWhile_const (CounterLens.fst ℕ) (J := fun _ => A)
    (fun _ _ _ => hA _ _)
    (fun k => DerivTot.conseq (Assn.le_refl' _) (innerDeriv A hA n k)
      (Assn.mask_le_mask (A := A) (B := A)
        (φ := fun σ => (σ.1 = k ∧ k < n) ∧ σ.2 = k)
        (ψ := fun σ => σ.1 = k ∧ k < n)
        (fun _ hσ => hσ.1) (fun _ _ => le_rfl)))

end CountedWhileTest

end Qhl
