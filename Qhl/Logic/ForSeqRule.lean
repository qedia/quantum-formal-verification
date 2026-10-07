import Qhl.Logic.Rules
import Qhl.Program.For

/-!
# The sequential (invariant-chain) `for`-loop rule of `QHL⁺_tot`

`Qhl/Logic/ForRule.lean` gives the **parallel** `for` rule
`DerivTot.forProg_parallelUnitary` (CoqQ `AxV_UTFP`, `qhl.v:2159`): it applies
only when the bodies touch **pairwise disjoint** wires (`l.Nodup`), so that the
loop is a tensor of independent gates and no invariant is needed. A loop whose
bodies **interact through shared wires** — QFT's controlled-phase ladder, where
every stage reads the wire the previous stage wrote — is *not* of that form. It
is a genuine `.seq`-chain and needs a **stage-indexed invariant chain**

```
J 0 → J 1 → … → J n,
```

one derivation per stage, chained by (R-Seq). This file is that rule: the
sequential counterpart of `AxV_UTFP`.

CoqQ discharges such loops by unrolling the `\big[seqc_/skip_]` fold with
`big_ord_recl`/`big_ord_recr` **inside its own proofs** — see the
`AxV_UTFP_seq`-style fold unrolling in `example/coqq_paper/qhl.v` and the QFT
stage lemma `RS_QFT_sub` in `example/coqq_paper/example.v`, which unrolls the
loop with `big_ord_recr` at the point of use. Here that induction is packaged
**once, in the library**, so an example never performs an induction over its
loop:

* `DerivTot.forProg_chain` — the general-index-list form: give a chain
  `J : ℕ → Assn σT D` and, for every position `k` of the list, a derivation
  taking `J k` to `J (k+1)` through the body at that position; the whole `for`
  fold then takes `J 0` to `J l.length`.
* `DerivTot.forProg_finRange_chain` — the corollary at `List.finRange n`, i.e.
  CoqQ's `[for i do C]` over all ordinals (`qwhile.v:459`), which is the shape
  QFT uses: `n` stage derivations `J i → J (i+1)` give `J 0 → J n`.

Both are derived **purely from the `DerivTot` constructors `.skip` and `.seq`**
— nothing else, no `conseq`, nothing quantum, no semantics — by structural
induction on the index list. A consumer discharges an interacting-wire `for`
loop with **one** application of the theorem plus one derivation per stage.

Everything is generic in the world `L`, the cell types `D`, the index type and
the classical state space `σT`; no example fixture and no particular gate
appears.
-/

namespace Qhl

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)]
variable {σT : Type*}

/-! ## §1. The invariant-chain rule over an arbitrary index list -/

/-- **The sequential `for`-loop rule of `QHL⁺_tot`** — the invariant-chain
counterpart of `DerivTot.forProg_parallelUnitary` (CoqQ `AxV_UTFP`,
`qhl.v:2159`), for loops whose bodies **share wires** and therefore cannot be
read as a tensor of independent gates.

Given a stage-indexed chain of assertions `J : ℕ → Assn σT D` and, for every
position `k` of the index list, a derivation

```
⊢ₜ {J k}  C (l.get ⟨k, hk⟩)  {J (k+1)}
```

the whole fold is derivable:

```
⊢ₜ {J 0}  for i in l do C i  {J l.length}.
```

This is exactly the `\big[seqc_/skip_]` unrolling that CoqQ performs with
`big_ord_recl`/`big_ord_recr` inside its own proofs (the `AxV_UTFP_seq`-style
fold unrolling of `example/coqq_paper/qhl.v`, and `RS_QFT_sub` in
`example/coqq_paper/example.v`), isolated once in the library so that no
example ever inducts over its loop.

The proof uses **only** the constructors `DerivTot.skip` and `DerivTot.seq`:
(Ax-Ski) at the empty list — where `[].length` reduces to `0` — and (R-Seq) at
a cons, recursing on the shifted chain `fun k => J (k+1)`. Nothing quantum, no
(R-Conseq), no semantics. -/
theorem DerivTot.forProg_chain {ι : Type*} {C : ι → Prog σT D} :
    ∀ (l : List ι) (J : ℕ → Assn σT D),
      (∀ k (hk : k < l.length), DerivTot (J k) (C (l.get ⟨k, hk⟩)) (J (k + 1))) →
      DerivTot (J 0) (Qhl.forProg l C) (J l.length)
  | [], J, _ => DerivTot.skip (J 0)
  | _ :: l, J, h =>
      DerivTot.seq (h 0 (Nat.succ_pos _))
        (DerivTot.forProg_chain l (fun k => J (k + 1))
          fun k hk => h (k + 1) (Nat.succ_lt_succ hk))

/-! ## §2. The `finRange` corollary (CoqQ's `[for i do C]`) -/

/-- **The stage-chain rule at `List.finRange n`** — CoqQ's `[for i do C]`, the
loop over all ordinals (`qwhile.v:459`), which is the shape QFT's
controlled-phase ladder takes. `n` stage derivations

```
⊢ₜ {J i}  C i  {J (i+1)}    (i : Fin n)
```

compose to the whole loop

```
⊢ₜ {J 0}  for i < n do C i  {J n}.
```

The chain `J` is indexed by `ℕ`, so `J i` above means `J (i : ℕ)` and `J (i+1)`
means `J ((i : ℕ) + 1)`: the casts are written out in the statement, and the
addition is addition in `ℕ`, **not** the wrap-around addition of `Fin n`.

This is `DerivTot.forProg_chain` transported along `List.length_finRange` and
`List.getElem_finRange`, hence — like it — derived from the `DerivTot`
constructors `.skip` and `.seq` alone. It is the direct analogue of CoqQ's
`big_ord_recr` unrolling in `RS_QFT_sub` (`example/coqq_paper/example.v`),
performed here once and for all: a consumer discharges its interacting-wire
loop with one application of this theorem plus one derivation per stage. -/
theorem DerivTot.forProg_finRange_chain {n : ℕ} {C : Fin n → Prog σT D} (J : ℕ → Assn σT D)
    (h : ∀ i : Fin n, DerivTot (J (i : ℕ)) (C i) (J ((i : ℕ) + 1))) :
    DerivTot (J 0) (Qhl.forProg (List.finRange n) C) (J n) := by
  have key : DerivTot (J 0) (Qhl.forProg (List.finRange n) C)
      (J (List.finRange n).length) := by
    refine DerivTot.forProg_chain (List.finRange n) J fun k hk => ?_
    have hkn : k < n := by rwa [List.length_finRange] at hk
    have hget : (List.finRange n).get ⟨k, hk⟩ = (⟨k, hkn⟩ : Fin n) := by
      simp [List.get_eq_getElem, List.getElem_finRange]
    rw [hget]
    exact h ⟨k, hkn⟩
  rwa [List.length_finRange] at key

end Qhl
