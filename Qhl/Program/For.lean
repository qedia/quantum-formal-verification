import Qhl.Program.Syntax

/-!
# The `for` loop as a fold of sequential composition

CoqQ's `for` loop is **not** a program primitive: it is notation for a big
operator over the existing sequential composition, with `skip` as the unit
(`example/coqq_paper/qwhile.v:441-459`),

```
[for i <- r do F] := \big[seqc_/skip_]_(i <- r) F
```

so a `for` loop over a finite index list is a finite `.seq`-chain that the
`qWhile⁺` syntax of `Qhl/Program/Syntax.lean` already expresses. `forProg`
below is that fold, verbatim: **no new `Prog` constructor**, hence no new
semantics, no new soundness obligation and no change to any existing file.

The counted `while` rendering of the same loop (a `ℕ`-valued loop counter in
the classical state, with the (R-Loop-tot) rule and a ranking function) remains
available and untouched; the fold
form is the one CoqQ reasons about, and it buys a loop rule that is pure
induction on the index list with no invariant and no ranking function
(`Qhl/Logic/ForRule.lean`).
-/

namespace Qhl

variable {σT : Type*} {L : Type*} {D : L → Type*}
  [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]

/-- CoqQ's `for` loop `[for i <- l do C i] = \big[seqc_/skip_]_(i <- l) C i`
(`qwhile.v:441-459`): the right fold of sequential composition over the index
list `l`, with `skip` as the unit. This is a finite `.seq`-chain built from the
existing constructors, **not** a new program primitive. -/
def forProg {ι : Type*} (l : List ι) (C : ι → Prog σT D) : Prog σT D :=
  l.foldr (fun i P => (C i).seq P) .skip

/-- CoqQ's `for`-loop notation `[for i <- r do F]` (`qwhile.v:441`), general
index-list form: `[for i in l do C]` is `forProg l (fun i => C)`, with `i`
bound in `C`. Pure surface syntax for the fold above. -/
scoped syntax:max (priority := high)
  "[" "for " Lean.binderIdent " in " termBeforeDo " do " term "]" : term

/-- CoqQ's `[for i do F]` — the loop over *all* ordinals (`qwhile.v:459`) —
as `[for i < n do C]`, i.e. `forProg (List.finRange n) (fun i => C)`; the
bound is written out so that the index type is determined by elaboration. -/
scoped syntax:max (priority := high)
  "[" "for " Lean.binderIdent " < " termBeforeDo " do " term "]" : term

scoped macro_rules
  | `([for $i:ident in $l do $C]) => `(Qhl.forProg $l fun $i => $C)
  | `([for _ in $l do $C]) => `(Qhl.forProg $l fun _ => $C)
  | `([for $i:ident < $n do $C]) => `(Qhl.forProg (List.finRange $n) fun $i => $C)
  | `([for _ < $n do $C]) => `(Qhl.forProg (List.finRange $n) fun _ => $C)

/-- The empty `for` loop is `skip` (CoqQ `big_nil`). -/
@[simp]
theorem forProg_nil {ι : Type*} (C : ι → Prog σT D) :
    forProg ([] : List ι) C = .skip := rfl

/-- One unrolling of the `for` fold (CoqQ `big_cons`): the head iteration
sequenced before the loop over the tail. -/
@[simp]
theorem forProg_cons {ι : Type*} (i : ι) (l : List ι) (C : ι → Prog σT D) :
    forProg (i :: l) C = (C i).seq (forProg l C) := rfl

end Qhl
