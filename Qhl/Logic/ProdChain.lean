import Qhl.Logic.ForSeqRule
import Qhl.Logic.Frame

/-!
# The derived structural combinators of `QHL⁺_tot` at product-state endpoints

CoqQ never writes the plumbing of a state triple by hand. Its case studies read
like the algorithm because four *derived* lemmas are ambient:

| CoqQ (`example/coqq_paper/qhl.v`) | statement |
|---|---|
| `RS_forward` (`:1594`) | `R = Q → ⊨s {P} c {R} → ⊨s {P} c {Q}` |
| `RS_back` (`:1599`) | `R = P → ⊨s {R} c {Q} → ⊨s {P} c {Q}` |
| `RS_SC` (`:1719`) | `⊨s {P} c₁ {Q} → ⊨s {Q} c₂ {R} → ⊨s {P} c₁;;c₂ {R}` |
| `RV_Frame` (`:1815`) | `⊨s {P} c {Q} → ⊨s {P ⊗ R} c {Q ⊗ R}` (`R` a ket) |

so that a stage of `RS_QFT_sub`/`RS_QFT_iter`/`RS_rev_circuit`
(`example/coqq_paper/example.v:260-345`) is *one* `apply` plus the state
algebra: the endpoints are bare kets `'|v; s⟩`, an equality of states is
consumed by `RS_forward`/`RS_back` with no assertion-level bookkeeping, and the
untouched wires are absorbed by `RV_Frame`.

This file is that ambient layer, here:

* `prodA` — the **bare-ket assertion** `∣⊗ᵢ ψᵢ⟩⟨⊗ᵢ ψᵢ∣` of a product state, i.e.
  the endpoint shape of CoqQ's `⊨s {P} c {Q}` with `P`, `Q` kets. It packages
  `Assn.ofState` together with the norm side condition `norm_prodV_eq_one`, which
  therefore never has to be written at a use site.
* `prodA_le`, `prodA_le_of_forall` — CoqQ's `RS_forward`/`RS_back` hypothesis
  `R = Q` reduced to the entailment `≤` that (R-Conseq) consumes: the norm
  witnesses are proofs and carry no information, so an *equality of states* — or
  even a pointwise one — is all a recast needs.
* `DerivTot.prodForward`, `DerivTot.prodBack` — `RS_forward` and `RS_back`
  themselves, as one-call recasts of a derivation's postcondition resp.
  precondition along an equality of state families.
* `DerivTot.forProg_prodChain` — `RS_forward` fused with the **sequential**
  `for`-rule `DerivTot.forProg_finRange_chain` (`Qhl/Logic/ForSeqRule.lean`):
  give a stage-indexed *family of product states* with its two endpoint
  identities and one derivation per stage, and the whole loop is discharged.
  This absorbs the entry/exit (R-Conseq) frame and every `Assn.ofState` / norm
  wrapper that otherwise surrounds a loop.
* `DerivTot.prodRung_pair`, `DerivTot.prodRung_single` — one gate step of such a
  chain: `RV_Frame` + (Ax-Uni) + both (R-Conseq)s in a single call, at a pair of
  cells resp. at one cell. The gate hypothesis stays *inside the gate's own
  world* (`DerivTot.unitary_pair_prodV`, `Qhl/Logic/Frame.lean`), and the
  state-algebra step `hstep` is given as a plain equality of families.

**Nothing is postulated.** Every declaration below is derived from
`DerivTot.conseq` (R-Conseq), `DerivTot.forProg_finRange_chain`,
`DerivTot.unitary_pair_prodV` and `DerivTot.unitary1_prodV` — themselves built
from the `DerivTot` constructors alone — plus `Assn.ofState_le_ofState`: no new
axiom, no new rule primitive, no appeal to soundness, and `DerivTot`,
`validTot` and `DerivTot.sound` are untouched.

**Ownership test.** No program, gate or example fixture is named here:
everything is generic in the world `L`, the cell-type family `D`, the gate, the
state families and the classical state space `σT`. The combinators are therefore
reusable verbatim by the inverse QFT, by QPE (whose stage adapters are chains of
exactly this shape) and by any repeat-until-success body whose endpoints are
product states.
-/

namespace Qhl

open Finset

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)]
variable {σT : Type*}

/-! ## §1. The bare-ket assertion of a product state -/

variable (D)

/-- **The bare-ket assertion of a product state** — the endpoint shape of CoqQ's
state triples `⊨s {P} c {Q}`, whose `P` and `Q` are kets `'|v; s⟩`
(`example/coqq_paper/qhl.v:1594` and everywhere in `example.v`).

It is `Assn.ofState` at `⊗ᵢ ψᵢ` with the unit-norm side condition
`norm_prodV_eq_one` already discharged from the pointwise hypothesis `hψ`, so a
use site never writes the wrapper: the *only* data are the state family `ψ` and
the fact that each factor is a unit vector — exactly what CoqQ's `'|v; s⟩`
carries through its `NormalState` canonical structure. -/
noncomputable def prodA (ψ : ∀ i, EuclideanSpace ℂ (D i)) (hψ : ∀ i, ‖ψ i‖ = 1) :
    Assn σT D :=
  Assn.ofState (prodV D (W := (univ : Finset L)) ψ) (norm_prodV_eq_one ψ hψ)

variable {D}

/-- The operator of a bare-ket assertion is the projector `|⊗ᵢψᵢ⟩⟨⊗ᵢψᵢ|`, in
every classical state. -/
@[simp]
theorem prodA_op (ψ : ∀ i, EuclideanSpace ℂ (D i)) (hψ : ∀ i, ‖ψ i‖ = 1) (σ : σT) :
    (prodA (σT := σT) D ψ hψ).op σ
      = outerLM (prodV D (W := (univ : Finset L)) ψ) (prodV D (W := (univ : Finset L)) ψ) :=
  rfl

/-! ## §2. `RS_forward`/`RS_back` as entailments -/

/-- **CoqQ's `RS_forward`/`RS_back` hypothesis, as an entailment.** Those rules
(`qhl.v:1594`, `:1599`) consume a bare *equality of states* `R = Q`; here the
same equality of state *families* yields the `≤` that (R-Conseq) takes, because
the unit-norm witnesses are proofs and carry no information
(`Assn.ofState_le_ofState`). -/
theorem prodA_le {ψ φ : ∀ i, EuclideanSpace ℂ (D i)} {hψ : ∀ i, ‖ψ i‖ = 1}
    {hφ : ∀ i, ‖φ i‖ = 1} (h : ψ = φ) :
    prodA (σT := σT) D ψ hψ ≤ prodA D φ hφ :=
  Assn.ofState_le_ofState (congrArg (prodV D (W := (univ : Finset L))) h)

/-- The pointwise form of `prodA_le`: two product states with cellwise equal
factors give the same bare-ket assertion, up to entailment. `funext` is applied
here, once, so that no consumer has to. -/
theorem prodA_le_of_forall {ψ φ : ∀ i, EuclideanSpace ℂ (D i)} {hψ : ∀ i, ‖ψ i‖ = 1}
    {hφ : ∀ i, ‖φ i‖ = 1} (h : ∀ i, ψ i = φ i) :
    prodA (σT := σT) D ψ hψ ≤ prodA D φ hφ :=
  prodA_le (funext h)

/-- **CoqQ `RS_forward`** (`qhl.v:1594`):

```
R = Q → ⊨s {P} c {R} → ⊨s {P} c {Q}
```

a derivation whose postcondition is a bare ket may be recast along any equality
of state families, in one call. This is (R-Conseq) with a reflexive
precondition; it is what keeps CoqQ's `RS_QFT_sub`/`RS_QFT_iter`
(`example.v:261`, `:311`) at one rule application per stage, the arithmetic of
the new state being supplied as a plain equation. -/
theorem DerivTot.prodForward {C : Prog σT D} {ψ φ φ' : ∀ i, EuclideanSpace ℂ (D i)}
    {hψ : ∀ i, ‖ψ i‖ = 1} {hφ : ∀ i, ‖φ i‖ = 1} {hφ' : ∀ i, ‖φ' i‖ = 1}
    (d : DerivTot (prodA D ψ hψ) C (prodA D φ hφ)) (h : φ = φ') :
    DerivTot (prodA (σT := σT) D ψ hψ) C (prodA D φ' hφ') :=
  DerivTot.conseq (Assn.le_refl' _) d (prodA_le h)

/-- **CoqQ `RS_back`** (`qhl.v:1599`):

```
R = P → ⊨s {R} c {Q} → ⊨s {P} c {Q}
```

the precondition counterpart of `DerivTot.prodForward`: a derivation starting at
a bare ket may be re-entered at any state family equal to it. -/
theorem DerivTot.prodBack {C : Prog σT D} {ψ ψ' φ : ∀ i, EuclideanSpace ℂ (D i)}
    {hψ : ∀ i, ‖ψ i‖ = 1} {hψ' : ∀ i, ‖ψ' i‖ = 1} {hφ : ∀ i, ‖φ i‖ = 1}
    (d : DerivTot (prodA D ψ hψ) C (prodA D φ hφ)) (h : ψ' = ψ) :
    DerivTot (prodA (σT := σT) D ψ' hψ') C (prodA D φ hφ) :=
  DerivTot.conseq (prodA_le h) d (Assn.le_refl' _)

/-! ## §3. The product-state stage chain (`RS_forward` + the sequential `for`-rule) -/

/-- **The bare-ket form of the sequential `for`-loop rule.**

`DerivTot.forProg_finRange_chain` (`Qhl/Logic/ForSeqRule.lean`) is the invariant
chain `J 0 → … → J n` for loops whose bodies share wires — the Lean counterpart
of the `big_ord_recr` unrolling CoqQ performs inside `RS_QFT_sub`
(`example/coqq_paper/example.v:261`). This is that rule with

* the invariant specialised to a **family of product states** `fam : ℕ → …`, so
  the `Assn.ofState`/`norm_prodV_eq_one` wrappers are supplied once here rather
  than at every stage, and
* CoqQ's `RS_back`/`RS_forward` (`qhl.v:1599`, `:1594`) already applied at the
  two ends: the caller states the loop with *its own* endpoints `ψ₀`, `ψ₁` and
  hands over the two identities `fam 0 = ψ₀`, `fam n = ψ₁` raw.

```
fam 0 = ψ₀ → fam n = ψ₁ → (∀ j, ⊢ₜ {fam j} C j {fam (j+1)})
  → ⊢ₜ {⊗ᵢ (ψ₀)ᵢ}  for j < n do C j  {⊗ᵢ (ψ₁)ᵢ}
```

Consequently a whole interacting-wire loop is **one** call: the loop induction
lives in `ForSeqRule.lean`, the entry/exit consequence steps live here, and the
consumer supplies only the invariant and one derivation per stage. `+ 1` is
addition in `ℕ`, not the wrap-around addition of `Fin n`. -/
theorem DerivTot.forProg_prodChain {n : ℕ} {C : Fin n → Prog σT D}
    (fam : ℕ → ∀ i, EuclideanSpace ℂ (D i)) (hnorm : ∀ m i, ‖fam m i‖ = 1)
    {ψ₀ ψ₁ : ∀ i, EuclideanSpace ℂ (D i)} {hψ₀ : ∀ i, ‖ψ₀ i‖ = 1} {hψ₁ : ∀ i, ‖ψ₁ i‖ = 1}
    (hzero : fam 0 = ψ₀) (hfull : fam n = ψ₁)
    (step : ∀ j : Fin n, DerivTot (prodA D (fam (j : ℕ)) (hnorm (j : ℕ))) (C j)
      (prodA D (fam ((j : ℕ) + 1)) (hnorm ((j : ℕ) + 1)))) :
    DerivTot (prodA (σT := σT) D ψ₀ hψ₀) (Qhl.forProg (List.finRange n) C)
      (prodA D ψ₁ hψ₁) :=
  DerivTot.conseq (prodA_le hzero.symm)
    (DerivTot.forProg_finRange_chain (fun m => prodA D (fam m) (hnorm m)) step)
    (prodA_le hfull)

/-! ## §4. One rung of a chain (`RV_Frame` + (Ax-Uni) + both consequences) -/

/-- **One two-cell rung, in one call** — CoqQ's `RV_Frame` (`qhl.v:1815`)
composed with (Ax-Uni) and the two (R-Conseq) steps that a chain stage needs:

```
G (ψₐ ⊗ ψ_b) = u' ⊗ v'  →  (ψ with a ↦ u', b ↦ v') = φ
  →  ⊢ₜ {⊗ᵢ ψᵢ}  (a, b) *= G  {⊗ᵢ φᵢ}
```

The gate hypothesis `hG` lives **entirely inside the gate's own two-cell world**
`EuclideanSpace ℂ (D a × D b)` — the `n = 2` computation — while every other
factor is the frame `R` of `RV_Frame`, carried through untouched by
`DerivTot.unitary_pair_prodV` (`Qhl/Logic/Frame.lean`). The state-algebra step
`hstep` is a plain equality of families, so the rung lands *directly* on the next
stage of a `DerivTot.forProg_prodChain` invariant, with no intervening `conseq`.

`hstep` deliberately precedes `hG`: elaborating its type pins the resulting
factors `u'`, `v'` and the target family `φ`, so the `hG` goal is fully
determined by the time a tactic proof for it runs (a tactic block cannot drive
unification). This is what lets a use site pass `_` for the state family and
omit every `(u' := …)` annotation. -/
theorem DerivTot.prodRung_pair (a b : L) (hab : a ≠ b)
    (G : UnitaryOp (EuclideanSpace ℂ (D a × D b)))
    (ψ : ∀ i, EuclideanSpace ℂ (D i)) (hψ : ∀ i, ‖ψ i‖ = 1)
    {u' : EuclideanSpace ℂ (D a)} {v' : EuclideanSpace ℂ (D b)}
    {φ : ∀ i, EuclideanSpace ℂ (D i)}
    (hstep : Function.update (Function.update ψ a u') b v' = φ)
    (hG : (G : EuclideanSpace ℂ (D a × D b) →ₗ[ℂ] EuclideanSpace ℂ (D a × D b))
        (vpair (ψ a) (ψ b)) = vpair u' v')
    (hu' : ‖u'‖ = 1) (hv' : ‖v'‖ = 1) (hφ : ∀ i, ‖φ i‖ = 1) :
    DerivTot (σT := σT) (prodA D ψ hψ) (Prog.unitary2 a b hab G) (prodA D φ hφ) :=
  DerivTot.conseq (Assn.le_refl' _)
    (DerivTot.unitary_pair_prodV a b hab G ψ hψ hG hu' hv')
    (prodA_le (hψ := norm_update_update_eq_one a b ψ hψ hu' hv') hstep)

/-- **One one-cell rung, in one call** — the `k = 1` analogue of
`DerivTot.prodRung_pair`, over `DerivTot.unitary1_prodV` (`Qhl/Logic/ForRule.lean`).
The program is CoqQ's `[ut x.[i] := ''H]` (`qwhile.v:429`), i.e. the library
notation `[ut a := U]`:

```
(ψ with a ↦ U ψₐ) = φ  →  ⊢ₜ {⊗ᵢ ψᵢ}  a *= U  {⊗ᵢ φᵢ}
```

Again `hstep` is the state algebra as a plain equality of families, so the step
lands directly on the next stage of a chain — CoqQ's `RS_forward`
(`qhl.v:1594`) absorbed into the rule. -/
theorem DerivTot.prodRung_single (a : L) (U : UnitaryOp (EuclideanSpace ℂ (D a)))
    (ψ : ∀ i, EuclideanSpace ℂ (D i)) (hψ : ∀ i, ‖ψ i‖ = 1)
    {φ : ∀ i, EuclideanSpace ℂ (D i)}
    (hstep : Function.update ψ a
        ((U : EuclideanSpace ℂ (D a) →ₗ[ℂ] EuclideanSpace ℂ (D a)) (ψ a)) = φ)
    (hφ : ∀ i, ‖φ i‖ = 1) :
    DerivTot (σT := σT) (prodA D ψ hψ)
      (Prog.unitary1 (fun _ => a) fun _ => singleGate D a U) (prodA D φ hφ) :=
  DerivTot.conseq (Assn.le_refl' _)
    (DerivTot.unitary1_prodV a U ψ hψ)
    (prodA_le (hψ := norm_update_eq_one a U ψ hψ) hstep)

end Qhl
