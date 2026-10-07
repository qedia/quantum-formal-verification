import Qhl.Logic.CountedWhile
import Qhl.Logic.AncillaEmbed

/-!
# The counted-`while` loop at store-indexed pure-state endpoints

`Qhl/Logic/CountedProdChain.lean` packages the counted loop
`cnt := 0 ; while cnt < N do BODY ; cnt := cnt + 1 od` at **product-state**
invariant families (`prodA`).  This file is the same layer one level up in
generality: the invariant family is an arbitrary **store-indexed pure state**
`fam : ℕ → σT → HS D univ` under `Assn.ofStateFam`
(`Qhl/Logic/AncillaEmbed.lean` §7) — the shape a loop whose state is entangled
across cells (so not a `prodV`) or depends on the classical store needs.

* `DerivTot.countedRung_fam` — the core masked rung at state families: one
  gate step of a counted loop, (Ax-Uni)+(R-Conseq)
  (`DerivTot.unitary_stepMask`) closed by rank-one algebra from the single
  hypothesis that, where the step mask holds, the lifted gate sends `v σ` to
  `w σ` (with the register expression distinct there, the paper's `Dist(q̄)`
  side condition).  The projector conjugation `U†∣w⟩⟨w∣U = ∣v⟩⟨v∣` is computed
  here once (`adjoint_comp_outerLM_comp`, `adjoint_apply_apply`).
* `DerivTot.countedRung_ite` — the rung through a classical conditional
  `if b then q̄ *= U else skip`: (R-Cond) (`DerivTot.cond'`) with the live
  branch a `countedRung_fam` and the dead branch (Ax-Ski)+(R-Conseq), from
  the action on the live guard and the identity `v σ = w σ` on the dead one.
* `DerivTot.countedStateChain` — a whole counted loop with a literal bound in
  one call: `DerivTot.countedWhile_const` at the state-family invariant, with
  the entry/exit (R-Conseq) recasts applied.  Because `Assn.ofStateFam` reads
  the store, the caller supplies counter-insensitivity of the family (`hins`);
  for a store-constant family it is `fun _ _ _ => rfl`.
* `DerivTot.countedStateChain_rel` — the relativised chain: the bound is read
  from the store and pinned to a literal by a frame predicate `φ`, both
  endpoints stay masked by `φ`, and the endpoint identities may use `φ`.  Its
  conclusion has exactly the shape of a step obligation of an outer
  `DerivTot.countedWhile_const`, so a nested counted loop feeds back as one
  call.

**Nothing is postulated.**  Everything below is derived from
the counted-loop helpers of `CountedWhile`, including their source variants,
`unitary_stepMask`, `DerivTot.cond'`, and `DerivTot.skip`,
plus (R-Conseq) and the rank-one algebra; no new axiom, no
new rule primitive, and `DerivTot`, `validTot`, `DerivTot.sound` are untouched.

**Ownership test.**  No program, gate or example fixture is named: everything
is generic in the world `L`, the cell family `D`, the store `σT`, the counter
lens, the register expressions and the state families.

The helpers whose names end in `Source` use the source total-loop constructor.
They require an unranked invariant-preservation derivation and a separate
identity-predicate derivation. The older helpers retain their original
combined-premise extension for compatibility; they are not source-rule proofs.
For nested loops with a store-dependent bound, `countedStateChainVarSource`
uses the bound and state family at the current classical store.
-/

namespace Qhl

open Finset

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)]
variable {σT : Type*}

/-! ## §1. The core masked rung at state families -/

/-- **One gate step of a counted loop, at store-indexed pure states.**  If, at
every store the step mask lets through, the lifted gate sends `v σ` to `w σ`
(with the register expression distinct there), then

```
⊢ₜ {∣v σ⟩⟨v σ∣ ∧ φ}  q̄(σ) *= U(σ)  {∣w σ⟩⟨w σ∣ ∧ φ}.
```

(Ax-Uni)+(R-Conseq) via `DerivTot.unitary_stepMask`; the projector conjugation
is the rank-one algebra `adjoint_comp_outerLM_comp`/`adjoint_apply_apply`,
computed here once for every consumer.  The state-family counterpart of
`DerivTot.countedRung`. -/
theorem DerivTot.countedRung_fam {k : ℕ} (rE : RegExpr σT L k)
    (gE : ∀ σ, UnitaryOp (TSpace D (rE σ))) {φ : σT → Prop}
    {v w : σT → HS D (univ : Finset L)}
    (hv : ∀ σ, ‖v σ‖ = 1) (hw : ∀ σ, ‖w σ‖ = 1)
    (hact : ∀ σ, φ σ → ∃ hinj : Function.Injective (rE σ),
      regLift ⟨rE σ, hinj⟩ (gE σ) (v σ) = w σ) :
    DerivTot ((Assn.ofStateFam v hv).mask φ) (.unitary k rE gE)
      ((Assn.ofStateFam w hw).mask φ) := by
  refine DerivTot.unitary_stepMask rE gE fun σ hσ => ?_
  obtain ⟨hinj, hlift⟩ := hact σ hσ
  refine le_of_eq ?_
  rw [Assn.unitaryPre_op_of_dist _ rE gE hinj,
    Assn.mask_op_of_pos (A := Assn.ofStateFam w hw) (φ := φ) (σ := σ) hσ,
    Assn.ofStateFam_op, Assn.ofStateFam_op, adjoint_comp_outerLM_comp, ← hlift,
    adjoint_apply_apply (isUnitary_regLift ⟨rE σ, hinj⟩ (gE σ))]

/-! ## §2. The rung through a classical conditional -/

/-- **One conditional gate step of a counted loop**: the body
`if b then q̄(σ) *= U(σ) else skip`, at store-indexed pure states.  On the
live guard the lifted gate sends `v σ` to `w σ`; on the dead guard the family
is unchanged (`v σ = w σ`).  (R-Cond) (`DerivTot.cond'`) with the live branch
a `countedRung_fam` and the dead branch (Ax-Ski)+(R-Conseq). -/
theorem DerivTot.countedRung_ite {k : ℕ} (b : σT → Bool) (rE : RegExpr σT L k)
    (gE : ∀ σ, UnitaryOp (TSpace D (rE σ))) {φ : σT → Prop}
    {v w : σT → HS D (univ : Finset L)}
    (hv : ∀ σ, ‖v σ‖ = 1) (hw : ∀ σ, ‖w σ‖ = 1)
    (hlive : ∀ σ, φ σ → b σ = true → ∃ hinj : Function.Injective (rE σ),
      regLift ⟨rE σ, hinj⟩ (gE σ) (v σ) = w σ)
    (hdead : ∀ σ, φ σ → b σ = false → v σ = w σ) :
    DerivTot ((Assn.ofStateFam v hv).mask φ)
      (Prog.ite b (.unitary k rE gE) .skip)
      ((Assn.ofStateFam w hw).mask φ) :=
  DerivTot.cond'
    (DerivTot.conseq (Assn.le_refl' _)
      (DerivTot.countedRung_fam rE gE (φ := fun σ => φ σ ∧ b σ = true) hv hw
        fun σ hσ => hlive σ hσ.1 hσ.2)
      (Assn.mask_le_mask (fun _ h => h.1) fun _ _ => le_rfl))
    (DerivTot.conseq
      (Assn.mask_le_of_imp_le fun σ hσ => le_of_eq (by
        rw [Assn.ofStateFam_op,
          Assn.mask_op_of_pos (A := Assn.ofStateFam w hw) (φ := φ) hσ.1,
          Assn.ofStateFam_op, hdead σ hσ.1 hσ.2]))
      (DerivTot.skip _) (Assn.le_refl' _))

/-! ## §3. The whole loop, in one call -/

/-- **The counted state-family chain** — the whole counted loop with a literal
bound:

```
fam 0 = v₀ → fam n = v₁ → (∀ k, ⊢ₜ {fam k ∧ cnt = k ∧ k < n} BODY {fam (k+1) ∧ …})
  → ⊢ₜ {∣v₀ σ⟩⟨v₀ σ∣}  cnt := 0 ; while cnt < n do BODY ; cnt := cnt + 1 od
      {∣v₁ σ⟩⟨v₁ σ∣ ∧ cnt = n}.
```

`DerivTot.countedWhile_const` at the state-family invariant, with the
entry/exit (R-Conseq) recasts applied.  `hins` is the counter insensitivity of
the family (for a store-constant family, `fun _ _ _ => rfl`).  The
state-family counterpart of `DerivTot.countedProdChain`. -/
theorem DerivTot.countedStateChain (c : CounterLens σT) {n : ℕ}
    (fam : ℕ → σT → HS D (univ : Finset L)) (hnorm : ∀ m σ, ‖fam m σ‖ = 1)
    {v₀ v₁ : σT → HS D (univ : Finset L)}
    {hv₀ : ∀ σ, ‖v₀ σ‖ = 1} {hv₁ : ∀ σ, ‖v₁ σ‖ = 1}
    (hins : ∀ m σ v', fam m (c.set σ v') = fam m σ)
    (hzero : fam 0 = v₀) (hfull : fam n = v₁) {BODY : Prog σT D}
    (step : ∀ k, DerivTot
      ((Assn.ofStateFam (fam k) (hnorm k)).mask fun σ => c.get σ = k ∧ k < n)
      BODY
      ((Assn.ofStateFam (fam (k + 1)) (hnorm (k + 1))).mask
        fun σ => c.get σ = k ∧ k < n)) :
    DerivTot (Assn.ofStateFam v₀ hv₀) (countedProg c (fun _ => n) BODY)
      ((Assn.ofStateFam v₁ hv₁).mask fun σ => c.get σ = n) :=
  DerivTot.conseq
    (fun σ => le_of_eq (by
      rw [Assn.ofStateFam_op, Assn.ofStateFam_op, hzero]))
    (DerivTot.countedWhile_const c
      (J := fun m => Assn.ofStateFam (fam m) (hnorm m))
      (fun m σ v' => by
        rw [Assn.ofStateFam_op, Assn.ofStateFam_op, hins m σ v'])
      step)
    (Assn.mask_le_mask (fun _ h => h)
      fun σ _ => le_of_eq (by
        rw [Assn.ofStateFam_op, Assn.ofStateFam_op, hfull]))

/-- **The relativised counted state-family chain**: the bound `N` is read from
the store and pinned to the literal `n` under the frame predicate `φ`, and
both endpoints stay masked by `φ`:

```
⊢ₜ {∣v₀ σ⟩⟨v₀ σ∣ ∧ φ}  cnt := 0 ; while cnt < N do BODY ; cnt := cnt + 1 od
    {∣v₁ σ⟩⟨v₁ σ∣ ∧ φ}.
```

The conclusion has exactly the shape of a step obligation of an outer
`DerivTot.countedWhile_const`, so a nested counted loop is fed back as one
call; where `φ` is false every mask is false and the obligations close
trivially.  The endpoint identities are pointwise and may use `φ` (e.g. a
bound an outer mask provides).  The state-family counterpart of
`DerivTot.countedProdChain_rel`. -/
theorem DerivTot.countedStateChain_rel (c : CounterLens σT) {N : σT → ℕ}
    (n : ℕ) {φ : σT → Prop}
    (hφ : ∀ σ v, φ (c.set σ v) ↔ φ σ) (hN : ∀ σ, φ σ → N σ = n)
    (fam : ℕ → σT → HS D (univ : Finset L)) (hnorm : ∀ m σ, ‖fam m σ‖ = 1)
    {v₀ v₁ : σT → HS D (univ : Finset L)}
    {hv₀ : ∀ σ, ‖v₀ σ‖ = 1} {hv₁ : ∀ σ, ‖v₁ σ‖ = 1}
    (hins : ∀ m σ v', fam m (c.set σ v') = fam m σ)
    (hzero : ∀ σ, φ σ → fam 0 σ = v₀ σ) (hfull : ∀ σ, φ σ → fam n σ = v₁ σ)
    {BODY : Prog σT D}
    (step : ∀ k, DerivTot
      ((Assn.ofStateFam (fam k) (hnorm k)).mask
        fun σ => φ σ ∧ c.get σ = k ∧ k < n)
      BODY
      ((Assn.ofStateFam (fam (k + 1)) (hnorm (k + 1))).mask
        fun σ => φ σ ∧ c.get σ = k ∧ k < n)) :
    DerivTot ((Assn.ofStateFam v₀ hv₀).mask φ) (countedProg c N BODY)
      ((Assn.ofStateFam v₁ hv₁).mask φ) :=
  DerivTot.conseq
    (Assn.mask_le_mask (fun _ h => h)
      fun σ hσ => le_of_eq (by
        rw [Assn.ofStateFam_op, Assn.ofStateFam_op, hzero σ hσ]))
    (DerivTot.countedWhile c hφ hN
      (J := fun m => Assn.ofStateFam (fam m) (hnorm m))
      (fun m σ v' => by
        rw [Assn.ofStateFam_op, Assn.ofStateFam_op, hins m σ v'])
      step)
    (Assn.mask_le_mask (fun _ h => h.1)
      fun σ hσ => le_of_eq (by
        rw [Assn.ofStateFam_op, Assn.ofStateFam_op, hfull σ hσ.1]))


/-- Source total-loop variant with a store-indexed invariant step and an
independent identity-predicate body derivation. -/
theorem DerivTot.countedStateChainSource (c : CounterLens σT) {n : ℕ}
    (fam : ℕ → σT → HS D (univ : Finset L)) (hnorm : ∀ m σ, ‖fam m σ‖ = 1)
    {v₀ v₁ : σT → HS D (univ : Finset L)}
    {hv₀ : ∀ σ, ‖v₀ σ‖ = 1} {hv₁ : ∀ σ, ‖v₁ σ‖ = 1}
    (hins : ∀ m σ v', fam m (c.set σ v') = fam m σ)
    (hzero : fam 0 = v₀) (hfull : fam n = v₁) {BODY : Prog σT D}
    (step : DerivTot
      ((Assn.ofFam c.get (fun m => Assn.ofStateFam (fam m) (hnorm m))).mask
        fun σ => c.get σ < n) BODY
      ((Assn.ofFam c.get (fun m => Assn.ofStateFam (fam (m + 1)) (hnorm (m + 1)))).mask
        fun σ => c.get σ < n))
    (hidentity : ∀ k, DerivTot
      ((Assn.one : Assn σT D).mask fun σ => c.get σ = k ∧ k < n) BODY
      ((Assn.one : Assn σT D).mask fun σ => c.get σ = k ∧ k < n)) :
    DerivTot (Assn.ofStateFam v₀ hv₀) (countedProg c (fun _ => n) BODY)
      ((Assn.ofStateFam v₁ hv₁).mask fun σ => c.get σ = n) :=
  DerivTot.conseq
    (fun σ => le_of_eq (by
      rw [Assn.ofStateFam_op, Assn.ofStateFam_op, hzero]))
    (DerivTot.countedWhile_constSource c
      (J := fun m => Assn.ofStateFam (fam m) (hnorm m))
      (fun m σ v' => by
        rw [Assn.ofStateFam_op, Assn.ofStateFam_op, hins m σ v'])
      step hidentity)
    (Assn.mask_le_mask (fun _ h => h)
      fun σ _ => le_of_eq (by
        rw [Assn.ofStateFam_op, Assn.ofStateFam_op, hfull]))

/-- Source total-loop variant with a store-indexed invariant step and an
independent identity-predicate body derivation. -/
theorem DerivTot.countedStateChain_relSource (c : CounterLens σT) {N : σT → ℕ}
    (n : ℕ) {φ : σT → Prop}
    (hφ : ∀ σ v, φ (c.set σ v) ↔ φ σ) (hN : ∀ σ, φ σ → N σ = n)
    (fam : ℕ → σT → HS D (univ : Finset L)) (hnorm : ∀ m σ, ‖fam m σ‖ = 1)
    {v₀ v₁ : σT → HS D (univ : Finset L)}
    {hv₀ : ∀ σ, ‖v₀ σ‖ = 1} {hv₁ : ∀ σ, ‖v₁ σ‖ = 1}
    (hins : ∀ m σ v', fam m (c.set σ v') = fam m σ)
    (hzero : ∀ σ, φ σ → fam 0 σ = v₀ σ) (hfull : ∀ σ, φ σ → fam n σ = v₁ σ)
    {BODY : Prog σT D}
    (step : DerivTot
      ((Assn.ofFam c.get (fun m => Assn.ofStateFam (fam m) (hnorm m))).mask
        fun σ => φ σ ∧ c.get σ < n) BODY
      ((Assn.ofFam c.get (fun m => Assn.ofStateFam (fam (m + 1)) (hnorm (m + 1)))).mask
        fun σ => φ σ ∧ c.get σ < n))
    (hidentity : ∀ k, DerivTot
      ((Assn.one : Assn σT D).mask fun σ => φ σ ∧ c.get σ = k ∧ k < n) BODY
      ((Assn.one : Assn σT D).mask fun σ => φ σ ∧ c.get σ = k ∧ k < n)) :
    DerivTot ((Assn.ofStateFam v₀ hv₀).mask φ) (countedProg c N BODY)
      ((Assn.ofStateFam v₁ hv₁).mask φ) :=
  DerivTot.conseq
    (Assn.mask_le_mask (fun _ h => h)
      fun σ hσ => le_of_eq (by
        rw [Assn.ofStateFam_op, Assn.ofStateFam_op, hzero σ hσ]))
    (DerivTot.countedWhileSource c hφ hN
      (J := fun m => Assn.ofStateFam (fam m) (hnorm m))
      (fun m σ v' => by
        rw [Assn.ofStateFam_op, Assn.ofStateFam_op, hins m σ v'])
      step hidentity)
    (Assn.mask_le_mask (fun _ h => h.1)
      fun σ hσ => le_of_eq (by
        rw [Assn.ofStateFam_op, Assn.ofStateFam_op, hfull σ hσ.1]))



/-- Selecting a pure-state family agrees with the pure state selected at the current store. -/
theorem Assn.ofFam_ofStateFam (g : σT → ℕ)
    (fam : ℕ → σT → HS D (univ : Finset L)) (hnorm : ∀ m σ, ‖fam m σ‖ = 1) :
    Assn.ofFam g (fun m => Assn.ofStateFam (fam m) (hnorm m)) =
      Assn.ofStateFam (fun σ => fam (g σ) σ) (fun σ => hnorm (g σ) σ) := by
  apply Assn.ext
  funext σ
  rfl

/-- A source counted loop with a store-dependent bound and state-family endpoints.
Both the bound and each state family are insensitive to counter writes. -/
theorem DerivTot.countedStateChainVarSource (c : CounterLens σT) {N : σT → ℕ}
    {φ : σT → Prop}
    (hφ : ∀ σ v, φ (c.set σ v) ↔ φ σ)
    (hN : ∀ σ v, N (c.set σ v) = N σ)
    (fam : ℕ → σT → HS D (univ : Finset L)) (hnorm : ∀ m σ, ‖fam m σ‖ = 1)
    {v₀ v₁ : σT → HS D (univ : Finset L)}
    {hv₀ : ∀ σ, ‖v₀ σ‖ = 1} {hv₁ : ∀ σ, ‖v₁ σ‖ = 1}
    (hins : ∀ m σ v', fam m (c.set σ v') = fam m σ)
    (hzero : ∀ σ, φ σ → fam 0 σ = v₀ σ)
    (hfull : ∀ σ, φ σ → fam (N σ) σ = v₁ σ)
    {BODY : Prog σT D}
    (step : DerivTot
      ((Assn.ofStateFam (fun σ => fam (c.get σ) σ) (fun σ => hnorm _ σ)).mask
        fun σ => φ σ ∧ c.get σ < N σ) BODY
      ((Assn.ofStateFam (fun σ => fam (c.get σ + 1) σ) (fun σ => hnorm _ σ)).mask
        fun σ => φ σ ∧ c.get σ < N σ))
    (hidentity : ∀ z : Int, DerivTot
      ((Assn.one : Assn σT D).mask
        fun σ => φ σ ∧ c.get σ < N σ ∧ ((N σ - c.get σ : ℕ) : Int) = z) BODY
      ((Assn.one : Assn σT D).mask
        fun σ => φ σ ∧ c.get σ < N σ ∧ ((N σ - c.get σ : ℕ) : Int) = z)) :
    DerivTot ((Assn.ofStateFam v₀ hv₀).mask φ) (countedProg c N BODY)
      ((Assn.ofStateFam v₁ hv₁).mask φ) := by
  refine DerivTot.conseq
    (Assn.mask_le_mask (fun _ h => h)
      fun σ hσ => le_of_eq (by
        rw [Assn.ofStateFam_op, Assn.ofStateFam_op, hzero σ hσ]))
    (DerivTot.countedWhileVarSource c hφ hN
      (J := fun m => Assn.ofStateFam (fam m) (hnorm m))
      (fun m σ v' => by
        rw [Assn.ofStateFam_op, Assn.ofStateFam_op, hins m σ v'])
      (by
        rw [Assn.ofFam_ofStateFam,
          Assn.ofFam_ofStateFam c.get (fun m => fam (m + 1)) (fun m => hnorm (m + 1))]
        exact step) hidentity)
    (Assn.mask_le_mask (fun _ h => h.1)
      fun σ hσ => le_of_eq (by
        rw [Assn.ofFam_op, Assn.ofStateFam_op, Assn.ofStateFam_op, hfull σ hσ.1]))

/-! ## §4. Composition test

Not an example (no program-specific content) — the witness that the rules
compose: a counted state-family chain over `skip` bodies, and a conditional
rung with an everywhere-false guard.  `#print axioms` on both reports
`[propext, Classical.choice, Quot.sound]`. -/

namespace CountedStateChainTest

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)]
variable (u : HS D (univ : Finset L)) (hu : ‖u‖ = 1)

/-- A counted chain of `skip`s over the constant state family. -/
theorem toyChain (n : ℕ) :
    DerivTot (Assn.ofStateFam (σT := ℕ) (fun _ => u) fun _ => hu)
      (countedProg CounterLens.nat (fun _ => n) .skip)
      ((Assn.ofStateFam (fun _ => u) fun _ => hu).mask
        fun σ => CounterLens.nat.get σ = n) :=
  DerivTot.countedStateChain CounterLens.nat (fun _ _ => u) (fun _ _ => hu)
    (fun _ _ _ => rfl) rfl rfl (fun _ => DerivTot.skip _)

/-- A conditional rung whose guard is everywhere false: the dead branch
carries the state through unchanged. -/
theorem toyIte (rE : RegExpr ℕ L 1)
    (gE : ∀ σ, UnitaryOp (TSpace D (rE σ))) :
    DerivTot ((Assn.ofStateFam (fun _ => u) fun _ => hu).mask fun σ => σ = 0)
      (Prog.ite (fun _ => false) (.unitary 1 rE gE) .skip)
      ((Assn.ofStateFam (fun _ => u) fun _ => hu).mask fun σ => σ = 0) :=
  DerivTot.countedRung_ite (fun _ => false) rE gE (fun _ => hu) (fun _ => hu)
    (fun _ _ hb => by simp at hb) (fun _ _ _ => rfl)

end CountedStateChainTest

end Qhl
