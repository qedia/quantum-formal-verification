import Qhl.Logic.CountedWhile
import Qhl.Logic.ProdChain

/-!
# The counted-`while` loop at product-state endpoints

`Qhl/Logic/CountedWhile.lean` derives the counted loop
`cnt := 0 ; while cnt < N do BODY ; cnt := cnt + 1 od` as one rule of
`QHL⁺_tot`, generic in the invariant family; `Qhl/Logic/ProdChain.lean` is the
ambient layer that keeps CoqQ-style state triples at bare kets (`prodA`,
`RS_forward`/`RS_back`). This file is the meet of the two — the counted loop
whose invariant is a **family of product states** and whose body is **one
gate**, packaged in the same shapes as the `for`-fold layer
(`DerivTot.forProg_prodChain` + `DerivTot.prodRung_pair`/`prodRung_single`):

* `DerivTot.countedRung` — the **core masked rung**: one gate step of a counted
  loop, (Ax-Uni)+(R-Conseq) (`DerivTot.unitary_stepMask`) closed by rank-one
  algebra from a single hypothesis — the *whole-world action* of the lifted
  gate on the invariant's product state, where the step mask holds. Off the
  mask the effect is `0` and nothing is proved; on the mask the register
  expression is distinct (the paper's `Dist(q̄)` side condition) and the
  projector conjugation `U†∣w⟩⟨w∣U = ∣v⟩⟨v∣` is computed here once
  (`adjoint_comp_outerLM_comp`, `adjoint_apply_apply`), so no consumer ever
  writes it again.
* `DerivTot.countedRung_single` / `DerivTot.countedRung_pair` — the rung with
  the action reduced to **cell-level data**: under the mask the store-read
  register expression collapses to `Reg.single`/`Reg.pair` at the touched
  cells, and the action is the one-cell update (`regLift_singleGate_prodV`)
  resp. the two-cell gate fact stated in the gate's own world
  (`regLift_pairGate_prodV`, CoqQ `lift_lf` on a `tenvm`-split state). These
  are the counted-loop counterparts of `DerivTot.prodRung_single` and
  `DerivTot.prodRung_pair` (`Qhl/Logic/ProdChain.lean` §4).
* `DerivTot.countedProdChain` — a whole counted loop with a literal bound, in
  **one call**: `DerivTot.countedWhile_const` with the invariant specialised to
  a product-state family and the entry/exit (R-Conseq) recasts — CoqQ's
  `RS_back`/`RS_forward` — already applied, exactly as
  `DerivTot.forProg_prodChain` packages the `for`-fold. The caller supplies
  the family, its two endpoint identities, and one step derivation per
  counter value. Counter insensitivity of the invariant is discharged here
  (`prodA` is store-constant), so it never appears at a use site.
* `DerivTot.countedProdChain_rel` — the **relativised** chain: the bound is
  read from the store and pinned to a literal by a frame predicate `φ`, and
  both endpoints stay masked by `φ`. Its conclusion has exactly the shape of
  a step obligation of an outer `DerivTot.countedWhile_const`, which is what
  a nested counted loop (a controlled-phase ladder inside its stage loop)
  feeds back; for the counter values the outer ranking makes vacuous, `φ` is
  everywhere false and every obligation closes trivially.

**Nothing is postulated.** Everything below is derived from
the counted-loop helpers of `CountedWhile`, including their source variants,
and `unitary_stepMask`, plus (R-Conseq) and the library
tensor bridges: no new axiom, no new rule primitive, and `DerivTot`,
`validTot` and `DerivTot.sound` are untouched.

**Ownership test.** No program, gate or example fixture is named: everything
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

/-! ## §1. The core masked rung -/

/-- **One gate step of a counted loop, from its whole-world action.** If, at
every store the step mask lets through, the lifted gate sends the product state
`⊗ᵢ vᵢ` to `⊗ᵢ wᵢ` (with the register expression distinct there), then

```
⊢ₜ {(⊗ᵢ vᵢ) ∧ φ}  q̄(σ) *= U(σ)  {(⊗ᵢ wᵢ) ∧ φ}.
```

(Ax-Uni)+(R-Conseq) via `DerivTot.unitary_stepMask`; the projector conjugation
is the rank-one algebra `adjoint_comp_outerLM_comp`/`adjoint_apply_apply`,
computed here once for every consumer. -/
theorem DerivTot.countedRung {k : ℕ} (rE : RegExpr σT L k)
    (gE : ∀ σ, UnitaryOp (TSpace D (rE σ))) {φ : σT → Prop}
    {v w : ∀ i, EuclideanSpace ℂ (D i)} (hv : ∀ i, ‖v i‖ = 1) (hw : ∀ i, ‖w i‖ = 1)
    (hact : ∀ σ, φ σ → ∃ hinj : Function.Injective (rE σ),
      regLift ⟨rE σ, hinj⟩ (gE σ) (prodV D (W := (univ : Finset L)) v)
        = prodV D (W := (univ : Finset L)) w) :
    DerivTot ((prodA D v hv).mask φ) (.unitary k rE gE) ((prodA D w hw).mask φ) := by
  refine DerivTot.unitary_stepMask rE gE fun σ hσ => ?_
  obtain ⟨hinj, hlift⟩ := hact σ hσ
  refine le_of_eq ?_
  rw [Assn.unitaryPre_op_of_dist _ rE gE hinj,
    Assn.mask_op_of_pos (A := prodA D w hw) (φ := φ) (σ := σ) hσ,
    prodA_op, prodA_op, adjoint_comp_outerLM_comp, ← hlift,
    adjoint_apply_apply (isUnitary_regLift ⟨rE σ, hinj⟩ (gE σ))]

/-! ## §2. The one-cell and two-cell rungs -/

/-- **The one-cell rung**: under the mask the store-read register collapses to
`Reg.single (a σ)` carrying the gate `U σ`, and the action is the one-factor
update of the invariant family (`regLift_singleGate_prodV`). The counted-loop
counterpart of `DerivTot.prodRung_single`. -/
theorem DerivTot.countedRung_single (rE : RegExpr σT L 1)
    (gE : ∀ σ, UnitaryOp (TSpace D (rE σ))) {φ : σT → Prop}
    (a : σT → L) (U : ∀ σ, UnitaryOp (EuclideanSpace ℂ (D (a σ))))
    {v w : ∀ i, EuclideanSpace ℂ (D i)} (hv : ∀ i, ‖v i‖ = 1) (hw : ∀ i, ‖w i‖ = 1)
    (hlift : ∀ σ, φ σ → ∃ hinj : Function.Injective (rE σ),
      regLift ⟨rE σ, hinj⟩ (gE σ)
        = regLift (D := D) (Reg.single (a σ)) (singleGate D (a σ) (U σ)))
    (hstep : ∀ σ, φ σ →
      Function.update v (a σ)
        ((U σ : EuclideanSpace ℂ (D (a σ)) →ₗ[ℂ] EuclideanSpace ℂ (D (a σ)))
          (v (a σ))) = w) :
    DerivTot ((prodA D v hv).mask φ) (.unitary 1 rE gE) ((prodA D w hw).mask φ) :=
  DerivTot.countedRung rE gE hv hw fun σ hσ => by
    obtain ⟨hinj, hK⟩ := hlift σ hσ
    exact ⟨hinj, by rw [hK, regLift_singleGate_prodV, hstep σ hσ]⟩

/-- **The two-cell rung**: under the mask the store-read register collapses to
`Reg.pair (a σ) (b σ)` carrying the gate `G σ`, and the action is the two-cell
gate fact in the gate's own world `D (a σ) × D (b σ)` together with the
two-factor update of the invariant family (`regLift_pairGate_prodV`, the frame
carried through untouched). The counted-loop counterpart of
`DerivTot.prodRung_pair`. -/
theorem DerivTot.countedRung_pair (rE : RegExpr σT L 2)
    (gE : ∀ σ, UnitaryOp (TSpace D (rE σ))) {φ : σT → Prop}
    (a b : σT → L) (hab : ∀ σ, φ σ → a σ ≠ b σ)
    (G : ∀ σ, UnitaryOp (EuclideanSpace ℂ (D (a σ) × D (b σ))))
    {v w : ∀ i, EuclideanSpace ℂ (D i)} (hv : ∀ i, ‖v i‖ = 1) (hw : ∀ i, ‖w i‖ = 1)
    (hlift : ∀ σ (hσ : φ σ), ∃ hinj : Function.Injective (rE σ),
      regLift ⟨rE σ, hinj⟩ (gE σ)
        = regLift (D := D) (Reg.pair (a σ) (b σ) (hab σ hσ))
            (pairGate (a σ) (b σ) (hab σ hσ) (G σ)))
    (hact : ∀ σ, φ σ →
      ∃ (u' : EuclideanSpace ℂ (D (a σ))) (v' : EuclideanSpace ℂ (D (b σ))),
        (G σ : EuclideanSpace ℂ (D (a σ) × D (b σ)) →ₗ[ℂ]
            EuclideanSpace ℂ (D (a σ) × D (b σ))) (vpair (v (a σ)) (v (b σ)))
            = vpair u' v'
          ∧ Function.update (Function.update v (a σ) u') (b σ) v' = w) :
    DerivTot ((prodA D v hv).mask φ) (.unitary 2 rE gE) ((prodA D w hw).mask φ) :=
  DerivTot.countedRung rE gE hv hw fun σ hσ => by
    obtain ⟨hinj, hK⟩ := hlift σ hσ
    obtain ⟨u', v', hG, hupd⟩ := hact σ hσ
    exact ⟨hinj, by
      rw [hK, regLift_pairGate_prodV (a σ) (b σ) (hab σ hσ) (G σ) v hG, hupd]⟩

/-! ## §3. The whole loop, in one call -/

/-- **The counted product-state chain** — the whole counted loop with a literal
bound:

```
fam 0 = ψ₀ → fam n = ψ₁ → (∀ k, ⊢ₜ {fam k ∧ cnt = k ∧ k < n} BODY {fam (k+1) ∧ …})
  → ⊢ₜ {⊗ᵢ (ψ₀)ᵢ}  cnt := 0 ; while cnt < n do BODY ; cnt := cnt + 1 od
      {(⊗ᵢ (ψ₁)ᵢ) ∧ cnt = n}.
```

`DerivTot.countedWhile_const` at the product-state invariant, with the
entry/exit (R-Conseq) recasts (CoqQ `RS_back`/`RS_forward`) and the counter
insensitivity of the invariant absorbed. The counted-loop counterpart of
`DerivTot.forProg_prodChain`. -/
theorem DerivTot.countedProdChain (c : CounterLens σT) {n : ℕ}
    (fam : ℕ → ∀ i, EuclideanSpace ℂ (D i)) (hnorm : ∀ m i, ‖fam m i‖ = 1)
    {ψ₀ ψ₁ : ∀ i, EuclideanSpace ℂ (D i)}
    {hψ₀ : ∀ i, ‖ψ₀ i‖ = 1} {hψ₁ : ∀ i, ‖ψ₁ i‖ = 1}
    (hzero : fam 0 = ψ₀) (hfull : fam n = ψ₁) {BODY : Prog σT D}
    (step : ∀ k, DerivTot
      ((prodA D (fam k) (hnorm k)).mask fun σ => c.get σ = k ∧ k < n) BODY
      ((prodA D (fam (k + 1)) (hnorm (k + 1))).mask fun σ => c.get σ = k ∧ k < n)) :
    DerivTot (prodA D ψ₀ hψ₀) (countedProg c (fun _ => n) BODY)
      ((prodA D ψ₁ hψ₁).mask fun σ => c.get σ = n) :=
  DerivTot.conseq (prodA_le hzero.symm)
    (DerivTot.countedWhile_const c (J := fun m => prodA D (fam m) (hnorm m))
      (fun _ _ _ => rfl) step)
    (Assn.mask_le_mask (fun _ h => h)
      fun _ _ => le_of_eq (by rw [prodA_op, prodA_op, hfull]))

/-- **The relativised counted product-state chain**: the bound `N` is read from
the store and pinned to the literal `n` under the frame predicate `φ`, and both
endpoints stay masked by `φ`:

```
⊢ₜ {(⊗ᵢ (ψ₀)ᵢ) ∧ φ}  cnt := 0 ; while cnt < N do BODY ; cnt := cnt + 1 od
    {(⊗ᵢ (ψ₁)ᵢ) ∧ φ}.
```

The conclusion has exactly the shape of a step obligation of an outer
`DerivTot.countedWhile_const`, so a nested counted loop is fed back as one
call; where `φ` is false every mask is false and the obligations close
trivially. The endpoint identities may use `φ` (e.g. a bound `k < n` an outer
mask provides). -/
theorem DerivTot.countedProdChain_rel (c : CounterLens σT) {N : σT → ℕ} (n : ℕ)
    {φ : σT → Prop}
    (hφ : ∀ σ v, φ (c.set σ v) ↔ φ σ) (hN : ∀ σ, φ σ → N σ = n)
    (fam : ℕ → ∀ i, EuclideanSpace ℂ (D i)) (hnorm : ∀ m i, ‖fam m i‖ = 1)
    {ψ₀ ψ₁ : ∀ i, EuclideanSpace ℂ (D i)}
    {hψ₀ : ∀ i, ‖ψ₀ i‖ = 1} {hψ₁ : ∀ i, ‖ψ₁ i‖ = 1}
    (hzero : ∀ σ, φ σ → fam 0 = ψ₀) (hfull : ∀ σ, φ σ → fam n = ψ₁)
    {BODY : Prog σT D}
    (step : ∀ k, DerivTot
      ((prodA D (fam k) (hnorm k)).mask fun σ => φ σ ∧ c.get σ = k ∧ k < n) BODY
      ((prodA D (fam (k + 1)) (hnorm (k + 1))).mask
        fun σ => φ σ ∧ c.get σ = k ∧ k < n)) :
    DerivTot ((prodA D ψ₀ hψ₀).mask φ) (countedProg c N BODY)
      ((prodA D ψ₁ hψ₁).mask φ) :=
  DerivTot.conseq
    (Assn.mask_le_mask (fun _ h => h)
      fun σ hσ => le_of_eq (by rw [prodA_op, prodA_op, hzero σ hσ]))
    (DerivTot.countedWhile c hφ hN (J := fun m => prodA D (fam m) (hnorm m))
      (fun _ _ _ => rfl) step)
    (Assn.mask_le_mask (fun _ h => h.1)
      fun σ hσ => le_of_eq (by rw [prodA_op, prodA_op, hfull σ hσ.1]))


/-- Source total-loop variant with a store-indexed invariant step and an
independent identity-predicate body derivation. -/
theorem DerivTot.countedProdChainSource (c : CounterLens σT) {n : ℕ}
    (fam : ℕ → ∀ i, EuclideanSpace ℂ (D i)) (hnorm : ∀ m i, ‖fam m i‖ = 1)
    {ψ₀ ψ₁ : ∀ i, EuclideanSpace ℂ (D i)}
    {hψ₀ : ∀ i, ‖ψ₀ i‖ = 1} {hψ₁ : ∀ i, ‖ψ₁ i‖ = 1}
    (hzero : fam 0 = ψ₀) (hfull : fam n = ψ₁) {BODY : Prog σT D}
    (step : DerivTot
      ((Assn.ofFam c.get (fun m => prodA D (fam m) (hnorm m))).mask fun σ => c.get σ < n) BODY
      ((Assn.ofFam c.get (fun m => prodA D (fam (m + 1)) (hnorm (m + 1)))).mask
        fun σ => c.get σ < n))
    (hidentity : ∀ k, DerivTot
      ((Assn.one : Assn σT D).mask fun σ => c.get σ = k ∧ k < n) BODY
      ((Assn.one : Assn σT D).mask fun σ => c.get σ = k ∧ k < n)) :
    DerivTot (prodA D ψ₀ hψ₀) (countedProg c (fun _ => n) BODY)
      ((prodA D ψ₁ hψ₁).mask fun σ => c.get σ = n) :=
  DerivTot.conseq (prodA_le hzero.symm)
    (DerivTot.countedWhile_constSource c (J := fun m => prodA D (fam m) (hnorm m))
      (fun _ _ _ => rfl) step hidentity)
    (Assn.mask_le_mask (fun _ h => h)
      fun _ _ => le_of_eq (by rw [prodA_op, prodA_op, hfull]))

/-- Source total-loop variant with a store-indexed invariant step and an
independent identity-predicate body derivation. -/
theorem DerivTot.countedProdChain_relSource (c : CounterLens σT) {N : σT → ℕ} (n : ℕ)
    {φ : σT → Prop}
    (hφ : ∀ σ v, φ (c.set σ v) ↔ φ σ) (hN : ∀ σ, φ σ → N σ = n)
    (fam : ℕ → ∀ i, EuclideanSpace ℂ (D i)) (hnorm : ∀ m i, ‖fam m i‖ = 1)
    {ψ₀ ψ₁ : ∀ i, EuclideanSpace ℂ (D i)}
    {hψ₀ : ∀ i, ‖ψ₀ i‖ = 1} {hψ₁ : ∀ i, ‖ψ₁ i‖ = 1}
    (hzero : ∀ σ, φ σ → fam 0 = ψ₀) (hfull : ∀ σ, φ σ → fam n = ψ₁)
    {BODY : Prog σT D}
    (step : DerivTot
      ((Assn.ofFam c.get (fun m => prodA D (fam m) (hnorm m))).mask fun σ => φ σ ∧ c.get σ < n) BODY
      ((Assn.ofFam c.get (fun m => prodA D (fam (m + 1)) (hnorm (m + 1)))).mask
        fun σ => φ σ ∧ c.get σ < n))
    (hidentity : ∀ k, DerivTot
      ((Assn.one : Assn σT D).mask fun σ => φ σ ∧ c.get σ = k ∧ k < n) BODY
      ((Assn.one : Assn σT D).mask fun σ => φ σ ∧ c.get σ = k ∧ k < n)) :
    DerivTot ((prodA D ψ₀ hψ₀).mask φ) (countedProg c N BODY)
      ((prodA D ψ₁ hψ₁).mask φ) :=
  DerivTot.conseq
    (Assn.mask_le_mask (fun _ h => h)
      fun σ hσ => le_of_eq (by rw [prodA_op, prodA_op, hzero σ hσ]))
    (DerivTot.countedWhileSource c hφ hN (J := fun m => prodA D (fam m) (hnorm m))
      (fun _ _ _ => rfl) step hidentity)
    (Assn.mask_le_mask (fun _ h => h.1)
      fun σ hσ => le_of_eq (by rw [prodA_op, prodA_op, hfull σ hσ.1]))

end Qhl
