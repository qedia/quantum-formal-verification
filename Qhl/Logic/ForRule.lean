import Qhl.Logic.Rules
import Qhl.Program.For
import Qhl.HSpace.LocalGate

/-!
# The `for`-loop rules of `QHL⁺_tot`

CoqQ proves its `for` loops **inside the library**, by unrolling the
`\big[seqc_/skip_]` fold with `big_nil`/`big_cons`, so that an example never
performs an induction over the loop: `AxV_UTFP_seq`
(`example/coqq_paper/qhl.v:2146`) and its corollaries `AxV_UTFP`
(`qhl.v:2159`), `AxV_UTFP_tuple`, `AxV_UTFP_ffun`. This file is that layer.

* `DerivTot.forProg` — the **seq-unroll skeleton** (the induction of CoqQ's
  `AxV_UTFP_seq`, isolated): for any body family and any precondition
  transformer discharging each body, the `for` fold is derivable with the fold
  of the transformers as precondition. Nothing quantum happens here: (Ax-Ski)
  at the empty list, (R-Seq) at a cons.
* `DerivTot.forProg_parallelUnitary` — the **parallel disjoint-unitary rule**,
  our form of CoqQ's `AxV_UTFP`: over a duplicate-free list of cells the loop
  `for a in l do a *= U a` takes the product state `⊗ᵢ ψᵢ` to the product state
  with `U a` applied at every cell of `l`. `l.Nodup` **is** the pairwise
  disjointness `[disjoint mset (x i) & mset (x j)]` of CoqQ's hypothesis: the
  registers are the one-cell registers `Reg.single a`, whose supports are
  disjoint exactly when the cells differ. The conclusion is CoqQ's
  `(\ten_i '[Uf i; x i]) \· Q` already pushed through `tentf_tuple_apply` —
  here the library bridge `liftF_singleGate_prodV`, the `k = 1` corollary of
  the arity-general block bridge `liftF_regOp_tenv` — so the tensor of the
  gates applied to a product state is displayed as the product state of the
  applied factors.

Everything is generic in the world `L`, the cell types `D`, the gate family
`U`, the state family `ψ` and the classical state space `σT`; no example
fixture and no particular gate appears. The single induction over the loop
lives here, exactly as in CoqQ, so a consumer discharges its loop with one
rule application and no invariant, no ranking function and no unrolling.
-/

namespace Qhl

open Finset
open scoped ComplexInnerProductSpace ComplexOrder

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)]
variable {σT : Type*}

/-! ## §1. Constant pure-state assertions -/

/-- The assertion "the world is in the state `v`" — the projector `|v⟩⟨v|` in
every classical state, i.e. the endpoint shape of CoqQ's state triples
`⊨s {P} c {Q}`. -/
noncomputable def Assn.ofState (v : HS D (univ : Finset L)) (hv : ‖v‖ = 1) : Assn σT D :=
  ⟨fun _ => outerLM v v, fun _ => isEffect_outerLM_self hv⟩

@[simp]
theorem Assn.ofState_op (v : HS D (univ : Finset L)) (hv : ‖v‖ = 1) (σ : σT) :
    (Assn.ofState (σT := σT) v hv).op σ = outerLM v v := rfl

/-- Pure-state assertions on equal states entail each other: the norm witness
is a proof and carries no information. -/
theorem Assn.ofState_le_ofState {v w : HS D (univ : Finset L)} {hv : ‖v‖ = 1} {hw : ‖w‖ = 1}
    (h : v = w) : (Assn.ofState (σT := σT) v hv) ≤ Assn.ofState w hw :=
  fun _ => le_of_eq (by rw [Assn.ofState_op, Assn.ofState_op, h])

/-! ## §2. Unit product states -/

/-- A product state of unit factors is a unit vector (library `norm_prodV`,
CoqQ `tenvm_norm`). -/
theorem norm_prodV_eq_one {W : Finset L} (ψ : ∀ i, EuclideanSpace ℂ (D i))
    (hψ : ∀ i, ‖ψ i‖ = 1) : ‖prodV D (W := W) ψ‖ = 1 := by
  rw [norm_prodV D (W := W) ψ]
  exact Finset.prod_eq_one fun i _ => hψ (i : L)

/-- A bundled unitary fixes the unit sphere. -/
theorem norm_unitaryOp_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (U : UnitaryOp E) {v : E} (hv : ‖v‖ = 1) :
    ‖(U : E →ₗ[ℂ] E) v‖ = 1 :=
  norm_eq_one_of_isUnitary U.2 hv

/-- Applying a unitary at one cell keeps every factor a unit vector. -/
theorem norm_update_eq_one (a : L) (U : UnitaryOp (EuclideanSpace ℂ (D a)))
    (ψ : ∀ i, EuclideanSpace ℂ (D i)) (hψ : ∀ i, ‖ψ i‖ = 1) (i : L) :
    ‖Function.update ψ a ((U : EuclideanSpace ℂ (D a) →ₗ[ℂ] EuclideanSpace ℂ (D a)) (ψ a)) i‖
      = 1 := by
  by_cases h : i = a
  · subst h
    rw [Function.update_self]
    exact norm_unitaryOp_apply U (hψ i)
  · rw [Function.update_of_ne h]
    exact hψ i

/-! ## §3. The loop body: (Ax-Uni) at a one-cell register, on a product state -/

/-- CoqQ's one-cell gate statement `[ut x.[i] := H]` (`qwhile.v:429`): here the
cell *is* the index, so `[ut a := U]` is
`Prog.unitary1 (fun _ => a) (fun _ => singleGate _ a U)` — the exact shape of
the loop body below. It lives in this file rather than next to `Prog.unitary1`
because `singleGate` (`Qhl/HSpace/LocalGate.lean`) is not in scope in
`Qhl/Program/Syntax.lean`, and this is the lowest file importing both. -/
scoped syntax:max (priority := high) "[" &"ut " term " := " term "]" : term

scoped macro_rules
  | `([ut $a := $U]) => `(Qhl.Prog.unitary1 (fun _ => $a) fun _ => Qhl.singleGate _ $a $U)

/-- The register expression of `Prog.unitary1` at a constant cell is the
one-cell register `Reg.single`, so the two cylindrical extensions agree. -/
theorem regLift_mk_of_single (a : L) (h : Function.Injective (fun _ : Fin 1 => a))
    (A : TSpace D (⟨fun _ : Fin 1 => a, h⟩ : Reg L 1).toFun →ₗ[ℂ]
      TSpace D (⟨fun _ : Fin 1 => a, h⟩ : Reg L 1).toFun) :
    regLift (D := D) (⟨fun _ : Fin 1 => a, h⟩ : Reg L 1) A = regLift (Reg.single a) A := rfl

/-- The whole-world form of the one-site bridge `liftF_singleGate_prodV` (CoqQ
`tentf_tuple_apply` under `lift_lf`, the `k = 1` corollary of the
arity-general `liftF_regOp_tenv`): the program-level lift of a one-cell gate
acts on the single factor it names and fixes the others. -/
theorem regLift_singleGate_prodV (a : L) (U : UnitaryOp (EuclideanSpace ℂ (D a)))
    (ψ : ∀ i, EuclideanSpace ℂ (D i)) :
    regLift (Reg.single a) (singleGate D a U) (prodV D (W := (univ : Finset L)) ψ)
      = prodV D (W := (univ : Finset L))
          (Function.update ψ a
            ((U : EuclideanSpace ℂ (D a) →ₗ[ℂ] EuclideanSpace ℂ (D a)) (ψ a))) :=
  liftF_singleGate_prodV D a (subset_univ _) U ψ

/-- The (Ax-Uni) precondition of a pure product-state postcondition: `U†|w⟩⟨w|U
= |ψ⟩⟨ψ|` when `U` sends `⊗ᵢψᵢ` to `w`. This is the whole computation of the
loop body — `adjoint_comp_outerLM_comp` to move the conjugation onto the
vectors, the bridge above backwards, and `adjoint_apply_apply` for `U†U = 1`
pointwise. -/
theorem adjoint_conj_outerLM_prodV (a : L) (U : UnitaryOp (EuclideanSpace ℂ (D a)))
    (ψ : ∀ i, EuclideanSpace ℂ (D i)) :
    LinearMap.adjoint (regLift (Reg.single a) (singleGate D a U))
        ∘ₗ outerLM
            (prodV D (W := (univ : Finset L))
              (Function.update ψ a
                ((U : EuclideanSpace ℂ (D a) →ₗ[ℂ] EuclideanSpace ℂ (D a)) (ψ a))))
            (prodV D (W := (univ : Finset L))
              (Function.update ψ a
                ((U : EuclideanSpace ℂ (D a) →ₗ[ℂ] EuclideanSpace ℂ (D a)) (ψ a))))
        ∘ₗ regLift (Reg.single a) (singleGate D a U)
      = outerLM (prodV D (W := (univ : Finset L)) ψ) (prodV D (W := (univ : Finset L)) ψ) := by
  rw [adjoint_comp_outerLM_comp, ← regLift_singleGate_prodV a U ψ,
    adjoint_apply_apply (isUnitary_regLift (Reg.single a) (singleGate D a U))]

/-- **(Ax-Uni) on a product state** — the body of the parallel loop rule: the
one-cell gate `U` on the cell `a` sends `|⊗ᵢψᵢ⟩⟨⊗ᵢψᵢ|` to the same projector
with the factor at `a` replaced by `U ψₐ`. `Dist(q̄)` is free for a one-cell
register, so the transformer never falls into the `0` branch (V7). -/
theorem DerivTot.unitary1_prodV (a : L) (U : UnitaryOp (EuclideanSpace ℂ (D a)))
    (ψ : ∀ i, EuclideanSpace ℂ (D i)) (hψ : ∀ i, ‖ψ i‖ = 1) :
    DerivTot (σT := σT)
      (Assn.ofState (prodV D (W := (univ : Finset L)) ψ) (norm_prodV_eq_one ψ hψ))
      (Prog.unitary1 (fun _ => a) fun _ => singleGate D a U)
      (Assn.ofState
        (prodV D (W := (univ : Finset L))
          (Function.update ψ a
            ((U : EuclideanSpace ℂ (D a) →ₗ[ℂ] EuclideanSpace ℂ (D a)) (ψ a))))
        (norm_prodV_eq_one _ (norm_update_eq_one a U ψ hψ))) := by
  have hinj : Function.Injective (fun _ : Fin 1 => a) := fun i j _ => Subsingleton.elim i j
  refine DerivTot.conseq ?_
    (DerivTot.unitary (fun _ (_ : Fin 1) => a) (fun _ => singleGate D a U) _)
    (Assn.le_refl' _)
  intro σ
  refine le_of_eq (Eq.symm (Eq.trans (Assn.unitaryPre_op_of_dist _ _ _ (σ := σ) hinj) ?_))
  rw [Assn.ofState_op, regLift_mk_of_single]
  exact adjoint_conj_outerLM_prodV a U ψ

/-! ## §4. The seq-unroll skeleton (CoqQ `AxV_UTFP_seq`) -/

/-- **The `for`-loop rule of `QHL⁺_tot`**, in its purely structural form: if
every body `C i` is derivable from the transformed postcondition `pre i B` for
every `B`, then the `for` fold over the index list is derivable with the fold
of the transformers as precondition. This is the `\big[seqc_/skip_]` unrolling
(`big_nil`/`big_cons`) that CoqQ's `AxV_UTFP_seq` performs, isolated from
anything quantum: (Ax-Ski) at the empty list, (R-Seq) at a cons. -/
theorem DerivTot.forProg {ι : Type*} {C : ι → Prog σT D}
    {pre : ι → Assn σT D → Assn σT D}
    (h : ∀ i B, DerivTot (pre i B) (C i) B) :
    ∀ (l : List ι) (A : Assn σT D), DerivTot (l.foldr pre A) (Qhl.forProg l C) A
  | [], A => DerivTot.skip A
  | i :: l, A => DerivTot.seq (h i _) (DerivTot.forProg h l A)

/-! ## §5. The parallel disjoint-unitary rule (CoqQ `AxV_UTFP`) -/

/-- The state family `ψ` with the gate `U a` applied at every cell of `l`:
CoqQ's `\ten_(i <- r) '[Uf i; x i]` applied to `⊗ᵢψᵢ`, in the form
`tentf_tuple_apply` puts it — a product state again. -/
noncomputable def applyOn (l : List L) (U : ∀ a : L, UnitaryOp (EuclideanSpace ℂ (D a)))
    (ψ : ∀ a : L, EuclideanSpace ℂ (D a)) (a : L) : EuclideanSpace ℂ (D a) :=
  if a ∈ l then (U a : EuclideanSpace ℂ (D a) →ₗ[ℂ] EuclideanSpace ℂ (D a)) (ψ a) else ψ a

/-- Over the empty list nothing is applied (CoqQ `big_nil`). -/
@[simp]
theorem applyOn_nil (U : ∀ a : L, UnitaryOp (EuclideanSpace ℂ (D a)))
    (ψ : ∀ a : L, EuclideanSpace ℂ (D a)) : applyOn [] U ψ = ψ :=
  funext fun _ => if_neg (by simp)

/-- One unrolling (CoqQ `big_cons`): applying `U a` at the cell `a` and then
the gates of `l` is applying the gates of `a :: l`. The disjointness
hypothesis `a ∉ l` is used here and **only** here — this equality is exactly
what fails when a cell is touched twice. -/
theorem applyOn_cons {a : L} {l : List L} (ha : a ∉ l)
    (U : ∀ b : L, UnitaryOp (EuclideanSpace ℂ (D b)))
    (ψ : ∀ b : L, EuclideanSpace ℂ (D b)) :
    applyOn l U
        (Function.update ψ a
          ((U a : EuclideanSpace ℂ (D a) →ₗ[ℂ] EuclideanSpace ℂ (D a)) (ψ a)))
      = applyOn (a :: l) U ψ := by
  funext b
  by_cases hb : b = a
  · subst hb
    simp [applyOn, ha]
  · simp [applyOn, hb, List.mem_cons]

/-- Every factor of the transformed family is still a unit vector. -/
theorem norm_applyOn (l : List L) (U : ∀ a : L, UnitaryOp (EuclideanSpace ℂ (D a)))
    (ψ : ∀ a : L, EuclideanSpace ℂ (D a)) (hψ : ∀ a, ‖ψ a‖ = 1) (a : L) :
    ‖applyOn l U ψ a‖ = 1 := by
  rw [applyOn]
  split
  · exact norm_unitaryOp_apply (U a) (hψ a)
  · exact hψ a

/-- **The parallel disjoint-unitary rule** — CoqQ's `AxV_UTFP` (`qhl.v:2159`),
proved the way CoqQ proves it, by the `AxV_UTFP_seq` fold-unrolling
(`qhl.v:2146`) inside the library:

```
⊢ₜ {⊗ᵢ ψᵢ}  for a in l do a *= U a  {(⊗_{a ∈ l} Uₐ) · ⊗ᵢ ψᵢ}
```

The registers are the one-cell registers `Reg.single a`, so CoqQ's pairwise
disjointness hypothesis `∀ i j, i ≠ j → [disjoint mset (x i) & mset (x j)]`
becomes `l.Nodup`: no cell is touched twice, which is what makes the loop a
*parallel* application of a tensor of gates. The postcondition is CoqQ's
`U \· Q` after `tentf_tuple_apply` — the tensor of the gates applied to a
product state is the product state of the applied factors (`applyOn`) — via
the library bridge `liftF_singleGate_prodV`.

Generic in the world `L`, the cell-type family `D`, the gate family `U`, the
state family `ψ` and the classical state space `σT`. The induction over the
loop lives here and nowhere else: a consumer discharges its `for` loop with
one application of this theorem. -/
theorem DerivTot.forProg_parallelUnitary (l : List L) (hl : l.Nodup)
    (U : ∀ a : L, UnitaryOp (EuclideanSpace ℂ (D a)))
    (ψ : ∀ a : L, EuclideanSpace ℂ (D a)) (hψ : ∀ a, ‖ψ a‖ = 1) :
    DerivTot (σT := σT)
      (Assn.ofState (prodV D (W := (univ : Finset L)) ψ) (norm_prodV_eq_one ψ hψ))
      (Qhl.forProg l fun a => Prog.unitary1 (fun _ => a) fun _ => singleGate D a (U a))
      (Assn.ofState (prodV D (W := (univ : Finset L)) (applyOn l U ψ))
        (norm_prodV_eq_one _ (norm_applyOn l U ψ hψ))) := by
  induction l generalizing ψ with
  | nil =>
      exact DerivTot.conseq (Assn.le_refl' _) (DerivTot.skip _)
        (Assn.ofState_le_ofState (congrArg (prodV D (W := (univ : Finset L))) (applyOn_nil U ψ)))
  | cons a l ih =>
      obtain ⟨ha, hl'⟩ := List.nodup_cons.mp hl
      exact DerivTot.conseq (Assn.le_refl' _)
        (DerivTot.seq (DerivTot.unitary1_prodV a (U a) ψ hψ)
          (ih hl' _ (norm_update_eq_one a (U a) ψ hψ)))
        (Assn.ofState_le_ofState
          (congrArg (prodV D (W := (univ : Finset L))) (applyOn_cons ha U ψ)))

end Qhl
