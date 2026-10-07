import Qhl.Logic.ForRule
import Qhl.Gate.Phase

/-!
# The frame / `n → m` qubit-embedding rules of `QHL⁺_tot` at a unitary step

CoqQ's frame rules `RV_Frame` and `RV_Framel` (`example/coqq_paper/qhl.v:1815`
and `:1824`) transport a proved triple across an untouched region:

```
[disjoint (fvars c) & W] → ⊨s {P} c {Q} → ⊨s {P ⊗ R} c {Q ⊗ R}
```

and `QFT_sub_cast` (`example/coqq_paper/example.v:176`) is the *register-recast*
reuse mechanism that goes with them: one and the same subroutine proof is
consumed at a different placement of the cells, the recast being nothing but a
reindexing. This file is that layer for a **unitary step**.

* `pairGate`, `Prog.unitary2` — a gate proved on its **own two-cell world**
  `EuclideanSpace ℂ (D a × D b)` (e.g. `CNOT`, `cphase` on `Bool × Bool`),
  transported to the tuple space of the two-cell register `Reg.pair a b`, and
  the program `[ut (a, b) := G]` that applies it. This is the `k = 2` analogue
  of `singleGate`/`Prog.unitary1`.
* `regLift_pairGate_prodV` — the **`k = 2` block bridge**: the whole-world lift
  of such a gate acts on the two factors it names and fixes every other factor.
  The `k = 1` case is the library's `liftF_singleGate_prodV`; both are corollaries
  of the arity-general block bridge `liftF_regOp_tenv` (CoqQ `lift_lf`).
* `DerivTot.unitary_pair_prodV` — **the workhorse**: (Ax-Uni) plus the frame, at
  a pair of cells, on a product state. Its gate hypothesis
  `hG : G (ψ a ⊗ ψ b) = u' ⊗ v'` lives *entirely inside the gate's own two-cell
  world* — the `n = 2` computation — and the theorem consumes it at an arbitrary
  pair of cells `a ≠ b` of an arbitrary world `L` — the `m`-cell circuit — with
  the whole complement framed. A two-qubit fact proved once is therefore reusable
  at every placement, with no re-derivation and no `m`-dependent bookkeeping.
* `DerivTot.unitary_tenv` — the **arity-general** form, stated in exactly CoqQ's
  `{P} S {Q} ⊢ {P ⊗ R} S {Q ⊗ R}` shape: for a register `r` of any arity, the
  state splits as `v ⊗ R` with `v` on `r.sig` and the frame `R` on the complement
  `univ \ r.sig`, and the step moves `v` to `r.op U v` leaving `R` alone.
  Disjointness — CoqQ's `[disjoint (fvars c) & W]` — is structural here: the
  frame lives on `univ \ r.sig` by construction, so no side condition is needed.

**Nothing is postulated.** Every derivation in this file is built from the two
`DerivTot` constructors `.unitary` (Ax-Uni) and `.conseq` (R-Conseq) alone, with
the library tensor bridge (`liftF_regOp_tenv` / `prodV_split`) doing the
transport: no new axiom, no new rule primitive, no appeal to soundness.

Everything is generic in the world `L`, the cell-type family `D`, the gate, the
state and the classical state space `σT`; no example fixture appears.
-/

namespace Qhl

open Finset
open scoped ComplexInnerProductSpace ComplexOrder

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)]
variable {σT : Type*}

/-! ## §1. The coordinates of a two-cell register

`Reg.equivSig` is an `Equiv.ofBijective` and does not compute, and for a
non-constant cell family `D` the reindexing `Reg.idxEquiv` carries an
`Equiv.cast` at each cell. Both are pinned here once, at the two cells of
`Reg.pair`, so that no later proof meets them. -/

omit [Fintype L] [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)] [∀ i, Inhabited (D i)] in
/-- The value of `Reg.idxEquiv` at a cell whose index is *known*: the cast that
`idxEquiv` carries is a cast along a proof of an equality of types, so once the
index is pinned it disappears by proof irrelevance. -/
theorem Reg.idxEquiv_apply_of_symm {k : ℕ} (r : Reg L k) (t : TIdx D r.toFun)
    (j : ↥r.sig) (i : Fin k) (hij : r.equivSig.symm j = i) (h2 : r i = (j : L)) :
    r.idxEquiv D t j = Equiv.cast (congrArg D h2) (t i) := by
  subst hij; rfl

omit [Fintype L] in
/-- The `Reg.equivSig` pin for a two-cell register: the index of a cell of
`{a, b}` is `1` at `b` and `0` at `a`. Proved through `Equiv.symm_apply_eq`
(the Bell-example trick) because `equivSig` does not reduce. -/
theorem Reg.equivSig_symm_pair (a b : L) (hab : a ≠ b) (j : ↥(Reg.pair a b hab).sig) :
    (Reg.pair a b hab).equivSig.symm j = (if (j : L) = b then 1 else 0 : Fin 2) := by
  rw [Equiv.symm_apply_eq]
  refine Subtype.ext ?_
  rw [Reg.coe_equivSig]
  have h2 : (j : L) ∈ ({a, b} : Finset L) := by
    rw [← Reg.sig_pair a b hab]; exact j.2
  have hj : (j : L) = a ∨ (j : L) = b := by simpa [Finset.mem_insert] using h2
  split_ifs with h
  · exact h
  · rcases hj with h1 | h1
    · exact h1
    · exact absurd h1 h

/-- A classical state of a two-cell register, read at its first cell. -/
theorem Reg.idxEquiv_pair_fst (a b : L) (hab : a ≠ b)
    (t : TIdx D (Reg.pair a b hab).toFun) (ha : a ∈ (Reg.pair a b hab).sig) :
    (Reg.pair a b hab).idxEquiv D t ⟨a, ha⟩ = t 0 :=
  Reg.idxEquiv_apply_of_symm _ t ⟨a, ha⟩ 0
    (by rw [Reg.equivSig_symm_pair]; exact if_neg hab) rfl

/-- A classical state of a two-cell register, read at its second cell. -/
theorem Reg.idxEquiv_pair_snd (a b : L) (hab : a ≠ b)
    (t : TIdx D (Reg.pair a b hab).toFun) (hb : b ∈ (Reg.pair a b hab).sig) :
    (Reg.pair a b hab).idxEquiv D t ⟨b, hb⟩ = t 1 :=
  Reg.idxEquiv_apply_of_symm _ t ⟨b, hb⟩ 1
    (by rw [Reg.equivSig_symm_pair]; exact if_pos rfl) rfl

/-! ## §2. The two-cell transport (CoqQ `tv2v`/`tf2f` at arity 2) -/

variable (D)

/-- The gate's own two-cell world as the tuple space of a two-cell register:
the `k = 2` analogue of `tupleOne`. `(Reg.pair a b hab) 0` and `... 1` reduce to
`a` and `b`, so `D a × D b` *is* the pair type of the register's cell types —
Decision H1 (casts are reindexings) is respected: this is `euclCongr` of a
bijection of index types, never an `Eq.rec`. -/
noncomputable def pairIso (a b : L) (hab : a ≠ b) :
    EuclideanSpace ℂ (D a × D b) ≃ₗᵢ[ℂ] TSpace D (Reg.pair a b hab).toFun :=
  euclCongr (piFinTwoEquiv fun i => D ((Reg.pair a b hab).toFun i)).symm

omit [Fintype L] [DecidableEq L] [∀ i, Inhabited (D i)] in
@[simp]
theorem pairIso_apply (a b : L) (hab : a ≠ b) (w : EuclideanSpace ℂ (D a × D b))
    (y : TIdx D (Reg.pair a b hab).toFun) : pairIso D a b hab w y = w (y 0, y 1) := rfl

/-- The gate's own two-cell world as the labelled space of the two cells:
`pairIso` followed by `Reg.encode`. The `k = 2` analogue of `singleIso`
(CoqQ `tv2v`, `qmem.v:157`). -/
noncomputable def pairEnc (a b : L) (hab : a ≠ b) :
    EuclideanSpace ℂ (D a × D b) ≃ₗᵢ[ℂ] HS D (Reg.pair a b hab).sig :=
  (pairIso D a b hab).trans ((Reg.pair a b hab).encode D)

variable {D}

theorem pairEnc_apply_idxEquiv (a b : L) (hab : a ≠ b)
    (w : EuclideanSpace ℂ (D a × D b)) (t : TIdx D (Reg.pair a b hab).toFun) :
    pairEnc D a b hab w ((Reg.pair a b hab).idxEquiv D t) = w (t 0, t 1) := by
  change (Reg.pair a b hab).encode D (pairIso D a b hab w) _ = _
  rw [Reg.encode_apply, Equiv.symm_apply_apply, pairIso_apply]

/-- The coordinates of a product state over the two cells of a pair register. -/
theorem prodV_apply_idxEquiv_pair (a b : L) (hab : a ≠ b)
    (ψ : ∀ i, EuclideanSpace ℂ (D i)) (t : TIdx D (Reg.pair a b hab).toFun) :
    prodV D (W := (Reg.pair a b hab).sig) ψ ((Reg.pair a b hab).idxEquiv D t)
      = ψ a (t 0) * ψ b (t 1) := by
  have ha : a ∈ (Reg.pair a b hab).sig := (Reg.pair a b hab).apply_mem_sig 0
  have hb : b ∈ (Reg.pair a b hab).sig := (Reg.pair a b hab).apply_mem_sig 1
  rw [prodV_apply, ← Equiv.prod_comp (Reg.pair a b hab).equivSig, Fin.prod_univ_two]
  change ψ a ((Reg.pair a b hab).idxEquiv D t ⟨a, ha⟩)
      * ψ b ((Reg.pair a b hab).idxEquiv D t ⟨b, hb⟩) = _
  rw [Reg.idxEquiv_pair_fst, Reg.idxEquiv_pair_snd]

/-- **The pair-block collapse** — the `k = 2` analogue of `prodV_sig_single`:
the product state over the two cells of `Reg.pair a b` is the transport of the
two-factor product vector `ψ a ⊗ ψ b` of the gate's own world (CoqQ
`t2tv_tuple`/`tenvm` at arity 2). This is what lets a fact stated with `vpair`
— i.e. stated about the gate alone — be read on a register's block factor. -/
theorem prodV_sig_pair (a b : L) (hab : a ≠ b) (ψ : ∀ i, EuclideanSpace ℂ (D i)) :
    prodV D (W := (Reg.pair a b hab).sig) ψ
      = pairEnc D a b hab (vpair (ψ a) (ψ b)) := by
  refine PiLp.ext fun x => ?_
  obtain ⟨t, rfl⟩ := ((Reg.pair a b hab).idxEquiv D).surjective x
  rw [prodV_apply_idxEquiv_pair, pairEnc_apply_idxEquiv, vpair_apply]

/-- A two-cell gate, moved to the tuple space of the two-cell register — the
shape a program's two-cell unitary gate has. The `k = 2` analogue of
`singleGate`; the same device as the Bell example's
`euclCongrOp (piFinTwoEquiv _).symm CNOT`, but for an arbitrary cell family. -/
noncomputable def pairGate (a b : L) (hab : a ≠ b)
    (G : UnitaryOp (EuclideanSpace ℂ (D a × D b))) :
    UnitaryOp (TSpace D (Reg.pair a b hab).toFun) :=
  euclCongrOp (piFinTwoEquiv fun i => D ((Reg.pair a b hab).toFun i)).symm G

omit [Fintype L] [DecidableEq L] [∀ i, Inhabited (D i)] in
/-- `pairGate` is `G` read through `pairIso`: the transported gate does to the
transported vector what `G` does to the vector. -/
theorem pairGate_apply_pairIso (a b : L) (hab : a ≠ b)
    (G : UnitaryOp (EuclideanSpace ℂ (D a × D b))) (w : EuclideanSpace ℂ (D a × D b)) :
    (pairGate a b hab G :
        TSpace D (Reg.pair a b hab).toFun →ₗ[ℂ] TSpace D (Reg.pair a b hab).toFun)
        (pairIso D a b hab w)
      = pairIso D a b hab ((G : EuclideanSpace ℂ (D a × D b) →ₗ[ℂ] _) w) := by
  change (pairIso D a b hab) ((G : EuclideanSpace ℂ (D a × D b) →ₗ[ℂ] _)
    ((pairIso D a b hab).symm ((pairIso D a b hab) w))) = _
  rw [LinearIsometryEquiv.symm_apply_apply]

/-- The register transport `Reg.op` of a `pairGate` is `G` itself, read through
`pairEnc` (CoqQ `tf2f` at arity 2). -/
theorem regOp_pairGate_pairEnc (a b : L) (hab : a ≠ b)
    (G : UnitaryOp (EuclideanSpace ℂ (D a × D b))) (w : EuclideanSpace ℂ (D a × D b)) :
    (Reg.pair a b hab).op D
        (pairGate a b hab G :
          TSpace D (Reg.pair a b hab).toFun →ₗ[ℂ] TSpace D (Reg.pair a b hab).toFun)
        (pairEnc D a b hab w)
      = pairEnc D a b hab ((G : EuclideanSpace ℂ (D a × D b) →ₗ[ℂ] _) w) := by
  have h : ((Reg.pair a b hab).encode D).symm (pairEnc D a b hab w) = pairIso D a b hab w :=
    LinearIsometryEquiv.symm_apply_apply _ _
  change (Reg.pair a b hab).encode D
    ((pairGate a b hab G : TSpace D (Reg.pair a b hab).toFun →ₗ[ℂ] _)
      (((Reg.pair a b hab).encode D).symm (pairEnc D a b hab w))) = _
  rw [h, pairGate_apply_pairIso]
  rfl

/-! ## §3. The `k = 2` block bridge -/

/-- The block identity: on the two cells it names, the transported gate does
exactly what the gate hypothesis says. The hypothesis `hG` is a statement about
`G` **in the gate's own world** — no register, no world `L`, no complement. -/
theorem regOp_pairGate_prodV_sig (a b : L) (hab : a ≠ b)
    (G : UnitaryOp (EuclideanSpace ℂ (D a × D b)))
    {u' : EuclideanSpace ℂ (D a)} {v' : EuclideanSpace ℂ (D b)}
    (ψ : ∀ i, EuclideanSpace ℂ (D i))
    (hG : (G : EuclideanSpace ℂ (D a × D b) →ₗ[ℂ] EuclideanSpace ℂ (D a × D b))
        (vpair (ψ a) (ψ b)) = vpair u' v') :
    (Reg.pair a b hab).op D
        (pairGate a b hab G : TSpace D (Reg.pair a b hab).toFun →ₗ[ℂ] _)
        (prodV D (W := (Reg.pair a b hab).sig) ψ)
      = prodV D (W := (Reg.pair a b hab).sig)
          (Function.update (Function.update ψ a u') b v') := by
  rw [prodV_sig_pair, regOp_pairGate_pairEnc, hG, prodV_sig_pair]
  congr 1
  simp only [Function.update_self, Function.update_of_ne hab]

/-- **The `k = 2` block bridge** (CoqQ `lift_lf` on a `tenvm`-split state, the
arity-2 case of the library's `liftF_regOp_tenv`): the whole-world lift of a
two-cell gate acts on the two factors the register names — as prescribed by the
gate's own hypothesis `hG` — and leaves every other factor of the product state
untouched. This is the exact `k = 2` analogue of `regLift_singleGate_prodV`, and
it is the frame rule in vector form: the complement is carried through
unchanged. -/
theorem regLift_pairGate_prodV (a b : L) (hab : a ≠ b)
    (G : UnitaryOp (EuclideanSpace ℂ (D a × D b)))
    {u' : EuclideanSpace ℂ (D a)} {v' : EuclideanSpace ℂ (D b)}
    (ψ : ∀ i, EuclideanSpace ℂ (D i))
    (hG : (G : EuclideanSpace ℂ (D a × D b) →ₗ[ℂ] EuclideanSpace ℂ (D a × D b))
        (vpair (ψ a) (ψ b)) = vpair u' v') :
    regLift (Reg.pair a b hab) (pairGate a b hab G) (prodV D (W := (univ : Finset L)) ψ)
      = prodV D (W := (univ : Finset L)) (Function.update (Function.update ψ a u') b v') := by
  have h : (Reg.pair a b hab).sig ⊆ (univ : Finset L) := subset_univ _
  change liftF D h ((Reg.pair a b hab).op D
    (pairGate a b hab G : TSpace D (Reg.pair a b hab).toFun →ₗ[ℂ] _))
      (prodV D (W := (univ : Finset L)) ψ) = _
  rw [liftF_regOp_prodV, regOp_pairGate_prodV_sig a b hab G ψ hG,
    prodV_split D h (Function.update (Function.update ψ a u') b v')]
  refine congrArg (castH D (union_sdiff_of_subset h)) (congrArg₂ (tenv D) rfl ?_)
  refine prodV_congr D fun i hi => ?_
  have hia : i ≠ a := fun hc =>
    (mem_sdiff.1 hi).2 (by rw [hc]; exact (Reg.pair a b hab).apply_mem_sig 0)
  have hib : i ≠ b := fun hc =>
    (mem_sdiff.1 hi).2 (by rw [hc]; exact (Reg.pair a b hab).apply_mem_sig 1)
  rw [Function.update_of_ne hib, Function.update_of_ne hia]

/-! ## §4. The pair-gate program and the (Ax-Uni)+frame workhorse -/

omit [∀ i, Inhabited (D i)] in
/-- The register expression of `Prog.unitary2` is the constant one, so the two
cylindrical extensions agree — the `Reg`-level analogue of
`regLift_mk_of_single`, by structure eta. -/
theorem regLift_mk_of_const {k : ℕ} (r : Reg L k) {σ : σT}
    (h : Function.Injective ((RegExpr.const (σT := σT) r) σ))
    (A : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun) :
    regLift (D := D) ⟨(RegExpr.const (σT := σT) r) σ, h⟩ A = regLift r A := rfl

omit [Fintype L] [∀ i, DecidableEq (D i)] [∀ i, Inhabited (D i)] in
/-- Applying a two-cell gate keeps every factor a unit vector — the arity-2
analogue of `norm_update_eq_one`. -/
theorem norm_update_update_eq_one (a b : L) {u' : EuclideanSpace ℂ (D a)}
    {v' : EuclideanSpace ℂ (D b)} (ψ : ∀ i, EuclideanSpace ℂ (D i)) (hψ : ∀ i, ‖ψ i‖ = 1)
    (hu' : ‖u'‖ = 1) (hv' : ‖v'‖ = 1) (i : L) :
    ‖Function.update (Function.update ψ a u') b v' i‖ = 1 := by
  by_cases hb : i = b
  · subst hb; rw [Function.update_self]; exact hv'
  · rw [Function.update_of_ne hb]
    by_cases ha : i = a
    · subst ha; rw [Function.update_self]; exact hu'
    · rw [Function.update_of_ne ha]; exact hψ i

/-- CoqQ's two-cell gate statement `[ut (x, y) := G]` (`qwhile.v`, e.g. the QFT's
`[ut (s.1, s.2.[i]) := BControl (PhGate (omegan i))]`, `example.v:164`): the
program applying a gate of the two-cell world `D a × D b` at the two named cells
`a ≠ b`. The `k = 2` analogue of `Prog.unitary1`. -/
noncomputable def Prog.unitary2 (a b : L) (hab : a ≠ b)
    (G : UnitaryOp (EuclideanSpace ℂ (D a × D b))) : Prog σT D :=
  .unitary 2 (RegExpr.const (Reg.pair a b hab)) fun _ => pairGate a b hab G

/-- The (Ax-Uni) precondition of a pure product-state postcondition at a pair of
cells: `U†|w⟩⟨w|U = |ψ⟩⟨ψ|`. `adjoint_comp_outerLM_comp` moves the conjugation
onto the vectors, the block bridge runs backwards, and `adjoint_apply_apply`
supplies `U†U = 1` pointwise — the arity-2 analogue of
`adjoint_conj_outerLM_prodV`. -/
theorem adjoint_conj_outerLM_pair (a b : L) (hab : a ≠ b)
    (G : UnitaryOp (EuclideanSpace ℂ (D a × D b)))
    {u' : EuclideanSpace ℂ (D a)} {v' : EuclideanSpace ℂ (D b)}
    (ψ : ∀ i, EuclideanSpace ℂ (D i))
    (hG : (G : EuclideanSpace ℂ (D a × D b) →ₗ[ℂ] EuclideanSpace ℂ (D a × D b))
        (vpair (ψ a) (ψ b)) = vpair u' v') :
    LinearMap.adjoint (regLift (Reg.pair a b hab) (pairGate a b hab G))
        ∘ₗ outerLM
            (prodV D (W := (univ : Finset L))
              (Function.update (Function.update ψ a u') b v'))
            (prodV D (W := (univ : Finset L))
              (Function.update (Function.update ψ a u') b v'))
        ∘ₗ regLift (Reg.pair a b hab) (pairGate a b hab G)
      = outerLM (prodV D (W := (univ : Finset L)) ψ) (prodV D (W := (univ : Finset L)) ψ) := by
  rw [adjoint_comp_outerLM_comp, ← regLift_pairGate_prodV a b hab G ψ hG,
    adjoint_apply_apply (isUnitary_regLift (Reg.pair a b hab) (pairGate a b hab G))]

/-- **The subroutine-reuse workhorse: (Ax-Uni) + frame at a pair of cells.**

```
⊢ₜ {⊗ᵢ ψᵢ}  (a, b) *= G  {⊗ᵢ ψᵢ with ψₐ ↦ u', ψ_b ↦ v'}   given  G (ψₐ ⊗ ψ_b) = u' ⊗ v'
```

The gate hypothesis `hG` is a statement **entirely inside the gate's own
two-cell world** `EuclideanSpace ℂ (D a × D b)` — the `n = 2` computation, e.g.
`CNOT (∣+⟩ ⊗ ∣0⟩) = …` or `cphase_vpair`. This theorem consumes it at *any* pair
of distinct cells of *any* world `L`: every other factor of the product state is
the frame `R` of CoqQ's `RV_Frame` and is carried through untouched (that is
`regLift_pairGate_prodV`). So a two-qubit subroutine proved once is reusable at
every placement inside an `m`-qubit circuit, with no re-derivation.

Derived from the `DerivTot` constructors `.unitary` (Ax-Uni) and `.conseq`
(R-Conseq) alone, plus the library tensor bridge: no new axiom, no new rule
primitive. `Dist(q̄)` holds by construction (`Reg.pair`'s injectivity), so the
`unitaryPre` transformer never falls into the `0` branch (V7). -/
theorem DerivTot.unitary_pair_prodV (a b : L) (hab : a ≠ b)
    (G : UnitaryOp (EuclideanSpace ℂ (D a × D b)))
    {u' : EuclideanSpace ℂ (D a)} {v' : EuclideanSpace ℂ (D b)}
    (ψ : ∀ i, EuclideanSpace ℂ (D i)) (hψ : ∀ i, ‖ψ i‖ = 1)
    (hG : (G : EuclideanSpace ℂ (D a × D b) →ₗ[ℂ] EuclideanSpace ℂ (D a × D b))
        (vpair (ψ a) (ψ b)) = vpair u' v')
    (hu' : ‖u'‖ = 1) (hv' : ‖v'‖ = 1) :
    DerivTot (σT := σT)
      (Assn.ofState (prodV D (W := (univ : Finset L)) ψ) (norm_prodV_eq_one ψ hψ))
      (Prog.unitary2 a b hab G)
      (Assn.ofState
        (prodV D (W := (univ : Finset L)) (Function.update (Function.update ψ a u') b v'))
        (norm_prodV_eq_one _ (norm_update_update_eq_one a b ψ hψ hu' hv'))) := by
  refine DerivTot.conseq ?_
    (DerivTot.unitary (RegExpr.const (Reg.pair a b hab)) (fun _ => pairGate a b hab G) _)
    (Assn.le_refl' _)
  intro σ
  refine le_of_eq (Eq.symm (Eq.trans
    (Assn.unitaryPre_op_of_dist _ _ _ (σ := σ) (Reg.pair a b hab).inj) ?_))
  rw [Assn.ofState_op]
  exact adjoint_conj_outerLM_pair a b hab G ψ hG

/-! ## §5. The arity-general frame rule (CoqQ `RV_Frame` at a unitary step) -/

omit [∀ i, Inhabited (D i)] in
/-- A split unit vector is a unit vector: `castH` is a `LinearIsometryEquiv` and
the two blocks are disjoint by construction (CoqQ `tenv_norm`). -/
theorem norm_castH_tenv_eq_one {S : Finset L} (v : HS D S) (w : HS D ((univ : Finset L) \ S))
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    ‖castH D (union_sdiff_of_subset (subset_univ S)) (tenv D v w)‖ = 1 := by
  rw [LinearIsometryEquiv.norm_map, tenv_norm D disjoint_sdiff_self_right, hv, hw, mul_one]

omit [Fintype L] [∀ i, Inhabited (D i)] in
/-- `Reg.op` of a bundled unitary is unitary, hence fixes the unit sphere. -/
theorem norm_reg_op_eq_one {k : ℕ} (r : Reg L k) (U : UnitaryOp (TSpace D r.toFun))
    {v : HS D r.sig} (hv : ‖v‖ = 1) :
    ‖r.op D (U : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun) v‖ = 1 :=
  norm_eq_one_of_isUnitary (r.op_isUnitary U.2) hv

omit [∀ i, Inhabited (D i)] in
/-- The whole-world form of the arity-general block bridge `liftF_regGate_tenv`
(CoqQ `lift_lf`): the program-level lift acts as `U` on the register's block and
fixes the frame. -/
theorem regLift_gate_tenv {k : ℕ} (r : Reg L k) (U : UnitaryOp (TSpace D r.toFun))
    (v : HS D r.sig) (w : HS D ((univ : Finset L) \ r.sig)) :
    regLift r (U : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun)
        (castH D (union_sdiff_of_subset (subset_univ r.sig)) (tenv D v w))
      = castH D (union_sdiff_of_subset (subset_univ r.sig))
          (tenv D (r.op D (U : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun) v) w) :=
  liftF_regGate_tenv D r (subset_univ r.sig) U v w

/-- The (Ax-Uni) precondition of a framed pure state: the arity-general
analogue of `adjoint_conj_outerLM_pair`. -/
theorem adjoint_conj_outerLM_tenv {k : ℕ} (r : Reg L k) (U : UnitaryOp (TSpace D r.toFun))
    (v : HS D r.sig) (w : HS D ((univ : Finset L) \ r.sig)) :
    LinearMap.adjoint (regLift r (U : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun))
        ∘ₗ outerLM
            (castH D (union_sdiff_of_subset (subset_univ r.sig))
              (tenv D (r.op D (U : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun) v) w))
            (castH D (union_sdiff_of_subset (subset_univ r.sig))
              (tenv D (r.op D (U : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun) v) w))
        ∘ₗ regLift r (U : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun)
      = outerLM (castH D (union_sdiff_of_subset (subset_univ r.sig)) (tenv D v w))
          (castH D (union_sdiff_of_subset (subset_univ r.sig)) (tenv D v w)) := by
  rw [adjoint_comp_outerLM_comp, ← regLift_gate_tenv r U v w,
    adjoint_apply_apply (isUnitary_regLift r U)]

/-- **The frame rule at a unitary step**, CoqQ's `RV_Frame`/`RV_Framel`
(`qhl.v:1815`, `:1824`) in its unitary instance:

```
⊢ₜ {v ⊗ R}  q̄ *= U  {(U · v) ⊗ R}
```

for a register `r` of **any** arity `k`: the state is split as the block `v` on
the cells `r.sig` the program names and the frame `R` on the untouched
complement `univ \ r.sig`, and the step moves the block by `r.op U` while `R` is
carried through verbatim. CoqQ's side condition `[disjoint (fvars c) & W]` is
structural here — the frame lives on `univ \ r.sig` by construction — and the
`n → m` embedding is the register `r` itself: a fact about `U` on the `k`-cell
tuple space `TSpace D r.toFun` (the subroutine's own world) becomes a triple in
the `m`-cell world `L` at whichever cells `r` names, `QFT_sub_cast`-style
(`example.v:176`), the recast being the reindexing `Reg.encode` and nothing more.

Derived from the `DerivTot` constructors `.unitary` (Ax-Uni) and `.conseq`
(R-Conseq) alone, plus the library tensor bridge `liftF_regGate_tenv`: no new
axiom, no new rule primitive. -/
theorem DerivTot.unitary_tenv {k : ℕ} (r : Reg L k) (U : UnitaryOp (TSpace D r.toFun))
    (v : HS D r.sig) (w : HS D ((univ : Finset L) \ r.sig)) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    DerivTot (σT := σT)
      (Assn.ofState (castH D (union_sdiff_of_subset (subset_univ r.sig)) (tenv D v w))
        (norm_castH_tenv_eq_one v w hv hw))
      (.unitary k (RegExpr.const r) fun _ => U)
      (Assn.ofState
        (castH D (union_sdiff_of_subset (subset_univ r.sig))
          (tenv D (r.op D (U : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun) v) w))
        (norm_castH_tenv_eq_one _ w (norm_reg_op_eq_one r U hv) hw)) := by
  refine DerivTot.conseq ?_ (DerivTot.unitary (RegExpr.const r) (fun _ => U) _)
    (Assn.le_refl' _)
  intro σ
  refine le_of_eq (Eq.symm (Eq.trans
    (Assn.unitaryPre_op_of_dist _ _ _ (σ := σ) r.inj) ?_))
  rw [Assn.ofState_op]
  exact adjoint_conj_outerLM_tenv r U v w

/-! ## §6. The arity-general block gate on a product state

§2–§4 are the `k = 2` layer: a gate given on its own two-cell world, consumed
at a pair of cells of an arbitrary world with the complement framed. This
section is the same story at **arbitrary arity** `k`, with the gate given on the
register's own *ordered tuple space* `TSpace D r.toFun` (CoqQ's `'H[T]` before
the register mapping) rather than on a product of two cell types.

* `tupleV` — the product vector of the tuple space, CoqQ `tentv_tuple`/`tenvm`
  (`hstensor.v:950`) on a register's own ordered tuple: the arity-`k` analogue
  of `vpair`.
* `Reg.idxEquiv_apply_equivSig` — the `idxEquiv` pin at a register's own `j`-th
  cell, generic in `k`: the arity-general analogue of `Reg.idxEquiv_pair_fst`
  and `Reg.idxEquiv_pair_snd`.
* `prodV_sig_reg` — **the arity-general block collapse**, the `k`-ary analogue
  of `prodV_sig_pair` (CoqQ `t2tv_tuple`/`tenvm`): the product state over the
  cells a register names *is* the transport `Reg.encode` (CoqQ `tv2v`) of the
  tuple-space product vector of its factors, in the register's own order.
* `regOp_prodV_sig`, `regLift_regGate_prodV` — **the arity-general frame
  bridge** (CoqQ `lift_lf` on a `tenvm`-split state): the whole-world lift of a
  `k`-cell gate acts on the `k` factors the register names — as prescribed by
  the gate's own hypothesis `hG`, stated entirely inside `TSpace D r.toFun` —
  and carries every other factor through untouched. The `k = 2` case is
  `regLift_pairGate_prodV`; unlike it, the output factors are given by a second
  family `φ` pinned on the complement by `hout`, which is what an arity-general
  gate needs (there is no `Function.update` chain to write). -/

variable (D)

/-- The product vector of a register's **own ordered tuple space** — CoqQ
`tentv_tuple`/`tenvm` (`hstensor.v:950`) applied to the tuple `f`. This is the
arity-`k` analogue of `vpair` (`Qhl/Gate/Phase.lean`): the space it lives in is
the gate's own world `TSpace D f`, with no world `L`, no register support and no
complement in sight, so a gate fact stated with `tupleV` is a fact about the
gate alone. -/
noncomputable def tupleV {k : ℕ} (f : Fin k → L) (χ : ∀ j, EuclideanSpace ℂ (D (f j))) :
    TSpace D f :=
  WithLp.toLp 2 fun t => ∏ j, χ j (t j)

omit [Fintype L] [DecidableEq L] [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
  [∀ i, Inhabited (D i)] in
@[simp]
theorem tupleV_apply {k : ℕ} (f : Fin k → L) (χ : ∀ j, EuclideanSpace ℂ (D (f j)))
    (t : TIdx D f) : tupleV D f χ t = ∏ j, χ j (t j) := rfl

variable {D}

omit [Fintype L] [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)] [∀ i, Inhabited (D i)] in
/-- The `Reg.idxEquiv` pin at a register's **own** `j`-th cell, at any arity:
reading a tuple-space classical state at the cell `r j` returns its `j`-th
component. The `Equiv.cast` that `idxEquiv` carries collapses because the cell
equality `r j = ↑(r.equivSig j)` is `rfl` (`Reg.coe_equivSig`). This is the
arity-general analogue of `Reg.idxEquiv_pair_fst`/`Reg.idxEquiv_pair_snd`, and
it needs no `equivSig` computation because the index is supplied, not
searched for. -/
theorem Reg.idxEquiv_apply_equivSig {k : ℕ} (r : Reg L k) (t : TIdx D r.toFun) (j : Fin k) :
    r.idxEquiv D t (r.equivSig j) = t j :=
  Reg.idxEquiv_apply_of_symm r t (r.equivSig j) j (Equiv.symm_apply_apply _ _) rfl

omit [Fintype L] [∀ i, Inhabited (D i)] in
/-- **The arity-general block collapse** — the `k`-ary analogue of
`prodV_sig_pair` (CoqQ `t2tv_tuple`/`tenvm`, `hstensor.v:950`): the product state
over the cells a register `r` names is the transport along `Reg.encode` (CoqQ
`tv2v`, `qmem.v:157`) of the tuple-space product vector of the same factors,
read in the register's own order `j ↦ ψ (r j)`. This is what lets a fact stated
with `tupleV` — i.e. stated about the gate alone, in the subroutine's own
`k`-cell world — be read on a register's block factor. -/
theorem prodV_sig_reg {k : ℕ} (r : Reg L k) (ψ : ∀ i, EuclideanSpace ℂ (D i)) :
    prodV D (W := r.sig) ψ = r.encode D (tupleV D r.toFun fun j => ψ (r j)) := by
  refine PiLp.ext fun x => ?_
  obtain ⟨t, rfl⟩ := (r.idxEquiv D).surjective x
  rw [prodV_apply, Reg.encode_apply, Equiv.symm_apply_apply, tupleV_apply,
    ← Equiv.prod_comp r.equivSig]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Reg.idxEquiv_apply_equivSig]
  rfl

omit [Fintype L] [∀ i, DecidableEq (D i)] [∀ i, Inhabited (D i)] in
/-- A product state is carried by the reindexing `castH` to the product state of
the same factors: only the *set* of cells changes, the family does not (CoqQ
`casths` on a `tenvm`, Decision H1 — the cast is a reindexing of the classical
state, never an `Eq.rec` on the space). -/
theorem castH_prodV {S T : Finset L} (h : S = T) (ψ : ∀ i, EuclideanSpace ℂ (D i)) :
    castH D h (prodV D (W := S) ψ) = prodV D (W := T) ψ := by
  subst h
  exact PiLp.ext fun _ => rfl

omit [Fintype L] [∀ i, Inhabited (D i)] in
/-- The block identity at arbitrary arity: on the `k` cells it names, the
register transport `Reg.op` (CoqQ `tf2f`) of the gate does exactly what the gate
hypothesis says. The hypothesis `hG` is a statement about `G` **in the gate's
own tuple world** `TSpace D r.toFun` — no world `L`, no complement. The `k = 2`
case is `regOp_pairGate_prodV_sig`. -/
theorem regOp_prodV_sig {k : ℕ} (r : Reg L k) (G : UnitaryOp (TSpace D r.toFun))
    (ψ φ : ∀ i, EuclideanSpace ℂ (D i))
    (hG : (G : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun)
        (tupleV D r.toFun fun j => ψ (r j)) = tupleV D r.toFun fun j => φ (r j)) :
    r.op D (G : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun) (prodV D (W := r.sig) ψ)
      = prodV D (W := r.sig) φ := by
  rw [prodV_sig_reg, Reg.op_apply, LinearIsometryEquiv.symm_apply_apply, hG, ← prodV_sig_reg]

omit [∀ i, Inhabited (D i)] in
/-- **The arity-general frame bridge on product states** (CoqQ `lift_lf`,
`hstensor.v:3390`, on a `tenvm`-split state whose output is again of product
form): the whole-world lift of a `k`-cell gate acts on the `k` factors the
register names — as prescribed by the gate's own hypothesis `hG`, which lives
entirely inside `TSpace D r.toFun` — and leaves every other factor of the
product state untouched. The output family `φ` is arbitrary on `r.sig` and
pinned to `ψ` off it by `hout`; this is exactly the frame `R` of CoqQ's
`RV_Frame` being carried through unchanged, and CoqQ's side condition
`[disjoint (fvars c) & W]` is structural here.

The `k = 2` case is `regLift_pairGate_prodV` and the `k = 1` case is
`liftF_singleGate_prodV`; the proof is the same three steps (`liftF_regOp_prodV`
to split off the block, the block identity `regOp_prodV_sig`, `prodV_split`
backwards to reassemble). -/
theorem regLift_regGate_prodV {k : ℕ} (r : Reg L k) (G : UnitaryOp (TSpace D r.toFun))
    (ψ φ : ∀ i, EuclideanSpace ℂ (D i))
    (hout : ∀ i ∈ (univ : Finset L) \ r.sig, φ i = ψ i)
    (hG : (G : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun)
        (tupleV D r.toFun fun j => ψ (r j)) = tupleV D r.toFun fun j => φ (r j)) :
    regLift r (G : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun)
        (prodV D (W := (univ : Finset L)) ψ)
      = prodV D (W := (univ : Finset L)) φ := by
  have h : r.sig ⊆ (univ : Finset L) := subset_univ _
  change liftF D h (r.op D (G : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun))
    (prodV D (W := (univ : Finset L)) ψ) = _
  rw [liftF_regOp_prodV, regOp_prodV_sig r G ψ φ hG, prodV_split D h φ]
  refine congrArg (castH D (union_sdiff_of_subset h)) (congrArg₂ (tenv D) rfl ?_)
  exact prodV_congr D fun i hi => (hout i hi).symm

/-! ## §7. Small effect / lift algebra

Four one-screen generic facts that every *measurement*-carrying derivation
needs, in the same spirit as §1–§6: none of them names a program, a gate or a
world.

* `outerLM_zero_left`/`outerLM_zero_right` — a rank-one with a zero slot dies.
  These are what makes a measurement branch that *annihilates* one summand of a
  decomposed invariant collapse by pure `outerLM` algebra.
* `isEffect_add_outerLM_of_orthonormal` — the sum of the rank-one projectors of
  two **orthonormal** vectors is again an effect (indeed a projection). This is
  what lets an invariant be written as `∣u⟩⟨u∣ + ∣v⟩⟨v∣` — a rank-*two*
  projector presented as an orthogonal decomposition, so that each predicate
  transformer acts summand by summand.
* `conj_isometryEquiv_outerLM` — conjugating a rank-one by an isometry
  equivalence transports its two vectors. Since `Reg.op`/`singleOp` (CoqQ
  `tf2f`) *are* such conjugations, this is how a rank-one gate/measurement
  operator given on a cell's own space is read on a register's block.
* `adjoint_regLift` — the whole-world lift (CoqQ `lift_lf`) commutes with the
  adjoint, so a self-adjoint block operator lifts to a self-adjoint one. -/

section EffectAlgebra

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

@[simp]
theorem outerLM_zero_left (v : F) : outerLM (0 : E) v = 0 :=
  LinearMap.ext fun _ => by simp

@[simp]
theorem outerLM_zero_right (u : E) : outerLM u (0 : F) = 0 :=
  LinearMap.ext fun _ => by simp

/-- Rescaling both slots of a rank-one projector: `∣c·u⟩⟨c·u∣ = |c|² ∣u⟩⟨u∣`. -/
theorem outerLM_smul_self (c : ℂ) (u : E) :
    outerLM (c • u) (c • u) = (c * star c) • outerLM u u := by
  rw [outerLM_smul_left, outerLM_smul_right, smul_smul]

/-- The sum of the rank-one projectors of two orthonormal vectors is a
projection, hence an effect: an assertion may be written as an orthogonal
decomposition `∣u⟩⟨u∣ + ∣v⟩⟨v∣`. -/
theorem isEffect_add_outerLM_of_orthonormal [FiniteDimensional ℂ E] {u v : E}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫ = 0) :
    IsEffect (outerLM u u + outerLM v v) := by
  have hvu : (⟪v, u⟫ : ℂ) = 0 := by rw [← inner_conj_symm, huv, map_zero]
  have huu : (⟪u, u⟫ : ℂ) = 1 := by rw [inner_self_eq_norm_sq_to_K, hu]; norm_num
  have hvv : (⟪v, v⟫ : ℂ) = 1 := by rw [inner_self_eq_norm_sq_to_K, hv]; norm_num
  refine isEffect_of_isProjOp ⟨?_, (isProjOp_outerLM_self hu).isSymmetric.add
    (isProjOp_outerLM_self hv).isSymmetric⟩
  change (outerLM u u + outerLM v v) ∘ₗ (outerLM u u + outerLM v v) = outerLM u u + outerLM v v
  rw [LinearMap.add_comp, LinearMap.comp_add, LinearMap.comp_add, outerLM_comp, outerLM_comp,
    outerLM_comp, outerLM_comp, huu, hvv, huv, hvu, one_smul, one_smul, zero_smul, zero_smul]
  abel

/-- Conjugating a rank-one operator by an isometry equivalence transports both
of its vectors — the rank-one case of the transport `Reg.op`/`singleOp`
(CoqQ `tf2f`) performs. -/
theorem conj_isometryEquiv_outerLM (e : E ≃ₗᵢ[ℂ] F) (u v : E) :
    e.toLinearEquiv.conj (outerLM u v) = outerLM (e u) (e v) := by
  refine LinearMap.ext fun z => ?_
  rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply]
  change e (outerLM u v (e.symm z)) = _
  rw [outerLM_apply, outerLM_apply, map_smul,
    ← LinearIsometryEquiv.inner_map_map e v (e.symm z),
    LinearIsometryEquiv.apply_symm_apply]

end EffectAlgebra

/-- The whole-world lift of a register operator (CoqQ `lift_lf`) commutes with
the adjoint: `(⟦A⟧)† = ⟦A†⟧`. -/
theorem adjoint_regLift {k : ℕ} (r : Reg L k)
    (A : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun) :
    LinearMap.adjoint (regLift r A) = regLift r (LinearMap.adjoint A) := by
  rw [regLift, regLift, adjoint_liftF, Reg.adjoint_op]

end Qhl
