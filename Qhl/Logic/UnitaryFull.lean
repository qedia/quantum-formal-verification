import Qhl.Logic.Frame

/-!
# The whole-register unitary layer: CoqQ's global gate `[ut x := U]`

CoqQ applies a *whole-system* gate in one program statement: `[ut x := U]`
(`qwhile.v:533`, the notation for the `unitary_` constructor `qwhile.v:128`)
where the register `x` covers **every** cell the operator `U` acts on. The QPE
case study is the paradigm — its last stage is the single statement
`[ut x := IQFT]` (`example/coqq_paper/example.v:1005`), applying the whole
inverse Fourier transform to the whole control register at once, and its
correctness step is one application of `AxV_UT` (`qhl.v:1623`), CoqQ's form of
the (Ax-Uni) axiom. Nothing is decomposed into per-cell gates there: the gate is
given as an operator of the register's Hilbert space and consumed as such.

This file is that layer. Its content is the *collapse* of the two transports the
semantics performs on a gate — the register transport `Reg.op` (CoqQ `tf2f`) and
the cylindrical extension `liftF` to the whole world (CoqQ `lift_lf`) — in the
case where the register covers the whole world: they cancel, and the program's
global operator **is** the operator one started from.

* `Reg.ofEquiv`, `Reg.sig_ofEquiv` — the full-coverage register of a bijection
  `Fin k ≃ L`: a genuine `Reg L k` (an *ordered* enumeration of the world) whose
  support is all of `L`.
* `Reg.fullEnc` — the reindexing isometry `TSpace D r.toFun ≃ₗᵢ HS D univ` of a
  register with `r.sig = univ`: `Reg.encode` (CoqQ `tv2v`) followed by the cast
  `castH` along `r.sig = univ` (Decision H1: casts are reindexings, never
  `Eq.rec`).
* `Reg.fullGate` — a whole-world unitary `V : UnitaryOp (HS D univ)` read as a
  gate of the register's tuple space, so that it can be the gate of a
  `Prog.unitary` step (the `k = n` analogue of `singleGate`/`pairGate`).
* `regLift_fullGate` — **the collapse**: `regLift r (r.fullGate D hr V) = V`.
  The program's global operator is literally `V`; there is no residual cast, no
  frame and no reindexing left. (Proof: entrywise on `deltav`. The Kronecker
  factor of `liftF` lives on `univ \ r.sig = ∅`, hence is `1`; the `Reg.op`
  factor is `castH`-conjugation by `Reg.op_fullGate`, and both index casts
  `QIdx.cast ∘ QIdx.res` are the identity on `QIdx D univ` by structure eta.)
* `Prog.unitaryAll` — the program `[ut x := V]` for a full register: a literal
  `Prog.unitary` term, inspectable like every other statement.
* `DerivTot.unitary_state` — **(Ax-Uni) at a pure state**, at a register of any
  arity: given `regLift r U v = w` for unit vectors `v w`, the syntactic triple
  `{|v⟩⟨v|} q̄ *= U {|w⟩⟨w|}` is derivable. This is CoqQ's `AxV_UT` in its state
  form `⊨s {P} [ut x := U] {Q}`, built from the `DerivTot` constructors
  `.unitary` (Ax-Uni) and `.conseq` (R-Conseq) alone.
* `DerivTot.unitaryAll_state` — **the headline corollary**: for a full register,
  the whole gate application is discharged by *one* call whose only hypothesis is
  the mathematical fact `V v = w` about the operator itself — exactly the shape
  of CoqQ's one-line `[ut x := IQFT]` step.

Everything is generic in the world `L`, the cell-type family `D`, the classical
state space `σT`, the register and the gate; no example fixture and no particular
gate appears. Nothing is postulated: every derivation is derived from the
`DerivTot` constructors, with the library transports doing the work.
-/

namespace Qhl

open Finset
open scoped ComplexInnerProductSpace ComplexOrder

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)]
variable {σT : Type*}

namespace Reg

variable {k : ℕ}

/-! ## §1. The full-coverage register -/

/-- The register of a bijection `Fin k ≃ L`: an *ordered* enumeration of the
whole world as a genuine `Reg L k` (the cells are pairwise distinct because `e`
is injective). This is the register CoqQ's whole-system statements
`[ut x := U]` name — e.g. QPE's control register in `[ut x := IQFT]`
(`example.v:1005`) — where the gate is given on the register's own space. -/
def ofEquiv (e : Fin k ≃ L) : Reg L k := ⟨e, e.injective⟩

omit [Fintype L] [DecidableEq L] in
@[simp]
theorem ofEquiv_apply (e : Fin k ≃ L) : ⇑(ofEquiv e) = ⇑e := rfl

/-- The register of a bijection covers the whole world: its support is `univ`.
This is the hypothesis every declaration below is parameterised by — it is
stated as `r.sig = univ` rather than tied to `ofEquiv`, so that any
full-coverage register (however it was built) is accepted. -/
theorem sig_ofEquiv (e : Fin k ≃ L) : (ofEquiv e).sig = (univ : Finset L) :=
  eq_univ_of_forall fun a => mem_sig.mpr ⟨e.symm a, e.apply_symm_apply a⟩

/-! ## §2. The whole-world encoding of a full register -/

variable (D)

/-- The reindexing isometry between the tuple space of a full register and the
whole-world space: `Reg.encode` (CoqQ `tv2v`, `qmem.v:157`) followed by the cast
along `r.sig = univ`. Decision H1 is respected — both factors are reindexings of
the classical-state index, never an `Eq.rec` on the space. -/
noncomputable def fullEnc (r : Reg L k) (hr : r.sig = (univ : Finset L)) :
    TSpace D r.toFun ≃ₗᵢ[ℂ] HS D (univ : Finset L) :=
  (r.encode D).trans (castH D hr)

omit [∀ i, Inhabited (D i)] in
@[simp]
theorem fullEnc_apply (r : Reg L k) (hr : r.sig = (univ : Finset L))
    (v : TSpace D r.toFun) : r.fullEnc D hr v = castH D hr (r.encode D v) := rfl

omit [∀ i, Inhabited (D i)] in
@[simp]
theorem fullEnc_symm_apply (r : Reg L k) (hr : r.sig = (univ : Finset L))
    (w : HS D (univ : Finset L)) :
    (r.fullEnc D hr).symm w = (r.encode D).symm (castH D hr.symm w) := rfl

/-- A whole-world unitary read as a gate of the register's tuple space — the
shape a `Prog.unitary` step requires (`Prog.unitary k r U` wants
`U σ : UnitaryOp (TSpace D (r σ))`). The `k = #L` analogue of `singleGate`
(`Qhl/HSpace/LocalGate.lean`) and `pairGate` (`Qhl/Logic/Frame.lean`): the gate
is transported, not re-derived. -/
noncomputable def fullGate (r : Reg L k) (hr : r.sig = (univ : Finset L))
    (V : UnitaryOp (HS D (univ : Finset L))) : UnitaryOp (TSpace D r.toFun) :=
  UnitaryOp.congr (r.fullEnc D hr).symm V

omit [∀ i, Inhabited (D i)] in
/-- The register transport `Reg.op` (CoqQ `tf2f`) of a `fullGate` is `V` read
through the cast alone: the `Reg.encode` half of `fullEnc` cancels against the
`Reg.encode` of `Reg.op`. -/
theorem op_fullGate (r : Reg L k) (hr : r.sig = (univ : Finset L))
    (V : UnitaryOp (HS D (univ : Finset L))) (v : HS D r.sig) :
    r.op D (r.fullGate D hr V : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun) v
      = castH D hr.symm
          ((V : HS D (univ : Finset L) →ₗ[ℂ] HS D (univ : Finset L)) (castH D hr v)) := by
  change r.encode D ((r.fullEnc D hr).symm
    ((V : HS D (univ : Finset L) →ₗ[ℂ] HS D (univ : Finset L))
      (r.fullEnc D hr ((r.encode D).symm v)))) = _
  rw [fullEnc_symm_apply, LinearIsometryEquiv.apply_symm_apply, fullEnc_apply,
    LinearIsometryEquiv.apply_symm_apply]

end Reg

/-! ## §3. The collapse: the lift of a full gate is the gate -/

omit [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)] [∀ i, Inhabited (D i)] in
/-- On a full register the two restrictions of a whole-world classical state to
the complement `univ \ r.sig` agree — the complement is empty, so its
classical-state type is a subsingleton. This is the Kronecker factor of
`liftF_deltav_apply` (CoqQ `lift_lf`) becoming `1`. The subset proof is
arbitrary, so the lemma matches whatever `simp` normal form the entry formula
carries. -/
theorem QIdx.res_sdiff_of_sig_eq_univ {k : ℕ} (r : Reg L k)
    (hr : r.sig = (univ : Finset L)) (h : (univ : Finset L) \ r.sig ⊆ (univ : Finset L))
    (x y : QIdx D (univ : Finset L)) : QIdx.res D h x = QIdx.res D h y :=
  funext fun i =>
    absurd (Finset.eq_univ_iff_forall.mp hr (i : L)) (mem_sdiff.mp i.2).2

omit [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)] [∀ i, Inhabited (D i)] in
/-- Restricting a whole-world classical state to a full register's support and
casting back along `r.sig = univ` is the identity: both maps only transport
membership proofs, so this is structure eta plus proof irrelevance. CoqQ's
`castidx`/`idxR` round trip (`hstensor.v:292`, `:466`). Both proofs are
arbitrary arguments, so the lemma matches any normal form. -/
theorem QIdx.cast_res_of_sig_eq_univ {k : ℕ} (r : Reg L k)
    (h : r.sig = (univ : Finset L)) (h' : r.sig ⊆ (univ : Finset L))
    (m : QIdx D (univ : Finset L)) : QIdx.cast D h (QIdx.res D h' m) = m := rfl

/-- **The whole-register collapse.** For a register `r` covering the whole world,
the operator the semantics builds from the transported gate — `Reg.op` (CoqQ
`tf2f`) followed by the cylindrical extension `liftF` to `univ` (CoqQ `lift_lf`),
i.e. `regLift` — is the operator `V` itself: nothing is left of either
transport.

This is what makes CoqQ's one-statement whole-system gate `[ut x := IQFT]`
(`example.v:1005`) usable in a Hoare triple with no bookkeeping: the semantic
effect of the statement is literally the mathematical operator, so a fact about
`V` is a fact about the program.

Proof: entrywise on the canonical basis (`linM_ext`). The Kronecker factor of
`liftF_deltav_apply` lives on `univ \ r.sig = ∅` and is therefore `1`
(`QIdx.res_sdiff_of_sig_eq_univ`); the `Reg.op` factor is `castH`-conjugation
(`Reg.op_fullGate`), and the two index reindexings that remain are identities
(`QIdx.cast_res_of_sig_eq_univ`). -/
theorem regLift_fullGate {k : ℕ} (r : Reg L k) (hr : r.sig = (univ : Finset L))
    (V : UnitaryOp (HS D (univ : Finset L))) :
    regLift r (r.fullGate D hr V : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun)
      = (V : HS D (univ : Finset L) →ₗ[ℂ] HS D (univ : Finset L)) := by
  refine linM_ext D fun m => PiLp.ext fun l => ?_
  rw [regLift_deltav_apply, if_pos (QIdx.res_sdiff_of_sig_eq_univ r hr _ l m), mul_one,
    Reg.op_fullGate, castH_apply, castH_deltav, QIdx.cast_res_of_sig_eq_univ,
    QIdx.cast_res_of_sig_eq_univ]

/-- Pointwise form of the collapse: the program's global operator sends `v` to
`V v`. -/
theorem regLift_fullGate_apply {k : ℕ} (r : Reg L k) (hr : r.sig = (univ : Finset L))
    (V : UnitaryOp (HS D (univ : Finset L))) (v : HS D (univ : Finset L)) :
    regLift r (r.fullGate D hr V : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun) v
      = (V : HS D (univ : Finset L) →ₗ[ℂ] HS D (univ : Finset L)) v := by
  rw [regLift_fullGate]

/-! ## §4. The whole-register program and its (Ax-Uni) rule -/

/-- CoqQ's whole-system gate statement `[ut x := U]` (`qwhile.v:533`) at a full
register — the exact shape of QPE's last stage `[ut x := IQFT]`
(`example.v:1005`). A literal `Prog.unitary` term: the register expression is the
constant full register, the gate is the whole-world unitary read on the
register's tuple space. -/
noncomputable def Prog.unitaryAll {k : ℕ} (r : Reg L k) (hr : r.sig = (univ : Finset L))
    (V : UnitaryOp (HS D (univ : Finset L))) : Prog σT D :=
  .unitary k (RegExpr.const r) fun _ => r.fullGate D hr V

omit [∀ i, Inhabited (D i)] in
/-- The (Ax-Uni) precondition of a pure-state postcondition at an arbitrary
register: `U†|w⟩⟨w|U = |v⟩⟨v|` when the step sends `v` to `w`.
`adjoint_comp_outerLM_comp` moves the conjugation onto the vectors, the
hypothesis runs backwards and `adjoint_apply_apply` supplies `U†U = 1`
pointwise — the state-level analogue of `adjoint_conj_outerLM_prodV`
(`Qhl/Logic/ForRule.lean`) and `adjoint_conj_outerLM_tenv`
(`Qhl/Logic/Frame.lean`). -/
theorem adjoint_conj_outerLM_state {k : ℕ} (r : Reg L k)
    (U : UnitaryOp (TSpace D r.toFun)) {v w : HS D (univ : Finset L)}
    (hU : regLift r (U : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun) v = w) :
    LinearMap.adjoint (regLift r (U : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun))
        ∘ₗ outerLM w w ∘ₗ regLift r (U : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun)
      = outerLM v v := by
  rw [adjoint_comp_outerLM_comp, ← hU, adjoint_apply_apply (isUnitary_regLift r U)]

/-- **(Ax-Uni) at a pure state, at a register of any arity** — CoqQ's `AxV_UT`
(`qhl.v:1623`) in its state form `⊨s {'|v⟩} [ut x := U] {'|w⟩}`:

```
⊢ₜ {|v⟩⟨v|}  q̄ *= U  {|w⟩⟨w|}      given   regLift r U v = w
```

The hypothesis is the *single* semantic fact that the step moves `v` to `w`;
everything else — the `Dist(q̄)` side condition (free: `r` is a register, so its
cells are distinct by construction, and the `unitaryPre` transformer never falls
into the `0` branch, V7), the conjugation `U†|w⟩⟨w|U = |v⟩⟨v|`, the norm
witnesses — is discharged here. Built from the `DerivTot` constructors `.unitary`
(Ax-Uni) and `.conseq` (R-Conseq) alone: no new axiom, no new rule primitive. -/
theorem DerivTot.unitary_state {k : ℕ} (r : Reg L k) (U : UnitaryOp (TSpace D r.toFun))
    {v w : HS D (univ : Finset L)} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hU : regLift r (U : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun) v = w) :
    DerivTot (σT := σT) (Assn.ofState v hv)
      (.unitary k (RegExpr.const r) fun _ => U)
      (Assn.ofState w hw) := by
  refine DerivTot.conseq ?_ (DerivTot.unitary (RegExpr.const r) (fun _ => U) _)
    (Assn.le_refl' _)
  intro σ
  refine le_of_eq (Eq.symm (Eq.trans
    (Assn.unitaryPre_op_of_dist _ _ _ (σ := σ) r.inj) ?_))
  rw [Assn.ofState_op]
  exact adjoint_conj_outerLM_state r U hU

/-- **The headline rule: one whole-register gate, one call.**

```
⊢ₜ {|v⟩⟨v|}  [ut x := V]  {|w⟩⟨w|}      given   V v = w
```

The hypothesis `hV` is a statement about the operator `V` **alone**, in the
whole-world space `HS D univ` — no register, no lift, no cast: exactly the
mathematical fact one proves about e.g. an inverse Fourier transform. The
theorem consumes it at any full-coverage register of the world, which is what
makes CoqQ's `[ut x := IQFT]` step (`example.v:1005`) one line there and one line
here. The bridge is `regLift_fullGate`. -/
theorem DerivTot.unitaryAll_state {k : ℕ} (r : Reg L k) (hr : r.sig = (univ : Finset L))
    (V : UnitaryOp (HS D (univ : Finset L))) {v w : HS D (univ : Finset L)}
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hV : (V : HS D (univ : Finset L) →ₗ[ℂ] HS D (univ : Finset L)) v = w) :
    DerivTot (σT := σT) (Assn.ofState v hv)
      (Prog.unitaryAll (σT := σT) r hr V) (Assn.ofState w hw) :=
  DerivTot.unitary_state r _ hv hw (by rw [regLift_fullGate_apply]; exact hV)

/-! ## §5. Whole-block gates on tuple product states, and (Ax-Uni)+frame at any
register

§1–§4 apply a whole-world unitary at a register that covers the **whole** world.
The remaining — and, for subroutine reuse, the decisive — step is to consume the
very same operator fact at a register that covers only *part* of a larger world:
CoqQ's `QFT_sub_cast` reuse (`example.v:176`) composed with the frame `RV_Frame`
(`qhl.v:1815`). The bridge is the tuple-space product vector `tupleV`
(`Qhl/Logic/Frame.lean` §6, CoqQ `tentv_tuple`/`tenvm`):

* `Reg.fullEnc_tupleV` — the reindexing `fullEnc` of a `k`-cell register's own
  tuple product vector is the whole-world product state of the same factors.
* `Reg.fullGate_tupleV` — **the transport of an operator fact**: an equation
  `V (⊗ᵢ ψᵢ) = ⊗ᵢ φᵢ` about a `k`-cell operator `V` on `HS D univ` — the
  subroutine's own world, e.g. an inverse Fourier transform sending a Fourier
  state to a basis ket — becomes the corresponding equation for the transported
  gate `r.fullGate D hr V` on the *tuple* space of any `k`-cell register `r`,
  i.e. exactly the hypothesis `hG` that the arity-general frame bridge
  `regLift_regGate_prodV` consumes.
* `DerivTot.unitary_reg_prodV` — **the arity-general reuse workhorse**: the
  sibling of `DerivTot.unitary_pair_prodV` (`Qhl/Logic/Frame.lean` §4) at any
  arity. A gate proved on its own `k`-cell world is applied at *any* `k` cells
  of *any* world, the whole complement being framed. Derived from
  `DerivTot.unitary_state` (§4) and the library tensor bridge alone: (Ax-Uni) +
  (R-Conseq), no new axiom and no new rule primitive.

Composing the two, a proved `n`-qubit subroutine triple is reusable inside an
`m`-qubit circuit in one call, with the `n → m` embedding being the register `r`
and nothing more. -/

omit [∀ i, Inhabited (D i)] in
/-- The whole-world reindexing of a register's own tuple product vector is the
product state over the world (CoqQ `tv2v` of a `tentv_tuple`). Both halves of
`fullEnc` are accounted for: `Reg.encode` by the block collapse `prodV_sig_reg`,
the cast by `castH_prodV`. -/
theorem Reg.fullEnc_tupleV {k : ℕ} (r : Reg L k) (hr : r.sig = (univ : Finset L))
    (ψ : ∀ i, EuclideanSpace ℂ (D i)) :
    r.fullEnc D hr (tupleV D r.toFun fun j => ψ (r j))
      = prodV D (W := (univ : Finset L)) ψ := by
  rw [Reg.fullEnc_apply, ← prodV_sig_reg, castH_prodV]

omit [∀ i, Inhabited (D i)] in
/-- **The transport of an operator fact to the register's tuple space.** A
statement about the operator `V` **alone**, in the `k`-cell world
`HS D univ` — `V (⊗ᵢ ψᵢ) = ⊗ᵢ φᵢ`, the mathematical content of a subroutine —
becomes the corresponding statement about the transported gate
`r.fullGate D hr V` on the ordered tuple space of a `k`-cell register.

This is the half of CoqQ's `QFT_sub_cast` (`example.v:176`) that changes the
*presentation* of the gate; combined with `regLift_regGate_prodV`
(`Qhl/Logic/Frame.lean` §6) — the half that frames the complement — it lets an
`n`-qubit operator fact be consumed at any placement of `n` cells inside an
`m`-cell world. -/
theorem Reg.fullGate_tupleV {k : ℕ} (r : Reg L k) (hr : r.sig = (univ : Finset L))
    (V : UnitaryOp (HS D (univ : Finset L))) (ψ φ : ∀ i, EuclideanSpace ℂ (D i))
    (hV : (V : HS D (univ : Finset L) →ₗ[ℂ] HS D (univ : Finset L))
        (prodV D (W := (univ : Finset L)) ψ) = prodV D (W := (univ : Finset L)) φ) :
    (r.fullGate D hr V : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun)
        (tupleV D r.toFun fun j => ψ (r j))
      = tupleV D r.toFun fun j => φ (r j) := by
  change (r.fullEnc D hr).symm ((V : HS D (univ : Finset L) →ₗ[ℂ] HS D (univ : Finset L))
    (r.fullEnc D hr (tupleV D r.toFun fun j => ψ (r j)))) = _
  rw [Reg.fullEnc_tupleV, hV, ← Reg.fullEnc_tupleV r hr φ,
    LinearIsometryEquiv.symm_apply_apply]

/-- **(Ax-Uni) + frame at a register of any arity, on bare product states** —
CoqQ's `AxV_UT` (`qhl.v:1623`) composed with `RV_Frame` (`qhl.v:1815`):

```
⊢ₜ {⊗ᵢ ψᵢ}  q̄ *= G  {⊗ᵢ φᵢ}     given  G (⊗ⱼ ψ_{q̄ⱼ}) = ⊗ⱼ φ_{q̄ⱼ}  and  φ = ψ off q̄
```

The arity-general sibling of `DerivTot.unitary_pair_prodV`
(`Qhl/Logic/Frame.lean` §4). The gate hypothesis `hG` lives **entirely inside
the gate's own `k`-cell tuple world** `TSpace D r.toFun` — the subroutine's `n`
qubits — and the theorem consumes it at whichever `k` cells of whichever world
`L` the register `r` names — the `m`-qubit circuit — with the entire complement
framed (`hout` says the output family only differs on the cells `r` names).
A `k`-qubit subroutine proved once is therefore reusable at every placement,
with no re-derivation and no `m`-dependent bookkeeping; `Reg.fullGate_tupleV`
supplies `hG` from a fact stated about the operator alone.

Derived from `DerivTot.unitary_state` (§4) — itself the `DerivTot` constructors
`.unitary` (Ax-Uni) and `.conseq` (R-Conseq) alone — plus the library tensor
bridge `regLift_regGate_prodV`: no new axiom, no new rule primitive, no appeal
to soundness. -/
theorem DerivTot.unitary_reg_prodV {k : ℕ} (r : Reg L k) (G : UnitaryOp (TSpace D r.toFun))
    (ψ φ : ∀ i, EuclideanSpace ℂ (D i)) (hψ : ∀ i, ‖ψ i‖ = 1) (hφ : ∀ i, ‖φ i‖ = 1)
    (hout : ∀ i ∈ (univ : Finset L) \ r.sig, φ i = ψ i)
    (hG : (G : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun)
        (tupleV D r.toFun fun j => ψ (r j)) = tupleV D r.toFun fun j => φ (r j)) :
    DerivTot (σT := σT)
      (Assn.ofState (prodV D (W := (univ : Finset L)) ψ) (norm_prodV_eq_one ψ hψ))
      (.unitary k (RegExpr.const r) fun _ => G)
      (Assn.ofState (prodV D (W := (univ : Finset L)) φ) (norm_prodV_eq_one φ hφ)) :=
  DerivTot.unitary_state r G (norm_prodV_eq_one ψ hψ) (norm_prodV_eq_one φ hφ)
    (regLift_regGate_prodV r G ψ φ hout hG)

end Qhl
