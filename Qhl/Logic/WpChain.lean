import Qhl.Logic.ProdChain
import Qhl.Logic.UnitaryFull

/-!
# The backward `wp`-chain of a straight-line unitary program, and the Born step

`Qhl/Logic/ForRule.lean`, `Qhl/Logic/ForSeqRule.lean` and
`Qhl/Logic/ProdChain.lean` discharge a straight-line unitary program *at a
product-state endpoint*: each gate is matched to (Ax-Uni), the endpoints are
bare kets, and the loop is one `forProg_prodChain` call. That machinery is
exact only as long as every intermediate state is again a **bare product
state**.

It is not, as soon as the input is a genuine **superposition** and the
postcondition is a *sum of basis projectors* — the readout of a circuit,
whose success probability is a Born sum
`∑_{good outcomes} |⟨m | K_ℓ ⋯ K_1 | v⟩|²`. This file is the generic layer for
that computation: it lets one *evaluate* the folded (Ax-Uni) + (R-Seq)
precondition, rather than only match it structurally.

Contents (everything is generic in the world `L`, the cell-type family `D`
and the classical state space `σT` — the **ownership test** is passed: no
program, no gate, no example fixture is named anywhere below).

* §1 **Pure states as density operators.** `PDensity.pure v` is the rank-one
  density operator `|v⟩⟨v|`, `PDensity.mass_pure` its unit mass, and
  `expect_pure` / `expectE_pure` the two expectation displays
  `expect A ⟨σ, |v⟩⟨v|⟩ = re ⟪v, A σ v⟫`. This is what turns the
  density-matrix semantics of `validTot` into a *number* at a chosen pure
  input, without weakening the semantics: `PDensity.pure v` is one particular
  `ρ` among the `∀ ρ` that `validTot` quantifies over.

* §2 **The semantic operator of a gate list.** `chainOp l K` is the ordered
  composite `K_{l.head} … ` applied *in program order*: it is the `foldr` that
  matches the `foldr` shape of a `forProg`/`.seq` chain, so that
  `chainOp (i :: l) K v = chainOp l K (K i v)` — the head gate acts first.

* §3 **The folded (Ax-Uni) transformer is one conjugation.**
  `foldr_unitaryPre_op` : the backward `wp`-fold of a list of unitary steps
  over an assertion `B` is `W† ∘ B ∘ W` with `W = chainOp l …` the semantic
  operator of the whole gate list. This is the display that makes the
  precondition of a straight-line circuit *computable*: it collapses `|l|`
  nested conjugations into a single one.

* §4 **The Born step.** `expect_foldr_unitaryPre_pure` : the expectation of
  that folded precondition in the pure state `|v⟩⟨v|` is
  `re ⟪W v, B σ (W v)⟫` — the postcondition evaluated at the *evolved* state.
  Together with §6 (`re_inner_sum_outerLM_self`) this is exactly the Born rule
  for the readout of a unitary circuit: for `B σ = ∑_{m ∈ good} |m⟩⟨m|` the
  number is `∑_{m ∈ good} ‖⟪m, W v⟫‖²`.

* §5 **Two collapses of `chainOp`.** `chainOp_single_prodV` evaluates a chain
  of *one-cell disjoint* gates on a product state (the `applyOn` normal form
  of `Qhl/Logic/ForRule.lean`); `chainOp_chain` / `chainOp_finRange_family`
  evaluate a chain along a *stage-indexed family* of states — the `chainOp`
  counterpart of `DerivTot.forProg_chain` / `forProg_finRange_chain`, so that
  a consumer never inducts over its own gate list.

* §6 **The effect algebra of an orthonormal outcome set.**
  `inner_sum_outerLM_self` / `re_inner_sum_outerLM_self` give the Born sum,
  and `isEffect_sum_outerLM_of_orthonormal` says that a sum of rank-one
  projectors along an orthonormal family really is a **quantum predicate**
  (`IsEffect`, i.e. `0 ≤ A ≤ 1`) — it is a symmetric projection, so no
  Bessel estimate is needed. This is what lets an example *name* its set of
  good outcomes as a genuine `Assn`.

* §7 **Transport laws.** `norm_apply_of_isUnitary` (a unitary is norm
  preserving) and `inner_deltav_regLift_prodV` — the generic Born
  factorisation of a block gate on a product frame: the amplitude of a basis
  outcome after a gate on a sub-register factors as the amplitude inside the
  register's own block times the amplitude of the untouched complement
  (CoqQ `lift_lf`/`tenvm` read through `dv_split`/`tenv_dot`).

Nothing here is postulated and nothing here is a new rule: §3 is a *display*
of `Assn.unitaryPre`, §4 a computation of `expect`, and the rest is state
algebra. `DerivTot`, `validTot` and `DerivTot.sound` are untouched.
-/

namespace Qhl

open Finset
open scoped ComplexInnerProductSpace

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)]
variable {σT : Type*}

/-! ## §1. Pure states as density operators, and their expectations -/

/-- The rank-one density operator `|v⟩⟨v|` of a vector — one particular `ρ`
among the states `validTot` quantifies over, not a weakening of the
semantics. -/
noncomputable def PDensity.pure (v : HS D (univ : Finset L)) : PDensity D :=
  ⟨outerLM v v, isPositive_outerLM_self v⟩

@[simp]
theorem PDensity.pure_op (v : HS D (univ : Finset L)) :
    (PDensity.pure v).op = outerLM v v := rfl

/-- A unit vector gives a *normalised* state: `Tr |v⟩⟨v| = ⟪v,v⟫ = ‖v‖² = 1`. -/
theorem PDensity.mass_pure {v : HS D (univ : Finset L)} (hv : ‖v‖ = 1) :
    (PDensity.pure v).mass = 1 := by
  refine NNReal.coe_injective ?_
  rw [PDensity.coe_mass, PDensity.pure_op, trace_outerLM,
    inner_self_eq_norm_sq_to_K (𝕜 := ℂ), hv]
  norm_num

/-- **The expectation of an effect in a pure state** is the quadratic form of
the effect at the state vector, `Tr (|v⟩⟨v| A) = ⟪v, A v⟫`. -/
theorem expect_pure (A : σT → EndM D (univ : Finset L)) (σ : σT)
    (v : HS D (univ : Finset L)) :
    expect A ⟨σ, PDensity.pure v⟩ = (⟪v, A σ v⟫ : ℂ).re := by
  rw [expect]
  change (LinearMap.trace ℂ (HS D (univ : Finset L)) (outerLM v v ∘ₗ A σ)).re = _
  rw [trace_outerLM_comp]

/-- `expectE` form of `expect_pure` — the shape `validTot` consumes. -/
theorem expectE_pure (A : σT → EndM D (univ : Finset L)) (σ : σT)
    (v : HS D (univ : Finset L)) :
    expectE A ⟨σ, PDensity.pure v⟩ = ENNReal.ofReal (⟪v, A σ v⟫ : ℂ).re := by
  rw [expectE, expect_pure]

/-! ## §2. The semantic operator of a straight-line gate list -/

/-- **The semantic operator of a gate list**, in *program order*: the head of
the list acts **first**. The `foldr` shape is the one a `.seq`-chain / a
`forProg` fold produces, so `chainOp` is definitionally aligned with the
program it evaluates (`chainOp_apply_cons` below is `rfl`). -/
noncomputable def chainOp {ι : Type*} (l : List ι) (K : ι → EndM D (univ : Finset L)) :
    EndM D (univ : Finset L) :=
  l.foldr (fun i M => M ∘ₗ K i) 1

@[simp]
theorem chainOp_nil {ι : Type*} (K : ι → EndM D (univ : Finset L)) :
    chainOp ([] : List ι) K = 1 := rfl

theorem chainOp_cons {ι : Type*} (i : ι) (l : List ι) (K : ι → EndM D (univ : Finset L)) :
    chainOp (i :: l) K = chainOp l K ∘ₗ K i := rfl

/-- One unrolling on a vector: the head gate acts first. -/
theorem chainOp_apply_cons {ι : Type*} (i : ι) (l : List ι)
    (K : ι → EndM D (univ : Finset L)) (v : HS D (univ : Finset L)) :
    chainOp (i :: l) K v = chainOp l K (K i v) := rfl

@[simp]
theorem chainOp_nil_apply {ι : Type*} (K : ι → EndM D (univ : Finset L))
    (v : HS D (univ : Finset L)) : chainOp ([] : List ι) K v = v := rfl

/-- The semantic operator of a gate list is unitary. -/
theorem isUnitary_chainOp {ι : Type*} :
    ∀ (l : List ι) (K : ι → EndM D (univ : Finset L)), (∀ i, IsUnitary (K i)) →
      IsUnitary (chainOp l K)
  | [], _, _ => isUnitary_one
  | i :: l, K, hK => (isUnitary_chainOp l K hK).comp (hK i)

/-! ## §3. The folded (Ax-Uni) transformer is a single conjugation -/

/-- **The `wp`-chain display.** The backward (Ax-Uni) fold of a list of
unitary steps over a postcondition `B` — i.e. the precondition that
(Ax-Uni) + (R-Seq) computes for the straight-line program
`q̄₁ *= U₁; …; q̄ₙ *= Uₙ` — is the single conjugation `W† B W` by the semantic
operator `W = chainOp l …` of the whole gate list.

The register arities may differ from step to step, hence the dependent
`k : ι → ℕ`; the distinctness side condition `Dist(q̄)` is assumed at each
step (`h`), which is exactly the branch on which `Assn.unitaryPre` is not
`0` (Decision V7). -/
theorem foldr_unitaryPre_op {ι : Type*} (l : List ι) (k : ι → ℕ)
    (R : ∀ i, RegExpr σT L (k i)) (U : ∀ i σ, UnitaryOp (TSpace D (R i σ)))
    (B : Assn σT D) (σ : σT) (h : ∀ i, Function.Injective (R i σ)) :
    (l.foldr (fun i A => A.unitaryPre (R i) (U i)) B).op σ
      = LinearMap.adjoint (chainOp l fun i => regLift ⟨R i σ, h i⟩ (U i σ)) ∘ₗ
          B.op σ ∘ₗ chainOp l fun i => regLift ⟨R i σ, h i⟩ (U i σ) := by
  induction l with
  | nil =>
      rw [List.foldr_nil, chainOp_nil, LinearMap.adjoint_one, Module.End.one_eq_id,
        LinearMap.id_comp, LinearMap.comp_id]
  | cons i l ih =>
      rw [List.foldr_cons, Assn.unitaryPre_op_of_dist _ (R i) (U i) (h i), ih,
        chainOp_cons, LinearMap.adjoint_comp]
      simp only [LinearMap.comp_assoc]

/-! ## §4. The Born step: the folded precondition at a pure input -/

/-- **The Born step on a superposed input.** The expectation of the folded
(Ax-Uni) precondition in the pure state `|v⟩⟨v|` is the postcondition
evaluated at the **evolved** state `W v`, `W` the semantic operator of the
gate list.

With `B.op σ = ∑_{m ∈ good} |m⟩⟨m|` (an effect by
`isEffect_sum_outerLM_of_orthonormal`) and `re_inner_sum_outerLM_self`, the
right-hand side is literally the success probability
`∑_{m ∈ good} ‖⟪m, W v⟫‖²`. -/
theorem expect_foldr_unitaryPre_pure {ι : Type*} (l : List ι) (k : ι → ℕ)
    (R : ∀ i, RegExpr σT L (k i)) (U : ∀ i σ, UnitaryOp (TSpace D (R i σ)))
    (B : Assn σT D) (σ : σT) (h : ∀ i, Function.Injective (R i σ))
    (v : HS D (univ : Finset L)) :
    expect (l.foldr (fun i A => A.unitaryPre (R i) (U i)) B).op ⟨σ, PDensity.pure v⟩
      = (⟪chainOp l (fun i => regLift ⟨R i σ, h i⟩ (U i σ)) v,
          B.op σ (chainOp l (fun i => regLift ⟨R i σ, h i⟩ (U i σ)) v)⟫ : ℂ).re := by
  rw [expect_pure, foldr_unitaryPre_op l k R U B σ h]
  simp only [LinearMap.comp_apply]
  rw [LinearMap.adjoint_inner_right]

/-! ## §5. Two collapses of `chainOp` -/

private theorem chainOp_single_prodV_aux :
    ∀ (l : List L), l.Nodup → ∀ (U : ∀ a : L, UnitaryOp (EuclideanSpace ℂ (D a)))
      (ψ : ∀ i, EuclideanSpace ℂ (D i)),
      chainOp l (fun a => regLift (Reg.single a)
          (singleGate D a (U a) :
            TSpace D (Reg.single a).toFun →ₗ[ℂ] TSpace D (Reg.single a).toFun))
          (prodV D (W := (univ : Finset L)) ψ)
        = prodV D (W := (univ : Finset L)) (applyOn l U ψ)
  | [], _, U, ψ => by rw [chainOp_nil_apply, applyOn_nil]
  | a :: l, hl, U, ψ => by
      rw [chainOp_apply_cons, regLift_singleGate_prodV,
        chainOp_single_prodV_aux l (List.nodup_cons.mp hl).2 U _,
        applyOn_cons (List.nodup_cons.mp hl).1]

/-- **A chain of disjoint one-cell gates on a product state.** The semantic
operator of a list of *distinct* cells (`l.Nodup`) sends a product state to
the product state with `U a` applied at every listed cell — the `applyOn`
normal form of `Qhl/Logic/ForRule.lean` (CoqQ `tentf_tuple_apply`). The
`Nodup` hypothesis is used exactly where `applyOn_cons` needs it. -/
theorem chainOp_single_prodV (l : List L) (hl : l.Nodup)
    (U : ∀ a : L, UnitaryOp (EuclideanSpace ℂ (D a)))
    (ψ : ∀ i, EuclideanSpace ℂ (D i)) :
    chainOp l (fun a => regLift (Reg.single a)
        (singleGate D a (U a) :
          TSpace D (Reg.single a).toFun →ₗ[ℂ] TSpace D (Reg.single a).toFun))
        (prodV D (W := (univ : Finset L)) ψ)
      = prodV D (W := (univ : Finset L)) (applyOn l U ψ) :=
  chainOp_single_prodV_aux l hl U ψ

/-- **The stage-chain collapse of `chainOp` over an arbitrary index list** —
the `chainOp` counterpart of `DerivTot.forProg_chain`: give a family
`v : ℕ → HS D univ` of intermediate states and one step law per position of
the list, and the whole composite is evaluated. The induction lives here, so
a consumer never inducts over its own gate list. -/
theorem chainOp_chain {ι : Type*} :
    ∀ (l : List ι) (K : ι → EndM D (univ : Finset L)) (v : ℕ → HS D (univ : Finset L)),
      (∀ (j : ℕ) (hj : j < l.length), K (l.get ⟨j, hj⟩) (v j) = v (j + 1)) →
      chainOp l K (v 0) = v l.length
  | [], _, _, _ => rfl
  | i :: l, K, v, h => by
      have h0 : K i (v 0) = v 1 := h 0 (Nat.succ_pos _)
      rw [chainOp_apply_cons, h0]
      exact chainOp_chain l K (fun m => v (m + 1))
        fun j hj => h (j + 1) (Nat.succ_lt_succ hj)

/-- **The stage-chain collapse at `List.finRange n`** — the shape a
`[for i < n do …]` loop takes: `n` step laws `K i (v i) = v (i+1)` evaluate
the whole composite as `v 0 ↦ v n`. Transport of `chainOp_chain` along
`List.length_finRange` / `List.getElem_finRange`. -/
theorem chainOp_finRange_family {n : ℕ} (K : Fin n → EndM D (univ : Finset L))
    (v : ℕ → HS D (univ : Finset L))
    (hstep : ∀ j : Fin n, K j (v (j : ℕ)) = v ((j : ℕ) + 1)) :
    chainOp (List.finRange n) K (v 0) = v n := by
  have key : chainOp (List.finRange n) K (v 0) = v (List.finRange n).length := by
    refine chainOp_chain (List.finRange n) K v fun j hj => ?_
    have hjn : j < n := by rwa [List.length_finRange] at hj
    have hget : (List.finRange n).get ⟨j, hj⟩ = (⟨j, hjn⟩ : Fin n) := by
      simp [List.get_eq_getElem, List.getElem_finRange]
    rw [hget]
    exact hstep ⟨j, hjn⟩
  rwa [List.length_finRange] at key

/-! ## §5b. Prefix chains: the semantic operator of the first `k` gates

`chainPre xs f k` is the semantic operator of the first `k` gates of the
list — the loop-invariant shape of a counted `while` over a gate list: after
`k` passes the state is `chainPre xs f k` applied to the input.  `chainOp`
composes the head first (`chainOp (i :: l) K = chainOp l K ∘ₗ K i`), so one
more pass composes the `k`-th gate on the **left** of the prefix
(`chainPre_succ`), and the full prefix is `chainOp` (`chainPre_length`). -/

/-- `chainOp` splits over a trailing element: the last gate of the list acts
last, i.e. composes on the left (the concat companion of `chainOp_cons`). -/
theorem chainOp_concat {ι : Type*} (l : List ι) (j : ι)
    (K : ι → EndM D (univ : Finset L)) :
    chainOp (l ++ [j]) K = K j ∘ₗ chainOp l K := by
  induction l with
  | nil =>
      rw [List.nil_append, chainOp_cons, chainOp_nil, Module.End.one_eq_id,
        LinearMap.id_comp, LinearMap.comp_id]
  | cons i t ih =>
      rw [List.cons_append, chainOp_cons, chainOp_cons, ih, LinearMap.comp_assoc]

/-- **The prefix-chain operator**: the semantic operator of the first `k`
gates of the list (in program order — the head acts first). -/
noncomputable def chainPre {ι : Type*} (xs : List ι)
    (f : ι → EndM D (univ : Finset L)) (k : ℕ) : EndM D (univ : Finset L) :=
  chainOp (xs.take k) f

@[simp]
theorem chainPre_zero {ι : Type*} (xs : List ι) (f : ι → EndM D (univ : Finset L)) :
    chainPre xs f 0 = 1 := rfl

/-- One more pass composes the `k`-th gate on the left of the prefix — the
order `chainOp` composes (head first, so the later gate is outer). -/
theorem chainPre_succ {ι : Type*} (xs : List ι) (f : ι → EndM D (univ : Finset L))
    {k : ℕ} (h : k < xs.length) :
    chainPre xs f (k + 1) = f (xs.get ⟨k, h⟩) ∘ₗ chainPre xs f k := by
  have htake : xs.take (k + 1) = xs.take k ++ [xs.get ⟨k, h⟩] := by
    rw [List.take_add_one, List.getElem?_eq_getElem h]
    rfl
  rw [chainPre, htake, chainOp_concat]
  rfl

/-- The full prefix is the whole chain. -/
theorem chainPre_length {ι : Type*} (xs : List ι)
    (f : ι → EndM D (univ : Finset L)) :
    chainPre xs f xs.length = chainOp xs f := by
  rw [chainPre, List.take_length]

/-- The position bridge between the ℕ-indexed pass list of a counted loop and
an arbitrary gate list: if the `j`-th pass operator is the `j`-th list gate,
the `chainOp` over `List.range` is the `chainOp` over the list.  (Instance of
`chainOp_chain` along the `chainPre` prefix family.) -/
theorem chainOp_range_of_get {ι : Type*} (l : List ι)
    (G : ℕ → EndM D (univ : Finset L)) (K : ι → EndM D (univ : Finset L))
    (h : ∀ (j : ℕ) (hj : j < l.length), G j = K (l.get ⟨j, hj⟩)) :
    chainOp (List.range l.length) G = chainOp l K := by
  refine LinearMap.ext fun z => ?_
  have hstep : ∀ (j : ℕ) (hj : j < (List.range l.length).length),
      G ((List.range l.length).get ⟨j, hj⟩) (chainPre l K j z)
        = chainPre l K (j + 1) z := by
    intro j hj
    have hjl : j < l.length := by rwa [List.length_range] at hj
    have hget : (List.range l.length).get ⟨j, hj⟩ = j := by
      simp [List.get_eq_getElem, List.getElem_range]
    rw [hget, h j hjl, chainPre_succ l K hjl, LinearMap.comp_apply]
  have hv := chainOp_chain (List.range l.length) G
    (fun m => chainPre l K m z) hstep
  rw [List.length_range] at hv
  calc chainOp (List.range l.length) G z
      = chainOp (List.range l.length) G (chainPre l K 0 z) := by
        rw [chainPre_zero, Module.End.one_apply]
    _ = chainPre l K l.length z := hv
    _ = chainOp l K z := by rw [chainPre_length]

/-- `chainPre_succ` at `List.finRange n` — the indexing the `for`-shaped
consumers use. -/
theorem chainPre_finRange_succ {n : ℕ} (f : Fin n → EndM D (univ : Finset L))
    {k : ℕ} (h : k < n) :
    chainPre (List.finRange n) f (k + 1) = f ⟨k, h⟩ ∘ₗ chainPre (List.finRange n) f k := by
  have hlen : k < (List.finRange n).length := by rwa [List.length_finRange]
  rw [chainPre_succ (List.finRange n) f hlen]
  have hget : (List.finRange n).get ⟨k, hlen⟩ = (⟨k, h⟩ : Fin n) := by
    simp [List.get_eq_getElem, List.getElem_finRange]
  rw [hget]

/-- `chainPre_length` at `List.finRange n`. -/
theorem chainPre_finRange_length {n : ℕ} (f : Fin n → EndM D (univ : Finset L)) :
    chainPre (List.finRange n) f n = chainOp (List.finRange n) f := by
  have h := chainPre_length (List.finRange n) f
  rwa [List.length_finRange] at h

/-! ## §6. The effect algebra of an orthonormal set of outcomes -/

section OuterSum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {ι : Type*}

/-- **The Born sum**, complex form: the quadratic form of a sum of rank-one
projectors is the sum of the squared moduli of the amplitudes. No
orthonormality is needed for this identity. -/
theorem inner_sum_outerLM_self (s : Finset ι) (f : ι → E) (w : E) :
    (⟪w, (∑ i ∈ s, outerLM (f i) (f i)) w⟫ : ℂ) = ∑ i ∈ s, (‖⟪f i, w⟫‖ : ℂ) ^ 2 := by
  rw [LinearMap.sum_apply, inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [outerLM_apply, inner_smul_right, ← inner_conj_symm w (f i), RCLike.mul_conj]
  norm_cast

/-- **The Born sum**, real form — the number an `expect` computation lands
on. -/
theorem re_inner_sum_outerLM_self (s : Finset ι) (f : ι → E) (w : E) :
    (⟪w, (∑ i ∈ s, outerLM (f i) (f i)) w⟫ : ℂ).re = ∑ i ∈ s, ‖⟪f i, w⟫‖ ^ 2 := by
  rw [inner_sum_outerLM_self, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

/-- A sum of rank-one projectors along a family that is orthonormal **on `s`**
is a symmetric projection: positivity gives symmetry, and orthonormality
gives idempotence through `outerLM_comp`. -/
theorem isProjOp_sum_outerLM_of_orthonormal [DecidableEq ι] (s : Finset ι) (f : ι → E)
    (hf : ∀ i ∈ s, ∀ j ∈ s, (⟪f i, f j⟫ : ℂ) = if i = j then (1 : ℂ) else 0) :
    IsProjOp (∑ i ∈ s, outerLM (f i) (f i)) := by
  have hpos : (∑ i ∈ s, outerLM (f i) (f i)).IsPositive :=
    LinearMap.isPositive_sum s fun i _ => isPositive_outerLM_self (f i)
  have hidem : (∑ i ∈ s, outerLM (f i) (f i)) * (∑ i ∈ s, outerLM (f i) (f i))
      = ∑ i ∈ s, outerLM (f i) (f i) := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have key : ∀ j ∈ s, (outerLM (f i) (f i) : E →ₗ[ℂ] E) * outerLM (f j) (f j)
        = if i = j then outerLM (f i) (f i) else 0 := by
      intro j hj
      have hcomp : (outerLM (f i) (f i) : E →ₗ[ℂ] E) * outerLM (f j) (f j)
          = (⟪f i, f j⟫ : ℂ) • outerLM (f i) (f j) := outerLM_comp _ _ _ _
      rw [hcomp, hf i hi j hj]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    rw [Finset.sum_congr rfl key, Finset.sum_ite_eq s i fun _ => outerLM (f i) (f i),
      if_pos hi]
  exact ⟨hidem, hpos.isSymmetric⟩

/-- **A set of orthonormal outcomes is a quantum predicate.** The sum of the
rank-one projectors of an orthonormal family is an effect, `0 ≤ A ≤ 1`, hence
the `op`-component of a genuine `Assn`. It is a symmetric projection, so this
is exact — no Bessel estimate is involved. -/
theorem isEffect_sum_outerLM_of_orthonormal [FiniteDimensional ℂ E] [DecidableEq ι]
    (s : Finset ι) (f : ι → E)
    (hf : ∀ i ∈ s, ∀ j ∈ s, (⟪f i, f j⟫ : ℂ) = if i = j then (1 : ℂ) else 0) :
    IsEffect (∑ i ∈ s, outerLM (f i) (f i)) :=
  isEffect_of_isProjOp (isProjOp_sum_outerLM_of_orthonormal s f hf)

end OuterSum

/-! ## §7. Transport laws -/

/-- A unitary is norm preserving. -/
theorem norm_apply_of_isUnitary {K : EndM D (univ : Finset L)} (hK : IsUnitary K)
    (v : HS D (univ : Finset L)) : ‖K v‖ = ‖v‖ := by
  have h : (⟪K v, K v⟫ : ℂ) = ⟪v, v⟫ := hK.isIsometryOp v v
  rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ), inner_self_eq_norm_sq_to_K (𝕜 := ℂ)] at h
  have h2 : ‖K v‖ ^ 2 = ‖v‖ ^ 2 := by exact_mod_cast h
  rw [← Real.sqrt_sq (norm_nonneg (K v)), ← Real.sqrt_sq (norm_nonneg v), h2]

/-- **The Born factorisation of a block gate on a product frame.** The
amplitude of a basis outcome `m` after applying a gate `G` on the
sub-register `r` of a product state factors as

* the amplitude, *inside the register's own block*, of the restricted outcome
  against `G` applied to the block factor, times
* the amplitude of the complementary restricted outcome against the untouched
  complement factor.

This is CoqQ's `lift_lf`/`tenvm` (`liftF_regOp_prodV` here) read through
`dv_split` (`deltav_split`) and `tenv_dot` (`tenv_inner`): the frame never
has to be re-derived at a use site, and the block amplitude is computed
entirely in the register's own tuple space. -/
theorem inner_deltav_regLift_prodV {k : ℕ} (r : Reg L k)
    (G : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun)
    (ψ : ∀ i, EuclideanSpace ℂ (D i)) (m : QIdx D (univ : Finset L)) :
    (⟪deltav D m, regLift r G (prodV D (W := (univ : Finset L)) ψ)⟫ : ℂ)
      = ⟪deltav D (QIdx.res D (subset_univ r.sig) m),
          r.op D G (prodV D (W := r.sig) ψ)⟫
        * ⟪deltav D (QIdx.res D (sdiff_subset : (univ : Finset L) \ r.sig ⊆ univ) m),
            prodV D (W := (univ : Finset L) \ r.sig) ψ⟫ := by
  have hcast : QIdx.cast D (union_sdiff_of_subset (subset_univ r.sig))
      (QIdx.cast D (union_sdiff_of_subset (subset_univ r.sig)).symm m) = m :=
    funext fun _ => rfl
  have hm : deltav D m = castH D (union_sdiff_of_subset (subset_univ r.sig))
      (deltav D (QIdx.cast D (union_sdiff_of_subset (subset_univ r.sig)).symm m)) := by
    rw [castH_deltav, hcast]
  have hres1 : QIdx.res D subset_union_left
      (QIdx.cast D (union_sdiff_of_subset (subset_univ r.sig)).symm m)
      = QIdx.res D (subset_univ r.sig) m := funext fun _ => rfl
  have hres2 : QIdx.res D subset_union_right
      (QIdx.cast D (union_sdiff_of_subset (subset_univ r.sig)).symm m)
      = QIdx.res D (sdiff_subset : (univ : Finset L) \ r.sig ⊆ univ) m := funext fun _ => rfl
  rw [regLift, liftF_regOp_prodV, hm, castH_inner, deltav_split,
    tenv_inner D disjoint_sdiff_self_right, hres1, hres2]

/-! ## §8. The Born amplitude of a straight-line block gate

§3–§4 evaluate the folded (Ax-Uni) precondition *as an expectation*; §7
factorises one block gate on a product frame. This last section supplies the
two remaining generic steps a Born computation on a superposed input needs.

* `inner_foldr_unitaryPre` / `inner_unitaryPre` — the **complex** (not just
  real) form of the `wp`-chain display, so that several folds of different
  register arities can be peeled one after the other inside a single inner
  product before any `re` is taken.
* `Reg.idxEquiv_restrict`, `inner_deltav_regLift_prodV_tupleV` — the block
  amplitude of `inner_deltav_regLift_prodV` read **in the register's own tuple
  space**: for a basis outcome coming from a *total* classical state `mtot` of
  the world, the block factor is an amplitude against `EuclideanSpace.single`
  in `TSpace D r.toFun` and the complement factor is a plain product of
  one-cell amplitudes over `univ \ r.sig`.
* `inner_single_fullGate_tupleV` — and, when the gate is a `Reg.fullGate` of a
  whole-world unitary `V` (the shape a *subroutine* takes,
  `Qhl/Logic/UnitaryFull.lean` §2), that tuple-space amplitude is literally the
  amplitude of `V` on the subroutine's own world: `Reg.fullEnc_tupleV` for the
  state, `Reg.encode_deltav` + `castH_deltav` for the outcome label.

Composing the last two, the readout amplitude of a basis outcome after a
subroutine `V` applied at a sub-register of a bigger world is the readout
amplitude of `V` in its own world times the frame amplitudes — which is exactly
what a precision analysis proved about `V` alone can be fed. Everything is
generic: no program, no gate and no example fixture is named. -/

/-- The complex form of the `wp`-chain display (§3) at a vector: the folded
(Ax-Uni) precondition, evaluated as a quadratic form at `v`, is the
postcondition evaluated at the evolved vector `W v`. `expect_foldr_unitaryPre_pure`
is its real part at a pure state; this form is what lets several folds be
peeled successively inside one inner product. -/
theorem inner_foldr_unitaryPre {ι : Type*} (l : List ι) (k : ι → ℕ)
    (R : ∀ i, RegExpr σT L (k i)) (U : ∀ i σ, UnitaryOp (TSpace D (R i σ)))
    (B : Assn σT D) (σ : σT) (h : ∀ i, Function.Injective (R i σ))
    (v : HS D (univ : Finset L)) :
    (⟪v, (l.foldr (fun i A => A.unitaryPre (R i) (U i)) B).op σ v⟫ : ℂ)
      = ⟪chainOp l (fun i => regLift ⟨R i σ, h i⟩ (U i σ)) v,
          B.op σ (chainOp l (fun i => regLift ⟨R i σ, h i⟩ (U i σ)) v)⟫ := by
  rw [foldr_unitaryPre_op l k R U B σ h]
  simp only [LinearMap.comp_apply]
  rw [LinearMap.adjoint_inner_right]

/-- One (Ax-Uni) step in the same complex form — the `l = [i]` case of
`inner_foldr_unitaryPre`, stated directly so that a single `Prog.unitary`
statement can be peeled without wrapping it in a list. -/
theorem inner_unitaryPre {k : ℕ} (R : RegExpr σT L k)
    (U : ∀ σ, UnitaryOp (TSpace D (R σ))) (B : Assn σT D) (σ : σT)
    (h : Function.Injective (R σ)) (v : HS D (univ : Finset L)) :
    (⟪v, (B.unitaryPre R U).op σ v⟫ : ℂ)
      = ⟪regLift ⟨R σ, h⟩ (U σ) v, B.op σ (regLift ⟨R σ, h⟩ (U σ) v)⟫ := by
  rw [Assn.unitaryPre_op_of_dist B R U h]
  simp only [LinearMap.comp_apply]
  rw [LinearMap.adjoint_inner_right]

omit [Fintype L] [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)] [∀ i, Inhabited (D i)] in
/-- The classical state of a register's own tuple space induced by a **total**
classical state `mtot` of the world is carried by `Reg.idxEquiv` to the
restriction of `mtot` to the register's support: reading the tuple at the cell
`r j` returns `mtot (r j)` (`Reg.idxEquiv_apply_equivSig`). -/
theorem Reg.idxEquiv_restrict {k : ℕ} (r : Reg L k) (mtot : ∀ i, D i) :
    r.idxEquiv D (fun j => mtot (r j)) = fun x : ↥r.sig => mtot (x : L) := by
  funext x
  obtain ⟨j, rfl⟩ := r.equivSig.surjective x
  rw [Reg.idxEquiv_apply_equivSig]
  rfl

/-- **The Born factorisation, in the register's own tuple space.** For a basis
outcome labelled by a *total* classical state `mtot` of the world, the
amplitude after a block gate `G` on the sub-register `r` of a product state is

* the amplitude of `G` against the tuple-space basis vector of the restricted
  label, computed entirely inside `TSpace D r.toFun` — the gate's own world —
  times
* the plain product, over the untouched cells `univ \ r.sig`, of the one-cell
  amplitudes of the frame.

This is `inner_deltav_regLift_prodV` (§7) with both factors evaluated:
`prodV_sig_reg` + `Reg.op_apply` on the block, `prodV_single` + `prodV_inner`
on the complement. -/
theorem inner_deltav_regLift_prodV_tupleV {k : ℕ} (r : Reg L k)
    (G : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun)
    (ψ : ∀ i, EuclideanSpace ℂ (D i)) (mtot : ∀ i, D i) :
    (⟪deltav D (fun i : ↥(univ : Finset L) => mtot (i : L)),
        regLift r G (prodV D (W := (univ : Finset L)) ψ)⟫ : ℂ)
      = ⟪EuclideanSpace.single (fun j => mtot (r j)) 1,
            G (tupleV D r.toFun fun j => ψ (r j))⟫
        * ∏ i ∈ (univ : Finset L) \ r.sig, ⟪EuclideanSpace.single (mtot i) 1, ψ i⟫ := by
  rw [inner_deltav_regLift_prodV r G ψ (fun i : ↥(univ : Finset L) => mtot (i : L))]
  refine congrArg₂ (· * ·) ?_ ?_
  · rw [prodV_sig_reg, Reg.op_apply, LinearIsometryEquiv.symm_apply_apply]
    have hres : QIdx.res D (subset_univ r.sig) (fun i : ↥(univ : Finset L) => mtot (i : L))
        = r.idxEquiv D (fun j => mtot (r j)) := (Reg.idxEquiv_restrict r mtot).symm
    rw [hres, deltav, ← Reg.encode_single, LinearIsometryEquiv.inner_map_map]
  · have hres : QIdx.res D (sdiff_subset : (univ : Finset L) \ r.sig ⊆ (univ : Finset L))
        (fun i : ↥(univ : Finset L) => mtot (i : L))
        = fun i : ↥((univ : Finset L) \ r.sig) => mtot (i : L) := rfl
    rw [hres, ← prodV_single D (W := (univ : Finset L) \ r.sig) mtot, prodV_inner]
    exact Finset.prod_coe_sort ((univ : Finset L) \ r.sig)
      (fun i => (⟪EuclideanSpace.single (mtot i) 1, ψ i⟫ : ℂ))

omit [∀ i, Inhabited (D i)] in
/-- **A subroutine's own amplitude, read at a placement.** When the block gate
is the transported whole-world unitary `r.fullGate D hr V` of a full-coverage
register (`Qhl/Logic/UnitaryFull.lean` §2) — i.e. the gate is a *subroutine*
`V` given on its own world — the tuple-space amplitude of
`inner_deltav_regLift_prodV_tupleV` is literally the amplitude of `V` between
the basis ket of `mtot` and the product state of the same factors.

So a fact proved about the operator `V` **alone** (e.g. a readout-amplitude
estimate) is consumable verbatim after `V` has been placed at a sub-register of
a larger world. `Reg.fullEnc_tupleV` handles the state, `Reg.encode_deltav` and
`castH_deltav` the outcome label. -/
theorem inner_single_fullGate_tupleV {k : ℕ} (r : Reg L k)
    (hr : r.sig = (univ : Finset L)) (V : UnitaryOp (HS D (univ : Finset L)))
    (ψ : ∀ i, EuclideanSpace ℂ (D i)) (mtot : ∀ i, D i) :
    (⟪EuclideanSpace.single (fun j => mtot (r j)) 1,
        (r.fullGate D hr V : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun)
          (tupleV D r.toFun fun j => ψ (r j))⟫ : ℂ)
      = ⟪deltav D (fun i : ↥(univ : Finset L) => mtot (i : L)),
          (V : HS D (univ : Finset L) →ₗ[ℂ] HS D (univ : Finset L))
            (prodV D (W := (univ : Finset L)) ψ)⟫ := by
  have hlab : r.fullEnc D hr (EuclideanSpace.single (fun j => mtot (r j)) 1)
      = deltav D (fun i : ↥(univ : Finset L) => mtot (i : L)) := by
    rw [Reg.fullEnc_apply, Reg.encode_single, ← deltav, castH_deltav,
      Reg.idxEquiv_restrict]
    rfl
  have hG : (r.fullGate D hr V : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun)
      (tupleV D r.toFun fun j => ψ (r j))
      = (r.fullEnc D hr).symm ((V : HS D (univ : Finset L) →ₗ[ℂ] HS D (univ : Finset L))
          (r.fullEnc D hr (tupleV D r.toFun fun j => ψ (r j)))) := rfl
  rw [hG, ← LinearIsometryEquiv.inner_map_map (r.fullEnc D hr),
    LinearIsometryEquiv.apply_symm_apply, Reg.fullEnc_tupleV, hlab]

end Qhl
