import Qhl.Logic.Assertion

/-!
# Computing the atomic predicate transformers: the initialisation Kraus sum

`Qhl/Logic/Assertion.lean` gives the three quantum predicate transformers of
the atomic axioms in the form each *proof* needs: `unitaryPre` and `measurePre`
are already displayed as an explicit conjugation resp. an explicit Born sum
(`unitaryPre_op_of_dist`, `measurePre_op_of_dist`), so a derivation computes
with them directly. The initialisation transformer (Ax-Init) is the odd one
out: `initPre_op` exposes it only as `E†` of an abstract channel,
`dualSO D (initLift (S σ))`.

This file supplies the missing display. `initKraus` names the Kraus family of
the initialisation channel `q̄ := ∣0…0⟩` on the whole world — CoqQ's
`initso`/`liftso` (`quantum.v`) — and `Assn.initPre_op_eq_sum` rewrites the
transformer as the *same shape* the other two axioms already have:

```
(A.initPre S).op σ = ∑ₓ (Eₓ)† ∘ A.op σ ∘ Eₓ .
```

The proof is three library rewrites (`initLift_eq_kraussoOf`,
`dualSO_kraussoOf`, `kraussoOf_apply`) plus `LinearMap.adjoint_adjoint`; the
dual of a Kraus map is the Kraus map of the adjoint family, which is why the
sum comes out with the *adjoints* on the outside — exactly the orientation a
backward (weakest-precondition) computation consumes.

Generic in the world `L`, the cell-type family `D`, the classical state space
`σT`, the assertion and the initialised cell set: no gate, no program and no
example fixture appears (ownership test).
-/

namespace Qhl

open Finset

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)]
variable {σT : Type*}

variable (D) in
/-- The Kraus family of the initialisation channel of the cell set `S`, on the
whole world: the operator `x ↦ ∣0…0⟩⟨x∣` of the initialised block, extended
cylindrically by the identity on the complement (CoqQ `initso` under
`liftso`). -/
noncomputable def initKraus (S : Finset L) (x : QIdx D S) : EndM D (univ : Finset L) :=
  liftF D (subset_univ S) (outerLM (deltav D (default : QIdx D S)) (deltav D x))

/-- The Kraus-sum display of the initialisation transformer (Ax-Init), in the
orientation a backward computation consumes:

```
(A.initPre S).op σ = ∑ₓ (Eₓ)† ∘ A.op σ ∘ Eₓ .
```

This is the initialisation counterpart of `Assn.unitaryPre_op_of_dist` and
`Assn.measurePre_op_of_dist`: with it, all three quantum axioms of `QHL⁺` are
computed by the same rank-one algebra (`adjoint_comp_outerLM_comp` and
friends), with no super-operator left in sight. -/
theorem Assn.initPre_op_eq_sum (A : Assn σT D) (S : σT → Finset L) (σ : σT) :
    (A.initPre S).op σ
      = ∑ x : QIdx D (S σ),
          LinearMap.adjoint (initKraus D (S σ) x) ∘ₗ A.op σ ∘ₗ initKraus D (S σ) x := by
  rw [Assn.initPre_op, initLift_eq_kraussoOf, dualSO_kraussoOf, kraussoOf_apply]
  exact Finset.sum_congr rfl fun x _ => by
    rw [initKraus, LinearMap.adjoint_adjoint]

end Qhl
