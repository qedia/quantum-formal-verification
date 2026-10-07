import Qhl.HSpace.Basic

/-!
# The labelled Dirac type: definition and module structure

Mirror of `CoqQ/src/dirac/dirac.v:86-214` (spec 03 §1, subgoals D-1, D-2).

`Dirac D` is the formal direct sum `⊕ (S T : Finset L), LinM D S T`: a
labelled Dirac expression stores one `(S, T)`-block linear map for every pair
of label sets, so kets, bras, scalars and operators over arbitrary label sets
coexist in a single non-dependent type. Unlike layer 1 (HSpace), this layer
assumes `[Fintype L]` (needed for the block decomposition
`∑ S, ∑ T, ⌈d S T⌉ᴰ = d` and for finite-dimensionality).

* `Dirac D` — one-field structure around `∀ S T : Finset L, LinM D S T`
  (CoqQ `'D[H]`, a `Variant` with `isNew`, `dirac.v:86-98`); coercion to
  functions (CoqQ `fun_of_dirac:93`), extensionality `Dirac.ext`
  (CoqQ `diracP:115`)
* `AddCommGroup (Dirac D)`, `Module ℂ (Dirac D)` — componentwise
  (CoqQ `dirac.v:136-179`), with `rfl` apply-lemmas tagged `dirac_simps`
* `Dirac.equivFun` — linear equivalence to the Pi type
  (CoqQ `dirac_vect_iso:190-214`), yielding `FiniteDimensional ℂ (Dirac D)`
-/

namespace Qhl

open Finset

/-- The labelled Dirac type: the formal direct sum
`⊕ (S T : Finset L), LinM D S T`, wrapped in a one-field structure for
instance and notation hygiene. CoqQ: `'D[H]`, a `Variant` with `isNew`
(`dirac.v:86-98`). -/
structure Dirac {L : Type*} [Fintype L] [DecidableEq L] (D : L → Type*)
    [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)] where
  /-- Wrap a dependent function of blocks as a Dirac expression.
  CoqQ: the `Dirac` constructor (`dirac.v:86-98`). -/
  ofFun ::
  /-- The `(S, T)`-block of a Dirac expression. CoqQ: `fun_of_dirac`
  (`dirac.v:93`). -/
  toFun : ∀ S T : Finset L, LinM D S T

namespace Dirac

variable {L : Type*} [Fintype L] [DecidableEq L] {D : L → Type*}
  [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]

/-- Dirac expressions apply to a pair of label sets, giving the block.
CoqQ: `fun_of_dirac` (`dirac.v:93`). -/
instance : CoeFun (Dirac D) fun _ => ∀ S T : Finset L, LinM D S T :=
  ⟨toFun⟩

theorem toFun_injective :
    Function.Injective (toFun : Dirac D → ∀ S T : Finset L, LinM D S T) :=
  fun _ _ h => congrArg ofFun h

/-- Dirac expressions with equal blocks are equal. CoqQ: `diracP`
(`dirac.v:115`). -/
@[ext]
theorem ext {d e : Dirac D} (h : ∀ S T : Finset L, d S T = e S T) : d = e :=
  toFun_injective (funext fun S => funext fun T => h S T)

/-! ## D-2: componentwise module structure (CoqQ `dirac.v:136-179`)

The operations are defined componentwise by hand, then the axioms are
transported along `toFun` by `Function.Injective.addCommGroup`/`.module`, so
that all the apply-lemmas below are `rfl`. -/

instance : Zero (Dirac D) := ⟨ofFun fun _ _ => 0⟩
instance : Add (Dirac D) := ⟨fun d e => ofFun fun S T => d S T + e S T⟩
instance : Neg (Dirac D) := ⟨fun d => ofFun fun S T => -d S T⟩
instance : Sub (Dirac D) := ⟨fun d e => ofFun fun S T => d S T - e S T⟩
instance : SMul ℂ (Dirac D) := ⟨fun c d => ofFun fun S T => c • d S T⟩
instance : SMul ℕ (Dirac D) := ⟨fun n d => ofFun fun S T => n • d S T⟩
instance : SMul ℤ (Dirac D) := ⟨fun n d => ofFun fun S T => n • d S T⟩

instance : AddCommGroup (Dirac D) :=
  Function.Injective.addCommGroup toFun toFun_injective rfl (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

instance : Module ℂ (Dirac D) :=
  Function.Injective.module ℂ
    { toFun := toFun, map_zero' := rfl, map_add' := fun _ _ => rfl }
    toFun_injective fun _ _ => rfl

/-! ## Apply-lemmas (all `rfl`; tagged `dirac_simps`) -/

@[simp, dirac_simps]
theorem zero_apply (S T : Finset L) : (0 : Dirac D) S T = 0 := rfl

@[simp, dirac_simps]
theorem add_apply (d e : Dirac D) (S T : Finset L) :
    (d + e) S T = d S T + e S T := rfl

@[simp, dirac_simps]
theorem neg_apply (d : Dirac D) (S T : Finset L) : (-d) S T = -d S T := rfl

@[simp, dirac_simps]
theorem sub_apply (d e : Dirac D) (S T : Finset L) :
    (d - e) S T = d S T - e S T := rfl

@[simp, dirac_simps]
theorem smul_apply (c : ℂ) (d : Dirac D) (S T : Finset L) :
    (c • d) S T = c • d S T := rfl

@[simp, dirac_simps]
theorem nsmul_apply (n : ℕ) (d : Dirac D) (S T : Finset L) :
    (n • d) S T = n • d S T := rfl

@[simp, dirac_simps]
theorem zsmul_apply (n : ℤ) (d : Dirac D) (S T : Finset L) :
    (n • d) S T = n • d S T := rfl

/-- Finite sums of Dirac expressions evaluate blockwise. CoqQ: consequence of
the componentwise `lmodType` structure (`dirac.v:136-179`). -/
@[simp, dirac_simps]
theorem sum_apply {ι : Type*} (s : Finset ι) (f : ι → Dirac D)
    (S T : Finset L) : (∑ i ∈ s, f i) S T = ∑ i ∈ s, f i S T := by
  induction s using Finset.cons_induction with
  | empty => rfl
  | cons i s hi ih => rw [Finset.sum_cons, Finset.sum_cons, add_apply, ih]

/-! ## D-2: the vector-space isomorphism and finite-dimensionality -/

variable (D) in
/-- `Dirac D` is linearly equivalent to the Pi type of its blocks.
CoqQ: `dirac_vect_iso` (`dirac.v:190-214`). -/
def equivFun : Dirac D ≃ₗ[ℂ] ∀ S T : Finset L, LinM D S T where
  toFun := toFun
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun := ofFun
  left_inv _ := rfl
  right_inv _ := rfl

@[simp, dirac_simps]
theorem equivFun_apply (d : Dirac D) (S T : Finset L) :
    equivFun D d S T = d S T := rfl

@[simp, dirac_simps]
theorem equivFun_symm_apply (f : ∀ S T : Finset L, LinM D S T) :
    (equivFun D).symm f = ofFun f := rfl

/-- `Dirac D` is finite-dimensional, via `Dirac.equivFun`.
CoqQ: `dirac_vect_iso` (`dirac.v:190-214`). -/
instance : FiniteDimensional ℂ (Dirac D) :=
  Module.Finite.equiv (equivFun D).symm

end Dirac

end Qhl
