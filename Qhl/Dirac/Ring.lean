import Qhl.Dirac.Products

/-!
# The commutative `⊗ᴰ`-algebra structure on `Dirac`

Mirror of `CoqQ/src/dirac/dirac.v:644-746,1065` (spec 03 §3, subgoals D-4 and
the remaining part of D-6).

* Sum-extensions of bilinearity: `tensor_sum_left/right`, `comp_sum_left/right`,
  `dot_sum_left/right` (lifting the `_add_`/`_zero_` laws of
  `Qhl.Dirac.Products` through `Finset.sum` by `Finset.cons_induction`)
* Ring laws: `tensor_assoc` (CoqQ `tendA:644`), `tensor_comm` (`tendC:662`),
  `num_one_tensor`/`tensor_num_one` (`ten1d:669`), `comp_assoc` (`muldA:746`)
* D-4 instances: `One`/`Mul` (`* = ⊗ᴰ`, `1 = num D 1`), **`CommRing (Dirac D)`**
  (CoqQ `tend_comRingMixin:741-744`), **`Algebra ℂ (Dirac D)`** via
  `Algebra.ofModule`, `Nontrivial`
* Bridges: `algebraMap_eq_num`, `num_one`, `num_mul` (CoqQ `numdM`),
  `smul_eq_num_tensor` (CoqQ `numdTl:1065`, = `Algebra.smul_def`)

**Flag (spec 03 §3):** on `Dirac D`, `*` means the labelled *tensor* `⊗ᴰ` and
`1` is the scalar `num D 1` at block `(∅, ∅)` — not composition and not any
identity operator. Payoff: `ring` normalizes tensor-polynomials and
`Finset.prod` is the big tensor (see the smoke tests at the end of this file).
Composition `∘ᴰ` stays a bare associative bilinear operation (no global unit),
and `·ᴰ` a bare bilinear operation — no instances for either.
-/

namespace Qhl

open Finset

variable {L : Type*} [Fintype L] [DecidableEq L] {D : L → Type*}
  [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)] {S T S' T' : Finset L}

namespace Dirac

/-! ## D-6: sum-extensions of bilinearity (CoqQ `linear_suml/sumr` instances
on `tend`/`muld`/`dotd`, `dirac.v:681-871`) -/

/-- `⊗ᴰ` distributes over sums on the left. CoqQ `tend_suml`. -/
theorem tensor_sum_left {ι : Type*} (s : Finset ι) (d : ι → Dirac D)
    (e : Dirac D) : (∑ i ∈ s, d i) ⊗ᴰ e = ∑ i ∈ s, d i ⊗ᴰ e := by
  induction s using Finset.cons_induction with
  | empty => simp only [Finset.sum_empty, tensor_zero_left]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, tensor_add_left, ih]

/-- `⊗ᴰ` distributes over sums on the right. CoqQ `tend_sumr`. -/
theorem tensor_sum_right {ι : Type*} (s : Finset ι) (d : Dirac D)
    (e : ι → Dirac D) : d ⊗ᴰ (∑ i ∈ s, e i) = ∑ i ∈ s, d ⊗ᴰ e i := by
  induction s using Finset.cons_induction with
  | empty => simp only [Finset.sum_empty, tensor_zero_right]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, tensor_add_right, ih]

/-- `∘ᴰ` distributes over sums on the left. CoqQ `muld_suml`. -/
theorem comp_sum_left {ι : Type*} (s : Finset ι) (d : ι → Dirac D)
    (e : Dirac D) : (∑ i ∈ s, d i) ∘ᴰ e = ∑ i ∈ s, d i ∘ᴰ e := by
  induction s using Finset.cons_induction with
  | empty => simp only [Finset.sum_empty, comp_zero_left]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, comp_add_left, ih]

/-- `∘ᴰ` distributes over sums on the right. CoqQ `muld_sumr`. -/
theorem comp_sum_right {ι : Type*} (s : Finset ι) (d : Dirac D)
    (e : ι → Dirac D) : d ∘ᴰ (∑ i ∈ s, e i) = ∑ i ∈ s, d ∘ᴰ e i := by
  induction s using Finset.cons_induction with
  | empty => simp only [Finset.sum_empty, comp_zero_right]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, comp_add_right, ih]

/-- `·ᴰ` distributes over sums on the left. CoqQ `dotd_suml`. -/
theorem dot_sum_left {ι : Type*} (s : Finset ι) (d : ι → Dirac D)
    (e : Dirac D) : (∑ i ∈ s, d i) ·ᴰ e = ∑ i ∈ s, d i ·ᴰ e := by
  induction s using Finset.cons_induction with
  | empty => simp only [Finset.sum_empty, dot_zero_left]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, dot_add_left, ih]

/-- `·ᴰ` distributes over sums on the right. CoqQ `dotd_sumr`. -/
theorem dot_sum_right {ι : Type*} (s : Finset ι) (d : Dirac D)
    (e : ι → Dirac D) : d ·ᴰ (∑ i ∈ s, e i) = ∑ i ∈ s, d ·ᴰ e i := by
  induction s using Finset.cons_induction with
  | empty => simp only [Finset.sum_empty, dot_zero_right]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, dot_add_right, ih]

/-! ## Sum-pushing through `∘ₗ` (local helpers for `comp_assoc`) -/

private theorem sumLM_comp {ι : Type*} {A B C : Finset L} (s : Finset ι)
    (f : ι → LinM D B C) (g : LinM D A B) :
    (∑ i ∈ s, f i) ∘ₗ g = ∑ i ∈ s, f i ∘ₗ g := by
  induction s using Finset.cons_induction with
  | empty => simp only [Finset.sum_empty, LinearMap.zero_comp]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, LinearMap.add_comp, ih]

private theorem comp_sumLM {ι : Type*} {A B C : Finset L} (s : Finset ι)
    (g : LinM D B C) (f : ι → LinM D A B) :
    g ∘ₗ (∑ i ∈ s, f i) = ∑ i ∈ s, g ∘ₗ f i := by
  induction s using Finset.cons_induction with
  | empty => simp only [Finset.sum_empty, LinearMap.comp_zero]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, LinearMap.comp_add, ih]

/-! ## D-6: ring laws of `⊗ᴰ` (CoqQ `tendA:644`, `tendC:662`, `ten1d:669`)

Strategy: reduce to single blocks by `sum_ofBlock` + the sum-extensions above,
then absorb the layer-1 cast (`tenf_castA`/`tenf_castC`/`tenf_cast1r`) with
`ofBlock_castF`. -/

/-- A single block tensor-commutes with any Dirac expression (single-block
case of CoqQ `tendC:662`). -/
theorem ofBlock_tensor_comm (f : LinM D S T) (e : Dirac D) :
    (⌈f⌉ᴰ : Dirac D) ⊗ᴰ e = e ⊗ᴰ ⌈f⌉ᴰ := by
  conv_lhs => rw [← sum_ofBlock e]
  conv_rhs => rw [← sum_ofBlock e]
  simp only [tensor_sum_left, tensor_sum_right, ofBlock_tensor]
  exact Finset.sum_congr rfl fun S₂ _ => Finset.sum_congr rfl fun T₂ _ => by
    rw [← tenf_castC D (union_comm S S₂) (union_comm T T₂) f (e S₂ T₂),
      ofBlock_castF]

/-- `⊗ᴰ` is associative — with *no* side condition and *no* cast.
CoqQ `tendA` (`dirac.v:644`). -/
theorem tensor_assoc (d₁ d₂ d₃ : Dirac D) :
    d₁ ⊗ᴰ d₂ ⊗ᴰ d₃ = d₁ ⊗ᴰ (d₂ ⊗ᴰ d₃) := by
  conv_lhs => rw [← sum_ofBlock d₁, ← sum_ofBlock d₂, ← sum_ofBlock d₃]
  conv_rhs => rw [← sum_ofBlock d₁, ← sum_ofBlock d₂, ← sum_ofBlock d₃]
  simp only [tensor_sum_left, tensor_sum_right, ofBlock_tensor]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  rw [← tenf_castA D (union_assoc _ _ _).symm (union_assoc _ _ _).symm,
    ofBlock_castF]

/-- `⊗ᴰ` is commutative — with *no* side condition and *no* cast.
CoqQ `tendC` (`dirac.v:662`). -/
theorem tensor_comm (d₁ d₂ : Dirac D) : d₁ ⊗ᴰ d₂ = d₂ ⊗ᴰ d₁ := by
  conv_lhs => rw [← sum_ofBlock d₁]
  conv_rhs => rw [← sum_ofBlock d₁]
  simp only [tensor_sum_left, tensor_sum_right]
  exact Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun T _ =>
    ofBlock_tensor_comm (d₁ S T) d₂

private theorem num_one_tensor_ofBlock (g : LinM D S T) :
    num D 1 ⊗ᴰ (⌈g⌉ᴰ : Dirac D) = ⌈g⌉ᴰ := by
  rw [num, toScalarM_one, ofBlock_tensor,
    ← tenf_castC D (union_comm S ∅) (union_comm T ∅) g (1 : EndM D ∅),
    ofBlock_castF,
    ← ofBlock_castF (union_empty S) (union_empty T) (tenf D g (1 : EndM D ∅)),
    tenf_cast1r]

/-- The scalar `1` is a left unit for `⊗ᴰ`. CoqQ `ten1d` (`dirac.v:669`). -/
@[simp, dirac_simps]
theorem num_one_tensor (d : Dirac D) : num D 1 ⊗ᴰ d = d := by
  conv_lhs => rw [← sum_ofBlock d]
  conv_rhs => rw [← sum_ofBlock d]
  simp only [tensor_sum_right]
  exact Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun T _ =>
    num_one_tensor_ofBlock (d S T)

/-- The scalar `1` is a right unit for `⊗ᴰ`. CoqQ `tend1` (`dirac.v:669`). -/
@[simp, dirac_simps]
theorem tensor_num_one (d : Dirac D) : d ⊗ᴰ num D 1 = d := by
  rw [tensor_comm, num_one_tensor]

/-- `∘ᴰ` is associative (mind the argument order: ours is
`(d₁ ∘ᴰ d₂) S T = ∑ W, d₁ W T ∘ₗ d₂ S W`, i.e. `d₁` acts *after* `d₂`).
CoqQ `muldA` (`dirac.v:746`). -/
theorem comp_assoc (d₁ d₂ d₃ : Dirac D) :
    (d₁ ∘ᴰ d₂) ∘ᴰ d₃ = d₁ ∘ᴰ (d₂ ∘ᴰ d₃) := by
  refine ext fun S₀ T₀ => ?_
  simp only [comp_apply, sumLM_comp, comp_sumLM]
  conv_lhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun V _ => Finset.sum_congr rfl fun W _ =>
    LinearMap.comp_assoc (d₃ S₀ W) (d₂ W V) (d₁ V T₀)

/-! ## D-4: the commutative ring and ℂ-algebra instances
(CoqQ `tend_comRingMixin`, `dirac.v:741-744`) -/

/-- On `Dirac D`, `1` is the scalar `num D 1` at block `(∅, ∅)`. -/
noncomputable instance : One (Dirac D) := ⟨num D 1⟩

/-- On `Dirac D`, `*` is the labelled tensor `⊗ᴰ` (spec 03 §3 flag). -/
noncomputable instance : Mul (Dirac D) := ⟨tensor⟩

/-- Unfolding for the `One` instance. -/
theorem one_def : (1 : Dirac D) = num D 1 := rfl

/-- Unfolding for the `Mul` instance: `*` *is* `⊗ᴰ`. -/
theorem mul_def (d e : Dirac D) : d * e = d ⊗ᴰ e := rfl

/-- `(Dirac D, +, ⊗ᴰ, num D 1)` is a commutative ring.
CoqQ `tend_comRingMixin` (`dirac.v:741-744`). -/
noncomputable instance : CommRing (Dirac D) :=
  { (inferInstance : AddCommGroup (Dirac D)),
    (inferInstance : Mul (Dirac D)), (inferInstance : One (Dirac D)) with
    mul_assoc := tensor_assoc
    mul_comm := tensor_comm
    one_mul := num_one_tensor
    mul_one := tensor_num_one
    left_distrib := tensor_add_right
    right_distrib := tensor_add_left
    zero_mul := tensor_zero_left
    mul_zero := tensor_zero_right }

/-- `Dirac D` is a ℂ-algebra under `⊗ᴰ` (spec 03, D-4; the scalar action is
the existing componentwise `Module ℂ`). -/
noncomputable instance : Algebra ℂ (Dirac D) :=
  Algebra.ofModule (fun c x y => tensor_smul_left c x y)
    (fun c x y => tensor_smul_right c x y)

/-- The algebra map is `num` (CoqQ `numd` as a ring morphism; a bundled
`ℂ →+* Dirac D` is `algebraMap ℂ (Dirac D)` itself). -/
theorem algebraMap_eq_num (c : ℂ) : algebraMap ℂ (Dirac D) c = num D c := by
  rw [Algebra.algebraMap_eq_smul_one, one_def, ← num_smul, mul_one]

/-- `num` sends `1` to `1`. CoqQ `numd1` area (`dirac.v:443-482`). -/
@[simp, dirac_simps]
theorem num_one : num D (1 : ℂ) = 1 := rfl

/-- `num` is multiplicative. CoqQ `numdM` (`dirac.v:443-482`). -/
theorem num_mul (a b : ℂ) : num D (a * b) = num D a * num D b := by
  rw [← algebraMap_eq_num, ← algebraMap_eq_num, ← algebraMap_eq_num, map_mul]

/-- Scalar action as a tensor with a `num` block. CoqQ `numdTl`
(`dirac.v:1065`), = `Algebra.smul_def`. -/
theorem smul_eq_num_tensor (c : ℂ) (d : Dirac D) : c • d = num D c ⊗ᴰ d := by
  rw [Algebra.smul_def, algebraMap_eq_num, mul_def]

/-- `Dirac D` is nontrivial: `num D 1 ≠ 0` (the block `(∅, ∅)` is the
one-dimensional `HS D ∅ ≃ ℂ`). -/
instance : Nontrivial (Dirac D) where
  exists_pair_ne := ⟨1, 0, fun h => by
    have h1 : num D (1 : ℂ) = num D 0 := by rw [num_zero]; exact h
    exact one_ne_zero (num_injective h1)⟩

/-! ## Smoke tests (spec 03 §8): `ring` and `Finset.prod` on the
`⊗ᴰ`-algebra replace CoqQ's `tendA/tendC/tendACA` rewriting bundles -/

example (a b c : Dirac D) : a * (b + c) * a = a * a * b + c * a * a := by ring

example (d : Fin 3 → Dirac D) : ∏ i, d i = d 0 * d 1 * d 2 :=
  Fin.prod_univ_three d

end Dirac

end Qhl
