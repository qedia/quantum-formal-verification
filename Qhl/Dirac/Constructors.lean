import Qhl.Dirac.Basic
import Qhl.HSpace.Cast
import Qhl.HSpace.KetBra

/-!
# Dirac constructors, projections and their calculus

Mirror of `CoqQ/src/dirac/dirac.v:224-487` (spec 03 §2, subgoal D-3).

* `Dirac.ofBlock f`, notation `⌈f⌉ᴰ` — a single block map placed at its home
  block, `0` elsewhere (CoqQ `lind:224`, `'[f]`)
* `Dirac.ket v` / `Dirac.bra v`, notations `∣v⟩ᴰ` / `⟨v∣ᴰ` — kets and bras at
  blocks `(∅, S)` / `(S, ∅)` (CoqQ `ketd:231`, `brad:233`)
* `Dirac.num D c`, notation `cᴰ`, and `Dirac.one D S`, notation `𝟙ᴰ S` —
  scalars at `(∅, ∅)` and identities at `(S, S)` (CoqQ `numd:235`,
  `\1_S` `dirac.v:276`)
* `Dirac.toLinM`/`toKet`/`toBra`/`toScalar` — typed block projections
  (CoqQ `d2f:267`, `d2v:263`, `d2dv:265`, `d2c:269`)
* D-3: `ofBlock` evaluation (`lind_id:411`, `lind_eq0l/lind_eq0r:413-424`),
  cast absorption `ofBlock_castF`, linearity and injectivity, round-trips
  (`lindK/ketdK/bradK/numdK:426-438`), block decomposition
  `sum_ofBlock` (`lind_dec:487`), `ket`/`bra` (anti)linearity
  (`dirac.v:443-482`), `num` additivity

Notation: the spec writes `⌈f⌉` (CoqQ `'[f]`), but a bare `⌈·⌉` collides with
mathlib's global `Int.ceil` notation, so this project uses the `ᴰ`-suffixed
variant `⌈f⌉ᴰ` (all Dirac-layer notations carry the `ᴰ` suffix). In `cᴰ` and
`𝟙ᴰ S` the family `D` is a hole, elaborated from the expected `Dirac D` type.
-/

namespace Qhl

open Finset

variable {L : Type*} [Fintype L] [DecidableEq L] {D : L → Type*}
  [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)] {S T S' T' : Finset L}

namespace Dirac

/-! ## Constructors (CoqQ `dirac.v:224-235,276`) -/

/-- Embed a single block map `f : LinM D S T` as the Dirac expression that is
`f` at block `(S, T)` and `0` elsewhere. CoqQ: `lind` / `'[f]`
(`dirac.v:224`). -/
noncomputable def ofBlock (f : LinM D S T) : Dirac D :=
  ofFun fun S' T' => if h : S = S' ∧ T = T' then castF D h.1 h.2 f else 0

/-- The labelled ket `∣v⟩ᴰ`, at block `(∅, S)`. CoqQ: `ketd` / `'|v>`
(`dirac.v:231`). -/
noncomputable def ket (v : HS D S) : Dirac D := ofBlock (toKetM D v)

/-- The labelled bra `⟨v∣ᴰ`, at block `(S, ∅)`. CoqQ: `brad` / `'<v|`
(`dirac.v:233`). -/
noncomputable def bra (v : HS D S) : Dirac D := ofBlock (toBraM D v)

variable (D) in
/-- A scalar as a Dirac expression, at block `(∅, ∅)`. CoqQ: `numd` / `c%:D`
(`dirac.v:235`). -/
noncomputable def num (c : ℂ) : Dirac D := ofBlock (toScalarM D c)

variable (D) in
/-- The identity on the register set `S` as a Dirac expression, at block
`(S, S)`. CoqQ: `\1_S` (`dirac.v:276`). -/
noncomputable def one (S : Finset L) : Dirac D := ofBlock (1 : EndM D S)

/-! ## Projections (CoqQ `dirac.v:263-269`) -/

/-- Project the `(S, T)`-block out of a Dirac expression (the coercion, with
its target block spelled out). CoqQ: `d2f` (`dirac.v:267`). -/
def toLinM (S T : Finset L) (d : Dirac D) : LinM D S T := d S T

/-- Recover a ket on `S` from the `(∅, S)`-block. CoqQ: `d2v`
(`dirac.v:263`). -/
noncomputable def toKet (S : Finset L) (d : Dirac D) : HS D S :=
  ofKetM D (d ∅ S)

/-- Recover a bra vector on `S` from the `(S, ∅)`-block (conjugate-linear in
the block). CoqQ: `d2dv` (`dirac.v:265`). -/
noncomputable def toBra (S : Finset L) (d : Dirac D) : HS D S :=
  ofBraM D (d S ∅)

/-- Recover a scalar from the `(∅, ∅)`-block. CoqQ: `d2c` (`dirac.v:269`). -/
noncomputable def toScalar (d : Dirac D) : ℂ :=
  emptyIso D (d ∅ ∅ (deltav D default))

end Dirac

/-! ## Notations (scoped to `Qhl`; see the module docstring on the `ᴰ`
suffix) -/

@[inherit_doc Dirac.ofBlock]
scoped notation:max "⌈" f "⌉ᴰ" => Dirac.ofBlock f

@[inherit_doc Dirac.ket]
scoped notation:max "∣" v "⟩ᴰ" => Dirac.ket v

@[inherit_doc Dirac.bra]
scoped notation:max "⟨" v "∣ᴰ" => Dirac.bra v

@[inherit_doc Dirac.num]
scoped notation:max c:max "ᴰ" => Dirac.num _ c

@[inherit_doc Dirac.one]
scoped notation:max "𝟙ᴰ" S:max => Dirac.one _ S

namespace Dirac

/-! ## D-3: `ofBlock` evaluation (CoqQ `dirac.v:411-424`) -/

/-- Blockwise normal form of `ofBlock`, as a `dite`. CoqQ: definition of
`lind` (`dirac.v:224`). -/
theorem ofBlock_apply (f : LinM D S T) (S' T' : Finset L) :
    (⌈f⌉ᴰ) S' T' = if h : S = S' ∧ T = T' then castF D h.1 h.2 f else 0 :=
  rfl

/-- `ofBlock` evaluates to its block map at its home block. CoqQ: `lind_id`
(`dirac.v:411`). -/
@[simp, dirac_simps]
theorem ofBlock_apply_self (f : LinM D S T) : (⌈f⌉ᴰ) S T = f := by
  rw [ofBlock_apply, dif_pos ⟨rfl, rfl⟩, castF_rfl]
  rfl

/-- `ofBlock` vanishes at blocks with the wrong source. CoqQ: `lind_eq0l`
(`dirac.v:413-424`). -/
@[simp, dirac_simps]
theorem ofBlock_apply_of_ne_left (f : LinM D S T) (h : S' ≠ S) :
    (⌈f⌉ᴰ) S' T' = 0 :=
  dif_neg fun hc => h hc.1.symm

/-- `ofBlock` vanishes at blocks with the wrong target. CoqQ: `lind_eq0r`
(`dirac.v:413-424`). -/
@[simp, dirac_simps]
theorem ofBlock_apply_of_ne_right (f : LinM D S T) (h : T' ≠ T) :
    (⌈f⌉ᴰ) S' T' = 0 :=
  dif_neg fun hc => h hc.2.symm

/-- Cast absorption: `ofBlock` swallows `castF`. Key lemma for working with
blocks at propositionally equal label sets (CoqQ handles this via `castlf`
conversions on `lind`, cf. `dirac.v:224,364`). -/
@[simp, cast_simps, dirac_simps]
theorem ofBlock_castF (h₁ : S = S') (h₂ : T = T') (f : LinM D S T) :
    (⌈castF D h₁ h₂ f⌉ᴰ : Dirac D) = ⌈f⌉ᴰ := by
  subst h₁; subst h₂; simp

/-! ## D-3: linearity and injectivity of `ofBlock` (CoqQ `dirac.v:398-410`) -/

/-- CoqQ: `lind` is additive (`dirac.v:398-410`). -/
theorem ofBlock_add (f g : LinM D S T) :
    (⌈f + g⌉ᴰ : Dirac D) = ⌈f⌉ᴰ + ⌈g⌉ᴰ := by
  ext S₀ T₀
  rw [add_apply, ofBlock_apply, ofBlock_apply, ofBlock_apply]
  by_cases h : S = S₀ ∧ T = T₀
  · rw [dif_pos h, dif_pos h, dif_pos h, map_add]
  · rw [dif_neg h, dif_neg h, dif_neg h, add_zero]

/-- CoqQ: `lind` is ℂ-homogeneous (`dirac.v:398-410`). -/
theorem ofBlock_smul (c : ℂ) (f : LinM D S T) :
    (⌈c • f⌉ᴰ : Dirac D) = c • ⌈f⌉ᴰ := by
  ext S₀ T₀
  rw [smul_apply, ofBlock_apply, ofBlock_apply]
  by_cases h : S = S₀ ∧ T = T₀
  · rw [dif_pos h, dif_pos h, map_smul]
  · rw [dif_neg h, dif_neg h, smul_zero]

/-- CoqQ: `lind` preserves zero (`dirac.v:398-410`). -/
@[simp, dirac_simps]
theorem ofBlock_zero : (⌈(0 : LinM D S T)⌉ᴰ : Dirac D) = 0 := by
  ext S₀ T₀
  rw [zero_apply, ofBlock_apply]
  by_cases h : S = S₀ ∧ T = T₀
  · rw [dif_pos h, map_zero]
  · rw [dif_neg h]

/-- CoqQ: `lind` preserves negation (`dirac.v:398-410`). -/
theorem ofBlock_neg (f : LinM D S T) : (⌈-f⌉ᴰ : Dirac D) = -⌈f⌉ᴰ := by
  rw [← neg_one_smul ℂ f, ofBlock_smul, neg_one_smul]

/-- CoqQ: `lind` preserves subtraction (`dirac.v:398-410`). -/
theorem ofBlock_sub (f g : LinM D S T) : (⌈f - g⌉ᴰ : Dirac D) = ⌈f⌉ᴰ - ⌈g⌉ᴰ := by
  rw [sub_eq_add_neg, sub_eq_add_neg, ofBlock_add, ofBlock_neg]

/-- `ofBlock` is injective (from the round-trip `lindK`, CoqQ
`dirac.v:426`). -/
theorem ofBlock_injective :
    Function.Injective (ofBlock : LinM D S T → Dirac D) := fun f g h => by
  have := congrArg (fun d : Dirac D => d S T) h
  simpa only [ofBlock_apply_self] using this

/-! ## D-3: round-trips (CoqQ `lindK/ketdK/bradK/numdK`, `dirac.v:426-438`) -/

/-- CoqQ: `lindK` (`dirac.v:426`). -/
@[simp, dirac_simps]
theorem toLinM_ofBlock (f : LinM D S T) : toLinM S T (⌈f⌉ᴰ) = f :=
  ofBlock_apply_self f

/-- CoqQ: `ketdK` (`dirac.v:430`). -/
@[simp, dirac_simps]
theorem toKet_ket (v : HS D S) : toKet S (∣v⟩ᴰ) = v := by
  rw [toKet, ket, ofBlock_apply_self, ofKetM_toKetM]

/-- CoqQ: `bradK` (`dirac.v:434`). -/
@[simp, dirac_simps]
theorem toBra_bra (v : HS D S) : toBra S (⟨v∣ᴰ) = v := by
  rw [toBra, bra, ofBlock_apply_self, ofBraM_toBraM]

/-- CoqQ: `numdK` (`dirac.v:438`). -/
@[simp, dirac_simps]
theorem toScalar_num (c : ℂ) : toScalar (num D c) = c := by
  simp [toScalar, num]

/-- Unfolding lemma for `one` (its home block is the identity map). -/
theorem one_eq_ofBlock : (one D S : Dirac D) = ⌈(1 : EndM D S)⌉ᴰ := rfl

/-- `𝟙ᴰ S` evaluates to the identity at its home block. -/
@[simp, dirac_simps]
theorem one_apply_self : (one D S : Dirac D) S S = 1 :=
  ofBlock_apply_self _

/-! ## D-3: block decomposition (CoqQ `lind_dec`, `dirac.v:487`) -/

/-- Every Dirac expression is the sum of its blocks. CoqQ: `lind_dec`
(`dirac.v:487`). -/
theorem sum_ofBlock (d : Dirac D) :
    ∑ S : Finset L, ∑ T : Finset L, (⌈d S T⌉ᴰ : Dirac D) = d := by
  ext S₀ T₀
  simp only [sum_apply]
  rw [Fintype.sum_eq_single S₀, Fintype.sum_eq_single T₀, ofBlock_apply_self]
  · exact fun T hT => ofBlock_apply_of_ne_right _ hT.symm
  · exact fun S hS => Finset.sum_eq_zero fun T _ =>
      ofBlock_apply_of_ne_left _ hS.symm

/-! ## D-3: `ket`/`bra` (anti)linearity (CoqQ `dirac.v:443-482`) -/

/-- CoqQ: `ketd` is additive (`dirac.v:443-482`). -/
theorem ket_add (u v : HS D S) : (∣u + v⟩ᴰ : Dirac D) = ∣u⟩ᴰ + ∣v⟩ᴰ := by
  rw [ket, ket, ket, toKetM_add, ofBlock_add]

/-- CoqQ: `ketd` is ℂ-homogeneous (`dirac.v:443-482`). -/
theorem ket_smul (c : ℂ) (v : HS D S) :
    (∣c • v⟩ᴰ : Dirac D) = c • ∣v⟩ᴰ := by
  rw [ket, ket, toKetM_smul, ofBlock_smul]

/-- CoqQ: `ketd` preserves zero (`dirac.v:443-482`). -/
@[simp, dirac_simps]
theorem ket_zero : (∣(0 : HS D S)⟩ᴰ : Dirac D) = 0 := by
  rw [← zero_smul ℂ (0 : HS D S), ket_smul, zero_smul]

/-- `ket` is injective (from the round-trip `ketdK`, CoqQ `dirac.v:430`). -/
theorem ket_injective : Function.Injective (ket : HS D S → Dirac D) :=
  fun u v h => by
    have := congrArg (toKet S) h
    rwa [toKet_ket, toKet_ket] at this

/-- CoqQ: `brad` is additive (`dirac.v:443-482`). -/
theorem bra_add (u v : HS D S) : (⟨u + v∣ᴰ : Dirac D) = ⟨u∣ᴰ + ⟨v∣ᴰ := by
  rw [bra, bra, bra, toBraM_add, ofBlock_add]

/-- `bra` is conjugate-homogeneous (matching `toBraM_smul`).
CoqQ: `dirac.v:443-482`. -/
theorem bra_smul (c : ℂ) (v : HS D S) :
    (⟨c • v∣ᴰ : Dirac D) = star c • ⟨v∣ᴰ := by
  rw [bra, bra, toBraM_smul, ofBlock_smul]

/-- CoqQ: `brad` preserves zero (`dirac.v:443-482`). -/
@[simp, dirac_simps]
theorem bra_zero : (⟨(0 : HS D S)∣ᴰ : Dirac D) = 0 := by
  rw [← zero_smul ℂ (0 : HS D S), bra_smul, star_zero, zero_smul]

/-- `bra` is injective (from the round-trip `bradK`, CoqQ `dirac.v:434`). -/
theorem bra_injective : Function.Injective (bra : HS D S → Dirac D) :=
  fun u v h => by
    have := congrArg (toBra S) h
    rwa [toBra_bra, toBra_bra] at this

/-! ## D-3: `num` additivity (CoqQ `dirac.v:443-482`; multiplicativity is
`⊗ᴰ`-algebra material, deferred to M4b) -/

/-- CoqQ: `numd` is additive (`dirac.v:443-482`). -/
theorem num_add (a b : ℂ) : num D (a + b) = num D a + num D b := by
  rw [num, num, num, toScalarM_add, ofBlock_add]

/-- CoqQ: `numd` is ℂ-homogeneous (`dirac.v:443-482`). -/
theorem num_smul (c a : ℂ) : num D (c * a) = c • num D a := by
  rw [num, num, show toScalarM D (c * a) = c • toScalarM D a by
    simp [toScalarM_def, mul_smul], ofBlock_smul]

/-- CoqQ: `numd` preserves zero (`dirac.v:443-482`). -/
@[simp, dirac_simps]
theorem num_zero : num D 0 = 0 := by
  rw [num, toScalarM_zero, ofBlock_zero]

/-- `num` is injective (from the round-trip `numdK`, CoqQ `dirac.v:438`). -/
theorem num_injective : Function.Injective (num D) := fun a b h => by
  have := congrArg toScalar h
  rwa [toScalar_num, toScalar_num] at this

end Dirac

end Qhl
