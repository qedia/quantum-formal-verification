import Qhl.HSpace.TenF

/-!
# Labelled Hilbert spaces: general composition

Mirror of the general-composition layer of `CoqQ/src/dirac/hstensor.v` (spec 02
§6, subgoal H-18, milestone M3).

* `dotf D f g` — general composition (CoqQ `dot_lfun`, `hstensor.v:1339`):
  `(f ⊗ᶠ 1) ∘ₗ castF D _ _ (g ⊗ᶠ 1)`, the identity legs filling the mismatch
  `T' \ S` resp. `S \ T'`
* `sdotf D f g : EndM D (S ∪ T)` — the square case (CoqQ `sdot_lfun`,
  `hstensor.v:1345`)
* bilinearity; `adjoint_dotf`/`conjLM_dotf`/`transposeLM_dotf` (CoqQ
  `dotf_adj:1618`, `dotf_conj:1614`, `dotf_tr:1625`) — all cast-free and
  unconditional
* degeneracies: `dotf_comp` (composable case `T' = S`, CoqQ `dotdf_comp`,
  `dirac.v:1777`-area) and `dotf_ten` (`Disjoint S T'`, CoqQ `dotdf_ten`,
  `dirac.v:1741`-area)
* conditional associativity `dotf_assoc` (CoqQ `dotFA_cond`,
  `hstensor.v:2567`), exactly the two disjointness side conditions of the
  Dirac-level `dotdA_cond` (spec 03, D-L4)
* `sdotf` suite: `sdotf_one_one`, `∅`-unit laws, `adjoint_sdotf`,
  `sdotf_ten`

The cast-plumbing helpers (`castF_castF`, `castF_tenf`, `tenf_one_congr`,
`castF_tenf_one_union`, `tenf_comp_one`, `tenf_cast_one_right`) live here
because casts of `tenf` first arise in this file. Following the file
conventions, every cast-carrying statement takes *arbitrary proofs* of the
label-set equalities, so by proof irrelevance it applies to any such cast.
-/

namespace Qhl

open Finset

variable {L : Type*} [DecidableEq L]
variable (D : L → Type*) [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable {S T U W W₁ W₂ S' T' S₁ S₂ S₃ T₁ T₂ T₃ : Finset L}

/-! ## Cast plumbing -/

/-- Consecutive operator casts collapse (definitionally). -/
@[simp, cast_simps]
theorem castF_castF {S'' T'' : Finset L} (h₁ : S = S') (h₂ : S' = S'') (h₃ : T = T')
    (h₄ : T' = T'') (f : LinM D S T) :
    castF D h₂ h₄ (castF D h₁ h₃ f) = castF D (h₁.trans h₂) (h₃.trans h₄) f := rfl

/-- `castF` commutes with basis conjugation. CoqQ `castlf_conj` (`hstensor.v:428`). -/
@[simp, cast_simps]
theorem castF_conj (h₁ : S = S') (h₂ : T = T') (f : LinM D S T) :
    conjLM (castF D h₁ h₂ f) = castF D h₁ h₂ (conjLM f) := by
  subst h₁; subst h₂; simp

/-- A cast of an operator tensor is the tensor of the casts. CoqQ `castlf_ten`. -/
theorem castF_tenf (e₁ : S₁ = S') (e₂ : T₁ = T') (e₃ : S₂ = U) (e₄ : T₂ = W)
    (h₁ : S₁ ∪ S₂ = S' ∪ U) (h₂ : T₁ ∪ T₂ = T' ∪ W)
    (f : LinM D S₁ T₁) (g : LinM D S₂ T₂) :
    castF D h₁ h₂ (tenf D f g) = tenf D (castF D e₁ e₂ f) (castF D e₃ e₄ g) := by
  subst e₁; subst e₂; subst e₃; subst e₄; simp

/-- Recasting only the identity leg of a tensor. -/
theorem tenf_one_congr (e : W₁ = W₂) (h₁ : S ∪ W₁ = S ∪ W₂) (h₂ : T ∪ W₁ = T ∪ W₂)
    (f : LinM D S T) :
    castF D h₁ h₂ (tenf D f (1 : EndM D W₁)) = tenf D f (1 : EndM D W₂) := by
  subst e; simp

/-- Splitting the identity leg of a tensor along a union (`tenf_castA` +
`tenf_one_one`). -/
theorem castF_tenf_one_union (h₁ : S ∪ (W₁ ∪ W₂) = (S ∪ W₁) ∪ W₂)
    (h₂ : T ∪ (W₁ ∪ W₂) = (T ∪ W₁) ∪ W₂) (f : LinM D S T) :
    castF D h₁ h₂ (tenf D f (1 : EndM D (W₁ ∪ W₂))) =
      tenf D (tenf D f (1 : EndM D W₁)) (1 : EndM D W₂) := by
  rw [← tenf_one_one, tenf_castA]

/-- Composing with the identity operator (definitionally). -/
theorem one_comp (f : LinM D S T) : (1 : EndM D T) ∘ₗ f = f :=
  LinearMap.ext fun _ => rfl

/-- Composing with the identity operator (definitionally). -/
theorem comp_one (f : LinM D S T) : f ∘ₗ (1 : EndM D S) = f :=
  LinearMap.ext fun _ => rfl

/-- The interchange law with a common identity leg. CoqQ `tenf_comp1r`
(`hstensor.v:1861`). -/
theorem tenf_comp_one (hd : Disjoint T W) (f : LinM D T U) (g : LinM D S T) :
    tenf D (f ∘ₗ g) (1 : EndM D W) =
      tenf D f (1 : EndM D W) ∘ₗ tenf D g (1 : EndM D W) := by
  have h := tenf_comp D hd f (1 : EndM D W) g (1 : EndM D W)
  rwa [one_comp] at h

/-- Absorbing an identity leg on a set equal to `∅` (generalizes
`tenf_cast1r`, whose `∅` is syntactic). -/
theorem tenf_cast_one_right (hW : W = ∅) (h₁ : S ∪ W = S) (h₂ : T ∪ W = T)
    (f : LinM D S T) :
    castF D h₁ h₂ (tenf D f (1 : EndM D W)) = f := by
  subst hW; exact tenf_cast1r D h₁ h₂ f

/-- The canonical-basis conjugation fixes the identity operator. -/
@[simp]
theorem conjLM_one : conjLM (1 : EndM D W) = 1 :=
  LinearMap.ext fun u => conjV_conjV u

/-! ## The general composition (CoqQ `dot_lfun`, `hstensor.v:1339`) -/

/-- General composition of labelled operators: `g`'s output on `T'` is fed into
`f`'s input on `S` wherever they overlap; the mismatches `T' \ S` and `S \ T'`
are passed through by identity legs. CoqQ `dot_lfun` (`hstensor.v:1339`). -/
noncomputable def dotf (f : LinM D S T) (g : LinM D S' T') :
    LinM D (S' ∪ (S \ T')) (T ∪ (T' \ S)) :=
  tenf D f (1 : EndM D (T' \ S)) ∘ₗ
    castF D rfl union_sdiff_symm (tenf D g (1 : EndM D (S \ T')))

/-- Square case of `dotf`, recast to `EndM D (S ∪ T)`. CoqQ `sdot_lfun`
(`hstensor.v:1345`). -/
noncomputable def sdotf (f : EndM D S) (g : EndM D T) : EndM D (S ∪ T) :=
  castF D (union_sdiff_self_eq_union.trans (union_comm T S)) union_sdiff_self_eq_union
    (dotf D f g)

/-! ## H-18: bilinearity (CoqQ bilinear instances, `hstensor.v:1598-1612`) -/

theorem dotf_add_left (f₁ f₂ : LinM D S T) (g : LinM D S' T') :
    dotf D (f₁ + f₂) g = dotf D f₁ g + dotf D f₂ g := by
  simp only [dotf, tenf_add_left, LinearMap.add_comp]

theorem dotf_add_right (f : LinM D S T) (g₁ g₂ : LinM D S' T') :
    dotf D f (g₁ + g₂) = dotf D f g₁ + dotf D f g₂ := by
  simp only [dotf, tenf_add_left, map_add, LinearMap.comp_add]

theorem dotf_smul_left (c : ℂ) (f : LinM D S T) (g : LinM D S' T') :
    dotf D (c • f) g = c • dotf D f g := by
  simp only [dotf, tenf_smul_left, LinearMap.smul_comp]

theorem dotf_smul_right (c : ℂ) (f : LinM D S T) (g : LinM D S' T') :
    dotf D f (c • g) = c • dotf D f g := by
  simp only [dotf, tenf_smul_left, map_smul, LinearMap.comp_smul]

@[simp]
theorem dotf_zero_left (g : LinM D S' T') : dotf D (0 : LinM D S T) g = 0 := by
  simp only [dotf, tenf_zero_left, LinearMap.zero_comp]

@[simp]
theorem dotf_zero_right (f : LinM D S T) : dotf D f (0 : LinM D S' T') = 0 := by
  simp only [dotf, tenf_zero_left, map_zero, LinearMap.comp_zero]

/-! ## H-18: adjoint, conjugation, transpose — cast-free and unconditional

The index sets of `(dotf D f g)†` and `dotf D g† f†` coincide *syntactically*,
so unlike CoqQ (which juggles `castlf`) no cast appears. -/

/-- CoqQ `dotf_adj` (`hstensor.v:1618`): `(f ·ᶠ g)† = g† ·ᶠ f†`. -/
@[simp]
theorem adjoint_dotf (f : LinM D S T) (g : LinM D S' T') :
    LinearMap.adjoint (dotf D f g) =
      dotf D (LinearMap.adjoint g) (LinearMap.adjoint f) := by
  simp only [dotf, LinearMap.adjoint_comp, castF_adj, adjoint_tenf,
    LinearMap.adjoint_one]
  exact LinearMap.ext fun _ => rfl

/-- CoqQ `dotf_conj` (`hstensor.v:1614`). -/
@[simp]
theorem conjLM_dotf (f : LinM D S T) (g : LinM D S' T') :
    conjLM (dotf D f g) = dotf D (conjLM f) (conjLM g) := by
  simp only [dotf, conjLM_comp, castF_conj, conjLM_tenf, conjLM_one]

/-- CoqQ `dotf_tr` (`hstensor.v:1625`): `(f ·ᶠ g)ᵀ = gᵀ ·ᶠ fᵀ`. -/
@[simp]
theorem transposeLM_dotf (f : LinM D S T) (g : LinM D S' T') :
    transposeLM (dotf D f g) = dotf D (transposeLM g) (transposeLM f) := by
  rw [← adjoint_conjLM, conjLM_dotf, adjoint_dotf, adjoint_conjLM, adjoint_conjLM]

/-! ## H-18: degeneracies

CoqQ states these at the `Fnd`/Dirac level (`dotdf_comp`, `dotdf_ten`,
`dirac.v`); here they are the concrete cast-carrying statements that the Dirac
layer's `dotd_mul` (D-L2) and `dotd_ten` (D-L1) will consume. Side conditions
match CoqQ exactly: none for the composable case (typing enforces `T' = S`),
`Disjoint S T'` for the tensor case. -/

/-- Degeneracy 1 (composable case): when `g` lands exactly on `f`'s domain,
`dotf` is plain composition, up to the cast absorbing `S \ S`. Bridge to
`dotd_mul` (spec 03, D-L2); CoqQ `dotdf_comp` (`dirac.v:1775`). -/
theorem dotf_comp (h₁ : W = W ∪ (S \ S)) (h₂ : T = T ∪ (S \ S))
    (f : LinM D S T) (g : LinM D W S) :
    dotf D f g = castF D h₁ h₂ (f ∘ₗ g) := by
  rw [dotf, castF_rfl, LinearEquiv.refl_apply, ← tenf_comp_one D disjoint_sdiff f g]
  nth_rewrite 2 [← tenf_cast_one_right D (Finset.sdiff_self S) h₁.symm h₂.symm (f ∘ₗ g)]
  rw [castF_castF, castF_rfl, LinearEquiv.refl_apply]

/-- Degeneracy 2 (disjoint case): when `f`'s input and `g`'s output cannot
interact, `dotf` is the operator tensor, up to cast. Bridge to `dotd_ten`
(spec 03, D-L1); CoqQ `dotdf_ten` (`dirac.v:1741`). -/
theorem dotf_ten (hd : Disjoint S T') (h₁ : S ∪ S' = S' ∪ (S \ T'))
    (h₂ : T ∪ T' = T ∪ (T' \ S)) (f : LinM D S T) (g : LinM D S' T') :
    dotf D f g = castF D h₁ h₂ (tenf D f g) := by
  have e₁ : T' \ S = T' := sdiff_eq_self_of_disjoint hd.symm
  have e₂ : S \ T' = S := sdiff_eq_self_of_disjoint hd
  have hm : S ∪ T' = S ∪ (T' \ S) := by rw [e₁]
  have key : tenf D f g = tenf D f (1 : EndM D T') ∘ₗ tenf D (1 : EndM D S) g := by
    have h := tenf_comp D hd f (1 : EndM D T') (1 : EndM D S) g
    rwa [comp_one, one_comp] at h
  rw [key, castF_comp D h₁ hm h₂, tenf_one_congr D e₁.symm hm h₂ f, dotf,
    ← tenf_castC D (union_comm S' S) (union_comm T' S) g (1 : EndM D S),
    ← tenf_one_congr D e₂ (by rw [e₂]) (by rw [e₂]) g, castF_castF, castF_castF]

/-! ## H-18: conditional associativity (CoqQ `dotFA_cond`, `hstensor.v:2567`)

This is the full generality the Dirac layer needs for `dotdA_cond` (spec 03,
D-L4): the two disjointness conditions are verbatim CoqQ's
`[disjoint tdom x2 & tdom x1 :\: tcdom x2]` and
`[disjoint tcdom x2 & tcdom x3 :\: tdom x2]`. The square-middle form `dotdA`
(`f₂ : EndM D S₂`) follows by instantiating both conditions with
`Finset.disjoint_sdiff`. CoqQ proves this at the cast-quotient `Fnd` level;
here the label-set identities `h₁`/`h₂` (which hold *because of* `P1`/`P2`)
are taken as hypotheses, per the file convention. -/

set_option maxRecDepth 8192 in
/-- Associativity of `dotf` under CoqQ's two disjointness side conditions. -/
theorem dotf_assoc (P1 : Disjoint S₂ (S₁ \ T₂)) (P2 : Disjoint T₂ (T₃ \ S₂))
    (h₁ : (S₃ ∪ S₂ \ T₃) ∪ S₁ \ (T₂ ∪ T₃ \ S₂) = S₃ ∪ (S₂ ∪ S₁ \ T₂) \ T₃)
    (h₂ : T₁ ∪ (T₂ ∪ T₃ \ S₂) \ S₁ = (T₁ ∪ T₂ \ S₁) ∪ T₃ \ (S₂ ∪ S₁ \ T₂))
    (f₁ : LinM D S₁ T₁) (f₂ : LinM D S₂ T₂) (f₃ : LinM D S₃ T₃) :
    castF D h₁ h₂ (dotf D f₁ (dotf D f₂ f₃)) = dotf D (dotf D f₁ f₂) f₃ := by
  have p1 := Finset.disjoint_left.1 P1
  have p2 := Finset.disjoint_left.1 P2
  -- the two interchange (`tenf_comp_one`) side conditions
  have disjL : Disjoint (S₂ ∪ T₃ \ S₂) (S₁ \ (T₂ ∪ T₃ \ S₂)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    have := @p1 x
    simp only [mem_union, mem_sdiff] at hx hx' this
    tauto
  have disjR : Disjoint (S₁ ∪ T₂ \ S₁) (T₃ \ (S₂ ∪ S₁ \ T₂)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    have := @p2 x
    simp only [mem_union, mem_sdiff] at hx hx' this
    tauto
  -- the three identity legs agree, under the side conditions
  have eX₁ : (T₂ ∪ T₃ \ S₂) \ S₁ = T₂ \ S₁ ∪ T₃ \ (S₂ ∪ S₁ \ T₂) := by
    ext x
    have := @p2 x
    simp only [mem_union, mem_sdiff] at this ⊢
    tauto
  have eX₂ : T₃ \ S₂ ∪ S₁ \ (T₂ ∪ T₃ \ S₂) = S₁ \ T₂ ∪ T₃ \ (S₂ ∪ S₁ \ T₂) := by
    ext x
    simp only [mem_union, mem_sdiff]
    tauto
  have eX₃ : S₂ \ T₃ ∪ S₁ \ (T₂ ∪ T₃ \ S₂) = (S₂ ∪ S₁ \ T₂) \ T₃ := by
    ext x
    have := @p1 x
    simp only [mem_union, mem_sdiff] at this ⊢
    tauto
  -- pull the inner casts of the nested `dotf`s out of their `⊗ 1` legs
  have mL : (T₃ ∪ S₂ \ T₃) ∪ S₁ \ (T₂ ∪ T₃ \ S₂) =
      (S₂ ∪ T₃ \ S₂) ∪ S₁ \ (T₂ ∪ T₃ \ S₂) := by rw [union_sdiff_symm]
  have mR : (T₂ ∪ S₁ \ T₂) ∪ T₃ \ (S₂ ∪ S₁ \ T₂) =
      (S₁ ∪ T₂ \ S₁) ∪ T₃ \ (S₂ ∪ S₁ \ T₂) := by rw [union_sdiff_symm]
  have pullL : tenf D (castF D rfl union_sdiff_symm (tenf D f₃ (1 : EndM D (S₂ \ T₃))))
        (1 : EndM D (S₁ \ (T₂ ∪ T₃ \ S₂))) =
      castF D rfl mL (tenf D (tenf D f₃ (1 : EndM D (S₂ \ T₃)))
        (1 : EndM D (S₁ \ (T₂ ∪ T₃ \ S₂)))) := by
    rw [castF_tenf D rfl union_sdiff_symm rfl rfl rfl mL, castF_rfl,
      LinearEquiv.refl_apply]
  have pullR : tenf D (castF D rfl union_sdiff_symm (tenf D f₂ (1 : EndM D (S₁ \ T₂))))
        (1 : EndM D (T₃ \ (S₂ ∪ S₁ \ T₂))) =
      castF D rfl mR (tenf D (tenf D f₂ (1 : EndM D (S₁ \ T₂)))
        (1 : EndM D (T₃ \ (S₂ ∪ S₁ \ T₂)))) := by
    rw [castF_tenf D rfl union_sdiff_symm rfl rfl rfl mR, castF_rfl,
      LinearEquiv.refl_apply]
  -- normalize both sides to `f₁ ∘ f₂ ∘ f₃` with cast-wrapped common legs;
  -- all remaining cast plumbing is definitional
  simp only [dotf]
  rw [tenf_comp_one D disjL (tenf D f₂ (1 : EndM D (T₃ \ S₂)))
      (castF D rfl union_sdiff_symm (tenf D f₃ (1 : EndM D (S₂ \ T₃)))),
    tenf_comp_one D disjR (tenf D f₁ (1 : EndM D (T₂ \ S₁)))
      (castF D rfl union_sdiff_symm (tenf D f₂ (1 : EndM D (S₁ \ T₂)))),
    pullL, pullR,
    ← castF_tenf_one_union D
      (union_assoc S₂ (T₃ \ S₂) (S₁ \ (T₂ ∪ T₃ \ S₂))).symm
      (union_assoc T₂ (T₃ \ S₂) (S₁ \ (T₂ ∪ T₃ \ S₂))).symm f₂,
    ← castF_tenf_one_union D
      (union_assoc S₃ (S₂ \ T₃) (S₁ \ (T₂ ∪ T₃ \ S₂))).symm
      (union_assoc T₃ (S₂ \ T₃) (S₁ \ (T₂ ∪ T₃ \ S₂))).symm f₃,
    ← castF_tenf_one_union D
      (union_assoc S₁ (T₂ \ S₁) (T₃ \ (S₂ ∪ S₁ \ T₂))).symm
      (union_assoc T₁ (T₂ \ S₁) (T₃ \ (S₂ ∪ S₁ \ T₂))).symm f₁,
    ← castF_tenf_one_union D
      (union_assoc S₂ (S₁ \ T₂) (T₃ \ (S₂ ∪ S₁ \ T₂))).symm
      (union_assoc T₂ (S₁ \ T₂) (T₃ \ (S₂ ∪ S₁ \ T₂))).symm f₂,
    ← tenf_one_congr D eX₁ (by rw [eX₁]) (by rw [eX₁]) f₁,
    ← tenf_one_congr D eX₂ (by rw [eX₂]) (by rw [eX₂]) f₂,
    ← tenf_one_congr D eX₃ (by rw [eX₃]) (by rw [eX₃]) f₃]
  exact LinearMap.ext fun _ => rfl

/-! ## H-18: the `sdotf` suite -/

/-- CoqQ `sdotf11` (`hstensor.v:1938`). -/
@[simp]
theorem sdotf_one_one : sdotf D (1 : EndM D S) (1 : EndM D T) = 1 := by
  rw [sdotf, dotf, tenf_one_one, tenf_one_one, one_comp, castF_castF]
  exact castF_one D _

/-- `∅`-register right unit, up to cast. CoqQ `sdotF1` (`hstensor.v:2650`-area). -/
theorem sdotf_one_right (h : S ∪ ∅ = S) (f : EndM D S) :
    castF D h h (sdotf D f (1 : EndM D ∅)) = f := by
  rw [sdotf, dotf_ten D (disjoint_empty_right S) (by simp) (by simp),
    castF_castF, castF_castF]
  exact tenf_cast_one_right D rfl _ _ f

/-- `∅`-register left unit, up to cast. CoqQ `sdot1F` (`hstensor.v:2650`-area). -/
theorem sdotf_one_left (h : ∅ ∪ T = T) (g : EndM D T) :
    castF D h h (sdotf D (1 : EndM D ∅) g) = g := by
  rw [sdotf, dotf_ten D (disjoint_empty_left T) (by simp) (by simp), castF_castF,
    castF_castF,
    ← tenf_castC D (union_comm T ∅) (union_comm T ∅) g (1 : EndM D ∅), castF_castF]
  exact tenf_cast_one_right D rfl _ _ g

/-- Adjoint of `sdotf`: the factors swap, up to the `union_comm` cast. Bridge
to `adjdG` (spec 03, D-7). -/
theorem adjoint_sdotf (h : T ∪ S = S ∪ T) (f : EndM D S) (g : EndM D T) :
    LinearMap.adjoint (sdotf D f g) =
      castF D h h (sdotf D (LinearMap.adjoint g) (LinearMap.adjoint f)) := by
  rw [sdotf, castF_adj, adjoint_dotf, sdotf, castF_castF]

/-- On disjoint registers `sdotf` *is* the operator tensor — cast-free, since
the index sets agree syntactically. CoqQ `sdotFT` (`hstensor.v:2641`). -/
theorem sdotf_ten (hd : Disjoint S T) (f : EndM D S) (g : EndM D T) :
    sdotf D f g = tenf D f g := by
  rw [sdotf,
    dotf_ten D hd (by rw [sdiff_eq_self_of_disjoint hd, union_comm])
      (by rw [sdiff_eq_self_of_disjoint hd.symm]),
    castF_castF, castF_rfl, LinearEquiv.refl_apply]

end Qhl
