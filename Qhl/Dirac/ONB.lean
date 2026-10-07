import Qhl.Dirac.Laws

/-!
# Orthonormal bases and normalized states at the Dirac level

Mirror of `CoqQ/src/dirac/dirac.v:2167-2310` (spec 03 §6, subgoal D-13).

* `Dirac.ONBD ι D S` — a family of labelled kets on `S`, pairwise orthonormal
  in the Dirac sense and of the right cardinality (CoqQ `onbd:2167-2230`)
* `Dirac.NSD D S` — a normalized labelled state (CoqQ `nsd`)
* transfer to/from mathlib's `OrthonormalBasis`
  (`ONBD.ofOrthonormalBasis`/`ONBD.toOrthonormalBasis`, CoqQ
  `onb2d`/`d2onb:2240-2250`); the canonical computational instance
  `ONBD.deltav` (CoqQ's `t2tv` ONB)
* resolution of the identity `ONBD.sum_ket_comp_adj` (CoqQ `sumonb_outerM:2256`)
* expansions of wf kets and wf operators in ONBs, `IsKetOn.onb_expansion`
  (CoqQ `onb_vecM:2266`) and `WFAt.onb_expansion` (CoqQ `onb_lfunM:2276`);
  both are stated with `•` for the coefficients — equivalent to CoqQ's
  `num ⊗ᴰ` form by `smul_eq_num_tensor`
* supporting canonical form for labelled scalars: `WFAt.eq_num`
  (`WFAt ∅ ∅ d → d = num D (toScalar d)`) with the layer-1 fact
  `eq_toScalarM` (`LinM D ∅ ∅` is one-dimensional)
-/

namespace Qhl

open scoped ComplexInnerProductSpace

namespace Dirac

/-- An orthonormal basis of labelled kets on `S`, at the Dirac level: each
member is a wf ket on `S`, the family is orthonormal in the Dirac sense, and
it has the cardinality of the computational basis. CoqQ: `onbd`
(`dirac.v:2167-2230`). -/
structure ONBD {L : Type*} [Fintype L] [DecidableEq L]
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (D : L → Type*) [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
    (S : Finset L) where
  /-- The family of labelled kets. -/
  ket : ι → Dirac D
  /-- Every member is a wf ket on `S`. -/
  isKetOn : ∀ i, IsKetOn S (ket i)
  /-- Dirac-level orthonormality (CoqQ `onbd` axiom). -/
  orthonormal : ∀ i j, (ket i)†ᴰ ∘ᴰ ket j = num D (if i = j then 1 else 0)
  /-- The family has the cardinality of the computational basis of `HS D S`. -/
  card_eq : Fintype.card ι = Fintype.card (QIdx D S)

/-- A normalized labelled state on `S`: a wf ket with `v†ᴰ ∘ᴰ v = 1`
(note `1 = num D 1`). CoqQ: `nsd` (`dirac.v:2167-2310`). -/
structure NSD {L : Type*} [Fintype L] [DecidableEq L]
    (D : L → Type*) [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
    (S : Finset L) where
  /-- The labelled state. -/
  ket : Dirac D
  /-- The state is a wf ket on `S`. -/
  isKetOn : IsKetOn S ket
  /-- Normalization: `⟨v|v⟩ = 1`. -/
  normalized : ket†ᴰ ∘ᴰ ket = 1

end Dirac

variable {L : Type*} [Fintype L] [DecidableEq L] {D : L → Type*}
  [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)] {S T : Finset L}
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-! ## Layer-1 support: `HS D ∅` and `LinM D ∅ ∅` are one-dimensional -/

/-- Every vector of the empty-register space is a multiple of the canonical
unit vector (`HS D ∅` is one-dimensional). -/
theorem eq_smul_deltav_default (w : HS D ∅) :
    w = w default • deltav D (default : QIdx D ∅) := by
  have h := dec_dv D w
  rwa [Fintype.sum_eq_single (default : QIdx D ∅)
    (fun k hk => absurd (Subsingleton.elim k default) hk), cdv_apply] at h

/-- Every `(∅, ∅)`-block map is a scalar map (`LinM D ∅ ∅` is
one-dimensional); the scalar is the one extracted by `Dirac.toScalar`. -/
theorem eq_toScalarM (f : LinM D ∅ ∅) :
    f = toScalarM D (emptyIso D (f (deltav D default))) := by
  refine linM_ext D fun k => ?_
  rw [Subsingleton.elim k default, toScalarM_apply, emptyIso_apply]
  exact eq_smul_deltav_default (f (deltav D default))

namespace Dirac

instance : CoeFun (ONBD ι D S) fun _ => ι → Dirac D := ⟨ONBD.ket⟩

/-! ## Scalar canonical form and scalar absorption -/

/-- `num` as a scalar multiple of the ring unit (= `Algebra.algebraMap_eq_smul_one`). -/
theorem num_eq_smul_one (c : ℂ) : num D c = c • (1 : Dirac D) := by
  rw [← algebraMap_eq_num, Algebra.algebraMap_eq_smul_one]

/-- Canonical form of a labelled scalar: a wf `(∅, ∅)` expression *is* a
`num`. Completes the canonical-form family `IsKetOn.eq_ket`/`IsBraOn.eq_bra`/
`IsSqOn.eq_ofBlock` (CoqQ `wfdiracE`-family, `dirac.v:1352-1360`). -/
theorem WFAt.eq_num {d : Dirac D} (h : WFAt ∅ ∅ d) : d = num D (toScalar d) := by
  conv_lhs => rw [← h.eq]
  exact congrArg ofBlock (eq_toScalarM (d ∅ ∅))

/-- Wf kets absorb scalars through `∘ᴰ` (CoqQ uses this inline in
`dirac.v:2266-2289`). -/
theorem comp_num_of_ket {d : Dirac D} (h : IsKetOn S d) (c : ℂ) :
    d ∘ᴰ num D c = c • d := by
  rw [num_eq_smul_one, comp_smul_right, ← one_empty, comp_one_of_wf h]

/-- Wf bras absorb scalars through `∘ᴰ` (mirror of `comp_num_of_ket`). -/
theorem num_comp_of_bra {d : Dirac D} (h : IsBraOn S d) (c : ℂ) :
    num D c ∘ᴰ d = c • d := by
  rw [num_eq_smul_one, comp_smul_left, ← one_empty, one_comp_of_wf h]

namespace ONBD

variable (Φ : ONBD ι D S)

/-! ## The underlying vectors and the transfer to `OrthonormalBasis`
(CoqQ `onb2d`/`d2onb`, `dirac.v:2240-2250`) -/

/-- The vector family underlying a Dirac-level ONB. -/
noncomputable def vec (i : ι) : HS D S := toKet S (Φ.ket i)

/-- Every member is the ket of its underlying vector. -/
theorem ket_eq (i : ι) : Φ.ket i = ∣Φ.vec i⟩ᴰ := (Φ.isKetOn i).eq_ket

/-- The underlying vectors are orthonormal in `HS D S`. -/
theorem orthonormal_vec : Orthonormal ℂ Φ.vec := by
  rw [orthonormal_iff_ite]
  intro i j
  apply num_injective (D := D)
  rw [← bra_comp_ket, ← adj_ket, ← Φ.ket_eq, ← Φ.ket_eq]
  exact Φ.orthonormal i j

/-- Repackage a mathlib `OrthonormalBasis` of `HS D S` as a Dirac-level ONB.
CoqQ: `onb2d` (`dirac.v:2240`). -/
noncomputable def ofOrthonormalBasis (b : OrthonormalBasis ι ℂ (HS D S)) :
    ONBD ι D S where
  ket i := ∣b i⟩ᴰ
  isKetOn i := wf_ket (b i)
  orthonormal i j := by
    rw [adj_ket, bra_comp_ket, orthonormal_iff_ite.mp b.orthonormal i j]
  card_eq := (Module.finrank_eq_card_basis b.toBasis).symm.trans
    finrank_euclideanSpace

@[simp]
theorem ofOrthonormalBasis_ket (b : OrthonormalBasis ι ℂ (HS D S)) (i : ι) :
    (ofOrthonormalBasis b).ket i = ∣b i⟩ᴰ := rfl

/-- Extract the mathlib `OrthonormalBasis` underlying a Dirac-level ONB
(orthonormality plus the cardinality field force spanning). CoqQ: `d2onb`
(`dirac.v:2245`). -/
noncomputable def toOrthonormalBasis : OrthonormalBasis ι ℂ (HS D S) :=
  OrthonormalBasis.mk Φ.orthonormal_vec
    (Φ.orthonormal_vec.linearIndependent.span_eq_top_of_card_eq_finrank'
      (Φ.card_eq.trans finrank_euclideanSpace.symm)).ge

@[simp]
theorem coe_toOrthonormalBasis : ⇑Φ.toOrthonormalBasis = Φ.vec :=
  OrthonormalBasis.coe_mk _ _

/-- The canonical computational ONB `{∣deltav k⟩ᴰ}` on `S` (CoqQ's `t2tv`
instance, `dirac.v:2230`-area). -/
noncomputable def deltav (D : L → Type*) [∀ i, Fintype (D i)]
    [∀ i, DecidableEq (D i)] (S : Finset L) : ONBD (QIdx D S) D S where
  ket k := ∣Qhl.deltav D k⟩ᴰ
  isKetOn k := wf_ket _
  orthonormal k l := by rw [adj_ket, bra_comp_ket, dv_dot]
  card_eq := rfl

@[simp]
theorem deltav_ket (k : QIdx D S) :
    (ONBD.deltav D S).ket k = ∣Qhl.deltav D k⟩ᴰ := rfl

/-! ## Resolution of the identity (CoqQ `sumonb_outerM`, `dirac.v:2256`) -/

/-- **D-13** resolution of the identity: `∑ i, ∣φᵢ⟩⟨φᵢ∣ = 𝟙ᴰ S`.
CoqQ: `sumonb_outerM` (`dirac.v:2256`). -/
theorem sum_ket_comp_adj : ∑ i, Φ.ket i ∘ᴰ (Φ.ket i)†ᴰ = one D S := by
  have h : ∑ i, outerLM (Φ.vec i) (Φ.vec i) = (1 : EndM D S) := by
    simpa using sum_outerLM_self Φ.toOrthonormalBasis
  calc ∑ i, Φ.ket i ∘ᴰ (Φ.ket i)†ᴰ
      = ∑ i, (⌈outerLM (Φ.vec i) (Φ.vec i)⌉ᴰ : Dirac D) :=
        Finset.sum_congr rfl fun i _ => by rw [Φ.ket_eq i, adj_ket, ket_comp_bra]
    _ = one D S := by rw [← ofBlock_sum, h, ← one_eq_ofBlock]

/-! ## Expansion coefficients (CoqQ `onb_vecM`'s scalars) -/

/-- The expansion coefficient of `d` along `Φ.ket i`, extracted at the Dirac
level: `⟨φᵢ| ∘ d` as a scalar. -/
noncomputable def coeff (i : ι) (d : Dirac D) : ℂ :=
  toScalar ((Φ.ket i)†ᴰ ∘ᴰ d)

theorem coeff_def (i : ι) (d : Dirac D) :
    Φ.coeff i d = toScalar ((Φ.ket i)†ᴰ ∘ᴰ d) := rfl

/-- On kets, `coeff` is the inner product against the underlying vector. -/
theorem coeff_ket (i : ι) (v : HS D S) : Φ.coeff i ∣v⟩ᴰ = ⟪Φ.vec i, v⟫ := by
  rw [coeff_def, Φ.ket_eq i, adj_ket, bra_comp_ket, toScalar_num]

end ONBD

/-! ## Expansions in an ONB (CoqQ `onb_vecM:2266`, `onb_lfunM:2276`)

Both are stated with `•` coefficients; CoqQ's `num ⊗ᴰ` form is equivalent by
`smul_eq_num_tensor`. -/

/-- **D-13** ket expansion: a wf ket is the sum of its ONB components.
CoqQ: `onb_vecM` (`dirac.v:2266`). -/
theorem IsKetOn.onb_expansion {d : Dirac D} (hd : IsKetOn S d)
    (Φ : ONBD ι D S) : d = ∑ i, Φ.coeff i d • Φ.ket i := by
  have key : ∀ i, Φ.coeff i d • Φ.ket i = Φ.ket i ∘ᴰ ((Φ.ket i)†ᴰ ∘ᴰ d) := fun i => by
    have hm : WFAt ∅ ∅ ((Φ.ket i)†ᴰ ∘ᴰ d) := ((Φ.isKetOn i).adj).comp hd
    rw [Φ.coeff_def, ← comp_num_of_ket (Φ.isKetOn i), ← hm.eq_num]
  calc d = (∑ i, Φ.ket i ∘ᴰ (Φ.ket i)†ᴰ) ∘ᴰ d := by
        rw [Φ.sum_ket_comp_adj, one_comp_of_wf hd]
    _ = ∑ i, Φ.ket i ∘ᴰ ((Φ.ket i)†ᴰ ∘ᴰ d) := by
        rw [comp_sum_left]
        exact Finset.sum_congr rfl fun i _ => comp_assoc _ _ _
    _ = ∑ i, Φ.coeff i d • Φ.ket i :=
        Finset.sum_congr rfl fun i _ => (key i).symm

/-- **D-13** operator expansion: a wf `(S, T)` operator is the double sum of
its matrix elements against ONBs of `S` and `T`. CoqQ: `onb_lfunM`
(`dirac.v:2276`). -/
theorem WFAt.onb_expansion {d : Dirac D} (hd : WFAt S T d)
    (Φ : ONBD ι D S) (Ψ : ONBD κ D T) :
    d = ∑ i, ∑ j, toScalar ((Ψ.ket j)†ᴰ ∘ᴰ d ∘ᴰ Φ.ket i) •
      (Ψ.ket j ∘ᴰ (Φ.ket i)†ᴰ) := by
  have key : ∀ (i : ι) (j : κ),
      toScalar ((Ψ.ket j)†ᴰ ∘ᴰ d ∘ᴰ Φ.ket i) • (Ψ.ket j ∘ᴰ (Φ.ket i)†ᴰ)
        = (Ψ.ket j ∘ᴰ (Ψ.ket j)†ᴰ) ∘ᴰ (d ∘ᴰ (Φ.ket i ∘ᴰ (Φ.ket i)†ᴰ)) := by
    intro i j
    have hm : WFAt ∅ ∅ ((Ψ.ket j)†ᴰ ∘ᴰ d ∘ᴰ Φ.ket i) :=
      ((Ψ.isKetOn j).adj).comp (hd.comp (Φ.isKetOn i))
    calc toScalar ((Ψ.ket j)†ᴰ ∘ᴰ d ∘ᴰ Φ.ket i) • (Ψ.ket j ∘ᴰ (Φ.ket i)†ᴰ)
        = Ψ.ket j ∘ᴰ (num D (toScalar ((Ψ.ket j)†ᴰ ∘ᴰ d ∘ᴰ Φ.ket i)) ∘ᴰ
            (Φ.ket i)†ᴰ) := by
          rw [num_comp_of_bra ((Φ.isKetOn i).adj), comp_smul_right]
      _ = Ψ.ket j ∘ᴰ (((Ψ.ket j)†ᴰ ∘ᴰ d ∘ᴰ Φ.ket i) ∘ᴰ (Φ.ket i)†ᴰ) := by
          rw [← hm.eq_num]
      _ = (Ψ.ket j ∘ᴰ (Ψ.ket j)†ᴰ) ∘ᴰ (d ∘ᴰ (Φ.ket i ∘ᴰ (Φ.ket i)†ᴰ)) := by
          simp only [comp_assoc]
  calc d = (∑ j, Ψ.ket j ∘ᴰ (Ψ.ket j)†ᴰ) ∘ᴰ
        (d ∘ᴰ ∑ i, Φ.ket i ∘ᴰ (Φ.ket i)†ᴰ) := by
        rw [Φ.sum_ket_comp_adj, Ψ.sum_ket_comp_adj, comp_one_of_wf hd,
          one_comp_of_wf hd]
    _ = ∑ j, ∑ i, (Ψ.ket j ∘ᴰ (Ψ.ket j)†ᴰ) ∘ᴰ
        (d ∘ᴰ (Φ.ket i ∘ᴰ (Φ.ket i)†ᴰ)) := by
        rw [comp_sum_left]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [comp_sum_right, comp_sum_right]
    _ = ∑ i, ∑ j, (Ψ.ket j ∘ᴰ (Ψ.ket j)†ᴰ) ∘ᴰ
        (d ∘ᴰ (Φ.ket i ∘ᴰ (Φ.ket i)†ᴰ)) := Finset.sum_comm
    _ = ∑ i, ∑ j, toScalar ((Ψ.ket j)†ᴰ ∘ᴰ d ∘ᴰ Φ.ket i) •
        (Ψ.ket j ∘ᴰ (Φ.ket i)†ᴰ) :=
        Finset.sum_congr rfl fun i _ =>
          Finset.sum_congr rfl fun j _ => (key i j).symm

/-! ## Normalized states (CoqQ `nsd`) -/

namespace NSD

variable (Ψ : NSD D S)

/-- The underlying vector of a normalized state. -/
noncomputable def vec : HS D S := toKet S Ψ.ket

theorem ket_eq : Ψ.ket = ∣Ψ.vec⟩ᴰ := Ψ.isKetOn.eq_ket

/-- The underlying vector has unit inner product with itself. -/
theorem inner_vec_self : ⟪Ψ.vec, Ψ.vec⟫ = 1 := by
  apply num_injective (D := D)
  rw [← bra_comp_ket, ← adj_ket, ← Ψ.ket_eq, Ψ.normalized, num_one]

end NSD

end Dirac

end Qhl
