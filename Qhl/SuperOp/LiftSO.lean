import Qhl.SuperOp.Tenso

/-!
# Super-operators: cylindrical extension and the frame lemmas

Spec 04 §2, milestone M6 phase 3 (item Q-9), on top of `Qhl/SuperOp/Tenso.lean`
and the operator-level extension `liftF` of `Qhl/HSpace/LiftF.lean`.

* `liftSO D h E` — Q-9, CoqQ `liftso` (`hstensor.v:3393`): extension of a
  super-operator on `S` by the identity super-operator on `T \ S`
* `liftSO_kraussoOf` / `liftSO_formsoOf` — CoqQ `liftso_krausso`/`liftso_formso`
  (`hstensor.v:3483,3489`); the latter bridges to the operator-level `liftF`
* closure: `IsCP.liftSO` / `IsQO.liftSO` / `IsQC.liftSO` — CoqQ
  `liftso_cp/tn/tp` (`hstensor.v:3493-3507`), all hypothesis-free
* **the frame lemmas (M6 acceptance)**: `liftSO_liftF_compl`/`compr` — CoqQ
  `liftfsoEf_compl`/`liftfsoEf_compr` (`hstensor.v:4269,4288`), stated at an
  arbitrary ambient register `W ⊇ S, T` (CoqQ states them only for the full
  space `[set: L]`, which needs `L` finite); the literal CoqQ forms are
  recovered in the `[Fintype L]` section as `liftSO_top_compl`/`compr`, via
  `liftF_top`/`liftSO_top` (CoqQ `liftf_lf`/`liftfso`, `hstensor.v:4058-4059`)

The `[Fintype L]` section is isolated at the end of the file, mirroring how
`Qhl/HSpace/LiftF.lean` isolates its `Nonempty` section.
-/

namespace Qhl

open Finset
open scoped ComplexInnerProductSpace ComplexOrder

variable {L : Type*} [DecidableEq L]
variable (D : L → Type*) [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable {S T W : Finset L}
variable {κ : Type*} [Fintype κ]

/-! ## Local helpers -/

private theorem liftF_sum {ι : Type*} (h : S ⊆ T) (s : Finset ι)
    (f : ι → EndM D S) : liftF D h (∑ i ∈ s, f i) = ∑ i ∈ s, liftF D h (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp only [Finset.sum_empty, liftF_zero]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, liftF_add, ih]

/-- Conjugating a Kraus map by an operator cast is the Kraus map of the cast
family (the applied form of CoqQ `castso_krausso`, `hstensor.v:3320`). -/
private theorem castF_conj_kraussoOf {A B : Finset L} (e : A = B)
    (g : κ → EndM D A) (x : EndM D B) :
    castF D e e (kraussoOf D g (castF D e.symm e.symm x))
      = kraussoOf D (fun i => castF D e e (g i)) x := by
  rw [kraussoOf_apply, kraussoOf_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [castF_comp D e e e, castF_comp D e e e, castF_castF, castF_rfl,
    LinearEquiv.refl_apply, ← castF_adj]

/-! ## Q-9: the cylindrical extension of super-operators -/

/-- Cylindrical extension of a super-operator on a subregister: tensor with
the identity super-operator on `T \ S` and conjugate by the cast along
`S ∪ (T \ S) = T`. CoqQ `liftso` (`hstensor.v:3393`). -/
noncomputable def liftSO (h : S ⊆ T) (E : SuperOp D S S) : SuperOp D T T :=
  (castF D (union_sdiff_of_subset h) (union_sdiff_of_subset h)).toLinearMap
    ∘ₗ tenso D E (LinearMap.id : SuperOp D (T \ S) (T \ S))
    ∘ₗ (castF D (union_sdiff_of_subset h).symm
        (union_sdiff_of_subset h).symm).toLinearMap

theorem liftSO_apply (h : S ⊆ T) (E : SuperOp D S S) (x : EndM D T) :
    liftSO D h E x
      = castF D (union_sdiff_of_subset h) (union_sdiff_of_subset h)
          (tenso D E (LinearMap.id : SuperOp D (T \ S) (T \ S))
            (castF D (union_sdiff_of_subset h).symm
              (union_sdiff_of_subset h).symm x)) := rfl

/-- CoqQ `liftso_krausso` (`hstensor.v:3483`): the extension of a Kraus map is
the Kraus map of the `liftF`-extended family. -/
theorem liftSO_kraussoOf (h : S ⊆ T) (f : κ → EndM D S) :
    liftSO D h (kraussoOf D f) = kraussoOf D fun i => liftF D h (f i) := by
  have hten : tenso D (kraussoOf D f) (LinearMap.id : SuperOp D (T \ S) (T \ S))
      = kraussoOf D fun p : κ × Unit => tenf D (f p.1) (1 : EndM D (T \ S)) := by
    rw [← formsoOf_one D (S := T \ S), formsoOf_eq_kraussoOf, tenso_kraussoOf]
  refine LinearMap.ext fun x => ?_
  rw [liftSO_apply, hten, castF_conj_kraussoOf, kraussoOf_apply, kraussoOf_apply,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_unique]
  rfl

/-- CoqQ `liftso_formso` (`hstensor.v:3489`): the bridge to the operator-level
extension — lifting a form super-operator is the form super-operator of the
lifted operator. -/
theorem liftSO_formsoOf (h : S ⊆ T) (f : EndM D S) :
    liftSO D h (formsoOf D f) = formsoOf D (liftF D h f) := by
  rw [formsoOf_eq_kraussoOf, liftSO_kraussoOf, formsoOf_eq_kraussoOf]

/-- The extension of the identity super-operator is the identity (the `idso`
unit law of CoqQ `liftso`). -/
theorem liftSO_id (h : S ⊆ T) :
    liftSO D h (LinearMap.id : SuperOp D S S) = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  rw [liftSO_apply, tenso_id_id]
  simp only [LinearMap.id_apply, castF_castF, castF_rfl, LinearEquiv.refl_apply]

/-! ## Q-9 closure: CP/QO/QC are preserved (CoqQ `hstensor.v:3493-3507`) -/

/-- CoqQ `liftso_cp` (`hstensor.v:3493`): the extension of a CP map is CP. -/
theorem IsCP.liftSO (h : S ⊆ T) {E : SuperOp D S S} (hE : IsCP D E) :
    IsCP D (liftSO D h E) := by
  obtain ⟨f, rfl⟩ := hE.exists_kraus
  rw [liftSO_kraussoOf]
  exact isCP_kraussoOf D _

/-- CoqQ `liftso_tp` (`hstensor.v:3503`): the extension of a channel is a
channel — the completeness relation lifts along `liftF`. -/
theorem IsQC.liftSO (h : S ⊆ T) {E : SuperOp D S S} (hE : IsQC D E) :
    IsQC D (liftSO D h E) := by
  obtain ⟨f, rfl⟩ := hE.1.exists_kraus
  have h1 := (isQC_kraussoOf_iff D f).mp hE
  rw [liftSO_kraussoOf]
  refine (isQC_kraussoOf_iff D _).mpr ?_
  rw [Finset.sum_congr rfl fun i _ =>
      show LinearMap.adjoint (liftF D h (f i)) ∘ₗ liftF D h (f i)
          = liftF D h (LinearMap.adjoint (f i) ∘ₗ f i) by
        rw [adjoint_liftF, ← liftF_comp],
    ← liftF_sum, h1, liftF_one]

/-- CoqQ `liftso_tn` (`hstensor.v:3498`): the extension of a quantum operation
is a quantum operation — `liftF` is Löwner-monotone in the needed direction. -/
theorem IsQO.liftSO (h : S ⊆ T) {E : SuperOp D S S} (hE : IsQO D E) :
    IsQO D (liftSO D h E) := by
  obtain ⟨f, rfl⟩ := hE.1.exists_kraus
  have h1 := (isQO_kraussoOf_iff D f).mp hE
  rw [liftSO_kraussoOf]
  refine (isQO_kraussoOf_iff D _).mpr ?_
  rw [Finset.sum_congr rfl fun i _ =>
      show LinearMap.adjoint (liftF D h (f i)) ∘ₗ liftF D h (f i)
          = liftF D h (LinearMap.adjoint (f i) ∘ₗ f i) by
        rw [adjoint_liftF, ← liftF_comp],
    ← liftF_sum, ← liftF_one D h, LinearMap.le_def, ← liftF_sub D h]
  exact liftF_isPositive D h ((LinearMap.le_def _ _).mp h1)

/-! ## The frame lemmas (CoqQ `liftfsoEf_compl/compr`, `hstensor.v:4269,4288`)

The multiplier is first normalized to live on the exact complement `W \ T`
(`castF_liftF_sdiff`), where the commutation is a `tenf`/`tenso` interchange
(`tenso_id_comp_left/right`); the general disjoint-support version follows by
`liftF_liftF`. -/

private theorem res_eq_res_iff_of_eq {P Q O : Finset L} (hPQ : P = Q)
    (hP : P ⊆ O) (hQ : Q ⊆ O) (k l : QIdx D O) :
    QIdx.res D hP l = QIdx.res D hP k ↔ QIdx.res D hQ l = QIdx.res D hQ k := by
  subst hPQ; exact Iff.rfl

/-- Under the cast splitting `T ∪ (W \ T) = W`, the extension of an operator
on the complement `W \ T` is the identity tensored with that operator. -/
private theorem castF_liftF_sdiff (hT : T ⊆ W) (b : EndM D (W \ T)) :
    castF D (union_sdiff_of_subset hT).symm (union_sdiff_of_subset hT).symm
        (liftF D sdiff_subset b) = tenf D (1 : EndM D T) b := by
  have hTS : W \ (W \ T) = T := Finset.sdiff_sdiff_eq_self hT
  refine linM_ext D fun k => PiLp.ext fun l => ?_
  rw [castF_apply, castH_deltav, castH_apply, liftF_deltav_apply, tenf_deltav]
  simp only [QIdx.res_cast, tenv_apply, Module.End.one_apply, deltav_apply]
  rw [mul_comm]
  exact congrArg₂ (· * ·)
    (if_congr (res_eq_res_iff_of_eq D hTS _ _ k l) rfl rfl) rfl

/-- The tensor-with-identity super-operator commutes past left-multiplication
by `1 ⊗ᶠ b` (the cast-free core of the frame lemmas). -/
private theorem tenso_id_comp_left (hd : Disjoint S T) (E : SuperOp D S S)
    (b : EndM D T) (x : EndM D (S ∪ T)) :
    tenso D E (LinearMap.id : SuperOp D T T) (tenf D (1 : EndM D S) b ∘ₗ x)
      = tenf D (1 : EndM D S) b
          ∘ₗ tenso D E (LinearMap.id : SuperOp D T T) x := by
  have key : (tenso D E (LinearMap.id : SuperOp D T T)).comp
        (LinearMap.mulLeft ℂ (tenf D (1 : EndM D S) b))
      = (LinearMap.mulLeft ℂ (tenf D (1 : EndM D S) b)).comp
          (tenso D E (LinearMap.id : SuperOp D T T)) := by
    refine endM_ext_outer D fun k l => ?_
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, Module.End.mul_eq_comp]
    conv_lhs => rw [comp_outerLM, tenf_deltav, Module.End.one_apply,
      deltav_split D l, ← tenf_outerLM, tenso_apply_tenf D hd, LinearMap.id_apply]
    rw [tenso_outerLM_deltav, LinearMap.id_apply, ← tenf_comp D hd, one_comp,
      comp_outerLM]
  have hx := LinearMap.congr_fun key x
  simpa only [LinearMap.comp_apply, LinearMap.mulLeft_apply,
    Module.End.mul_eq_comp] using hx

/-- The tensor-with-identity super-operator commutes past right-multiplication
by `1 ⊗ᶠ b` (the cast-free core of the frame lemmas). -/
private theorem tenso_id_comp_right (hd : Disjoint S T) (E : SuperOp D S S)
    (b : EndM D T) (x : EndM D (S ∪ T)) :
    tenso D E (LinearMap.id : SuperOp D T T) (x ∘ₗ tenf D (1 : EndM D S) b)
      = tenso D E (LinearMap.id : SuperOp D T T) x
          ∘ₗ tenf D (1 : EndM D S) b := by
  have key : (tenso D E (LinearMap.id : SuperOp D T T)).comp
        (LinearMap.mulRight ℂ (tenf D (1 : EndM D S) b))
      = (LinearMap.mulRight ℂ (tenf D (1 : EndM D S) b)).comp
          (tenso D E (LinearMap.id : SuperOp D T T)) := by
    refine endM_ext_outer D fun k l => ?_
    simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, Module.End.mul_eq_comp]
    conv_lhs => rw [outerLM_comp_right D, adjoint_tenf, LinearMap.adjoint_one,
      tenf_deltav, Module.End.one_apply, deltav_split D k, ← tenf_outerLM,
      tenso_apply_tenf D hd, LinearMap.id_apply]
    rw [tenso_outerLM_deltav, LinearMap.id_apply, ← tenf_comp D hd, comp_one,
      outerLM_comp_right D]
  have hx := LinearMap.congr_fun key x
  simpa only [LinearMap.comp_apply, LinearMap.mulRight_apply,
    Module.End.mul_eq_comp] using hx

private theorem liftSO_liftF_compl_sdiff (hT : T ⊆ W) (E : SuperOp D T T)
    (b : EndM D (W \ T)) (g : EndM D W) :
    liftSO D hT E (liftF D sdiff_subset b ∘ₗ g)
      = liftF D sdiff_subset b ∘ₗ liftSO D hT E g := by
  have e := union_sdiff_of_subset hT
  rw [liftSO_apply, liftSO_apply,
    castF_comp D e.symm e.symm e.symm (liftF D sdiff_subset b) g,
    castF_liftF_sdiff D hT b, tenso_id_comp_left D disjoint_sdiff E b,
    castF_comp D e e e (tenf D (1 : EndM D T) b) _,
    ← castF_liftF_sdiff D hT b, castF_castF, castF_rfl, LinearEquiv.refl_apply]

private theorem liftSO_liftF_compr_sdiff (hT : T ⊆ W) (E : SuperOp D T T)
    (b : EndM D (W \ T)) (g : EndM D W) :
    liftSO D hT E (g ∘ₗ liftF D sdiff_subset b)
      = liftSO D hT E g ∘ₗ liftF D sdiff_subset b := by
  have e := union_sdiff_of_subset hT
  rw [liftSO_apply, liftSO_apply,
    castF_comp D e.symm e.symm e.symm g (liftF D sdiff_subset b),
    castF_liftF_sdiff D hT b, tenso_id_comp_right D disjoint_sdiff E b,
    castF_comp D e e e _ (tenf D (1 : EndM D T) b),
    ← castF_liftF_sdiff D hT b, castF_castF, castF_rfl, LinearEquiv.refl_apply]

/-- **Frame lemma, left version (M6 acceptance)** — CoqQ `liftfsoEf_compl`
(`hstensor.v:4269`), generalized from CoqQ's full space `[set: L]` to an
arbitrary common ambient register `W`: a lifted super-operator commutes past
left-composition by the lift of an operator supported on disjoint labels,
`liftSO E (liftF f ∘ g) = liftF f ∘ liftSO E g` for `Disjoint S T`. -/
theorem liftSO_liftF_compl (hd : Disjoint S T) (hS : S ⊆ W) (hT : T ⊆ W)
    (f : EndM D S) (E : SuperOp D T T) (g : EndM D W) :
    liftSO D hT E (liftF D hS f ∘ₗ g) = liftF D hS f ∘ₗ liftSO D hT E g := by
  have hSR : S ⊆ W \ T := subset_sdiff.mpr ⟨hS, hd⟩
  have hf : liftF D hS f = liftF D sdiff_subset (liftF D hSR f) :=
    (liftF_liftF D hSR sdiff_subset f).symm
  rw [hf, liftSO_liftF_compl_sdiff]

/-- **Frame lemma, right version (M6 acceptance)** — CoqQ `liftfsoEf_compr`
(`hstensor.v:4288`), generalized to an arbitrary common ambient register `W`:
`liftSO E (g ∘ liftF f) = liftSO E g ∘ liftF f` for `Disjoint S T`. -/
theorem liftSO_liftF_compr (hd : Disjoint S T) (hS : S ⊆ W) (hT : T ⊆ W)
    (f : EndM D S) (E : SuperOp D T T) (g : EndM D W) :
    liftSO D hT E (g ∘ₗ liftF D hS f) = liftSO D hT E g ∘ₗ liftF D hS f := by
  have hSR : S ⊆ W \ T := subset_sdiff.mpr ⟨hS, hd⟩
  have hf : liftF D hS f = liftF D sdiff_subset (liftF D hSR f) :=
    (liftF_liftF D hSR sdiff_subset f).symm
  rw [hf, liftSO_liftF_compr_sdiff]

/-! ## The full-space forms (CoqQ `hstensor.v:4058-4303`)

CoqQ's `liftf_lf`/`liftfso` live on the full space `[set: L]`, so this section
is the only place needing `[Fintype L]` (isolated here per the file
conventions). -/

section FullSpace

variable [Fintype L]

/-- Full-space cylindrical extension of operators (Q-9; CoqQ `liftf_lf`,
`hstensor.v:4058`). -/
noncomputable def liftF_top (f : EndM D S) : EndM D (univ : Finset L) :=
  liftF D (subset_univ S) f

/-- Full-space cylindrical extension of super-operators (Q-9; CoqQ `liftfso`,
`hstensor.v:4059`). -/
noncomputable def liftSO_top (E : SuperOp D S S) :
    SuperOp D (univ : Finset L) univ :=
  liftSO D (subset_univ S) E

/-- CoqQ `liftfsoEf_compl` (`hstensor.v:4269`), verbatim: the full-space form
of the left frame lemma. -/
theorem liftSO_top_compl (hd : Disjoint S T) (f : EndM D S)
    (E : SuperOp D T T) (g : EndM D (univ : Finset L)) :
    liftSO_top D E (liftF_top D f ∘ₗ g) = liftF_top D f ∘ₗ liftSO_top D E g :=
  liftSO_liftF_compl D hd (subset_univ S) (subset_univ T) f E g

/-- CoqQ `liftfsoEf_compr` (`hstensor.v:4288`), verbatim: the full-space form
of the right frame lemma. -/
theorem liftSO_top_compr (hd : Disjoint S T) (f : EndM D S)
    (E : SuperOp D T T) (g : EndM D (univ : Finset L)) :
    liftSO_top D E (g ∘ₗ liftF_top D f) = liftSO_top D E g ∘ₗ liftF_top D f :=
  liftSO_liftF_compr D hd (subset_univ S) (subset_univ T) f E g

end FullSpace

end Qhl
