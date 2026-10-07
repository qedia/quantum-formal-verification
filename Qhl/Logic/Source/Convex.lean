import Qhl.Logic.Source.TotalLoop
import Qhl.Logic.InitBlock
import Qhl.History.KrausSum

/-! # Scalar subprobability combinations with strict source domains

Weights are constant nonnegative reals. Every child retains its definedness
obligation, including zero-weight children. Convex2 permits the empty family;
Convex1's source rule uses a nonempty family so its supremum is an actual maximum.
-/
namespace Qhl
open Finset
open scoped NNReal ENNReal ComplexOrder ComplexInnerProductSpace
variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)] {σT : Type*}

private theorem convex_smul_mono (p : ℝ≥0) {X Y : EndM D (univ : Finset L)}
    (h : X ≤ Y) : (p : ℂ) • X ≤ (p : ℂ) • Y := by
  rw [le_iff_inner_le] at h ⊢
  intro v
  simp only [LinearMap.smul_apply, inner_smul_right]
  exact mul_le_mul_of_nonneg_left (h v) (Complex.zero_le_real.mpr p.2)

private theorem convex_smul_pos (p : ℝ≥0) {X : EndM D (univ : Finset L)}
    (h : X.IsPositive) : ((p : ℂ) • X).IsPositive := by
  apply (LinearMap.nonneg_iff_isPositive _).mp
  simpa using convex_smul_mono p ((LinearMap.nonneg_iff_isPositive _).mpr h)

private theorem convex_effect {ι : Type*} [Fintype ι]
    (A : ι → EndM D (univ : Finset L)) (hA : ∀ i, IsEffect (A i))
    (p : ι → ℝ≥0) (hp : ∑ i, p i ≤ 1) : IsEffect (∑ i, (p i : ℂ) • A i) := by
  constructor
  · exact Finset.sum_nonneg fun i _ =>
      (LinearMap.nonneg_iff_isPositive _).mpr (convex_smul_pos (p i) (hA i).isPositive)
  · calc
      _ ≤ ∑ i, (p i : ℂ) • (1 : EndM D univ) :=
        Finset.sum_le_sum fun i _ => convex_smul_mono (p i) (hA i).2
      _ = ((∑ i, p i : ℝ≥0) : ℂ) • (1 : EndM D univ) := by
        rw [← Finset.sum_smul]; simp
      _ ≤ 1 := by
        have h := real_smul_le_real_smul (show ((∑ i, p i : ℝ≥0) : ℝ) ≤ 1 by exact_mod_cast hp)
          (LinearMap.isPositive_one (E := HS D univ))
        simpa using h

namespace SourceAssertion
noncomputable def convex {ι : Type*} [Fintype ι] (φ : σT → Prop)
    (A : ι → SourceAssertion σT D) (p : ι → ℝ≥0) (hp : ∑ i, p i ≤ 1) :
    SourceAssertion σT D where
  classical := φ
  defined σ := ∀ i, (A i).defined σ
  quantum := ⟨fun σ => ∑ i, (p i : ℂ) • (A i).quantum.op σ,
    fun σ => convex_effect _ (fun i => (A i).quantum.isEffect σ) p hp⟩

noncomputable def scaled (φ : σT → Prop) (B : SourceAssertion σT D)
    (p : ℝ≥0) (hp : p ≤ 1) : SourceAssertion σT D where
  classical := φ
  defined := B.defined
  quantum := B.quantum.scaled p p.2 (by exact_mod_cast hp)

noncomputable def convexMax {ι : Type*} [Fintype ι] (p : ι → ℝ≥0) : ℝ≥0 :=
  univ.sup p

theorem le_convexMax {ι : Type*} [Fintype ι] (p : ι → ℝ≥0) (i : ι) :
    p i ≤ convexMax p := Finset.le_sup (f := p) (mem_univ i)

/-- On a nonempty family the finite supremum is an attained maximum. -/
theorem convexMax_attained {ι : Type*} [Fintype ι] [Nonempty ι] (p : ι → ℝ≥0) :
    ∃ i, p i = convexMax p := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup univ univ_nonempty p
  exact ⟨i, hi.symm⟩

theorem convexMax_le_one {ι : Type*} [Fintype ι] (p : ι → ℝ≥0)
    (hp : ∑ i, p i ≤ 1) : convexMax p ≤ 1 := by
  apply Finset.sup_le
  intro i _
  exact (Finset.single_le_sum (fun j _ => show 0 ≤ p j from zero_le) (mem_univ i)).trans hp

private theorem convex_pre_le {ι : Type*} [Fintype ι]
    (φ : σT → Prop) (A : ι → SourceAssertion σT D)
    (p : ι → ℝ≥0) (hp : ∑ i, p i ≤ 1) (σ : σT) :
    (convex φ A p hp).toAssn.op σ ≤
      ∑ i, (p i : ℂ) • ((A i).withClassical φ).toAssn.op σ := by
  classical
  by_cases h : φ σ ∧ ∀ i, (A i).defined σ
  · apply le_of_eq
    simp [toAssn, convex, withClassical, Assn.mask, h.1, h.2]
  · rw [show (convex φ A p hp).toAssn.op σ = 0 by
      simp [toAssn, convex, Assn.mask, h]]
    exact Finset.sum_nonneg fun i _ => (LinearMap.nonneg_iff_isPositive _).mpr
      (convex_smul_pos (p i) (((A i).withClassical φ).toAssn.isPositive σ))

private theorem convex_post_eq {ι : Type*} [Fintype ι]
    (ψ : σT → Prop) (B : ι → SourceAssertion σT D)
    (p : ι → ℝ≥0) (hp : ∑ i, p i ≤ 1)
    (hd : ∀ σ, ψ σ → ∀ i, (B i).defined σ) (σ : σT) :
    (convex ψ B p hp).toAssn.op σ =
      ∑ i, (p i : ℂ) • ((B i).withClassical ψ).toAssn.op σ := by
  classical
  by_cases h : ψ σ
  · simp [toAssn, convex, withClassical, Assn.mask, h, hd σ h]
  · simp [toAssn, convex, withClassical, Assn.mask, h]
end SourceAssertion

private theorem convex_expect_smul (p : ℝ≥0) (A : σT → EndM D (univ : Finset L))
    (s : CQState σT D) :
    expectE (fun σ => (p : ℂ) • A σ) s = (p : ℝ≥0∞) * expectE A s := by
  rw [expectE, expect, LinearMap.comp_smul, map_smul, smul_eq_mul,
    Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  change ENNReal.ofReal ((p : ℝ) * expect A s) = (p : ℝ≥0∞) * expectE A s
  simpa only [ENNReal.ofReal_coe_nnreal, expectE] using
    (ENNReal.ofReal_mul (p := (p : ℝ)) (q := expect A s) p.2)

private theorem convex_dSum_mul (r : ℝ≥0∞) (f : CQState σT D → ℝ≥0∞)
    (c : Config σT D) (n : ℕ) :
    dSum (fun t => r * f t) c n = r * dSum f c n := by
  simp only [dSum]
  generalize boundedFront c n = l
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    have hd : dVal (fun t => r * f t) a = r * dVal f a := by
      unfold dVal
      split_ifs <;> simp
    rw [hd, mul_add]

private theorem convex_PostH_smul (p : ℝ≥0) (A : σT → EndM D (univ : Finset L))
    (hA : ∀ σ, (A σ).IsPositive) (c : Config σT D) :
    PostH c (fun σ => (p : ℂ) • A σ) = (p : ℝ≥0∞) * PostH c A := by
  rw [PostH_eq_tsum (fun σ => convex_smul_pos p (hA σ)), PostH_eq_tsum hA,
    ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro n
  unfold postAtE
  rw [show expectE (fun σ => (p : ℂ) • A σ) = fun s => (p : ℝ≥0∞) * expectE A s
    from funext (convex_expect_smul p A)]
  exact convex_dSum_mul _ _ _ _

private theorem convex_expect_sum {ι : Type*} [Fintype ι]
    (A : ι → Assn σT D) (p : ι → ℝ≥0) (s : CQState σT D) :
    expectE (fun σ => ∑ i, (p i : ℂ) • (A i).op σ) s =
      ∑ i, (p i : ℝ≥0∞) * expectE (A i).op s := by
  rw [expectE_finset_sum univ _ (fun i _ σ => convex_smul_pos (p i) ((A i).isPositive σ))]
  apply Finset.sum_congr rfl
  intro i _
  exact convex_expect_smul _ _ _

private theorem convex_PostH_sum {ι : Type*} [Fintype ι]
    (A : ι → Assn σT D) (p : ι → ℝ≥0) (c : Config σT D) :
    PostH c (fun σ => ∑ i, (p i : ℂ) • (A i).op σ) =
      ∑ i, (p i : ℝ≥0∞) * PostH c (A i).op := by
  rw [PostH_fintype_sum _ (fun i σ => convex_smul_pos (p i) ((A i).isPositive σ))]
  apply Finset.sum_congr rfl
  intro i _
  exact convex_PostH_smul _ _ (A i).isPositive _

namespace SourceAssertion
private theorem validTot_convex_core {ι : Type*} [Fintype ι]
    (φ : σT → Prop) (A : ι → SourceAssertion σT D) (C : ι → Assn σT D)
    (B : Assn σT D) (p : ι → ℝ≥0) (hp : ∑ i, p i ≤ 1) (P : Prog σT D)
    (hout : ∀ σ, (∑ i, (p i : ℂ) • (C i).op σ) ≤ B.op σ)
    (hc : ∀ i, validTot ((A i).withClassical φ).toAssn P (C i)) :
    validTot (convex φ A p hp).toAssn P B := by
  intro s
  calc
    _ ≤ expectE (fun σ => ∑ i, (p i : ℂ) • ((A i).withClassical φ).toAssn.op σ) s :=
      expectE_mono (convex_pre_le φ A p hp) s
    _ = ∑ i, (p i : ℝ≥0∞) * expectE ((A i).withClassical φ).toAssn.op s :=
      convex_expect_sum _ _ _
    _ ≤ ∑ i, (p i : ℝ≥0∞) * PostH (Config.init P s) (C i).op :=
      Finset.sum_le_sum fun i _ => mul_le_mul le_rfl (hc i s) bot_le bot_le
    _ = PostH (Config.init P s) (fun σ => ∑ i, (p i : ℂ) • (C i).op σ) :=
      (convex_PostH_sum _ _ _).symm
    _ ≤ _ := PostH_mono (fun σ => LinearMap.isPositive_sum _
      (fun i _ => convex_smul_pos (p i) ((C i).isPositive σ))) B.isPositive hout _

private theorem validPar_convex_core {ι : Type*} [Fintype ι]
    (φ : σT → Prop) (A : ι → SourceAssertion σT D) (C : ι → Assn σT D)
    (B : Assn σT D) (p : ι → ℝ≥0) (hp : ∑ i, p i ≤ 1) (P : Prog σT D)
    (hout : ∀ σ, (∑ i, (p i : ℂ) • (C i).op σ) ≤ B.op σ)
    (hc : ∀ i, validPar ((A i).withClassical φ).toAssn P (C i)) :
    validPar (convex φ A p hp).toAssn P B := by
  intro s
  have hnt : (∑ i, (p i : ℝ≥0∞) * NT (Config.init P s)) ≤ NT (Config.init P s) := by
    rw [← Finset.sum_mul]
    have hsum : (∑ i, (p i : ℝ≥0∞)) ≤ 1 := by
      exact_mod_cast hp
    simpa using mul_le_mul hsum (le_refl (NT (Config.init P s))) bot_le bot_le
  calc
    _ ≤ expectE (fun σ => ∑ i, (p i : ℂ) • ((A i).withClassical φ).toAssn.op σ) s :=
      expectE_mono (convex_pre_le φ A p hp) s
    _ = ∑ i, (p i : ℝ≥0∞) * expectE ((A i).withClassical φ).toAssn.op s :=
      convex_expect_sum _ _ _
    _ ≤ ∑ i, (p i : ℝ≥0∞) * (PostH (Config.init P s) (C i).op + NT (Config.init P s)) :=
      Finset.sum_le_sum fun i _ => mul_le_mul le_rfl (hc i s) bot_le bot_le
    _ = (∑ i, (p i : ℝ≥0∞) * PostH (Config.init P s) (C i).op) +
        ∑ i, (p i : ℝ≥0∞) * NT (Config.init P s) := by
      simp only [mul_add, Finset.sum_add_distrib]
    _ ≤ PostH (Config.init P s) B.op + NT (Config.init P s) := by
      apply add_le_add _ hnt
      rw [← convex_PostH_sum]
      exact PostH_mono (fun σ => LinearMap.isPositive_sum _
        (fun i _ => convex_smul_pos (p i) ((C i).isPositive σ))) B.isPositive hout _

/-- Convex2 with every postpredicate defined under the common postcondition.
The index type may be empty; its strict-domain sum is then the total zero predicate. -/
theorem validTot_convex2 {ι : Type*} [Fintype ι]
    (φ ψ : σT → Prop) (A B : ι → SourceAssertion σT D)
    (p : ι → ℝ≥0) (hp : ∑ i, p i ≤ 1) (P : Prog σT D)
    (hdom : ∀ σ, ψ σ → ∀ i, (B i).defined σ)
    (hcomp : ∀ i, validTot ((A i).withClassical φ).toAssn P
      ((B i).withClassical ψ).toAssn) :
    validTot (convex φ A p hp).toAssn P (convex ψ B p hp).toAssn :=
  validTot_convex_core φ A _ _ p hp P
    (fun σ => (convex_post_eq ψ B p hp hdom σ).symm.le) hcomp

theorem validPar_convex2 {ι : Type*} [Fintype ι]
    (φ ψ : σT → Prop) (A B : ι → SourceAssertion σT D)
    (p : ι → ℝ≥0) (hp : ∑ i, p i ≤ 1) (P : Prog σT D)
    (hdom : ∀ σ, ψ σ → ∀ i, (B i).defined σ)
    (hcomp : ∀ i, validPar ((A i).withClassical φ).toAssn P
      ((B i).withClassical ψ).toAssn) :
    validPar (convex φ A p hp).toAssn P (convex ψ B p hp).toAssn :=
  validPar_convex_core φ A _ _ p hp P
    (fun σ => (convex_post_eq ψ B p hp hdom σ).symm.le) hcomp

private theorem convex1_post_le {ι : Type*} [Fintype ι]
    (ψ : ι → σT → Prop) (B : SourceAssertion σT D)
    (p : ι → ℝ≥0) (hp : ∑ i, p i ≤ 1)
    (hx : ∀ σ i j, i ≠ j → ψ i σ → ¬ ψ j σ) (σ : σT) :
    (∑ i, (p i : ℂ) • (B.withClassical (ψ i)).toAssn.op σ) ≤
      (scaled (fun σ => ∃ i, ψ i σ) B (convexMax p) (convexMax_le_one p hp)).toAssn.op σ := by
  classical
  by_cases hd : B.defined σ
  · by_cases he : ∃ i, ψ i σ
    · obtain ⟨j, hj⟩ := he
      have hs : (∑ i, (p i : ℂ) • (B.withClassical (ψ i)).toAssn.op σ) =
          (p j : ℂ) • B.quantum.op σ := by
        rw [Finset.sum_eq_single j]
        · simp [toAssn, withClassical, Assn.mask, hj, hd]
        · intro i _ hij
          have hi : ¬ ψ i σ := hx σ j i (Ne.symm hij) hj
          simp [toAssn, withClassical, Assn.mask, hi]
        · simp
      rw [hs]
      have he : ∃ i, ψ i σ := ⟨j, hj⟩
      simp only [toAssn, scaled, Assn.mask, he, hd, and_self, if_true]
      change (p j : ℂ) • B.quantum.op σ ≤ (convexMax p : ℂ) • B.quantum.op σ
      exact real_smul_le_real_smul (show (p j : ℝ) ≤ (convexMax p : ℝ) from
        le_convexMax p j) (B.quantum.isPositive σ)
    · have hn : ∀ i, ¬ ψ i σ := fun i hi => he ⟨i, hi⟩
      simp [toAssn, withClassical, scaled, Assn.mask, hn]
  · simp [toAssn, withClassical, scaled, Assn.mask, hd]

/-- Convex1 uses a nonempty family so `convexMax` denotes an attained maximum.
The common postpredicate retains its domain without any extra WD premise. -/
theorem validTot_convex1 {ι : Type*} [Fintype ι] [Nonempty ι]
    (φ : σT → Prop) (ψ : ι → σT → Prop)
    (A : ι → SourceAssertion σT D) (B : SourceAssertion σT D)
    (p : ι → ℝ≥0) (hp : ∑ i, p i ≤ 1) (P : Prog σT D)
    (hexcl : ∀ σ i j, i ≠ j → ψ i σ → ¬ ψ j σ)
    (hcomp : ∀ i, validTot ((A i).withClassical φ).toAssn P
      (B.withClassical (ψ i)).toAssn) :
    validTot (convex φ A p hp).toAssn P
      (scaled (fun σ => ∃ i, ψ i σ) B (convexMax p) (convexMax_le_one p hp)).toAssn :=
  validTot_convex_core φ A _ _ p hp P (convex1_post_le ψ B p hp hexcl) hcomp

theorem validPar_convex1 {ι : Type*} [Fintype ι] [Nonempty ι]
    (φ : σT → Prop) (ψ : ι → σT → Prop)
    (A : ι → SourceAssertion σT D) (B : SourceAssertion σT D)
    (p : ι → ℝ≥0) (hp : ∑ i, p i ≤ 1) (P : Prog σT D)
    (hexcl : ∀ σ i j, i ≠ j → ψ i σ → ¬ ψ j σ)
    (hcomp : ∀ i, validPar ((A i).withClassical φ).toAssn P
      (B.withClassical (ψ i)).toAssn) :
    validPar (convex φ A p hp).toAssn P
      (scaled (fun σ => ∃ i, ψ i σ) B (convexMax p) (convexMax_le_one p hp)).toAssn :=
  validPar_convex_core φ A _ _ p hp P (convex1_post_le ψ B p hp hexcl) hcomp
end SourceAssertion
end Qhl
