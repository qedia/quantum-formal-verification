import Qhl.Logic.Assertion
import Qhl.History.KrausFrame

/-! # Finite positive-operator sums in history expectations -/

namespace Qhl

open Finset
open scoped NNReal ENNReal

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)] {σT : Type*}

omit [∀ i, Inhabited (D i)] in
/-- Trace expectations distribute over an arbitrary finite operator family. -/
theorem expect_finset_sum {ι : Type*} (t : Finset ι)
    (A : ι → σT → EndM D (univ : Finset L)) (s : CQState σT D) :
    expect (fun σ => ∑ i ∈ t, A i σ) s = ∑ i ∈ t, expect (A i) s := by
  induction t using Finset.cons_induction with
  | empty => simp [expect]
  | cons i t hi ih =>
      simp only [Finset.sum_cons]
      simp only [expect, LinearMap.comp_add, map_add, Complex.add_re] at ih ⊢
      rw [ih]

/-- Nonnegative finite expectations distribute through the ENNReal embedding. -/
theorem expectE_finset_sum {ι : Type*} (t : Finset ι)
    (A : ι → σT → EndM D (univ : Finset L))
    (hA : ∀ i ∈ t, ∀ σ, (A i σ).IsPositive) (s : CQState σT D) :
    expectE (fun σ => ∑ i ∈ t, A i σ) s = ∑ i ∈ t, expectE (A i) s := by
  rw [expectE, expect_finset_sum, ENNReal.ofReal_sum_of_nonneg]
  · rfl
  · intro i hi
    exact expect_nonneg (hA i hi) s

/-- The full post-expectation is additive in a finite positive family. -/
theorem PostH_fintype_sum {ι : Type*} [Fintype ι]
    (A : ι → σT → EndM D (univ : Finset L))
    (hA : ∀ i σ, (A i σ).IsPositive) (c : Config σT D) :
    PostH c (fun σ => ∑ i, A i σ) = ∑ i, PostH c (A i) := by
  have hsum : ∀ σ, (∑ i, A i σ).IsPositive :=
    fun σ => LinearMap.isPositive_sum _ (fun i _ => hA i σ)
  rw [PostH_eq_tsum hsum]
  simp_rw [PostH_eq_tsum (hA _)]
  have he : ∀ n, postAtE c n (fun σ => ∑ i, A i σ) = ∑ i, postAtE c n (A i) := by
    intro n
    unfold postAtE
    rw [show expectE (fun σ => ∑ i, A i σ) =
      (fun s => ∑ i, expectE (A i) s) from
        funext fun s => expectE_finset_sum univ A (fun i _ => hA i) s]
    exact dSum_finset_sum univ (fun i => expectE (A i)) c n
  simp_rw [he]
  simpa only [tsum_fintype] using
    (ENNReal.tsum_comm (f := fun n (i : ι) => postAtE c n (A i)))

/-- Finite Kraus expectation decomposition, for arbitrary positive child operators. -/
theorem expectE_kraus_sum {ι : Type*} [Fintype ι]
    (A : ι → σT → EndM D (univ : Finset L))
    (hA : ∀ i σ, (A i σ).IsPositive)
    (K : σT → ι → EndM D (univ : Finset L)) (s : CQState σT D) :
    expectE (fun σ => ∑ i, LinearMap.adjoint (K σ i) ∘ₗ A i σ ∘ₗ K σ i) s =
      ∑ i, expectE (A i) ⟨s.cls, s.q.conj (K s.cls i)⟩ := by
  rw [expectE_finset_sum univ _ (fun i _ σ => (hA i σ).adjoint_conj (K σ i))]
  apply Finset.sum_congr rfl
  intro i _
  unfold expectE
  rw [← expect_conj (A i) (K s.cls i) s.cls s]
  rfl

omit [∀ i, Inhabited (D i)] in
/-- Normalization conserves total mass across the finite family. -/
theorem sum_massE_conj {ι : Type*} [Fintype ι]
    (K : ι → EndM D (univ : Finset L)) (hK : IsQMeasure D K) (ρ : PDensity D) :
    ∑ i, ((ρ.conj (K i)).mass : ℝ≥0∞) = (ρ.mass : ℝ≥0∞) := by
  rw [← ENNReal.ofNNReal_finsetSum, PDensity.sum_mass_conj_of_isQMeasure hK]

/-- Normalized framed branches preserve the total terminating trace mass. -/
theorem sum_TermH_krausMap {ι : Type*} [Fintype ι]
    (K : σT → ι → EndM D (univ : Finset L))
    (hK : ∀ σ, IsQMeasure D (K σ)) (c : Config σT D)
    (hc : ∀ i, c.ctrl.KrausFrame (fun σ => K σ i)) :
    (∑ i, TermH (c.krausMap (fun σ => K σ i))) = TermH c := by
  simp_rw [TermH_eq_tsum]
  have hexchange : (∑ i, ∑' n, termMassE (c.krausMap (fun σ => K σ i)) n) =
      ∑' n, ∑ i, termMassE (c.krausMap (fun σ => K σ i)) n := by
    simpa only [tsum_fintype] using
      (ENNReal.tsum_comm (f := fun (i : ι) n => termMassE (c.krausMap (fun σ => K σ i)) n))
  rw [hexchange]
  apply tsum_congr
  intro n
  simp only [termMassE, (hc _).dSum_map]
  rw [← dSum_finset_sum]
  apply dSum_congr
  intro t
  exact sum_massE_conj (K t.cls) (hK t.cls) t.q

/-- Normalization sums the branch nontermination quantities to the original one.
The proof uses finite mass balance, so it covers infinite execution and stuck
configurations without treating an operator difference as a positive state. -/
theorem sum_NTH_krausMap {ι : Type*} [Fintype ι]
    (K : σT → ι → EndM D (univ : Finset L))
    (hK : ∀ σ, IsQMeasure D (K σ)) (c : Config σT D)
    (hc : ∀ i, c.ctrl.KrausFrame (fun σ => K σ i)) :
    (∑ i, NTH (c.krausMap (fun σ => K σ i))) = NTH c := by
  have hfinite : TermH c ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top (terminatingTraceMass_le c)
  apply (ENNReal.add_left_inj hfinite).mp
  calc
    (∑ i, NTH (c.krausMap (fun σ => K σ i))) + TermH c =
        (∑ i, NTH (c.krausMap (fun σ => K σ i))) +
          ∑ i, TermH (c.krausMap (fun σ => K σ i)) := by
      rw [sum_TermH_krausMap K hK c hc]
    _ = ∑ i, (NTH (c.krausMap (fun σ => K σ i)) +
        TermH (c.krausMap (fun σ => K σ i))) := (Finset.sum_add_distrib).symm
    _ = ∑ i, ((c.q.conj (K c.cls i)).mass : ℝ≥0∞) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [add_comm, TermH_add_NTH]
      rfl
    _ = (c.mass : ℝ≥0∞) := sum_massE_conj (K c.cls) (hK c.cls) c.q
    _ = NTH c + TermH c := by rw [add_comm, TermH_add_NTH]

/-- The summed branch post-expectations are the post-expectation of the
Kraus-transformed finite family. -/
theorem sum_PostH_krausMap {ι : Type*} [Fintype ι]
    (K : σT → ι → EndM D (univ : Finset L)) (B : ι → Assn σT D)
    (c : Config σT D) (hc : ∀ i, c.ctrl.KrausFrame (fun σ => K σ i)) :
    (∑ i, PostH (c.krausMap (fun σ => K σ i)) (B i).op) =
      PostH c (fun σ => ∑ i, LinearMap.adjoint (K σ i) ∘ₗ (B i).op σ ∘ₗ K σ i) := by
  rw [PostH_fintype_sum _ (fun i σ => (B i).isPositive σ |>.adjoint_conj (K σ i))]
  apply Finset.sum_congr rfl
  intro i _
  exact (hc i).PostH_map (B i)

end Qhl
