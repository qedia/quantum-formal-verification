import Qhl.Logic.Source.RegisterKraus
import Qhl.HSpace.KrausDomination

/-! # Tuple-space Kraus domination on raw registers

Domination by a singleton is transported to arbitrary global positive
inputs. For a normalized input family, the domination premise makes the singleton
injective; its contraction bound need not be an equality. The proof derives
proportionality from the local hypothesis; it does not restrict the supplied
operators to an assumed scalar family. Aliased registers
use the total extension already chosen by `registerKrausOps`.
-/

namespace Qhl

open Finset
open scoped ComplexOrder

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)] {E : Type*}

/-- A normalized family dominated by one operator forces that operator to be
injective. This uses domination on pure states, not unitarity. -/
theorem injective_of_normalized_domination {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] {ι : Type*} [Fintype ι]
    (K : ι → V →ₗ[ℂ] V) (J : V →ₗ[ℂ] V)
    (hK : ∑ i, LinearMap.adjoint (K i) ∘ₗ K i = 1)
    (hdom : ∀ i (R : V →ₗ[ℂ] V), R.IsPositive →
      K i ∘ₗ R ∘ₗ LinearMap.adjoint (K i) ≤ J ∘ₗ R ∘ₗ LinearMap.adjoint J) :
    Function.Injective J := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm _ bot_le
  intro v hv
  change v = 0
  have hj : J v = 0 := hv
  have hk : ∀ i, K i v = 0 := by
    intro i
    have h := hdom i (outerLM v v) (isPositive_outerLM_self v)
    have hx (T : V →ₗ[ℂ] V) : T ∘ₗ outerLM v v ∘ₗ LinearMap.adjoint T =
        outerLM (T v) (T v) := by
      simpa only [LinearMap.adjoint_adjoint] using
        adjoint_comp_outerLM_comp (LinearMap.adjoint T) v v
    rw [hx, hx, hj] at h
    have hm := mem_span_of_outerLM_le h
    simpa using hm
  have he := congrArg (fun T : V →ₗ[ℂ] V => T v) hK
  simpa [LinearMap.sum_apply, LinearMap.comp_apply, hk, Module.End.one_eq_id] using he.symm

/-- Domination by an injective singleton forces proportionality without
requiring the singleton to be unitary. -/
theorem eq_smul_of_conj_le_injective {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (K J : V →ₗ[ℂ] V) (hinj : Function.Injective J)
    (hdom : ∀ R : V →ₗ[ℂ] V, R.IsPositive →
      K ∘ₗ R ∘ₗ LinearMap.adjoint K ≤ J ∘ₗ R ∘ₗ LinearMap.adjoint J) :
    ∃ a : ℂ, K = a • J := by
  let e := LinearEquiv.ofInjectiveEndo J hinj
  let C : V →ₗ[ℂ] V := e.symm.toLinearMap ∘ₗ K
  obtain ⟨a, ha⟩ : ∃ a : ℂ, C = a • (1 : V →ₗ[ℂ] V) := by
    apply LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
    intro v hv
    have h := hdom (outerLM v v) (isPositive_outerLM_self v)
    have hx (T : V →ₗ[ℂ] V) : T ∘ₗ outerLM v v ∘ₗ LinearMap.adjoint T =
        outerLM (T v) (T v) := by
      simpa only [LinearMap.adjoint_adjoint] using
        adjoint_comp_outerLM_comp (LinearMap.adjoint T) v v
    rw [hx, hx] at h
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp (mem_span_of_outerLM_le h)
    have hvC : b • v = C v := by
      have hh := congrArg e.symm hb
      simpa only [map_smul, C, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
        show J v = e v from rfl, LinearEquiv.symm_apply_apply] using hh
    have hz := (LinearIndependent.pair_iff.mp hv) b (-1) (by simp [hvC])
    norm_num at hz
  refine ⟨a, LinearMap.ext fun v => ?_⟩
  have h := congrArg (fun T : V →ₗ[ℂ] V => e (T v)) ha
  simpa [C, e, Module.End.one_eq_id] using h

/-- The scalar domination factor is contractive for any injective singleton. -/
theorem scalar_gap_nonneg_of_conj_le_injective {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [Nontrivial V]
    (a : ℂ) (J : V →ₗ[ℂ] V) (hinj : Function.Injective J)
    (hdom : ∀ R : V →ₗ[ℂ] V, R.IsPositive →
      (a • J) ∘ₗ R ∘ₗ LinearMap.adjoint (a • J) ≤ J ∘ₗ R ∘ₗ LinearMap.adjoint J) :
    0 ≤ 1 - a * starRingEnd ℂ a := by
  have hn : J ∘ₗ LinearMap.adjoint J ≠ 0 := by
    intro hz
    have ha : LinearMap.adjoint J = 0 := by
      ext v
      apply hinj
      simpa using congrArg (fun T : V →ₗ[ℂ] V => T v) hz
    have hj : J = 0 := by simpa using congrArg LinearMap.adjoint ha
    exact LinearMap.ne_zero_of_injective hinj hj
  have h := hdom 1 LinearMap.isPositive_one
  rw [conj_smul_op, Module.End.one_eq_id, LinearMap.id_comp, LinearMap.le_def] at h
  have hp : (J ∘ₗ LinearMap.adjoint J).IsPositive := by
    simpa [Module.End.one_eq_id] using LinearMap.isPositive_one.conj_adjoint J
  apply (hp.isPositive_smul_iff hn).mp
  simpa only [sub_smul, one_smul] using h

/-- Tuple-space domination by an injective singleton extends to entangled inputs. -/
theorem regLift_conj_le_of_tuple_domination_injective {k : ℕ} (r : Reg L k)
    (K J : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun)
    (hinj : Function.Injective J)
    (hdom : ∀ R : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun, R.IsPositive →
      K ∘ₗ R ∘ₗ LinearMap.adjoint K ≤ J ∘ₗ R ∘ₗ LinearMap.adjoint J)
    (ρ : PDensity D) :
    (ρ.conj (regLift r K)).op ≤ (ρ.conj (regLift r J)).op := by
  obtain ⟨a, ha⟩ := eq_smul_of_conj_le_injective K J hinj hdom
  subst K
  have hgap := scalar_gap_nonneg_of_conj_le_injective a J hinj hdom
  have hs : regLift r (a • J) = a • regLift r J := by
    rw [regLift, r.op_smul, liftF_smul]
    rfl
  simp only [PDensity.conj_op, hs]
  rw [conj_smul_op, LinearMap.le_def]
  have hp := (ρ.pos.conj_adjoint (regLift r J)).smul_of_nonneg hgap
  simpa only [sub_smul, one_smul] using hp

/-- Normalized input-family domination lifts to an arbitrary singleton,
including a strictly subnormalized singleton. -/
theorem registerSingletonOps_domination {m k : ℕ} (r : E → Fin k → L)
    (M : ∀ a, QMeasure m (TSpace D (r a)))
    (J : ∀ a, TSpace D (r a) →ₗ[ℂ] TSpace D (r a))
    (hdom : ∀ a i (R : TSpace D (r a) →ₗ[ℂ] TSpace D (r a)), R.IsPositive →
      (M a).M i ∘ₗ R ∘ₗ LinearMap.adjoint ((M a).M i) ≤
        J a ∘ₗ R ∘ₗ LinearMap.adjoint (J a))
    (a : E) (i : Fin m) (ρ : PDensity D) :
    (ρ.conj (registerKrausOps r M a i)).op ≤
      (ρ.conj (registerSingletonOps r J a)).op := by
  classical
  by_cases hr : Function.Injective (r a)
  · simp only [registerKrausOps, registerSingletonOps, dif_pos hr]
    exact regLift_conj_le_of_tuple_domination_injective ⟨r a, hr⟩ _ _
      (injective_of_normalized_domination (M a).M (J a) (M a).complete (hdom a))
      (hdom a i) ρ
  · simp only [registerKrausOps, registerSingletonOps, dif_neg hr]
    split_ifs
    · exact le_rfl
    · simpa [PDensity.conj_op, Module.End.one_eq_id] using
        (LinearMap.nonneg_iff_isPositive ρ.op).mpr ρ.pos

/-- A tuple-space domination premise extends through ordered-register transport
and cylindrical extension, even for entangled global inputs. -/
theorem regLift_conj_le_of_tuple_domination {k : ℕ} (r : Reg L k)
    (K J : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun)
    (hJ : LinearMap.adjoint J ∘ₗ J = 1)
    (hdom : ∀ R : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun, R.IsPositive →
      K ∘ₗ R ∘ₗ LinearMap.adjoint K ≤ J ∘ₗ R ∘ₗ LinearMap.adjoint J)
    (ρ : PDensity D) :
    (ρ.conj (regLift r K)).op ≤ (ρ.conj (regLift r J)).op := by
  have hu := isUnitary_of_adjoint_comp_self hJ
  obtain ⟨a, ha⟩ := eq_smul_of_conj_le_unitary K J hu hdom
  subst K
  have hgap := scalar_gap_nonneg_of_conj_le a J hu hdom
  have hs : regLift r (a • J) = a • regLift r J := by
    rw [regLift, r.op_smul, liftF_smul]
    rfl
  simp only [PDensity.conj_op, hs]
  rw [conj_smul_op, LinearMap.le_def]
  have hp := (ρ.pos.conj_adjoint (regLift r J)).smul_of_nonneg hgap
  simpa only [sub_smul, one_smul] using hp

/-- The source's local tuple-space domination premise implies full-world state
domination for the total raw-register Kraus families. The fallback outside Dist
is either identity or zero, and the singleton fallback is identity. -/
theorem registerKrausOps_domination {m k : ℕ} (r : E → Fin k → L)
    (M : ∀ a, QMeasure m (TSpace D (r a)))
    (J : ∀ a, QMeasure 1 (TSpace D (r a)))
    (hdom : ∀ a i (R : TSpace D (r a) →ₗ[ℂ] TSpace D (r a)), R.IsPositive →
      (M a).M i ∘ₗ R ∘ₗ LinearMap.adjoint ((M a).M i) ≤
        (J a).M 0 ∘ₗ R ∘ₗ LinearMap.adjoint ((J a).M 0))
    (a : E) (i : Fin m) (ρ : PDensity D) :
    (ρ.conj (registerKrausOps r M a i)).op ≤
      (ρ.conj (registerKrausOps r J a 0)).op := by
  classical
  by_cases hr : Function.Injective (r a)
  · simp only [registerKrausOps, dif_pos hr]
    apply regLift_conj_le_of_tuple_domination ⟨r a, hr⟩
    · simpa using (J a).complete
    · exact hdom a i
  · have hj : Classical.choice (J a).index_nonempty = (0 : Fin 1) := Subsingleton.elim _ _
    simp only [registerKrausOps, dif_neg hr, hj, ↓reduceIte]
    split_ifs
    · exact le_rfl
    · simpa [PDensity.conj_op, Module.End.one_eq_id] using
        (LinearMap.nonneg_iff_isPositive ρ.op).mpr ρ.pos

end Qhl
