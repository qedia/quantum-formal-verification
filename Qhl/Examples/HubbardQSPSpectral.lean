import Qhl.Examples.HubbardQSPBK
import Qhl.HSpace.SpectralNorm

/-! # Strict spectral hypotheses for the Hubbard QSP example -/
namespace Qhl.HubbardQSPSpectral
open Finset BravyiKitaev HubbardLCU HubbardQSP

/-- Real Pauli coefficients make the Hubbard Hamiltonian Hermitian. -/
theorem hubbard_symmetric (x : ℕ) (t U : ℝ) : (hubbardOp x t U).IsSymmetric := by
  rw [LinearMap.isSymmetric_iff_isSelfAdjoint, isSelfAdjoint_iff, ← hubbardBK_eq]
  simp only [star_sum, star_smul, Complex.star_def, Complex.conj_ofReal,
    LinearMap.star_eq_adjoint, adjoint_pauliString]

theorem hubbard_one_apply (a b : Bool) :
    hubbardOp 1 1 1 (bkKet 1 ![a, b]) =
      if a then (if b then bkKet 1 ![true, true] else -bkKet 1 ![false, true])
      else (if b then -bkKet 1 ![true, false] else 0) := by
  have h01 : Function.update (Function.update (![false, true] : Fin 2 → Bool) 1 false)
      0 true = ![true, false] := by ext i; fin_cases i <;> rfl
  have h10 : Function.update (Function.update (![true, false] : Fin 2 → Bool) 0 false)
      1 true = ![false, true] := by ext i; fin_cases i <;> rfl
  cases a <;> cases b <;>
    simp [hubbardOp, nPairs, pL, pR, LinearMap.comp_apply,
      annOp_bkKet 1, creOp_bkKet 1, numOp_bkKet 1, signBelow,
      Function.update, Finset.prod_filter, h01, h10]

/-- At two modes, hopping and interaction both equal to one, H³ = H. -/
theorem hubbard_cube :
    hubbardOp 1 1 1 ∘ₗ hubbardOp 1 1 1 ∘ₗ hubbardOp 1 1 1 = hubbardOp 1 1 1 := by
  apply bkEndM_ext
  intro f
  have hf : f = ![f 0, f 1] := by ext i; fin_cases i <;> rfl
  rw [hf]
  cases h0 : f 0 <;> cases h1 : f 1 <;>
    simp [LinearMap.comp_apply, hubbard_one_apply false false,
      hubbard_one_apply false true, hubbard_one_apply true false, hubbard_one_apply true true]

private theorem abs_hopSignA (x : ℕ) (j : Fin (nPairs x)) : |hopSignA x j| = 1 := by
  have h := congrArg norm (hopSignA_spec x j)
  simpa [norm_mul, norm_phFactor] using h

private theorem abs_hopSignB (x : ℕ) (j : Fin (nPairs x)) : |hopSignB x j| = 1 := by
  have h := congrArg norm (hopSignB_spec x j)
  simpa [norm_mul, norm_phFactor] using h

/-- The actual LCU coefficient one-norm in the concrete strict instance. -/
theorem lam_one_one : lam 1 (1, 1) = 2 := by
  unfold lam cf
  rw [Equiv.sum_comp (tIdx 1) (fun l => |termCoef 1 1 1 l|)]
  simp [Fintype.sum_prod_type, nPairs, Fin.sum_univ_six, termCoef,
    abs_div, abs_hopSignA, abs_hopSignB]
  norm_num

abbrev WitnessSpace := HS (QubitCells (SysL 1)) (univ : Finset (SysL 1))
abbrev WitnessIndex := Fin (Module.finrank ℂ WitnessSpace)

noncomputable def witnessBasis : Module.Basis WitnessIndex ℂ WitnessSpace :=
  ((hubbard_symmetric 1 1 1).eigenvectorBasis rfl).toBasis
noncomputable def witnessEigenvalues : WitnessIndex → ℝ :=
  (hubbard_symmetric 1 1 1).eigenvalues rfl

theorem witness_norm (i : WitnessIndex) : ‖witnessBasis i‖ = 1 :=
  ((hubbard_symmetric 1 1 1).eigenvectorBasis rfl).norm_eq_one i

theorem witness_eig (i : WitnessIndex) :
    hubbardOp 1 1 1 (witnessBasis i) = (witnessEigenvalues i : ℂ) • witnessBasis i :=
  (hubbard_symmetric 1 1 1).apply_eigenvectorBasis rfl i

/-- Each real eigenvalue in this instance is zero, one or minus one. -/
theorem witness_eigenvalues_cases (i : WitnessIndex) :
    witnessEigenvalues i = 0 ∨ witnessEigenvalues i = 1 ∨ witnessEigenvalues i = -1 := by
  have h := congrArg (fun T => T (witnessBasis i)) hubbard_cube
  simp only [LinearMap.comp_apply, witness_eig, map_smul, smul_smul] at h
  have hv : witnessBasis i ≠ 0 := by
    intro hz
    have hn := witness_norm i
    rw [hz, norm_zero] at hn
    norm_num at hn
  have hc : (witnessEigenvalues i : ℂ) ^ 3 = witnessEigenvalues i := by
    apply (smul_left_injective ℂ hv)
    simpa [pow_succ, mul_assoc] using h
  have hr : witnessEigenvalues i ^ 3 = witnessEigenvalues i := by exact_mod_cast hc
  have hp : witnessEigenvalues i * (witnessEigenvalues i - 1) *
      (witnessEigenvalues i + 1) = 0 := by nlinarith [hr]
  rcases mul_eq_zero.mp hp with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (by linarith))
  · exact Or.inr (Or.inr (by linarith))

theorem witness_strict (i : WitnessIndex) :
    (witnessEigenvalues i / lam 1 (1, 1)) ^ 2 < 1 := by
  rw [lam_one_one]
  rcases witness_eigenvalues_cases i with h | h | h <;> rw [h] <;> norm_num

/-- Satisfiability of all spectral hypotheses used by the QSP block theorem. -/
theorem qsp_spectral_witness :
    ∃ (b : Module.Basis WitnessIndex ℂ WitnessSpace) (e : WitnessIndex → ℝ),
      (∀ i, ‖b i‖ = 1) ∧
      (∀ i, hubbardOp 1 1 1 (b i) = (e i : ℂ) • b i) ∧
      0 < lam 1 (1, 1) ∧ (∀ i, (e i / lam 1 (1, 1)) ^ 2 < 1) :=
  ⟨witnessBasis, witnessEigenvalues, witness_norm, witness_eig,
    by rw [lam_one_one]; norm_num, witness_strict⟩

/-- The operator norm hypothesis in the paper supplies the existing spectral premises. -/
theorem spectral_of_hubbard_norm_lt (x d : ℕ) (σ : STQc d)
    (h : ‖(hubbardOp x (coefQ d σ).1 (coefQ d σ).2).toContinuousLinearMap‖ <
      lam x (coefQ d σ)) :
    0 < lam x (coefQ d σ) ∧
    ∃ (b : Module.Basis (Fin (Module.finrank ℂ
        (HS (QubitCells (SysL x)) (univ : Finset (SysL x))))) ℂ
        (HS (QubitCells (SysL x)) (univ : Finset (SysL x)))) (e : _ → ℝ),
      (∀ i, ‖b i‖ = 1) ∧
      (∀ i, hubbardOp x (coefQ d σ).1 (coefQ d σ).2 (b i) = (e i : ℂ) • b i) ∧
      (∀ i, (e i / lam x (coefQ d σ)) ^ 2 < 1) :=
  spectral_of_norm_lt _ (hubbard_symmetric x _ _) _ h

/-- Under the induced operator norm bound, the actual BK-prefixed block has
an all-input spectral-polynomial description. -/
theorem encodedBlock_of_norm_lt (x : ℕ) (hx : 0 < x) (d : ℕ) (σ : STQc d)
    (h : ‖(hubbardOp x (coefQ d σ).1 (coefQ d σ).2).toContinuousLinearMap‖ <
      lam x (coefQ d σ)) :
    ∃ (b : Module.Basis (Fin (Module.finrank ℂ
        (HS (QubitCells (SysL x)) (univ : Finset (SysL x))))) ℂ
        (HS (QubitCells (SysL x)) (univ : Finset (SysL x)))) (e : _ → ℝ),
      (∀ i, ‖b i‖ = 1) ∧
      (∀ i, hubbardOp x (coefQ d σ).1 (coefQ d σ).2 (b i) = (e i : ℂ) • b i) ∧
      (∀ i, (e i / lam x (coefQ d σ)) ^ 2 < 1) ∧
      HubbardQSPBK.encodedBlock x hx d σ =
        HubbardQSPPredicates.spectralPolynomial x d b e σ ∘ₗ
          (BKTransform.bkUnitary x).val := by
  obtain ⟨hlam, b, e, hn, he, hs⟩ := spectral_of_hubbard_norm_lt x d σ h
  exact ⟨b, e, hn, he, hs,
    HubbardQSPBK.encodedBlock_eq_spectralPolynomial x hx d b e σ hlam hn he hs⟩

/-- The source-rule QSP theorem with the paper's strict operator norm domain. -/
theorem deriv_of_norm_lt (x : ℕ) (hx : 0 < x) (d : ℕ)
    (K : EndM (QubitCells (SysL x)) (univ : Finset (SysL x))) (hK : IsEffect K) :
    SourceDerivTot
      (SourceAssertion.ofAssn (HubbardQSPBK.pre x hx d K hK)
        (fun σ => ‖(hubbardOp x (coefQ d σ).1 (coefQ d σ).2).toContinuousLinearMap‖ <
          lam x (coefQ d σ)))
      (HubbardQSPBK.qspBKProg x hx d)
      (SourceAssertion.ofAssn (HubbardQSPPredicates.post x d K hK) (fun _ => True)) :=
  HubbardQSPBK.derivUnder x hx d K hK _

theorem valid_of_norm_lt (x : ℕ) (hx : 0 < x) (d : ℕ)
    (K : EndM (QubitCells (SysL x)) (univ : Finset (SysL x))) (hK : IsEffect K) :
    validTot
      (SourceAssertion.ofAssn (HubbardQSPBK.pre x hx d K hK)
        (fun σ => ‖(hubbardOp x (coefQ d σ).1 (coefQ d σ).2).toContinuousLinearMap‖ <
          lam x (coefQ d σ))).toAssn
      (HubbardQSPBK.qspBKProg x hx d) (HubbardQSPPredicates.post x d K hK) := by
  simpa only [SourceAssertion.toAssn_ofAssn_true] using (deriv_of_norm_lt x hx d K hK).sound

/-- The concrete strict witness identifies the actual BK-prefixed block at every
phase sequence and depth. -/
theorem witness_encodedBlock (d : ℕ) (σ : STQc d) (hσ : coefQ d σ = (1, 1)) :
    HubbardQSPBK.encodedBlock 1 (by omega) d σ =
      HubbardQSPPredicates.spectralPolynomial 1 d witnessBasis witnessEigenvalues σ ∘ₗ
        (BKTransform.bkUnitary 1).val := by
  apply HubbardQSPBK.encodedBlock_eq_spectralPolynomial
  · rw [hσ, lam_one_one]; norm_num
  · exact witness_norm
  · simpa only [hσ] using witness_eig
  · simpa only [hσ] using witness_strict

#print axioms deriv_of_norm_lt
#print axioms valid_of_norm_lt
#print axioms witness_encodedBlock
#print axioms hubbard_symmetric
#print axioms hubbard_cube
#print axioms lam_one_one
#print axioms qsp_spectral_witness
#print axioms spectral_of_hubbard_norm_lt
#print axioms encodedBlock_of_norm_lt

end Qhl.HubbardQSPSpectral
