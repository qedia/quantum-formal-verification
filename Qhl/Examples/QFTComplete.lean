import Qhl.Logic.Source.SharpPost
import Qhl.Examples.QFTUniform
import Qhl.Examples.QFTArbitrary
import Qhl.Register.FourierUniform
import Qhl.Logic.SharpPost

/-! # QFT correctness from basis and uniform-superposition Hoare triples

The relative-phase argument uses the proved Hoare triples, not the separate
gate-composite Fourier equality. The final arbitrary-input result is again
a source-rule derivation, obtained by consequence.
-/

namespace Qhl.QFTComplete
open Qhl Finset
open scoped ComplexInnerProductSpace

variable (n : ℕ) [NeZero n]

/-- The basis triples identify the output projectors of the circuit composite. -/
theorem basis_projector_from_triples (x : Fin n → Bool) :
    let w := prodV (QubitD n) (W := (univ : Finset (QubitL n))) (fun i => qbit (x i))
    outerLM (QFTTriple.qftCirOp n w) (QFTTriple.qftCirOp n w) =
      outerLM (fourierState n x) (fourierState n x) := by
  exact (QFTArbitrary.qftDeriv n _ (norm_prodV_eq_one _ fun _ => norm_qbit _)).pure_post_unique
    (0, 0) (QFTTriple.qftDeriv n x)

/-- The uniform-input triple fixes the remaining relative phases. -/
theorem qftCirOp_phase_from_triples :
    ∃ c : ℂ, ‖c‖ = 1 ∧ QFTTriple.qftCirOp n =
      c • (qftOp n : HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
        HS (QubitD n) (univ : Finset (QubitL n))) := by
  let b := EuclideanSpace.basisFun (QIdx (QubitD n) (univ : Finset (QubitL n))) ℂ
  have hbasis (i : QIdx (QubitD n) (univ : Finset (QubitL n))) :
      b i = deltav (QubitD n) i := by
    simp only [b, EuclideanSpace.basisFun_apply, deltav]
  apply isometry_eq_phase_of_basis_projectors b (QFTTriple.qftCirOp n) (qftOp n)
    (QFTArbitrary.isUnitary_qftCirOp n).isIsometryOp (qftOp n).isUnitary.isIsometryOp
    (allPlus n) (norm_allPlus n)
  · intro i
    rw [hbasis]
    rw [Qhl.inner_deltav (D := QubitD n) (S := univ), allPlus_apply]
    exact pow_ne_zero _ (inv_ne_zero (Complex.ofReal_ne_zero.mpr
      (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))))
  · intro i
    rw [hbasis]
    change outerLM (QFTTriple.qftCirOp n (deltav (QubitD n) i))
      (QFTTriple.qftCirOp n (deltav (QubitD n) i)) =
      outerLM ((qftOp n : EndM (QubitD n) (univ : Finset (QubitL n))) (deltav (QubitD n) i))
        ((qftOp n : EndM (QubitD n) (univ : Finset (QubitL n))) (deltav (QubitD n) i))
    have h := basis_projector_from_triples n (fun j => i ⟨j, mem_univ j⟩)
    dsimp only at h
    rw [QFTTriple.prodV_qbit_eq_deltav] at h
    rw [qftOp_deltav n (fun j => i ⟨j, mem_univ j⟩)]
    exact h
  · rw [qftOp_allPlus]
    exact (QFTArbitrary.qftDeriv n (allPlus n) (norm_allPlus n)).pure_post_unique
      (0, 0) (QFTUniform.qftUniformDeriv n)

/-- The circuit and Fourier operator agree on every pure-state projector. -/
theorem qft_projector_from_triples
    (ψ : HS (QubitD n) (univ : Finset (QubitL n))) :
    outerLM (QFTTriple.qftCirOp n ψ) (QFTTriple.qftCirOp n ψ) =
      outerLM ((qftOp n : EndM (QubitD n) (univ : Finset (QubitL n))) ψ)
        ((qftOp n : EndM (QubitD n) (univ : Finset (QubitL n))) ψ) := by
  obtain ⟨c, hc, h⟩ := qftCirOp_phase_from_triples n
  rw [h]
  simp only [LinearMap.smul_apply, outerLM_smul_left, outerLM_smul_right, smul_smul]
  have hphase : starRingEnd ℂ c * c = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]
    norm_num
  change (starRingEnd ℂ c * c) • _ = _
  rw [hphase, one_smul]

/-- QHL⁺ total correctness for every unit input, using the identified projector. -/
theorem qftAllInputDeriv (ψ : HS (QubitD n) (univ : Finset (QubitL n))) (hψ : ‖ψ‖ = 1) :
    DerivTot (σT := ℕ × ℕ) (Assn.ofState ψ hψ) (QFTTriple.qftCir n)
      (Assn.ofState ((qftOp n : EndM (QubitD n) (univ : Finset (QubitL n))) ψ)
        (norm_eq_one_of_isUnitary (qftOp n).isUnitary hψ)) := by
  refine DerivTot.conseq (fun _ => le_rfl) (QFTArbitrary.qftDeriv n ψ hψ) ?_
  intro σ
  exact le_of_eq (qft_projector_from_triples n ψ)

/-- Semantic validity follows from the arbitrary-input QHL⁺ derivation. -/
theorem qftAllInputValid (ψ : HS (QubitD n) (univ : Finset (QubitL n))) (hψ : ‖ψ‖ = 1) :
    validTot (σT := ℕ × ℕ) (Assn.ofState ψ hψ) (QFTTriple.qftCir n)
      (Assn.ofState ((qftOp n : EndM (QubitD n) (univ : Finset (QubitL n))) ψ)
        (norm_eq_one_of_isUnitary (qftOp n).isUnitary hψ)) :=
  (qftAllInputDeriv n ψ hψ).sound

end Qhl.QFTComplete

namespace Qhl.QFTCompleteSource
open Qhl Finset
open scoped ComplexInnerProductSpace

variable (n : ℕ) [NeZero n]

/-- The basis triples identify the output projectors of the circuit composite. -/
theorem basis_projector_from_triples (x : Fin n → Bool) :
    let w := prodV (QubitD n) (W := (univ : Finset (QubitL n))) (fun i => qbit (x i))
    outerLM (QFTTriple.qftCirOp n w) (QFTTriple.qftCirOp n w) =
      outerLM (fourierState n x) (fourierState n x) := by
  exact (QFTArbitrarySource.qftDeriv n _
    (norm_prodV_eq_one _ fun _ => norm_qbit _)).pure_post_unique
    (0, 0) (QFTSource.qftDeriv n x)

/-- The uniform-input triple fixes the remaining relative phases. -/
theorem qftCirOp_phase_from_triples :
    ∃ c : ℂ, ‖c‖ = 1 ∧ QFTTriple.qftCirOp n =
      c • (qftOp n : HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
        HS (QubitD n) (univ : Finset (QubitL n))) := by
  let b := EuclideanSpace.basisFun (QIdx (QubitD n) (univ : Finset (QubitL n))) ℂ
  have hbasis (i : QIdx (QubitD n) (univ : Finset (QubitL n))) :
      b i = deltav (QubitD n) i := by
    simp only [b, EuclideanSpace.basisFun_apply, deltav]
  apply isometry_eq_phase_of_basis_projectors b (QFTTriple.qftCirOp n) (qftOp n)
    (QFTArbitrary.isUnitary_qftCirOp n).isIsometryOp (qftOp n).isUnitary.isIsometryOp
    (allPlus n) (norm_allPlus n)
  · intro i
    rw [hbasis]
    rw [Qhl.inner_deltav (D := QubitD n) (S := univ), allPlus_apply]
    exact pow_ne_zero _ (inv_ne_zero (Complex.ofReal_ne_zero.mpr
      (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))))
  · intro i
    rw [hbasis]
    change outerLM (QFTTriple.qftCirOp n (deltav (QubitD n) i))
      (QFTTriple.qftCirOp n (deltav (QubitD n) i)) =
      outerLM ((qftOp n : EndM (QubitD n) (univ : Finset (QubitL n))) (deltav (QubitD n) i))
        ((qftOp n : EndM (QubitD n) (univ : Finset (QubitL n))) (deltav (QubitD n) i))
    have h := basis_projector_from_triples n (fun j => i ⟨j, mem_univ j⟩)
    dsimp only at h
    rw [QFTTriple.prodV_qbit_eq_deltav] at h
    rw [qftOp_deltav n (fun j => i ⟨j, mem_univ j⟩)]
    exact h
  · rw [qftOp_allPlus]
    exact (QFTArbitrarySource.qftDeriv n (allPlus n) (norm_allPlus n)).pure_post_unique
      (0, 0) (QFTSource.qftUniformDeriv n)

/-- The circuit and Fourier operator agree on every pure-state projector. -/
theorem qft_projector_from_triples
    (ψ : HS (QubitD n) (univ : Finset (QubitL n))) :
    outerLM (QFTTriple.qftCirOp n ψ) (QFTTriple.qftCirOp n ψ) =
      outerLM ((qftOp n : EndM (QubitD n) (univ : Finset (QubitL n))) ψ)
        ((qftOp n : EndM (QubitD n) (univ : Finset (QubitL n))) ψ) := by
  obtain ⟨c, hc, h⟩ := qftCirOp_phase_from_triples n
  rw [h]
  simp only [LinearMap.smul_apply, outerLM_smul_left, outerLM_smul_right, smul_smul]
  have hphase : starRingEnd ℂ c * c = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]
    norm_num
  change (starRingEnd ℂ c * c) • _ = _
  rw [hphase, one_smul]

/-- The arbitrary-input source derivation has the independent Fourier target. -/
theorem qftAllInputDeriv (ψ : HS (QubitD n) (univ : Finset (QubitL n))) (hψ : ‖ψ‖ = 1) :
    SourceDerivTot
      (SourceAssertion.ofAssn (Assn.ofState ψ hψ) (fun _ => True)) (QFTTriple.qftCir n)
      (SourceAssertion.ofAssn
        (Assn.ofState ((qftOp n : EndM (QubitD n) (univ : Finset (QubitL n))) ψ)
          (norm_eq_one_of_isUnitary (qftOp n).isUnitary hψ)) (fun _ => True)) := by
  refine SourceDerivTot.conseq (SourceAssertion.entails_refl _)
    (QFTArbitrarySource.qftDeriv n ψ hψ) ?_
  apply SourceAssertion.entails_ofAssn
  · intro _ h; exact h
  · intro σ _
    exact le_of_eq (qft_projector_from_triples n ψ)

theorem qftAllInputValid (ψ : HS (QubitD n) (univ : Finset (QubitL n))) (hψ : ‖ψ‖ = 1) :
    validTot (Assn.ofState ψ hψ) (QFTTriple.qftCir n)
      (Assn.ofState ((qftOp n : EndM (QubitD n) (univ : Finset (QubitL n))) ψ)
        (norm_eq_one_of_isUnitary (qftOp n).isUnitary hψ)) := by
  simpa only [SourceAssertion.toAssn_ofAssn_true] using (qftAllInputDeriv n ψ hψ).sound
end Qhl.QFTCompleteSource
