import Qhl.Examples.QPEApproxTriple

/-!
# Approximate QPE — the operational success-probability guarantee

`Qhl/Examples/QPEApproxTriple.lean` closes the *evolution* triple
`{∣0…0,ψ⟩⟨0…0,ψ∣} qpeCirF n U {∣qpeOutR⟩⟨qpeOutR∣}` (the circuit reaches the state
`qpeOutR n φ ψ`) and the trivial weakest-precondition triple
`{qpeApproxPre} qpeCirF n U {goodA}`.  Neither of those yet contains the
Nielsen & Chuang success-probability bound `1 − 1/(2(e−1))`.

This file closes the **operational guarantee**: the good-outcome effect `goodA`
has expectation at least `1 − 1/(2(e−1))` in the state `qpeOutR n φ ψ` the
circuit reaches, for an eigenphase whose scaled value `2ⁿ·φ = b + δ` sits within
`δ ∈ [0,1)` of the integer `b`.  The bound is imported from the proven
`qpe_stage2_fourier_successBound` / `qpe_readout_successBound`
(`Qhl/Register/QPEPrecisionBridge.lean`, N&C (5.35)), assembled through the
Born-rule layer `Qhl/Logic/WpChain.lean`:

* `expectE_pure` turns the expectation into the quadratic form
  `⟪qpeOutR, goodOp qpeOutR⟫.re`;
* `re_inner_sum_outerLM_self` turns that quadratic form of the projector sum
  `goodOp = ∑_{good} ∣·⟩⟨·∣` into the Born sum `∑_{good} ‖⟪·, qpeOutR⟫‖²`;
* `inner_deltav_regLift_prodV` factors each good-outcome amplitude into the
  amplitude inside the counting block (the readout of the IQFT on the kicked
  profile) times the amplitude of the untouched target factor `ψ`;
* summing the target factor over its two basis values gives `‖ψ‖² = 1`, and the
  counting-block sum is exactly `qpe_readout_successBound ≥ 1 − 1/(2(e−1))`.

Everything is additive: `DerivTot`, `validTot`, the core inductives are
untouched.
-/

namespace Qhl.QPEApproxTriple

open Finset
open scoped ComplexInnerProductSpace
open Qhl.QPETriple

/-! ## §1. The good-outcome index of the full `(n+1)`-qubit world -/

/-- The classical index of the good ket `goodKet n b j c`: the counting bits are
`goodBits n b j`, the target bit is `c`. -/
noncomputable def goodTot (n : ℕ) (b j : ℤ) (c : Bool) :
    ∀ i : QubitL (n + 1), QubitD (n + 1) i :=
  fun i => if h : ((i : QubitL (n + 1)) : ℕ) < n
    then goodBits n b j ⟨((i : QubitL (n + 1)) : ℕ), h⟩ else c

/-- `goodKet` is the computational basis ket of the total outcome state `goodTot`. -/
theorem goodKet_eq_deltav (n : ℕ) (b j : ℤ) (c : Bool) :
    goodKet n b j c
      = deltav (QubitD (n + 1))
          (fun i : ↥(univ : Finset (QubitL (n + 1))) => goodTot n b j c (i : QubitL (n + 1))) :=
  rfl

/-- On a counting cell `goodTot` reads off the good bit vector. -/
theorem goodTot_castSucc (n : ℕ) (b j : ℤ) (c : Bool) (i : QubitL n) :
    goodTot n b j c (Fin.castSucc i) = goodBits n b j i := by
  have h : ((Fin.castSucc i : QubitL (n + 1)) : ℕ) < n := by rw [Fin.val_castSucc]; exact i.isLt
  rw [goodTot, dif_pos h]
  congr 1

/-- On the target cell `goodTot` reads off the eigenstate bit `c`. -/
theorem goodTot_last (n : ℕ) (b j : ℤ) (c : Bool) : goodTot n b j c (Fin.last n) = c := by
  rw [goodTot, dif_neg (by rw [Fin.val_last]; omega)]

/-! ## §2. The complement of the counting register is the target wire -/

/-- The counting register's complement is the single target wire. -/
theorem compl_ctrlReg (n : ℕ) :
    (univ : Finset (QubitL (n + 1))) \ (ctrlReg n).sig = {Fin.last n} := by
  ext i
  rw [Finset.mem_sdiff, Finset.mem_singleton]
  constructor
  · rintro ⟨-, hi⟩
    have hns : ¬ ((i : ℕ) < n) := fun hc => hi (mem_sig_ctrlReg.mpr hc)
    have := i.isLt
    exact Fin.ext (by simp only [Fin.val_last]; omega)
  · rintro rfl
    refine ⟨mem_univ _, fun hc => ?_⟩
    have := mem_sig_ctrlReg.mp hc
    simp only [Fin.val_last] at this
    omega

/-! ## §3. The Born factorisation of a good-outcome amplitude -/

/-- **The full good-outcome amplitude factors** into the counting-block IQFT
readout amplitude (the summand of `qpe_readout_successBound`) times the untouched
target component `ψ c`.  The block factorisation is `inner_deltav_regLift_prodV_tupleV`
and the subroutine transport of the counting block is `inner_single_fullGate_tupleV`
(both in `Qhl/Logic/WpChain.lean`), with the counting state identified through
`prodV_qpePhasedFamR_castSucc`. -/
theorem inner_goodKet_qpeOutR (n : ℕ) (φ : ℝ) (ψ : 𝕢) (b j : ℤ) (c : Bool) :
    (⟪goodKet n b j c, qpeOutR n φ ψ⟫ : ℂ)
      = ⟪deltav (QubitD n) (fun i => goodBits n b j (i : QubitL n)),
            (iqftOp n : HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
                HS (QubitD n) (univ : Finset (QubitL n))) (qpeKickedKet n φ)⟫
        * ψ c := by
  have hidx :
      (fun i : ↥(univ : Finset (QubitL n)) => goodTot n b j c (Fin.castSucc (i : QubitL n)))
        = fun i : ↥(univ : Finset (QubitL n)) => goodBits n b j (i : QubitL n) := by
    funext i; exact goodTot_castSucc n b j c (i : QubitL n)
  rw [goodKet_eq_deltav, qpeOutR,
    inner_deltav_regLift_prodV_tupleV (ctrlReg n) (iqftGate n) (qpePhasedFamR n φ ψ)
      (goodTot n b j c),
    compl_ctrlReg, Finset.prod_singleton]
  refine congrArg₂ (· * ·) ?_ ?_
  · -- counting block: subroutine transport of the IQFT
    rw [← prodV_qpePhasedFamR_castSucc, ← hidx]
    exact inner_single_fullGate_tupleV (fullRegN n) (Reg.sig_ofEquiv (Equiv.refl (Fin n)))
      (iqftOp n) (fun i => qpePhasedFamR n φ ψ (Fin.castSucc i))
      (fun i => goodTot n b j c (Fin.castSucc i))
  · -- target factor: the untouched eigenstate component
    rw [qpePhasedFamR_last, goodTot_last, EuclideanSpace.inner_single_left, map_one, one_mul]

/-! ## §4. Summing the target factor over its two basis values -/

/-- Summing `‖ψ c‖²` over the two target-qubit basis values gives `‖ψ‖²`. -/
theorem sum_norm_sq_target (ψ : 𝕢) :
    ∑ c ∈ (univ : Finset Bool), ‖ψ c‖ ^ 2 = ‖ψ‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]

/-! ## §5. The success-probability lower bound -/

/-- **The QPE success-probability lower bound (N&C 5.35).** For an eigenphase with
scaled value `2ⁿ·φ = b + δ`, `δ ∈ [0,1)`, the good-outcome effect `goodA` — the
`2e+1` computational-basis estimates within `e` of `b` — has expectation at least
`1 − 1/(2(e−1))` in the state the circuit reaches.  The bound is the proven
`qpe_readout_successBound` (hence `qpe_stage2_fourier_successBound`, N&C (5.35));
nothing here is postulated. -/
theorem qpeApprox_success_ge (n : ℕ) (φ : ℝ) (ψ : 𝕢) (hψ : ‖ψ‖ = 1)
    (b : ℤ) (δ : ℝ) (hb : (b : ℝ) + δ = 2 ^ n * φ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (e : ℕ) (he : 2 ≤ e) (heN : 2 * e < 2 ^ n) :
    ENNReal.ofReal (1 - 1 / (2 * ((e : ℝ) - 1)))
      ≤ expectE (goodA n b e heN).op ⟨(), PDensity.pure (qpeOutR n φ ψ)⟩ := by
  rw [expectE_pure]
  apply ENNReal.ofReal_le_ofReal
  -- The quadratic form of the projector sum is the Born sum.
  rw [goodA_op, goodOp,
    re_inner_sum_outerLM_self ((Finset.Icc (-(e : ℤ)) (e : ℤ)) ×ˢ (univ : Finset Bool))
      (fun p : ℤ × Bool => goodKet n b p.1 p.2) (qpeOutR n φ ψ)]
  -- Factor each summand.
  have hfac : ∀ p ∈ (Finset.Icc (-(e : ℤ)) (e : ℤ)) ×ˢ (univ : Finset Bool),
      ‖(⟪goodKet n b p.1 p.2, qpeOutR n φ ψ⟫ : ℂ)‖ ^ 2
        = ‖(⟪deltav (QubitD n) (fun i => goodBits n b p.1 (i : QubitL n)),
              (iqftOp n : HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
                  HS (QubitD n) (univ : Finset (QubitL n))) (qpeKickedKet n φ)⟫ : ℂ)‖ ^ 2
          * ‖ψ p.2‖ ^ 2 := by
    intro p _
    rw [inner_goodKet_qpeOutR, norm_mul, mul_pow]
  rw [Finset.sum_congr rfl hfac, Finset.sum_product]
  -- Split the double sum: the target factor sums to ‖ψ‖² = 1.
  have hsplit : ∑ j ∈ Finset.Icc (-(e : ℤ)) (e : ℤ),
      ∑ c ∈ (univ : Finset Bool),
        ‖(⟪deltav (QubitD n) (fun i => goodBits n b j (i : QubitL n)),
            (iqftOp n : HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
                HS (QubitD n) (univ : Finset (QubitL n))) (qpeKickedKet n φ)⟫ : ℂ)‖ ^ 2
          * ‖ψ c‖ ^ 2
        = ∑ j ∈ Finset.Icc (-(e : ℤ)) (e : ℤ),
            ‖(⟪deltav (QubitD n) (fun i => goodBits n b j (i : QubitL n)),
                (iqftOp n : HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
                    HS (QubitD n) (univ : Finset (QubitL n))) (qpeKickedKet n φ)⟫ : ℂ)‖ ^ 2 := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.mul_sum, sum_norm_sq_target, hψ, one_pow, mul_one]
  rw [hsplit]
  -- The counting-block Born sum is the proven readout bound.
  exact qpe_readout_successBound n φ b δ hb hδ0 hδ1 e he heN

/-! ## §6. The wp-fold at the input equals the good effect at the reached state -/

/-- Injectivity of a constant register expression, stated with the conclusion
type carrying `RegExpr.const` syntactically (so the anonymous `Reg` constructor
built by `inner_unitaryPre`/`inner_foldr_unitaryPre` is type-correct at
`implicit` transparency and `regLift_mk_of_const` fires). -/
theorem injective_regExpr_const (n : ℕ) {k : ℕ} (r : Reg (QubitL (n + 1)) k) :
    Function.Injective ((RegExpr.const (σT := Unit) r) ()) := r.inj

/-- **The Born bridge.** The weakest-precondition fold `qpeApproxPre` evaluated in
the pure input state `|0…0,ψ⟩` equals the good-outcome effect `goodA` evaluated in
the state `qpeOutR n φ ψ` the circuit reaches — the wp identity for a total unitary
program, obtained by peeling the three (Ax-Uni) stages of `qpeApproxPre` onto the
forward semantic operators (`inner_foldr_unitaryPre`/`inner_unitaryPre` of
`Qhl/Logic/WpChain.lean`) and identifying the evolved vector with `qpeOutR`
through the forward chain lemmas `chainOp_phCtrl`, `chainOp_kickCir` (§5) and the
definition of `qpeOutR` (the readout stage, `regLift_iqftCtrl`). Needs the
eigenphase hypothesis `hU`. -/
theorem expectE_qpeApproxPre_inputState (n : ℕ) (φ : ℝ) (U : UnitaryOp 𝕢) (ψ : 𝕢)
    (hU : (U : 𝕢 →ₗ[ℂ] 𝕢) ψ
      = Complex.exp (((2 * Real.pi * φ : ℝ) : ℂ) * Complex.I) • ψ)
    (b : ℤ) (e : ℕ) (heN : 2 * e < 2 ^ n) :
    expectE (qpeApproxPre n U b e heN).op (inputState n ψ)
      = expectE (goodA n b e heN).op ⟨(), PDensity.pure (qpeOutR n φ ψ)⟩ := by
  rw [inputState, expectE_pure, expectE_pure, goodA_op]
  refine congrArg (fun z : ℝ => ENNReal.ofReal z) (congrArg Complex.re ?_)
  rw [qpeApproxPre]
  rw [inner_foldr_unitaryPre (List.map Fin.castSucc (List.finRange n)) (fun _ => 1)
    (fun a => fun _ (_ : Fin 1) => a) (fun a => fun _ => singleGate (QubitD (n + 1)) a H)
    _ () (fun a => Function.injective_of_subsingleton (fun _ : Fin 1 => a)) _]
  rw [inner_foldr_unitaryPre (List.finRange n) (fun _ => 2)
    (fun k => RegExpr.const (Reg.pair k.castSucc (Fin.last n) (castSucc_ne_last k)))
    (fun k _ => pairGate (D := QubitD (n + 1)) k.castSucc (Fin.last n) (castSucc_ne_last k)
      (control (U ^ 2 ^ (n - 1 - (k : ℕ)))))
    ((goodA n b e heN).unitaryPre (RegExpr.const (ctrlReg n)) (fun _ => iqftGate n)) ()
    (fun k => injective_regExpr_const n (Reg.pair k.castSucc (Fin.last n) (castSucc_ne_last k))) _]
  rw [inner_unitaryPre (RegExpr.const (ctrlReg n)) (fun _ => iqftGate n) _ ()
    (injective_regExpr_const n (ctrlReg n)) _]
  -- Normalise the peeled registers to the §5 forms and evaluate the forward chain.
  simp only [regLift_mk_of_single, regLift_mk_of_const]
  rw [chainOp_phCtrl, chainOp_kickCir n φ U ψ hU, goodA_op, qpeOutR]

/-! ## §7. The operational success-probability guarantee -/

/-- **The fused operational QPE success-probability guarantee.** Running the
approximate-QPE circuit `qpeCirF n U` on the input `|0…0⟩⊗ψ` (an eigenvector of
`U` with eigenphase `φ`, `2ⁿ·φ = b + δ`, `δ ∈ [0,1)`), the terminal
post-expectation of the good-outcome effect `goodA` — the operational success
probability that the readout lands within `e` of the integer `b` — is at least
`1 − 1/(2(e−1))` (Nielsen & Chuang (5.35)). This chains the evolution/wp triple
`qpeApproxValid` (soundness of the (Ax-Uni) derivation) with the Fourier bound
`qpeApprox_success_ge` (hence the proven `qpe_stage2_fourier_successBound`)
through the Born bridge `expectE_qpeApproxPre_inputState`; nothing is
re-axiomatised. -/
theorem qpeApprox_operational (n : ℕ) (φ : ℝ) (U : UnitaryOp 𝕢) (ψ : 𝕢) (hψ : ‖ψ‖ = 1)
    (hU : (U : 𝕢 →ₗ[ℂ] 𝕢) ψ
      = Complex.exp (((2 * Real.pi * φ : ℝ) : ℂ) * Complex.I) • ψ)
    (b : ℤ) (δ : ℝ) (hb : (b : ℝ) + δ = 2 ^ n * φ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (e : ℕ) (he : 2 ≤ e) (heN : 2 * e < 2 ^ n) :
    ENNReal.ofReal (1 - 1 / (2 * ((e : ℝ) - 1)))
      ≤ PostH (Config.init (qpeCirF n U) (inputState n ψ)) (goodA n b e heN).op := by
  refine le_trans ?_ (qpeApproxValid n U b e heN (inputState n ψ))
  rw [expectE_qpeApproxPre_inputState n φ U ψ hU b e heN]
  exact qpeApprox_success_ge n φ ψ hψ b δ hb hδ0 hδ1 e he heN

end Qhl.QPEApproxTriple
