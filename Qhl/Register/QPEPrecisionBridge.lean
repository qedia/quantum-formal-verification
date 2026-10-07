import Qhl.Register.Fourier
import Qhl.Register.QPEPrecision

/-!
# The kicked profile state and its Fourier overlap (precision-analysis groundwork)

**PRECISION-ANALYSIS LAYER — with an operational consumer.** This file is the
quantum-side half of the standalone Nielsen & Chuang §5.2.1 *precision analysis*.
It is **not** composed into the *exact*-phase phase-estimation triple, and
nothing on the exact-phase path imports it — that dependency points this way
only: the bridge *reads* the verified stage-2 states (`qpePhasedFam`,
`qpePhasedFamR`, `Qhl/Register/Fourier.lean` §11–§12), the exact-phase
development never reads the bridge.

It **is** consumed by the operational approximate-QPE example
`Qhl/Examples/QPEApproxTriple.lean`, which proves a genuine `validTot`
weakest-precondition triple for the phase-estimation program at an arbitrary real
phase `φ`, with the *good-outcome effect* `P_good` — the sum of the `2e+1`
computational-basis projectors `goodBits n b j`, `|j| ≤ e` (§7 below) — as
postcondition, and reads off `PostH(P_good) ≥ 1 − 1/(2(e−1))` at the intended
pure input state.

Honest scope of that endpoint. The operational statement is made **at the
intended input state, through the wp precondition**, and not as a universal
scaled-projector triple: `validTot {c·∣0,ψ⟩⟨0,ψ∣} qpeCir {P_good}` is *false* for
any success probability `c < 1`. Validity over **all** density operators ρ is
equivalent to the operator inequality `c·∣0,ψ⟩⟨0,ψ∣ ≤ wp(qpeCir)(P_good)`, and a
rank-one operator is dominated by `wp(qpeCir)(P_good)` only if the whole
bad-outcome subspace — where the wp effect has small (indeed zero) eigenvalues —
is orthogonal to `∣0,ψ⟩`, which is exactly what `c < 1` denies: an ρ supported
there refutes the inequality. That is why the operational endpoint is stated at
the intended input through the wp precondition rather than as a scaled projector.

Everything below is still a *state-level* identity about vectors, about the
inverse-Fourier operator, and about the indexing of basis outcomes; the passage
to a program statement happens in the example.

Contents:

* `qpeKickedKet n φ` — the **general (inexact-phase) kicked profile state**: the
  product state on the standard `n`-qubit world whose wire `j` carries the phase
  `2π·2^{n-1-j}·φ`, for an *arbitrary* real phase `φ` (in turns/2π). At an exact
  dyadic phase `φ = natVal x / 2^n` it is the Fourier state (`qpeKickedKet_natVal`),
  and it is the counting-block content of the verified stage-2 family
  (`prodV_qpePhasedFam_castSucc`).
* `inner_qpeKickedKet_prod` — **the crux**: the Hermitian overlap of two kicked
  profiles factorises wire-by-wire into the geometric product
  `∏_{j<n} (1 + e^{2πi·2^j·(φ−ψ)})/2`.
* `inner_deltav_iqftOp_qpeKickedKet` — the readout-amplitude form: the amplitude of
  the basis outcome `x` after the library IQFT is applied to a kicked profile *is*
  the Fourier overlap.
* `inner_qpeKickedKet` — **the bridge**: the overlap *is* the normalised geometric
  amplitude `qpeAmp (2^n) (φ − ψ)` of N&C (5.25) (`Qhl/Register/QPEPrecision.lean`),
  i.e. `qpeAmp` is the Fourier coefficient of the verified stage-2 kicked state
  along the exact-case profiles; `inner_fourierState_qpeKickedKet` reads it at a
  Fourier profile.
* `qpe_stage2_fourier_successBound` — **N&C (5.35) on those overlaps,
  hypothesis-free**: for an arbitrary eigenphase `φ` with `2^n·φ = b + δ`,
  `δ ∈ [0,1)`, the squared overlaps of the kicked state at `φ` with the profiles
  of the `2e+1` candidate estimates nearest `b` sum to at least `1 − 1/(2(e−1))`.
  This is the Fourier-side content of the QPE precision claim — still a statement
  about state overlaps.
* `qpeKickedKet_int_add`, `prodV_qpePhasedFamR_castSucc` (§6) — the kicked profile
  sees the phase only modulo `1`, and it *is* the counting block of the
  real-phase stage-2 family `qpePhasedFamR` (`Qhl/Register/Fourier.lean` §12):
  the hand-over point from a derivation at an arbitrary phase to the analysis.
* `goodBits`, `natVal_goodBits`, `goodBits_injOn` (§7) — the `2e+1` good estimates
  as **distinct computational-basis bit vectors** (`b + j` reduced mod `2^n`).
* `qpe_goodBits_successBound`, `qpe_readout_successBound` (§8) — N&C (5.35) at
  those basis kets: the squared readout amplitudes of the good outcomes, after
  the library IQFT, sum to at least `1 − 1/(2(e−1))`. This is the form the
  operational example consumes.
-/

namespace Qhl

open Finset
open scoped ComplexInnerProductSpace

/-! ## §1. The per-wire overlap of two phase kets -/

/-- The overlap of two phase kets: `⟪'ph a, 'ph b⟫ = (1 + e^{i(b−a)})/2`. This is
the single-wire content of `inner_qpeKickedKet_prod`. (Conjugate-linear in the
first argument, so it is the `a`-ket that is conjugated.) -/
private theorem inner_phaseKet (a b : ℝ) :
    ⟪phaseKet a, phaseKet b⟫ = (1 + Complex.exp (((b - a : ℝ) : ℂ) * Complex.I)) / 2 := by
  have hss : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = (2 : ℂ)⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have h1 : phaseKet b true * (starRingEnd ℂ) (phaseKet a true)
      = (2 : ℂ)⁻¹ * Complex.exp (((b - a : ℝ) : ℂ) * Complex.I) := by
    rw [phaseKet_apply_exp, phaseKet_apply_exp, map_mul, map_inv₀, Complex.conj_ofReal,
      ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_mul_mul_comm,
      hss, ← Complex.exp_add]
    congr 2
    push_cast [bitVal_true]
    ring
  have h0 : phaseKet b false * (starRingEnd ℂ) (phaseKet a false) = (2 : ℂ)⁻¹ := by
    rw [phaseKet_apply_exp, phaseKet_apply_exp, map_mul, map_inv₀, Complex.conj_ofReal,
      ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_mul_mul_comm,
      hss, ← Complex.exp_add]
    norm_num [bitVal_false]
  rw [PiLp.inner_apply, Fintype.sum_bool]
  simp only [RCLike.inner_apply]
  rw [h1, h0]
  ring

/-! ## §2. The kicked profile state -/

/-- **The general kicked profile state.** Wire `j` of the counting register
carries the phase `2π·2^{n-1-j}·φ` — the phase that the controlled `2^{n-1-j}`-th
power deposits on that wire — for an **arbitrary** real phase `φ` (turns divided
by `2π`), not necessarily an `n`-bit dyadic.

At an exact dyadic phase `φ = natVal x / 2^n` this state *is* the Fourier state
of `x` (`qpeKickedKet_natVal`), and it is exactly the counting-block content of
the verified stage-2 family `qpePhasedFam` (`prodV_qpePhasedFam_castSucc`). -/
noncomputable def qpeKickedKet (n : ℕ) (φ : ℝ) : HS (QubitD n) (univ : Finset (QubitL n)) :=
  prodV (QubitD n) (W := (univ : Finset (QubitL n)))
    (fun j => phaseKet (2 * Real.pi * ((2 : ℝ) ^ (n - 1 - (j : ℕ)) * φ)))

/-- The kicked profile is a unit vector: it is a product of phase kets. -/
@[simp]
theorem norm_qpeKickedKet (n : ℕ) (φ : ℝ) : ‖qpeKickedKet n φ‖ = 1 :=
  norm_prodV_eq_one _ fun _ => norm_phaseKet _

/-- **The exact case.** At the dyadic phase `φ = natVal x / 2^n` the kicked profile
is the Fourier state of `x`: wire by wire, the deposited phase `2π·2^{n-1-j}·natVal x/2^n`
is the QFT angle of that wire up to whole turns (`phaseKet_kick`). -/
theorem qpeKickedKet_natVal (n : ℕ) (x : Fin n → Bool) :
    qpeKickedKet n ((natVal x : ℝ) / 2 ^ n) = fourierState n x := by
  rw [qpeKickedKet, fourierState_eq_prodV]
  refine prodV_congr (QubitD n) fun j _ => ?_
  have hj : n - 1 - (j : ℕ) < n := by
    have := j.isLt
    omega
  have hang : 2 * Real.pi * ((2 : ℝ) ^ (n - 1 - (j : ℕ)) * ((natVal x : ℝ) / 2 ^ n))
      = ((2 ^ (n - 1 - (j : ℕ)) : ℕ) : ℝ) * (2 * Real.pi * ((natVal x : ℝ) / 2 ^ n)) := by
    push_cast
    ring
  rw [hang]
  exact phaseKet_kick n x hj

/-- **The verified stage-2 anchor.** The counting block of the stage-2 family
`qpePhasedFam` — the state the verified development provably reaches at the exact
phase `natVal x / 2^n` — is precisely the kicked profile at that phase. This is
the only point at which the precision analysis touches the verified development,
and it touches it read-only. -/
theorem prodV_qpePhasedFam_castSucc (n : ℕ) (x : Fin n → Bool) (ψ : 𝕢) :
    prodV (QubitD n) (W := (univ : Finset (QubitL n)))
        (fun j => qpePhasedFam n x ψ (Fin.castSucc j))
      = qpeKickedKet n ((natVal x : ℝ) / 2 ^ n) := by
  rw [qpeKickedKet_natVal, fourierState_eq_prodV]
  exact prodV_congr (QubitD n) fun j _ => qpePhasedFam_castSucc n x ψ j

/-! ## §3. The Fourier overlap of two kicked profiles -/

/-- **The overlap product formula.** The Hermitian overlap of the kicked profiles
at phases `ψ` and `φ` factorises wire by wire into the geometric product
`∏_{j<n} (1 + e^{2πi·2^j·(φ−ψ)})/2` — the finite geometric amplitude of the phase
difference `φ − ψ`. (Conjugate-linear in the first argument, so it is the `ψ`-ket
that is conjugated.) This is the state-level identity the precision analysis rests
on; it says nothing about any program. -/
theorem inner_qpeKickedKet_prod (n : ℕ) (ψ φ : ℝ) :
    ⟪qpeKickedKet n ψ, qpeKickedKet n φ⟫
      = ∏ j ∈ Finset.range n,
          ((1 + Complex.exp ((2 * Real.pi * ((2 : ℝ) ^ j * (φ - ψ)) : ℝ) * Complex.I)) / 2) := by
  classical
  have hwire : ∀ i : QubitL n,
      (⟪phaseKet (2 * Real.pi * ((2 : ℝ) ^ (n - 1 - (i : ℕ)) * ψ)),
          phaseKet (2 * Real.pi * ((2 : ℝ) ^ (n - 1 - (i : ℕ)) * φ))⟫ : ℂ)
        = (1 + Complex.exp ((2 * Real.pi * ((2 : ℝ) ^ (n - 1 - (i : ℕ)) * (φ - ψ)) : ℝ)
            * Complex.I)) / 2 := by
    intro i
    rw [inner_phaseKet,
      show (2 * Real.pi * ((2 : ℝ) ^ (n - 1 - (i : ℕ)) * φ)
              - 2 * Real.pi * ((2 : ℝ) ^ (n - 1 - (i : ℕ)) * ψ) : ℝ)
          = 2 * Real.pi * ((2 : ℝ) ^ (n - 1 - (i : ℕ)) * (φ - ψ)) from by ring]
  have hprod := prodV_inner (QubitD n) (W := (univ : Finset (QubitL n)))
    (fun j => phaseKet (2 * Real.pi * ((2 : ℝ) ^ (n - 1 - (j : ℕ)) * ψ)))
    (fun j => phaseKet (2 * Real.pi * ((2 : ℝ) ^ (n - 1 - (j : ℕ)) * φ)))
  rw [qpeKickedKet, qpeKickedKet, hprod]
  rw [Finset.prod_congr rfl fun (i : ↥(univ : Finset (QubitL n))) _ => hwire (i : QubitL n)]
  have hreindex : (∏ i : ↥(univ : Finset (QubitL n)),
        (1 + Complex.exp ((2 * Real.pi * ((2 : ℝ) ^ (n - 1 - ((i : QubitL n) : ℕ)) * (φ - ψ)) : ℝ)
          * Complex.I)) / 2)
      = ∏ j : Fin n,
        (1 + Complex.exp ((2 * Real.pi * ((2 : ℝ) ^ (n - 1 - (j : ℕ)) * (φ - ψ)) : ℝ)
          * Complex.I)) / 2 :=
    Fintype.prod_equiv (Equiv.subtypeUnivEquiv fun a : QubitL n => Finset.mem_univ a)
      _ _ fun _ => rfl
  rw [hreindex,
    Fin.prod_univ_eq_prod_range (fun j : ℕ =>
      (1 + Complex.exp ((2 * Real.pi * ((2 : ℝ) ^ (n - 1 - j) * (φ - ψ)) : ℝ) * Complex.I)) / 2) n]
  exact Finset.prod_range_reflect (fun j : ℕ =>
    (1 + Complex.exp ((2 * Real.pi * ((2 : ℝ) ^ j * (φ - ψ)) : ℝ) * Complex.I)) / 2) n

/-! ## §4. The readout-amplitude form -/

/-- **The readout amplitude is the Fourier overlap.** The amplitude of the
computational basis outcome `x` in the vector obtained by applying the library
inverse Fourier transform to the kicked profile at phase `φ` equals the overlap of
the exact Fourier profile of `x` with that kicked profile.

Honest scope: this is a **state-level identity about the IQFT operator** — the
adjoint moved across the inner product — and nothing more. By itself it is *not* a
statement about any program's measurement distribution; that step is taken in
`Qhl/Examples/QPEApproxTriple.lean`, which consumes it through
`qpe_readout_successBound` (§8). -/
theorem inner_deltav_iqftOp_qpeKickedKet (n : ℕ) (x : Fin n → Bool) (φ : ℝ) :
    ⟪deltav (QubitD n) (fun i => x (i : QubitL n)),
      (iqftOp n : HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
          HS (QubitD n) (univ : Finset (QubitL n))) (qpeKickedKet n φ)⟫
      = ⟪fourierState n x, qpeKickedKet n φ⟫ := by
  rw [coe_iqftOp, LinearMap.adjoint_inner_right, qftOp_deltav]

/-! ## §5. The bridge to the geometric amplitude `qpeAmp` (N&C 5.25/5.35) -/

/-- **The Fourier-overlap bridge.** The Hermitian overlap of two kicked profiles
is exactly the normalised geometric amplitude `qpeAmp (2^n)` (N&C (5.25),
`Qhl/Register/QPEPrecision.lean`) of their phase difference: `qpeAmp` genuinely
is the Fourier coefficient of the verified stage-2 kicked state along the
exact-case profiles. It is the overlap product formula
(`inner_qpeKickedKet_prod`) read at the `N = 2^n` product form of the amplitude
(`qpeAmp_two_pow_prod`). (Conjugate-linear in the first argument, so it is the
`ψ`-ket that is conjugated.) -/
theorem inner_qpeKickedKet (n : ℕ) (ψ φ : ℝ) :
    ⟪qpeKickedKet n ψ, qpeKickedKet n φ⟫ = qpeAmp (2 ^ n) (φ - ψ) := by
  rw [inner_qpeKickedKet_prod, qpeAmp_two_pow_prod]

/-- The bridge read at an exact Fourier profile: the overlap of the Fourier state
of `x` with the kicked profile at phase `φ` is `qpeAmp (2^n)` of the offset of
`φ` from the dyadic `natVal x / 2^n`. -/
theorem inner_fourierState_qpeKickedKet (n : ℕ) (x : Fin n → Bool) (φ : ℝ) :
    ⟪fourierState n x, qpeKickedKet n φ⟫
      = qpeAmp (2 ^ n) (φ - (natVal x : ℝ) / 2 ^ n) := by
  rw [← qpeKickedKet_natVal, inner_qpeKickedKet]

/-- **N&C (5.35) in Fourier-overlap form, hypothesis-free.** Write the eigenphase
as `2^n·φ = b + δ` with `b : ℤ` and `δ ∈ [0,1)` the sub-resolution part. The
squared Fourier overlaps of the kicked state at `φ` — the state the verified
stage 1–2 algebra produces wire-by-wire at an **arbitrary** phase — against the
kicked profiles at the `2e+1` candidate estimates `(b+j)/2^n`, `|j| ≤ e`, sum to
at least `1 − 1/(2(e−1))`. All hypotheses are discharged: the Parseval
normalisation is `qpeAmp_parseval`, the tail estimate is `qpeTailBound`.

Honest scope: for in-range estimates the profile `qpeKickedKet n ((b+j)/2^n)` is
exactly the inverse-QFT entry state that the verified readout stage maps to the
corresponding basis result in the exact case (`qpeKickedKet_natVal` +
`iqftOp_fourierState`), and `inner_deltav_iqftOp_qpeKickedKet` exhibits each
overlap as the basis-outcome amplitude of the IQFT-transformed kicked state.
This theorem is therefore the Fourier-side content of the QPE precision claim,
but it is by itself **not** a statement about any program's measurement-outcome
distribution at inexact `φ`. It is carried to basis-outcome form in §7–§8
(`qpe_readout_successBound`) and to a program statement in
`Qhl/Examples/QPEApproxTriple.lean` (see the module header for the scope of that
endpoint). -/
theorem qpe_stage2_fourier_successBound (n : ℕ) (φ : ℝ) (b : ℤ) (δ : ℝ)
    (hb : (b : ℝ) + δ = 2 ^ n * φ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (e : ℕ) (he : 2 ≤ e) (heN : 2 * e < 2 ^ n) :
    (1 : ℝ) - 1 / (2 * ((e : ℝ) - 1)) ≤
      ∑ j ∈ Finset.Icc (-(e : ℤ)) (e : ℤ),
        ‖⟪qpeKickedKet n (((b + j : ℤ) : ℝ) / 2 ^ n), qpeKickedKet n φ⟫‖ ^ 2 := by
  have hn0 : n ≠ 0 := by
    intro h
    subst h
    have h1 : 2 * e < 1 := by simpa using heN
    omega
  have hEven : Even (2 ^ n) := Nat.even_pow.mpr ⟨even_two, hn0⟩
  have key : ∀ j ∈ Finset.Icc (-(e : ℤ)) (e : ℤ),
      ‖⟪qpeKickedKet n (((b + j : ℤ) : ℝ) / 2 ^ n), qpeKickedKet n φ⟫‖ ^ 2
        = ‖qpeAmp (2 ^ n) (((j : ℝ) - δ) / ((2 ^ n : ℕ) : ℝ))‖ ^ 2 := by
    intro j _
    rw [inner_qpeKickedKet]
    have hcast : ((2 ^ n : ℕ) : ℝ) = (2 : ℝ) ^ n := by push_cast; ring
    have h2n : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    have harg : φ - ((b + j : ℤ) : ℝ) / 2 ^ n
        = -(((j : ℝ) - δ) / ((2 ^ n : ℕ) : ℝ)) := by
      rw [hcast]
      field_simp
      push_cast
      linarith
    rw [harg, norm_qpeAmp_neg]
  rw [Finset.sum_congr rfl key]
  exact qpeSuccessBound_unconditional (2 ^ n) hEven δ hδ0 hδ1 e he heN

/-! ## §6. Integer periodicity and the real-phase stage-2 anchor -/

/-- **A kicked profile only sees the phase modulo `1`.** Shifting `φ` by an
integer shifts every wire angle `2π·2^{n-1-j}·φ` by an integer number of whole
turns, which a phase ket does not see (`phaseKet_add_int_mul_two_pi`). This is
the state-level reason a phase-estimation readout can only ever determine the
fractional part of the phase. -/
theorem qpeKickedKet_int_add (n : ℕ) (φ : ℝ) (N : ℤ) :
    qpeKickedKet n (φ + N) = qpeKickedKet n φ := by
  rw [qpeKickedKet, qpeKickedKet]
  refine prodV_congr (QubitD n) fun j _ => ?_
  have h : 2 * Real.pi * ((2 : ℝ) ^ (n - 1 - (j : ℕ)) * (φ + (N : ℝ)))
      = 2 * Real.pi * ((2 : ℝ) ^ (n - 1 - (j : ℕ)) * φ)
        + (((2 ^ (n - 1 - (j : ℕ)) * N : ℤ)) : ℝ) * (2 * Real.pi) := by
    push_cast
    ring
  rw [h, phaseKet_add_int_mul_two_pi]

/-- **The real-phase stage-2 anchor.** The counting block of the *inexact-phase*
stage-2 family `qpePhasedFamR` (`Qhl/Register/Fourier.lean` §12) — the state the
kickback loop reaches at an **arbitrary** real phase `φ` — is precisely the
kicked profile at that phase. This is the inexact-phase counterpart of
`prodV_qpePhasedFam_castSucc`, and the point at which an operational
approximate-QPE derivation hands its stage-2 state to the precision analysis. -/
theorem prodV_qpePhasedFamR_castSucc (n : ℕ) (φ : ℝ) (ψ : 𝕢) :
    prodV (QubitD n) (W := (univ : Finset (QubitL n)))
        (fun j => qpePhasedFamR n φ ψ (Fin.castSucc j))
      = qpeKickedKet n φ := by
  rw [qpeKickedKet]
  exact prodV_congr (QubitD n) fun j _ => qpePhasedFamR_castSucc n φ ψ j

/-! ## §7. The good outcomes as computational-basis bit vectors -/

/-- **The `j`-th good outcome.** N&C (5.35) bounds the total weight of the `2e+1`
candidate estimates `b + j`, `|j| ≤ e`, nearest the true scaled phase. As a
*readout result* such an estimate is the `n`-bit vector of `b + j` reduced modulo
`2^n` — the counting register holds `n` bits, so estimates wrap. `goodBits n b j`
is that bit vector; `natVal_goodBits` identifies its value. -/
noncomputable def goodBits (n : ℕ) (b j : ℤ) : Fin n → Bool :=
  (natValEquiv n).symm ⟨((b + j) % (2 ^ n : ℕ)).toNat, by
    have key : ∀ r : ℤ, 0 ≤ r → r < ((2 ^ n : ℕ) : ℤ) → r.toNat < 2 ^ n := by
      intro r h0 hlt
      omega
    exact key _ (Int.emod_nonneg _ (by positivity)) (Int.emod_lt_of_pos _ (by positivity))⟩

/-- The value of the `j`-th good outcome is `b + j` reduced modulo `2^n`. -/
theorem natVal_goodBits (n : ℕ) (b j : ℤ) :
    (natVal (goodBits n b j) : ℤ) = (b + j) % (2 ^ n : ℕ) := by
  have h : natVal (goodBits n b j) = ((b + j) % ((2 ^ n : ℕ) : ℤ)).toNat := by
    rw [goodBits, ← natValEquiv_val, Equiv.apply_symm_apply]
  rw [h]
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity))

/-- **The good outcomes are distinct.** As long as the window is strictly inside
one period, `2e < 2^n`, the `2e+1` estimates `b + j`, `|j| ≤ e`, reduce to
`2e+1` *distinct* bit vectors — no two of them wrap onto each other. This is what
lets a sum over `j` be read as a sum over disjoint measurement outcomes. -/
theorem goodBits_injOn (n : ℕ) (b : ℤ) {e : ℕ} (heN : 2 * e < 2 ^ n) :
    Set.InjOn (goodBits n b) ↑(Finset.Icc (-(e : ℤ)) (e : ℤ)) := by
  intro j hj j' hj' h
  rw [Finset.mem_coe, Finset.mem_Icc] at hj hj'
  have hmod : Int.ModEq ((2 ^ n : ℕ) : ℤ) (b + j) (b + j') := by
    change (b + j) % ((2 ^ n : ℕ) : ℤ) = (b + j') % ((2 ^ n : ℕ) : ℤ)
    rw [← natVal_goodBits, ← natVal_goodBits, h]
  have hdvd : ((2 ^ n : ℕ) : ℤ) ∣ j' - j := by
    have hd := hmod.dvd
    rwa [show b + j' - (b + j) = j' - j from by ring] at hd
  have hnat : ((2 ^ n : ℕ) : ℤ).natAbs = 2 ^ n := by simp
  have hz : j' - j = 0 := by
    refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd ?_
    omega
  omega

/-- **The good-outcome overlap is a candidate-profile overlap.** The Fourier
profile of the bit vector `goodBits n b j` has exactly the same overlap with the
kicked state at `φ` as the (possibly out-of-range) candidate profile at
`(b+j)/2^n` that N&C (5.35) bounds: the two phases differ by the integer
`(b+j) / 2^n`, invisible to a phase ket (`qpeKickedKet_int_add`), and at the
in-range remainder the kicked profile *is* the Fourier state
(`qpeKickedKet_natVal`). -/
theorem fourierState_goodBits_overlap (n : ℕ) (φ : ℝ) (b j : ℤ) :
    ⟪fourierState n (goodBits n b j), qpeKickedKet n φ⟫
      = ⟪qpeKickedKet n (((b + j : ℤ) : ℝ) / 2 ^ n), qpeKickedKet n φ⟫ := by
  have hint : (b + j : ℤ)
      = (natVal (goodBits n b j) : ℤ)
        + ((2 ^ n : ℕ) : ℤ) * ((b + j) / ((2 ^ n : ℕ) : ℤ)) := by
    rw [natVal_goodBits]
    linarith [Int.mul_ediv_add_emod (b + j) ((2 ^ n : ℕ) : ℤ)]
  have hreal : ((b + j : ℤ) : ℝ)
      = (natVal (goodBits n b j) : ℝ)
        + (2 : ℝ) ^ n * ((((b + j) / ((2 ^ n : ℕ) : ℤ) : ℤ)) : ℝ) := by
    have hc := congrArg (fun z : ℤ => (z : ℝ)) hint
    push_cast at hc ⊢
    linarith
  have h2n : ((2 : ℝ) ^ n) ≠ 0 := by positivity
  have hdiv : ((b + j : ℤ) : ℝ) / 2 ^ n
      = (natVal (goodBits n b j) : ℝ) / 2 ^ n
        + ((((b + j) / ((2 ^ n : ℕ) : ℤ) : ℤ)) : ℝ) := by
    rw [hreal]
    field_simp
  have hvec : qpeKickedKet n (((b + j : ℤ) : ℝ) / 2 ^ n)
      = fourierState n (goodBits n b j) := by
    rw [hdiv, qpeKickedKet_int_add, qpeKickedKet_natVal]
  rw [hvec]

/-! ## §8. N&C (5.35) at computational-basis readout kets -/

/-- **N&C (5.35) at the good-outcome Fourier profiles.** The same bound as
`qpe_stage2_fourier_successBound`, but with the candidate profiles replaced by
the Fourier states of the `2e+1` *bit vectors* `goodBits n b j` — genuine
`n`-qubit computational-basis labels (distinct, by `goodBits_injOn`), which is
the form a readout statement needs. -/
theorem qpe_goodBits_successBound (n : ℕ) (φ : ℝ) (b : ℤ) (δ : ℝ)
    (hb : (b : ℝ) + δ = 2 ^ n * φ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (e : ℕ) (he : 2 ≤ e) (heN : 2 * e < 2 ^ n) :
    (1 : ℝ) - 1 / (2 * ((e : ℝ) - 1)) ≤
      ∑ j ∈ Finset.Icc (-(e : ℤ)) (e : ℤ),
        ‖⟪fourierState n (goodBits n b j), qpeKickedKet n φ⟫‖ ^ 2 := by
  rw [Finset.sum_congr rfl fun j _ => congrArg (fun z : ℂ => ‖z‖ ^ 2)
    (fourierState_goodBits_overlap n φ b j)]
  exact qpe_stage2_fourier_successBound n φ b δ hb hδ0 hδ1 e he heN

/-- **N&C (5.35) as a readout-amplitude bound.** After the library inverse QFT is
applied to the kicked profile at an arbitrary phase `φ` with `2^n·φ = b + δ`,
`δ ∈ [0,1)`, the squared amplitudes of the `2e+1` computational-basis outcomes
`goodBits n b j`, `|j| ≤ e`, sum to at least `1 − 1/(2(e−1))`.

This is the form an operational approximate-QPE triple consumes: the summands are
Born weights of *basis outcomes* of the readout register, indexed by honest bit
vectors. See `Qhl/Examples/QPEApproxTriple.lean`. -/
theorem qpe_readout_successBound (n : ℕ) (φ : ℝ) (b : ℤ) (δ : ℝ)
    (hb : (b : ℝ) + δ = 2 ^ n * φ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (e : ℕ) (he : 2 ≤ e) (heN : 2 * e < 2 ^ n) :
    (1 : ℝ) - 1 / (2 * ((e : ℝ) - 1)) ≤
      ∑ j ∈ Finset.Icc (-(e : ℤ)) (e : ℤ),
        ‖⟪deltav (QubitD n) (fun i => goodBits n b j (i : QubitL n)),
            (iqftOp n : HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
                HS (QubitD n) (univ : Finset (QubitL n))) (qpeKickedKet n φ)⟫‖ ^ 2 := by
  rw [Finset.sum_congr rfl fun j _ => congrArg (fun z : ℂ => ‖z‖ ^ 2)
    (inner_deltav_iqftOp_qpeKickedKet n (goodBits n b j) φ)]
  exact qpe_goodBits_successBound n φ b δ hb hδ0 hδ1 e he heN

end Qhl
