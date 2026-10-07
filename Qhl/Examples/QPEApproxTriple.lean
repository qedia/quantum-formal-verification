import Qhl.Examples.QPETriple
import Qhl.Register.QPEPrecisionBridge
import Qhl.Logic.WpChain

/-! # Approximate QPE (placeholder header) -/

namespace Qhl.QPEApproxTriple

open Finset
open scoped ComplexInnerProductSpace
open Qhl.QPETriple

/-! ## §0. The bounded straight-line rendering of the QPE circuit (local)

`Qhl/Examples/QPETriple.lean` renders the two QPE loops as genuine counted
`while` loops (`countedProg`, `σT = ℕ`). The weakest-precondition fold of §4
and the forward chain of §5 below analyse the **bounded straight-line**
rendering of the same circuit — the `for`-fold over the counting cells, CoqQ's
`QPE` (`example.v:1001-1005`) — so that rendering is kept here, locally, with
its uniform-superposition stage triple `phDerivF`. Stage for stage the gates
are identical to `phCtrl`/`kickCir`/`iqftCtrl`; only the loop rendering
differs. -/

/-- The uniform-superposition stage as a `for`-fold — CoqQ `[ut x := 'Hn]`. -/
noncomputable def phCtrlF (n : ℕ) : Prog Unit (QubitD (n + 1)) :=
  [for a in (List.finRange n).map Fin.castSucc do [ut a := H]]

/-- The phase-kickback stage as a `for`-fold — CoqQ `[ut (x,y) := Uf]`,
`Uf = Multiplexer (fun i => U ^+ i)`. -/
noncomputable def kickCirF (n : ℕ) (U : UnitaryOp 𝕢) : Prog Unit (QubitD (n + 1)) :=
  [for k < n do
    Prog.unitary2 k.castSucc (Fin.last n) (castSucc_ne_last k)
      (control (U ^ 2 ^ (n - 1 - (k : ℕ))))]

/-- The readout stage — CoqQ `[ut x := IQFT]`: the whole `n`-qubit inverse
Fourier transform as ONE gate, at `σT = Unit`. -/
noncomputable def iqftCtrlF (n : ℕ) : Prog Unit (QubitD (n + 1)) :=
  .unitary n (RegExpr.const (ctrlReg n)) fun _ => iqftGate n

/-- CoqQ `QPE` (`example.v:1001`), straight-line rendering. -/
noncomputable def qpeCirF (n : ℕ) (U : UnitaryOp 𝕢) : Prog Unit (QubitD (n + 1)) :=
  (phCtrlF n).seq ((kickCirF n U).seq (iqftCtrlF n))

/-- Stage 1 of the straight-line rendering —
`{∣0⟩^n ⊗ ψ} phCtrlF {∣+⟩^n ⊗ ψ}`: ONE call of the parallel rule `AxV_UTFP`
(`DerivTot.forProg_parallelUnitary`) at the counting cells; the target cell is
not in the loop list, hence framed. -/
theorem phDerivF (n : ℕ) (ψ : 𝕢) (hψ : ‖ψ‖ = 1) :
    DerivTot (σT := Unit)
      (prodA (QubitD (n + 1)) (qpeInitFam n ψ) (norm_qpeInitFam n ψ hψ))
      (phCtrlF n)
      (prodA (QubitD (n + 1)) (qpePlusFam n ψ) (norm_qpePlusFam n ψ hψ)) :=
  DerivTot.prodForward
    (hφ := norm_applyOn ((List.finRange n).map Fin.castSucc) (fun _ => H)
      (qpeInitFam n ψ) (norm_qpeInitFam n ψ hψ))
    (DerivTot.forProg_parallelUnitary ((List.finRange n).map Fin.castSucc)
      ((List.nodup_finRange n).map (Fin.castSucc_injective n))
      (fun _ => H) (qpeInitFam n ψ) (norm_qpeInitFam n ψ hψ))
    (applyOn_castSucc_H n ψ)

/-! ## §1. The good-outcome effect -/

/-- The `(j, c)`-th good basis ket. -/
noncomputable def goodKet (n : ℕ) (b j : ℤ) (c : Bool) :
    HS (QubitD (n + 1)) (univ : Finset (QubitL (n + 1))) :=
  deltav (QubitD (n + 1))
    (fun i => if h : ((i : QubitL (n + 1)) : ℕ) < n
      then goodBits n b j ⟨((i : QubitL (n + 1)) : ℕ), h⟩ else c)

/-- Distinct labels give distinct basis kets. -/
theorem inner_goodKet (n : ℕ) (b : ℤ) {e : ℕ} (heN : 2 * e < 2 ^ n) (p q : ℤ × Bool)
    (hp : p.1 ∈ Finset.Icc (-(e : ℤ)) (e : ℤ)) (hq : q.1 ∈ Finset.Icc (-(e : ℤ)) (e : ℤ)) :
    (⟪goodKet n b p.1 p.2, goodKet n b q.1 q.2⟫ : ℂ) = if p = q then 1 else 0 := by
  rw [goodKet, goodKet]
  refine (dv_dot (QubitD (n + 1)) _ _).trans ?_
  by_cases hpq : p = q
  · rw [if_pos hpq, if_pos (by rw [hpq])]
  · rw [if_neg hpq, if_neg]
    intro h
    refine hpq ?_
    have hc : p.2 = q.2 := by simpa using congrFun h ⟨Fin.last n, mem_univ _⟩
    have hbits : goodBits n b p.1 = goodBits n b q.1 := by
      funext t
      simpa using congrFun h ⟨Fin.castSucc t, mem_univ _⟩
    exact Prod.ext (goodBits_injOn n b heN (Finset.mem_coe.mpr hp) (Finset.mem_coe.mpr hq) hbits)
      hc

/-- The good-outcome effect. -/
noncomputable def goodOp (n : ℕ) (b : ℤ) (e : ℕ) :
    EndM (QubitD (n + 1)) (univ : Finset (QubitL (n + 1))) :=
  ∑ p ∈ (Finset.Icc (-(e : ℤ)) (e : ℤ)) ×ˢ (univ : Finset Bool),
    outerLM (goodKet n b p.1 p.2) (goodKet n b p.1 p.2)

theorem isEffect_goodOp (n : ℕ) (b : ℤ) (e : ℕ) (heN : 2 * e < 2 ^ n) :
    IsEffect (goodOp n b e) :=
  isEffect_sum_outerLM_of_orthonormal
    ((Finset.Icc (-(e : ℤ)) (e : ℤ)) ×ˢ (univ : Finset Bool))
    (fun p : ℤ × Bool => goodKet n b p.1 p.2)
    fun p hp q hq => inner_goodKet n b heN p q (Finset.mem_product.mp hp).1
      (Finset.mem_product.mp hq).1

/-- The good-outcome assertion. -/
noncomputable def goodA (n : ℕ) (b : ℤ) (e : ℕ) (heN : 2 * e < 2 ^ n) :
    Assn Unit (QubitD (n + 1)) :=
  ⟨fun _ => goodOp n b e, fun _ => isEffect_goodOp n b e heN⟩

@[simp]
theorem goodA_op (n : ℕ) (b : ℤ) (e : ℕ) (heN : 2 * e < 2 ^ n) (σ : Unit) :
    (goodA n b e heN).op σ = goodOp n b e := rfl

/-! ## §2. The output state and the input state -/

/-- The state the circuit reaches at an arbitrary real phase. -/
noncomputable def qpeOutR (n : ℕ) (φ : ℝ) (ψ : 𝕢) :
    HS (QubitD (n + 1)) (univ : Finset (QubitL (n + 1))) :=
  regLift (ctrlReg n)
    (iqftGate n : TSpace (QubitD (n + 1)) (ctrlReg n).toFun →ₗ[ℂ]
        TSpace (QubitD (n + 1)) (ctrlReg n).toFun)
    (prodV (QubitD (n + 1)) (W := (univ : Finset (QubitL (n + 1)))) (qpePhasedFamR n φ ψ))

theorem norm_qpeOutR (n : ℕ) (φ : ℝ) (ψ : 𝕢) (hψ : ‖ψ‖ = 1) : ‖qpeOutR n φ ψ‖ = 1 := by
  rw [qpeOutR, norm_apply_of_isUnitary (isUnitary_regLift (ctrlReg n) (iqftGate n)),
    norm_prodV_eq_one _ (norm_qpePhasedFamR n φ ψ hψ)]

/-- The intended input state. -/
noncomputable def inputState (n : ℕ) (ψ : 𝕢) : CQState Unit (QubitD (n + 1)) :=
  ⟨(), PDensity.pure
    (prodV (QubitD (n + 1)) (W := (univ : Finset (QubitL (n + 1)))) (qpeInitFam n ψ))⟩

theorem mass_inputState (n : ℕ) (ψ : 𝕢) (hψ : ‖ψ‖ = 1) : (inputState n ψ).q.mass = 1 :=
  PDensity.mass_pure (norm_prodV_eq_one _ (norm_qpeInitFam n ψ hψ))

/-! ## §3. Part 1 — the evolution triple at an arbitrary real phase -/

section Evolution

variable (n : ℕ) (φ : ℝ) (U : UnitaryOp 𝕢) (ψ : 𝕢) (hψ : ‖ψ‖ = 1)

variable (hU : (U : 𝕢 →ₗ[ℂ] 𝕢) ψ
    = Complex.exp (((2 * Real.pi * φ : ℝ) : ℂ) * Complex.I) • ψ)

include hU in
/-- Stage 2 at an arbitrary real phase. -/
theorem kickDerivR :
    DerivTot (σT := Unit)
      (prodA (QubitD (n + 1)) (qpePlusFam n ψ) (norm_qpePlusFam n ψ hψ))
      (kickCirF n U)
      (prodA (QubitD (n + 1)) (qpePhasedFamR n φ ψ) (norm_qpePhasedFamR n φ ψ hψ)) :=
  DerivTot.forProg_prodChain (qpeKickFamR n φ ψ) (norm_qpeKickFamR n φ ψ hψ)
    (qpeKickFamR_zero n φ ψ) (qpeKickFamR_full n φ ψ)
    fun k => DerivTot.prodRung_pair k.castSucc (Fin.last n) (castSucc_ne_last k)
      (control (U ^ 2 ^ (n - 1 - (k : ℕ))))
      (qpeKickFamR n φ ψ (k : ℕ)) (norm_qpeKickFamR n φ ψ hψ (k : ℕ))
      (qpeKickFamR_step n φ ψ k)
      (by
        have hangle : ((2 ^ (n - 1 - (k : ℕ)) : ℕ) : ℝ) * (2 * Real.pi * φ)
            = 2 * Real.pi * ((2 : ℝ) ^ (n - 1 - (k : ℕ)) * φ) := by
          push_cast
          ring
        rw [qpeKickFamR_ctrl, qpeKickFamR_last, ← phaseKet_zero,
          control_pow_vpair_phaseKet U hU (2 ^ (n - 1 - (k : ℕ))) 0, zero_add, hangle])
      (norm_phaseKet _) hψ (norm_qpeKickFamR n φ ψ hψ ((k : ℕ) + 1))

/-- Stage 3 at an arbitrary real phase. -/
theorem iqftCtrlDerivR :
    DerivTot (σT := Unit)
      (prodA (QubitD (n + 1)) (qpePhasedFamR n φ ψ) (norm_qpePhasedFamR n φ ψ hψ))
      (iqftCtrlF n)
      (Assn.ofState (qpeOutR n φ ψ) (norm_qpeOutR n φ ψ hψ)) :=
  DerivTot.unitary_state (ctrlReg n) (iqftGate n)
    (norm_prodV_eq_one _ (norm_qpePhasedFamR n φ ψ hψ)) (norm_qpeOutR n φ ψ hψ) rfl

include hU in
/-- **Part 1** — the evolution triple. -/
theorem qpeApproxEvolDeriv :
    DerivTot (σT := Unit)
      (prodA (QubitD (n + 1)) (qpeInitFam n ψ) (norm_qpeInitFam n ψ hψ))
      (qpeCirF n U)
      (Assn.ofState (qpeOutR n φ ψ) (norm_qpeOutR n φ ψ hψ)) :=
  DerivTot.seq (phDerivF n ψ hψ)
    (DerivTot.seq (kickDerivR n φ U ψ hψ hU) (iqftCtrlDerivR n φ ψ hψ))

include hU in
/-- **Part 1, semantically.** -/
theorem qpeApproxEvolValid :
    validTot (σT := Unit)
      (prodA (QubitD (n + 1)) (qpeInitFam n ψ) (norm_qpeInitFam n ψ hψ))
      (qpeCirF n U)
      (Assn.ofState (qpeOutR n φ ψ) (norm_qpeOutR n φ ψ hψ)) :=
  (qpeApproxEvolDeriv n φ U ψ hψ hU).sound

end Evolution

/-! ## §4. Part 3 — the integrated weakest-precondition triple -/

/-- The (Ax-Uni) transformer chain of the good-outcome effect. -/
noncomputable def qpeApproxPre (n : ℕ) (U : UnitaryOp 𝕢) (b : ℤ) (e : ℕ)
    (heN : 2 * e < 2 ^ n) : Assn Unit (QubitD (n + 1)) :=
  ((List.finRange n).map Fin.castSucc).foldr
    (fun a A => A.unitaryPre (fun _ (_ : Fin 1) => a)
      (fun _ => singleGate (QubitD (n + 1)) a H))
    ((List.finRange n).foldr
      (fun k A => A.unitaryPre
        (RegExpr.const (Reg.pair k.castSucc (Fin.last n) (castSucc_ne_last k)))
        (fun _ => pairGate k.castSucc (Fin.last n) (castSucc_ne_last k)
          (control (U ^ 2 ^ (n - 1 - (k : ℕ))))))
      ((goodA n b e heN).unitaryPre (RegExpr.const (ctrlReg n)) (fun _ => iqftGate n)))

/-- The Hadamard stage under the (Ax-Uni) fold — the `for`-skeleton rule
`DerivTot.forProg` at the counting cells, for an arbitrary postcondition. -/
theorem phCtrl_wp (n : ℕ) (A : Assn Unit (QubitD (n + 1))) :
    DerivTot (σT := Unit)
      (((List.finRange n).map Fin.castSucc).foldr
        (fun a A => A.unitaryPre (fun _ (_ : Fin 1) => a)
          (fun _ => singleGate (QubitD (n + 1)) a H)) A)
      (phCtrlF n) A :=
  DerivTot.forProg (fun (_ : QubitL (n + 1)) B => DerivTot.unitary _ _ B) _ _

/-- The kickback stage under the (Ax-Uni) fold, for an arbitrary
postcondition. -/
theorem kickCir_wp (n : ℕ) (U : UnitaryOp 𝕢) (A : Assn Unit (QubitD (n + 1))) :
    DerivTot (σT := Unit)
      ((List.finRange n).foldr
        (fun k A => A.unitaryPre
          (RegExpr.const (Reg.pair k.castSucc (Fin.last n) (castSucc_ne_last k)))
          (fun _ => pairGate k.castSucc (Fin.last n) (castSucc_ne_last k)
            (control (U ^ 2 ^ (n - 1 - (k : ℕ)))))) A)
      (kickCirF n U) A :=
  DerivTot.forProg (fun (_ : Fin n) B => DerivTot.unitary _ _ B) _ _

/-- **Part 3** — the integrated wp derivation. -/
theorem qpeApproxDeriv (n : ℕ) (U : UnitaryOp 𝕢) (b : ℤ) (e : ℕ) (heN : 2 * e < 2 ^ n) :
    DerivTot (σT := Unit) (qpeApproxPre n U b e heN) (qpeCirF n U) (goodA n b e heN) :=
  DerivTot.seq (phCtrl_wp n _)
    (DerivTot.seq (kickCir_wp n U _)
      (DerivTot.unitary (RegExpr.const (ctrlReg n)) (fun _ => iqftGate n)
        (goodA n b e heN)))

/-- **Part 3, semantically.** -/
theorem qpeApproxValid (n : ℕ) (U : UnitaryOp 𝕢) (b : ℤ) (e : ℕ) (heN : 2 * e < 2 ^ n) :
    validTot (σT := Unit) (qpeApproxPre n U b e heN) (qpeCirF n U) (goodA n b e heN) :=
  (qpeApproxDeriv n U b e heN).sound

/-! ## §5. The evolved state, stage by stage

`qpeApproxPre` is the *backward* (Ax-Uni) fold; `Qhl/Logic/WpChain.lean` §3
displays it as one conjugation by the **forward** semantic operator
`chainOp` of the gate list. The three lemmas below evaluate that forward
operator on the intended input — they are the `chainOp` mirrors of the three
stage triples of §3, proved from the very same library step laws (`applyOn`,
`qpeKickFamR_step`, the definition of `qpeOutR`), so no new state algebra is
introduced. -/

/-- **Stage 1, forward.** The chain of Hadamards on the counting cells sends the
all-zeros counting block to the uniform superposition; the gates are on pairwise
distinct wires (`Nodup`), so the whole chain collapses to `applyOn`. -/
theorem chainOp_phCtrl (n : ℕ) (ψ : 𝕢) :
    chainOp ((List.finRange n).map Fin.castSucc)
        (fun a => regLift (Reg.single a)
          (singleGate (QubitD (n + 1)) a H :
            TSpace (QubitD (n + 1)) (Reg.single a).toFun →ₗ[ℂ]
              TSpace (QubitD (n + 1)) (Reg.single a).toFun))
        (prodV (QubitD (n + 1)) (W := (univ : Finset (QubitL (n + 1)))) (qpeInitFam n ψ))
      = prodV (QubitD (n + 1)) (W := (univ : Finset (QubitL (n + 1)))) (qpePlusFam n ψ) := by
  rw [chainOp_single_prodV ((List.finRange n).map Fin.castSucc)
      ((List.nodup_finRange n).map (Fin.castSucc_injective n)) (fun _ => H) (qpeInitFam n ψ),
    applyOn_castSucc_H n ψ]

section EvolChain

variable (n : ℕ) (φ : ℝ) (U : UnitaryOp 𝕢) (ψ : 𝕢)

variable (hU : (U : 𝕢 →ₗ[ℂ] 𝕢) ψ
    = Complex.exp (((2 * Real.pi * φ : ℝ) : ℂ) * Complex.I) • ψ)

include hU in
/-- **Stage 2, forward.** One `chainOp_finRange_family` call along the library
invariant `qpeKickFamR`: each rung is one two-cell frame step
(`regLift_pairGate_prodV`) whose gate obligation is the library phase kickback
`control_pow_vpair_phaseKet` — literally the obligation `kickDerivR` discharges,
here consumed on the semantic operator instead of on the triple. -/
theorem chainOp_kickCir :
    chainOp (List.finRange n)
        (fun k : Fin n => regLift (Reg.pair k.castSucc (Fin.last n) (castSucc_ne_last k))
          (pairGate (D := QubitD (n + 1)) k.castSucc (Fin.last n) (castSucc_ne_last k)
            (control (U ^ 2 ^ (n - 1 - (k : ℕ))))))
        (prodV (QubitD (n + 1)) (W := (univ : Finset (QubitL (n + 1)))) (qpePlusFam n ψ))
      = prodV (QubitD (n + 1)) (W := (univ : Finset (QubitL (n + 1))))
          (qpePhasedFamR n φ ψ) := by
  have key := chainOp_finRange_family
    (D := QubitD (n + 1))
    (fun k : Fin n => regLift (Reg.pair k.castSucc (Fin.last n) (castSucc_ne_last k))
      (pairGate (D := QubitD (n + 1)) k.castSucc (Fin.last n) (castSucc_ne_last k)
        (control (U ^ 2 ^ (n - 1 - (k : ℕ))))))
    (fun m => prodV (QubitD (n + 1)) (W := (univ : Finset (QubitL (n + 1))))
      (qpeKickFamR n φ ψ m))
    (fun k => by
      have hangle : ((2 ^ (n - 1 - (k : ℕ)) : ℕ) : ℝ) * (2 * Real.pi * φ)
          = 2 * Real.pi * ((2 : ℝ) ^ (n - 1 - (k : ℕ)) * φ) := by
        push_cast
        ring
      have hG : (control (U ^ 2 ^ (n - 1 - (k : ℕ))) :
            EuclideanSpace ℂ (Bool × Bool) →ₗ[ℂ] EuclideanSpace ℂ (Bool × Bool))
          (vpair (qpeKickFamR n φ ψ (k : ℕ) k.castSucc)
            (qpeKickFamR n φ ψ (k : ℕ) (Fin.last n)))
          = vpair (phaseKet (2 * Real.pi * ((2 : ℝ) ^ (n - 1 - (k : ℕ)) * φ))) ψ := by
        rw [qpeKickFamR_ctrl, qpeKickFamR_last, ← phaseKet_zero,
          control_pow_vpair_phaseKet U hU (2 ^ (n - 1 - (k : ℕ))) 0, zero_add, hangle]
      rw [regLift_pairGate_prodV k.castSucc (Fin.last n) (castSucc_ne_last k)
        (control (U ^ 2 ^ (n - 1 - (k : ℕ)))) (qpeKickFamR n φ ψ (k : ℕ)) hG,
        qpeKickFamR_step n φ ψ k])
  rw [qpeKickFamR_zero] at key
  rw [key, qpeKickFamR_full]

end EvolChain

/-- **Stage 3, forward.** The readout stage is the *definition* of `qpeOutR`. -/
theorem regLift_iqftCtrl (n : ℕ) (φ : ℝ) (ψ : 𝕢) :
    regLift (ctrlReg n)
        (iqftGate n : TSpace (QubitD (n + 1)) (ctrlReg n).toFun →ₗ[ℂ]
          TSpace (QubitD (n + 1)) (ctrlReg n).toFun)
        (prodV (QubitD (n + 1)) (W := (univ : Finset (QubitL (n + 1))))
          (qpePhasedFamR n φ ψ))
      = qpeOutR n φ ψ := rfl

end Qhl.QPEApproxTriple
