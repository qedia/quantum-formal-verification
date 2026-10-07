import Qhl.Register.IsingDiag
import Qhl.Gate.Rx
import Qhl.HSpace.OperatorExp

/-!
# The transverse-field Ising model: the two slice layers and their spectra

The operator layer of the Trotterized transverse-field Ising example
(`Qhl/Examples/TrotterTFIMTriple.lean`). The Hamiltonian is

```
H  =  H_X + H_ZZ,
H_X  = Σ_{j<n}   a j · X_j,          H_ZZ = Σ_{j<n-1} b j · Z_j Z_{j+1},
```

whose two parts do **not** commute, so the first-order product formula
`(e^{-iφ H_ZZ} e^{-iφ H_X})^N` is a genuine approximant, not the exact
evolution. One slice of the product formula is realised by one elementary
rotation per Hamiltonian term; this file defines the two **layer operators**
of a slice, as composites of the lifted rotations:

* `aPart k` — the composite of the first `k` lifted `Rx(2·(a j)·φ)` gates,
  `AOp φ = aPart n` the whole `X` layer;
* `bPart k` — the composite of the first `k` lifted `Rzz(2·(b j)·φ)` gates,
  `BOp φ = bPart (n-1)` the whole `ZZ` layer;
* `WOp φ = BOp φ ∘ AOp φ` — one slice, and `wIter φ ψ k = (WOp φ)^k ψ` its
  `k`-fold application (the state after `k` slices).

and proves the two **layer characterizations** — the mathematical content
justifying the reading `WOp φ = e^{-iφ H_ZZ} e^{-iφ H_X}`:

* `BOp_deltav` — the `ZZ` layer is the diagonal phase operator of the
  coupling energy: `BOp φ ∣y⟩ = e^{-iφ·E_ZZ(y)} ∣y⟩` with
  `E_ZZ(y) = Σ_{j<n-1} (b j)·z(y_j)z(y_{j+1})` (`coupleE` of
  `Qhl/Register/IsingDiag.lean`) — i.e. `BOp φ = e^{-iφ H_ZZ}`, since `H_ZZ`
  is diagonal with spectrum `E_ZZ` on the computational basis;
* `AOp_pmState` — the `X` layer is diagonal in the `±` **product basis**:
  `AOp φ (⊗_j ∣±_{s j}⟩) = e^{-iφ·E_X(s)} (⊗_j ∣±_{s j}⟩)` with
  `E_X(s) = Σ_{j<n} (a j)·z(s j)` (`xEnergy`) — i.e. `AOp φ = e^{-iφ H_X}`,
  since `H_X` is diagonal with spectrum `E_X` on the `X`-eigenbasis
  `pmKet` (`Qhl/Gate/Rx.lean`).

Everything is generic in the coefficients; no program and no example fixture
occurs. The **Trotter limit/error** `WOp(θ/N)^N → e^{-iθH}` is *not* part of
this library: only the exact algebra of the layers is.
-/

namespace Qhl

open Finset

section Model

variable (n : ℕ) (ca : Fin n → ℝ) (cb : Fin (n - 1) → ℝ)

/-! ## §1. The lifted slice gates -/

/-- The lifted transverse-field rotation at site `j`:
`Rx(2·(a j)·φ) = e^{-iφ·(a j)·X_j}`, extended to the whole world. -/
noncomputable def xGate (φ : ℝ) (j : Fin n) :
    EndM (QubitD n) (univ : Finset (QubitL n)) :=
  gateAt (QubitL n) j (Rx (2 * ca j * φ))

theorem isUnitary_xGate (φ : ℝ) (j : Fin n) : IsUnitary (xGate n ca φ j) :=
  isUnitary_gateAt (QubitL n) j _

/-- The lifted coupling rotation at the coupling `j`:
`Rzz(2·(b j)·φ) = e^{-iφ·(b j)·Z_j Z_{j+1}}`, extended to the whole world. -/
noncomputable def zzGate (φ : ℝ) (j : Fin (n - 1)) :
    EndM (QubitD n) (univ : Finset (QubitL n)) :=
  regLift (Reg.pair (loCell n j) (hiCell n j) (loCell_ne_hiCell n j))
    (pairGate (D := QubitD n) (loCell n j) (hiCell n j) (loCell_ne_hiCell n j)
      (Rzz (2 * cb j * φ)))

/-- The lifted coupling gate at re-indexed cells: transports a store-read
pair register onto the `loCell`/`hiCell` presentation of `zzGate` — the
counted-while mirror of the fold-era `regLift_regE2`. -/
theorem zzLift_eq (φ : ℝ) (j : Fin (n - 1)) {a b : QubitL n} (hne : a ≠ b)
    (ha : a = loCell n j) (hb : b = hiCell n j) :
    regLift (Reg.pair a b hne)
      (pairGate (D := QubitD n) a b hne (Rzz (2 * cb j * φ)))
      = zzGate n cb φ j := by
  subst ha; subst hb; rfl

theorem isUnitary_zzGate (φ : ℝ) (j : Fin (n - 1)) : IsUnitary (zzGate n cb φ j) :=
  isUnitary_regLift _ _

/-! ## §2. The partial layers and the slice operator -/

/-- The partial `X` layer: the composite of the lifted `Rx` gates at the
sites `< k` (identity beyond the last site). -/
noncomputable def aPart (φ : ℝ) : ℕ → EndM (QubitD n) (univ : Finset (QubitL n))
  | 0 => 1
  | k + 1 => (if h : k < n then xGate n ca φ ⟨k, h⟩ else 1) ∘ₗ aPart φ k

/-- The partial `ZZ` layer: the composite of the lifted `Rzz` gates at the
couplings `< k` (identity beyond the last coupling). -/
noncomputable def bPart (φ : ℝ) : ℕ → EndM (QubitD n) (univ : Finset (QubitL n))
  | 0 => 1
  | k + 1 => (if h : k < n - 1 then zzGate n cb φ ⟨k, h⟩ else 1) ∘ₗ bPart φ k

@[simp] theorem aPart_zero (φ : ℝ) : aPart n ca φ 0 = 1 := rfl

@[simp] theorem bPart_zero (φ : ℝ) : bPart n cb φ 0 = 1 := rfl

/-- Unfolding one stage of the `X` layer, below the bound. -/
theorem aPart_succ_of_lt (φ : ℝ) {k : ℕ} (hk : k < n) :
    aPart n ca φ (k + 1) = xGate n ca φ ⟨k, hk⟩ ∘ₗ aPart n ca φ k := by
  rw [show aPart n ca φ (k + 1)
      = (if h : k < n then xGate n ca φ ⟨k, h⟩ else 1) ∘ₗ aPart n ca φ k from rfl,
    dif_pos hk]

/-- Unfolding one stage of the `ZZ` layer, below the bound. -/
theorem bPart_succ_of_lt (φ : ℝ) {k : ℕ} (hk : k < n - 1) :
    bPart n cb φ (k + 1) = zzGate n cb φ ⟨k, hk⟩ ∘ₗ bPart n cb φ k := by
  rw [show bPart n cb φ (k + 1)
      = (if h : k < n - 1 then zzGate n cb φ ⟨k, h⟩ else 1) ∘ₗ bPart n cb φ k from rfl,
    dif_pos hk]

theorem isUnitary_aPart (φ : ℝ) : ∀ k, IsUnitary (aPart n ca φ k)
  | 0 => isUnitary_one
  | k + 1 => by
      refine IsUnitary.comp ?_ (isUnitary_aPart φ k)
      by_cases h : k < n
      · rw [dif_pos h]; exact isUnitary_xGate n ca φ ⟨k, h⟩
      · rw [dif_neg h]; exact isUnitary_one

theorem isUnitary_bPart (φ : ℝ) : ∀ k, IsUnitary (bPart n cb φ k)
  | 0 => isUnitary_one
  | k + 1 => by
      refine IsUnitary.comp ?_ (isUnitary_bPart φ k)
      by_cases h : k < n - 1
      · rw [dif_pos h]; exact isUnitary_zzGate n cb φ ⟨k, h⟩
      · rw [dif_neg h]; exact isUnitary_one

/-- The whole `X` layer `AOp φ = Π_{j<n} e^{-iφ·(a j)·X_j} = e^{-iφ H_X}`
(the factors commute; see `AOp_pmState` for the spectral form). -/
noncomputable def AOp (φ : ℝ) : EndM (QubitD n) (univ : Finset (QubitL n)) :=
  aPart n ca φ n

/-- The whole `ZZ` layer `BOp φ = Π_{j<n-1} e^{-iφ·(b j)·Z_jZ_{j+1}}
= e^{-iφ H_ZZ}` (the factors commute; see `BOp_deltav` for the spectral
form). -/
noncomputable def BOp (φ : ℝ) : EndM (QubitD n) (univ : Finset (QubitL n)) :=
  bPart n cb φ (n - 1)

/-- One slice of the first-order product formula:
`WOp φ = BOp φ ∘ AOp φ = e^{-iφ H_ZZ} e^{-iφ H_X}`. Because `H_X` and `H_ZZ`
do **not** commute, `WOp φ` is *not* `e^{-iφ H}`; the product formula is the
honest object. -/
noncomputable def WOp (φ : ℝ) : EndM (QubitD n) (univ : Finset (QubitL n)) :=
  BOp n cb φ ∘ₗ AOp n ca φ

theorem isUnitary_AOp (φ : ℝ) : IsUnitary (AOp n ca φ) := isUnitary_aPart n ca φ n

theorem isUnitary_BOp (φ : ℝ) : IsUnitary (BOp n cb φ) := isUnitary_bPart n cb φ (n - 1)

theorem isUnitary_WOp (φ : ℝ) : IsUnitary (WOp n ca cb φ) :=
  (isUnitary_BOp n cb φ).comp (isUnitary_AOp n ca φ)

/-- The `k`-fold application of the slice operator: `wIter φ ψ k = (WOp φ)^k ψ`,
the state after `k` slices of the product formula. -/
noncomputable def wIter (φ : ℝ) (ψ : HS (QubitD n) (univ : Finset (QubitL n))) :
    ℕ → HS (QubitD n) (univ : Finset (QubitL n))
  | 0 => ψ
  | k + 1 => WOp n ca cb φ (wIter φ ψ k)

@[simp] theorem wIter_zero (φ : ℝ) (ψ : HS (QubitD n) (univ : Finset (QubitL n))) :
    wIter n ca cb φ ψ 0 = ψ := rfl

theorem wIter_succ (φ : ℝ) (ψ : HS (QubitD n) (univ : Finset (QubitL n))) (k : ℕ) :
    wIter n ca cb φ ψ (k + 1) = WOp n ca cb φ (wIter n ca cb φ ψ k) := rfl

/-- Each slice is unitary, so the slice iterates stay on the unit sphere. -/
theorem norm_wIter (φ : ℝ) {ψ : HS (QubitD n) (univ : Finset (QubitL n))}
    (hψ : ‖ψ‖ = 1) : ∀ k, ‖wIter n ca cb φ ψ k‖ = 1
  | 0 => hψ
  | k + 1 => norm_eq_one_of_isUnitary (isUnitary_WOp n ca cb φ) (norm_wIter φ hψ k)

/-! ## §3. The transverse-field energy and the `±` product basis -/

/-- The transverse-field energy, restricted to the sites `< k`:
`Σ_{j<k} (a j)·z(s j)` — the spectrum of the partial `H_X` on the
`X`-eigenbasis labelled by `s`.  Here `zsign (s j)` is read as the
`X`-eigenvalue (the paper writes `x(s_j)`), since the bits `s j` label the
`±` basis; `zsign` itself is the basis-neutral bit sign `(-1)^b`
(`Qhl/Gate/Rzz.lean`). -/
noncomputable def xEnergy (k : ℕ) (s : QubitL n → Bool) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), ca i * zsign (s i)

private theorem filter_lt_succ' {k : ℕ} (i : Fin k) :
    Finset.univ.filter (fun j : Fin k => (j : ℕ) < (i : ℕ) + 1)
      = insert i (Finset.univ.filter (fun j : Fin k => (j : ℕ) < (i : ℕ))) := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Nat.lt_succ_iff_lt_or_eq, Fin.ext_iff]
  tauto

/-- No site is below `0`: the empty partial sum. -/
theorem xEnergy_zero (s : QubitL n → Bool) : xEnergy n ca 0 s = 0 := by
  rw [xEnergy, Finset.filter_false_of_mem fun i _ => by omega, Finset.sum_empty]

/-- The partial-sum recursion of the transverse-field energy. -/
theorem xEnergy_succ (i : Fin n) (s : QubitL n → Bool) :
    xEnergy n ca ((i : ℕ) + 1) s = xEnergy n ca (i : ℕ) s + ca i * zsign (s i) := by
  rw [xEnergy, filter_lt_succ', Finset.sum_insert (by simp), xEnergy, add_comm]

/-- The `±` product basis state `⊗_j ∣±_{s j}⟩` labelled by `s` — the
`X`-eigenbasis of the whole world. -/
noncomputable def pmState (s : QubitL n → Bool) :
    HS (QubitD n) (univ : Finset (QubitL n)) :=
  prodV (QubitD n) (W := (univ : Finset (QubitL n))) (fun j => pmKet (s j))

/-- Each `±` product basis state is a unit vector. -/
theorem norm_pmState (s : QubitL n → Bool) : ‖pmState n s‖ = 1 :=
  norm_prodV_eq_one _ fun _ => norm_pmKet _

/-- A lifted one-site `Rx` is a pure phase on every `±` product basis state:
`Rx φ` at site `i` sends `⊗_j ∣±_{s j}⟩` to `e^{-i(φ/2)·z(sᵢ)} ⊗_j ∣±_{s j}⟩`
— the `±`-basis analogue of `gateAt_Rz_deltav`. -/
theorem gateAt_Rx_pmState (i : QubitL n) (φ : ℝ) (s : QubitL n → Bool) :
    gateAt (QubitL n) i (Rx φ) (pmState n s)
      = Complex.exp ((-(φ / 2 * zsign (s i)) : ℝ) * Complex.I) • pmState n s := by
  rw [pmState, gateAt_prodV, Rx_pmKet,
    prodV_update_smul (QubitD n) _ i (Finset.mem_univ i), Function.update_eq_self]

/-! ## §4. The layer characterizations

The two lemmas that justify reading the slice as
`WOp φ = e^{-iφ H_ZZ} e^{-iφ H_X}`: each layer is the diagonal phase operator
of its part of the Hamiltonian, on that part's eigenbasis. -/

/-- The partial `X` layer on the `±` product basis: the composite of the
first `k` lifted `Rx` gates is the pure phase `e^{-iφ·xEnergy k}`. -/
theorem aPart_pmState (φ : ℝ) (s : QubitL n → Bool) (k : ℕ) (hk : k ≤ n) :
    aPart n ca φ k (pmState n s)
      = Complex.exp ((-(φ * xEnergy n ca k s) : ℝ) * Complex.I) • pmState n s := by
  induction k with
  | zero =>
      rw [aPart_zero, Module.End.one_apply, xEnergy_zero]
      norm_num
  | succ k ih =>
      have hkn : k < n := Nat.lt_of_succ_le hk
      rw [aPart_succ_of_lt n ca φ hkn, LinearMap.comp_apply, ih (Nat.le_of_lt hkn),
        map_smul, show xGate n ca φ ⟨k, hkn⟩ = gateAt (QubitL n) ⟨k, hkn⟩
          (Rx (2 * ca ⟨k, hkn⟩ * φ)) from rfl,
        gateAt_Rx_pmState, smul_smul, ← Complex.exp_add,
        show ((k : ℕ) + 1) = ((⟨k, hkn⟩ : Fin n) : ℕ) + 1 from rfl,
        xEnergy_succ]
      congr 2
      push_cast
      ring

/-- **The `X`-layer characterization**: the whole `X` layer is diagonal in the
`±` product basis with eigenvalue `e^{-iφ·E_X(s)}`, `E_X(s) = Σ_{j<n}
(a j)·z(s j)` — the precise rendering of `AOp φ = e^{-iφ H_X}`, since `H_X`
has spectrum `E_X` on the `X`-eigenbasis. -/
theorem AOp_pmState (φ : ℝ) (s : QubitL n → Bool) :
    AOp n ca φ (pmState n s)
      = Complex.exp ((-(φ * xEnergy n ca n s) : ℝ) * Complex.I) • pmState n s :=
  aPart_pmState n ca φ s n le_rfl

/-- The partial `ZZ` layer on the computational basis: the composite of the
first `k` lifted `Rzz` gates is the pure phase `e^{-iφ·coupleE k}`. -/
theorem bPart_deltav (φ : ℝ) (m : QIdx (QubitD n) (univ : Finset (QubitL n)))
    (k : ℕ) (hk : k ≤ n - 1) :
    bPart n cb φ k (deltav (QubitD n) m)
      = Complex.exp ((-(φ * coupleE n cb k m) : ℝ) * Complex.I) • deltav (QubitD n) m := by
  induction k with
  | zero =>
      rw [bPart_zero, Module.End.one_apply, coupleE_zero]
      norm_num
  | succ k ih =>
      have hkn : k < n - 1 := Nat.lt_of_succ_le hk
      rw [bPart_succ_of_lt n cb φ hkn, LinearMap.comp_apply, ih (Nat.le_of_lt hkn),
        map_smul, show zzGate n cb φ ⟨k, hkn⟩
          = regLift (Reg.pair (loCell n ⟨k, hkn⟩) (hiCell n ⟨k, hkn⟩)
              (loCell_ne_hiCell n ⟨k, hkn⟩))
            (pairGate (D := QubitD n) (loCell n ⟨k, hkn⟩) (hiCell n ⟨k, hkn⟩)
              (loCell_ne_hiCell n ⟨k, hkn⟩) (Rzz (2 * cb ⟨k, hkn⟩ * φ))) from rfl,
        regLift_Rzz_deltav, smul_smul, ← Complex.exp_add,
        show ((k : ℕ) + 1) = ((⟨k, hkn⟩ : Fin (n - 1)) : ℕ) + 1 from rfl,
        coupleE_succ]
      congr 2
      push_cast
      ring

/-- **The `ZZ`-layer characterization**: the whole `ZZ` layer is the diagonal
phase operator of the coupling energy, `BOp φ ∣y⟩ = e^{-iφ·E_ZZ(y)} ∣y⟩`,
`E_ZZ(y) = Σ_{j<n-1} (b j)·z(y_j)z(y_{j+1})` (`coupleE`) — the precise
rendering of `BOp φ = e^{-iφ H_ZZ}`, since `H_ZZ` is diagonal with spectrum
`E_ZZ` on the computational basis. -/
theorem BOp_deltav (φ : ℝ) (m : QIdx (QubitD n) (univ : Finset (QubitL n))) :
    BOp n cb φ (deltav (QubitD n) m)
      = Complex.exp ((-(φ * coupleE n cb (n - 1) m) : ℝ) * Complex.I) •
          deltav (QubitD n) m :=
  bPart_deltav n cb φ m (n - 1) le_rfl

/-! ## §5. The Hamiltonians and the operator-exponential characterization

The two Hamiltonians of the model as labelled operators — `HX = Σ_{j<n}
(a j)·X_j` and `HZZ = Σ_{j<n-1} (b j)·Z_jZ_{j+1}`, sums of lifted Pauli
blocks — their spectra on their eigenbases, and the **exact operator
equalities** `AOp φ = e^{-iφ·HX}` and `BOp φ = e^{-iφ·HZZ}` (`expOp`,
`Qhl/HSpace/OperatorExp.lean`): the layer characterizations of §4, upgraded
from a phase computation per basis vector to equalities of operators. -/

open scoped ComplexInnerProductSpace

/-! ### §5a. The Pauli atoms on their eigenbases -/

/-- The Pauli `X` fixes the `±` basis up to sign: `X∣±⟩ = ±∣±⟩` — the
`X`-eigenbasis fact behind the transverse-field term. -/
theorem X_pmKet (b : Bool) :
    (X : 𝕢 →ₗ[ℂ] 𝕢) (pmKet b) = ((zsign b : ℝ) : ℂ) • pmKet b := by
  cases b
  · rw [pmKet_false, qplus, map_smul, map_add, X_q0, X_q1, add_comm]
    simp
  · rw [pmKet_true, qminus, map_smul, map_sub, X_q0, X_q1]
    simp only [zsign_true]
    rw [smul_smul, mul_comm, ← smul_smul]
    congr 1
    push_cast
    rw [neg_smul, one_smul, neg_sub]

/-- The `±` kets are orthonormal: `⟨±_a, ±_b⟩ = δ_{ab}` — through the
Hadamard images `∣±⟩ = H∣0⟩, H∣1⟩` and the isometry of a unitary. -/
theorem inner_pmKet (a b : Bool) :
    (⟪pmKet a, pmKet b⟫ : ℂ) = if a = b then 1 else 0 := by
  have hH : ∀ u v : 𝕢, (⟪(H : 𝕢 →ₗ[ℂ] 𝕢) u, (H : 𝕢 →ₗ[ℂ] 𝕢) v⟫ : ℂ) = ⟪u, v⟫ :=
    H.isUnitary.isIsometryOp
  cases a <;> cases b
  · rw [pmKet_false, ← H_q0, hH, inner_q0_q0, if_pos rfl]
  · rw [pmKet_false, pmKet_true, ← H_q0, ← H_q1, hH, inner_q0_q1, if_neg (by decide)]
  · rw [pmKet_true, pmKet_false, ← H_q1, ← H_q0, hH, inner_q1_q0, if_neg (by decide)]
  · rw [pmKet_true, ← H_q1, hH, inner_q1_q1, if_pos rfl]

/-- The two-qubit Pauli coupling `Z⊗Z`: the diagonal gate
`∣y₁y₂⟩ ↦ z(y₁)z(y₂) ∣y₁y₂⟩` — unitary since its diagonal is `±1`. -/
noncomputable def ZZ : UnitaryOp (EuclideanSpace ℂ (Bool × Bool)) :=
  diagOp (fun p => ((zsign p.1 * zsign p.2 : ℝ) : ℂ))
    (fun p => by cases p.1 <;> cases p.2 <;> simp [zsign])

/-- The defining basis action of `Z⊗Z`. -/
theorem ZZ_single (p : Bool × Bool) (c : ℂ) :
    (ZZ : EuclideanSpace ℂ (Bool × Bool) →ₗ[ℂ] EuclideanSpace ℂ (Bool × Bool))
        (EuclideanSpace.single p c)
      = ((zsign p.1 * zsign p.2 : ℝ) : ℂ) • EuclideanSpace.single p c := by
  rw [ZZ, diagOp_single, single_eq_smul_single p _, single_eq_smul_single p c, smul_smul]

/-- The basis action of `Z⊗Z` in the two-factor `vpair` form the pair-register
bridge `regLift_pairGate_prodV` consumes (the sign on the first factor). -/
theorem ZZ_vpair (y₁ y₂ : Bool) :
    (ZZ : EuclideanSpace ℂ (Bool × Bool) →ₗ[ℂ] EuclideanSpace ℂ (Bool × Bool))
        (vpair (EuclideanSpace.single y₁ (1 : ℂ)) (EuclideanSpace.single y₂ (1 : ℂ)))
      = vpair
          (((zsign y₁ * zsign y₂ : ℝ) : ℂ) • EuclideanSpace.single y₁ (1 : ℂ))
          (EuclideanSpace.single y₂ (1 : ℂ)) := by
  rw [vpair_single, one_mul, ZZ_single, vpair_smul_left, vpair_single, one_mul]

/-- A lifted two-site `Z⊗Z` at the pair `(a, b)` is a sign on every
whole-world basis ket: `∣y⟩ ↦ z(yₐ)z(y_b) ∣y⟩` — the `Z⊗Z` analogue of
`regLift_Rzz_deltav`. -/
theorem regLift_ZZ_deltav (a b : QubitL n) (hab : a ≠ b)
    (m : QIdx (QubitD n) (univ : Finset (QubitL n))) :
    regLift (Reg.pair a b hab) (pairGate (D := QubitD n) a b hab ZZ) (deltav (QubitD n) m)
      = ((zsign (bitAt n m a) * zsign (bitAt n m b) : ℝ) : ℂ) • deltav (QubitD n) m := by
  rw [deltav_eq_prodV,
    regLift_pairGate_prodV a b hab ZZ
      (fun j => EuclideanSpace.single (bitAt n m j) 1)
      (ZZ_vpair (bitAt n m a) (bitAt n m b))]
  have h1 : Function.update
        (Function.update (fun j => EuclideanSpace.single (bitAt n m j) (1 : ℂ)) a
          (((zsign (bitAt n m a) * zsign (bitAt n m b) : ℝ) : ℂ) •
            EuclideanSpace.single (bitAt n m a) (1 : ℂ)))
        b (EuclideanSpace.single (bitAt n m b) (1 : ℂ))
      = Function.update (fun j => EuclideanSpace.single (bitAt n m j) (1 : ℂ)) a
          (((zsign (bitAt n m a) * zsign (bitAt n m b) : ℝ) : ℂ) •
            EuclideanSpace.single (bitAt n m a) (1 : ℂ)) := by
    rw [show EuclideanSpace.single (bitAt n m b) (1 : ℂ)
        = Function.update (fun j => EuclideanSpace.single (bitAt n m j) (1 : ℂ)) a
            (((zsign (bitAt n m a) * zsign (bitAt n m b) : ℝ) : ℂ) •
              EuclideanSpace.single (bitAt n m a) (1 : ℂ)) b
      from (Function.update_of_ne (Ne.symm hab)
        (((zsign (bitAt n m a) * zsign (bitAt n m b) : ℝ) : ℂ) •
          EuclideanSpace.single (bitAt n m a) (1 : ℂ))
        (fun j => EuclideanSpace.single (bitAt n m j) (1 : ℂ))).symm]
    exact Function.update_eq_self _ _
  rw [h1, prodV_update_smul (QubitD n) _ a (Finset.mem_univ a), Function.update_eq_self,
    ← deltav_eq_prodV]

/-! ### §5b. The Hamiltonians and their spectra -/

/-- **The transverse-field Hamiltonian** `HX = Σ_{j<n} (a j)·X_j`: the sum of
the lifted Pauli `X` blocks, weighted by the field coefficients — the
generator of the `X` layer. -/
noncomputable def HX : EndM (QubitD n) (univ : Finset (QubitL n)) :=
  ∑ j : Fin n, (ca j : ℂ) • gateAt (QubitL n) j X

/-- **The coupling Hamiltonian** `HZZ = Σ_{j<n-1} (b j)·Z_jZ_{j+1}`: the sum
of the lifted Pauli `Z⊗Z` blocks at the nearest-neighbour pairs, weighted by
the coupling coefficients — the generator of the `ZZ` layer. -/
noncomputable def HZZ : EndM (QubitD n) (univ : Finset (QubitL n)) :=
  ∑ j : Fin (n - 1), (cb j : ℂ) •
    regLift (Reg.pair (loCell n j) (hiCell n j) (loCell_ne_hiCell n j))
      (pairGate (D := QubitD n) (loCell n j) (hiCell n j) (loCell_ne_hiCell n j) ZZ)

/-- At the full site count the partial transverse-field energy is the whole
spectrum sum `Σ_{j<n} (a j)·z(s j)`. -/
theorem xEnergy_top (s : QubitL n → Bool) :
    xEnergy n ca n s = ∑ j : Fin n, ca j * zsign (s j) := by
  rw [xEnergy, Finset.filter_true_of_mem fun i _ => i.isLt]

/-- At the full coupling count the partial coupling energy is the whole
spectrum sum `Σ_{j<n-1} (b j)·z(y_j)z(y_{j+1})`. -/
theorem coupleE_top (m : QIdx (QubitD n) (univ : Finset (QubitL n))) :
    coupleE n cb (n - 1) m
      = ∑ j : Fin (n - 1),
          cb j * (zsign (bitAt n m (loCell n j)) * zsign (bitAt n m (hiCell n j))) := by
  rw [coupleE, Finset.filter_true_of_mem fun j _ => j.isLt]

/-- A lifted one-site Pauli `X` on a `±` product basis state: the sign of the
named factor — the Hamiltonian-term analogue of `gateAt_Rx_pmState`. -/
theorem gateAt_X_pmState (i : QubitL n) (s : QubitL n → Bool) :
    gateAt (QubitL n) i X (pmState n s)
      = ((zsign (s i) : ℝ) : ℂ) • pmState n s := by
  rw [pmState, gateAt_prodV, X_pmKet,
    prodV_update_smul (QubitD n) _ i (Finset.mem_univ i), Function.update_eq_self]

/-- **The spectrum of `HX`** on the `±` product basis:
`HX (⊗_j ∣±_{s j}⟩) = E_X(s) · ⊗_j ∣±_{s j}⟩` with `E_X(s) = Σ_j (a j)·z(s j)`
(`xEnergy`) — `HX` is diagonal on the `X`-eigenbasis. -/
theorem HX_pmState (s : QubitL n → Bool) :
    HX n ca (pmState n s) = ((xEnergy n ca n s : ℝ) : ℂ) • pmState n s := by
  rw [HX, LinearMap.sum_apply,
    Finset.sum_congr rfl (fun j _ => by
      rw [LinearMap.smul_apply, gateAt_X_pmState, smul_smul]),
    ← Finset.sum_smul, xEnergy_top]
  congr 1
  push_cast
  ring_nf

/-- **The spectrum of `HZZ`** on the computational basis:
`HZZ ∣y⟩ = E_ZZ(y) ∣y⟩` with `E_ZZ(y) = Σ_j (b j)·z(y_j)z(y_{j+1})`
(`coupleE`) — `HZZ` is diagonal on the computational basis. -/
theorem HZZ_deltav (m : QIdx (QubitD n) (univ : Finset (QubitL n))) :
    HZZ n cb (deltav (QubitD n) m)
      = ((coupleE n cb (n - 1) m : ℝ) : ℂ) • deltav (QubitD n) m := by
  rw [HZZ, LinearMap.sum_apply,
    Finset.sum_congr rfl (fun j _ => by
      rw [LinearMap.smul_apply, regLift_ZZ_deltav, smul_smul]),
    ← Finset.sum_smul, coupleE_top]
  congr 1
  push_cast
  ring_nf

/-! ### §5c. The `±` product basis is a basis -/

/-- The `±` product basis states are orthonormal: factorwise `inner_pmKet`
through `prodV_inner`. -/
theorem orthonormal_pmState :
    Orthonormal ℂ (fun s : QubitL n → Bool => pmState n s) := by
  rw [orthonormal_iff_ite]
  intro s t
  rw [pmState, pmState,
    prodV_inner (QubitD n) (W := (univ : Finset (QubitL n)))]
  by_cases hst : s = t
  · subst hst
    rw [if_pos rfl]
    exact Finset.prod_eq_one fun i _ => by rw [inner_pmKet, if_pos rfl]
  · rw [if_neg hst]
    obtain ⟨i, hi⟩ : ∃ i, s i ≠ t i := by
      by_contra hc
      push Not at hc
      exact hst (funext hc)
    exact Finset.prod_eq_zero
      (Finset.mem_univ (⟨i, Finset.mem_univ i⟩ : ↥(univ : Finset (QubitL n))))
      (by rw [inner_pmKet, if_neg hi])

/-- The `±` product basis, as a basis: `2^n` orthonormal vectors in the
`2^n`-dimensional world — the `X`-eigenbasis mirror of the computational
basis (the same device as the Fourier basis of `Qhl/Register/Fourier.lean`
§10). -/
noncomputable def pmBasis :
    Module.Basis (QubitL n → Bool) ℂ (HS (QubitD n) (univ : Finset (QubitL n))) :=
  basisOfOrthonormalOfCardEqFinrank (orthonormal_pmState n)
    (by rw [finrank_HS]; simp [QubitL, QubitD])

/-- Extensionality over the `±` product basis: two endomorphisms agreeing on
every `pmState` are equal — the `X`-eigenbasis mirror of `linM_ext`. -/
theorem linM_ext_pmState {f g : EndM (QubitD n) (univ : Finset (QubitL n))}
    (h : ∀ s, f (pmState n s) = g (pmState n s)) : f = g :=
  Module.Basis.ext (pmBasis n) fun s => by
    rw [show (pmBasis n) s = pmState n s from congrFun
      (coe_basisOfOrthonormalOfCardEqFinrank _ _) s, h]

/-! ### §5d. The operator equalities: the layers are the exponentials -/

/-- **The `X` layer is the operator exponential of its Hamiltonian**:
`AOp φ = e^{-iφ·HX}`, as an equality of operators — both sides are diagonal
on the `±` product basis (`AOp_pmState`, `HX_pmState` through
`expOp_eigenvector`) with the same eigenvalues. -/
theorem AOp_eq_expOp (φ : ℝ) :
    AOp n ca φ = expOp ((-(Complex.I * (φ : ℂ))) • HX n ca) := by
  refine linM_ext_pmState n fun s => ?_
  have heig : ((-(Complex.I * (φ : ℂ))) • HX n ca) (pmState n s)
      = ((-(Complex.I * (φ : ℂ))) * ((xEnergy n ca n s : ℝ) : ℂ)) • pmState n s := by
    rw [LinearMap.smul_apply, HX_pmState, smul_smul]
  rw [AOp_pmState, expOp_eigenvector heig]
  congr 1
  push_cast
  ring_nf

/-- **The `ZZ` layer is the operator exponential of its Hamiltonian**:
`BOp φ = e^{-iφ·HZZ}`, as an equality of operators — both sides are diagonal
on the computational basis (`BOp_deltav`, `HZZ_deltav` through
`expOp_eigenvector`) with the same eigenvalues. -/
theorem BOp_eq_expOp (φ : ℝ) :
    BOp n cb φ = expOp ((-(Complex.I * (φ : ℂ))) • HZZ n cb) := by
  refine linM_ext (QubitD n) fun m => ?_
  have heig : ((-(Complex.I * (φ : ℂ))) • HZZ n cb) (deltav (QubitD n) m)
      = ((-(Complex.I * (φ : ℂ))) * ((coupleE n cb (n - 1) m : ℝ) : ℂ)) •
          deltav (QubitD n) m := by
    rw [LinearMap.smul_apply, HZZ_deltav, smul_smul]
  rw [BOp_deltav, expOp_eigenvector heig]
  congr 1
  push_cast
  ring_nf

/-- The slice iterates are the powers of the slice operator:
`wIter φ ψ k = (WOp φ)^k ψ`. -/
theorem wIter_eq_pow (φ : ℝ) (ψ : HS (QubitD n) (univ : Finset (QubitL n))) :
    ∀ k, wIter n ca cb φ ψ k = ((WOp n ca cb φ) ^ k) ψ
  | 0 => by rw [wIter_zero, pow_zero, Module.End.one_apply]
  | k + 1 => by
      rw [wIter_succ, wIter_eq_pow φ ψ k, pow_succ', Module.End.mul_apply]

end Model

end Qhl
