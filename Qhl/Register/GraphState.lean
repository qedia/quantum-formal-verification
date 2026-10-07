import Qhl.Logic.Frame
import Qhl.Register.Qubits
import Qhl.Register.Fourier
import Qhl.Register.PauliString

/-!
# The 1D cluster (graph) state and its CZ-chain interpolation

The state layer of the cluster-state preparation example (cluster / graph
states: Briegel–Raussendorf 2001 — the Ising-type entangling layer of `CZ`
gates on nearest-neighbour pairs, applied to `⊗ᵢ ∣+⟩`).

* **Generic tensor algebra** (`vpair_smul_right`, `prodV_update_smul_self`,
  `regLift_pairGate_smul`): a two-cell gate whose action on the two named
  factors of a product state is multiplication by a scalar lifts to scalar
  multiplication on the whole product state — the diagonal-gate instance of the
  `k = 2` block bridge `regLift_pairGate_prodV` (`Qhl/Logic/Frame.lean`, CoqQ
  `lift_lf` on a `tenvm`-split state).
* **The `CZ` basis action** `CZ_vpair_smul`: on a product of basis kets, `CZ`
  is the sign `(-1)^{x·y}` (`CZ_single` of `Qhl/Gate/Qubit.lean` read on a
  `vpair`).
* **The chain cells** `chainA`/`chainB` — the `k`-th nearest-neighbour edge
  `(k, k+1)` of the standard `n`-qubit world `QubitL n`.
* **The edge signs** `edgeSign`/`czSign` — the sign `(-1)^{y_k·y_{k+1}}` of one
  edge under a computational-basis assignment `y`, and the accumulated sign
  `∏_{j<k} (-1)^{y_j·y_{j+1}}` of the first `k` edges.
* **The interpolating family** `clusterFam n k` — the state after `k` edges of
  the entangling layer,

  ```
  clusterFam n k = 2^{-n/2} ∑_y (-1)^{∑_{j<k} y_j·y_{j+1}} ∣y⟩,
  ```

  defined by its coordinates (like `fourierState`, `Qhl/Register/Fourier.lean`)
  with the signed basis-sum presentation `clusterFam_eq_sum`, the loop entry
  `clusterFam_zero : clusterFam n 0 = allPlus n`, the loop step
  `clusterFam_step` (one lifted `CZ` at the edge `(k, k+1)` advances the family
  by one edge — proved coordinatewise: expand in the `deltav` basis, push the
  lifted gate through the sum by linearity, and multiply each basis ket by its
  edge sign), and the unit norm `norm_clusterFam` (every coordinate has modulus
  `2^{-n/2}`). For `k ≥ 1` the family is entangled — it is **not** a product
  state — which is why the preparation example consumes these lemmas at
  `Assn.ofState` endpoints rather than through the product-state combinators.
* **The 1D cluster state** `clusterVec n = clusterFam n (n-1)` — all `n-1`
  edges — with its norm, its nonvanishing `∣0…0⟩` coordinate `2^{-n/2}`
  (`clusterVec_apply_allFalse`), and `clusterVec_ne_zero`.
* **The cluster stabilizers** `clusterStab n j = K_j = Z_{j-1} X_j Z_{j+1}`
  (§5) — the standard graph-state stabilizers of the path graph, as Pauli
  strings (`pauliString`, `Qhl/Register/PauliString.lean`), with the boundary
  cases `K_0 = X_0 Z_1` and `K_{n-1} = Z_{n-2} X_{n-1}`, and the **stabilizer
  property** `clusterStab_clusterVec : K_j ∣C_n⟩ = ∣C_n⟩` for every `j` —
  proved on the amplitude formula `clusterFam_eq_sum`: `X_j` flips bit `j`,
  which flips the (at most two) edge signs at the edges meeting `j`, and the
  two `Z` neighbours contribute exactly the compensating parity signs.

Everything here names states, gates and registers only — no program and no
example fixture appears (ownership test of the charter).
-/

namespace Qhl

open Finset

/-! ## §1. Generic tensor algebra: a scalar action on two factors lifts -/

section Generic

variable {α β : Type*}

/-- The product vector is linear in its right factor (the sibling of the
library's `vpair_smul_left`). -/
theorem vpair_smul_right (c : ℂ) (u : EuclideanSpace ℂ α) (v : EuclideanSpace ℂ β) :
    vpair u (c • v) = c • vpair u v := by
  ext p
  simp only [vpair_apply, PiLp.smul_apply, smul_eq_mul]
  ring

end Generic

section GenericD

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)]

omit [Fintype L] [∀ i, Inhabited (D i)] in
/-- Rescaling one factor of a product state rescales the product state: the
multilinearity of `prodV` in the factor at `b ∈ W`. -/
theorem prodV_update_smul_self {W : Finset L} {b : L} (hb : b ∈ W) (c : ℂ)
    (ψ : ∀ i, EuclideanSpace ℂ (D i)) :
    prodV D (W := W) (Function.update ψ b (c • ψ b)) = c • prodV D (W := W) ψ := by
  refine PiLp.ext fun l => ?_
  rw [prodV_apply, PiLp.smul_apply, prodV_apply, smul_eq_mul]
  rw [← Finset.mul_prod_erase Finset.univ
      (fun i : ↥W => Function.update ψ b (c • ψ b) (i : L) (l i))
      (Finset.mem_univ (⟨b, hb⟩ : ↥W)),
    ← Finset.mul_prod_erase Finset.univ (fun i : ↥W => ψ (i : L) (l i))
      (Finset.mem_univ (⟨b, hb⟩ : ↥W))]
  have hb0 : Function.update ψ b (c • ψ b) ((⟨b, hb⟩ : ↥W) : L) (l ⟨b, hb⟩)
      = c * ψ b (l ⟨b, hb⟩) := by
    change Function.update ψ b (c • ψ b) b (l ⟨b, hb⟩) = c * ψ b (l ⟨b, hb⟩)
    rw [Function.update_self, PiLp.smul_apply, smul_eq_mul]
  have herase : ∀ i ∈ (Finset.univ : Finset ↥W).erase ⟨b, hb⟩,
      Function.update ψ b (c • ψ b) (i : L) (l i) = ψ (i : L) (l i) := by
    intro i hi
    have hib : (i : L) ≠ b := fun hc => (Finset.mem_erase.mp hi).1 (Subtype.ext hc)
    rw [Function.update_of_ne hib]
  rw [Finset.prod_congr rfl herase, hb0]
  ring

/-- **A two-cell gate acting as a scalar on its block lifts to the scalar on
the whole product state** — the diagonal instance of the `k = 2` block bridge
`regLift_pairGate_prodV` (CoqQ `lift_lf` on a `tenvm`-split state): if `G`
multiplies the two named factors by `c`, the lifted gate multiplies the whole
product state by `c`, every other factor being framed. -/
theorem regLift_pairGate_smul (a b : L) (hab : a ≠ b)
    (G : UnitaryOp (EuclideanSpace ℂ (D a × D b))) (c : ℂ)
    (ψ : ∀ i, EuclideanSpace ℂ (D i))
    (hG : (G : EuclideanSpace ℂ (D a × D b) →ₗ[ℂ] EuclideanSpace ℂ (D a × D b))
        (vpair (ψ a) (ψ b)) = c • vpair (ψ a) (ψ b)) :
    regLift (Reg.pair a b hab) (pairGate a b hab G) (prodV D (W := (univ : Finset L)) ψ)
      = c • prodV D (W := (univ : Finset L)) ψ := by
  have hG' : (G : EuclideanSpace ℂ (D a × D b) →ₗ[ℂ] EuclideanSpace ℂ (D a × D b))
      (vpair (ψ a) (ψ b)) = vpair (ψ a) (c • ψ b) := by
    rw [hG, vpair_smul_right]
  rw [regLift_pairGate_prodV a b hab G ψ hG', Function.update_eq_self,
    prodV_update_smul_self (Finset.mem_univ b)]

end GenericD

/-! ## §2. The `CZ` basis action -/

/-- **The `CZ` action on a product of basis kets**: the sign `(-1)^{x·y}` —
`CZ_single` (`Qhl/Gate/Qubit.lean`) read on a `vpair`, in the scalar form the
lift `regLift_pairGate_smul` consumes. -/
theorem CZ_vpair_smul (x y : Bool) :
    (CZ : EuclideanSpace ℂ (Bool × Bool) →ₗ[ℂ] EuclideanSpace ℂ (Bool × Bool))
        (vpair (qbit x) (qbit y))
      = (if x && y then (-1 : ℂ) else 1) • vpair (qbit x) (qbit y) := by
  simp only [qbit, vpair_single, mul_one, CZ_single]
  ext p
  simp only [PiLp.smul_apply, smul_eq_mul, PiLp.single_apply, mul_ite, mul_one, mul_zero]

/-! ## §3. The chain cells and the edge signs -/

/-- The left cell of the `k`-th nearest-neighbour edge of the `n`-qubit
chain. -/
def chainA {n k : ℕ} (hk : k + 1 < n) : QubitL n := ⟨k, Nat.lt_of_succ_lt hk⟩

/-- The right cell of the `k`-th nearest-neighbour edge. -/
def chainB {n k : ℕ} (hk : k + 1 < n) : QubitL n := ⟨k + 1, hk⟩

theorem chainA_ne_chainB {n k : ℕ} (hk : k + 1 < n) : chainA hk ≠ chainB hk :=
  Fin.ne_of_val_ne (Nat.ne_of_lt (Nat.lt_succ_self k))

/-- The sign `(-1)^{y_j·y_{j+1}}` of the `j`-th edge under the
computational-basis assignment `m`, and `1` when the edge leaves the world
(`j + 1 ≥ n`) — the totalisation that lets the accumulated sign be indexed by
an arbitrary `ℕ`. -/
def edgeSign (n : ℕ) (m : Fin n → Bool) (j : ℕ) : ℂ :=
  if h : j + 1 < n then (if m (chainA h) && m (chainB h) then -1 else 1) else 1

theorem edgeSign_of_lt {n k : ℕ} (hk : k + 1 < n) (m : Fin n → Bool) :
    edgeSign n m k = if m (chainA hk) && m (chainB hk) then -1 else 1 :=
  dif_pos hk

@[simp]
theorem norm_edgeSign (n : ℕ) (m : Fin n → Bool) (j : ℕ) : ‖edgeSign n m j‖ = 1 := by
  unfold edgeSign
  split_ifs <;> simp

/-- The accumulated sign of the first `k` edges,
`∏_{j<k} (-1)^{y_j·y_{j+1}}`. -/
def czSign (n k : ℕ) (m : Fin n → Bool) : ℂ := ∏ j ∈ Finset.range k, edgeSign n m j

@[simp]
theorem czSign_zero (n : ℕ) (m : Fin n → Bool) : czSign n 0 m = 1 :=
  Finset.prod_range_zero _

theorem czSign_succ (n k : ℕ) (m : Fin n → Bool) :
    czSign n (k + 1) m = czSign n k m * edgeSign n m k :=
  Finset.prod_range_succ _ _

@[simp]
theorem norm_czSign (n k : ℕ) (m : Fin n → Bool) : ‖czSign n k m‖ = 1 := by
  rw [czSign, norm_prod]
  exact Finset.prod_eq_one fun j _ => norm_edgeSign n m j

/-- Under the all-`false` assignment every edge sign is trivial. -/
theorem czSign_allFalse (n k : ℕ) : czSign n k (fun _ => false) = 1 :=
  Finset.prod_eq_one fun j _ => by unfold edgeSign; split <;> simp

/-! ## §4. The interpolating family and the cluster state -/

/-- **The CZ-chain interpolating family**: the state of the `n`-qubit world
after the Hadamard layer and the first `k` edges of the entangling layer,

```
clusterFam n k = 2^{-n/2} ∑_y (-1)^{∑_{j<k} y_j·y_{j+1}} ∣y⟩,
```

given by its coordinates (the presentation `fourierState` uses); the signed
basis-sum form is `clusterFam_eq_sum`. Entangled — not a product state — for
`k ≥ 1`. -/
noncomputable def clusterFam (n k : ℕ) : HS (QubitD n) (univ : Finset (QubitL n)) :=
  WithLp.toLp 2 fun l =>
    ((Real.sqrt 2 : ℂ))⁻¹ ^ n * czSign n k (fun i : QubitL n => l ⟨i, Finset.mem_univ i⟩)

@[simp]
theorem clusterFam_apply (n k : ℕ) (l : QIdx (QubitD n) (univ : Finset (QubitL n))) :
    clusterFam n k l
      = ((Real.sqrt 2 : ℂ))⁻¹ ^ n
        * czSign n k (fun i : QubitL n => l ⟨i, Finset.mem_univ i⟩) := rfl

/-- The signed basis-sum presentation: `clusterFam n k` **is** the sum
`2^{-n/2} ∑_y (-1)^{∑_{j<k} y_j·y_{j+1}} ∣y⟩` over the computational basis —
the canonical-basis expansion `dec_dv` reindexed along `bitsEquiv`. -/
theorem clusterFam_eq_sum (n k : ℕ) :
    clusterFam n k
      = ∑ m : Fin n → Bool,
          (((Real.sqrt 2 : ℂ))⁻¹ ^ n * czSign n k m)
            • deltav (QubitD n) (fun i : ↥(univ : Finset (QubitL n)) => m (i : QubitL n)) :=
  (dec_dv (QubitD n) (clusterFam n k)).trans
    (Fintype.sum_equiv (bitsEquiv n) _ _ fun _ => rfl)

/-- **Loop entry**: before any edge the family is the uniform superposition
`⊗ᵢ ∣+⟩` the Hadamard layer produced. -/
theorem clusterFam_zero (n : ℕ) : clusterFam n 0 = allPlus n := by
  refine PiLp.ext fun l => ?_
  rw [clusterFam_apply, czSign_zero, mul_one, allPlus_apply]

/-- A product of basis kets is the computational basis ket (the library
`prodV_single` at the standard qubit world). -/
theorem prodV_qbit (n : ℕ) (m : Fin n → Bool) :
    prodV (QubitD n) (W := (univ : Finset (QubitL n))) (fun i => qbit (m i))
      = deltav (QubitD n) (fun i : ↥(univ : Finset (QubitL n)) => m (i : QubitL n)) :=
  prodV_single (QubitD n) fun i => m i

/-- **Loop step**: the lifted `CZ` at the edge `(k, k+1)` advances the family
by one edge. Coordinatewise: expand in the `deltav` basis
(`clusterFam_eq_sum`), push the lifted gate through the sum by linearity
(`map_sum`), and multiply each basis ket `∣y⟩` by its edge sign
`(-1)^{y_k·y_{k+1}}` (`regLift_pairGate_smul` over `CZ_vpair_smul`). -/
theorem clusterFam_step {n k : ℕ} (hk : k + 1 < n) :
    regLift (Reg.pair (chainA hk) (chainB hk) (chainA_ne_chainB hk))
        (pairGate (D := QubitD n) (chainA hk) (chainB hk) (chainA_ne_chainB hk) CZ)
        (clusterFam n k)
      = clusterFam n (k + 1) := by
  rw [clusterFam_eq_sum n k, clusterFam_eq_sum n (k + 1), map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hG : (CZ : EuclideanSpace ℂ (Bool × Bool) →ₗ[ℂ] EuclideanSpace ℂ (Bool × Bool))
      (vpair (qbit (m (chainA hk))) (qbit (m (chainB hk))))
      = edgeSign n m k • vpair (qbit (m (chainA hk))) (qbit (m (chainB hk))) := by
    rw [CZ_vpair_smul, edgeSign_of_lt hk]
  rw [map_smul, ← prodV_qbit n m,
    regLift_pairGate_smul (D := QubitD n) (chainA hk) (chainB hk) (chainA_ne_chainB hk) CZ
      (edgeSign n m k) (fun i => qbit (m i)) hG,
    smul_smul, czSign_succ, mul_assoc]

/-- `clusterFam_step` at cell indexing: the library edge fact is stated at
`chainA`/`chainB`; this transports it to any pair of cells equal to them —
the form the store-read register of a counted `while` produces. -/
theorem clusterFam_step_cell {n k : ℕ} (hk : k + 1 < n) {a b : QubitL n}
    (ha : a = chainA hk) (hb : b = chainB hk) (hab : a ≠ b) :
    regLift (Reg.pair a b hab) (pairGate (D := QubitD n) a b hab CZ) (clusterFam n k)
      = clusterFam n (k + 1) := by
  subst ha; subst hb
  exact clusterFam_step hk

/-- Every coordinate of the family has modulus `2^{-n/2}`, so the family is a
unit vector. -/
theorem norm_clusterFam (n k : ℕ) : ‖clusterFam n k‖ = 1 := by
  have hcard : Fintype.card (QIdx (QubitD n) (univ : Finset (QubitL n))) = 2 ^ n := by
    rw [Fintype.card_congr (bitsEquiv n), Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin]
  have hns : ‖((Real.sqrt 2 : ℂ))⁻¹ ^ n‖ = (Real.sqrt 2)⁻¹ ^ n := by
    rw [norm_pow, norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg 2)]
  have hcoord : ∀ l : QIdx (QubitD n) (univ : Finset (QubitL n)),
      ‖clusterFam n k l‖ ^ 2 = ((Real.sqrt 2)⁻¹ ^ n) ^ 2 := fun l => by
    rw [clusterFam_apply, norm_mul, norm_czSign, mul_one, hns]
  rw [EuclideanSpace.norm_eq, Finset.sum_congr rfl fun l _ => hcoord l,
    Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
  have h2 : ((2 ^ n : ℕ) : ℝ) * ((Real.sqrt 2)⁻¹ ^ n) ^ 2 = 1 := by
    push_cast
    rw [← pow_mul, mul_comm n 2, pow_mul, inv_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), ← mul_pow,
      mul_inv_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_pow]
  rw [h2, Real.sqrt_one]

/-- **The 1D cluster state** `C_n` (Briegel–Raussendorf 2001): the family after
all `n - 1` nearest-neighbour edges,

```
C_n = 2^{-n/2} ∑_y (-1)^{∑_{j<n-1} y_j·y_{j+1}} ∣y⟩.
``` -/
noncomputable def clusterVec (n : ℕ) : HS (QubitD n) (univ : Finset (QubitL n)) :=
  clusterFam n (n - 1)

@[simp]
theorem norm_clusterVec (n : ℕ) : ‖clusterVec n‖ = 1 := norm_clusterFam n (n - 1)

/-- The `∣0…0⟩` coordinate of the cluster state is `2^{-n/2}`: the
postcondition of the preparation example is a genuinely nonzero predicate. -/
theorem clusterVec_apply_allFalse (n : ℕ) :
    clusterVec n (fun _ => false) = ((Real.sqrt 2 : ℂ))⁻¹ ^ n := by
  have h : clusterVec n (fun _ => false)
      = ((Real.sqrt 2 : ℂ))⁻¹ ^ n * czSign n (n - 1) (fun _ => false) := rfl
  rw [h, czSign_allFalse, mul_one]

theorem clusterVec_ne_zero (n : ℕ) : clusterVec n ≠ 0 := fun h =>
  one_ne_zero (α := ℝ) (by rw [← norm_clusterVec n, h, norm_zero])

/-! ## §5. The cluster stabilizers `K_j = Z_{j-1} X_j Z_{j+1}`

The standard graph-state stabilizers of the path graph (Briegel–Raussendorf
2001): `K_j = X_j ∏_{i ~ j} Z_i`, the product over the chain neighbours of
`j` — so `K_j = Z_{j-1} X_j Z_{j+1}` in the interior and `K_0 = X_0 Z_1`,
`K_{n-1} = Z_{n-2} X_{n-1}` at the boundary (for `n = 1`, `K_0 = X_0`).  Each
is a Pauli string (`pauliString`, `Qhl/Register/PauliString.lean`), hence
unitary, self-adjoint and an involution for free; the content of this section
is the **stabilizer property** `clusterStab_clusterVec : K_j ∣C_n⟩ = ∣C_n⟩`,
proved coordinatewise on `clusterFam_eq_sum`: `X_j` flips bit `j` of each
basis ket, which flips the edge signs of the (at most two) chain edges meeting
`j`, and the `Z` letters at the chain neighbours of `j` contribute exactly the
compensating parity signs `(-1)^{y_{j-1}}·(-1)^{y_{j+1}}`. -/

section Stabilizer

/-- The Pauli letter assignment of the `j`-th **cluster stabilizer**: `X` at
the site `j`, `Z` at each chain neighbour of `j`, identity elsewhere.  The
neighbour conditions are on the underlying naturals, so at the boundary
(`j = 0`, `j = n-1`) the missing neighbour is simply never matched. -/
def stabLetter (n : ℕ) (j : Fin n) (k : QubitL n) : PLetter :=
  if k = j then PLetter.x
  else if (k : ℕ) + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = (k : ℕ) then PLetter.z
  else PLetter.one

/-- **The `j`-th cluster stabilizer** `K_j = Z_{j-1} X_j Z_{j+1}` (boundary:
`K_0 = X_0 Z_1`, `K_{n-1} = Z_{n-2} X_{n-1}`), as a Pauli string on the
`n`-qubit world. -/
noncomputable def clusterStab (n : ℕ) (j : Fin n) :
    EndM (QubitD n) (univ : Finset (QubitL n)) :=
  pauliString (stabLetter n j)

/-- `K_j` is unitary. -/
theorem isUnitary_clusterStab (n : ℕ) (j : Fin n) : IsUnitary (clusterStab n j) :=
  isUnitary_pauliString _

/-- `K_j` is self-adjoint — a genuine observable. -/
theorem adjoint_clusterStab (n : ℕ) (j : Fin n) :
    LinearMap.adjoint (clusterStab n j) = clusterStab n j :=
  adjoint_pauliString _

/-- `K_j ∘ K_j = 1`. -/
theorem clusterStab_comp_self (n : ℕ) (j : Fin n) :
    clusterStab n j ∘ₗ clusterStab n j = 1 :=
  pauliString_comp_self _

/-- The bit-flip pattern of `K_j` is the flip of bit `j` alone (only the `X`
letter flips). -/
theorem stabLetter_flips (n : ℕ) (j : Fin n) (m : Fin n → Bool) :
    (fun k => xor (stabLetter n j k).flips (m k)) = Function.update m j (!(m j)) := by
  funext k
  by_cases hkj : k = j
  · subst hkj
    simp [stabLetter, PLetter.flips]
  · rw [Function.update_of_ne hkj]
    by_cases hz : (k : ℕ) + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = (k : ℕ) <;>
      simp [stabLetter, hkj, hz, PLetter.flips]

/-- The per-site scalar of `K_j` splits as a left-neighbour and a
right-neighbour parity factor (the `X` site and untouched sites contribute
`1`). -/
theorem stabLetter_ph (n : ℕ) (j : Fin n) (m : Fin n → Bool) (k : QubitL n) :
    (stabLetter n j k).ph (m k)
      = (if (k : ℕ) + 1 = (j : ℕ) ∧ m k then (-1 : ℂ) else 1)
        * (if (j : ℕ) + 1 = (k : ℕ) ∧ m k then (-1 : ℂ) else 1) := by
  by_cases hkj : k = j
  · subst hkj
    simp [stabLetter, PLetter.ph]
  · by_cases hL : (k : ℕ) + 1 = (j : ℕ)
    · have hR : ¬((j : ℕ) + 1 = (k : ℕ)) := by omega
      cases m k <;> simp [stabLetter, hkj, hL, hR, PLetter.ph]
    · by_cases hR : (j : ℕ) + 1 = (k : ℕ)
      · cases m k <;> simp [stabLetter, hkj, hL, hR, PLetter.ph]
      · simp [stabLetter, hkj, hL, hR, PLetter.ph]

/-- The **left parity sign** `(-1)^{y_{j-1}}` when `j` has a left chain
neighbour, `1` at the boundary `j = 0`. -/
noncomputable def leftNbrSign (n : ℕ) (j : Fin n) (m : Fin n → Bool) : ℂ :=
  if h : 1 ≤ (j : ℕ) then
    (if m (chainA (show (j : ℕ) - 1 + 1 < n from by have := j.isLt; omega))
      then -1 else 1)
  else 1

/-- The **right parity sign** `(-1)^{y_{j+1}}` when `j` has a right chain
neighbour, `1` at the boundary `j = n-1`. -/
noncomputable def rightNbrSign (n : ℕ) (j : Fin n) (m : Fin n → Bool) : ℂ :=
  if h : (j : ℕ) + 1 < n then (if m (chainB h) then -1 else 1) else 1

/-- The per-site scalars of `K_j` multiply to the two neighbour parity signs:
each of the two factor families is `1` except at the (at most one) matching
neighbour site. -/
theorem prod_stabLetter_ph (n : ℕ) (j : Fin n) (m : Fin n → Bool) :
    (∏ k, (stabLetter n j k).ph (m k)) = leftNbrSign n j m * rightNbrSign n j m := by
  rw [Finset.prod_congr rfl fun k _ => stabLetter_ph n j m k, Finset.prod_mul_distrib]
  congr 1
  · by_cases hj : 1 ≤ (j : ℕ)
    · have hlt : (j : ℕ) - 1 + 1 < n := by have := j.isLt; omega
      rw [Finset.prod_eq_single_of_mem (chainA hlt) (Finset.mem_univ _)
        (fun k _ hk => by
          rw [if_neg]
          rintro ⟨hc, -⟩
          exact hk (Fin.ext (show (k : ℕ) = (j : ℕ) - 1 from by omega)))]
      rw [leftNbrSign, dif_pos hj]
      have hc : (chainA hlt : ℕ) + 1 = (j : ℕ) := by
        show (j : ℕ) - 1 + 1 = (j : ℕ)
        omega
      simp [hc]
    · rw [leftNbrSign, dif_neg hj]
      exact Finset.prod_eq_one fun k _ => by
        rw [if_neg]
        rintro ⟨hc, -⟩
        omega
  · by_cases hj : (j : ℕ) + 1 < n
    · rw [Finset.prod_eq_single_of_mem (chainB hj) (Finset.mem_univ _)
        (fun k _ hk => by
          rw [if_neg]
          rintro ⟨hc, -⟩
          exact hk (Fin.ext (show (k : ℕ) = (j : ℕ) + 1 from by omega)))]
      rw [rightNbrSign, dif_pos hj]
      have hc : (j : ℕ) + 1 = (chainB hj : ℕ) := rfl
      simp [← hc]
    · rw [rightNbrSign, dif_neg hj]
      exact Finset.prod_eq_one fun k _ => by
        rw [if_neg]
        rintro ⟨hc, -⟩
        exact hj (hc ▸ k.isLt)

/-- The **left flip-correction** at edge `i`: the factor by which the `i`-th
edge sign changes when bit `j` is flipped and `i + 1 = j`. -/
noncomputable def lCorr (n : ℕ) (j : ℕ) (m : Fin n → Bool) (i : ℕ) : ℂ :=
  if h : i + 1 < n then (if i + 1 = j ∧ m (chainA h) then -1 else 1) else 1

/-- The **right flip-correction** at edge `i`: the factor by which the `i`-th
edge sign changes when bit `j` is flipped and `i = j`. -/
noncomputable def rCorr (n : ℕ) (j : ℕ) (m : Fin n → Bool) (i : ℕ) : ℂ :=
  if h : i + 1 < n then (if i = j ∧ m (chainB h) then -1 else 1) else 1

/-- Flipping bit `j` changes the `i`-th edge sign by exactly the two
flip-corrections: the edge is touched iff it meets the site `j`, and then the
sign flips iff the *other* endpoint stores `1`. -/
theorem edgeSign_update (n : ℕ) (j : Fin n) (m : Fin n → Bool) (i : ℕ) :
    edgeSign n (Function.update m j (!(m j))) i
      = edgeSign n m i * (lCorr n (j : ℕ) m i * rCorr n (j : ℕ) m i) := by
  by_cases h : i + 1 < n
  · rw [edgeSign_of_lt h, edgeSign_of_lt h, lCorr, rCorr, dif_pos h, dif_pos h]
    by_cases hL : i + 1 = (j : ℕ)
    · have hBj : chainB h = j := Fin.ext hL
      have hAj : chainA h ≠ j := fun hc => by
        have : (i : ℕ) = (j : ℕ) := congrArg Fin.val hc
        omega
      have hR : ¬(i = (j : ℕ)) := by omega
      rw [Function.update_of_ne hAj, hBj, Function.update_self]
      cases m (chainA h) <;> cases m j <;> norm_num [hL, hR]
    · by_cases hM : i = (j : ℕ)
      · have hAj : chainA h = j := Fin.ext hM
        have hBj : chainB h ≠ j := fun hc => by
          have : (i : ℕ) + 1 = (j : ℕ) := congrArg Fin.val hc
          omega
        rw [Function.update_of_ne hBj, hAj, Function.update_self]
        cases m j <;> cases m (chainB h) <;> norm_num [hL, hM]
      · have hAj : chainA h ≠ j := fun hc => hM (congrArg Fin.val hc)
        have hBj : chainB h ≠ j := fun hc => hL (congrArg Fin.val hc)
        rw [Function.update_of_ne hAj, Function.update_of_ne hBj]
        norm_num [hL, hM]
  · simp only [edgeSign, lCorr, rCorr, dif_neg h]
    ring

/-- Flipping bit `j` multiplies the accumulated sign by the product of all the
flip-corrections. -/
theorem czSign_update (n : ℕ) (j : Fin n) (m : Fin n → Bool) (k : ℕ) :
    czSign n k (Function.update m j (!(m j)))
      = czSign n k m * ((∏ i ∈ Finset.range k, lCorr n (j : ℕ) m i)
          * ∏ i ∈ Finset.range k, rCorr n (j : ℕ) m i) := by
  rw [czSign, Finset.prod_congr rfl fun i _ => edgeSign_update n j m i,
    Finset.prod_mul_distrib, Finset.prod_mul_distrib, ← czSign]

/-- Over the **full** edge set `range (n-1)` the left flip-corrections
collapse to the left parity sign: the only candidate edge is `(j-1, j)`, and
it is in range exactly when `j` has a left neighbour. -/
theorem prod_lCorr (n : ℕ) (j : Fin n) (m : Fin n → Bool) :
    ∏ i ∈ Finset.range (n - 1), lCorr n (j : ℕ) m i = leftNbrSign n j m := by
  by_cases hj : 1 ≤ (j : ℕ)
  · have hjn : (j : ℕ) < n := j.isLt
    have hlt : (j : ℕ) - 1 + 1 < n := by omega
    have hmem : (j : ℕ) - 1 ∈ Finset.range (n - 1) := Finset.mem_range.mpr (by omega)
    rw [Finset.prod_eq_single_of_mem ((j : ℕ) - 1) hmem
      (fun b hb hbj => by
        have hb' : b + 1 < n := by
          have := Finset.mem_range.mp hb
          omega
        rw [lCorr, dif_pos hb', if_neg]
        rintro ⟨hc, -⟩
        omega)]
    rw [lCorr, dif_pos hlt, leftNbrSign, dif_pos hj]
    have hc : (j : ℕ) - 1 + 1 = (j : ℕ) := by omega
    simp [hc]
  · rw [leftNbrSign, dif_neg hj]
    exact Finset.prod_eq_one fun b hb => by
      by_cases hb' : b + 1 < n
      · rw [lCorr, dif_pos hb', if_neg]
        rintro ⟨hc, -⟩
        omega
      · rw [lCorr, dif_neg hb']

/-- Over the full edge set the right flip-corrections collapse to the right
parity sign: the only candidate edge is `(j, j+1)`, in range exactly when `j`
has a right neighbour. -/
theorem prod_rCorr (n : ℕ) (j : Fin n) (m : Fin n → Bool) :
    ∏ i ∈ Finset.range (n - 1), rCorr n (j : ℕ) m i = rightNbrSign n j m := by
  by_cases hj : (j : ℕ) + 1 < n
  · have hmem : (j : ℕ) ∈ Finset.range (n - 1) := Finset.mem_range.mpr (by omega)
    rw [Finset.prod_eq_single_of_mem ((j : ℕ)) hmem
      (fun b hb hbj => by
        by_cases hb' : b + 1 < n
        · rw [rCorr, dif_pos hb', if_neg]
          rintro ⟨hc, -⟩
          exact hbj hc
        · rw [rCorr, dif_neg hb'])]
    rw [rCorr, dif_pos hj, rightNbrSign, dif_pos hj]
    simp
  · rw [rightNbrSign, dif_neg hj]
    exact Finset.prod_eq_one fun b hb => by
      by_cases hb' : b + 1 < n
      · rw [rCorr, dif_pos hb', if_neg]
        rintro ⟨hc, -⟩
        omega
      · rw [rCorr, dif_neg hb']

/-- **The sign bookkeeping closes**: on the full edge set of the chain, the
accumulated sign of the bit-`j`-flipped assignment is the accumulated sign of
the assignment times the two neighbour parity signs of `K_j` — the `Z`
letters compensate exactly the edge-sign flips the `X` letter causes. -/
theorem czSign_mul_ph (n : ℕ) (j : Fin n) (m : Fin n → Bool) :
    czSign n (n - 1) m * ∏ k, (stabLetter n j k).ph (m k)
      = czSign n (n - 1) (Function.update m j (!(m j))) := by
  rw [prod_stabLetter_ph, czSign_update n j m (n - 1), prod_lCorr, prod_rCorr]

/-- The action of `K_j` on a computational basis ket: flip bit `j`, multiply
by the neighbour parity signs — the Pauli-string master action lemma
(`pauliString_deltav`) at the stabilizer letter assignment. -/
theorem clusterStab_deltav (n : ℕ) (j : Fin n) (m : Fin n → Bool) :
    clusterStab n j (deltav (QubitD n) (qbIdx (QubitL n) m))
      = (∏ k, (stabLetter n j k).ph (m k)) •
          deltav (QubitD n) (qbIdx (QubitL n) (Function.update m j (!(m j)))) := by
  rw [clusterStab, pauliString_deltav, stabLetter_flips]

/-- **The stabilizer property** (the abstract graph-state specification of the
1D cluster state): `∣C_n⟩` is a `+1`-eigenvector of every cluster stabilizer,

```
K_j ∣C_n⟩ = ∣C_n⟩,   K_j = Z_{j-1} X_j Z_{j+1}   (j = 0, …, n-1).
```

Coordinatewise on `clusterFam_eq_sum`: `K_j` sends the signed basis term of
`y` to the signed basis term of `y` with bit `j` flipped (`clusterStab_deltav`
+ `czSign_mul_ph`), and flipping bit `j` permutes the basis sum. -/
theorem clusterStab_clusterVec (n : ℕ) (j : Fin n) :
    clusterStab n j (clusterVec n) = clusterVec n := by
  have hinv : Function.Involutive
      (fun m : Fin n → Bool => Function.update m j (!(m j))) := by
    intro m
    simp only [Function.update_self, Bool.not_not, Function.update_idem,
      Function.update_eq_self]
  have hsum : clusterVec n
      = ∑ m : Fin n → Bool,
          (((Real.sqrt 2 : ℂ))⁻¹ ^ n * czSign n (n - 1) m)
            • deltav (QubitD n) (qbIdx (QubitL n) m) := clusterFam_eq_sum n (n - 1)
  rw [hsum, map_sum,
    Finset.sum_congr rfl fun m _ => by
      rw [map_smul, clusterStab_deltav, smul_smul, mul_assoc, czSign_mul_ph]]
  exact Fintype.sum_bijective _ hinv.bijective _ _ fun m => rfl

end Stabilizer

end Qhl
