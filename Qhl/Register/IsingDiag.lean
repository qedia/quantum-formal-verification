import Qhl.Register.Qubits
import Qhl.Gate.Rzz
import Qhl.Logic.Frame

/-!
# The diagonal Ising model on the standard `n`-qubit world

The operator layer of the Trotterized Ising-simulation example
(`Qhl/Examples/TrotterIsingTriple.lean`): the classical energy function of the
diagonal Ising Hamiltonian

```
H  =  Σ_{j<n} a j · Z_j  +  Σ_{j<n-1} b j · Z_j Z_{j+1},
E(y) =  Σ_{j<n} a j · z(y_j)  +  Σ_{j<n-1} b j · z(y_j) z(y_{j+1}),
```

with `z(false) = 1`, `z(true) = -1` (`zsign`, the `Rz` sign convention of
`Qhl/Gate/Qubit.lean`), and the diagonal evolution operator
`isingEvo θ = e^{-iθH} : ∣y⟩ ↦ e^{-iθE(y)} ∣y⟩`, a `diagOp` on the whole
`n`-qubit space, together with:

* `phaseDiag f` — the diagonal phase gate `∣y⟩ ↦ e^{-i f(y)} ∣y⟩` of a real
  phase function on the whole computational basis (the `n`-qubit generalisation
  of the one/two-site diagonals `Rz`, `CZ`, `cphase`), with the group laws
  `phaseDiag_phaseDiag` (phases add) and `phaseDiag_zero_apply` (zero phase is
  the identity) — whence `isingEvo α ∘ isingEvo β = isingEvo (α+β)` and
  `isingEvo 0 = 1`;
* the basis actions of the *lifted* slice gates — `gateAt_Rz_deltav` (a lifted
  one-site `Rz` is a pure phase on every basis ket) and `regLift_Rzz_deltav`
  (a lifted two-site `Rzz` likewise), via the library bridges `gateAt_prodV`
  and `regLift_pairGate_prodV`;
* the **phase-absorption laws** `gateAt_Rz_phaseDiag` and
  `regLift_Rzz_phaseDiag`: composing one slice gate with a diagonal phase adds
  the gate's site term to the phase function. Together with the partial-sum
  recursions `singleE_succ`/`coupleE_succ` these are the slice factorization —
  the composite of the `n + (n-1)` lifted slice gates is `isingEvo (θ/N)` —
  in the stage-by-stage form the invariant-chain rule
  `DerivTot.forProg_finRange_chain` consumes.

All Ising terms are diagonal, hence commute, so the first-order Trotter product
formula is **exact** here (no Trotter-error term); see the example file.
-/

namespace Qhl

open Finset

/-! ## §0. A generic slot of tensor algebra: scaling one factor of `prodV` -/

section Generic

variable {L : Type*} [DecidableEq L]
variable (D : L → Type*) [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable {W : Finset L}

/-- Scaling one factor of a per-cell product state scales the product state:
`⊗ (ψ with a ↦ c • v) = c • ⊗ (ψ with a ↦ v)` — the multilinearity of CoqQ's
`tenvm` in one slot. Generic tensor algebra: no gate, no model. -/
theorem prodV_update_smul (ψ : ∀ i, EuclideanSpace ℂ (D i)) (a : L) (ha : a ∈ W)
    (c : ℂ) (v : EuclideanSpace ℂ (D a)) :
    prodV D (W := W) (Function.update ψ a (c • v))
      = c • prodV D (W := W) (Function.update ψ a v) := by
  refine PiLp.ext fun l => ?_
  have hP : ∀ w : EuclideanSpace ℂ (D a),
      ∏ i ∈ Finset.univ.erase (⟨a, ha⟩ : ↥W), Function.update ψ a w (i : L) (l i)
        = ∏ i ∈ Finset.univ.erase (⟨a, ha⟩ : ↥W), ψ (i : L) (l i) := by
    intro w
    refine Finset.prod_congr rfl fun i hi => ?_
    have hia : (i : L) ≠ a := fun hc => (Finset.mem_erase.mp hi).1 (Subtype.ext hc)
    rw [Function.update_of_ne hia]
  rw [PiLp.smul_apply, prodV_apply, prodV_apply, smul_eq_mul,
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (⟨a, ha⟩ : ↥W)),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (⟨a, ha⟩ : ↥W)),
    hP (c • v), hP v]
  change Function.update ψ a (c • v) a (l ⟨a, ha⟩) * _
      = c * (Function.update ψ a v a (l ⟨a, ha⟩) * _)
  rw [Function.update_self, Function.update_self, PiLp.smul_apply, smul_eq_mul, mul_assoc]

end Generic

/-! ## §1. Whole-world basis kets of the `n`-qubit world -/

section World

variable (n : ℕ)

/-- The bit of a whole-world classical state at the site `i`. -/
def bitAt (m : QIdx (QubitD n) (univ : Finset (QubitL n))) (i : QubitL n) : Bool :=
  m ⟨i, Finset.mem_univ i⟩

/-- A whole-world basis ket is the per-cell product of one-qubit basis kets
(`prodV_single` read at a whole-world classical state). -/
theorem deltav_eq_prodV (m : QIdx (QubitD n) (univ : Finset (QubitL n))) :
    deltav (QubitD n) m
      = prodV (QubitD n) (W := (univ : Finset (QubitL n)))
          (fun i => EuclideanSpace.single (bitAt n m i) 1) := by
  rw [prodV_single]
  exact congrArg (deltav (QubitD n))
    (funext fun i => congrArg m (Subtype.ext rfl))

/-- A lifted one-site `Rz` is a pure phase on every whole-world basis ket:
`Rz φ` at site `i` sends `∣y⟩` to `e^{-i(φ/2)·z(yᵢ)} ∣y⟩`. -/
theorem gateAt_Rz_deltav (i : QubitL n) (φ : ℝ)
    (m : QIdx (QubitD n) (univ : Finset (QubitL n))) :
    gateAt (QubitL n) i (Rz φ) (deltav (QubitD n) m)
      = Complex.exp ((-(φ / 2 * zsign (bitAt n m i)) : ℝ) * Complex.I) •
          deltav (QubitD n) m := by
  rw [deltav_eq_prodV, gateAt_prodV, Rz_single,
    prodV_update_smul (QubitD n) _ i (Finset.mem_univ i), Function.update_eq_self]

/-- A lifted two-site `Rzz` at the pair `(a, b)` is a pure phase on every
whole-world basis ket: `∣y⟩ ↦ e^{-i(φ/2)·z(yₐ)z(y_b)} ∣y⟩`. -/
theorem regLift_Rzz_deltav (a b : QubitL n) (hab : a ≠ b) (φ : ℝ)
    (m : QIdx (QubitD n) (univ : Finset (QubitL n))) :
    regLift (Reg.pair a b hab) (pairGate (D := QubitD n) a b hab (Rzz φ)) (deltav (QubitD n) m)
      = Complex.exp
          ((-(φ / 2 * (zsign (bitAt n m a) * zsign (bitAt n m b))) : ℝ) * Complex.I) •
          deltav (QubitD n) m := by
  rw [deltav_eq_prodV,
    regLift_pairGate_prodV a b hab (Rzz φ)
      (fun j => EuclideanSpace.single (bitAt n m j) 1)
      (Rzz_vpair φ (bitAt n m a) (bitAt n m b))]
  have h1 : Function.update
        (Function.update (fun j => EuclideanSpace.single (bitAt n m j) (1 : ℂ)) a
          (Complex.exp
            ((-(φ / 2 * (zsign (bitAt n m a) * zsign (bitAt n m b))) : ℝ) * Complex.I) •
            EuclideanSpace.single (bitAt n m a) (1 : ℂ)))
        b (EuclideanSpace.single (bitAt n m b) (1 : ℂ))
      = Function.update (fun j => EuclideanSpace.single (bitAt n m j) (1 : ℂ)) a
          (Complex.exp
            ((-(φ / 2 * (zsign (bitAt n m a) * zsign (bitAt n m b))) : ℝ) * Complex.I) •
            EuclideanSpace.single (bitAt n m a) (1 : ℂ)) := by
    rw [show EuclideanSpace.single (bitAt n m b) (1 : ℂ)
        = Function.update (fun j => EuclideanSpace.single (bitAt n m j) (1 : ℂ)) a
            (Complex.exp
              ((-(φ / 2 * (zsign (bitAt n m a) * zsign (bitAt n m b))) : ℝ) * Complex.I) •
              EuclideanSpace.single (bitAt n m a) (1 : ℂ)) b
      from (Function.update_of_ne (Ne.symm hab)
        (Complex.exp
          ((-(φ / 2 * (zsign (bitAt n m a) * zsign (bitAt n m b))) : ℝ) * Complex.I) •
          EuclideanSpace.single (bitAt n m a) (1 : ℂ))
        (fun j => EuclideanSpace.single (bitAt n m j) (1 : ℂ))).symm]
    exact Function.update_eq_self _ _
  rw [h1, prodV_update_smul (QubitD n) _ a (Finset.mem_univ a), Function.update_eq_self,
    ← deltav_eq_prodV]

/-! ## §2. The diagonal phase gate of a whole-world phase function -/

/-- The diagonal phase gate `∣y⟩ ↦ e^{-i f(y)} ∣y⟩` of a real phase function on
the whole computational basis — the `n`-qubit generalisation of the one/two-site
unit-modulus diagonals `Rz`, `CZ`, `cphase` (`diagOp`, so unitary for free). -/
noncomputable def phaseDiag (f : QIdx (QubitD n) (univ : Finset (QubitL n)) → ℝ) :
    UnitaryOp (HS (QubitD n) (univ : Finset (QubitL n))) :=
  diagOp (fun m => Complex.exp ((-(f m) : ℝ) * Complex.I))
    (fun _ => Complex.norm_exp_ofReal_mul_I _)

/-- The defining basis action of `phaseDiag`. -/
theorem phaseDiag_deltav (f : QIdx (QubitD n) (univ : Finset (QubitL n)) → ℝ)
    (m : QIdx (QubitD n) (univ : Finset (QubitL n))) :
    (phaseDiag n f : HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
        HS (QubitD n) (univ : Finset (QubitL n))) (deltav (QubitD n) m)
      = Complex.exp ((-(f m) : ℝ) * Complex.I) • deltav (QubitD n) m := by
  rw [deltav_def, phaseDiag, diagOp_single, mul_one, single_eq_smul_single]

/-- Diagonal phases add: `phaseDiag f ∘ phaseDiag g = phaseDiag (f + g)`
pointwise — the group law of the diagonal evolutions. -/
theorem phaseDiag_phaseDiag (f g : QIdx (QubitD n) (univ : Finset (QubitL n)) → ℝ)
    (v : HS (QubitD n) (univ : Finset (QubitL n))) :
    (phaseDiag n f : HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
        HS (QubitD n) (univ : Finset (QubitL n)))
        ((phaseDiag n g : HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
          HS (QubitD n) (univ : Finset (QubitL n))) v)
      = (phaseDiag n (fun m => f m + g m) : HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
          HS (QubitD n) (univ : Finset (QubitL n))) v := by
  ext m
  simp only [phaseDiag, diagOp_apply]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The zero phase is the identity. -/
theorem phaseDiag_zero_apply (v : HS (QubitD n) (univ : Finset (QubitL n))) :
    (phaseDiag n (fun _ => 0) : HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
        HS (QubitD n) (univ : Finset (QubitL n))) v = v := by
  ext m
  simp only [phaseDiag, diagOp_apply]
  norm_num

/-! ## §3. The phase-absorption laws of the slice gates

One slice gate composed with a diagonal phase adds its site term to the phase
function. These two laws, driven along the partial-sum recursions
`singleE_succ`/`coupleE_succ` of §4, are the slice factorization — the
composite of all `n + (n-1)` lifted slice gates equals `isingEvo (θ/N)` — in
the stage-by-stage form the invariant-chain rule consumes. -/

/-- Absorbing a lifted one-site `Rz` into a diagonal phase. -/
theorem gateAt_Rz_phaseDiag (i : QubitL n) (φ : ℝ)
    (f : QIdx (QubitD n) (univ : Finset (QubitL n)) → ℝ)
    (v : HS (QubitD n) (univ : Finset (QubitL n))) :
    gateAt (QubitL n) i (Rz φ)
        ((phaseDiag n f : HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
          HS (QubitD n) (univ : Finset (QubitL n))) v)
      = (phaseDiag n (fun m => f m + φ / 2 * zsign (bitAt n m i)) :
          HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
          HS (QubitD n) (univ : Finset (QubitL n))) v := by
  have h : gateAt (QubitL n) i (Rz φ) ∘ₗ
      (phaseDiag n f : HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
        HS (QubitD n) (univ : Finset (QubitL n)))
      = (phaseDiag n (fun m => f m + φ / 2 * zsign (bitAt n m i)) :
          HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
          HS (QubitD n) (univ : Finset (QubitL n))) := by
    refine linM_ext (QubitD n) fun m => ?_
    rw [LinearMap.comp_apply, phaseDiag_deltav, map_smul, gateAt_Rz_deltav,
      phaseDiag_deltav, smul_smul, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  exact DFunLike.congr_fun h v

/-- Absorbing a lifted two-site `Rzz` into a diagonal phase. -/
theorem regLift_Rzz_phaseDiag (a b : QubitL n) (hab : a ≠ b) (φ : ℝ)
    (f : QIdx (QubitD n) (univ : Finset (QubitL n)) → ℝ)
    (v : HS (QubitD n) (univ : Finset (QubitL n))) :
    regLift (Reg.pair a b hab) (pairGate (D := QubitD n) a b hab (Rzz φ))
        ((phaseDiag n f : HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
          HS (QubitD n) (univ : Finset (QubitL n))) v)
      = (phaseDiag n
          (fun m => f m + φ / 2 * (zsign (bitAt n m a) * zsign (bitAt n m b))) :
          HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
          HS (QubitD n) (univ : Finset (QubitL n))) v := by
  have h : regLift (Reg.pair a b hab) (pairGate (D := QubitD n) a b hab (Rzz φ)) ∘ₗ
      (phaseDiag n f : HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
        HS (QubitD n) (univ : Finset (QubitL n)))
      = (phaseDiag n
          (fun m => f m + φ / 2 * (zsign (bitAt n m a) * zsign (bitAt n m b))) :
          HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
          HS (QubitD n) (univ : Finset (QubitL n))) := by
    refine linM_ext (QubitD n) fun m => ?_
    rw [LinearMap.comp_apply, phaseDiag_deltav, map_smul, regLift_Rzz_deltav,
      phaseDiag_deltav, smul_smul, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  exact DFunLike.congr_fun h v

end World

/-! ## §4. The Ising energy and its partial sums -/

section Model

variable (n : ℕ) (a : Fin n → ℝ) (b : Fin (n - 1) → ℝ)

/-- The left cell of the `j`-th coupling `Z_j Z_{j+1}`. -/
def loCell (j : Fin (n - 1)) : Fin n := ⟨(j : ℕ), by have := j.isLt; omega⟩

/-- The right cell of the `j`-th coupling `Z_j Z_{j+1}`. -/
def hiCell (j : Fin (n - 1)) : Fin n := ⟨(j : ℕ) + 1, by have := j.isLt; omega⟩

/-- The two cells of a coupling are distinct (`Dist(q̄)` of the `Rzz` step). -/
theorem loCell_ne_hiCell (j : Fin (n - 1)) : loCell n j ≠ hiCell n j := by
  simp only [loCell, hiCell, ne_eq, Fin.mk.injEq]
  omega

/-- The single-site part of the Ising energy, restricted to the sites `< k`:
`Σ_{i<k} aᵢ · z(yᵢ)`. -/
noncomputable def singleE (k : ℕ) (m : QIdx (QubitD n) (univ : Finset (QubitL n))) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), a i * zsign (bitAt n m i)

/-- The coupling part of the Ising energy, restricted to the couplings `< k`:
`Σ_{j<k} bⱼ · z(yⱼ)z(yⱼ₊₁)`. -/
noncomputable def coupleE (k : ℕ) (m : QIdx (QubitD n) (univ : Finset (QubitL n))) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin (n - 1) => (j : ℕ) < k),
    b j * (zsign (bitAt n m (loCell n j)) * zsign (bitAt n m (hiCell n j)))

/-- The classical Ising energy
`E(y) = Σ_{j<n} aⱼ z(yⱼ) + Σ_{j<n-1} bⱼ z(yⱼ)z(yⱼ₊₁)`. -/
noncomputable def energy (m : QIdx (QubitD n) (univ : Finset (QubitL n))) : ℝ :=
  singleE n a n m + coupleE n b (n - 1) m

private theorem filter_lt_succ {k : ℕ} (i : Fin k) :
    Finset.univ.filter (fun j : Fin k => (j : ℕ) < (i : ℕ) + 1)
      = insert i (Finset.univ.filter (fun j : Fin k => (j : ℕ) < (i : ℕ))) := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Nat.lt_succ_iff_lt_or_eq, Fin.ext_iff]
  tauto

/-- No site is below `0`: the empty partial sum. -/
theorem singleE_zero (m : QIdx (QubitD n) (univ : Finset (QubitL n))) :
    singleE n a 0 m = 0 := by
  rw [singleE, Finset.filter_false_of_mem fun i _ => by omega, Finset.sum_empty]

/-- The partial-sum recursion of the single-site part: one more site adds its
term. -/
theorem singleE_succ (i : Fin n) (m : QIdx (QubitD n) (univ : Finset (QubitL n))) :
    singleE n a ((i : ℕ) + 1) m = singleE n a (i : ℕ) m + a i * zsign (bitAt n m i) := by
  rw [singleE, filter_lt_succ, Finset.sum_insert (by simp), singleE, add_comm]

/-- No coupling is below `0`: the empty partial sum. -/
theorem coupleE_zero (m : QIdx (QubitD n) (univ : Finset (QubitL n))) :
    coupleE n b 0 m = 0 := by
  rw [coupleE, Finset.filter_false_of_mem fun j _ => by omega, Finset.sum_empty]

/-- The partial-sum recursion of the coupling part: one more coupling adds its
term. -/
theorem coupleE_succ (j : Fin (n - 1)) (m : QIdx (QubitD n) (univ : Finset (QubitL n))) :
    coupleE n b ((j : ℕ) + 1) m
      = coupleE n b (j : ℕ) m
        + b j * (zsign (bitAt n m (loCell n j)) * zsign (bitAt n m (hiCell n j))) := by
  rw [coupleE, filter_lt_succ, Finset.sum_insert (by simp), coupleE, add_comm]

/-! ## §5. The diagonal Ising evolution `e^{-iθH}` -/

/-- The diagonal Ising evolution `isingEvo θ = e^{-iθH} : ∣y⟩ ↦ e^{-iθE(y)} ∣y⟩`. -/
noncomputable def isingEvo (θ : ℝ) :
    UnitaryOp (HS (QubitD n) (univ : Finset (QubitL n))) :=
  phaseDiag n (fun m => θ * energy n a b m)

/-- The defining basis action of the Ising evolution. -/
theorem isingEvo_deltav (θ : ℝ) (m : QIdx (QubitD n) (univ : Finset (QubitL n))) :
    (isingEvo n a b θ : HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
        HS (QubitD n) (univ : Finset (QubitL n))) (deltav (QubitD n) m)
      = Complex.exp ((-(θ * energy n a b m) : ℝ) * Complex.I) • deltav (QubitD n) m :=
  phaseDiag_deltav n _ m

/-- The evolution group law `e^{-iαH} e^{-iβH} = e^{-i(α+β)H}` — the exactness
of the product formula for a family of commuting (here: simultaneously
diagonal) Hamiltonian terms. -/
theorem isingEvo_isingEvo (α β : ℝ) (v : HS (QubitD n) (univ : Finset (QubitL n))) :
    (isingEvo n a b α : HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
        HS (QubitD n) (univ : Finset (QubitL n)))
        ((isingEvo n a b β : HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
          HS (QubitD n) (univ : Finset (QubitL n))) v)
      = (isingEvo n a b (α + β) : HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
          HS (QubitD n) (univ : Finset (QubitL n))) v := by
  rw [isingEvo, isingEvo, isingEvo, phaseDiag_phaseDiag]
  exact congrArg
    (fun f => (phaseDiag n f : HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
      HS (QubitD n) (univ : Finset (QubitL n))) v)
    (funext fun m => by ring)

/-- The zero-time evolution is the identity: `e^{-i·0·H} = 1`. -/
theorem isingEvo_zero (v : HS (QubitD n) (univ : Finset (QubitL n))) :
    (isingEvo n a b 0 : HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
        HS (QubitD n) (univ : Finset (QubitL n))) v = v := by
  rw [isingEvo,
    show (fun m => (0 : ℝ) * energy n a b m) = fun _ => (0 : ℝ) from
      funext fun m => by ring]
  exact phaseDiag_zero_apply n v

end Model

end Qhl
