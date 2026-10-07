import Qhl.HSpace.TenV

/-!
# M2 acceptance demo: a Bell state on two labelled qubits

Two qubits labelled by `Bool` (registers `{false}` and `{true}`); the
unnormalized Bell vector `|00⟩ + |11⟩` built with the `⊗ᵥ` notation, its
basis-ket form via `deltav_merge`, and `⟪bell, bell⟫ = 2` via `tenv_inner`
and `dv_dot`.
-/

namespace Qhl.Bell

open Finset
open scoped ComplexInnerProductSpace Qhl

/-- Two qubits, one for each label. -/
abbrev Qubit : Bool → Type := fun _ => Bool

/-- Classical states `0`/`1` of the first qubit. -/
def k₀ : QIdx Qubit {false} := fun _ => false

@[inherit_doc k₀]
def k₁ : QIdx Qubit {false} := fun _ => true

/-- Classical states `0`/`1` of the second qubit. -/
def l₀ : QIdx Qubit {true} := fun _ => false

@[inherit_doc l₀]
def l₁ : QIdx Qubit {true} := fun _ => true

/-- The unnormalized Bell state `|00⟩ + |11⟩` on the joint register. -/
noncomputable def bell : HS Qubit ({false} ∪ {true}) :=
  deltav Qubit k₀ ⊗ᵥ deltav Qubit l₀ + deltav Qubit k₁ ⊗ᵥ deltav Qubit l₁

/-- The two registers are disjoint. -/
theorem disj : Disjoint ({false} : Finset Bool) {true} := by decide

/-- `bell` is a sum of two basis kets of the joint register (`deltav_merge`). -/
example : bell =
    deltav Qubit (QIdx.merge Qubit k₀ l₀) + deltav Qubit (QIdx.merge Qubit k₁ l₁) := by
  simp [bell, deltav_merge Qubit disj]

/-- M2 acceptance: the squared norm of the Bell vector is `2`, by bilinearity
of the inner product, `tenv_inner`, and `dv_dot`. -/
example : ⟪bell, bell⟫ = 2 := by
  have h : k₀ ≠ k₁ := fun h => by
    simpa [k₀, k₁] using congrFun h ⟨false, Finset.mem_singleton_self false⟩
  rw [bell, inner_add_left, inner_add_right, inner_add_right,
    tenv_inner Qubit disj, tenv_inner Qubit disj, tenv_inner Qubit disj,
    tenv_inner Qubit disj, dv_dot Qubit k₀ k₀, dv_dot Qubit k₀ k₁,
    dv_dot Qubit k₁ k₀, dv_dot Qubit k₁ k₁, dv_dot Qubit l₀ l₀,
    dv_dot Qubit l₀ l₁, dv_dot Qubit l₁ l₀, dv_dot Qubit l₁ l₁]
  simp [h, h.symm, one_add_one_eq_two]

end Qhl.Bell
