import Qhl.Register.PauliString

/-!
# Prefix chains of a Pauli string

A `for`-fold that applies the letters of a Pauli string site by site builds,
after `m` rungs, the **prefix operator** `stringTake n P m` — the composition
of the first `m` one-site letter gates.  This file provides the three facts a
loop derivation needs: the prefix starts at the identity (`stringTake_zero`),
each rung advances it by one site gate (`stringTake_succ`), and the full
prefix **is** the Pauli string (`stringTake_top`, via order-invariance of
`stringOn` on `Nodup` covers).
-/

namespace Qhl

open Finset

section

variable {L : Type*} [Fintype L] [DecidableEq L]

/-- `stringOn` over any `Nodup` list that covers every site is the full
Pauli string (site order is immaterial). -/
theorem stringOn_eq_pauliString (P : L → PLetter) (l : List L) (hl : l.Nodup)
    (hcov : ∀ a, a ∈ l) : stringOn P l = pauliString P := by
  refine qubitEndM_ext fun f => ?_
  rw [stringOn_deltav P l hl f, pauliString_deltav]
  have h1 : l.toFinset = univ := by
    ext a
    simp [hcov a]
  have h2 : (fun k => if k ∈ l then xor (P k).flips (f k) else f k)
      = fun k => xor (P k).flips (f k) := by
    funext k
    rw [if_pos (hcov k)]
  rw [h1, h2]

end

section Take

variable {n : ℕ}

/-- The prefix operator: the letters of the first `m` sites applied, in
application order (site `0` first). -/
noncomputable def stringTake (P : Fin n → PLetter) (m : ℕ) :
    EndM (QubitCells (Fin n)) (univ : Finset (Fin n)) :=
  stringOn P (((List.finRange n).take m).reverse)

@[simp]
theorem stringTake_zero (P : Fin n → PLetter) : stringTake P 0 = 1 := rfl

/-- One rung advances the prefix by the site gate at position `m`. -/
theorem stringTake_succ (P : Fin n → PLetter) (m : ℕ) (hm : m < n) :
    stringTake P (m + 1)
      = gateAt (Fin n) ⟨m, hm⟩ (P ⟨m, hm⟩).gate ∘ₗ stringTake P m := by
  rw [stringTake, stringTake]
  have htake : (List.finRange n).take (m + 1)
      = (List.finRange n).take m ++ [⟨m, hm⟩] := by
    rw [List.take_succ]
    congr 1
    have hlt : m < (List.finRange n).length := by
      rwa [List.length_finRange]
    rw [List.getElem?_eq_getElem hlt]
    simp [List.getElem_finRange]
  rw [htake, List.reverse_append]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
  rw [stringOn_cons]

/-- The full prefix is the Pauli string. -/
theorem stringTake_top (P : Fin n → PLetter) : stringTake P n = pauliString P := by
  rw [stringTake]
  refine stringOn_eq_pauliString P _ ?_ ?_
  · rw [List.nodup_reverse]
    exact (List.nodup_finRange n).sublist (List.take_sublist _ _)
  · intro a
    rw [List.mem_reverse]
    have : (List.finRange n).take n = List.finRange n := by
      apply List.take_of_length_le
      rw [List.length_finRange]
    rw [this]
    exact List.mem_finRange a

end Take

end Qhl
