import Qhl.Program.GhostParameters
import Qhl.Logic.Assertion

/-! # Executing a program with an immutable classical ghost component -/

namespace Qhl

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)] {σT V : Type*}

namespace CQState

/-- Add a ghost value to a state without changing its quantum operator. -/
def withGhost (z : V) (s : CQState σT D) : CQState (σT × V) D :=
  ⟨(s.cls, z), s.q⟩

end CQState

namespace Control

/-- Transport a control to the product store, leaving its ghost component untouched. -/
def withGhost (_z : V) : Control σT D → Control (σT × V) D
  | .done => .done
  | .running P => .running (P.mapStore (StoreLens.fst (R := V)))

/-- Ghost transport commutes with sequencing of controls. -/
theorem withGhost_seqWith (z : V) (c : Control σT D) (P : Prog σT D) :
    (c.seqWith P).withGhost z =
      (c.withGhost z).seqWith (P.mapStore (StoreLens.fst (R := V))) := by
  cases c <;> rfl

end Control

namespace Config

/-- Transport a configuration into a product store at a fixed ghost value. -/
def withGhost (z : V) (c : Config σT D) : Config (σT × V) D :=
  ⟨c.ctrl.withGhost z, (c.cls, z), c.q⟩

/-- Configuration state transport agrees with cq-state transport. -/
theorem withGhost_st (z : V) (c : Config σT D) :
    (c.withGhost z).st = c.st.withGhost z := rfl

/-- Initial configurations commute with ghost transport. -/
theorem withGhost_init (z : V) (P : Prog σT D) (s : CQState σT D) :
    (Config.init P s).withGhost z =
      Config.init (P.mapStore (StoreLens.fst (R := V))) (s.withGhost z) := rfl

/-- Termination status does not depend on the ghost. -/
theorem withGhost_isDone (z : V) (c : Config σT D) :
    (c.withGhost z).isDone = c.isDone := by
  cases c with
  | mk ctrl σ ρ => cases ctrl <;> rfl

/-- Quantum mass does not depend on the ghost. -/
theorem withGhost_mass (z : V) (c : Config σT D) :
    (c.withGhost z).mass = c.mass := rfl

end Config

/-- Every one-step transition of a transported program carries the same ghost. -/
theorem stepProg_withGhost (z : V) (P : Prog σT D)
    (σ : σT) (ρ : PDensity D) :
    stepProg (P.mapStore (StoreLens.fst (R := V))) (σ, z) ρ =
      (stepProg P σ ρ).map (Config.withGhost z) := by
  induction P generalizing σ ρ with
  | skip => rfl
  | assign f => rfl
  | init S => rfl
  | unitary k r U =>
      by_cases hi : Function.Injective (r σ)
      · simp [Prog.mapStore, stepProg, StoreLens.fst, hi,
          Config.withGhost, Control.withGhost]
      · simp [Prog.mapStore, stepProg, StoreLens.fst, hi]
  | measure m k r M upd =>
      by_cases hi : Function.Injective (r σ)
      · simp [Prog.mapStore, stepProg, StoreLens.fst, hi,
          Config.withGhost, Control.withGhost]
      · simp [Prog.mapStore, stepProg, StoreLens.fst, hi]
  | seq P Q ihP ihQ =>
      simp only [Prog.mapStore, stepProg]
      rw [ihP]
      simp only [List.map_map]
      apply List.map_congr_left
      intro c _
      cases c with
      | mk ctrl σ ρ =>
          simp only [Function.comp_def, Config.withGhost]
          congr 1
          exact (Control.withGhost_seqWith z ctrl Q).symm
  | ite b P Q ihP ihQ =>
      cases hb : b σ <;>
        simp [Prog.mapStore, stepProg, StoreLens.fst, hb,
          Config.withGhost, Control.withGhost]
  | «while» b P ih =>
      cases hb : b σ <;>
        simp [Prog.mapStore, stepProg, StoreLens.fst, hb,
          Config.withGhost, Control.withGhost]

/-- The successor list of a lifted configuration is the lifted original list. -/
theorem next_withGhost (z : V) (c : Config σT D) :
    next (c.withGhost z) = (next c).map (Config.withGhost z) := by
  obtain ⟨ctrl, σ, ρ⟩ := c
  cases ctrl with
  | done => rfl
  | running P => exact stepProg_withGhost z P σ ρ

/-- Every finite frontier is transported occurrence by occurrence. -/
theorem boundedFront_withGhost (z : V) (c : Config σT D) (n : ℕ) :
    boundedFront (c.withGhost z) n =
      (boundedFront c n).map (Config.withGhost z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [boundedFront_succ, ih, List.flatMap_map, boundedFront_succ]
      simp only [next_withGhost, List.map_flatMap]

/-- Terminal mass at each depth is unchanged by adding a fixed ghost. -/
theorem termMass_withGhost (z : V) (c : Config σT D) (n : ℕ) :
    termMass (c.withGhost z) n = termMass c n := by
  simp only [termMass, boundedFront_withGhost]
  rw [← map_filter_comp]
  simp only [Config.withGhost_isDone, Config.withGhost_mass]

/-- The post-expectation at one depth slices a product-store effect at the ghost. -/
theorem postAt_withGhost (z : V) (c : Config σT D) (n : ℕ)
    (A : (σT × V) → EndM D (Finset.univ : Finset L)) :
    postAt (c.withGhost z) n A = postAt c n (fun σ => A (σ, z)) := by
  simp only [postAt, boundedFront_withGhost]
  rw [← map_filter_comp]
  simp only [Config.withGhost_isDone]
  rfl

/-- Total post-expectation slices the product-store effect at the fixed ghost. -/
theorem PostH_withGhost (z : V) (c : Config σT D)
    (A : (σT × V) → EndM D (Finset.univ : Finset L)) :
    PostH (c.withGhost z) A = PostH c (fun σ => A (σ, z)) := by
  simp only [PostH, postAt_withGhost]

/-- Terminating trace mass is unchanged by the fixed ghost. -/
theorem terminatingTraceMass_withGhost (z : V) (c : Config σT D) :
    terminatingTraceMass (c.withGhost z) = terminatingTraceMass c := by
  simp only [terminatingTraceMass, termMass_withGhost]

/-- Nontermination quantity is unchanged by the fixed ghost. -/
theorem NT_withGhost (z : V) (c : Config σT D) :
    NT (c.withGhost z) = NT c := by
  simp only [NT, Config.withGhost_mass, terminatingTraceMass_withGhost]

namespace Assn

/-- Restrict a product-store assertion to one fixed ghost value. -/
def ghostSlice (A : Assn (σT × V) D) (z : V) : Assn σT D where
  op σ := A.op (σ, z)
  isEffect σ := A.isEffect (σ, z)

end Assn

/-- Total validity over a product store is equivalent to every fixed-ghost slice. -/
theorem validTot_mapStore_fst_iff (A B : Assn (σT × V) D) (P : Prog σT D) :
    validTot A (P.mapStore (StoreLens.fst (R := V))) B ↔
      ∀ z : V, validTot (A.ghostSlice z) P (B.ghostSlice z) := by
  constructor
  · intro h z s
    have hs := h (s.withGhost z)
    rw [← Config.withGhost_init, PostH_withGhost] at hs
    exact hs
  · intro h s
    obtain ⟨⟨σ, z⟩, ρ⟩ := s
    have hs := h z (⟨σ, ρ⟩ : CQState σT D)
    change expectE A.op ((⟨σ, ρ⟩ : CQState σT D).withGhost z) ≤
      PostH (Config.init (P.mapStore (StoreLens.fst (R := V)))
        ((⟨σ, ρ⟩ : CQState σT D).withGhost z)) B.op
    rw [← Config.withGhost_init, PostH_withGhost]
    exact hs

/-- Partial validity over a product store is equivalent to every fixed-ghost slice. -/
theorem validPar_mapStore_fst_iff (A B : Assn (σT × V) D) (P : Prog σT D) :
    validPar A (P.mapStore (StoreLens.fst (R := V))) B ↔
      ∀ z : V, validPar (A.ghostSlice z) P (B.ghostSlice z) := by
  constructor
  · intro h z s
    have hs := h (s.withGhost z)
    rw [← Config.withGhost_init, PostH_withGhost, NT_withGhost] at hs
    exact hs
  · intro h s
    obtain ⟨⟨σ, z⟩, ρ⟩ := s
    have hs := h z (⟨σ, ρ⟩ : CQState σT D)
    change expectE A.op ((⟨σ, ρ⟩ : CQState σT D).withGhost z) ≤
      PostH (Config.init (P.mapStore (StoreLens.fst (R := V)))
        ((⟨σ, ρ⟩ : CQState σT D).withGhost z)) B.op +
        NT (Config.init (P.mapStore (StoreLens.fst (R := V)))
          ((⟨σ, ρ⟩ : CQState σT D).withGhost z))
    rw [← Config.withGhost_init, PostH_withGhost, NT_withGhost]
    exact hs

end Qhl
