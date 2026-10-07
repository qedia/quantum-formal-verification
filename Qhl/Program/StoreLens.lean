import Qhl.Program.For
import Qhl.Logic.CountedWhile

/-!
# Store lenses: running a program over an enlarged classical store

A `qWhile⁺` program is typed over its classical store `σT` (`Prog σT D`).  A
circuit fragment proved over a small store (e.g. the Hamiltonian coefficients
`(t, U)`) is often reused inside a larger program whose store carries more
classical data (loop counters, angle arrays).  A **store lens** is the pair of
maps that exhibits the small store inside the large one:

* `get : σT' → σT` reads the embedded small store;
* `put : σT' → σT → σT'` writes a small-store value back, keeping the rest.

`Prog.mapStore` transports a program along a lens, constructor by
constructor: guards and gate/measurement families precompose with `get`;
classical writes (`assign`, the measurement write-back) act through
`get`/`put`.  No new `Prog` constructor and no new semantics: the mapped
program is built from the same eight constructors.

`mapStore_forProg` records that the transport commutes with the `for`-fold
(`Qhl/Program/For.lean`), so a `for`-loop of gates maps to the `for`-loop of
the mapped gates.
-/

namespace Qhl

/-- A lens exhibiting the store `σT` inside the larger store `σT'`. -/
structure StoreLens (σT' σT : Type*) where
  /-- Read the embedded small store. -/
  get : σT' → σT
  /-- Write a small-store value back into the large store. -/
  put : σT' → σT → σT'

/-- The first-projection lens onto the left factor of a product store. -/
def StoreLens.fst {σT R : Type*} : StoreLens (σT × R) σT where
  get := Prod.fst
  put := fun σ' σ => (σ, σ'.2)

variable {σT σT' : Type*} {L : Type*} {D : L → Type*}
  [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]

/-- Transport a program along a store lens: reads precompose with `get`,
classical writes act through `get`/`put`.  Structural recursion over the
`Prog` constructors — the mapped program is a program of the same shape. -/
def Prog.mapStore (l : StoreLens σT' σT) : Prog σT D → Prog σT' D
  | .skip => .skip
  | .assign f => .assign fun σ' => l.put σ' (f (l.get σ'))
  | .init S => .init fun σ' => S (l.get σ')
  | .unitary k r U => .unitary k (fun σ' => r (l.get σ')) (fun σ' => U (l.get σ'))
  | .measure m k r M upd =>
      .measure m k (fun σ' => r (l.get σ')) (fun σ' => M (l.get σ'))
        (fun i σ' => l.put σ' (upd i (l.get σ')))
  | .seq P₁ P₂ => (P₁.mapStore l).seq (P₂.mapStore l)
  | .ite b P₁ P₀ => .ite (fun σ' => b (l.get σ')) (P₁.mapStore l) (P₀.mapStore l)
  | .while b P => .while (fun σ' => b (l.get σ')) (P.mapStore l)

/-- The transport commutes with the `for`-fold: a `for`-loop of fragments maps
to the `for`-loop of the mapped fragments. -/
theorem Prog.mapStore_forProg (l : StoreLens σT' σT) {ι : Type*} (li : List ι)
    (C : ι → Prog σT D) :
    (Qhl.forProg li C).mapStore l = Qhl.forProg li fun i => (C i).mapStore l := by
  induction li with
  | nil => rfl
  | cons i t ih =>
      show ((C i).seq (Qhl.forProg t C)).mapStore l = _
      rw [show ((C i).seq (Qhl.forProg t C)).mapStore l
          = ((C i).mapStore l).seq ((Qhl.forProg t C).mapStore l) from rfl, ih]
      rfl

/-! ## Pulling a counter lens back along a store lens

A counted loop (`Qhl/Logic/CountedWhile.lean`) proved over a small store
`σT` is reused inside a larger store `σT'` by transporting its program along
a store lens.  The loop counter of the transported program is read/written
through the lens; `CounterLens.pullback` packages this as a `CounterLens` on
the large store.

`StoreLens` carries no lens law, and the counter law `get_set` of the
pullback needs read-after-write, `l.get (l.put σ' σ) = σ`.  Rather than
adding a law field to `StoreLens` (which would touch every existing
instance), the law is taken as an explicit hypothesis `hgp` — it holds by
`rfl` for the projection lenses actually in use (`StoreLens.fst`, and the
`fst`-style projections of `Qhl/Examples/HubbardQSPTriple.lean`). -/

/-- Read-after-write holds definitionally for the first-projection lens. -/
theorem StoreLens.fst_get_put {σT R : Type*} (σ' : σT × R) (σ : σT) :
    (StoreLens.fst (R := R)).get ((StoreLens.fst (R := R)).put σ' σ) = σ := rfl

/-- Pull a counter lens on the small store back along a store lens: the
counter of the large store is the embedded small store's counter.  The
read-after-write law of the lens is an explicit hypothesis (see the section
comment); for `StoreLens.fst` it is `rfl` (`StoreLens.fst_get_put`). -/
def CounterLens.pullback (l : StoreLens σT' σT) (c : CounterLens σT)
    (hgp : ∀ σ' σ, l.get (l.put σ' σ) = σ) : CounterLens σT' where
  get := c.get ∘ l.get
  set σ' v := l.put σ' (c.set (l.get σ') v)
  get_set σ' v := by
    simp only [Function.comp_apply, hgp, c.get_set]

@[simp] theorem CounterLens.pullback_get (l : StoreLens σT' σT) (c : CounterLens σT)
    (hgp : ∀ σ' σ, l.get (l.put σ' σ) = σ) (σ' : σT') :
    (c.pullback l hgp).get σ' = c.get (l.get σ') := rfl

@[simp] theorem CounterLens.pullback_set (l : StoreLens σT' σT) (c : CounterLens σT)
    (hgp : ∀ σ' σ, l.get (l.put σ' σ) = σ) (σ' : σT') (v : ℕ) :
    (c.pullback l hgp).set σ' v = l.put σ' (c.set (l.get σ') v) := rfl

/-- The pullback along the first-projection lens, concretely (the shape the
QSP-style product stores use). -/
def CounterLens.pullbackFst {R : Type*} (c : CounterLens σT) : CounterLens (σT × R) :=
  c.pullback StoreLens.fst fun _ _ => rfl

/-- **The transport commutes with the counted loop**: mapping
`cnt := 0 ; while cnt < N do BODY ; cnt := cnt + 1 od` along a store lens
gives the counted loop of the mapped body, over the pulled-back counter and
the bound read through the lens.  Every piece of `countedProg` maps
structurally through `Prog.mapStore`, so this is definitional. -/
theorem Prog.mapStore_countedProg (l : StoreLens σT' σT) (c : CounterLens σT)
    (hgp : ∀ σ' σ, l.get (l.put σ' σ) = σ) (N : σT → ℕ) (B : Prog σT D) :
    (countedProg c N B).mapStore l
      = countedProg (c.pullback l hgp) (N ∘ l.get) (B.mapStore l) := rfl

end Qhl
