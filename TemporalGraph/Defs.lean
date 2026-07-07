module

public import SimpleGraph.Cut
public import SimpleGraph.Volume
public import Mathlib.Analysis.Real.Sqrt

/-! ## Temporal graph: core definitions

A temporal graph on a fixed vertex set `V` is a sequence of simple graphs
indexed by `ℕ`. This file collects the structure and all basic definitions
(degree, edges, volume, potential, fixed-degrees). -/

@[expose] public section

open Finset
open scoped BigOperators

/-- \label{def:temporal-graph} -/
structure TemporalGraph (V : Type*) [Fintype V] [Nonempty V] [DecidableEq V] where
  /-- The graph snapshot at each time step; `G.snapshot t = G_t`. -/
  snapshot : ℕ → SimpleGraph V
  /-- Each snapshot has a decidable adjacency relation. -/
  decidableAdj : ∀ t, DecidableRel (snapshot t).Adj

attribute [instance] TemporalGraph.decidableAdj

namespace TemporalGraph

/-- Neighbours of `v` at time `t`. -/
abbrev neighborFinset {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraph V) (t : ℕ) (v : V) : Finset V :=
  (G.snapshot t).neighborFinset v

/-- Degree of `v` at time `t`. -/
abbrev degree {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraph V) (t : ℕ) (v : V) : ℕ :=
  (G.snapshot t).degree v

/-- \label{def:temporal-graph}

`G` has fixed positive degrees: every vertex has the same degree at all times, and that degree is
strictly positive (no isolated vertices). With `TemporalGraph`, this is the paper's *temporal graph
with fixed degrees*. -/
def FixedDegrees {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraph V) : Prop :=
  (∀ v : V, ∀ t₁ t₂ : ℕ, degree G t₁ v = degree G t₂ v) ∧
  (∀ v : V, ∀ t : ℕ, 0 < degree G t v)

/-- For a fixed-degree temporal graph, the time-independent degree of a vertex. -/
def deg {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V] (G : TemporalGraph V) (v : V) : ℕ :=
  degree G 0 v

/-- Edge count between `S` and `N` in the snapshot `G_t`. -/
abbrev edgesBetween {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraph V) (t : ℕ) (S N : Finset V) : ℕ :=
  (G.snapshot t).edgesBetween S N

/-- Number of neighbours of `v` inside `N` at time `t`. -/
abbrev degreeIn {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraph V) (t : ℕ) (v : V) (N : Finset V) : ℕ :=
  (G.snapshot t).degreeIn v N

/-- Volume `Vol(S) = ∑_{v ∈ S} deg(v)` in the snapshot at time `t`. -/
abbrev volume {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraph V) (t : ℕ) (S : Finset V) : ℕ :=
  (G.snapshot t).volume S

/-- \label{eq:relative-volume-definition}

Relative volume `π(S) = Vol(S)/Vol(V)`; time-invariant under fixed degrees, so evaluated at the
first snapshot. -/
abbrev relativeVolume {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraph V) (S : Finset V) : ℚ :=
  (G.snapshot 0).relativeVolume S

/-- Potential of a set `S` at time `t`: `ψ(S) = √Vol(S)`. Lean-internal helper;
not a labeled paper definition (paper uses `ψ(S)` inline without a numbered
definition). -/
noncomputable def potential {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraph V) (t : ℕ) (S : Finset V) : ℝ :=
  Real.sqrt (volume G t S : ℝ)

end TemporalGraph

/-- A temporal graph (a sequence of snapshots) in which every vertex keeps the same, strictly
positive degree at all times: the paper's *temporal graph with fixed degrees*. -/
structure TemporalGraphFixedDegree (V : Type*) [Fintype V] [Nonempty V] [DecidableEq V] where
  /-- The graph snapshot at each time step; `G.snapshot t = G_t`. -/
  snapshot : ℕ → SimpleGraph V
  /-- Each snapshot has a decidable adjacency relation. -/
  decidableAdj : ∀ t, DecidableRel (snapshot t).Adj
  /-- Every vertex has the same degree at all times. -/
  degrees_fixed : ∀ v t₁ t₂, (snapshot t₁).degree v = (snapshot t₂).degree v
  /-- Every vertex has strictly positive degree (no isolated vertices). -/
  degrees_pos : ∀ v t, 0 < (snapshot t).degree v

attribute [instance] TemporalGraphFixedDegree.decidableAdj

namespace TemporalGraphFixedDegree

/-- The underlying `TemporalGraph` of a fixed-degree temporal graph.
Reducible so that `G.toTemporalGraph.snapshot` and `G.snapshot` unify definitionally, keeping
`TemporalGraph`-level lemmas usable on fixed-degree graphs via dot notation. -/
@[reducible] def toTemporalGraph {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraphFixedDegree V) : TemporalGraph V where
  snapshot := G.snapshot
  decidableAdj := G.decidableAdj

/-- A fixed-degree temporal graph coerces to its underlying `TemporalGraph`. -/
instance {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V] :
    Coe (TemporalGraphFixedDegree V) (TemporalGraph V) :=
  ⟨TemporalGraphFixedDegree.toTemporalGraph⟩


/-- The bundled fixed-degrees proof, recovering the `FixedDegrees` predicate. -/
theorem fixed {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraphFixedDegree V) : TemporalGraph.FixedDegrees G.toTemporalGraph :=
  ⟨G.degrees_fixed, G.degrees_pos⟩

/-- Neighbours of `v` at time `t`. -/
abbrev neighborFinset {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraphFixedDegree V) (t : ℕ) (v : V) : Finset V :=
  G.toTemporalGraph.neighborFinset t v

/-- Degree of `v` at time `t`. -/
abbrev degree {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraphFixedDegree V) (t : ℕ) (v : V) : ℕ :=
  G.toTemporalGraph.degree t v

/-- Edge count between `S` and `N` in the snapshot `G_t`. -/
abbrev edgesBetween {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraphFixedDegree V) (t : ℕ) (S N : Finset V) : ℕ :=
  G.toTemporalGraph.edgesBetween t S N

/-- Number of neighbours of `v` inside `N` at time `t`. -/
abbrev degreeIn {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraphFixedDegree V) (t : ℕ) (v : V) (N : Finset V) : ℕ :=
  G.toTemporalGraph.degreeIn t v N

/-- Relative volume `π(S) = Vol(S)/Vol(V)`. -/
abbrev relativeVolume {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraphFixedDegree V) (S : Finset V) : ℚ :=
  G.toTemporalGraph.relativeVolume S

/-- For a fixed-degree temporal graph, the time-independent degree of a vertex. -/
abbrev deg {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraphFixedDegree V) (v : V) : ℕ :=
  G.toTemporalGraph.deg v

/-- Potential of a set `S` at time `t`: `ψ(S) = √Vol(S)`. -/
@[reducible] noncomputable def potential {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraphFixedDegree V) (t : ℕ) (S : Finset V) : ℝ :=
  G.toTemporalGraph.potential t S

end TemporalGraphFixedDegree

/-- Bundle a temporal graph with a fixed-degrees proof into a `TemporalGraphFixedDegree`.
Reducible so that `(G.withFixed h).toTemporalGraph` unfolds to `G` for `rw`/defeq matching. -/
@[reducible] def TemporalGraph.withFixed {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraph V) (h : TemporalGraph.FixedDegrees G) : TemporalGraphFixedDegree V where
  snapshot := G.snapshot
  decidableAdj := G.decidableAdj
  degrees_fixed := h.1
  degrees_pos := h.2
