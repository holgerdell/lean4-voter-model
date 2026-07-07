module

public import TemporalGraph.Defs

/-! ## Min/Max degree for temporal graphs

Defines `minDegreeAt` and `maxDegree` for `TemporalGraph` directly in terms of
`TemporalGraph.degree`. The global `minDegree` is the unconditional least
degree over all times and vertices (an infimum over the infinite time index,
attained since `ℕ` is well-ordered). Time-independent versions are provided
under `FixedDegrees`. -/

@[expose] public section

open Finset
open scoped BigOperators

noncomputable section

namespace TemporalGraph

/-! ### Time-indexed min/max degree -/

/-- Minimum degree over all vertices in the snapshot at time `t`. -/
def minDegreeAt {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraph V) (t : ℕ) : ℕ :=
  Finset.univ.inf' univ_nonempty (fun v => G.degree t v)

/-- Maximum vertex-degree in `G` at time `t`. -/
def maxDegree {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraph V) (t : ℕ) : ℕ :=
  Finset.univ.sup' univ_nonempty (fun v => G.degree t v)

theorem minDegreeAt_le_degree {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraph V) (t : ℕ) (v : V) :
    G.minDegreeAt t ≤ G.degree t v :=
  Finset.inf'_le _ (mem_univ v)

theorem degree_le_maxDegree {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraph V) (t : ℕ) (v : V) :
    G.degree t v ≤ G.maxDegree t :=
  Finset.le_sup' _ (mem_univ v)

theorem minDegreeAt_le_maxDegree {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraph V) (t : ℕ) :
    G.minDegreeAt t ≤ G.maxDegree t := by
  obtain ⟨v⟩ : Nonempty V := inferInstance
  exact le_trans (minDegreeAt_le_degree G t v) (degree_le_maxDegree G t v)

theorem exists_minDegreeAt_vertex {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraph V) (t : ℕ) :
    ∃ v : V, G.minDegreeAt t = G.degree t v := by
  exact Finset.exists_mem_eq_inf' univ_nonempty (fun v => G.degree t v)
    |>.imp fun v ⟨_, hv⟩ => hv


/-! ### Time-independent min/max degree under `FixedDegrees` -/

theorem minDegreeAt_eq_of_fixedDegrees {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraph V) (hfix : FixedDegrees G)
    (t₁ t₂ : ℕ) : G.minDegreeAt t₁ = G.minDegreeAt t₂ := by
  simp only [minDegreeAt]
  congr 1; ext v; exact hfix.1 v t₁ t₂

theorem maxDegree_eq_of_fixedDegrees {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraph V) (hfix : FixedDegrees G)
    (t₁ t₂ : ℕ) : G.maxDegree t₁ = G.maxDegree t₂ := by
  simp only [maxDegree]
  congr 1; ext v; exact hfix.1 v t₁ t₂

/-- The time-independent maximum degree of a fixed-degree temporal graph. -/
def maxDeg {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V] (G : TemporalGraph V) : ℕ :=
  G.maxDegree 0

theorem maxDeg_eq_maxDegree {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraph V) (hfix : FixedDegrees G) (t : ℕ) :
    G.maxDeg = G.maxDegree t := by
  simp [maxDeg, maxDegree_eq_of_fixedDegrees G hfix 0 t]

theorem minDegree_le_deg {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraph V) (v : V) :
    G.minDegreeAt 0 ≤ G.deg v :=
  minDegreeAt_le_degree G 0 v



/-! ### Global minimum degree -/

/-- The global minimum degree of a temporal graph. -/
def minDegree {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V] (G : TemporalGraph V) : ℕ :=
  ⨅ t : ℕ, ⨅ v : V, (G.snapshot t).degree v

theorem minDegree_eq_iInf_minDegreeAt {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraph V) :
    G.minDegree = ⨅ t : ℕ, G.minDegreeAt t := by
  simp only [minDegree, minDegreeAt, Finset.inf'_eq_csInf_image, Finset.coe_univ, Set.image_univ,
    iInf]

theorem minDegree_le_minDegreeAt {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraph V) (t : ℕ) :
    G.minDegree ≤ G.minDegreeAt t := by
  rw [minDegree_eq_iInf_minDegreeAt]
  exact ciInf_le (OrderBot.bddBelow _) t

theorem minDegree_le_degree {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraph V) (t : ℕ) (v : V) :
    G.minDegree ≤ G.degree t v :=
  le_trans (minDegree_le_minDegreeAt G t) (minDegreeAt_le_degree G t v)


/-- Under `FixedDegrees` the global minimum degree equals `minDegreeAt` at any
time (all `minDegreeAt t` coincide, so the infimum is that common value). -/
theorem minDegree_eq_minDegreeAt {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraph V) (hfix : FixedDegrees G)
    (t : ℕ) : G.minDegree = G.minDegreeAt t := by
  rw [minDegree_eq_iInf_minDegreeAt, iInf_congr (g := fun _ => G.minDegreeAt t)
    fun s => minDegreeAt_eq_of_fixedDegrees G hfix s t]
  exact ciInf_const

end TemporalGraph

namespace TemporalGraphFixedDegree

/-! ### Time-independent min/max degree on the bundled type -/

/-- The global minimum degree of a temporal graph. -/
def minDegree {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraphFixedDegree V) : ℕ :=
  ⨅ t, ⨅ v, (G.snapshot t).degree v

/-- The minimum degree over all vertices in the snapshot at time `t`. -/
abbrev minDegreeAt {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraphFixedDegree V) (t : ℕ) : ℕ :=
  G.toTemporalGraph.minDegreeAt t

/-- The maximum degree over all vertices in the snapshot at time `t`. -/
abbrev maxDegree {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraphFixedDegree V) (t : ℕ) : ℕ :=
  G.toTemporalGraph.maxDegree t

/-- The time-independent maximum degree of a fixed-degree temporal graph. -/
abbrev maxDeg {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraphFixedDegree V) : ℕ :=
  G.toTemporalGraph.maxDeg


/-- The global `minDegree` equals `minDegreeAt` at any time for a fixed-degree
graph, since all snapshots share the same degree sequence. -/
theorem minDegree_eq_minDegreeAt {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraphFixedDegree V) (t : ℕ) :
    G.minDegree = G.minDegreeAt t :=
  G.toTemporalGraph.minDegree_eq_minDegreeAt G.fixed t

/-- `minDegreeAt` is time-independent for a fixed-degree graph. -/
theorem minDegreeAt_eq {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraphFixedDegree V) (t₁ t₂ : ℕ) :
    G.minDegreeAt t₁ = G.minDegreeAt t₂ :=
  G.toTemporalGraph.minDegreeAt_eq_of_fixedDegrees G.fixed t₁ t₂


/-- The time-independent maximum degree equals the maximum degree at any time. -/
theorem maxDeg_eq_maxDegree {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraphFixedDegree V) (t : ℕ) :
    G.maxDeg = G.maxDegree t :=
  G.toTemporalGraph.maxDeg_eq_maxDegree G.fixed t

theorem minDegreeAt_le_degree {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraphFixedDegree V) (t : ℕ) (v : V) :
    G.minDegreeAt t ≤ G.degree t v :=
  G.toTemporalGraph.minDegreeAt_le_degree t v

theorem degree_le_maxDegree {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraphFixedDegree V) (t : ℕ) (v : V) :
    G.degree t v ≤ G.maxDegree t :=
  G.toTemporalGraph.degree_le_maxDegree t v

theorem minDegree_le_degree {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraphFixedDegree V) (t : ℕ) (v : V) :
    G.minDegree ≤ G.degree t v :=
  G.toTemporalGraph.minDegree_le_degree t v

theorem minDegreeAt_le_maxDegree {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraphFixedDegree V) (t : ℕ) :
    G.minDegreeAt t ≤ G.maxDegree t :=
  G.toTemporalGraph.minDegreeAt_le_maxDegree t

theorem minDegree_le_deg {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraphFixedDegree V) (v : V) :
    G.minDegreeAt 0 ≤ G.deg v :=
  G.toTemporalGraph.minDegree_le_deg v

end TemporalGraphFixedDegree
