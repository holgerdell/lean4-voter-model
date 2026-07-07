module

public import TemporalGraph.Defs
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic.ContinuousFunctionalCalculus

/-! ## Temporal graph: basic theorems

Lemmas about edges, volume, and the `FixedDegrees` property. -/

@[expose] public section

open Finset
open scoped BigOperators

noncomputable section

namespace TemporalGraph

/-- Summing `degreeIn` over all vertices counts exactly the volume of `S`. -/
theorem sum_edgesVertex_eq_volume {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraph V) (t : ℕ) (S : Finset V) :
    ∑ v, degreeIn G t v S = volume G t S := by
  have hlhs :
      ∑ v, degreeIn G t v S =
        ∑ x ∈ Finset.univ ×ˢ S, (if (G.snapshot t).Adj x.1 x.2 then (1 : ℕ) else 0) := by
    simp only [TemporalGraph.degreeIn, SimpleGraph.degreeIn, Finset.card_filter]
    symm
    exact Finset.sum_product' Finset.univ S
      (fun v u => if (G.snapshot t).Adj v u then (1 : ℕ) else 0)
  have hswap :
      ∑ x ∈ Finset.univ ×ˢ S, (if (G.snapshot t).Adj x.1 x.2 then (1 : ℕ) else 0) =
        ∑ x ∈ S ×ˢ Finset.univ, (if (G.snapshot t).Adj x.1 x.2 then (1 : ℕ) else 0) := by
    refine Finset.sum_nbij' (fun x => (x.2, x.1)) (fun x => (x.2, x.1)) ?_ ?_ ?_ ?_ ?_ <;>
      simp [and_comm, SimpleGraph.adj_comm]
  have hrhs :
      volume G t S =
        ∑ x ∈ S ×ˢ Finset.univ, (if (G.snapshot t).Adj x.1 x.2 then (1 : ℕ) else 0) := by
    simp only [TemporalGraph.volume, SimpleGraph.volume, SimpleGraph.degree,
               SimpleGraph.neighborFinset, SimpleGraph.neighborSet, Set.toFinset_setOf,
               Finset.card_filter]
    symm
    exact Finset.sum_product' S Finset.univ
      (fun u v => if (G.snapshot t).Adj u v then (1 : ℕ) else 0)
  rw [hlhs, hswap, hrhs]

/-- For a fixed-degree temporal graph the volume is time-independent. -/
theorem volume_fixed {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraph V) (hfix : FixedDegrees G) (S : Finset V)
    (t₁ t₂ : ℕ) :
    volume G t₁ S = volume G t₂ S := by
  simp only [TemporalGraph.volume, SimpleGraph.volume]
  exact Finset.sum_congr rfl (fun v _ => hfix.1 v t₁ t₂)

end TemporalGraph

namespace TemporalGraphFixedDegree

/-- The number `m` of edges of the graph; for fixed-degree temporal graphs, this number does not
depend on the time `t`, so we use `t=0`. -/
def numEdges {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraphFixedDegree V) : ℕ :=
  (G.snapshot 0).edgeFinset.card

/-- For a fixed-degree graph the volume is time-independent. -/
theorem volume_fixed {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraphFixedDegree V) (S : Finset V) (t₁ t₂ : ℕ) :
    (G.snapshot t₁).volume S = (G.snapshot t₂).volume S :=
  G.toTemporalGraph.volume_fixed G.fixed S t₁ t₂


/-- A fixed-degree graph has at least one edge: every vertex has positive degree, so the degree
sum is positive, and the handshake identity forces `numEdges > 0` (the paper's `m ≥ 1`). -/
theorem numEdges_pos {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraphFixedDegree V) : 0 < G.numEdges := by
  have hsum : ∑ v : V, (G.snapshot 0).degree v = 2 * (G.snapshot 0).edgeFinset.card :=
    (G.snapshot 0).sum_degrees_eq_twice_card_edges
  have hpos : 0 < ∑ v : V, (G.snapshot 0).degree v :=
    Finset.sum_pos (fun v _ => G.degrees_pos v 0) Finset.univ_nonempty
  rw [hsum] at hpos
  have hcard : 0 < (G.snapshot 0).edgeFinset.card := by omega
  simpa [numEdges] using hcard

end TemporalGraphFixedDegree
