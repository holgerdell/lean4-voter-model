module

public import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Init
import Mathlib.Data.Rat.Cast.Order


/-! ## Volume and relative volume for simple graphs

Defines `SimpleGraph.volume` and `SimpleGraph.relativeVolume` for a vertex
subset `S` of a finite simple graph `G`.

## Main results

- `volume G S` — `Vol(S) = ∑_{v ∈ S} deg(v)`.
- `relativeVolume G S` — `π(S) = Vol(S) / Vol(V)` as a rational number.
- `volume_pos_of_nonempty` — `S` nonempty and every vertex has positive degree implies
  `Vol(S) > 0`.
- `relativeVolume_le_one` — `π(S) ≤ 1`.
- `relativeVolume_univ` — `π(V) = 1` when every vertex has positive degree.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace SimpleGraph

/-- \label{eq:volume}

Volume of a vertex set: `Vol(S) = ∑_{v ∈ S} deg(v)`. -/
def volume {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  ∑ v ∈ S, G.degree v

/-- \label{eq:relative-volume-definition}

Relative volume `π(S) = Vol(S)/Vol(V)`, the random-walk stationary mass of `S` (as a rational). -/
def relativeVolume {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) : ℚ :=
  (G.volume S : ℚ) / (G.volume Finset.univ : ℚ)

theorem volume_mono {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {S T : Finset V} (h : S ⊆ T) : G.volume S ≤ G.volume T :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun _ _ _ => Nat.zero_le _)

theorem volume_pos_of_nonempty {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {S : Finset V}
    (hS : S.Nonempty) (hdeg : ∀ v : V, 0 < G.degree v) :
    0 < G.volume S := by
  obtain ⟨v, hv⟩ := hS
  unfold volume
  exact Nat.lt_of_lt_of_le (hdeg v)
    (Finset.single_le_sum (f := fun u => G.degree u) (fun u _ => Nat.zero_le _) hv)

theorem volume_univ_pos {V : Type*} [Fintype V] [Nonempty V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (hdeg : ∀ v : V, 0 < G.degree v) :
    0 < G.volume Finset.univ :=
  G.volume_pos_of_nonempty Finset.univ_nonempty hdeg


end SimpleGraph
