module

public import TemporalGraph.Defs

/-! ## Regular-graph-specific conductance theorems

Theorems for temporal graphs where all vertices have the same degree
at all times (using the `hregular` hypothesis).

## Main results

- `volume_eq_card_mul_deg_of_regular` — Vol(S) = |S| · deg for regular graphs.
- `relativeVolume_eq_card_ratio_of_regular` — π(S) = |S| / |V| for regular graphs.
- `mem_admissibleCuts_of_nonempty_of_two_mul_card_le_of_regular` — Nonempty sets of size ≤ |V|/2 are admissible cuts in regular graphs.
-/

@[expose] public section

open Finset
open scoped BigOperators

noncomputable section

namespace TemporalGraph

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]

theorem volume_eq_card_mul_deg_of_regular
    (G : TemporalGraph V)
    (hregular : ∀ u v : V, deg G u = deg G v)
    (S : Finset V) :
    volume G 0 S = S.card * deg G (Classical.choice ‹Nonempty V›) := by
  let v0 : V := Classical.choice ‹Nonempty V›
  simp only [TemporalGraph.volume, SimpleGraph.volume]
  calc ∑ v ∈ S, (G.snapshot 0).degree v
        = ∑ v ∈ S, deg G v0 :=
          Finset.sum_congr rfl (fun v _ => hregular v v0)
    _ = S.card * deg G v0 := by simp

end TemporalGraph
