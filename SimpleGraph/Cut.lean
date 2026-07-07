module

public import Mathlib.Combinatorics.SimpleGraph.Basic

/-! ## Basic combinatorial definitions for simple graphs

Edge cuts and restricted degrees for a simple graph `G`.

## Main results

- `edgesBetween G S N` — number of edges between vertex sets `S` and `N`.
- `degreeIn G v N` — number of neighbours of `v` inside `N`.
-/

@[expose] public section

open Finset

namespace SimpleGraph

/-- The number e(S,N) of edges between `S` and `N` (edges within `S ∩ N` are counted twice). -/
def edgesBetween {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (S N : Finset V) : ℕ :=
  #{e ∈ S ×ˢ N | G.Adj e.1 e.2}

/-- Number of neighbours of `v` inside `N`: `degreeIn G v N = |N(v) ∩ N|`. -/
def degreeIn {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (N : Finset V) : ℕ :=
  #{w ∈ N | G.Adj v w}

/-- `edgesBetween G S N = edgesBetween G N S` by the bijection `(u,w) ↦ (w,u)`
and `SimpleGraph.adj_comm`. -/
theorem edgesBetween_comm {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (S N : Finset V) : G.edgesBetween S N = G.edgesBetween N S := by
  unfold edgesBetween
  exact Finset.card_bijective (fun x : V × V => (x.2, x.1))
    ⟨fun ⟨_, _⟩ ⟨_, _⟩ h => by
      simp [Prod.ext_iff] at h ⊢; exact ⟨h.2, h.1⟩,
     fun ⟨a, b⟩ => ⟨⟨b, a⟩, by simp⟩⟩
    (fun ⟨a, b⟩ => by
      simp only [Finset.mem_filter, Finset.mem_product,
        and_comm (a := a ∈ S), adj_comm])

end SimpleGraph
