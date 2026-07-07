module

public import SimpleGraph.Cut
public import SimpleGraph.Volume
public import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Positivity.Finset


/-! ## Conductance of a vertex set in a simple graph

Defines `SimpleGraph.setConductance`, the conductance `φ(S) = e(S, S̄)/Vol(S)`
of a vertex subset `S` of a finite simple graph `G`.

## Main results

- `setConductance G S` — `φ(S) = e(S, S̄)/Vol(S)`.
- `admissibleCuts G` — sets `S` with `0 < Vol(S) ≤ Vol(V)/2`.
- `edgesBetween_univ_eq_volume` — `e(S, V) = Vol(S)`.
- `setConductance_nonneg`, `setConductance_le_one` — `0 ≤ φ(S) ≤ 1`.
-/

@[expose] public section

open Finset

noncomputable section

namespace SimpleGraph

/-- \label{eq:set-conductance-at-time}

Conductance of `S` in `G`: `φ(S) = e(S, S̄)/Vol(S)`. And `φ(S) = 0` if `Vol(S) = 0`. -/
def setConductance {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : ℝ :=
  (G.edgesBetween S (Finset.univ \ S) : ℝ) / (G.volume S : ℝ)

/-- Sets `S` that satisfy `0 < Vol(S) ≤ Vol(V)/2`. -/
def admissibleCuts {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Set (Finset V) :=
  {S : Finset V | 0 < G.volume S ∧ 2 * G.volume S ≤ G.volume Finset.univ}

/-- Admissible cuts are nonempty: `Vol(S) > 0` forces `S ≠ ∅`. -/
theorem nonempty_of_mem_admissibleCuts {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {S : Finset V} (hS : S ∈ G.admissibleCuts) : S.Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  subst h
  simp [admissibleCuts, volume] at hS


theorem setConductance_nonneg {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) : 0 ≤ G.setConductance S := by
  unfold setConductance
  positivity

/-- Counting all edges leaving `S` without restriction gives the volume: `e(S, V) = Vol(S)`. -/
theorem edgesBetween_univ_eq_volume {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) :
    G.edgesBetween S Finset.univ = G.volume S := by
  have hlhs : G.edgesBetween S Finset.univ =
      ∑ x ∈ S ×ˢ Finset.univ, (if G.Adj x.1 x.2 then (1 : ℕ) else 0) := by
    simp only [edgesBetween, Finset.card_filter]
  have hrhs : G.volume S =
      ∑ x ∈ S ×ˢ Finset.univ, (if G.Adj x.1 x.2 then (1 : ℕ) else 0) := by
    simp only [volume, degree, neighborFinset, neighborSet, Set.toFinset_setOf,
               Finset.card_filter]
    symm
    exact Finset.sum_product' S Finset.univ (fun u v => if G.Adj u v then (1 : ℕ) else 0)
  rw [hlhs, hrhs]

theorem edgesBetween_sdiff_le_volume {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) :
    G.edgesBetween S (Finset.univ \ S) ≤ G.volume S := by
  calc
    G.edgesBetween S (Finset.univ \ S) ≤ G.edgesBetween S Finset.univ := by
      unfold edgesBetween
      exact Finset.card_le_card <| by
        intro x hx
        rcases Finset.mem_filter.mp hx with ⟨hxmem, hAdj⟩
        rcases Finset.mem_product.mp hxmem with ⟨hxS, hxCompl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hxS, by simp⟩, hAdj⟩
    _ = G.volume S := G.edgesBetween_univ_eq_volume S

theorem setConductance_le_one {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) : G.setConductance S ≤ 1 := by
  by_cases hvol0 : G.volume S = 0
  · have hcut0 : G.edgesBetween S (Finset.univ \ S) = 0 := by
      apply Nat.eq_zero_of_le_zero
      simpa [hvol0] using G.edgesBetween_sdiff_le_volume S
    simp [setConductance, hvol0, hcut0]
  · have hvol_pos : 0 < (G.volume S : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hvol0
    have hcut_le : (G.edgesBetween S (Finset.univ \ S) : ℝ) ≤ (G.volume S : ℝ) := by
      exact_mod_cast G.edgesBetween_sdiff_le_volume S
    exact (div_le_iff₀ hvol_pos).2 (by simpa using hcut_le)

end SimpleGraph
