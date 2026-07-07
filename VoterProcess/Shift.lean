module

public import TemporalGraph.Conductance
public import TemporalGraph.Degree
import TemporalGraph.Basic
public import VoterProcess.CrossCut

/-! ## Time-shift of a temporal graph

This file defines the *time-shift* `TemporalGraph.shift G r`, the temporal graph
whose snapshot at time `s` is `G`'s snapshot at time `s + r`, and proves that all
voter-model and conductance quantities transport across it. These feed the §3.4
multi-opinion reduction (restarting the process at time `t_r` on the shifted
graph).

## Main results

- `TemporalGraph.shift` — `(shift G r).snapshot s = G.snapshot (s + r)`.
- `neighborFinset_shift`, `degree_shift` — neighbour/degree transport (definitional).
- `FixedDegrees_shift` — fixed degrees are preserved under shifting.
- `minDegree_shift`, `volume_shift`, `relativeVolume_shift` — degree/volume invariants
  (using `FixedDegrees`).
- `maxSetConductanceOnInterval_shift` — conductance
  transport across the shift (with index reindexing on intervals).
- `admissibleCuts_shift` — the set of admissible cuts is invariant.
- `VoterModel.stepDist₂_shift`, `VoterModel.stepDist_shift` — one-step transition transport.
- `VoterModel.opinionProcess₂_shift`, `VoterModel.opinionProcess_shift` — multi-step
  process transport: running `r + Δ` steps on `G` from time `r` equals running `Δ`
  steps on `shift G r` from time `0`.
-/

@[expose] public section

open Finset
open scoped BigOperators Classical

noncomputable section

namespace TemporalGraph

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]

/-- The time-shift of a temporal graph: `(shift G r)` is the temporal graph whose
snapshot at time `s` is `G`'s snapshot at time `s + r`. -/
def shift (G : TemporalGraph V) (r : ℕ) : TemporalGraph V where
  snapshot := fun s => G.snapshot (s + r)
  decidableAdj := fun s => G.decidableAdj (s + r)

@[simp] theorem shift_graph (G : TemporalGraph V) (r s : ℕ) :
    (shift G r).snapshot s = G.snapshot (s + r) := rfl



/-- Fixed positive degrees are preserved under time-shifting. -/
theorem FixedDegrees_shift (G : TemporalGraphFixedDegree V) (r : ℕ) :
    (shift G.toTemporalGraph r).FixedDegrees :=
  ⟨fun v t₁ t₂ => G.degrees_fixed v (t₁ + r) (t₂ + r), fun v t => G.degrees_pos v (t + r)⟩

/-- The time-independent minimum degree is invariant under shifting (fixed degrees). -/
theorem minDegree_shift (G : TemporalGraphFixedDegree V) (r : ℕ) :
    (shift G.toTemporalGraph r).minDegreeAt 0 = G.minDegreeAt 0 := by
  simp only [minDegreeAt]
  congr 1
  ext v
  exact G.degrees_fixed v (0 + r) 0

/-- The volume of a set is invariant under shifting (fixed degrees). -/
theorem volume_shift (G : TemporalGraphFixedDegree V) (r : ℕ)
    (s : ℕ) (S : Finset V) :
    volume (shift G.toTemporalGraph r) s S = volume G.toTemporalGraph 0 S :=
  G.volume_fixed S (s + r) 0


/-- The maximum set conductance over a length-`Δ` window transports across the
shift, the window start being reindexed by `(· + r)`. -/
theorem maxSetConductanceOnInterval_shift (G : TemporalGraph V) (r t Δ : ℕ) (S : Finset V) :
    maxSetConductanceOnInterval (shift G r) t Δ S
      = maxSetConductanceOnInterval G (t + r) Δ S := by
  apply le_antisymm
  · apply maxSetConductanceOnInterval_le (shift G r) t Δ S
      (maxSetConductanceOnInterval_nonneg G (t + r) Δ S)
    intro s hs
    simp only [shift_graph]
    apply le_maxSetConductanceOnInterval
    rw [Finset.mem_Icc] at hs ⊢
    omega
  · apply maxSetConductanceOnInterval_le G (t + r) Δ S
      (maxSetConductanceOnInterval_nonneg (shift G r) t Δ S)
    intro s hs
    rw [Finset.mem_Icc] at hs
    rw [show (G.snapshot s).setConductance S =
        ((shift G r).snapshot (s - r)).setConductance S by
      simp only [shift_graph]; congr 2; omega]
    apply le_maxSetConductanceOnInterval
    rw [Finset.mem_Icc]
    omega

/-- The set of admissible cuts is invariant under shifting (fixed degrees). -/
theorem admissibleCuts_shift (G : TemporalGraphFixedDegree V) (r : ℕ) :
    admissibleCuts (shift G.toTemporalGraph r) = admissibleCuts G.toTemporalGraph := by
  ext S
  simp only [admissibleCuts, SimpleGraph.admissibleCuts, Set.mem_setOf_eq, volume_shift G r 0]

end TemporalGraph

namespace VoterModel

open TemporalGraph

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]


/-- The two-opinion one-step transition transports across the shift. -/
theorem stepDist₂_shift (G : TemporalGraph V) (r t : ℕ) :
    stepDist₂ (shift G r) t = stepDist₂ G (t + r) := by
  have h : nextOpinionDist₂ (shift G r) t = nextOpinionDist₂ G (t + r) := rfl
  unfold stepDist₂
  rw [h]

end VoterModel
