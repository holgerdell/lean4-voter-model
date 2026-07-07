module

public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import TemporalGraph.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! ## Voter model kernel on a temporal graph

Provides the one-step voter transition as a Mathlib `Kernel` (`voterKernel₂`),
the discrete σ-algebra instances on `Finset V`, and the edge-cut symmetry helper
`edgesBetween_comm'`. The voter model bundle itself is the κ-opinion
`TemporalGraph.VoterModelAbstract` (in `Spec/VoterModelGeneral.lean`). -/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators

noncomputable section

namespace TemporalGraph

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]

variable {Ω : Type*} [MeasurableSpace Ω] {G : TemporalGraph V}

/-- `edgesBetween G t S N = edgesBetween G t N S`: the temporal-graph edge cut
is symmetric, by `SimpleGraph.edgesBetween_comm`. -/
theorem edgesBetween_comm' (G : TemporalGraph V)
    (t : ℕ) (S N : Finset V) :
    edgesBetween G t S N =
      edgesBetween G t N S :=
  SimpleGraph.edgesBetween_comm _ S N

instance instMeasurableSpaceFinsetV :
    MeasurableSpace (Finset V) := ⊤

instance instTopologicalSpaceFinsetV : TopologicalSpace (Finset V) :=
  ⊥

instance instDiscreteTopologyFinsetV : DiscreteTopology (Finset V) :=
  ⟨rfl⟩

end TemporalGraph
