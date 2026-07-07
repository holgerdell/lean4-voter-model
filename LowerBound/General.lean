module

import VoterProcess.TwoOpinion
public import VoterProcess.Absorption.Consensus
public import VoterProcess.Absorption.Time
import Mathlib.Data.ENat.Lattice

/-! ## General-model lower bounds

This file lifts the §4 lower-bound theorems — proved for the κ=2 voter model
`TemporalGraph.VoterModelAbstract G 2 Ω` via its opinion-0 set `absorptionTime` — to the
`consensusTime`-phrased statements the paper attaches to *the standard voter
model* (`def:voter-model`). For `κ = 2`, `absorptionTime` (first empty minority
set) and `consensusTime` (first all-equal configuration) coincide whenever every
vertex always has a neighbour (`absorptionTime_eq_consensusTime`).

## Main results

- `lower_bound_odd_regular_averaged_abstract` — general-model version of the interval
  lower-bound theorem (`thm:lower-bound-intervals`).
- Shared helpers `fixedDegrees_neighbor_nonempty`, `absorptionTime_eq_consensusTime`,
  `floor_enat_lt_iff`, reused by the paper-facing statements in `MainTheorems.lean`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Classical NNReal ENNReal

noncomputable section

/-! ## General-model lower bounds

The §1/§4 lower-bound theorems, restated over the general κ=2 voter model
`TemporalGraph.VoterModelAbstract G 2 Ω`. Each follows from its two-opinion counterpart
by sending a general model `vm` to `vm.toTwoOpinion` (every vertex of the
fixed-degree construction has a neighbour), under which `A`, `μ`, `T_abs` agree
definitionally. -/

namespace TemporalGraph.VoterProcess.LowerBound

open TemporalGraph

/-- Under fixed degrees every vertex has at least one neighbour at every time. -/
theorem fixedDegrees_neighbor_nonempty {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    {G : TemporalGraph V} (hFix : G.FixedDegrees) :
    ∀ t v, (G.neighborFinset t v).Nonempty :=
  fun t v => Finset.card_pos.mp (hFix.2 v t)

/-- When every vertex always has a neighbour, the two-opinion `absorptionTime` (first time the
minority set empties) and `consensusTime` (first all-equal configuration) coincide pointwise. -/
theorem absorptionTime_eq_consensusTime
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V] {Ω : Type*} [MeasurableSpace Ω]
    {G : TemporalGraph V} (vm : TemporalGraph.VoterModelAbstract G 2 Ω)
    (hG : ∀ t v, (G.neighborFinset t v).Nonempty) (ω : Ω) :
    vm.absorptionTime ω = vm.consensusTime ω := by
  -- The two hitting-time predicates agree pointwise: the minority set of the
  -- opinion-0 set `phiZero (ξ_t)` is empty iff `ξ_t` is at consensus.
  have hpred : ∀ t, (_root_.VoterModel.minoritySet G t (vm.opinionZeroSet t ω) = ∅)
      ↔ _root_.VoterModel.IsConsensus (vm.ξ t ω) := by
    intro t
    show _root_.VoterModel.minoritySet G t (_root_.VoterModel.phiZero (vm.ξ t ω)) = ∅
      ↔ _root_.VoterModel.IsConsensus (vm.ξ t ω)
    constructor
    · intro hempty
      by_contra hcon
      exact _root_.VoterModel.minoritySet_phiZero_ne_empty_of_not_isConsensus hcon hempty
    · intro hcon
      exact _root_.VoterModel.minoritySet_phiZero_eq_empty_of_isConsensus (fun v => hG t v) hcon
  unfold TemporalGraph.VoterModelAbstract.absorptionTime TemporalGraph.VoterModelAbstract.consensusTime
  by_cases hc : ∃ t, _root_.VoterModel.IsConsensus (vm.ξ t ω)
  · have ha : ∃ t, _root_.VoterModel.minoritySet G t (vm.opinionZeroSet t ω) = ∅ := by
      obtain ⟨t, ht⟩ := hc; exact ⟨t, (hpred t).mpr ht⟩
    rw [dif_pos ha, dif_pos hc]
    have h1 : Nat.find ha ≤ Nat.find hc :=
      Nat.find_le ((hpred (Nat.find hc)).mpr (Nat.find_spec hc))
    have h2 : Nat.find hc ≤ Nat.find ha :=
      Nat.find_le ((hpred (Nat.find ha)).mp (Nat.find_spec ha))
    exact_mod_cast le_antisymm h1 h2
  · have ha : ¬ ∃ t, _root_.VoterModel.minoritySet G t (vm.opinionZeroSet t ω) = ∅ := by
      rintro ⟨t, ht⟩; exact hc ⟨t, (hpred t).mp ht⟩
    rw [dif_neg ha, dif_neg hc]

/-- Comparing the floor `⌊x⌋₊` (as an extended natural) against a threshold `T : ℕ∞` is the same
as comparing `x` itself, as an extended real, against `T`. This lets the lower-bound statements
express their time threshold directly via `ENNReal.ofReal x` instead of `⌊x⌋₊`. -/
theorem floor_enat_lt_iff (x : ℝ) (T : ℕ∞) :
    (⌊x⌋₊ : ℕ∞) < T ↔ ENNReal.ofReal x < (T : ℝ≥0∞) := by
  rcases le_total 0 x with hx | hx
  · induction T with
    | top => simp [ENNReal.ofReal_lt_top]
    | coe m =>
      rw [Nat.cast_lt, Nat.floor_lt hx, ENat.toENNReal_coe, ← ENNReal.ofReal_natCast,
          ENNReal.ofReal_lt_ofReal_iff_of_nonneg hx]
  · rw [Nat.floor_of_nonpos hx, ENNReal.ofReal_of_nonpos hx]
    induction T with
    | top => simp
    | coe m => simp [ENat.toENNReal_coe]


end TemporalGraph.VoterProcess.LowerBound
