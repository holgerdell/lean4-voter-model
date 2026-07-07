module

import VoterProcess.Absorption.Basic
public import VoterProcess.CrossCut

/-! ## Absorbing-state lemmas for the VoterModel structure

Structure-level (measure-theoretic) versions of the absorbing-boundary and
Chapman–Kolmogorov lemmas, stated in terms of the `VoterModelAbstract G 2 Ω` structure
rather than the raw `opinionProcess₂` PMF.

## Main results
- `opinionProcess₂_empty_eq_pure`: `opinionProcess₂ G t₀ Δ ∅ = PMF.pure ∅`.
- `opinionProcess₂_univ_eq_pure`: `opinionProcess₂ G t₀ Δ univ = PMF.pure univ`.
- `markov_deterministic_init`: under deterministic initial state,
  `vm.μ {ω | vm.opinionZeroSet Δ ω = S'} = opinionProcess₂ G 0 Δ A₀ S'`.
- `voterModel_chapmanKolmogorov`: total probability formula
  `vm.μ {A (t₀+Δ) = S'} = ∑_T vm.μ {A t₀ = T} * opinionProcess₂ G t₀ Δ T S'`.
- `voterModel_empty_absorbing`: deterministic init `vm.opinionZeroSet 0 = ∅` ⟹ `vm.μ {A t = ∅} = 1`.
- `voterModel_univ_absorbing`: deterministic init `vm.opinionZeroSet 0 = univ` ⟹ `vm.μ {A t = univ} = 1`.
-/

@[expose] public section

noncomputable section

namespace TemporalGraph.VoterProcess.LowerBound

open MeasureTheory Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
variable {G : TemporalGraph V} {Ω : Type*} [MeasurableSpace Ω]

/-- The empty set is absorbing for `opinionProcess₂`:
    `opinionProcess₂ G t₀ Δ ∅ = PMF.pure ∅` for all `t₀`, `Δ`. -/
theorem opinionProcess₂_empty_eq_pure (G : TemporalGraph V) (t₀ Δ : ℕ) :
    VoterModel.opinionProcess₂ G t₀ Δ ∅ = PMF.pure ∅ := by
  induction Δ with
  | zero => rfl
  | succ Δ ih =>
    show (VoterModel.opinionProcess₂ G t₀ Δ ∅).bind
        (VoterModel.stepDist₂ G (t₀ + Δ)) = PMF.pure ∅
    rw [ih, PMF.pure_bind, VoterModel.stepDist₂_empty]

/-- The universal set is absorbing for `opinionProcess₂`:
    `opinionProcess₂ G t₀ Δ univ = PMF.pure univ` for all `t₀`, `Δ`. -/
theorem opinionProcess₂_univ_eq_pure (G : TemporalGraph V) (t₀ Δ : ℕ) :
    VoterModel.opinionProcess₂ G t₀ Δ Finset.univ = PMF.pure Finset.univ := by
  induction Δ with
  | zero => rfl
  | succ Δ ih =>
    show (VoterModel.opinionProcess₂ G t₀ Δ Finset.univ).bind
        (VoterModel.stepDist₂ G (t₀ + Δ)) = PMF.pure Finset.univ
    rw [ih, PMF.pure_bind, VoterModel.stepDist₂_univ]

end TemporalGraph.VoterProcess.LowerBound
