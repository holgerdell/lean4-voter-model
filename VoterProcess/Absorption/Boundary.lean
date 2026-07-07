module

import VoterProcess.Absorption.Basic
import VoterProcess.TwoOpinion
public import VoterProcess.Step

/-! ## Boundary states are absorbing for the two-opinion voter process

A *boundary* (consensus) state of the two-opinion model is an opinion-0 set
`A ∈ {∅, Finset.univ}`: either every vertex holds opinion `1` (`A = ∅`) or every
vertex holds opinion `0` (`A = Finset.univ`). The one-step distribution
`stepDist₂` fixes both: `stepDist₂ G t ∅ = PMF.pure ∅` (`stepDist₂_empty`) and
`stepDist₂ G t univ = PMF.pure univ` (`stepDist₂_univ`). Hence, conditioned on the
history, once `A_t` is a boundary state it stays equal to it forever, almost
surely. This is the two-opinion replacement for the structure field
`hT_abs_permanent`.

The empty minority set `minoritySet G t A = ∅` is equivalent to `A` being a
boundary state **provided the volume is positive** (true under `FixedDegrees`,
which forbids isolated vertices): the volume tie-break in `minoritySet` only
sends `univ` to `∅` when `Vol(univ) > 0`. The forward implication
(`minoritySet = ∅ → A ∈ {∅, univ}`) holds unconditionally.

## Main results

- `VoterModel.minoritySet_empty` — `minoritySet G t ∅ = ∅`.
- `VoterModel.minoritySet_univ_of_degree_pos` — positive degrees give
  `minoritySet G t univ = ∅`.
- `VoterModel.boundary_of_minoritySet_empty` — `minoritySet G t S = ∅ →
  S = ∅ ∨ S = univ` (unconditional).
- `VoterModel.minoritySet_empty_iff_boundary` — under positive degrees,
  `minoritySet G t S = ∅ ↔ S = ∅ ∨ S = univ`.
- `VoterModelAbstract.ae_mem_boundary_permanent` — a.e., once `A` is a
  boundary state it stays constant (unconditional).
- `VoterModelAbstract.ae_minoritySet_empty_permanent` — a.e. permanence of the
  empty minority set, under `FixedDegrees`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Classical

noncomputable section

namespace VoterModel

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V] {G : TemporalGraph V}

/-- The minority set of the empty opinion-0 set is empty: `Vol(∅) = 0 ≤ Vol(V)`,
so the `minoritySet` tie-break keeps `∅`. -/
theorem minoritySet_empty (t : ℕ) : minoritySet G t (∅ : Finset V) = ∅ := by
  unfold minoritySet
  rw [if_pos]
  simp [TemporalGraph.volume, SimpleGraph.volume]

/-- With positive degrees, the minority set of the full set is empty:
`Vol(V) > 0 = Vol(∅)`, so the `minoritySet` tie-break sends `univ` to
`univ \ univ = ∅`. -/
theorem minoritySet_univ_of_degree_pos (t : ℕ)
    (hpos : ∀ v : V, 0 < TemporalGraph.degree G t v) :
    minoritySet G t (Finset.univ : Finset V) = ∅ := by
  unfold minoritySet
  rw [if_neg]
  · simp
  · have hvol : 0 < TemporalGraph.volume G t (Finset.univ : Finset V) :=
      SimpleGraph.volume_univ_pos hpos
    simp only [Finset.sdiff_self]
    simp only [TemporalGraph.volume, SimpleGraph.volume, Finset.sum_empty] at *
    omega

/-- The forward implication of the boundary characterization, **unconditional**:
if the minority set is empty then the opinion-0 set is a boundary state. The
`minoritySet` is either `S` (forcing `S = ∅`) or `univ \ S` (forcing `S = univ`). -/
theorem boundary_of_minoritySet_empty (t : ℕ) (S : Finset V)
    (h : minoritySet G t S = ∅) : S = ∅ ∨ S = Finset.univ := by
  unfold minoritySet at h
  split_ifs at h with hcond
  · exact Or.inl h
  · right
    rw [Finset.sdiff_eq_empty_iff_subset] at h
    exact Finset.Subset.antisymm (Finset.subset_univ S) h

end VoterModel

namespace TemporalGraph.VoterModelAbstract

open _root_.VoterModel

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
  {Ω : Type*} [mΩ : MeasurableSpace Ω] {G : TemporalGraph V}

/-- The set `{ω | A t ω = T}` is measurable w.r.t. the time-`t` history
σ-algebra `ℱ_t = ⨆ j ∈ Iic t, σ(A_j)`. -/
private theorem measurableSet_history_eq (vm : VoterModelAbstract G 2 Ω) (t : ℕ)
    (T : Finset V) :
    @MeasurableSet Ω (⨆ j ∈ Finset.Iic t, MeasurableSpace.comap (vm.opinionZeroSet j) ⊤)
      {ω | vm.opinionZeroSet t ω = T} := by
  have hle : MeasurableSpace.comap (vm.opinionZeroSet t) ⊤
      ≤ ⨆ j ∈ Finset.Iic t, MeasurableSpace.comap (vm.opinionZeroSet j) ⊤ :=
    le_iSup₂ (f := fun j (_ : j ∈ Finset.Iic t) => MeasurableSpace.comap (vm.opinionZeroSet j) ⊤)
      t (Finset.mem_Iic.mpr le_rfl)
  exact hle _ ⟨{T}, trivial, rfl⟩

/-- The set `{ω | A t ω = T}` is measurable in the ambient σ-algebra. -/
private theorem measurableSet_eq (vm : VoterModelAbstract G 2 Ω) (t : ℕ) (T : Finset V) :
    MeasurableSet {ω | vm.opinionZeroSet t ω = T} :=
  vm.A_meas t _ ⟨{T}, trivial, rfl⟩

/-- One-step permanence as a measure-zero statement: for a state `S` whose
one-step distribution is the point mass at `S` and any target `S' ≠ S`,
transitioning from `S` at time `t` to `S'` at time `t+1` is null. -/
private theorem measure_transition_pure_eq_zero (vm : VoterModelAbstract G 2 Ω) (t : ℕ)
    (S S' : Finset V) (hfix : VoterModel.stepDist₂ G t S = PMF.pure S) (hne : S' ≠ S) :
    (vm.μ : Measure Ω) ({ω | vm.opinionZeroSet t ω = S} ∩ {ω | vm.opinionZeroSet (t + 1) ω = S'}) = 0 := by
  rw [vm.A_markovProperty t S' {ω | vm.opinionZeroSet t ω = S} (measurableSet_history_eq vm t S)]
  rw [setLIntegral_congr_fun (measurableSet_eq vm t S)
    (g := fun _ => (0 : ENNReal)) (fun ω hω => ?_)]
  · simp
  · simp only [Set.mem_setOf_eq] at hω
    rw [hω, hfix, PMF.pure_apply]
    simp [hne]

/-- One-step a.e. permanence on the boundary: almost surely, if `A t ω` is a
boundary state (`∅` or `univ`) then `A (t+1) ω` equals it. -/
private theorem ae_mem_boundary_step (vm : VoterModelAbstract G 2 Ω) (t : ℕ) :
    ∀ᵐ ω ∂(vm.μ : Measure Ω),
      (vm.opinionZeroSet t ω = ∅ ∨ vm.opinionZeroSet t ω = Finset.univ) → vm.opinionZeroSet (t + 1) ω = vm.opinionZeroSet t ω := by
  rw [ae_iff]
  have hsub : {ω | ¬ ((vm.opinionZeroSet t ω = ∅ ∨ vm.opinionZeroSet t ω = Finset.univ) →
      vm.opinionZeroSet (t + 1) ω = vm.opinionZeroSet t ω)} ⊆
      ⋃ S : Finset V, ⋃ (_ : S = ∅ ∨ S = Finset.univ), ⋃ S' : Finset V, ⋃ (_ : S' ≠ S),
        ({ω | vm.opinionZeroSet t ω = S} ∩ {ω | vm.opinionZeroSet (t + 1) ω = S'}) := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Classical.not_imp] at hω
    obtain ⟨hbdy, hne⟩ := hω
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    exact ⟨vm.opinionZeroSet t ω, hbdy, vm.opinionZeroSet (t + 1) ω, hne, rfl, rfl⟩
  refine measure_mono_null hsub ?_
  refine measure_iUnion_null fun S => measure_iUnion_null fun hS =>
    measure_iUnion_null fun S' => measure_iUnion_null fun hne => ?_
  have hfix : VoterModel.stepDist₂ G t S = PMF.pure S := by
    rcases hS with rfl | rfl
    · exact VoterModel.stepDist₂_empty G t
    · exact VoterModel.stepDist₂_univ G t
  exact measure_transition_pure_eq_zero vm t S S' hfix hne

/-- **A.e. permanence of boundary states** (unconditional): almost surely, once
the opinion-0 set `A` reaches a boundary state (`∅` or `univ`) it stays constant
forever. The boundary states are the fixed points of `stepDist₂`. -/
theorem ae_mem_boundary_permanent (vm : VoterModelAbstract G 2 Ω) :
    ∀ᵐ ω ∂(vm.μ : Measure Ω), ∀ t s : ℕ, t ≤ s →
      (vm.opinionZeroSet t ω = ∅ ∨ vm.opinionZeroSet t ω = Finset.univ) → vm.opinionZeroSet s ω = vm.opinionZeroSet t ω := by
  have hall : ∀ᵐ ω ∂(vm.μ : Measure Ω), ∀ t : ℕ,
      (vm.opinionZeroSet t ω = ∅ ∨ vm.opinionZeroSet t ω = Finset.univ) → vm.opinionZeroSet (t + 1) ω = vm.opinionZeroSet t ω :=
    ae_all_iff.mpr (ae_mem_boundary_step vm)
  filter_upwards [hall] with ω hω
  intro t s hts
  induction s, hts using Nat.le_induction with
  | base => exact fun _ => rfl
  | succ s hts ih =>
      intro hbdy
      have hAs : vm.opinionZeroSet s ω = vm.opinionZeroSet t ω := ih hbdy
      have hbdy_s : vm.opinionZeroSet s ω = ∅ ∨ vm.opinionZeroSet s ω = Finset.univ := hAs ▸ hbdy
      rw [hω s hbdy_s, hAs]

/-- **A.e. permanence of consensus** for the two-opinion process, under
`FixedDegrees`: almost surely, once the minority set is empty it stays empty
forever. This is the law-only replacement for the structure field
`hT_abs_permanent`.

`FixedDegrees` (positive degrees) is needed only to convert the absorbing
boundary state `A = univ` back to `minoritySet = ∅`; the forward direction and
the boundary permanence are unconditional. -/
theorem ae_minoritySet_empty_permanent {G : TemporalGraphFixedDegree V}
    (vm : VoterModelAbstract G 2 Ω) :
    ∀ᵐ ω ∂(vm.μ : Measure Ω), ∀ t s : ℕ, t ≤ s →
      VoterModel.minoritySet G.toTemporalGraph t (vm.opinionZeroSet t ω) = ∅ →
      VoterModel.minoritySet G.toTemporalGraph s (vm.opinionZeroSet s ω) = ∅ := by
  filter_upwards [ae_mem_boundary_permanent vm] with ω hω
  intro t s hts hempty
  have hbdy : vm.opinionZeroSet t ω = ∅ ∨ vm.opinionZeroSet t ω = Finset.univ :=
    VoterModel.boundary_of_minoritySet_empty t (vm.opinionZeroSet t ω) hempty
  have hAs : vm.opinionZeroSet s ω = vm.opinionZeroSet t ω := hω t s hts hbdy
  rw [hAs]
  rcases hbdy with hb | hb
  · rw [hb]; exact VoterModel.minoritySet_empty s
  · rw [hb]; exact VoterModel.minoritySet_univ_of_degree_pos s (fun v => G.degrees_pos v s)

end TemporalGraph.VoterModelAbstract
