module

public import VoterProcess.Step
import Mathlib.Data.ENat.Lattice

/-! ## The consensus time as an `ℕ∞`-valued hitting time

This file defines the *consensus time* of a κ-opinion voter model as an
`ℕ∞`-valued function, the first time the opinion process reaches a consensus
state (or `⊤` if consensus is never reached), and proves its basic API:
characterization of finiteness, the consensus spec at the (finite) hitting time,
minimality, measurability, and a.e. permanence.

`consensusTime` is the law-only replacement for the structure field `T_abs`
(it will be renamed to `T_abs` once the field is removed). The permanence and
measurability proofs use `ae_isConsensus_permanent` and the discrete σ-algebra
on `V → Fin κ` carried by `hξ_meas`.

## Main results

- `VoterModelAbstract.consensusTime` — the `ℕ∞`-valued consensus time (`Nat.find` or `⊤`).
- `VoterModelAbstract.consensusTime_lt_top_iff` — finiteness iff consensus is reached.
- `VoterModelAbstract.isConsensus_consensusTime` — consensus holds at the finite hitting time.
- `VoterModelAbstract.not_isConsensus_of_lt_consensusTime` — minimality of the hitting time.
- `VoterModelAbstract.coe_lt_consensusTime_iff_forall` — `n <` iff consensus is not reached
  at any time `t ≤ n`.
- `VoterModelAbstract.consensusTime_measurable` — `consensusTime` is measurable.
- `VoterModelAbstract.ae_isConsensus_of_consensusTime_le` — a.e., consensus holds at every
  time `s` with `consensusTime ω ≤ s`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Classical

noncomputable section

namespace TemporalGraph.VoterModelAbstract

open _root_.VoterModel

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V] {κ : ℕ} [NeZero κ]
  {Ω : Type*} [mΩ : MeasurableSpace Ω] {G : TemporalGraph V}

/-- Consensus time: the first time `t` at which all vertices share an opinion, or `⊤` if that never
happens (`ℕ∞`-valued). -/
def consensusTime {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V] {κ : ℕ} [NeZero κ] {Ω : Type*} [MeasurableSpace Ω] {G : TemporalGraph V} (vm : VoterModelAbstract G κ Ω) (ω : Ω) : ℕ∞ :=
  if h : ∃ t, IsConsensus (vm.ξ t ω) then (Nat.find h : ℕ∞) else ⊤

/-- The consensus time is finite iff the process reaches consensus at some time. -/
theorem consensusTime_lt_top_iff (vm : VoterModelAbstract G κ Ω) (ω : Ω) :
    vm.consensusTime ω < ⊤ ↔ ∃ t, IsConsensus (vm.ξ t ω) := by
  unfold consensusTime
  split_ifs with h
  · simp [h, ENat.coe_lt_top]
  · simp [h]


/-- Minimality: before the consensus time the process is not at consensus. -/
theorem not_isConsensus_of_lt_consensusTime (vm : VoterModelAbstract G κ Ω) (ω : Ω) (t : ℕ)
    (ht : (t : ℕ∞) < vm.consensusTime ω) :
    ¬ IsConsensus (vm.ξ t ω) := by
  by_cases he : ∃ s, IsConsensus (vm.ξ s ω)
  · have hval : vm.consensusTime ω = (Nat.find he : ℕ∞) := by
      unfold consensusTime; exact dif_pos he
    rw [hval] at ht
    have htlt : t < Nat.find he := by exact_mod_cast ht
    exact Nat.find_min he htlt
  · push Not at he; exact he t

/-- `{ω | IsConsensus (ξ t ω)}` is measurable in the ambient σ-algebra. -/
private theorem measurableSet_isConsensus (vm : VoterModelAbstract G κ Ω) (t : ℕ) :
    MeasurableSet {ω | IsConsensus (vm.ξ t ω)} :=
  vm.hξ_meas t _ ⟨{g | IsConsensus g}, trivial, rfl⟩

/-- The consensus time is measurable. The preimage of each value `x : ℕ∞` is a
countable Boolean combination of the measurable consensus events `{ξ t = consensus}`. -/
theorem consensusTime_measurable (vm : VoterModelAbstract G κ Ω) : Measurable vm.consensusTime := by
  apply measurable_to_countable'
  intro x
  induction x using ENat.recTopCoe with
  | top =>
      have heq : vm.consensusTime ⁻¹' {(⊤ : ℕ∞)} =
          ⋂ t, {ω | ¬ IsConsensus (vm.ξ t ω)} := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Set.mem_setOf_eq]
        rw [← not_lt_top_iff (a := vm.consensusTime ω), consensusTime_lt_top_iff]
        push Not
        rfl
      rw [heq]
      exact MeasurableSet.iInter fun t => (measurableSet_isConsensus vm t).compl
  | coe n =>
      have heq : vm.consensusTime ⁻¹' {(n : ℕ∞)} =
          {ω | IsConsensus (vm.ξ n ω)} ∩ ⋂ k ∈ Finset.range n,
            {ω | ¬ IsConsensus (vm.ξ k ω)} := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff,
          Set.mem_iInter, Finset.mem_range, Set.mem_setOf_eq]
        constructor
        · intro hx
          have hlt : vm.consensusTime ω < ⊤ := by rw [hx]; exact ENat.coe_lt_top n
          have he : ∃ t, IsConsensus (vm.ξ t ω) := (consensusTime_lt_top_iff vm ω).mp hlt
          have hval : vm.consensusTime ω = (Nat.find he : ℕ∞) := by
            unfold consensusTime; exact dif_pos he
          rw [hval] at hx
          have hfind : Nat.find he = n := by exact_mod_cast hx
          refine ⟨hfind ▸ Nat.find_spec he, fun k hk => ?_⟩
          exact Nat.find_min he (hfind ▸ hk)
        · rintro ⟨hcons, hmin⟩
          have he : ∃ t, IsConsensus (vm.ξ t ω) := ⟨n, hcons⟩
          have hval : vm.consensusTime ω = (Nat.find he : ℕ∞) := by
            unfold consensusTime; exact dif_pos he
          rw [hval]
          have hfind : Nat.find he = n := by
            refine le_antisymm (Nat.find_le hcons) ?_
            by_contra hlt
            push Not at hlt
            exact hmin (Nat.find he) hlt (Nat.find_spec he)
          rw [hfind]
      rw [heq]
      refine (measurableSet_isConsensus vm n).inter ?_
      exact MeasurableSet.biInter (Finset.range n).countable_toSet
        fun k _ => (measurableSet_isConsensus vm k).compl

end TemporalGraph.VoterModelAbstract
