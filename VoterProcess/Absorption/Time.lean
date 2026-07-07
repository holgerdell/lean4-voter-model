module

import VoterProcess.Absorption.Boundary
import VoterProcess.TwoOpinion
public import VoterProcess.Step
import Mathlib.Data.ENat.Lattice

/-! ## The absorption time as an `ℕ∞`-valued hitting time

This file defines the *absorption time* of a two-opinion voter model as an
`ℕ∞`-valued function, the first time the minority set becomes empty (or `⊤` if it
never does), and proves its basic API: characterization of finiteness, the
absorption spec at the (finite) hitting time, minimality, measurability, a.e.
permanence, and a.e. finiteness under positive conductance.

`absorptionTime` is the law-only replacement for the structure field `T_abs`
(it will be renamed to `T_abs` once the field is removed). The permanence,
finiteness, and measurability proofs use `ae_minoritySet_empty_permanent`,
`ae_exists_minoritySet_empty`, and the discrete σ-algebra on `Finset V` carried
by `hA_meas`.

## Main results

- `VoterModelAbstract.absorptionTime` — the `ℕ∞`-valued absorption time.
- `VoterModelAbstract.absorptionTime_lt_top_iff` — finiteness iff the minority
  set is empty at some time.
- `VoterModelAbstract.minoritySet_empty_absorptionTime` — empty minority set at
  the finite hitting time.
- `VoterModelAbstract.minoritySet_ne_empty_of_lt_absorptionTime` — minimality.
- `VoterModelAbstract.absorptionTime_le_coe_iff_exists` — `≤ n` iff the minority
  set is empty at some time `t ≤ n`.
- `VoterModelAbstract.coe_lt_absorptionTime_iff_forall` — `n <` iff the minority
  set is nonempty at every time `t ≤ n`.
- `VoterModelAbstract.absorptionTime_measurable` — measurability.
- `VoterModelAbstract.ae_minoritySet_empty_of_absorptionTime_le` — a.e.,
  empty minority set at every time `s` with `absorptionTime ω ≤ s`.
- `VoterModelAbstract.absorptionTime_finite_ae` — a.e. finiteness under
  fixed degrees and positive conductance.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Classical

noncomputable section

namespace TemporalGraph.VoterModelAbstract

open _root_.VoterModel

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
  {Ω : Type*} [mΩ : MeasurableSpace Ω] {G : TemporalGraph V}

/-- The absorption time `absorptionTime ω ∈ ℕ∞`: the first time the minority set
is empty, or `⊤` if it is never empty. -/
def absorptionTime (vm : VoterModelAbstract G 2 Ω) (ω : Ω) : ℕ∞ :=
  if h : ∃ t, minoritySet G t (vm.opinionZeroSet t ω) = ∅ then (Nat.find h : ℕ∞) else ⊤

/-- The absorption time is finite iff the minority set is empty at some time. -/
theorem absorptionTime_lt_top_iff (vm : VoterModelAbstract G 2 Ω) (ω : Ω) :
    vm.absorptionTime ω < ⊤ ↔ ∃ t, minoritySet G t (vm.opinionZeroSet t ω) = ∅ := by
  unfold absorptionTime
  split_ifs with h
  · simp [h, ENat.coe_lt_top]
  · simp [h]



/-- `{ω | minoritySet G t (A t ω) = ∅}` is measurable in the ambient σ-algebra. -/
private theorem measurableSet_minoritySet_empty (vm : VoterModelAbstract G 2 Ω) (t : ℕ) :
    MeasurableSet {ω | minoritySet G t (vm.opinionZeroSet t ω) = ∅} :=
  vm.A_meas t _ ⟨{S | minoritySet G t S = ∅}, trivial, rfl⟩

/-- The absorption time is measurable. The preimage of each value `x : ℕ∞` is a
countable Boolean combination of the measurable absorption events
`{minoritySet G t (A t) = ∅}`. -/
theorem absorptionTime_measurable (vm : VoterModelAbstract G 2 Ω) :
    Measurable vm.absorptionTime := by
  apply measurable_to_countable'
  intro x
  induction x using ENat.recTopCoe with
  | top =>
      have heq : vm.absorptionTime ⁻¹' {(⊤ : ℕ∞)} =
          ⋂ t, {ω | minoritySet G t (vm.opinionZeroSet t ω) ≠ ∅} := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Set.mem_setOf_eq]
        rw [← not_lt_top_iff (a := vm.absorptionTime ω), absorptionTime_lt_top_iff]
        push Not
        rfl
      rw [heq]
      exact MeasurableSet.iInter fun t => (measurableSet_minoritySet_empty vm t).compl
  | coe n =>
      have heq : vm.absorptionTime ⁻¹' {(n : ℕ∞)} =
          {ω | minoritySet G n (vm.opinionZeroSet n ω) = ∅} ∩ ⋂ k ∈ Finset.range n,
            {ω | minoritySet G k (vm.opinionZeroSet k ω) ≠ ∅} := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff,
          Set.mem_iInter, Finset.mem_range, Set.mem_setOf_eq]
        constructor
        · intro hx
          have hlt : vm.absorptionTime ω < ⊤ := by rw [hx]; exact ENat.coe_lt_top n
          have he : ∃ t, minoritySet G t (vm.opinionZeroSet t ω) = ∅ :=
            (absorptionTime_lt_top_iff vm ω).mp hlt
          have hval : vm.absorptionTime ω = (Nat.find he : ℕ∞) := by
            unfold absorptionTime; exact dif_pos he
          rw [hval] at hx
          have hfind : Nat.find he = n := by exact_mod_cast hx
          refine ⟨hfind ▸ Nat.find_spec he, fun k hk => ?_⟩
          exact Nat.find_min he (hfind ▸ hk)
        · rintro ⟨hempty, hmin⟩
          have he : ∃ t, minoritySet G t (vm.opinionZeroSet t ω) = ∅ := ⟨n, hempty⟩
          have hval : vm.absorptionTime ω = (Nat.find he : ℕ∞) := by
            unfold absorptionTime; exact dif_pos he
          rw [hval]
          have hfind : Nat.find he = n := by
            refine le_antisymm (Nat.find_le hempty) ?_
            by_contra hlt
            push Not at hlt
            exact hmin (Nat.find he) hlt (Nat.find_spec he)
          rw [hfind]
      rw [heq]
      refine (measurableSet_minoritySet_empty vm n).inter ?_
      exact MeasurableSet.biInter (Finset.range n).countable_toSet
        fun k _ => (measurableSet_minoritySet_empty vm k).compl

/-- Threshold characterization: `absorptionTime ω ≤ n` iff the minority set is
empty at some time `t ≤ n`. Law-only (field-free) replacement for `T_abs ≤ n`. -/
theorem absorptionTime_le_coe_iff_exists (vm : VoterModelAbstract G 2 Ω) (ω : Ω) (n : ℕ) :
    vm.absorptionTime ω ≤ (n : ℕ∞) ↔ ∃ t ≤ n, minoritySet G t (vm.opinionZeroSet t ω) = ∅ := by
  by_cases he : ∃ t, minoritySet G t (vm.opinionZeroSet t ω) = ∅
  · have hval : vm.absorptionTime ω = (Nat.find he : ℕ∞) := by
      unfold absorptionTime; exact dif_pos he
    rw [hval, Nat.cast_le, Nat.find_le_iff]
  · have hval : vm.absorptionTime ω = ⊤ := by unfold absorptionTime; exact dif_neg he
    rw [hval]
    simp only [top_le_iff, ENat.coe_ne_top n, false_iff]
    push Not at he
    rintro ⟨t, _, ht⟩
    exact (Finset.nonempty_iff_ne_empty.mp (he t)) ht


/-- A.e. permanence: almost surely, the minority set is empty at every time `s`
with `absorptionTime ω ≤ s`. Derived from `ae_minoritySet_empty_permanent` by
applying permanence from the finite hitting time `(absorptionTime ω).toNat ≤ s`. -/
theorem ae_minoritySet_empty_of_absorptionTime_le {G : TemporalGraphFixedDegree V}
    (vm : VoterModelAbstract G 2 Ω) :
    ∀ᵐ ω ∂(vm.μ : Measure Ω), ∀ s : ℕ, vm.absorptionTime ω ≤ (s : ℕ∞) →
      minoritySet G.toTemporalGraph s (vm.opinionZeroSet s ω) = ∅ := by
  filter_upwards [ae_minoritySet_empty_permanent vm] with ω hperm
  intro s hs
  have hlt : vm.absorptionTime ω < ⊤ := lt_of_le_of_lt hs (ENat.coe_lt_top s)
  have he : ∃ t, minoritySet G.toTemporalGraph t (vm.opinionZeroSet t ω) = ∅ :=
    (absorptionTime_lt_top_iff vm ω).mp hlt
  have hval : vm.absorptionTime ω = (Nat.find he : ℕ∞) := by
    unfold absorptionTime; exact dif_pos he
  rw [hval] at hs
  have hfs : Nat.find he ≤ s := by exact_mod_cast hs
  exact hperm (Nat.find he) s hfs (Nat.find_spec he)



/-- The absorption time depends only on the minority-set-empty predicate sequence:
if two models (possibly on different probability spaces) have the same emptiness
pattern at outcomes `ω₁`, `ω₂`, their absorption times coincide. -/
theorem absorptionTime_eq_of_minoritySet_eq
    {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (vm₁ : VoterModelAbstract G 2 Ω₁) (vm₂ : VoterModelAbstract G 2 Ω₂) (ω₁ : Ω₁) (ω₂ : Ω₂)
    (h : ∀ t, minoritySet G t (vm₁.opinionZeroSet t ω₁) = ∅ ↔ minoritySet G t (vm₂.opinionZeroSet t ω₂) = ∅) :
    vm₁.absorptionTime ω₁ = vm₂.absorptionTime ω₂ := by
  unfold absorptionTime
  by_cases hc : ∃ t, minoritySet G t (vm₂.opinionZeroSet t ω₂) = ∅
  · have hc' : ∃ t, minoritySet G t (vm₁.opinionZeroSet t ω₁) = ∅ := hc.imp fun t ht => (h t).mpr ht
    rw [dif_pos hc', dif_pos hc]
    norm_cast
    exact le_antisymm (Nat.find_le ((h _).mpr (Nat.find_spec hc)))
      (Nat.find_le ((h _).mp (Nat.find_spec hc')))
  · have hc' : ¬ ∃ t, minoritySet G t (vm₁.opinionZeroSet t ω₁) = ∅ :=
      fun hh => hc (hh.imp fun t ht => (h t).mp ht)
    rw [dif_neg hc', dif_neg hc]

end TemporalGraph.VoterModelAbstract
