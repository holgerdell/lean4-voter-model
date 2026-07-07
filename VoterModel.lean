module

import UpperBound.General
import LowerBound.General
public import VoterProcess.Model
public import TemporalGraph.Degree
public import TemporalGraph.Conductance
public import TemporalGraph.Basic
import Mathlib.Algebra.Order.Star.Real
import LowerBound.Absorption.Core

/-! ## Main theorems

The paper-facing statements of the voter-model bounds, phrased over the standard voter
model via `consensusTime`. Each is a thin wrapper around the general abstract-model results
in `TheoremUpperBoundGeneral.lean` / `TheoremLowerBoundGeneral.lean`.

## Main results

- `upper_bound_window_conductance` (`thm:upper-bound-window-conductance`) — §3.4 upper bound, general `κ`-opinion window form.
- `upper_bound_temporal_conductance` (`thm:upper-bound-temporal-conductance`) — §3.4 upper bound in closed form.
- `lower_bound_3regular` (`thm:lower-bound-3regular`) — §4 lower
  bound (`κ=2`) on arbitrarily large 3-regular temporal graphs.
- `lower_bound_odd_regular_averaged` (`thm:lower-bound-odd-regular-averaged`) — §1 introduction
  interval lower bound (`κ=2`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Classical ENNReal NNReal

noncomputable section

open TemporalGraph
open TemporalGraph.VoterProcess.LowerBound

-- Root-namespace alias so the headline statements can write the paper's `Φ G`
-- without an `open TemporalGraphFixedDegree in` prefix.
export TemporalGraphFixedDegree (Φ Φ_eq)

/-- \label{thm:upper-bound-window-conductance} -/
theorem upper_bound_window_conductance
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V] {κ : ℕ} [NeZero κ]
    (G : TemporalGraphFixedDegree V) (vm : VoterModel G κ)
    (Δ : ℕ → ℕ) (hΔ_pos : ∀ j, 1 ≤ Δ j)
    (φ : ℕ → ℝ) (hφ_nn : ∀ j, 0 ≤ φ j) (hφ_le1 : ∀ j, φ j ≤ 1)
    (hwin : ∀ j, ∀ Sc ∈ G.admissibleCuts,
      φ j ≤ G.maxSetConductanceOnInterval (∑ i ∈ Finset.range j, Δ i) (Δ j) Sc)
    (J : ℕ) (hJ : 2 ^ 21 * G.numEdges / G.minDegree ≤ ∑ ℓ ∈ Finset.range (J + 1), φ ℓ) :
    0.5 ≤ vm.μ {ξ | VoterModel.consensusTime ξ ≤ ∑ j ∈ Finset.range (J + 1), Δ j} := by
  rw [G.minDegree_eq_minDegreeAt 0, mul_div_assoc] at hJ
  have h := upper_bound_window_conductance_abstract G vm.toAbstract Δ hΔ_pos φ hφ_nn hφ_le1 hwin J hJ
  exact h

/-- \label{thm:upper-bound-temporal-conductance} -/
theorem upper_bound_temporal_conductance
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V] {κ : ℕ} [NeZero κ]
    (G : TemporalGraphFixedDegree V) (vm : VoterModel G κ) :
    0.5 ≤ vm.μ {ξ | (VoterModel.consensusTime ξ : ℝ≥0∞) ≤ 2 ^ 22 * G.numEdges / (G.minDegree * Φ G)} := by
  rw [G.minDegree_eq_minDegreeAt 0, Φ_eq]
  exact upper_bound_temporal_conductance_abstract G vm.toAbstract

/-- The deterministic voter model started with opinion `0` exactly on `s₀`
(and opinion `1` elsewhere) has opinion-0 set equal to `s₀` almost surely at time `0`.
This is the a.e. initial condition consumed by the §4 absorption lemma. -/
private theorem ofDeterministic_ae_opinionZeroSet
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraphFixedDegree V) (s₀ : Finset V) :
    ∀ᵐ ω ∂((VoterModel.ofDeterministic G
        (fun v => if v ∈ s₀ then (0 : Fin 2) else 1)).toAbstract.μ : Measure _),
      (VoterModel.ofDeterministic G
        (fun v => if v ∈ s₀ then (0 : Fin 2) else 1)).toAbstract.opinionZeroSet 0 ω = s₀ := by
  set ξ₀ : V → Fin 2 := fun v => if v ∈ s₀ then (0 : Fin 2) else 1 with hξ₀
  set vm := VoterModel.ofDeterministic G ξ₀ with hvm
  have hmeas : MeasurableSet {ω : ℕ → (V → Fin 2) | ω 0 = ξ₀} := by
    have hpre : {ω : ℕ → (V → Fin 2) | ω 0 = ξ₀} = (fun ω => ω 0) ⁻¹' {ξ₀} := by
      ext ω; simp [Set.mem_preimage, Set.mem_singleton_iff]
    rw [hpre]
    exact (measurable_pi_apply 0) (MeasurableSet.singleton ξ₀)
  have hstart : (vm.toAbstract.μ : Measure _) {ω : ℕ → (V → Fin 2) | ω 0 = ξ₀} = 1 := by
    rw [hvm]
    show (_root_.VoterModel.voterTrajectoryMeasureFrom G.toTemporalGraph (Measure.dirac ξ₀))
        {ω | ω 0 = ξ₀} = 1
    rw [_root_.VoterModel.voterTrajectoryMeasureFrom_marginal_zero]
    simp
  have hae_good : ∀ᵐ (ω : ℕ → (V → Fin 2)) ∂(vm.toAbstract.μ : Measure _), ω 0 = ξ₀ := by
    rw [MeasureTheory.ae_iff]
    have hcompl : {ω : ℕ → (V → Fin 2) | ¬ (ω 0 = ξ₀)} = {ω | ω 0 = ξ₀}ᶜ := rfl
    rw [hcompl, measure_compl hmeas (measure_ne_top _ _), measure_univ, hstart, tsub_self]
  filter_upwards [hae_good] with ω hω
  show Finset.univ.filter (fun v => ω 0 v = 0) = s₀
  rw [hω]
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hξ₀]
  by_cases hv : v ∈ s₀
  · rw [if_pos hv]; simp [hv]
  · rw [if_neg hv]; simp only [hv, iff_false]; decide

/-- \label{thm:lower-bound-3regular} -/
theorem lower_bound_3regular :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
    ∃ (V : Type) (_ : Fintype V) (_ : Nonempty V) (_ : DecidableEq V)
      (G : TemporalGraphFixedDegree V),
      Fintype.card V = n ∧
      (∀ t v, (G.snapshot t).degree v = 3) ∧
    ∃ vm : VoterModel G 2,
      0.5 ≤ vm.μ {ξ | VoterModel.consensusTime ξ > n / (3684 * Φ G)} := by
  have H := lower_bound_3regular_voter_absorption
  intro N
  obtain ⟨n, hn, V, hFV, hNe, hDE, G, hFix, hcard, hdeg, hΦpos, s₀, habs⟩ := H N
  -- Canonical witness: the deterministic voter model started at `s₀` (opinion 0 on `s₀`),
  -- whose opinion-0 set equals `s₀` almost surely.
  refine ⟨n, hn, V, hFV, hNe, hDE, G.withFixed hFix, hcard, hdeg,
    VoterModel.ofDeterministic (G.withFixed hFix)
      (fun v => if v ∈ s₀ then (0 : Fin 2) else 1), ?_⟩
  have hA0 := ofDeterministic_ae_opinionZeroSet (G.withFixed hFix) s₀
  set vm := VoterModel.ofDeterministic (G.withFixed hFix)
    (fun v => if v ∈ s₀ then (0 : Fin 2) else 1) with hvm
  show 0.5 ≤ vm.toAbstract.μ {ξ | vm.toAbstract.consensusTime ξ > n / (3684 * Φ (G.withFixed hFix))}
  have heq : (n : ℝ≥0∞) / (3684 * Φ (G.withFixed hFix)) =
      ENNReal.ofReal ((1 / 3684) * (n : ℝ) / (G.withFixed hFix).temporalConductance) := by
    rw [Φ_eq,
      show (1 : ℝ) / 3684 * (n : ℝ) / (G.withFixed hFix).temporalConductance
        = (n : ℝ) / (3684 * (G.withFixed hFix).temporalConductance) from by ring,
      ENNReal.ofReal_div_of_pos (mul_pos (by norm_num) hΦpos),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3684), ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]
  rw [heq]
  have h := habs vm.toAbstract hA0
  simp only [absorptionTime_eq_consensusTime vm.toAbstract
    (fixedDegrees_neighbor_nonempty hFix), floor_enat_lt_iff] at h
  -- `vm.μ` here is the `ℝ≥0`-valued `ProbabilityMeasure`; bridge from the real `.toReal` form.
  rw [← NNReal.coe_le_coe]
  rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, ENNReal.coe_toReal] at h
  push_cast at h ⊢
  linarith [h]

/-- \label{thm:lower-bound-odd-regular-averaged}
\label{thm:lower-bound-intervals}

Concrete fixed-degree form of the §4 interval lower bound. Also formalizes the
paper's general interval theorem `thm:lower-bound-intervals`: the two share the
same §4 absorption machinery (`ln_paper`/`ln_const` in `LemmaAbsorption`), and
the abstract-model restatement carries no extra content over this headline. -/
theorem lower_bound_odd_regular_averaged :
    ∀ d : ℕ, Odd d →
    ∃ (φ : ℕ → ℝ≥0) (Δ : ℕ → ℕ),
      Δ = (fun n => 24 * n / (d + 1)) ∧
      φ = (fun n => 1 / (Δ n : ℝ≥0)) ∧
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
    ∃ (V : Type) (_ : Fintype V) (_ : Nonempty V) (_ : DecidableEq V)
      (G : TemporalGraphFixedDegree V),
      Fintype.card V = n ∧
      (∀ t v, (G.snapshot t).degree v = d) ∧
      0 < φ n ∧ 0 < Δ n ∧
    (∀ t, ∀ S ∈ G.admissibleCuts,
        (φ n : ℝ) ≤ 1 / (Δ n : ℝ) *
              ∑ s ∈ Finset.Icc t (t + Δ n - 1), (G.snapshot s).setConductance S) ∧
    ∃ vm : VoterModel G 2,
      0.5 ≤ vm.μ {ξ | VoterModel.consensusTime ξ > (1 / 1837 : ℝ≥0∞) * n * Δ n / (d * φ n)} := by
  intro d hd_odd
  have hd_pos : 0 < d := hd_odd.pos
  refine ⟨fun n => 1 / ((24 * n / (d + 1) : ℕ) : ℝ≥0), fun n => 24 * n / (d + 1), rfl, rfl, ?_⟩
  intro N
  obtain ⟨n, hn, V, hFV, hNe, hDE, G, hFix, hcard, hdeg, φ_val, Δ_val, hφ_pos, hΔ_pos,
      hΔ_eq, hφ_eq, hcond, s₀, habs⟩ :=
    lower_bound_intervals_intro_fixed d hd_pos hd_odd N
  subst hΔ_eq
  subst hφ_eq
  have hφ_nnreal :
      ((1 / ((24 * n / (d + 1) : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) = 1 / ((24 * n / (d + 1) : ℕ) : ℝ) := by
    push_cast; ring
  -- Canonical witness: deterministic voter model started at `s₀` (opinion 0 on `s₀`),
  -- whose opinion-0 set equals `s₀` almost surely.
  have hA0 := ofDeterministic_ae_opinionZeroSet (G.withFixed hFix) s₀
  set vm := VoterModel.ofDeterministic (G.withFixed hFix)
    (fun v => if v ∈ s₀ then (0 : Fin 2) else 1) with hvm
  refine ⟨n, hn, V, hFV, hNe, hDE, G.withFixed hFix, hcard, hdeg,
    div_pos one_pos (by exact_mod_cast hΔ_pos),
    hΔ_pos, fun t S hS => by
      have hvol : 0 < G.volume t S := by
        rw [TemporalGraph.volume_fixed G hFix S t 0]; exact hS.1
      have hvol_le : 2 * G.volume t S ≤ G.volume t Finset.univ := by
        rw [TemporalGraph.volume_fixed G hFix S t 0,
          TemporalGraph.volume_fixed G hFix Finset.univ t 0]
        exact hS.2
      simp only [hφ_nnreal]; exact_mod_cast hcond t S hvol hvol_le,
    vm, ?_⟩
  show 0.5 ≤ vm.toAbstract.μ {ξ | vm.toAbstract.consensusTime ξ >
    (1 / 1837 : ℝ≥0∞) * n * ((24 * n / (d + 1) : ℕ) : ℝ≥0∞) /
      ((d : ℝ≥0∞) * ((1 / ((24 * n / (d + 1) : ℕ) : ℝ≥0) : ℝ≥0) : ℝ≥0∞))}
  have h := habs vm.toAbstract hA0
  simp only [absorptionTime_eq_consensusTime vm.toAbstract
    (fixedDegrees_neighbor_nonempty hFix), floor_enat_lt_iff] at h
  have hd_pos_R : (0 : ℝ) < d := by exact_mod_cast hd_pos
  have hc_eq : (1 / 1837 : ℝ≥0∞) = ENNReal.ofReal (1 / 1837 : ℝ) := by
    rw [show (1 / 1837 : ℝ≥0∞) = ((1 / 1837 : ℝ≥0) : ℝ≥0∞) from by norm_num,
      ← ENNReal.ofReal_coe_nnreal]
    norm_num
  have hφ_eq2 : ((1 / ((24 * n / (d + 1) : ℕ) : ℝ≥0) : ℝ≥0) : ℝ≥0∞) =
      ENNReal.ofReal (1 / ((24 * n / (d + 1) : ℕ) : ℝ)) := by
    rw [← ENNReal.ofReal_coe_nnreal, hφ_nnreal]
  rw [hc_eq, hφ_eq2]
  have heq : ENNReal.ofReal (1 / 1837) * (n : ℝ≥0∞) * ((24 * n / (d + 1) : ℕ) : ℝ≥0∞) /
        ((d : ℝ≥0∞) * ENNReal.ofReal (1 / ((24 * n / (d + 1) : ℕ) : ℝ))) =
      ENNReal.ofReal
        (1 / 1837 * n * (24 * n / (d + 1) : ℕ) / ((d : ℝ) * (1 / ((24 * n / (d + 1) : ℕ) : ℝ)))) := by
    have hnum : ENNReal.ofReal (1 / 1837) * (n : ℝ≥0∞) * ((24 * n / (d + 1) : ℕ) : ℝ≥0∞) =
        ENNReal.ofReal (1 / 1837 * (n : ℝ) * ((24 * n / (d + 1) : ℕ) : ℝ)) := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
    have hden : (d : ℝ≥0∞) * ENNReal.ofReal (1 / ((24 * n / (d + 1) : ℕ) : ℝ)) =
        ENNReal.ofReal ((d : ℝ) * (1 / ((24 * n / (d + 1) : ℕ) : ℝ))) := by
      rw [← ENNReal.ofReal_natCast d, ENNReal.ofReal_mul (Nat.cast_nonneg d)]
    rw [hnum, hden, ← ENNReal.ofReal_div_of_pos (mul_pos hd_pos_R (by positivity))]
  rw [heq]
  -- `vm.μ` here is the `ℝ≥0`-valued `ProbabilityMeasure`; bridge from the real `.toReal` form.
  rw [← NNReal.coe_le_coe]
  rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, ENNReal.coe_toReal] at h
  push_cast at h ⊢
  linarith [h]

end
