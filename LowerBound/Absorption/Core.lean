module

import LowerBound.ConductanceBound
import TemporalGraph.Regular
import TemporalGraph.Basic
import Mathlib.Algebra.Order.Star.Real
public import TemporalGraph.Conductance

public import LowerBound.Absorption.Defs
import LowerBound.Absorption.Martingale
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Data.ENat.Lattice
import Mathlib.MeasureTheory.Covering.Besicovitch

/-! ## Main results

`blockCount_voter_coupling`, `lower_bound_core`,
`lower_bound_absorption_sharp`, and the final
`lower_bound_3regular_voter_absorption`. -/

public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

namespace TemporalGraph.VoterProcess.LowerBound

/-- Core probabilistic bound for `lem:lower-bound-absorption`, with the sharp
horizon `T·z²/51` (the paper's statement uses the weaker `T·z²/128`; see
`lower_bound_absorption`).

Given `Γ` from `berenbrink_step_bound_pmf`, `z ≥ 20`, `T ≥ 10·Γ·k·log z`,
and initial state `halfCutLow`, the voter model on `lowerBoundGraph p` does not
absorb within `T·z²/51` steps with probability at least `0.5075`.

**Proof outline (Azuma + τ-stopping):**
1. Let `τ` be the first interval where some mixed K_{2k} clique fails to absorb.
   `P(τ ≤ N) ≤ 2N·2^{-α} ≤ 1/450` (by `perInterval_absorption_prob` + union bound,
   using ≤ 2 mixed cliques per interval and `(1/2)^α ≤ 1/z³`).
2. On `{τ > N}`, `blockCount_stopped` is a martingale with `|ΔW| ≤ 2` and `W 0 = z/2`.
3. By `azuma_inequality` (c_i = 2): `P(|W_N − z/2| ≥ z/2) ≤ 2·exp(−z²/(32N)) ≤ 2·exp(−45/32)`.
4. Combine (via `blockCount_absorbed_ub`): `P(bad) ≤ 0.4925`.
5. `P(T_abs ≥ T·z²/51) ≥ 0.5075 > 1/2`. -/
theorem blockCount_voter_coupling (Γ : ℕ) (p : Params)
    (hz : 4 ≤ p.z) (hz20 : 20 ≤ p.z)
    (hTbound : (10 : ℝ) * Γ * p.k * Real.log p.z ≤ (p.T : ℝ))
    (hstep : ∀ (t : ℕ) (T : Finset (CliqueVertex p.k)),
        (1 / 2 : ENNReal) ≤
          VoterModel.opinionProcess₂ (staticCliqueGraph p.k) t (Γ * p.k) T Finset.univ +
          VoterModel.opinionProcess₂ (staticCliqueGraph p.k) t (Γ * p.k) T ∅)
    {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (vm : TemporalGraph.VoterModelAbstract (lowerBoundGraph p) 2 Ω)
    (hA₀ : ∀ᵐ ω ∂(vm.μ : Measure Ω), vm.opinionZeroSet 0 ω = halfCutLow p) :
    ((vm.μ : Measure _) {ω | (⌈(p.T : ℝ) * (p.z : ℝ) ^ 2 / 51⌉₊ : ℕ∞) ≤
        vm.absorptionTime ω}).toReal ≥ 0.5075 := by
  -- Abbreviate the survival budget `X = T·z²/51`; the good event is `{⌈X⌉₊ ≤ τ}`,
  -- the bad event its complement `{τ < ⌈X⌉₊}` (here `τ = vm.absorptionTime`).
  set X : ℝ := (p.T : ℝ) * (p.z : ℝ) ^ 2 / 51 with hX_def
  -- Phase 1: choose N = ⌈z²/51⌉ as the slow horizon.
  set N : ℕ := Nat.ceil ((p.z : ℝ) ^ 2 / 51) with hN_def
  have hN_ge : (p.z : ℝ) ^ 2 / 51 ≤ (N : ℝ) := Nat.le_ceil _
  have hpT_nn : (0 : ℝ) ≤ (p.T : ℝ) := by exact_mod_cast Nat.zero_le _
  -- `⌈z²/51⌉ < z²/51 + 1 ≤ z²/45` needs `z² ≥ 45·51/6 = 382.5`; `z ≥ 20` gives `z² ≥ 400`.
  have hN_lt : (N : ℝ) < (p.z : ℝ) ^ 2 / 45 := by
    have hnn : (0 : ℝ) ≤ (p.z : ℝ) ^ 2 / 51 := by positivity
    have hN_bound : (N : ℝ) < (p.z : ℝ) ^ 2 / 51 + 1 := Nat.ceil_lt_add_one hnn
    have hz20R : (20 : ℝ) ≤ (p.z : ℝ) := by exact_mod_cast hz20
    linarith [hz20R, sq_nonneg ((p.z : ℝ) - 20)]
  -- Phase 2: measurability of the bad event `{τ < ⌈X⌉₊}` (ℕ∞ is discrete-measurable).
  have hmeas_bad : MeasurableSet {ω : Ω | vm.absorptionTime ω < (⌈X⌉₊ : ℕ∞)} :=
    (MeasurableSet.of_discrete (s := {x : ℕ∞ | x < (⌈X⌉₊ : ℕ∞)})).preimage
      vm.absorptionTime_measurable
  -- Phase 3: chain of inclusions and probability bound.
  -- Step A: {τ < ⌈X⌉₊} ⊆ {τ < ⌈T·N⌉₊} since X ≤ T·N.
  have hXle : X ≤ (p.T : ℝ) * (N : ℝ) := by
    rw [hX_def]
    have hmul := mul_le_mul_of_nonneg_left hN_ge hpT_nn
    linarith
  have hceil_le : (⌈X⌉₊ : ℕ∞) ≤ (⌈(p.T : ℝ) * (N : ℝ)⌉₊ : ℕ∞) := by
    exact_mod_cast Nat.ceil_mono hXle
  have hsubA : {ω : Ω | vm.absorptionTime ω < (⌈X⌉₊ : ℕ∞)}
      ⊆ {ω : Ω | vm.absorptionTime ω < (⌈(p.T : ℝ) * (N : ℝ)⌉₊ : ℕ∞)} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    exact lt_of_lt_of_le hω hceil_le
  -- Step B: {τ < ⌈T·N⌉₊} ⊆ᵐ {∃ i ≤ N, blockCount hits boundary} (a.e. permanence).
  have hsubB := absorptionTime_lt_implies_blockCount_boundary p vm N
  -- Step C: Azuma + τ-bound (deferred to `blockCount_absorbed_ub`).
  have hC := blockCount_absorbed_ub Γ p hz20 hTbound hstep vm hA₀ N hN_lt
  -- Step D: combine to get μ{bad} ≤ 1 − 0.5075.
  have h_voter_bad_le :
      ((vm.μ : Measure _) {ω : Ω | vm.absorptionTime ω < (⌈X⌉₊ : ℕ∞)}).toReal ≤ 1 - 0.5075 :=
    calc ((vm.μ : Measure _) {ω : Ω | vm.absorptionTime ω < (⌈X⌉₊ : ℕ∞)}).toReal
        ≤ ((vm.μ : Measure _) {ω | ∃ i ≤ N,
                      blockCount p vm i ω = 0 ∨ blockCount p vm i ω = p.z}).toReal :=
          ENNReal.toReal_mono (measure_ne_top _ _)
            (le_trans (measure_mono hsubA) (measure_mono_ae hsubB))
      _ ≤ 1 - 0.5075 := hC
  -- Final: good event = complement; P(good) = 1 − P(bad) ≥ 0.5075.
  have h_good_compl :
      {ω : Ω | (⌈X⌉₊ : ℕ∞) ≤ vm.absorptionTime ω}
        = {ω : Ω | vm.absorptionTime ω < (⌈X⌉₊ : ℕ∞)}ᶜ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_lt]
  rw [h_good_compl]
  rw [MeasureTheory.prob_compl_eq_one_sub hmeas_bad]
  rw [ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top]
  rw [ENNReal.toReal_one]
  linarith

/-- Core lower bound: follows from `blockCount_voter_coupling` and arithmetic. -/
private theorem lower_bound_core (Γ : ℕ) (p : Params)
    (hz20 : 20 ≤ p.z)
    (hTbound : (10 : ℝ) * Γ * p.k * Real.log p.z ≤ (p.T : ℝ))
    (hstep : ∀ (t : ℕ) (T : Finset (CliqueVertex p.k)),
        (1 / 2 : ENNReal) ≤
          VoterModel.opinionProcess₂ (staticCliqueGraph p.k) t (Γ * p.k) T Finset.univ +
          VoterModel.opinionProcess₂ (staticCliqueGraph p.k) t (Γ * p.k) T ∅)
    {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (vm : TemporalGraph.VoterModelAbstract (lowerBoundGraph p) 2 Ω)
    (hA₀ : ∀ᵐ ω ∂(vm.μ : Measure Ω), vm.opinionZeroSet 0 ω = halfCutLow p) :
    ((vm.μ : Measure _) {ω | (⌈(p.T : ℝ) * (p.z : ℝ) ^ 2 / 51⌉₊ : ℕ∞) ≤
        vm.absorptionTime ω}).toReal ≥ 1 / 2 := by
  have h := blockCount_voter_coupling Γ p (by omega) hz20 hTbound hstep vm hA₀
  linarith [show (1 : ℝ) / 2 ≤ (0.5075 : ℝ) from by norm_num]

/-- \label{lem:lower-bound-absorption}

Sharp form of `lem:lower-bound-absorption`, with survival horizon `T·z²/51`
instead of the paper's `T·z²/128` (the paper statement is recovered verbatim in
`lower_bound_absorption` below). Downstream theorems consume this sharper form.

Let `T, k, z ≥ 1` with `z` even and `z ≥ 20`, and suppose
`T ≥ 10 * Γ * k * log z`. Then there exists `s₀ ⊆ V(𝒢^{T,k,z})` such that
with probability at least `1/2`, the standard voter model on `𝒢^{T,k,z}` with
initial state `s₀` does not absorb within time `T * z² / 51` steps.
-/
theorem lower_bound_absorption_sharp :
    ∃ Γ : ℕ, 1 ≤ Γ ∧
    ∀ (p : Params),
    -- z ≥ 20
    20 ≤ p.z →
    -- T ≥ 10 * Γ * k * log z
    (10 : ℝ) * Γ * p.k * Real.log p.z ≤ (p.T : ℝ) →
    -- Conclusion: ∃ s₀, P(T_abs ≥ T·z²/51) ≥ 1/2
    ∃ s₀ : Finset (VertexSet p),
    ∀ {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω]
      (vm : TemporalGraph.VoterModelAbstract (lowerBoundGraph p) 2 Ω),
    (∀ᵐ ω ∂(vm.μ : Measure Ω), vm.opinionZeroSet 0 ω = s₀) →
    (((vm.μ : Measure _) {ω | (⌈(p.T : ℝ) * (p.z : ℝ) ^ 2 / 51⌉₊ : ℕ∞) ≤
        vm.absorptionTime ω}).toReal ≥ 1 / 2) := by
  -- Extract Γ and per-round step bound from Berenbrink's PMF theorem.
  obtain ⟨Γ, hΓ_ge1, hstep_all⟩ := berenbrink_step_bound_pmf
  refine ⟨Γ, hΓ_ge1, ?_⟩
  intro p hz20 hTbound
  -- Initial state: first z/2 blocks all hold opinion 0.
  refine ⟨halfCutLow p, ?_⟩
  intro Ω _ _ vm hA₀
  -- Instantiate hstep for the specific k = p.k.
  have hstep : ∀ (t : ℕ) (T : Finset (CliqueVertex p.k)),
      (1 / 2 : ENNReal) ≤
        VoterModel.opinionProcess₂ (staticCliqueGraph p.k) t (Γ * p.k) T Finset.univ +
        VoterModel.opinionProcess₂ (staticCliqueGraph p.k) t (Γ * p.k) T ∅ :=
    fun t T => hstep_all p.k p.hk_pos t T
  exact lower_bound_core Γ p hz20 hTbound hstep vm hA₀


/-! ### §1 introduction-level corollaries and §4 main theorem

The following three theorems are the paper's introduction-level statements
(§1) and the main §4 lower-bound theorem. They follow from
`lower_bound_absorption_sharp` via the construction `lowerBoundGraph` with
suitable parameter choices.
-/

/-- Linear dominates logarithm: if `z ≥ 25·Γ²·k²`, then `10·Γ·k·log z ≤ 4·z`.

This lets the interval lower bounds define the window parameter as `T := 4·z` (matching the
paper's `T ≔ 4z` in the proof of `thm:lower-bound-intervals`) rather than the minimal
log-threshold, so that `Δ = 3T = Θ(z) = Θ(n)` for fixed degree. The bound `10·Γ·k·log z ≤ T`
required by `lower_bound_absorption` is then verified via this lemma (using `log z ≤ 2·√z`). -/
private theorem log_le_four_z (Γ k z : ℕ) (hz_pos : 0 < z)
    (hz : 25 * Γ ^ 2 * k ^ 2 ≤ z) :
    (10 : ℝ) * Γ * k * Real.log z ≤ 4 * z := by
  have hzR : (0 : ℝ) < (z : ℝ) := by exact_mod_cast hz_pos
  have hzcast : (25 : ℝ) * (Γ : ℝ) ^ 2 * (k : ℝ) ^ 2 ≤ (z : ℝ) := by exact_mod_cast hz
  have hlog : Real.log (z : ℝ) ≤ 2 * Real.sqrt (z : ℝ) := by
    have h1 : Real.log (z : ℝ) = 2 * Real.log (Real.sqrt (z : ℝ)) := by
      rw [Real.log_sqrt hzR.le]; ring
    rw [h1]
    have h2 : Real.log (Real.sqrt (z : ℝ)) ≤ Real.sqrt (z : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hzR)
    linarith
  have hsqrt_ge : (5 : ℝ) * Γ * (k : ℝ) ≤ Real.sqrt (z : ℝ) := by
    rw [show (5 : ℝ) * Γ * (k : ℝ) = Real.sqrt ((5 * Γ * k) ^ 2) by
      rw [Real.sqrt_sq (by positivity)]]
    apply Real.sqrt_le_sqrt
    linarith [hzcast]
  have hGk : (0 : ℝ) ≤ (Γ : ℝ) * (k : ℝ) := by positivity
  have hsqrt_nn : (0 : ℝ) ≤ Real.sqrt (z : ℝ) := Real.sqrt_nonneg _
  have hsq_eq : Real.sqrt (z : ℝ) * Real.sqrt (z : ℝ) = (z : ℝ) := Real.mul_self_sqrt hzR.le
  nlinarith [mul_le_mul_of_nonneg_left hlog hGk, hsqrt_ge, hsqrt_nn, hsq_eq, hGk]

/-- Constant-parametrized form of `lower_bound_intervals`.

Identical construction and conclusion to `lower_bound_intervals`, but with the
absorption-threshold constant `1/(A·(d+1))` carried as an explicit real parameter `A`,
constrained only by `918 < A·d`. This is exactly the inequality the final `hbound` step
needs: after cancellation the goal reduces to `1836 < 2A·(2k-1)`, i.e. `918 < A·(2k-1) = A·d`
(using `d = 2k-1`; `1836 = 36·51` from the sharp absorption horizon `T·z²/51`). So `A` may
be chosen per-`d` as tight as this permits:
`lower_bound_intervals` instantiates `A = 919` (worst case `d = 1` needs `918 < A`, so `919`
is tightest there); `lower_bound_3regular_voter_absorption` instantiates `A = 307` (for `d = 3`
it needs `918 < 3·A`, i.e. `A ≥ 307`). -/
theorem lower_bound_intervals_const (A : ℝ) :
    -- Fix an odd integer d > 0 with 918 < A·d.
    ∀ (d : ℕ), 0 < d → Odd d → 918 < A * (d : ℝ) →
    -- For arbitrarily large n (explicit constant `1/(A·(d+1))`).
    ∀ (N : ℕ), ∃ (n : ℕ), N ≤ n ∧
    -- ∃ an n-vertex d-regular temporal graph 𝒢
    ∃ (V : Type) (_ : Fintype V) (_ : Nonempty V) (_ : DecidableEq V)
      (G : TemporalGraph V), G.FixedDegrees ∧
      Fintype.card V = n ∧
      (∀ (t : ℕ) (v : V), G.degree t v = d) ∧
    -- ∃ φ : ℝ_{>0}, Δ : ℕ
    ∃ (φ : ℝ) (Δ : ℕ), 0 < φ ∧ 0 < Δ ∧
    -- For all intervals I of length Δ and S with 0 < Vol(S) ≤ Vol(V)/2
    (∀ (t_start : ℕ) (S : Finset V),
        0 < G.volume t_start S →
        2 * G.volume t_start S ≤ G.volume t_start Finset.univ →
        -- (1/|I|) ∑_{t ∈ I} φ^t(S) ≥ φ
        φ ≤ (1 / (Δ : ℝ)) * ∑ t ∈ Finset.Icc t_start (t_start + Δ - 1),
              (G.snapshot t).setConductance S) ∧
    -- Conclusion: with prob ≥ 1/2, voter does not absorb within c·n·Δ/(d·φ)
    ∃ (s₀ : Finset V),
    ∀ {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω]
      (vm : TemporalGraph.VoterModelAbstract G 2 Ω),
      (∀ᵐ ω ∂(vm.μ : Measure Ω), vm.opinionZeroSet 0 ω = s₀) →
      (1 / 2 : ℝ) ≤
        ((vm.μ : Measure _) {ω | (⌊(1 / (A * ((d : ℝ) + 1))) * n * Δ / (d * φ)⌋₊ : ℕ∞) <
          vm.absorptionTime ω}).toReal := by
  -- Fix d, extracting k from the odd witness: d = 2*m + 1, so k = m + 1.
  intro d hd_pos hd_odd hA
  obtain ⟨m, hm⟩ := hd_odd
  -- k = m + 1; degree = 2*k - 1 = 2*(m+1) - 1 = 2*m + 1 = d ✓
  set k := m + 1 with hk_def
  have hk_pos : 0 < k := by omega
  intro N
  -- Extract the universal Γ from lower_bound_absorption_sharp.
  obtain ⟨Γ, hΓ, habs⟩ := lower_bound_absorption_sharp
  -- Choose z: even, ≥ max(20, N/k + 1, 25·Γ²·k²), so that n = k·z ≥ N and 4z ≥ 10Γk·log z.
  set z₀ := 2 * Nat.max (Nat.max 10 (N / k + 1)) (25 * Γ ^ 2 * k ^ 2) with hz₀_def
  have hz₀_even : 2 ∣ z₀ := ⟨_, rfl⟩
  have hz₀_twenty : 20 ≤ z₀ := by
    have h1 : 10 ≤ Nat.max 10 (N / k + 1) := Nat.le_max_left _ _
    have h2 : Nat.max 10 (N / k + 1) ≤
        Nat.max (Nat.max 10 (N / k + 1)) (25 * Γ ^ 2 * k ^ 2) := Nat.le_max_left _ _
    simp only [hz₀_def]; omega
  have hz₀_large : k * z₀ ≥ N := by
    simp only [hz₀_def]
    have h1 : N / k + 1 ≤ Nat.max (Nat.max 10 (N / k + 1)) (25 * Γ ^ 2 * k ^ 2) :=
      le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
    have hkz : N ≤ k * (N / k + 1) := by
      have := Nat.div_add_mod N k
      linarith [Nat.mod_lt N hk_pos]
    nlinarith
  have hz₀_pos : 0 < z₀ := by omega
  -- 25·Γ²·k² ≤ z₀ (used to bound 10Γk·log z₀ ≤ 4z₀ = T₀).
  have hz₀_bound : 25 * Γ ^ 2 * k ^ 2 ≤ z₀ := by
    have h1 : 25 * Γ ^ 2 * k ^ 2 ≤
        Nat.max (Nat.max 10 (N / k + 1)) (25 * Γ ^ 2 * k ^ 2) := Nat.le_max_right _ _
    simp only [hz₀_def]; omega
  -- Choose T := 4·z₀ (paper's `T ≔ 4z`), so 10Γk·log z₀ ≤ T₀ and Δ = 3T₀ = 12z₀ = Θ(n).
  set T₀ := 4 * z₀ with hT₀_def
  have hT₀_pos : 0 < T₀ := by omega
  have hT₀_bound : (10 : ℝ) * Γ * k * Real.log z₀ ≤ (T₀ : ℝ) := by
    have := log_le_four_z Γ k z₀ hz₀_pos hz₀_bound
    rw [hT₀_def]; push_cast; linarith
  -- Make z₀, T₀ opaque so downstream unification does not unfold their large bodies.
  clear_value z₀ T₀
  -- Build the Params record.
  set p : Params := ⟨T₀, k, z₀, hT₀_pos, hk_pos, hz₀_pos, hz₀_even⟩ with hp_def
  haveI hne : Nonempty (VertexSet p) := ⟨⟨⟨0, hz₀_pos⟩, ⟨0, hk_pos⟩⟩⟩
  refine ⟨k * z₀, hz₀_large, VertexSet p, inferInstance, hne, inferInstance,
          lowerBoundGraph p, lowerBoundGraph_fixedDegrees p, ?_, ?_, ?_⟩
  · -- Fintype.card (VertexSet p) = k * z₀
    exact card_vertexSet p
  · -- degree = d = 2*k - 1
    intro t v
    rw [lowerBoundGraph_degree]
    show 2 * k - 1 = d; omega
  · -- φ, Δ, conductance, absorption
    set φ_val : ℝ := 1 / (12 * z₀) with hφ_def
    set Δ_val : ℕ := 3 * T₀ with hΔ_def
    have hφ_pos : 0 < φ_val := by
      simp only [hφ_def]; positivity
    have hΔ_pos : 0 < Δ_val := by simp only [hΔ_def]; omega
    refine ⟨φ_val, Δ_val, hφ_pos, hΔ_pos, ?_, ?_⟩
    · -- Conductance bound: average conductance ≥ φ.
      intro t_start S hvol_pos hvol_le
      -- From positive volume, S is nonempty.
      have hS_nonempty : S.Nonempty := by
        by_contra hempty
        rw [Finset.not_nonempty_iff_eq_empty] at hempty
        subst hempty
        simp [TemporalGraph.volume, SimpleGraph.volume] at hvol_pos
      -- Volume of S in lowerBoundGraph equals S.card * (2*k - 1).
      have hreg : ∀ u v : VertexSet p,
          TemporalGraph.deg (lowerBoundGraph p) u =
            TemporalGraph.deg (lowerBoundGraph p) v := by
        intro u v
        simp [TemporalGraph.deg, lowerBoundGraph_degree]
      haveI hne_loc : Nonempty (VertexSet p) := hne
      have hvol_eq : ∀ (t : ℕ) (T : Finset (VertexSet p)),
          (lowerBoundGraph p).volume t T = T.card * (2 * p.k - 1) := by
        intro t T
        calc (lowerBoundGraph p).volume t T
            = (lowerBoundGraph p).volume 0 T :=
                TemporalGraph.volume_fixed (lowerBoundGraph p)
                  (lowerBoundGraph_fixedDegrees p) T t 0
          _ = T.card * TemporalGraph.deg (lowerBoundGraph p)
                (Classical.choice hne_loc) :=
                TemporalGraph.volume_eq_card_mul_deg_of_regular
                  (lowerBoundGraph p) hreg T
          _ = T.card * (2 * p.k - 1) := by
                congr 1
                simp [TemporalGraph.deg, lowerBoundGraph_degree]
      -- From `2 * Vol(S) ≤ Vol(univ)`, derive `2 * S.card ≤ Fintype.card`.
      have hS_card_le : 2 * S.card ≤ Fintype.card (VertexSet p) := by
        have h2k1_pos : 0 < 2 * p.k - 1 := by
          have := p.hk_pos; omega
        have hvolS := hvol_eq t_start S
        have hvolU := hvol_eq t_start Finset.univ
        rw [hvolS, hvolU] at hvol_le
        -- hvol_le : 2 * (S.card * (2*p.k - 1)) ≤ Finset.univ.card * (2*p.k - 1)
        have huniv_card :
            (Finset.univ : Finset (VertexSet p)).card = Fintype.card (VertexSet p) :=
          Finset.card_univ
        rw [huniv_card] at hvol_le
        -- 2 * (S.card * (2*p.k - 1)) ≤ Fintype.card (VertexSet p) * (2*p.k - 1)
        have h1 : 2 * S.card * (2 * p.k - 1) ≤
            Fintype.card (VertexSet p) * (2 * p.k - 1) := by
          have heq : 2 * (S.card * (2 * p.k - 1)) = 2 * S.card * (2 * p.k - 1) := by ring
          linarith
        exact Nat.le_of_mul_le_mul_right h1 h2k1_pos
      -- Apply the strengthened conductance bound.
      have hsum_ge : (p.T : ℝ) / (4 * p.z) ≤
          ∑ t ∈ Finset.Icc t_start (t_start + 3 * p.T - 1),
            ((lowerBoundGraph p).snapshot t).setConductance S :=
        clique_lower_bound_conductance_general p hk_pos t_start S hS_nonempty hS_card_le
      have hpT : p.T = T₀ := by simp [hp_def]
      have hpz : p.z = z₀ := by simp [hp_def]
      have hΔ_eq : Δ_val = 3 * p.T := by simp [hΔ_def, hpT]
      rw [hΔ_eq]
      have hT₀_pos_R : (0 : ℝ) < T₀ := by exact_mod_cast hT₀_pos
      have hz₀_pos_R : (0 : ℝ) < z₀ := by exact_mod_cast hz₀_pos
      have hT_pos_R : (0 : ℝ) < (p.T : ℝ) := by rw [hpT]; exact hT₀_pos_R
      have hz_pos_R : (0 : ℝ) < (p.z : ℝ) := by rw [hpz]; exact hz₀_pos_R
      rw [hφ_def]
      have hcast_3T : ((3 * p.T : ℕ) : ℝ) = 3 * (p.T : ℝ) := by push_cast; ring
      rw [hcast_3T]
      have hpz_R : (p.z : ℝ) = (z₀ : ℝ) := by exact_mod_cast hpz
      have htriv : (1 : ℝ) / (12 * (z₀ : ℝ)) ≤
          (1 / (3 * (p.T : ℝ))) * ((p.T : ℝ) / (4 * (p.z : ℝ))) := by
        rw [hpz_R]
        rw [show (1 / (3 * (p.T : ℝ))) * ((p.T : ℝ) / (4 * (z₀ : ℝ)))
              = (p.T : ℝ) / (3 * (p.T : ℝ) * (4 * (z₀ : ℝ))) by ring]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        linarith [hT_pos_R, hz₀_pos_R]
      have h_inv3T_nn : 0 ≤ (1 : ℝ) / (3 * (p.T : ℝ)) := by positivity
      have hsum_scaled :
          (1 / (3 * (p.T : ℝ))) * ((p.T : ℝ) / (4 * (p.z : ℝ))) ≤
            (1 / (3 * (p.T : ℝ))) *
              ∑ t ∈ Finset.Icc t_start (t_start + 3 * p.T - 1),
                ((lowerBoundGraph p).snapshot t).setConductance S :=
        mul_le_mul_of_nonneg_left hsum_ge h_inv3T_nn
      linarith
    · -- Absorption: use lower_bound_absorption
      obtain ⟨s₀, habs_s₀⟩ := habs p hz₀_twenty hT₀_bound
      refine ⟨s₀, ?_⟩
      intro Ω _ _ vm hA₀
      have hsurvival := habs_s₀ vm hA₀
      refine le_trans hsurvival ?_
      apply ENNReal.toReal_mono (measure_lt_top _ _).ne
      apply MeasureTheory.measure_mono
      -- Survival past `⌈T·z²/51⌉₊` implies survival past `⌊c·(k·z₀)·Δ/(d·φ)⌋₊`.
      -- Algebra: 1/(2Ak) * k*z₀ * 3T₀ / ((2k-1) * 1/(12z₀))
      --       = 36 * T₀ * z₀² / (2A * (2k-1)).
      -- Want ≤ T₀*z₀²/51, i.e. 36*51 ≤ 2A*(2k-1), i.e. 918 ≤ A*(2k-1) = A*d. Given by `hA`.
      have hd1 : (d : ℝ) + 1 = 2 * (k : ℝ) := by
        have hdm : (d : ℝ) = 2 * (m : ℝ) + 1 := by exact_mod_cast hm
        have hkm : (k : ℝ) = (m : ℝ) + 1 := by exact_mod_cast hk_def
        linarith
      have hd_eq : (d : ℝ) = 2 * (k : ℝ) - 1 := by
        have hdm : (d : ℝ) = 2 * (m : ℝ) + 1 := by exact_mod_cast hm
        have hkm : (k : ℝ) = (m : ℝ) + 1 := by exact_mod_cast hk_def
        linarith
      have hk_one : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_pos
      have h2k1_pos : (0 : ℝ) < 2 * (k : ℝ) - 1 := by linarith
      have hAk : 918 < A * (2 * (k : ℝ) - 1) := hd_eq ▸ hA
      have hA_pos : (0 : ℝ) < A := by nlinarith [hAk, h2k1_pos]
      have hbound : (1 / (A * ((d : ℝ) + 1))) * ↑(k * z₀) * ↑Δ_val / ((d : ℝ) * φ_val) <
          (p.T : ℝ) * (p.z : ℝ) ^ 2 / 51 := by
        rw [show (1 : ℝ) / (A * ((d : ℝ) + 1)) = 1 / (2 * A * (k : ℝ)) by rw [hd1]; ring]
        simp only [hp_def, hΔ_def, hφ_def]
        push_cast
        have hk' : (0 : ℝ) < k := by exact_mod_cast hk_pos
        have hz₀' : (0 : ℝ) < z₀ := by exact_mod_cast hz₀_pos
        have hT₀' : (0 : ℝ) < T₀ := by exact_mod_cast hT₀_pos
        rw [hd_eq]
        field_simp
        nlinarith [hAk, hA_pos, h2k1_pos]
      have hYnn : (0 : ℝ) ≤
          (1 / (A * ((d : ℝ) + 1))) * ↑(k * z₀) * ↑Δ_val / ((d : ℝ) * φ_val) := by
        have hd_pos_R : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd_pos
        positivity
      exact setOf_ceil_le_subset_floor_lt vm hYnn hbound


/-- Fixed-`d`, uniform-constant witness for `thm:lower-bound-odd-regular-averaged` (`\LowerBoundf`).

This is the paper's `\LowerBoundf` proof specialized to a single odd degree `d`: it applies
`lower_bound_absorption_sharp` to the construction `𝒢^{T,k,z}` with `k = (d+1)/2`, `z` even and
large, `T := 4z`, `φ := 1/(12z)`, `Δ := 3T = 12z`. The absorption threshold `T·z²/51`
dominates the target time `(1/1837)·n·Δ/(d·φ)` because the `/d` factor makes the required
inequality `1837 < 1838·k` (true for every `k ≥ 1`), which is why the constant `c = 1/1837`
is **uniform in `d`** (unlike `lower_bound_intervals`, whose `1/(919(d+1))` constant decays).
`1837` is the tightest integer constant: the binding case `d = 1, k = 1` needs `1836 < D`.

For fixed `d`, `φ = 1/(12z) = (d+1)/(24n)= Θ(1/n)` and `Δ = 12z = 12n/k = Θ(n)`, so the rates
are the paper's `Θ(1/n)`, `Θ(n)`; here `n = k·z`. The construction's window/conductance are
exposed as the **closed formulas** `Δ = 12 · (n / k)` and `φ = 1 / (12 · (n / k) : ℝ)`,
`k = (d+1)/2`, so that a caller (`lower_bound_odd_regular_averaged`) can define genuine
total functions `Δ, φ : ℕ → ℕ/ℝ` of `n` (matching the paper's `φ : ℕ → ℝ`, `Δ : ℕ → ℕ`) and know
they agree with this witness at the specific `n` produced here. -/
theorem lower_bound_intervals_intro_fixed
    -- Fix an odd integer d > 0.
    (d : ℕ) (hd_pos : 0 < d) (hd_odd : Odd d) (N : ℕ) :
    -- For arbitrarily large n (uniform constant `c = 1/1837`, with the paper's `/d` factor).
    ∃ (n : ℕ), N ≤ n ∧
    ∃ (V : Type) (_ : Fintype V) (_ : Nonempty V) (_ : DecidableEq V)
      (G : TemporalGraph V), G.FixedDegrees ∧
      Fintype.card V = n ∧
      (∀ (t : ℕ) (v : V), G.degree t v = d) ∧
    ∃ (φ : ℝ) (Δ : ℕ), 0 < φ ∧ 0 < Δ ∧
    -- Closed formulas for Δ, φ as single-nat-division functions of n, letting a caller
    -- define genuine total functions Δ, φ : ℕ → ℕ/ℝ agreeing with this witness at n.
    -- Since the witness `n = k·z` is an exact multiple of `k = (d+1)/2` and `d+1 = 2k`,
    -- `24·n/(d+1) = 24·(k·z)/(2k) = 12·z` exactly — the same window as `12·z = 3·(4z)`.
    Δ = 24 * n / (d + 1) ∧
    φ = 1 / ((24 * n / (d + 1) : ℕ) : ℝ) ∧
    (∀ (t_start : ℕ) (S : Finset V),
        0 < G.volume t_start S →
        2 * G.volume t_start S ≤ G.volume t_start Finset.univ →
        φ ≤ (1 / (Δ : ℝ)) * ∑ t ∈ Finset.Icc t_start (t_start + Δ - 1),
              (G.snapshot t).setConductance S) ∧
    ∃ (s₀ : Finset V),
    ∀ {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω]
      (vm : TemporalGraph.VoterModelAbstract G 2 Ω),
      (∀ᵐ ω ∂(vm.μ : Measure Ω), vm.opinionZeroSet 0 ω = s₀) →
      (1 / 2 : ℝ) ≤
        ((vm.μ : Measure _) {ω | (⌊(1 / 1837) * n * Δ / ((d : ℝ) * φ)⌋₊ : ℕ∞) <
          vm.absorptionTime ω}).toReal := by
  obtain ⟨m, hm⟩ := hd_odd
  set k := m + 1 with hk_def
  have hk_pos : 0 < k := by omega
  obtain ⟨Γ, hΓ, habs⟩ := lower_bound_absorption_sharp
  -- Choose z: even, ≥ max(20, N/k + 1, 25·Γ²·k²), so that n = k·z ≥ N and 4z ≥ 10Γk·log z.
  set z₀ := 2 * Nat.max (Nat.max 10 (N / k + 1)) (25 * Γ ^ 2 * k ^ 2) with hz₀_def
  have hz₀_even : 2 ∣ z₀ := ⟨_, rfl⟩
  have hz₀_twenty : 20 ≤ z₀ := by
    have h1 : 10 ≤ Nat.max 10 (N / k + 1) := Nat.le_max_left _ _
    have h2 : Nat.max 10 (N / k + 1) ≤
        Nat.max (Nat.max 10 (N / k + 1)) (25 * Γ ^ 2 * k ^ 2) := Nat.le_max_left _ _
    simp only [hz₀_def]; omega
  have hz₀_large : k * z₀ ≥ N := by
    simp only [hz₀_def]
    have h1 : N / k + 1 ≤ Nat.max (Nat.max 10 (N / k + 1)) (25 * Γ ^ 2 * k ^ 2) :=
      le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
    have hkz : N ≤ k * (N / k + 1) := by
      have := Nat.div_add_mod N k
      linarith [Nat.mod_lt N hk_pos]
    nlinarith
  have hz₀_pos : 0 < z₀ := by omega
  have hz₀_bound : 25 * Γ ^ 2 * k ^ 2 ≤ z₀ := by
    have h1 : 25 * Γ ^ 2 * k ^ 2 ≤
        Nat.max (Nat.max 10 (N / k + 1)) (25 * Γ ^ 2 * k ^ 2) := Nat.le_max_right _ _
    simp only [hz₀_def]; omega
  -- T := 4·z₀ (paper's `T ≔ 4z`), so Δ = 3T₀ = 12z₀ = Θ(n).
  set T₀ := 4 * z₀ with hT₀_def
  have hT₀_pos : 0 < T₀ := by omega
  have hT₀_bound : (10 : ℝ) * Γ * k * Real.log z₀ ≤ (T₀ : ℝ) := by
    have := log_le_four_z Γ k z₀ hz₀_pos hz₀_bound
    rw [hT₀_def]; push_cast; linarith
  clear_value z₀ T₀
  set p : Params := ⟨T₀, k, z₀, hT₀_pos, hk_pos, hz₀_pos, hz₀_even⟩ with hp_def
  haveI hne : Nonempty (VertexSet p) := ⟨⟨⟨0, hz₀_pos⟩, ⟨0, hk_pos⟩⟩⟩
  refine ⟨k * z₀, hz₀_large, VertexSet p, inferInstance, hne, inferInstance,
          lowerBoundGraph p, lowerBoundGraph_fixedDegrees p, ?_, ?_, ?_⟩
  · exact card_vertexSet p
  · intro t v
    rw [lowerBoundGraph_degree]
    show 2 * k - 1 = d; omega
  · set φ_val : ℝ := 1 / (12 * z₀) with hφ_def
    set Δ_val : ℕ := 3 * T₀ with hΔ_def
    have hφ_pos : 0 < φ_val := by simp only [hφ_def]; positivity
    have hΔ_pos : 0 < Δ_val := by simp only [hΔ_def]; omega
    have hd1 : d + 1 = 2 * k := by omega
    have h2k : 0 < 2 * k := by omega
    have hnat : 24 * (k * z₀) / (d + 1) = 12 * z₀ := by
      rw [hd1, show 24 * (k * z₀) = (2 * k) * (12 * z₀) from by ring,
        Nat.mul_div_cancel_left (12 * z₀) h2k]
    refine ⟨φ_val, Δ_val, hφ_pos, hΔ_pos, ?_, ?_, ?_, ?_⟩
    · -- Δ_val = 24·(k*z₀)/(d+1) = 12·z₀, since d+1 = 2k and 24·(k*z₀) = (2k)·(12·z₀).
      rw [hΔ_def, hT₀_def, hnat]; ring
    · -- φ_val = 1 / (24·(k*z₀)/(d+1) : ℝ) = 1/(12*z₀).
      rw [hφ_def, hnat]; push_cast; ring
    · intro t_start S hvol_pos hvol_le
      have hS_nonempty : S.Nonempty := by
        by_contra hempty
        rw [Finset.not_nonempty_iff_eq_empty] at hempty
        subst hempty
        simp [TemporalGraph.volume, SimpleGraph.volume] at hvol_pos
      have hreg : ∀ u v : VertexSet p,
          TemporalGraph.deg (lowerBoundGraph p) u =
            TemporalGraph.deg (lowerBoundGraph p) v := by
        intro u v
        simp [TemporalGraph.deg, lowerBoundGraph_degree]
      haveI hne_loc : Nonempty (VertexSet p) := hne
      have hvol_eq : ∀ (t : ℕ) (T : Finset (VertexSet p)),
          (lowerBoundGraph p).volume t T = T.card * (2 * p.k - 1) := by
        intro t T
        calc (lowerBoundGraph p).volume t T
            = (lowerBoundGraph p).volume 0 T :=
                TemporalGraph.volume_fixed (lowerBoundGraph p)
                  (lowerBoundGraph_fixedDegrees p) T t 0
          _ = T.card * TemporalGraph.deg (lowerBoundGraph p)
                (Classical.choice hne_loc) :=
                TemporalGraph.volume_eq_card_mul_deg_of_regular
                  (lowerBoundGraph p) hreg T
          _ = T.card * (2 * p.k - 1) := by
                congr 1
                simp [TemporalGraph.deg, lowerBoundGraph_degree]
      have hS_card_le : 2 * S.card ≤ Fintype.card (VertexSet p) := by
        have h2k1_pos : 0 < 2 * p.k - 1 := by
          have := p.hk_pos; omega
        have hvolS := hvol_eq t_start S
        have hvolU := hvol_eq t_start Finset.univ
        rw [hvolS, hvolU] at hvol_le
        have huniv_card :
            (Finset.univ : Finset (VertexSet p)).card = Fintype.card (VertexSet p) :=
          Finset.card_univ
        rw [huniv_card] at hvol_le
        have h1 : 2 * S.card * (2 * p.k - 1) ≤
            Fintype.card (VertexSet p) * (2 * p.k - 1) := by
          have heq : 2 * (S.card * (2 * p.k - 1)) = 2 * S.card * (2 * p.k - 1) := by ring
          linarith
        exact Nat.le_of_mul_le_mul_right h1 h2k1_pos
      have hsum_ge : (p.T : ℝ) / (4 * p.z) ≤
          ∑ t ∈ Finset.Icc t_start (t_start + 3 * p.T - 1),
            ((lowerBoundGraph p).snapshot t).setConductance S :=
        clique_lower_bound_conductance_general p hk_pos t_start S hS_nonempty hS_card_le
      have hpT : p.T = T₀ := by simp [hp_def]
      have hpz : p.z = z₀ := by simp [hp_def]
      have hΔ_eq : Δ_val = 3 * p.T := by simp [hΔ_def, hpT]
      rw [hΔ_eq]
      have hT₀_pos_R : (0 : ℝ) < T₀ := by exact_mod_cast hT₀_pos
      have hz₀_pos_R : (0 : ℝ) < z₀ := by exact_mod_cast hz₀_pos
      have hT_pos_R : (0 : ℝ) < (p.T : ℝ) := by rw [hpT]; exact hT₀_pos_R
      have hz_pos_R : (0 : ℝ) < (p.z : ℝ) := by rw [hpz]; exact hz₀_pos_R
      rw [hφ_def]
      have hcast_3T : ((3 * p.T : ℕ) : ℝ) = 3 * (p.T : ℝ) := by push_cast; ring
      rw [hcast_3T]
      have hpz_R : (p.z : ℝ) = (z₀ : ℝ) := by exact_mod_cast hpz
      have htriv : (1 : ℝ) / (12 * (z₀ : ℝ)) ≤
          (1 / (3 * (p.T : ℝ))) * ((p.T : ℝ) / (4 * (p.z : ℝ))) := by
        rw [hpz_R]
        rw [show (1 / (3 * (p.T : ℝ))) * ((p.T : ℝ) / (4 * (z₀ : ℝ)))
              = (p.T : ℝ) / (3 * (p.T : ℝ) * (4 * (z₀ : ℝ))) by ring]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        linarith [hT_pos_R, hz₀_pos_R]
      have h_inv3T_nn : 0 ≤ (1 : ℝ) / (3 * (p.T : ℝ)) := by positivity
      have hsum_scaled :
          (1 / (3 * (p.T : ℝ))) * ((p.T : ℝ) / (4 * (p.z : ℝ))) ≤
            (1 / (3 * (p.T : ℝ))) *
              ∑ t ∈ Finset.Icc t_start (t_start + 3 * p.T - 1),
                ((lowerBoundGraph p).snapshot t).setConductance S :=
        mul_le_mul_of_nonneg_left hsum_ge h_inv3T_nn
      linarith
    · obtain ⟨s₀, habs_s₀⟩ := habs p hz₀_twenty hT₀_bound
      refine ⟨s₀, ?_⟩
      intro Ω _ _ vm hA₀
      have hsurvival := habs_s₀ vm hA₀
      refine le_trans hsurvival ?_
      apply ENNReal.toReal_mono (measure_lt_top _ _).ne
      apply MeasureTheory.measure_mono
      -- Survival past `⌈T·z²/51⌉₊` implies survival past `⌊(1/1837)·(k·z₀)·Δ/(d·φ)⌋₊`.
      -- Algebra: (1/1837)·k·z₀·3T₀/((2k-1)·(1/(12z₀))) = 36·k·T₀·z₀²/(1837·(2k-1));
      -- want < T₀·z₀²/51, i.e. 1836·k < 1837·(2k-1), i.e. 1837 < 1838·k (true for k ≥ 1).
      have hbound : (1 / 1837 : ℝ) * ↑(k * z₀) * ↑Δ_val / ((d : ℝ) * φ_val) <
          (p.T : ℝ) * (p.z : ℝ) ^ 2 / 51 := by
        simp only [hp_def, hΔ_def, hφ_def]
        push_cast
        have hz₀' : (0 : ℝ) < z₀ := by exact_mod_cast hz₀_pos
        have hT₀' : (0 : ℝ) < T₀ := by exact_mod_cast hT₀_pos
        have hd_eq : (d : ℝ) = 2 * (k : ℝ) - 1 := by
          have hdm : (d : ℝ) = 2 * (m : ℝ) + 1 := by exact_mod_cast hm
          have hkm : (k : ℝ) = (m : ℝ) + 1 := by exact_mod_cast hk_def
          linarith
        rw [hd_eq]
        have hk_one : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_pos
        field_simp
        rw [div_lt_iff₀ (by linarith : (0 : ℝ) < (k : ℝ) * 2 - 1)]
        linarith [hk_one, hT₀', hz₀']
      exact setOf_ceil_le_subset_floor_lt vm (by positivity) hbound

/-! ### Helpers for T10 (`lower_bound_3regular_voter_absorption`) -/


/-- For a `d`-regular temporal graph with `d ≥ 1` and at least 2 vertices,
the singleton `{v}` for any vertex `v` is in `admissibleCuts G`. -/
private theorem singleton_mem_admissibleCuts_of_regular
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraph V) (d : ℕ) (hd : 0 < d)
    (hdeg : ∀ (t : ℕ) (v : V), G.degree t v = d)
    (hcard : 2 ≤ Fintype.card V) (v : V) :
    ({v} : Finset V) ∈ TemporalGraph.admissibleCuts G := by
  have hdeg0 : ∀ u : V, (G.snapshot 0).degree u = d := by
    intro u
    have := hdeg 0 u
    simpa [TemporalGraph.degree] using this
  have hdeg_pos : ∀ u : V, 0 < (G.snapshot 0).degree u := by
    intro u; rw [hdeg0]; exact hd
  rw [TemporalGraph.mem_admissibleCuts_iff_relativeVolume G hdeg_pos]
  refine ⟨Finset.singleton_nonempty _, ?_, ?_, ?_⟩
  · intro hsing
    have hcard_eq : ({v} : Finset V).card = (Finset.univ : Finset V).card := by rw [hsing]
    rw [Finset.card_singleton, Finset.card_univ] at hcard_eq
    omega
  · unfold TemporalGraph.relativeVolume SimpleGraph.relativeVolume
    refine div_pos ?_ ?_
    · exact_mod_cast SimpleGraph.volume_pos_of_nonempty
        (G := G.snapshot 0) (Finset.singleton_nonempty v) hdeg_pos
    · exact_mod_cast SimpleGraph.volume_univ_pos (G := G.snapshot 0) hdeg_pos
  · unfold TemporalGraph.relativeVolume SimpleGraph.relativeVolume
    have hvol_sing : (G.snapshot 0).volume {v} = d := by
      unfold SimpleGraph.volume
      rw [Finset.sum_singleton, hdeg0]
    have hvol_univ : (G.snapshot 0).volume Finset.univ = Fintype.card V * d := by
      unfold SimpleGraph.volume
      rw [Finset.sum_congr rfl (fun u _ => hdeg0 u),
          Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rw [hvol_sing, hvol_univ]
    have hcard_pos : 0 < Fintype.card V := by omega
    have hcard_Q_pos : (0 : ℚ) < (Fintype.card V : ℚ) := by exact_mod_cast hcard_pos
    have hd_Q_pos : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd
    rw [Nat.cast_mul, div_le_iff₀ (by positivity)]
    have hcard_Q : ((2 : ℕ) : ℚ) ≤ (Fintype.card V : ℚ) := by exact_mod_cast hcard
    push_cast at hcard_Q
    -- Goal: ↑d ≤ 1/2 * (↑(Fintype.card V) * ↑d). With cardV ≥ 2 and d ≥ 1:
    linarith [hcard_Q, hd_Q_pos,
      mul_nonneg (by linarith : (0 : ℚ) ≤ (Fintype.card V : ℚ) - 2) (le_of_lt hd_Q_pos)]

/-- Lower bound on `setConductanceOnInterval` from the T41 average hypothesis,
for admissible cuts. -/
private theorem setConductanceOnInterval_ge_of_avg
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraphFixedDegree V) (Δ : ℕ) (hΔ : 1 ≤ Δ) (φ : ℝ)
    (hcond : ∀ (t_start : ℕ) (S : Finset V),
        0 < (G.snapshot t_start).volume S →
        2 * (G.snapshot t_start).volume S ≤ (G.snapshot t_start).volume Finset.univ →
        φ ≤ (1 / (Δ : ℝ)) * ∑ t ∈ Finset.Icc t_start (t_start + Δ - 1),
              (G.snapshot t).setConductance S)
    (t_start : ℕ) (S : Finset V) (hS : S ∈ TemporalGraph.admissibleCuts G.toTemporalGraph) :
    (Δ : ℝ) * φ ≤ G.setConductanceOnInterval t_start (t_start + Δ - 1) S := by
  obtain ⟨hvol_pos0, hvol_le0⟩ := hS
  have hvol_pos : 0 < (G.snapshot t_start).volume S := by
    rw [G.volume_fixed S t_start 0]; exact hvol_pos0
  have hvol_le_nat :
      2 * (G.snapshot t_start).volume S ≤ (G.snapshot t_start).volume Finset.univ := by
    rw [G.volume_fixed S t_start 0,
        G.volume_fixed Finset.univ t_start 0]
    exact hvol_le0
  have havg := hcond t_start S hvol_pos hvol_le_nat
  have hΔ_pos_R : (0 : ℝ) < (Δ : ℝ) := by exact_mod_cast hΔ
  have hmul := mul_le_mul_of_nonneg_left havg (le_of_lt hΔ_pos_R)
  have hcalc : (Δ : ℝ) * ((1 / (Δ : ℝ)) * ∑ t ∈ Finset.Icc t_start (t_start + Δ - 1),
              (G.snapshot t).setConductance S) =
      ∑ t ∈ Finset.Icc t_start (t_start + Δ - 1), (G.snapshot t).setConductance S := by
    field_simp
  rw [hcalc] at hmul
  exact hmul

/-- Pigeonhole: if `(Δ : ℝ) * φ ≤ ∑_{t ∈ Icc t₁ (t₁ + Δ - 1)} (G.snapshot t).setConductance S`
for every admissible cut, then there exists `t` in the window with
`φ ≤ (G.snapshot t).setConductance S`. Combined with `setConductanceOnInterval_ge_of_avg`,
this yields the window guarantee directly from T41's average hypothesis. -/
private theorem hasWindowGuarantee_of_avg
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraphFixedDegree V) (Δ : ℕ) (hΔ : 1 ≤ Δ) (φ : ℝ)
    (hcond : ∀ (t_start : ℕ) (S : Finset V),
        0 < (G.snapshot t_start).volume S →
        2 * (G.snapshot t_start).volume S ≤ (G.snapshot t_start).volume Finset.univ →
        φ ≤ (1 / (Δ : ℝ)) * ∑ t ∈ Finset.Icc t_start (t_start + Δ - 1),
              (G.snapshot t).setConductance S) :
    TemporalGraph.hasWindowGuarantee G.toTemporalGraph φ Δ := by
  intro t₁ S hS
  have hsum_ge :
      (Δ : ℝ) * φ ≤ G.setConductanceOnInterval t₁ (t₁ + Δ - 1) S :=
    setConductanceOnInterval_ge_of_avg G Δ hΔ φ hcond t₁ S hS
  have hIcc_ne : (Finset.Icc t₁ (t₁ + Δ - 1)).Nonempty :=
    Finset.nonempty_Icc.mpr (by omega)
  have hcard_Icc : (Finset.Icc t₁ (t₁ + Δ - 1)).card = Δ := by
    rw [Nat.card_Icc]; omega
  have hsum_const : ∑ _t ∈ Finset.Icc t₁ (t₁ + Δ - 1), φ = (Δ : ℝ) * φ := by
    rw [Finset.sum_const, hcard_Icc, nsmul_eq_mul]
  have hsum_le :
      ∑ t ∈ Finset.Icc t₁ (t₁ + Δ - 1), φ
        ≤ ∑ t ∈ Finset.Icc t₁ (t₁ + Δ - 1), (G.snapshot t).setConductance S := by
    rw [hsum_const]
    exact hsum_ge
  obtain ⟨t, ht, hφt⟩ :=
    Finset.exists_le_of_sum_le (f := fun _ => φ)
      (g := fun t => (G.snapshot t).setConductance S) hIcc_ne hsum_le
  exact ⟨t, ht, hφt⟩

/-- Two-opinion witness for `thm:lower-bound-3regular`; the paper label
now lives on the general-model version `lower_bound_3regular`
(in `VoterModel/Spec/TheoremLowerBoundGeneral.lean`), which lifts this via
`VoterModel.toTwoOpinion`.

There exist arbitrarily large `n`-vertex `3`-regular temporal graphs `𝒢`
and a constant `c` such that, with probability at least `1/2`, the standard
voter model on `𝒢` does not absorb within time `c · n / Φ(𝒢)` steps.

(The paper writes the constant inconsistently as `c` and `C`; we use `c`
throughout. Per the paper's `\llm` annotation, "There exists ... graphs"
is a subject-verb mismatch; we render with `∀ N, ∃ n ≥ N`.)

Proof: apply `lower_bound_intervals_const` (T41) with `A = 307`, `d = 3`. Since only
`d = 3` (hence `k = 2`) is needed here, the tightest constant is `A = 307` (the binding
inequality `918 < A·d = 3A` needs `A ≥ 307`), sharper than the uniform-over-all-`d`
value `919` used by `lower_bound_intervals`. T41 produces concrete
`φ_val, Δ_val` such that the average conductance is `≥ φ_val` on every window
of length `Δ_val`. Pigeonholing the average gives a `hasWindowGuarantee` witness
`(φ_val, Δ_val)`. Applying L104
(`temporalConductance_ge_div_of_hasWindowGuarantee`) converts this to
`φ_val / Δ_val ≤ Φ(𝒢)`, which combined with T41's strict absorption inequality
yields T10.
-/
theorem lower_bound_3regular_voter_absorption :
    -- For arbitrarily large n (explicit constant `1/3684 = (1/1228)/3`).
    ∀ (N : ℕ), ∃ (n : ℕ), N ≤ n ∧
    -- ∃ an n-vertex 3-regular temporal graph 𝒢
    ∃ (V : Type) (_ : Fintype V) (_ : Nonempty V) (_ : DecidableEq V)
      (G : TemporalGraph V), G.FixedDegrees ∧
      Fintype.card V = n ∧
      (∀ (t : ℕ) (v : V), G.degree t v = 3) ∧
      0 < TemporalGraph.temporalConductance G ∧
    -- Conclusion: with prob ≥ 1/2, voter does not absorb within c·n/Φ(𝒢)
    ∃ (s₀ : Finset V),
    ∀ {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω]
      (vm : TemporalGraph.VoterModelAbstract G 2 Ω),
      (∀ᵐ ω ∂(vm.μ : Measure Ω), vm.opinionZeroSet 0 ω = s₀) →
      (1 / 2 : ℝ) ≤
        ((vm.μ : Measure _) {ω | (⌊(1 / 3684) * n / TemporalGraph.temporalConductance G⌋₊ : ℕ∞) <
          vm.absorptionTime ω}).toReal := by
  classical
  -- A = 307 is the tightest constant for d = 3 (needs 918 < 3·A, i.e. A ≥ 307).
  have hT41 := lower_bound_intervals_const 307 3 (by decide) (by decide) (by norm_num)
  intro N
  obtain ⟨n, hNn, V, hFV, hNeV, hDeqV, G, hFix, hcard, hdeg3, φ_val, Δ_val,
          hφ_pos, hΔ_pos, hcond_avg, s₀, habs⟩ := hT41 N
  set c₀ : ℝ := 1 / (307 * (((3 : ℕ) : ℝ) + 1)) with hc₀_def
  have hc₀_pos : 0 < c₀ := by rw [hc₀_def]; norm_num
  letI : Fintype V := hFV
  letI : Nonempty V := hNeV
  letI : DecidableEq V := hDeqV
  -- `Φ(𝒢) > 0`: the window guarantee `(φ_val, Δ_val)` from T41 lower-bounds it by `φ_val/Δ_val > 0`.
  have hΔ_ge_one : 1 ≤ Δ_val := hΔ_pos
  have hcard_ge : 2 ≤ Fintype.card V := by
    obtain ⟨v₀⟩ := hNeV
    have hdeg_v0 : (G.snapshot 0).degree v₀ = 3 := by
      have := hdeg3 0 v₀
      simpa [TemporalGraph.degree] using this
    have hneighbor_card : ((G.snapshot 0).neighborFinset v₀).card = 3 := hdeg_v0
    have hdisj : Disjoint ((G.snapshot 0).neighborFinset v₀) {v₀} := by
      rw [Finset.disjoint_singleton_right]
      simp [SimpleGraph.mem_neighborFinset, SimpleGraph.irrefl]
    have hcard_un :
        (((G.snapshot 0).neighborFinset v₀) ∪ {v₀}).card =
          ((G.snapshot 0).neighborFinset v₀).card + 1 := by
      rw [Finset.card_union_of_disjoint hdisj, Finset.card_singleton]
    have hsub : (((G.snapshot 0).neighborFinset v₀) ∪ {v₀}).card ≤ Fintype.card V := by
      rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ _)
    rw [hcard_un, hneighbor_card] at hsub
    omega
  have hΦ_pos : 0 < TemporalGraph.temporalConductance G := by
    obtain ⟨v₀⟩ := hNeV
    have hcuts_ne : (TemporalGraph.admissibleCuts G).Nonempty :=
      ⟨{v₀}, singleton_mem_admissibleCuts_of_regular G 3 (by norm_num) hdeg3 hcard_ge v₀⟩
    have hwin : TemporalGraph.hasWindowGuarantee G φ_val Δ_val :=
      hasWindowGuarantee_of_avg (TemporalGraph.withFixed G hFix) Δ_val hΔ_ge_one φ_val hcond_avg
    have hΦ_ge : φ_val / (Δ_val : ℝ) ≤ TemporalGraph.temporalConductance G :=
      TemporalGraph.temporalConductance_ge_div_of_hasWindowGuarantee
        G hcuts_ne hΔ_ge_one hwin
    have hΔ_pos_R : (0 : ℝ) < (Δ_val : ℝ) := by exact_mod_cast hΔ_pos
    exact lt_of_lt_of_le (div_pos hφ_pos hΔ_pos_R) hΦ_ge
  refine ⟨n, hNn, V, hFV, hNeV, hDeqV, G, hFix, hcard, hdeg3, hΦ_pos, s₀, ?_⟩
  intro Ω _ _ vm hA₀
  have hT41_concl := habs vm hA₀
  -- Survival past `⌊c₀·n·Δ/(3φ)⌋₊` implies survival past `⌊(c₀/3)·n/Φ̃⌋₊`, since
  -- `(c₀/3)·n/Φ̃ ≤ c₀·n·Δ/(3φ)` (from `φ/Δ ≤ Φ̃`).
  refine le_trans hT41_concl ?_
  apply ENNReal.toReal_mono (measure_lt_top _ _).ne
  apply MeasureTheory.measure_mono
  -- The explicit `1/3684` in the goal equals `c₀/3`; rewrite so `hY21` (below) applies.
  rw [show (1 : ℝ) / 3684 = c₀ / 3 by rw [hc₀_def]; norm_num]
  have hY21 : c₀ / 3 * (n : ℝ) / TemporalGraph.temporalConductance G ≤
      c₀ * (n : ℝ) * (Δ_val : ℝ) / (((3 : ℕ) : ℝ) * φ_val) := by
    have hn_pos_nat : 0 < n := by rw [← hcard]; exact Fintype.card_pos
    have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
    have hΔ_pos_R : (0 : ℝ) < (Δ_val : ℝ) := by exact_mod_cast hΔ_pos
    have hΔ_ge_one : 1 ≤ Δ_val := hΔ_pos
    have hΦ_nn : 0 ≤ TemporalGraph.temporalConductance G :=
      TemporalGraph.temporalConductance_nonneg G
    have hT41_rhs_pos : 0 < c₀ * n * Δ_val / (3 * φ_val) := by positivity
    rcases eq_or_lt_of_le hΦ_nn with hΦ0 | hΦpos
    · have h0 : c₀ / 3 * (n : ℝ) / TemporalGraph.temporalConductance G = 0 := by
        rw [← hΦ0]; simp
      rw [h0]; linarith
    · -- Need ≥ 2 vertices to build an admissible cut. For 3-regular: card ≥ 4.
      have hcard_ge : 2 ≤ Fintype.card V := by
        obtain ⟨v₀⟩ := hNeV
        have hdeg_v0 : (G.snapshot 0).degree v₀ = 3 := by
          have := hdeg3 0 v₀
          simpa [TemporalGraph.degree] using this
        have hneighbor_card : ((G.snapshot 0).neighborFinset v₀).card = 3 := hdeg_v0
        have hdisj : Disjoint ((G.snapshot 0).neighborFinset v₀) {v₀} := by
          rw [Finset.disjoint_singleton_right]
          simp [SimpleGraph.mem_neighborFinset, SimpleGraph.irrefl]
        have hcard_un :
            (((G.snapshot 0).neighborFinset v₀) ∪ {v₀}).card =
              ((G.snapshot 0).neighborFinset v₀).card + 1 := by
          rw [Finset.card_union_of_disjoint hdisj, Finset.card_singleton]
        have hsub : (((G.snapshot 0).neighborFinset v₀) ∪ {v₀}).card ≤ Fintype.card V := by
          rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ _)
        rw [hcard_un, hneighbor_card] at hsub
        omega
      obtain ⟨v₀⟩ := hNeV
      have hcuts_ne : (TemporalGraph.admissibleCuts G).Nonempty :=
        ⟨{v₀}, singleton_mem_admissibleCuts_of_regular G 3 (by norm_num) hdeg3 hcard_ge v₀⟩
      -- Window guarantee from T41's average hypothesis via pigeonhole.
      have hwin : TemporalGraph.hasWindowGuarantee G φ_val Δ_val :=
        hasWindowGuarantee_of_avg (TemporalGraph.withFixed G hFix) Δ_val hΔ_ge_one φ_val hcond_avg
      -- L104: φ / Δ ≤ Φ̃(𝒢).
      have hΦ_ge : φ_val / (Δ_val : ℝ) ≤ TemporalGraph.temporalConductance G :=
        TemporalGraph.temporalConductance_ge_div_of_hasWindowGuarantee
          G hcuts_ne hΔ_ge_one hwin
      -- Algebra: c·n/Φ̃ ≤ c₀·n·Δ/(3φ). With c = c₀/3:
      have hφ_pos_R : (0 : ℝ) < φ_val := hφ_pos
      have h_div_pos : (0 : ℝ) < φ_val / (Δ_val : ℝ) := div_pos hφ_pos_R hΔ_pos_R
      -- Reciprocal: 1/Φ̃ ≤ Δ/φ.
      have h_inv_le : 1 / TemporalGraph.temporalConductance G ≤ (Δ_val : ℝ) / φ_val := by
        rw [div_le_div_iff₀ hΦpos hφ_pos_R]
        have := hΦ_ge
        rw [div_le_iff₀ hΔ_pos_R] at this
        linarith
      have hcn_nn : 0 ≤ (c₀ / 3 : ℝ) * n := by positivity
      have hLHS_le : (c₀ / 3 : ℝ) * n / TemporalGraph.temporalConductance G ≤
          (c₀ / 3) * n * ((Δ_val : ℝ) / φ_val) := by
        rw [div_eq_mul_one_div]
        exact mul_le_mul_of_nonneg_left h_inv_le hcn_nn
      have hRHS_eq : (c₀ / 3 : ℝ) * n * ((Δ_val : ℝ) / φ_val) =
          c₀ * n * Δ_val / (3 * φ_val) := by
        field_simp
      linarith
  exact setOf_floor_lt_mono vm hY21


end TemporalGraph.VoterProcess.LowerBound
