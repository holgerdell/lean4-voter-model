module

public import UpperBound.LogMartingale
import UpperBound.IntervalChain
import VoterProcess.Expectation
import Mathlib.Algebra.Order.Star.Real
public import TemporalGraph.Conductance

public import UpperBound.PotentialDecrease.StableInterval
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Covering.Besicovitch
import TemporalGraph.Basic
import UpperBound.PotentialDecrease.Drift


@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

namespace VoterModel

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]

/-! ## Main results

Per-fiber drift and dispatch theorems (`*_on_fiber`): stable/unstable psi- and
chi-drift, exit-time, calendar-window good step, and the combined drift dispatch. -/

/-- \label{lem:psi-down-drift-stable-from-IsStableInterval-on-fiber}

**L90 — Stable dispatch wrapper for L68 Case 2.**

Combines the fiber-relative Case-2 ψ-bound
(`potential_decrease_stable_interval_combined_unconditional_on_fiber`) and the L77 χ-bound under the
`Case2Hypotheses` bundle, yielding the integrated stable drift bound on the
fiber `F`. Specifically, for `F ⊆ {ω | T_j ω = t_j ∧ vm.S t_j ω = s_j}`
with `vol(t_j, s_j) < 8 · vol(0, s_0)` and a good-step witness for `φ_j > 0`,

  `∫_F (α · Δψ + Δχ) dvm.μ ≤ -(φ_j / 2048) · (vm.μ F).toReal,`

where `α = √vol(0, s_0) / d_min` and `Δψ = ψ(T_{j+1}) − ψ(T_j)`,
`Δχ = χ(T_{j+1}, S_{T_{j+1}}) − χ(T_j, S_{T_j})`.

**Constant derivation.** The Case-2 ψ-bound gives
`∫_F Δψ ≤ -(d_min·φ_j)/(192·√6·ψ(t_j,s_j)) · μ(F)`.
Multiplying by `α = √vol(0,s_0)/d_min` gives
`α · (d_min·φ_j)/(192·√6·ψ(t_j,s_j)) = φ_j·√vol(0,s_0)/(192·√6·√vol(t_j,s_j))`.
Since `vol(t_j,s_j) < 8·vol(0,s_0)`, this is `> φ_j/(192·√6·√8) = φ_j/(192·√48) ≈ φ_j/1330`,
which is `≥ φ_j/2048`. Combining with L77's non-positive χ bound yields the
target `-(φ_j/2048)·μ(F)`.

**Note on hypotheses.** Per advisor analysis, the L84/L85 infrastructure
(for L84 and `Case2Hypotheses.stable`) requires GLOBAL stability, which the
L68 caller (holding only F-restricted information via `D27`) cannot supply
without a broader refactor. L90 therefore consumes the raw Case-2 bundle
(`hgood_step`, `hedge_sum_small`, `hC2`) directly; the bridge from
`IsStableInterval`-on-F + `hcond` to that bundle is deferred to the L68
caller (a residual blocker on the L84/L85 interface, not on L90 itself). -/
theorem psi_down_drift_stable_from_IsStableInterval_on_fiber
    {Ω : Type*} [MeasurableSpace Ω]
    (G : TemporalGraphFixedDegree V)
    (vm : G.VoterModelAbstract 2 Ω)
    (d_min : ℕ) (hd : d_min = G.minDegreeAt 0) (hd_pos : 0 < d_min)
    -- Initial set s_0, current fiber state s_j ≠ ∅, realized time t_j
    (s_0 : Finset V) (hs_0_ne : s_0.Nonempty)
    (s_j : Finset V) (hs_j_ne : s_j.Nonempty)
    (t_j : ℕ)
    -- Embedded chain parameters
    (Δ : ℕ → ℕ) (hΔ_pos : ∀ k, 1 ≤ Δ k) (j : ℕ)
    -- Volume sub-fiber bound (from L68's indicator-TRUE selector at index j)
    (hvol_lt : ((G.snapshot 0).volume s_j : ℝ) <
      8 * ((G.snapshot 0).volume s_0 : ℝ))
    -- Fiber F: measurable in ℱ_{t_j}, with T_j = t_j and S_{t_j} = s_j on F
    (F : Set Ω)
    (hF_meas : MeasurableSet[vm.ℱ t_j] F)
    (hF_T : ∀ ω ∈ F, embeddedChainTime G.toTemporalGraph vm Δ j ω = t_j)
    (hF_S : ∀ ω ∈ F, vm.S t_j ω = s_j)
    -- t_j is within the cap for the (j+1)-th embedded interval (paper-tight cap)
    (hT_cap : t_j ≤ (∑ k ∈ Finset.range (j + 1), Δ k) - 1)
    -- L76 bundle: φ_j > 0, good-step witness, hedge-sum upper bound, hC2
    (φ_j : ℝ) (hφ_j_pos : 0 < φ_j)
    (hgood_step : ∃ t', t_j ≤ t' ∧ t' ≤ (∑ k ∈ Finset.range (j + 1), Δ k) - 1 ∧
        (G.edgesBetween t' s_j (Finset.univ \ s_j) : ℝ) ≥
          φ_j * ((G.snapshot t_j).volume s_j : ℝ))
    -- F-restricted hedge-sum UB at threshold (1/8)·V/(1/φ_j) (matches the
    -- parameter choice in `potential_decrease_stable_interval_combined_unconditional_on_fiber`).
    (hedge_sum_small : ∀ᵐ ω ∂((vm.μ : Measure Ω).restrict F),
      ((vm.μ : Measure Ω)[fun ω' => ∑ k ∈ Finset.Icc t_j (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω' - 1),
        (vm.cutS k ω' : ℝ) | vm.ℱ t_j]) ω
        ≤ (1 / 8 : ℝ) * ((G.snapshot t_j).volume s_j : ℝ) / (1 / φ_j))
    -- Case2Hypotheses bundle, F-restricted to the L90 fiber `F`.
    (hC2 : ∀ t', t_j ≤ t' → t' ≤ (∑ k ∈ Finset.range (j + 1), Δ k) - 1 →
        Case2Hypotheses G.toTemporalGraph vm s_j t_j (embeddedChainTime G.toTemporalGraph vm Δ (j + 1)) t' φ_j F) :
    -- Conclusion: integrated stable combined drift ≤ -(φ_j/2048)·μ(F).toReal
    ∫ ω in F,
      ((Real.sqrt ((G.snapshot 0).volume s_0 : ℝ) / d_min)
          * (vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω
              - vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω)
        + (G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
              (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω)
          - G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ j ω)
              (vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω)))
      ∂vm.μ ≤ -(φ_j / 2048) * ((vm.μ : Measure Ω) F).toReal := by
  classical
  haveI hprob : IsProbabilityMeasure (vm.μ : Measure Ω) := inferInstance
  -- Top-level measurability of F.
  have hF_meas_top : MeasurableSet F := vm.ℱ.le t_j _ hF_meas
  -- Abbreviation: α := √vol(0, s_0)/d_min ≥ 0.
  set α : ℝ := Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) / d_min with hα_def
  have hd_pos_real : (0 : ℝ) < d_min := by exact_mod_cast hd_pos
  have hα_nn : (0 : ℝ) ≤ α :=
    div_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _)
  -- Volume of s_0 is positive (s_0 nonempty + FixedDegrees + min degree pos, but we only need ≥ 0
  -- in fact strict via s_0 nonempty using SimpleGraph.volume_pos style argument).
  have hVol_s0_pos : (0 : ℝ) < TemporalGraph.volume G.toTemporalGraph 0 s_0 := by
    have hv_pos_nat : 0 < TemporalGraph.volume G.toTemporalGraph 0 s_0 := by
      obtain ⟨v, hv⟩ := hs_0_ne
      have hd_le : d_min ≤ G.degree 0 v := by
        rw [hd, G.minDegreeAt_eq 0 0]; exact G.minDegreeAt_le_degree 0 v
      have hv_deg_pos : 0 < G.degree 0 v := lt_of_lt_of_le hd_pos hd_le
      have h_le_vol : G.degree 0 v ≤ TemporalGraph.volume G.toTemporalGraph 0 s_0 := by
        unfold TemporalGraph.volume SimpleGraph.volume
        exact Finset.single_le_sum (f := fun u => G.degree 0 u)
          (fun u _ => Nat.zero_le _) hv
      exact lt_of_lt_of_le hv_deg_pos h_le_vol
    exact_mod_cast hv_pos_nat
  -- Volume of s_j is positive (similarly).
  have hVol_sj_pos : (0 : ℝ) < TemporalGraph.volume G.toTemporalGraph t_j s_j := by
    have hv_pos_nat : 0 < TemporalGraph.volume G.toTemporalGraph t_j s_j := by
      obtain ⟨v, hv⟩ := hs_j_ne
      have hd_le : d_min ≤ G.degree t_j v := by
        rw [hd, G.minDegreeAt_eq 0 t_j]; exact G.minDegreeAt_le_degree t_j v
      have hv_deg_pos : 0 < G.degree t_j v := lt_of_lt_of_le hd_pos hd_le
      have h_le_vol : G.degree t_j v ≤ TemporalGraph.volume G.toTemporalGraph t_j s_j := by
        unfold TemporalGraph.volume SimpleGraph.volume
        exact Finset.single_le_sum (f := fun u => G.degree t_j u)
          (fun u _ => Nat.zero_le _) hv
      exact lt_of_lt_of_le hv_deg_pos h_le_vol
    exact_mod_cast hv_pos_nat
  -- ψ(t_j, s_j) = potential G.toTemporalGraph t_j s_j > 0.
  have hψ_sj_pos : (0 : ℝ) < TemporalGraph.potential G.toTemporalGraph t_j s_j := by
    unfold TemporalGraph.potential
    exact Real.sqrt_pos.mpr hVol_sj_pos
  -- Apply the fiber-relative Case-2 ψ-drift bound (L79).
  have h_L79 := potential_decrease_stable_interval_combined_unconditional_on_fiber
    G vm s_j hs_j_ne t_j Δ j F
    hF_meas hF_T hF_S φ_j hφ_j_pos hT_cap hgood_step hedge_sum_small hC2
  -- Normalize its RHS spelling to `TemporalGraph.potential`.
  have h_L79' : ∀ᵐ ω ∂((vm.μ : Measure Ω).restrict F),
      ((vm.μ : Measure Ω)[fun ω' => vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω') ω' -
        TemporalGraph.potential G.toTemporalGraph t_j s_j | vm.ℱ t_j]) ω
        ≤ -((G.minDegreeAt 0 : ℝ) * φ_j) /
            (192 * Real.sqrt 6 * TemporalGraph.potential G.toTemporalGraph t_j s_j) := h_L79
  -- Apply L77 (chi_down_drift_voter_on_fiber).
  have hL77 := chi_down_drift_voter_on_fiber G vm s_j t_j Δ hΔ_pos j F
    hF_meas hF_T hF_S hT_cap
  -- ψ(T_j ω) ω = potential G.toTemporalGraph t_j s_j and χ(T_j ω, S_{T_j ω}) = chiPotential G.toTemporalGraph t_j s_j on F.
  have hψ_Tj_eq_on_F : ∀ ω ∈ F, vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω =
      TemporalGraph.potential G.toTemporalGraph t_j s_j := by
    intro ω hω
    show TemporalGraph.potential G.toTemporalGraph (embeddedChainTime G.toTemporalGraph vm Δ j ω)
        (vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω) = _
    rw [hF_T ω hω, hF_S ω hω]
  have hχ_Tj_eq_on_F : ∀ ω ∈ F,
      G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ j ω)
        (vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω)
        = G.chiPotential t_j s_j := by
    intro ω hω
    rw [hF_T ω hω, hF_S ω hω]
  -- Integrand rewrite on F.
  have hinteg_eq_on_F : ∀ ω ∈ F,
      ((α : ℝ) * (vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω
              - vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω)
          + (G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
                (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω)
            - G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ j ω)
                (vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω))) =
      (α * (vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω
              - TemporalGraph.potential G.toTemporalGraph t_j s_j)
        + (G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
              (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω)
            - G.chiPotential t_j s_j)) := by
    intro ω hω
    rw [hψ_Tj_eq_on_F ω hω, hχ_Tj_eq_on_F ω hω]
  -- Rewrite the LHS integral via setIntegral_congr_fun.
  rw [setIntegral_congr_fun hF_meas_top (fun ω hω => hinteg_eq_on_F ω hω)]
  -- Universe-bound Vu for integrability.
  set Vu : ℕ := TemporalGraph.volume G.toTemporalGraph 0 (Finset.univ : Finset V) with hVu_def
  have hVol_le_univ : ∀ t S, TemporalGraph.volume G.toTemporalGraph t S ≤ Vu := by
    intro t S
    have h1 : TemporalGraph.volume G.toTemporalGraph t S ≤ TemporalGraph.volume G.toTemporalGraph t Finset.univ := by
      unfold TemporalGraph.volume SimpleGraph.volume
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have h2 : TemporalGraph.volume G.toTemporalGraph t Finset.univ = Vu :=
      G.volume_fixed _ _ _
    exact h1.trans_eq h2
  -- Stopping-time scaffolding (for measurability of ψ(T_{j+1}), χ(T_{j+1},·)).
  have hS_meas_ℱ : ∀ t, @Measurable Ω (Finset V) (vm.ℱ t) ⊤ (vm.S t) := fun t =>
    (measurable_of_countable (fun A => VoterModel.minoritySet G.toTemporalGraph t A)).comp
      (vm.A_stronglyAdapted t).measurable
  have hT_stop : ∀ k,
      IsStoppingTime vm.ℱ (fun ω => (embeddedChainTime G.toTemporalGraph vm Δ k ω : ℕ∞)) := fun k =>
    embeddedChainTime_isStoppingTime G.toTemporalGraph vm Δ hS_meas_ℱ k
  have hT_meas : ∀ k, Measurable (embeddedChainTime G.toTemporalGraph vm Δ k) := by
    intro k s _
    rw [show (embeddedChainTime G.toTemporalGraph vm Δ k) ⁻¹' s =
        ⋃ u ∈ s, {w | embeddedChainTime G.toTemporalGraph vm Δ k w = u} from by ext ω; simp]
    refine MeasurableSet.biUnion (Set.to_countable s) (fun u _ => ?_)
    have heq2 : {w : Ω | embeddedChainTime G.toTemporalGraph vm Δ k w = u} =
        {w | (embeddedChainTime G.toTemporalGraph vm Δ k w : ℕ∞) = ↑u} := by
      ext w
      exact ⟨fun heq => by exact_mod_cast heq, fun heq => by exact_mod_cast heq⟩
    rw [heq2]; exact vm.ℱ.le u _ ((hT_stop k).measurableSet_eq u)
  have hψE_meas : Measurable (fun ω => vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω) := by
    intro S hS
    rw [show (fun ω => vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω) ⁻¹' S =
        ⋃ t : ℕ, (embeddedChainTime G.toTemporalGraph vm Δ (j + 1)) ⁻¹' {t} ∩ (vm.psiS t) ⁻¹' S from by
      ext ω
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_singleton_iff]
      refine ⟨fun h => ⟨embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω, rfl, h⟩, ?_⟩
      rintro ⟨t, heq, hp⟩
      show vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω ∈ S
      rw [heq]; exact hp]
    refine MeasurableSet.iUnion (fun t => ?_)
    have hpsi_meas : Measurable (vm.psiS t) := by
      have h1 : Measurable (fun ω => (TemporalGraph.volume G.toTemporalGraph t (vm.S t ω) : ℝ)) := by
        have hvol_fn : Measurable
            (fun s : Finset V => (TemporalGraph.volume G.toTemporalGraph t s : ℝ)) :=
          measurable_of_countable _
        have hS_t : Measurable (vm.S t) := fun S hS => vm.ℱ.le t _ ((hS_meas_ℱ t) hS)
        exact hvol_fn.comp hS_t
      show Measurable (fun ω => Real.sqrt (TemporalGraph.volume G.toTemporalGraph t (vm.S t ω) : ℝ))
      exact Real.continuous_sqrt.measurable.comp h1
    exact (hT_meas (j + 1) (measurableSet_singleton _)).inter (hpsi_meas hS)
  have hχE_meas : Measurable (fun ω => G.chiPotential
      (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω)) := by
    intro S hS
    rw [show (fun ω => G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
        (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω)) ⁻¹' S =
        ⋃ t : ℕ, (embeddedChainTime G.toTemporalGraph vm Δ (j + 1)) ⁻¹' {t} ∩
          (fun ω => G.chiPotential t (vm.S t ω)) ⁻¹' S from by
      ext ω
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_singleton_iff]
      refine ⟨fun h => ⟨embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω, rfl, h⟩, ?_⟩
      rintro ⟨t, heq, hp⟩
      show G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
        (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω) ∈ S
      rw [heq]; exact hp]
    refine MeasurableSet.iUnion (fun t => ?_)
    have hchi_meas : Measurable (fun ω => G.chiPotential t (vm.S t ω)) := by
      have hchi_fn : Measurable (fun s : Finset V => G.chiPotential t s) :=
        measurable_of_countable _
      have hS_t : Measurable (vm.S t) := fun S hS => vm.ℱ.le t _ ((hS_meas_ℱ t) hS)
      exact hchi_fn.comp hS_t
    exact (hT_meas (j + 1) (measurableSet_singleton _)).inter (hchi_meas hS)
  -- Integrability of (ψ(T_{j+1}) − ψ(t_j,s_j)) and (χ(T_{j+1}, S_{T_{j+1}}) − χ(t_j,s_j)).
  have hψ_int : Integrable
      (fun ω => vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω -
        TemporalGraph.potential G.toTemporalGraph t_j s_j) vm.μ := by
    refine MeasureTheory.Integrable.of_bound
      (C := Real.sqrt (Vu : ℝ) + TemporalGraph.potential G.toTemporalGraph t_j s_j)
      (hψE_meas.sub_const _).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    have h_nn : 0 ≤ vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω :=
      Real.sqrt_nonneg _
    have h_bnd : vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω ≤ Real.sqrt (Vu : ℝ) := by
      show TemporalGraph.potential G.toTemporalGraph _ _ ≤ _
      apply Real.sqrt_le_sqrt
      exact_mod_cast hVol_le_univ _ _
    have hpot_nn : 0 ≤ TemporalGraph.potential G.toTemporalGraph t_j s_j := Real.sqrt_nonneg _
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · linarith [Real.sqrt_nonneg ((Vu : ℝ))]
    · linarith
  have hχ_int : Integrable
      (fun ω => G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
          (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω) -
        G.chiPotential t_j s_j) vm.μ := by
    have hVol_nn : (0 : ℝ) ≤ (Vu : ℝ) := Nat.cast_nonneg _
    refine MeasureTheory.Integrable.of_bound
      (C := Real.log (1 + (Vu : ℝ)) + G.chiPotential t_j s_j)
      (hχE_meas.sub_const _).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    have h_nn : 0 ≤ G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
        (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω) := by
      unfold TemporalGraphFixedDegree.chiPotential TemporalGraph.chiPotential
      apply Real.log_nonneg
      have h0 : (0 : ℝ) ≤ (TemporalGraph.volume G.toTemporalGraph (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
          (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω) : ℝ) := Nat.cast_nonneg _
      linarith
    have h_bnd : G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
        (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω) ≤ Real.log (1 + (Vu : ℝ)) := by
      unfold TemporalGraphFixedDegree.chiPotential TemporalGraph.chiPotential
      have h1 : (0 : ℝ) < 1 + (TemporalGraph.volume G.toTemporalGraph (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
          (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω) : ℝ) := by
        have h0 : (0 : ℝ) ≤ (TemporalGraph.volume G.toTemporalGraph (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
            (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω) : ℝ) := Nat.cast_nonneg _
        linarith
      apply Real.log_le_log h1
      have h := hVol_le_univ (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
        (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω)
      have h2 : (TemporalGraph.volume G.toTemporalGraph (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
          (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω) : ℝ) ≤ (Vu : ℝ) := by
        exact_mod_cast h
      linarith
    have hchi_pot_nn : 0 ≤ G.chiPotential t_j s_j := by
      unfold TemporalGraphFixedDegree.chiPotential TemporalGraph.chiPotential
      apply Real.log_nonneg
      have : (0 : ℝ) ≤ (TemporalGraph.volume G.toTemporalGraph t_j s_j : ℝ) := Nat.cast_nonneg _
      linarith
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · have hlog_nn : 0 ≤ Real.log (1 + (Vu : ℝ)) :=
        Real.log_nonneg (by linarith)
      linarith
    · linarith
  -- Split the integral by linearity.
  have hint_eq : ∫ ω in F,
      (α * (vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω
              - TemporalGraph.potential G.toTemporalGraph t_j s_j)
        + (G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
              (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω)
            - G.chiPotential t_j s_j)) ∂vm.μ =
      α * ∫ ω in F,
        (vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω -
          TemporalGraph.potential G.toTemporalGraph t_j s_j) ∂vm.μ +
      ∫ ω in F,
        (G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
            (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω) -
          G.chiPotential t_j s_j) ∂vm.μ := by
    rw [integral_add (hψ_int.const_mul _).integrableOn hχ_int.integrableOn]
    rw [integral_const_mul]
  rw [hint_eq]
  -- Use the Case-2 ψ-bound (scaled by α) and L77 to get the bound.
  set K_ψ : ℝ := -((G.minDegreeAt 0 : ℝ) * φ_j)
        / (192 * Real.sqrt 6 * TemporalGraph.potential G.toTemporalGraph t_j s_j) with hKψ_def
  -- Case-2 ψ-bound: ∫_F (ψ - potential) ≤ K_ψ · μ(F).toReal.
  -- L77: ∫_F (χ - chiPotential) ≤ 0.
  -- Goal: α · ∫_F Δψ + ∫_F Δχ ≤ -(φ_j/2048) · μ(F).toReal.
  -- It suffices to show α · K_ψ ≤ -(φ_j/2048), i.e.
  --   α · d_min · φ_j / (192·√6·ψ(s_j)) ≥ φ_j/2048.
  set μF : ℝ := ((vm.μ : Measure Ω) F).toReal with hμF_def
  have hμF_nn : 0 ≤ μF := ENNReal.toReal_nonneg
  -- ∫_F (ψ - potential) = ∫_F E[ψ - potential | ℱ_{t_j}] ≤ K_ψ · μF.
  have hψ_setInt_le : ∫ ω in F,
      (vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω -
        TemporalGraph.potential G.toTemporalGraph t_j s_j) ∂vm.μ ≤ K_ψ * μF := by
    have h_setInt :=
      setIntegral_condExp (μ := vm.μ) (hm := vm.ℱ.le t_j) (f :=
          fun ω' => vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω') ω' -
            TemporalGraph.potential G.toTemporalGraph t_j s_j)
        (hf := hψ_int) (hs := hF_meas)
    rw [← h_setInt]
    have hbnd : ∫ ω in F,
        ((vm.μ : Measure Ω)[fun ω' => vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω') ω' -
            TemporalGraph.potential G.toTemporalGraph t_j s_j | vm.ℱ t_j]) ω ∂vm.μ ≤
        ∫ _ω in F, K_ψ ∂vm.μ :=
      setIntegral_mono_ae_restrict
        (integrable_condExp.integrableOn) (integrable_const _).integrableOn h_L79'
    have hrhs : ∫ _ω in F, K_ψ ∂vm.μ = K_ψ * μF := by
      rw [setIntegral_const]
      show ((vm.μ : Measure Ω) F).toReal • K_ψ = K_ψ * μF
      rw [smul_eq_mul, mul_comm, hμF_def]
    linarith [hrhs ▸ hbnd]
  -- Derive φ_j · √vol(s_0) / (192 · √6 · √vol(s_j)) ≥ φ_j / 2048.
  -- α · (G.minDegreeAt 0 : ℝ) · φ_j / (192·√6·ψ) = (G.minDegreeAt 0 · √vol(0,s_0)/d_min) · φ_j /(192·√6·ψ)
  --                                     = φ_j · √vol(0,s_0) / (192·√6·√vol(t_j,s_j))  [as d_min = G.minDegreeAt 0]
  have hd_eq : (G.minDegreeAt 0 : ℝ) = (d_min : ℝ) := by rw [hd]
  -- The "α-scaled" L76 bound. We show:
  --   α · K_ψ ≤ -(φ_j/2048).
  -- Equivalently: φ_j · √vol(0,s_0) / (192·√6·√vol(t_j,s_j)) ≥ φ_j/2048.
  -- Volume is time-independent under FixedDegrees; transport hvol_lt to time t_j.
  have hvol_lt_tj : (TemporalGraph.volume G.toTemporalGraph t_j s_j : ℝ) <
      8 * (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) := by
    rw [show (TemporalGraph.volume G.toTemporalGraph t_j s_j : ℝ) = (TemporalGraph.volume G.toTemporalGraph 0 s_j : ℝ) from by
      exact_mod_cast (G.volume_fixed s_j t_j 0)]
    exact hvol_lt
  have hsqrt_lt : Real.sqrt (TemporalGraph.volume G.toTemporalGraph t_j s_j : ℝ) <
      Real.sqrt (8 * (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ)) :=
    Real.sqrt_lt_sqrt (Nat.cast_nonneg _) hvol_lt_tj
  have hsqrt8_eq : Real.sqrt (8 * (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ)) =
      Real.sqrt 8 * Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8)]
  -- Threshold inequality
  have hα_K_le : α * K_ψ ≤ -(φ_j / 2048) := by
    -- K_ψ = -d_min·φ_j / (192·√6·ψ(s_j)).
    -- α·K_ψ = -√vol(s_0)/d_min · d_min·φ_j / (192·√6·ψ(s_j)) = -φ_j·√vol(s_0)/(192·√6·ψ(s_j)).
    have hsqrt6_pos : (0 : ℝ) < Real.sqrt 6 := Real.sqrt_pos.mpr (by norm_num)
    have hsqrt8_pos : (0 : ℝ) < Real.sqrt 8 := Real.sqrt_pos.mpr (by norm_num)
    have hsqrt_s0_pos : (0 : ℝ) < Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) :=
      Real.sqrt_pos.mpr hVol_s0_pos
    have hsqrt_sj_pos : (0 : ℝ) < Real.sqrt (TemporalGraph.volume G.toTemporalGraph t_j s_j : ℝ) :=
      Real.sqrt_pos.mpr hVol_sj_pos
    have hψ_sj_eq : TemporalGraph.potential G.toTemporalGraph t_j s_j =
        Real.sqrt (TemporalGraph.volume G.toTemporalGraph t_j s_j : ℝ) := rfl
    -- Simplify α·K_ψ = -φ_j·√vol(s_0) / (192·√6·√vol(t_j,s_j))
    have hd_ne : (d_min : ℝ) ≠ 0 := ne_of_gt hd_pos_real
    have hα_K : α * K_ψ = -(φ_j * Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ)) /
        (192 * Real.sqrt 6 * Real.sqrt (TemporalGraph.volume G.toTemporalGraph t_j s_j : ℝ)) := by
      rw [hα_def, hKψ_def, hψ_sj_eq, hd_eq]
      field_simp
    rw [hα_K]
    -- Want: -(φ_j · √vol(0,s_0)) / (192·√6·√vol(t_j,s_j)) ≤ -(φ_j/2048)
    -- ↔ φ_j · √vol(0,s_0) / (192·√6·√vol(t_j,s_j)) ≥ φ_j/2048.
    -- Since φ_j > 0, divide both sides by φ_j: √vol(0,s_0) / (192·√6·√vol(t_j,s_j)) ≥ 1/2048
    -- ↔ 2048 · √vol(0,s_0) ≥ 192·√6·√vol(t_j,s_j)
    -- ↔ √vol(t_j,s_j) ≤ 2048/(192·√6) · √vol(0,s_0) = (125/3√6) · √vol(0,s_0).
    -- And we have √vol(t_j,s_j) < √8 · √vol(0,s_0) ≈ 2.828·√vol(0,s_0).
    -- Since 125/(3·√6) = 125/(3·√6) ≈ 17.01 > 2.828, the bound holds with margin.
    rw [neg_div, neg_le_neg_iff]
    -- Now: φ_j / 2048 ≤ (φ_j · √vol(0,s_0)) / (192 · √6 · √vol(t_j,s_j))
    have hdenom_pos : (0 : ℝ) < 192 * Real.sqrt 6 *
        Real.sqrt (TemporalGraph.volume G.toTemporalGraph t_j s_j : ℝ) := by
      have : (0 : ℝ) < 192 * Real.sqrt 6 := by positivity
      exact mul_pos this hsqrt_sj_pos
    rw [le_div_iff₀ hdenom_pos]
    -- Now: (φ_j / 2048) * (192·√6·√vol(t_j,s_j)) ≤ φ_j · √vol(0,s_0)
    -- ↔ φ_j · (192·√6·√vol(t_j,s_j) / 2048) ≤ φ_j · √vol(0,s_0)
    -- ↔ √vol(t_j,s_j) · 192·√6/2048 ≤ √vol(0,s_0)
    -- ↔ √vol(t_j,s_j) ≤ (2048/(192·√6)) · √vol(0,s_0)
    -- We have √vol(t_j,s_j) < √8·√vol(0,s_0), so suffices √8 ≤ 2048/(192·√6), i.e.
    -- 192·√6·√8 ≤ 2048, i.e. 192·√48 ≤ 2048.
    -- √48 < 7, so 192·√48 < 1344 < 2048. ✓
    have h48_lt : Real.sqrt 48 ≤ 7 := by
      have h49 : (7 : ℝ) = Real.sqrt 49 := by
        rw [show (49 : ℝ) = 7 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 7)]
      rw [h49]
      exact Real.sqrt_le_sqrt (by norm_num)
    have hsqrt6_mul_sqrt8 : Real.sqrt 6 * Real.sqrt 8 = Real.sqrt 48 := by
      rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 6)]; norm_num
    -- Show √vol(t_j,s_j) ≤ √8 · √vol(0,s_0) using hsqrt_lt and hsqrt8_eq.
    have hsqrt_sj_le : Real.sqrt (TemporalGraph.volume G.toTemporalGraph t_j s_j : ℝ) ≤
        Real.sqrt 8 * Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) := by
      rw [← hsqrt8_eq]; exact le_of_lt hsqrt_lt
    -- Final inequality: φ_j · √vol(0,s_0) ≥ (φ_j / 2048) · (192·√6·√vol(t_j,s_j))
    -- Multiply hsqrt_sj_le by (φ_j / 2048) · 192 · √6 (nonneg) on the left:
    -- (φ_j/2048) · 192 · √6 · √vol(t_j,s_j) ≤ (φ_j/2048) · 192 · √6 · √8 · √vol(0,s_0)
    -- =  (φ_j/2048) · 192 · √48 · √vol(0,s_0)
    -- ≤ (φ_j/2048) · 192 · 7 · √vol(0,s_0) = (1344/2048) · φ_j · √vol(0,s_0)
    -- ≤ φ_j · √vol(0,s_0). ✓
    have hφ_4000_nn : 0 ≤ φ_j / 2048 := by positivity
    have h_step1 : (φ_j / 2048) * (192 * Real.sqrt 6 *
          Real.sqrt (TemporalGraph.volume G.toTemporalGraph t_j s_j : ℝ)) ≤
        (φ_j / 2048) * (192 * Real.sqrt 6 *
          (Real.sqrt 8 * Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ hφ_4000_nn
      apply mul_le_mul_of_nonneg_left hsqrt_sj_le
      positivity
    have h_step1' : (φ_j / 2048) * (192 * Real.sqrt 6 *
          (Real.sqrt 8 * Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ))) =
        (φ_j / 2048) * (192 * Real.sqrt 48 *
          Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ)) := by
      rw [show 192 * Real.sqrt 6 * (Real.sqrt 8 *
          Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ)) =
        192 * (Real.sqrt 6 * Real.sqrt 8) *
          Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) from by ring,
        hsqrt6_mul_sqrt8]
    rw [h_step1'] at h_step1
    refine le_trans h_step1 ?_
    -- Want: (φ_j/2048)·192·√48·√vol(s_0) ≤ φ_j·√vol(s_0)
    -- Since √48 ≤ 7: (φ_j/2048)·192·√48·√vol(s_0) ≤ (φ_j/2048)·96·7·√vol(s_0)
    --              = (1344·φ_j / 2048)·√vol(s_0) ≤ φ_j·√vol(s_0).
    have h_step2 : (φ_j / 2048) * (192 * Real.sqrt 48 *
          Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ)) ≤
        (φ_j / 2048) * (192 * 7 *
          Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hφ_4000_nn
      apply mul_le_mul_of_nonneg_right
      · apply mul_le_mul_of_nonneg_left h48_lt; norm_num
      · exact le_of_lt hsqrt_s0_pos
    refine le_trans h_step2 ?_
    -- (φ_j/2048)·1344·√vol(s_0) ≤ φ_j·√vol(s_0). Equivalent to 1344/2048 ≤ 1.
    have : (φ_j / 2048) * (192 * 7 *
          Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ)) =
        (φ_j * Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ)) * (1344 / 2048) := by ring
    rw [this]
    linarith only [mul_nonneg hφ_j_pos.le hsqrt_s0_pos.le]
  -- Conclude: α · ∫_F Δψ + ∫_F Δχ ≤ α · K_ψ · μF + 0 ≤ -(φ_j/2048) · μF.
  have hL76' : α * ∫ ω in F,
      (vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω -
        TemporalGraph.potential G.toTemporalGraph t_j s_j) ∂vm.μ ≤ α * (K_ψ * μF) :=
    mul_le_mul_of_nonneg_left hψ_setInt_le hα_nn
  -- Sum the ψ- and χ-bounds.
  have hbound : α * ∫ ω in F,
      (vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω -
        TemporalGraph.potential G.toTemporalGraph t_j s_j) ∂vm.μ +
      ∫ ω in F,
        (G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
            (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω) -
          G.chiPotential t_j s_j) ∂vm.μ ≤
      α * (K_ψ * μF) + 0 := by
    exact add_le_add hL76' hL77
  refine le_trans hbound ?_
  -- α · K_ψ · μF + 0 ≤ -(φ_j/2048) · μF.
  rw [add_zero]
  rw [show α * (K_ψ * μF) = (α * K_ψ) * μF from by ring]
  exact mul_le_mul_of_nonneg_right hα_K_le hμF_nn

/-- \label{lem:psi-chi-combined-drift-case1-from-largeEdgeSum-on-fiber}

**L96 — Stable Case 1 dispatch wrapper for L68; mirrors L90 but uses L81
directly via the *large edge sum* (paper L30) hypothesis.**

For the indicator-TRUE sub-fiber `F_T` of L68 (where the `Pind` indicator
triggers) and a hypothesis `hLarge` that the expected edge-sum over the
embedded interval exceeds `(1/8)·Vol(t_j, s_j)` (the paper's lower bound from
`lem:prob-good-event`), this lemma proves the integrated stable drift bound

  `∫_{F_T} (α · Δψ + Δχ) dvm.μ ≤ -(φ_j / 2048) · (vm.μ F_T).toReal,`

where `α = √vol(0, s_0) / d_min`, `Δψ = ψ(T_{j+1}) − ψ(T_j)`,
`Δχ = χ(T_{j+1}, S_{T_{j+1}}) − χ(T_j, S_{T_j})`.

**Why this exists.** L93 was originally meant to produce the *upper* bound on
the edge sum (`hedge_sum_small`) from F-restricted stability, then feed L76.
But the paper's `lem:prob-good-event` (≡ L30, L82 in Lean) proves a
**lower** bound on the edge sum in the stable case. The architectural fix
mirrors the paper: L92 dispatches stable into Case 1 (this lemma; uses the
LB `hLarge` directly via L81) and Case 2 (the L90 path, where `¬hLarge` is
literally `hedge_sum_small`).

**Constant derivation.** L81 with `μ_param = 1, Δ = 8/φ_j`, and the
large-edge-sum hypothesis (LB form `> (1/8)·Vol/(1/φ_j) = φ_j·Vol/8`) gives
`E[Δψ | ℱ_{t_j}] ≤ -(1·d_min) / (24·√6·(8/φ_j)·ψ(t_j, s_j))
                       = -d_min·φ_j / (192·√6·ψ(t_j, s_j))` a.e. on `F_T`.
Multiplying by `α = √vol(0,s_0)/d_min` and using `vol(t_j,s_j) < 8·vol(0,s_0)`
gives `α · K_ψ_L81 ≤ -(φ_j / 2048)` (since `192·√48 < 192·7 = 1344 < 2048`).
Combined with L77's non-positive χ bound, the integrated bound follows.

**Depends on:** L77 (`chi_down_drift_voter_on_fiber`), L81
(`potential_decrease_stable_interval_large_on_fiber`). -/
theorem psi_chi_combined_drift_case1_from_largeEdgeSum_on_fiber
    {Ω : Type*} [MeasurableSpace Ω]
    (G : TemporalGraphFixedDegree V)
    (vm : G.VoterModelAbstract 2 Ω)
    (d_min : ℕ) (hd : d_min = G.minDegreeAt 0) (hd_pos : 0 < d_min)
    -- Initial set s_0, current fiber state s_j ≠ ∅, realized time t_j
    (s_0 : Finset V) (hs_0_ne : s_0.Nonempty)
    (s_j : Finset V) (hs_j_ne : s_j.Nonempty)
    (t_j : ℕ)
    -- Embedded chain parameters
    (Δ : ℕ → ℕ) (hΔ_pos : ∀ k, 1 ≤ Δ k) (j : ℕ)
    -- Volume sub-fiber bound (from L68's indicator-TRUE selector at index j)
    (hvol_lt : ((G.snapshot 0).volume s_j : ℝ) <
      8 * ((G.snapshot 0).volume s_0 : ℝ))
    -- Fiber F_T: measurable in ℱ_{t_j}, with T_j = t_j and S_{t_j} = s_j on F_T
    (F_T : Set Ω)
    (hF_T_meas : MeasurableSet[vm.ℱ t_j] F_T)
    (hF_T_eq : ∀ ω ∈ F_T, embeddedChainTime G.toTemporalGraph vm Δ j ω = t_j)
    (hF_S_eq : ∀ ω ∈ F_T, vm.S t_j ω = s_j)
    -- t_j is within the cap for the (j+1)-th embedded interval (paper-tight cap)
    (hT_cap : t_j ≤ (∑ k ∈ Finset.range (j + 1), Δ k) - 1)
    -- Window guarantee parameter φ_j ∈ (0, 1]
    (φ_j : ℝ) (hφ_j_pos : 0 < φ_j)
    -- F_T-restricted "large edge sum" hypothesis (paper L30's LB conclusion;
    -- threshold (1/8) to align with the Case 2 negation):
    -- E[Σ_{k ∈ [t_j, T_{j+1}-1]} cutS k | ℱ_{t_j}] ω > (1/8)·Vol(t_j, s_j)/(1/φ_j)
    -- = (φ_j/8)·Vol(t_j, s_j), a.e. on μ.restrict F_T.
    (hLarge : ∀ᵐ ω ∂((vm.μ : Measure Ω).restrict F_T),
      ((vm.μ : Measure Ω)[fun ω' => ∑ k ∈ Finset.Icc t_j (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω' - 1),
        (vm.cutS k ω' : ℝ) | vm.ℱ t_j]) ω
        > (1 / 8 : ℝ) * ((G.snapshot t_j).volume s_j : ℝ) / (1 / φ_j)) :
    -- Conclusion: integrated Case 1 stable combined drift ≤ -(φ_j/2048)·μ(F_T).toReal
    ∫ ω in F_T,
      ((Real.sqrt ((G.snapshot 0).volume s_0 : ℝ) / d_min)
          * (vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω
              - vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω)
        + (G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
              (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω)
          - G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ j ω)
              (vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω)))
      ∂vm.μ ≤ -(φ_j / 2048) * ((vm.μ : Measure Ω) F_T).toReal := by
  classical
  haveI hprob : IsProbabilityMeasure (vm.μ : Measure Ω) := inferInstance
  -- Top-level measurability of F_T.
  have hF_T_meas_top : MeasurableSet F_T := vm.ℱ.le t_j _ hF_T_meas
  -- Abbreviation: α := √vol(0, s_0)/d_min ≥ 0.
  set α : ℝ := Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) / d_min with hα_def
  have hd_pos_real : (0 : ℝ) < d_min := by exact_mod_cast hd_pos
  have hα_nn : (0 : ℝ) ≤ α :=
    div_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _)
  -- Volume of s_0 is positive (s_0 nonempty + FixedDegrees + min degree pos).
  have hVol_s0_pos : (0 : ℝ) < TemporalGraph.volume G.toTemporalGraph 0 s_0 := by
    have hv_pos_nat : 0 < TemporalGraph.volume G.toTemporalGraph 0 s_0 := by
      obtain ⟨v, hv⟩ := hs_0_ne
      have hd_le : d_min ≤ G.degree 0 v := by
        rw [hd, G.minDegreeAt_eq 0 0]; exact G.minDegreeAt_le_degree 0 v
      have hv_deg_pos : 0 < G.degree 0 v := lt_of_lt_of_le hd_pos hd_le
      have h_le_vol : G.degree 0 v ≤ TemporalGraph.volume G.toTemporalGraph 0 s_0 := by
        unfold TemporalGraph.volume SimpleGraph.volume
        exact Finset.single_le_sum (f := fun u => G.degree 0 u)
          (fun u _ => Nat.zero_le _) hv
      exact lt_of_lt_of_le hv_deg_pos h_le_vol
    exact_mod_cast hv_pos_nat
  -- Volume of s_j is positive (similarly).
  have hVol_sj_pos : (0 : ℝ) < TemporalGraph.volume G.toTemporalGraph t_j s_j := by
    have hv_pos_nat : 0 < TemporalGraph.volume G.toTemporalGraph t_j s_j := by
      obtain ⟨v, hv⟩ := hs_j_ne
      have hd_le : d_min ≤ G.degree t_j v := by
        rw [hd, G.minDegreeAt_eq 0 t_j]; exact G.minDegreeAt_le_degree t_j v
      have hv_deg_pos : 0 < G.degree t_j v := lt_of_lt_of_le hd_pos hd_le
      have h_le_vol : G.degree t_j v ≤ TemporalGraph.volume G.toTemporalGraph t_j s_j := by
        unfold TemporalGraph.volume SimpleGraph.volume
        exact Finset.single_le_sum (f := fun u => G.degree t_j u)
          (fun u _ => Nat.zero_le _) hv
      exact lt_of_lt_of_le hv_deg_pos h_le_vol
    exact_mod_cast hv_pos_nat
  -- ψ(t_j, s_j) > 0.
  have hψ_sj_pos : (0 : ℝ) < TemporalGraph.potential G.toTemporalGraph t_j s_j := by
    unfold TemporalGraph.potential
    exact Real.sqrt_pos.mpr hVol_sj_pos
  -- ── Set up the L81 invocation. ──────────────────────────────────────────────
  -- Stopping-time scaffolding.
  have hS_meas_ℱ : ∀ t, @Measurable Ω (Finset V) (vm.ℱ t) ⊤ (vm.S t) := fun t =>
    (measurable_of_countable (fun A => VoterModel.minoritySet G.toTemporalGraph t A)).comp
      (vm.A_stronglyAdapted t).measurable
  have hT_stop_emb : ∀ k,
      IsStoppingTime vm.ℱ (fun ω => (embeddedChainTime G.toTemporalGraph vm Δ k ω : ℕ∞)) := fun k =>
    embeddedChainTime_isStoppingTime G.toTemporalGraph vm Δ hS_meas_ℱ k
  -- T_{j+1} ≤ cap + 1 globally (the structural bound on volumeExcursionTime).
  set cap : ℕ := (∑ k ∈ Finset.range (j + 1), Δ k) - 1 with hcap_def
  have hT_next_le : ∀ ω, embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω ≤ cap + 1 := fun ω => by
    show volumeExcursionTime G.toTemporalGraph vm (embeddedChainTime G.toTemporalGraph vm Δ j ω) cap ω ≤ cap + 1
    exact volumeExcursionTime_le_succ G.toTemporalGraph vm _ _ ω
  -- T_{j+1} > 0 globally: T_{j+1} ω = vET (T_j ω) cap ω. Either T_j ω ≤ cap and
  -- `lt_volumeExcursionTime` applies, or T_j ω > cap and the candidates set is
  -- empty so vET = cap + 1 ≥ 1.
  have hT_next_pos : ∀ ω, 0 < embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω := by
    intro ω
    show 0 < volumeExcursionTime G.toTemporalGraph vm (embeddedChainTime G.toTemporalGraph vm Δ j ω) cap ω
    set t₀ := embeddedChainTime G.toTemporalGraph vm Δ j ω
    by_cases h : t₀ ≤ cap
    · exact Nat.lt_of_le_of_lt (Nat.zero_le _) (lt_volumeExcursionTime G.toTemporalGraph vm t₀ cap ω h)
    · push Not at h
      unfold volumeExcursionTime
      dsimp only
      have hIcc_empty : Finset.Icc t₀ cap = ∅ := Finset.Icc_eq_empty (by omega)
      have hcand_empty : ((Finset.Icc t₀ cap).filter fun t =>
          2 * TemporalGraph.volume G.toTemporalGraph t (vm.S t ω) <
            TemporalGraph.volume G.toTemporalGraph t₀ (vm.S t₀ ω) ∨
          3 * TemporalGraph.volume G.toTemporalGraph t₀ (vm.S t₀ ω) <
            2 * TemporalGraph.volume G.toTemporalGraph t (vm.S t ω)) = ∅ := by
        rw [hIcc_empty]; rfl
      rw [hcand_empty]
      simp only [Finset.not_nonempty_empty, ↓reduceDIte]
      omega
  -- T_{j+1} ≥ t_j a.e. on F_T (from T_j = t_j on F_T + strict-mono).
  have hT_next_ge_F : ∀ᵐ ω ∂((vm.μ : Measure Ω).restrict F_T),
      t_j ≤ embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω := by
    refine ae_restrict_of_forall_mem hF_T_meas_top ?_
    intro ω hωF
    have hle : embeddedChainTime G.toTemporalGraph vm Δ j ω ≤ cap := hF_T_eq ω hωF ▸ hT_cap
    have hmono := embeddedChainTime_strictMono G.toTemporalGraph vm Δ j ω hle
    linarith [hF_T_eq ω hωF]
  -- T_{j+1} > 0 a.e. on F_T.
  have hT_next_pos_F : ∀ᵐ ω ∂((vm.μ : Measure Ω).restrict F_T),
      0 < embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω :=
    ae_of_all _ hT_next_pos
  -- ψ(t_j) ≤ ψ(t_j, s_j) a.e. on F_T (equality, via hF_S).
  have hpsi_init_F : ∀ᵐ ω ∂((vm.μ : Measure Ω).restrict F_T),
      vm.psiS t_j ω ≤ TemporalGraph.potential G.toTemporalGraph t_j s_j := by
    apply ae_restrict_of_forall_mem hF_T_meas_top
    intro ω hω
    have : vm.psiS t_j ω = TemporalGraph.potential G.toTemporalGraph t_j s_j := by
      change TemporalGraph.potential G.toTemporalGraph t_j (vm.S t_j ω) = _; rw [hF_S_eq ω hω]
    linarith
  -- Stability on F_T: derived from hF_T_eq + hF_S_eq + volumeExcursionTime_vol_le.
  have hstable_vol : ∀ ω ∈ F_T, ∀ k, t_j ≤ k →
      k < embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω →
      (TemporalGraph.volume G.toTemporalGraph k (vm.S k ω) : ℝ) ≤
        3 / 2 * (TemporalGraph.volume G.toTemporalGraph t_j s_j : ℝ) := by
    intro ω hωF k h_lo h_hi
    have hT_next : embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω =
        volumeExcursionTime G.toTemporalGraph vm t_j cap ω := by
      simp only [embeddedChainTime]; rw [hF_T_eq ω hωF, ← hcap_def]
    rw [hT_next] at h_hi
    have hbound := volumeExcursionTime_vol_le G.toTemporalGraph vm t_j _ k ω h_lo h_hi
    rw [hF_S_eq ω hωF] at hbound
    have hbound_r : (2 : ℝ) * (TemporalGraph.volume G.toTemporalGraph k (vm.S k ω) : ℝ) ≤
        3 * (TemporalGraph.volume G.toTemporalGraph t_j s_j : ℝ) := by exact_mod_cast hbound
    linarith
  -- Nonempty S_k on F_T throughout [t_j, T_{j+1}).
  have hS_nonempty_F : ∀ ω ∈ F_T, ∀ k, t_j ≤ k →
      k < embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω →
      (vm.S k ω).Nonempty := by
    intro ω hωF k h_lo h_hi
    have hT_next : embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω =
        volumeExcursionTime G.toTemporalGraph vm t_j cap ω := by
      simp only [embeddedChainTime]; rw [hF_T_eq ω hωF, ← hcap_def]
    rw [hT_next] at h_hi
    exact volumeExcursionTime_S_nonempty G vm t_j _ k ω h_lo h_hi
      (hF_S_eq ω hωF ▸ hs_j_ne)
  -- Convert hLarge to L81's `hedge_sum_large` form: μ_param = 1, Δ_L81 = 8/φ_j.
  -- L81 wants: E[Σ cutS | ℱ_{t_j}] > μ_param · Vol(t_j, s_j) / Δ_L81 a.e. on F_T.
  -- With μ_param=1, Δ_L81=8/φ_j: 1·Vol/(8/φ_j) = φ_j·Vol/8 = (1/8)·Vol/(1/φ_j).
  -- The input `hLarge` is exactly `> (1/8) · Vol / (1/φ_j)`, so just rewrite RHS.
  have hΔ_L81 : (0 : ℝ) < 8 / φ_j := by positivity
  have h_edge_strict : ∀ᵐ ω ∂((vm.μ : Measure Ω).restrict F_T),
      ((vm.μ : Measure Ω)[fun ω' => ∑ k ∈ Finset.Icc t_j (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω' - 1),
        (vm.cutS k ω' : ℝ) | vm.ℱ t_j]) ω
        > 1 * (TemporalGraph.volume G.toTemporalGraph t_j s_j : ℝ) / (8 / φ_j) := by
    filter_upwards [hLarge] with ω hω
    have hrw : (1 / 8 : ℝ) * (TemporalGraph.volume G.toTemporalGraph t_j s_j : ℝ) / (1 / φ_j) =
        1 * (TemporalGraph.volume G.toTemporalGraph t_j s_j : ℝ) / (8 / φ_j) := by
      have hφ_ne : φ_j ≠ 0 := ne_of_gt hφ_j_pos
      field_simp
    linarith [hrw ▸ hω]
  -- Apply L81: `potential_decrease_stable_interval_large_on_fiber` with
  -- μ_param=1, Δ=8/φ_j. Gives conditional ψ-drift bound a.e. on F_T.
  have h_L81 := potential_decrease_stable_interval_large_on_fiber
    G vm s_j hs_j_ne t_j (embeddedChainTime G.toTemporalGraph vm Δ (j + 1))
    (hT_stop_emb (j + 1)) (cap + 1) hT_next_le
    F_T hF_T_meas hT_next_ge_F hT_next_pos_F hpsi_init_F (8 / φ_j) hΔ_L81
    hstable_vol hS_nonempty_F 1 h_edge_strict
  -- Normalize L81's bound to the target form:
  --   -((1·d_min)/(24·√6·(8/φ_j)·ψ(s_j))) ≤ -((d_min·φ_j)/(192·√6·ψ(s_j)))
  -- (equality after `field_simp`).
  have h_L81' : ∀ᵐ ω ∂((vm.μ : Measure Ω).restrict F_T),
      ((vm.μ : Measure Ω)[fun ω' => vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω') ω' -
        TemporalGraph.potential G.toTemporalGraph t_j s_j | vm.ℱ t_j]) ω
        ≤ -((G.minDegreeAt 0 : ℝ) * φ_j) /
            (192 * Real.sqrt 6 * TemporalGraph.potential G.toTemporalGraph t_j s_j) := by
    refine h_L81.mono fun ω hω => le_trans hω ?_
    have hsq6 : Real.sqrt 6 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
    have hφ_ne : φ_j ≠ 0 := ne_of_gt hφ_j_pos
    by_cases hψ0 : TemporalGraph.potential G.toTemporalGraph t_j s_j = 0
    · simp [hψ0]
    · have heq : -((1 * (G.minDegreeAt 0 : ℝ)) / (24 * Real.sqrt 6 *
          (8 / φ_j) * TemporalGraph.potential G.toTemporalGraph t_j s_j)) =
          -((G.minDegreeAt 0 : ℝ) * φ_j) / (192 * Real.sqrt 6 *
            TemporalGraph.potential G.toTemporalGraph t_j s_j) := by
        field_simp [hsq6, hφ_ne, hψ0]
        ring
      linarith [heq]
  -- ── Integrate the conditional bound over F_T. ────────────────────────────────
  -- Use setIntegral_condExp to convert to set-integral form on F_T.
  -- Apply L77 (chi_down_drift_voter_on_fiber) for χ part.
  have hL77 := chi_down_drift_voter_on_fiber G vm s_j t_j Δ hΔ_pos j F_T
    hF_T_meas hF_T_eq hF_S_eq hT_cap
  -- ψ(T_j ω) = potential G.toTemporalGraph t_j s_j and χ(T_j ω, S_{T_j ω}) = chiPotential G.toTemporalGraph t_j s_j on F_T.
  have hψ_Tj_eq_on_F : ∀ ω ∈ F_T, vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω =
      TemporalGraph.potential G.toTemporalGraph t_j s_j := by
    intro ω hω
    show TemporalGraph.potential G.toTemporalGraph (embeddedChainTime G.toTemporalGraph vm Δ j ω)
        (vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω) = _
    rw [hF_T_eq ω hω, hF_S_eq ω hω]
  have hχ_Tj_eq_on_F : ∀ ω ∈ F_T,
      G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ j ω)
        (vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω)
        = G.chiPotential t_j s_j := by
    intro ω hω
    rw [hF_T_eq ω hω, hF_S_eq ω hω]
  -- Integrand rewrite on F_T.
  have hinteg_eq_on_F : ∀ ω ∈ F_T,
      ((α : ℝ) * (vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω
              - vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω)
          + (G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
                (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω)
            - G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ j ω)
                (vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω))) =
      (α * (vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω
              - TemporalGraph.potential G.toTemporalGraph t_j s_j)
        + (G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
              (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω)
            - G.chiPotential t_j s_j)) := by
    intro ω hω
    rw [hψ_Tj_eq_on_F ω hω, hχ_Tj_eq_on_F ω hω]
  rw [setIntegral_congr_fun hF_T_meas_top (fun ω hω => hinteg_eq_on_F ω hω)]
  -- ── Universe-bound for integrability. ──────────────────────────────────────
  set Vu : ℕ := TemporalGraph.volume G.toTemporalGraph 0 (Finset.univ : Finset V) with hVu_def
  have hVol_le_univ : ∀ t S, TemporalGraph.volume G.toTemporalGraph t S ≤ Vu := by
    intro t S
    have h1 : TemporalGraph.volume G.toTemporalGraph t S ≤ TemporalGraph.volume G.toTemporalGraph t Finset.univ := by
      unfold TemporalGraph.volume SimpleGraph.volume
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have h2 : TemporalGraph.volume G.toTemporalGraph t Finset.univ = Vu :=
      G.volume_fixed _ _ _
    exact h1.trans_eq h2
  have hT_meas : ∀ k, Measurable (embeddedChainTime G.toTemporalGraph vm Δ k) := by
    intro k s _
    rw [show (embeddedChainTime G.toTemporalGraph vm Δ k) ⁻¹' s =
        ⋃ u ∈ s, {w | embeddedChainTime G.toTemporalGraph vm Δ k w = u} from by ext ω; simp]
    refine MeasurableSet.biUnion (Set.to_countable s) (fun u _ => ?_)
    have heq2 : {w : Ω | embeddedChainTime G.toTemporalGraph vm Δ k w = u} =
        {w | (embeddedChainTime G.toTemporalGraph vm Δ k w : ℕ∞) = ↑u} := by
      ext w
      exact ⟨fun heq => by exact_mod_cast heq, fun heq => by exact_mod_cast heq⟩
    rw [heq2]; exact vm.ℱ.le u _ ((hT_stop_emb k).measurableSet_eq u)
  have hψE_meas : Measurable (fun ω => vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω) := by
    intro S hS
    rw [show (fun ω => vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω) ⁻¹' S =
        ⋃ t : ℕ, (embeddedChainTime G.toTemporalGraph vm Δ (j + 1)) ⁻¹' {t} ∩ (vm.psiS t) ⁻¹' S from by
      ext ω
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_singleton_iff]
      refine ⟨fun h => ⟨embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω, rfl, h⟩, ?_⟩
      rintro ⟨t, heq, hp⟩
      show vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω ∈ S
      rw [heq]; exact hp]
    refine MeasurableSet.iUnion (fun t => ?_)
    have hpsi_meas : Measurable (vm.psiS t) := by
      have h1 : Measurable (fun ω => (TemporalGraph.volume G.toTemporalGraph t (vm.S t ω) : ℝ)) := by
        have hvol_fn : Measurable
            (fun s : Finset V => (TemporalGraph.volume G.toTemporalGraph t s : ℝ)) :=
          measurable_of_countable _
        have hS_t : Measurable (vm.S t) := fun S hS => vm.ℱ.le t _ ((hS_meas_ℱ t) hS)
        exact hvol_fn.comp hS_t
      show Measurable (fun ω => Real.sqrt (TemporalGraph.volume G.toTemporalGraph t (vm.S t ω) : ℝ))
      exact Real.continuous_sqrt.measurable.comp h1
    exact (hT_meas (j + 1) (measurableSet_singleton _)).inter (hpsi_meas hS)
  have hχE_meas : Measurable (fun ω => G.chiPotential
      (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω)) := by
    intro S hS
    rw [show (fun ω => G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
        (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω)) ⁻¹' S =
        ⋃ t : ℕ, (embeddedChainTime G.toTemporalGraph vm Δ (j + 1)) ⁻¹' {t} ∩
          (fun ω => G.chiPotential t (vm.S t ω)) ⁻¹' S from by
      ext ω
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_singleton_iff]
      refine ⟨fun h => ⟨embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω, rfl, h⟩, ?_⟩
      rintro ⟨t, heq, hp⟩
      show G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
        (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω) ∈ S
      rw [heq]; exact hp]
    refine MeasurableSet.iUnion (fun t => ?_)
    have hchi_meas : Measurable (fun ω => G.chiPotential t (vm.S t ω)) := by
      have hchi_fn : Measurable (fun s : Finset V => G.chiPotential t s) :=
        measurable_of_countable _
      have hS_t : Measurable (vm.S t) := fun S hS => vm.ℱ.le t _ ((hS_meas_ℱ t) hS)
      exact hchi_fn.comp hS_t
    exact (hT_meas (j + 1) (measurableSet_singleton _)).inter (hchi_meas hS)
  -- Integrability of (ψ(T_{j+1}) - ψ(t_j,s_j)).
  have hψ_int : Integrable
      (fun ω => vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω -
        TemporalGraph.potential G.toTemporalGraph t_j s_j) vm.μ := by
    refine MeasureTheory.Integrable.of_bound
      (C := Real.sqrt (Vu : ℝ) + TemporalGraph.potential G.toTemporalGraph t_j s_j)
      (hψE_meas.sub_const _).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    have h_nn : 0 ≤ vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω :=
      Real.sqrt_nonneg _
    have h_bnd : vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω ≤ Real.sqrt (Vu : ℝ) := by
      show TemporalGraph.potential G.toTemporalGraph _ _ ≤ _
      apply Real.sqrt_le_sqrt
      exact_mod_cast hVol_le_univ _ _
    have hpot_nn : 0 ≤ TemporalGraph.potential G.toTemporalGraph t_j s_j := Real.sqrt_nonneg _
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · linarith [Real.sqrt_nonneg ((Vu : ℝ))]
    · linarith
  have hχ_int : Integrable
      (fun ω => G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
          (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω) -
        G.chiPotential t_j s_j) vm.μ := by
    have hVol_nn : (0 : ℝ) ≤ (Vu : ℝ) := Nat.cast_nonneg _
    refine MeasureTheory.Integrable.of_bound
      (C := Real.log (1 + (Vu : ℝ)) + G.chiPotential t_j s_j)
      (hχE_meas.sub_const _).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    have h_nn : 0 ≤ G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
        (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω) := by
      unfold TemporalGraphFixedDegree.chiPotential TemporalGraph.chiPotential
      apply Real.log_nonneg
      have h0 : (0 : ℝ) ≤ (TemporalGraph.volume G.toTemporalGraph (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
          (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω) : ℝ) := Nat.cast_nonneg _
      linarith
    have h_bnd : G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
        (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω) ≤ Real.log (1 + (Vu : ℝ)) := by
      unfold TemporalGraphFixedDegree.chiPotential TemporalGraph.chiPotential
      have h1 : (0 : ℝ) < 1 + (TemporalGraph.volume G.toTemporalGraph (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
          (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω) : ℝ) := by
        have h0 : (0 : ℝ) ≤ (TemporalGraph.volume G.toTemporalGraph (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
            (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω) : ℝ) := Nat.cast_nonneg _
        linarith
      apply Real.log_le_log h1
      have h := hVol_le_univ (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
        (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω)
      have h2 : (TemporalGraph.volume G.toTemporalGraph (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
          (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω) : ℝ) ≤ (Vu : ℝ) := by
        exact_mod_cast h
      linarith
    have hchi_pot_nn : 0 ≤ G.chiPotential t_j s_j := by
      unfold TemporalGraphFixedDegree.chiPotential TemporalGraph.chiPotential
      apply Real.log_nonneg
      have : (0 : ℝ) ≤ (TemporalGraph.volume G.toTemporalGraph t_j s_j : ℝ) := Nat.cast_nonneg _
      linarith
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · have hlog_nn : 0 ≤ Real.log (1 + (Vu : ℝ)) :=
        Real.log_nonneg (by linarith)
      linarith
    · linarith
  -- Split the integral by linearity.
  have hint_eq : ∫ ω in F_T,
      (α * (vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω
              - TemporalGraph.potential G.toTemporalGraph t_j s_j)
        + (G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
              (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω)
            - G.chiPotential t_j s_j)) ∂vm.μ =
      α * ∫ ω in F_T,
        (vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω -
          TemporalGraph.potential G.toTemporalGraph t_j s_j) ∂vm.μ +
      ∫ ω in F_T,
        (G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
            (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω) -
          G.chiPotential t_j s_j) ∂vm.μ := by
    rw [integral_add (hψ_int.const_mul _).integrableOn hχ_int.integrableOn]
    rw [integral_const_mul]
  rw [hint_eq]
  -- ── Convert L81's a.e.-on-F_T conditional bound to a set-integral on F_T. ───
  -- L81 (`h_L81'`) says E[ψ(T_{j+1}) - ψ(t_j,s_j) | ℱ_{t_j}] ≤ K_ψ a.e. on F_T,
  -- where K_ψ = -(d_min·φ_j)/(192·√6·ψ(s_j)) (Δ_L81=8/φ_j).
  set K_ψ : ℝ := -((G.minDegreeAt 0 : ℝ) * φ_j)
      / (192 * Real.sqrt 6 * TemporalGraph.potential G.toTemporalGraph t_j s_j) with hKψ_def
  set μF : ℝ := ((vm.μ : Measure Ω) F_T).toReal with hμF_def
  have hμF_nn : 0 ≤ μF := ENNReal.toReal_nonneg
  -- ∫_{F_T} (ψ - potential) = ∫_{F_T} E[ψ - potential | ℱ_{t_j}] ≤ K_ψ · μF.
  have hψ_setInt_le : ∫ ω in F_T,
      (vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω -
        TemporalGraph.potential G.toTemporalGraph t_j s_j) ∂vm.μ ≤ K_ψ * μF := by
    -- Convert via setIntegral_condExp.
    have h_setInt :=
      setIntegral_condExp (μ := vm.μ) (hm := vm.ℱ.le t_j) (f :=
          fun ω' => vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω') ω' -
            TemporalGraph.potential G.toTemporalGraph t_j s_j)
        (hf := hψ_int) (hs := hF_T_meas)
    -- h_setInt : ∫_{F_T} E[ψ - pot | ℱ_{t_j}] dμ = ∫_{F_T} (ψ - pot) dμ.
    rw [← h_setInt]
    -- Now: ∫_{F_T} E[ψ - pot | ℱ_{t_j}] dμ ≤ K_ψ · μF.
    -- Use the a.e.-on-F_T bound h_L81'.
    have hbnd : ∫ ω in F_T,
        ((vm.μ : Measure Ω)[fun ω' => vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω') ω' -
            TemporalGraph.potential G.toTemporalGraph t_j s_j | vm.ℱ t_j]) ω ∂vm.μ ≤
        ∫ _ω in F_T, K_ψ ∂vm.μ := by
      refine setIntegral_mono_ae_restrict
        (integrable_condExp.integrableOn) (integrable_const _).integrableOn h_L81'
    have hrhs : ∫ _ω in F_T, K_ψ ∂vm.μ = K_ψ * μF := by
      rw [setIntegral_const]
      show ((vm.μ : Measure Ω) F_T).toReal • K_ψ = K_ψ * μF
      rw [smul_eq_mul, mul_comm, hμF_def]
    linarith [hrhs ▸ hbnd]
  -- ── Arithmetic: α · K_ψ ≤ -(φ_j / 2048). ─────────────────────────────────────
  have hd_eq : (G.minDegreeAt 0 : ℝ) = (d_min : ℝ) := by rw [hd]
  have hvol_lt_tj : (TemporalGraph.volume G.toTemporalGraph t_j s_j : ℝ) <
      8 * (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) := by
    rw [show (TemporalGraph.volume G.toTemporalGraph t_j s_j : ℝ) = (TemporalGraph.volume G.toTemporalGraph 0 s_j : ℝ) from by
      exact_mod_cast (G.volume_fixed s_j t_j 0)]
    exact hvol_lt
  have hsqrt_lt : Real.sqrt (TemporalGraph.volume G.toTemporalGraph t_j s_j : ℝ) <
      Real.sqrt (8 * (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ)) :=
    Real.sqrt_lt_sqrt (Nat.cast_nonneg _) hvol_lt_tj
  have hsqrt8_eq : Real.sqrt (8 * (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ)) =
      Real.sqrt 8 * Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8)]
  have hα_K_le : α * K_ψ ≤ -(φ_j / 2048) := by
    have hsqrt6_pos : (0 : ℝ) < Real.sqrt 6 := Real.sqrt_pos.mpr (by norm_num)
    have hsqrt8_pos : (0 : ℝ) < Real.sqrt 8 := Real.sqrt_pos.mpr (by norm_num)
    have hsqrt_s0_pos : (0 : ℝ) < Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) :=
      Real.sqrt_pos.mpr hVol_s0_pos
    have hsqrt_sj_pos : (0 : ℝ) < Real.sqrt (TemporalGraph.volume G.toTemporalGraph t_j s_j : ℝ) :=
      Real.sqrt_pos.mpr hVol_sj_pos
    have hψ_sj_eq : TemporalGraph.potential G.toTemporalGraph t_j s_j =
        Real.sqrt (TemporalGraph.volume G.toTemporalGraph t_j s_j : ℝ) := rfl
    have hd_ne : (d_min : ℝ) ≠ 0 := ne_of_gt hd_pos_real
    -- Simplify α·K_ψ = -(φ_j·√vol(s_0)) / (192·√6·√vol(t_j,s_j))
    have hα_K : α * K_ψ = -(φ_j * Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ)) /
        (192 * Real.sqrt 6 * Real.sqrt (TemporalGraph.volume G.toTemporalGraph t_j s_j : ℝ)) := by
      rw [hα_def, hKψ_def, hψ_sj_eq, hd_eq]
      field_simp
    rw [hα_K]
    rw [neg_div, neg_le_neg_iff]
    -- Want: φ_j / 2048 ≤ (φ_j·√vol(s_0)) / (192·√6·√vol(t_j,s_j)).
    have hdenom_pos : (0 : ℝ) < 192 * Real.sqrt 6 *
        Real.sqrt (TemporalGraph.volume G.toTemporalGraph t_j s_j : ℝ) := by
      have : (0 : ℝ) < 192 * Real.sqrt 6 := by positivity
      exact mul_pos this hsqrt_sj_pos
    rw [le_div_iff₀ hdenom_pos]
    -- Want: (φ_j/2048) · (192·√6·√vol(t_j,s_j)) ≤ φ_j·√vol(s_0).
    -- Using √vol(t_j,s_j) ≤ √8·√vol(s_0) and √48 ≤ 7:
    -- (φ_j/2048)·192·√6·√vol(t_j,s_j) ≤ (φ_j/2048)·192·√6·√8·√vol(s_0)
    --   = (φ_j/2048)·192·√48·√vol(s_0) ≤ (φ_j/2048)·192·7·√vol(s_0)
    --   = (2048·φ_j/2048)·√vol(s_0) ≤ φ_j·√vol(s_0). ✓ (since 2048 ≤ 2048)
    have h48_le : Real.sqrt 48 ≤ 7 := by
      have h49 : (7 : ℝ) = Real.sqrt 49 := by
        rw [show (49 : ℝ) = 7 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 7)]
      rw [h49]
      exact Real.sqrt_le_sqrt (by norm_num)
    have hsqrt6_mul_sqrt8 : Real.sqrt 6 * Real.sqrt 8 = Real.sqrt 48 := by
      rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 6)]; norm_num
    have hsqrt_sj_le : Real.sqrt (TemporalGraph.volume G.toTemporalGraph t_j s_j : ℝ) ≤
        Real.sqrt 8 * Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) := by
      rw [← hsqrt8_eq]; exact le_of_lt hsqrt_lt
    have hφ_4000_nn : 0 ≤ φ_j / 2048 := by positivity
    have h_step1 : (φ_j / 2048) * (192 * Real.sqrt 6 *
          Real.sqrt (TemporalGraph.volume G.toTemporalGraph t_j s_j : ℝ)) ≤
        (φ_j / 2048) * (192 * Real.sqrt 6 *
          (Real.sqrt 8 * Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ hφ_4000_nn
      apply mul_le_mul_of_nonneg_left hsqrt_sj_le
      positivity
    have h_step1' : (φ_j / 2048) * (192 * Real.sqrt 6 *
          (Real.sqrt 8 * Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ))) =
        (φ_j / 2048) * (192 * Real.sqrt 48 *
          Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ)) := by
      rw [show 192 * Real.sqrt 6 * (Real.sqrt 8 *
          Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ)) =
        192 * (Real.sqrt 6 * Real.sqrt 8) *
          Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) from by ring,
        hsqrt6_mul_sqrt8]
    rw [h_step1'] at h_step1
    refine le_trans h_step1 ?_
    have h_step2 : (φ_j / 2048) * (192 * Real.sqrt 48 *
          Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ)) ≤
        (φ_j / 2048) * (192 * 7 *
          Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hφ_4000_nn
      apply mul_le_mul_of_nonneg_right
      · apply mul_le_mul_of_nonneg_left h48_le; norm_num
      · exact le_of_lt hsqrt_s0_pos
    refine le_trans h_step2 ?_
    -- (φ_j/2048)·192·7·√vol(s_0) = (2048·φ_j/2048)·√vol(s_0) ≤ φ_j·√vol(s_0).
    have : (φ_j / 2048) * (192 * 7 *
          Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ)) =
        (φ_j * Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ)) * (1344 / 2048) := by ring
    rw [this]
    linarith only [mul_nonneg hφ_j_pos.le hsqrt_s0_pos.le]
  -- Conclude: α · ∫_F Δψ + ∫_F Δχ ≤ α · K_ψ · μF + 0 ≤ -(φ_j/2048) · μF.
  have hL81_scaled : α * ∫ ω in F_T,
      (vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω -
        TemporalGraph.potential G.toTemporalGraph t_j s_j) ∂vm.μ ≤ α * (K_ψ * μF) :=
    mul_le_mul_of_nonneg_left hψ_setInt_le hα_nn
  have hbound : α * ∫ ω in F_T,
      (vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω -
        TemporalGraph.potential G.toTemporalGraph t_j s_j) ∂vm.μ +
      ∫ ω in F_T,
        (G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
            (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω) -
          G.chiPotential t_j s_j) ∂vm.μ ≤
      α * (K_ψ * μF) + 0 :=
    add_le_add hL81_scaled hL77
  refine le_trans hbound ?_
  rw [add_zero]
  rw [show α * (K_ψ * μF) = (α * K_ψ) * μF from by ring]
  exact mul_le_mul_of_nonneg_right hα_K_le hμF_nn

/-- \label{lem:chi-down-drift-voter-unstable-from-NotIsStableInterval-on-fiber}

**L91 — Unstable dispatch wrapper for L68 Case 3.**

Combines the L75 ψ-bound and the L78 χ-bound under an F-restricted
positive-form unstable hypothesis (the a.e.-on-F negation of
`IsStableInterval G.toTemporalGraph vm Δ (1/8) j hT_stop`), yielding the integrated unstable
drift bound on the fiber `F`. Specifically, for
`F ⊆ {ω | T_j ω = t_j ∧ vm.S t_j ω = s_j}`,

  `∫_F (α · Δψ + Δχ) dvm.μ ≤ -1/2048 · (vm.μ F).toReal,`

where `α = √vol(0, s_0) / d_min` and `Δψ = ψ(T_{j+1}) − ψ(T_j)`,
`Δχ = χ(T_{j+1}, S_{T_{j+1}}) − χ(T_j, S_{T_j})`.

**Constant derivation.** L78 gives `∫_F Δχ ≤ -(1/2048) · μ(F).toReal`.
L75 gives `∫_F Δψ ≤ 0`; multiplying by `α ≥ 0` preserves this.
Summing gives `∫_F (α·Δψ + Δχ) ≤ -(1/2048) · μ(F).toReal`. -/
theorem chi_down_drift_voter_unstable_from_NotIsStableInterval_on_fiber
    {Ω : Type*} [MeasurableSpace Ω]
    (G : TemporalGraphFixedDegree V)
    (vm : G.VoterModelAbstract 2 Ω)
    (d_min : ℕ)
    -- Initial set s_0, current fiber state s_j ≠ ∅, realized time t_j
    (s_0 : Finset V)
    (s_j : Finset V) (hs_j_ne : s_j.Nonempty)
    (t_j : ℕ)
    -- Embedded chain parameters
    (Δ : ℕ → ℕ) (hΔ_pos : ∀ k, 1 ≤ Δ k) (j : ℕ)
    -- Fiber F: measurable in ℱ_{t_j}, with T_j = t_j and S_{t_j} = s_j on F
    (F : Set Ω)
    (hF_meas : MeasurableSet[vm.ℱ t_j] F)
    (hF_T : ∀ ω ∈ F, embeddedChainTime G.toTemporalGraph vm Δ j ω = t_j)
    (hF_S : ∀ ω ∈ F, vm.S t_j ω = s_j)
    -- t_j is within the cap for the (j+1)-th embedded interval (paper-tight cap)
    (hT_cap : t_j ≤ (∑ k ∈ Finset.range (j + 1), Δ k) - 1)
    -- Stopping-time certificate for T_j (matches L83's hT_stop)
    (hT_stop : IsStoppingTime vm.ℱ
        (fun ω => (embeddedChainTime G.toTemporalGraph vm Δ j ω : ℕ∞)))
    -- F-restricted positive-form unstable hypothesis (matches L83's input)
    (hUnstable_F : ∀ᵐ ω ∂((vm.μ : Measure Ω).restrict F),
        ((vm.μ : Measure Ω)[fun ω' =>
            |vm.volS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω') ω' -
              vm.volS (embeddedChainTime G.toTemporalGraph vm Δ j ω') ω'|
            | hT_stop.measurableSpace]) ω
          ≥ (1 / 8 : ℝ) * vm.volS (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω) :
    -- Conclusion: integrated unstable combined drift ≤ -1/2048·μ(F).toReal
    ∫ ω in F,
      ((Real.sqrt ((G.snapshot 0).volume s_0 : ℝ) / d_min)
          * (vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω
              - vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω)
        + (G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
              (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω)
          - G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ j ω)
              (vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω)))
      ∂vm.μ ≤ -(1 / 2048 : ℝ) * ((vm.μ : Measure Ω) F).toReal := by
  classical
  haveI hprob : IsProbabilityMeasure (vm.μ : Measure Ω) := inferInstance
  -- Top-level measurability of F.
  have hF_meas_top : MeasurableSet F := vm.ℱ.le t_j _ hF_meas
  -- Abbreviation: α := √vol(0, s_0)/d_min ≥ 0.
  set α : ℝ := Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) / d_min with hα_def
  have hα_nn : (0 : ℝ) ≤ α :=
    div_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _)
  -- Convert hUnstable_F to L78's hjump_F via L83.
  have hjump_F : ∀ᵐ ω ∂((vm.μ : Measure Ω).restrict F),
      ((vm.μ : Measure Ω)[fun ω' =>
          |vm.volS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω') ω' -
            vm.volS (embeddedChainTime G.toTemporalGraph vm Δ j ω') ω'| | vm.ℱ t_j]) ω
        ≥ 1 / 8 * (TemporalGraph.volume G.toTemporalGraph t_j s_j : ℝ) :=
    unstable_jump_from_conductance_on_fiber G.toTemporalGraph vm s_j t_j Δ j F
      hF_meas hF_T hF_S hT_stop hUnstable_F
  -- Apply L78 (chi_down_drift_voter_unstable_on_fiber).
  have hL78 := chi_down_drift_voter_unstable_on_fiber G vm s_j hs_j_ne t_j Δ hΔ_pos j F
    hF_meas hF_T hF_S hT_cap hjump_F
  -- Apply L75 (psi_down_drift_on_fiber).
  have hL75 := psi_down_drift_on_fiber G vm s_j t_j Δ hΔ_pos j F
    hF_meas hF_T hF_S hT_cap
  -- ψ(T_j ω) ω = potential G.toTemporalGraph t_j s_j and χ(T_j ω, S_{T_j ω}) = chiPotential G.toTemporalGraph t_j s_j on F.
  have hψ_Tj_eq_on_F : ∀ ω ∈ F, vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω =
      TemporalGraph.potential G.toTemporalGraph t_j s_j := by
    intro ω hω
    show TemporalGraph.potential G.toTemporalGraph (embeddedChainTime G.toTemporalGraph vm Δ j ω)
        (vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω) = _
    rw [hF_T ω hω, hF_S ω hω]
  have hχ_Tj_eq_on_F : ∀ ω ∈ F,
      G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ j ω)
        (vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω)
        = G.chiPotential t_j s_j := by
    intro ω hω
    rw [hF_T ω hω, hF_S ω hω]
  -- Integrand rewrite on F.
  have hinteg_eq_on_F : ∀ ω ∈ F,
      ((α : ℝ) * (vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω
              - vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω)
          + (G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
                (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω)
            - G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ j ω)
                (vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω))) =
      (α * (vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω
              - TemporalGraph.potential G.toTemporalGraph t_j s_j)
        + (G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
              (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω)
            - G.chiPotential t_j s_j)) := by
    intro ω hω
    rw [hψ_Tj_eq_on_F ω hω, hχ_Tj_eq_on_F ω hω]
  -- Rewrite the LHS integral via setIntegral_congr_fun.
  rw [setIntegral_congr_fun hF_meas_top (fun ω hω => hinteg_eq_on_F ω hω)]
  -- Universe-bound Vu for integrability.
  set Vu : ℕ := TemporalGraph.volume G.toTemporalGraph 0 (Finset.univ : Finset V) with hVu_def
  have hVol_le_univ : ∀ t S, TemporalGraph.volume G.toTemporalGraph t S ≤ Vu := by
    intro t S
    have h1 : TemporalGraph.volume G.toTemporalGraph t S ≤ TemporalGraph.volume G.toTemporalGraph t Finset.univ := by
      unfold TemporalGraph.volume SimpleGraph.volume
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have h2 : TemporalGraph.volume G.toTemporalGraph t Finset.univ = Vu :=
      G.volume_fixed _ _ _
    exact h1.trans_eq h2
  -- Stopping-time scaffolding (for measurability of ψ(T_{j+1}), χ(T_{j+1},·)).
  have hS_meas_ℱ : ∀ t, @Measurable Ω (Finset V) (vm.ℱ t) ⊤ (vm.S t) := fun t =>
    (measurable_of_countable (fun A => VoterModel.minoritySet G.toTemporalGraph t A)).comp
      (vm.A_stronglyAdapted t).measurable
  have hT_stop' : ∀ k,
      IsStoppingTime vm.ℱ (fun ω => (embeddedChainTime G.toTemporalGraph vm Δ k ω : ℕ∞)) := fun k =>
    embeddedChainTime_isStoppingTime G.toTemporalGraph vm Δ hS_meas_ℱ k
  have hT_meas : ∀ k, Measurable (embeddedChainTime G.toTemporalGraph vm Δ k) := by
    intro k s _
    rw [show (embeddedChainTime G.toTemporalGraph vm Δ k) ⁻¹' s =
        ⋃ u ∈ s, {w | embeddedChainTime G.toTemporalGraph vm Δ k w = u} from by ext ω; simp]
    refine MeasurableSet.biUnion (Set.to_countable s) (fun u _ => ?_)
    have heq2 : {w : Ω | embeddedChainTime G.toTemporalGraph vm Δ k w = u} =
        {w | (embeddedChainTime G.toTemporalGraph vm Δ k w : ℕ∞) = ↑u} := by
      ext w
      exact ⟨fun heq => by exact_mod_cast heq, fun heq => by exact_mod_cast heq⟩
    rw [heq2]; exact vm.ℱ.le u _ ((hT_stop' k).measurableSet_eq u)
  have hψE_meas : Measurable (fun ω => vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω) := by
    intro S hS
    rw [show (fun ω => vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω) ⁻¹' S =
        ⋃ t : ℕ, (embeddedChainTime G.toTemporalGraph vm Δ (j + 1)) ⁻¹' {t} ∩ (vm.psiS t) ⁻¹' S from by
      ext ω
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_singleton_iff]
      refine ⟨fun h => ⟨embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω, rfl, h⟩, ?_⟩
      rintro ⟨t, heq, hp⟩
      show vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω ∈ S
      rw [heq]; exact hp]
    refine MeasurableSet.iUnion (fun t => ?_)
    have hpsi_meas : Measurable (vm.psiS t) := by
      have h1 : Measurable (fun ω => (TemporalGraph.volume G.toTemporalGraph t (vm.S t ω) : ℝ)) := by
        have hvol_fn : Measurable
            (fun s : Finset V => (TemporalGraph.volume G.toTemporalGraph t s : ℝ)) :=
          measurable_of_countable _
        have hS_t : Measurable (vm.S t) := fun S hS => vm.ℱ.le t _ ((hS_meas_ℱ t) hS)
        exact hvol_fn.comp hS_t
      show Measurable (fun ω => Real.sqrt (TemporalGraph.volume G.toTemporalGraph t (vm.S t ω) : ℝ))
      exact Real.continuous_sqrt.measurable.comp h1
    exact (hT_meas (j + 1) (measurableSet_singleton _)).inter (hpsi_meas hS)
  have hχE_meas : Measurable (fun ω => G.chiPotential
      (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω)) := by
    intro S hS
    rw [show (fun ω => G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
        (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω)) ⁻¹' S =
        ⋃ t : ℕ, (embeddedChainTime G.toTemporalGraph vm Δ (j + 1)) ⁻¹' {t} ∩
          (fun ω => G.chiPotential t (vm.S t ω)) ⁻¹' S from by
      ext ω
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_singleton_iff]
      refine ⟨fun h => ⟨embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω, rfl, h⟩, ?_⟩
      rintro ⟨t, heq, hp⟩
      show G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
        (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω) ∈ S
      rw [heq]; exact hp]
    refine MeasurableSet.iUnion (fun t => ?_)
    have hchi_meas : Measurable (fun ω => G.chiPotential t (vm.S t ω)) := by
      have hchi_fn : Measurable (fun s : Finset V => G.chiPotential t s) :=
        measurable_of_countable _
      have hS_t : Measurable (vm.S t) := fun S hS => vm.ℱ.le t _ ((hS_meas_ℱ t) hS)
      exact hchi_fn.comp hS_t
    exact (hT_meas (j + 1) (measurableSet_singleton _)).inter (hchi_meas hS)
  -- Integrability of (ψ(T_{j+1}) − ψ(t_j,s_j)) and (χ(T_{j+1}, S_{T_{j+1}}) − χ(t_j,s_j)).
  have hψ_int : Integrable
      (fun ω => vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω -
        TemporalGraph.potential G.toTemporalGraph t_j s_j) vm.μ := by
    refine MeasureTheory.Integrable.of_bound
      (C := Real.sqrt (Vu : ℝ) + TemporalGraph.potential G.toTemporalGraph t_j s_j)
      (hψE_meas.sub_const _).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    have h_nn : 0 ≤ vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω :=
      Real.sqrt_nonneg _
    have h_bnd : vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω ≤ Real.sqrt (Vu : ℝ) := by
      show TemporalGraph.potential G.toTemporalGraph _ _ ≤ _
      apply Real.sqrt_le_sqrt
      exact_mod_cast hVol_le_univ _ _
    have hpot_nn : 0 ≤ TemporalGraph.potential G.toTemporalGraph t_j s_j := Real.sqrt_nonneg _
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · linarith [Real.sqrt_nonneg ((Vu : ℝ))]
    · linarith
  have hχ_int : Integrable
      (fun ω => G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
          (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω) -
        G.chiPotential t_j s_j) vm.μ := by
    have hVol_nn : (0 : ℝ) ≤ (Vu : ℝ) := Nat.cast_nonneg _
    refine MeasureTheory.Integrable.of_bound
      (C := Real.log (1 + (Vu : ℝ)) + G.chiPotential t_j s_j)
      (hχE_meas.sub_const _).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    have h_nn : 0 ≤ G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
        (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω) := by
      unfold TemporalGraphFixedDegree.chiPotential TemporalGraph.chiPotential
      apply Real.log_nonneg
      have h0 : (0 : ℝ) ≤ (TemporalGraph.volume G.toTemporalGraph (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
          (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω) : ℝ) := Nat.cast_nonneg _
      linarith
    have h_bnd : G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
        (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω) ≤ Real.log (1 + (Vu : ℝ)) := by
      unfold TemporalGraphFixedDegree.chiPotential TemporalGraph.chiPotential
      have h1 : (0 : ℝ) < 1 + (TemporalGraph.volume G.toTemporalGraph (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
          (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω) : ℝ) := by
        have h0 : (0 : ℝ) ≤ (TemporalGraph.volume G.toTemporalGraph (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
            (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω) : ℝ) := Nat.cast_nonneg _
        linarith
      apply Real.log_le_log h1
      have h := hVol_le_univ (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
        (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω)
      have h2 : (TemporalGraph.volume G.toTemporalGraph (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
          (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω) : ℝ) ≤ (Vu : ℝ) := by
        exact_mod_cast h
      linarith
    have hchi_pot_nn : 0 ≤ G.chiPotential t_j s_j := by
      unfold TemporalGraphFixedDegree.chiPotential TemporalGraph.chiPotential
      apply Real.log_nonneg
      have : (0 : ℝ) ≤ (TemporalGraph.volume G.toTemporalGraph t_j s_j : ℝ) := Nat.cast_nonneg _
      linarith
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · have hlog_nn : 0 ≤ Real.log (1 + (Vu : ℝ)) :=
        Real.log_nonneg (by linarith)
      linarith
    · linarith
  -- Split the integral by linearity.
  have hint_eq : ∫ ω in F,
      (α * (vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω
              - TemporalGraph.potential G.toTemporalGraph t_j s_j)
        + (G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
              (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω)
            - G.chiPotential t_j s_j)) ∂vm.μ =
      α * ∫ ω in F,
        (vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω -
          TemporalGraph.potential G.toTemporalGraph t_j s_j) ∂vm.μ +
      ∫ ω in F,
        (G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
            (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω) -
          G.chiPotential t_j s_j) ∂vm.μ := by
    rw [integral_add (hψ_int.const_mul _).integrableOn hχ_int.integrableOn]
    rw [integral_const_mul]
  rw [hint_eq]
  set μF : ℝ := ((vm.μ : Measure Ω) F).toReal with hμF_def
  have hμF_nn : 0 ≤ μF := ENNReal.toReal_nonneg
  -- α · ∫_F Δψ ≤ α · 0 = 0 (from L75 + α ≥ 0).
  have hL75' : α * ∫ ω in F,
      (vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω -
        TemporalGraph.potential G.toTemporalGraph t_j s_j) ∂vm.μ ≤ 0 := by
    have := mul_le_mul_of_nonneg_left hL75 hα_nn
    simpa using this
  -- Sum L75' and L78 bounds: ≤ 0 + (-1/2048) · μF = -1/2048 · μF.
  have hbound : α * ∫ ω in F,
      (vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω -
        TemporalGraph.potential G.toTemporalGraph t_j s_j) ∂vm.μ +
      ∫ ω in F,
        (G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
            (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω) -
          G.chiPotential t_j s_j) ∂vm.μ ≤
      0 + (-1 / 2048) * μF := by
    exact add_le_add hL75' hL78
  refine le_trans hbound ?_
  -- 0 + (-1/2048) · μF ≤ -(1/2048) · μF.
  rw [zero_add]
  have h_const : (-1 / 2048 : ℝ) ≤ -(1 / 2048) := by norm_num
  exact mul_le_mul_of_nonneg_right h_const hμF_nn

/-- \label{lem:hexit-from-volumeExcursionTime-on-fiber}

**L94 — Exit-time excursion bound from `volumeExcursionTime` definition.**

When the (j+1)-th embedded chain time `T_{j+1}` fires within the cap (so an
actual volume excursion occurred), the volume at `T_{j+1}` deviates from
`Vol(t_j, s_j)` by at least `Vol(t_j, s_j) / 2`. This is the `exit`-field
shape of `Case2Hypotheses`.

**Statement.** Under the F-restricted setting where `T_j ω = t_j` and
`S_{t_j} ω = s_j` for all `ω ∈ F`, and for every such `ω` satisfying
`T_{j+1} ω ≤ cap` (i.e., the volume-excursion candidate set was nonempty),

  `(1/2) · Vol(t_j, s_j) ≤ |Vol(T_{j+1}, S_{T_{j+1}}) - Vol(t_j, s_j)|`.

This is essentially a definitional unfolding of `volumeExcursionTime`: when
the candidate set is nonempty, the minimum candidate satisfies the filter
predicate, which is exactly the up/down 3/2-or-1/2 excursion. We convert
the integer predicate into the real-valued absolute-value inequality. -/
theorem hexit_from_volumeExcursionTime_on_fiber
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    {Ω : Type*} [MeasurableSpace Ω]
    (G : TemporalGraph V)
    (vm : TemporalGraph.VoterModelAbstract G 2 Ω)
    -- Embedded chain parameters
    (Δ : ℕ → ℕ) (j : ℕ)
    -- Calendar / embedded times: t_j is the realized time, cap is the (j+1)-th cap
    (t_j : ℕ) (s_j : Finset V)
    (cap : ℕ)
    -- Fiber data: on F, T_j = t_j and S_{t_j} = s_j; cap is the embedded cap
    -- for transition (j → j+1) (paper-tight).
    (hcap_def : cap = (∑ k ∈ Finset.range (j + 1), Δ k) - 1)
    -- ω satisfies the fiber identities and the exit fired (T_{j+1} ω ≤ cap).
    (ω : Ω)
    (hT_j : embeddedChainTime G vm Δ j ω = t_j)
    (hS_j : vm.S t_j ω = s_j)
    (hexit_fired : embeddedChainTime G vm Δ (j + 1) ω ≤ cap) :
    -- Conclusion: |Vol(T_{j+1}, S_{T_{j+1}}) - Vol(t_j, s_j)| ≥ (1/2) · Vol(t_j, s_j)
    (1 / 2 : ℝ) * (TemporalGraph.volume G t_j s_j : ℝ) ≤
      |(TemporalGraph.volume G (embeddedChainTime G vm Δ (j + 1) ω)
            (vm.S (embeddedChainTime G vm Δ (j + 1) ω) ω) : ℝ)
        - (TemporalGraph.volume G t_j s_j : ℝ)| := by
  classical
  -- Unfold `embeddedChainTime G vm Δ (j+1) ω = volumeExcursionTime G vm t_j cap ω`.
  -- (After substituting t_j for T_j via hT_j.)
  set T1 : ℕ := embeddedChainTime G vm Δ (j + 1) ω with hT1_def
  have hT1_eq : T1 = volumeExcursionTime G vm t_j cap ω := by
    rw [hT1_def]
    show embeddedChainTime G vm Δ (j + 1) ω = _
    -- embeddedChainTime (j+1) = volumeExcursionTime G vm (embeddedChainTime j ω) cap' ω
    -- where cap' = (∑ k ∈ range (j+1), Δ k) - 1 (paper-tight).
    show volumeExcursionTime G vm
        (embeddedChainTime G vm Δ j ω)
        ((∑ k ∈ Finset.range (j + 1), Δ k) - 1) ω = _
    rw [hT_j, ← hcap_def]
  -- Substitute back into the goal.
  rw [hT1_eq] at hexit_fired
  -- volumeExcursionTime t_j cap ω = candidates.min' (when nonempty), else cap+1.
  -- Since `hexit_fired : volumeExcursionTime ≤ cap`, the candidates set is nonempty,
  -- and the result equals candidates.min'. The min' element satisfies the
  -- excursion predicate, giving the desired inequality.
  -- Step 1: extract that the candidates set is nonempty.
  -- Otherwise volumeExcursionTime = cap + 1, contradicting hexit_fired.
  set v₀ : ℕ := TemporalGraph.volume G t_j (vm.S t_j ω) with hv₀_def
  set candidates : Finset ℕ := (Finset.Icc t_j cap).filter fun t =>
    2 * TemporalGraph.volume G t (vm.S t ω) < v₀ ∨
    3 * v₀ < 2 * TemporalGraph.volume G t (vm.S t ω) with hcand_def
  have hvET_eq : volumeExcursionTime G vm t_j cap ω =
      if h : candidates.Nonempty then candidates.min' h else cap + 1 := by
    unfold volumeExcursionTime
    rfl
  -- Case-split on Nonempty.
  by_cases hne : candidates.Nonempty
  · -- candidates.min' satisfies the excursion predicate.
    rw [hvET_eq, dif_pos hne] at hexit_fired
    -- T1 (the inhabited witness in candidates) satisfies the excursion predicate.
    have hT1_eq_min : volumeExcursionTime G vm t_j cap ω = candidates.min' hne := by
      rw [hvET_eq, dif_pos hne]
    rw [hT1_eq, hT1_eq_min]
    -- min' candidates satisfies the filter predicate.
    have hmem := Finset.min'_mem candidates hne
    have hfilt : (candidates.min' hne) ∈
        (Finset.Icc t_j cap).filter (fun t =>
          2 * TemporalGraph.volume G t (vm.S t ω) < v₀ ∨
          3 * v₀ < 2 * TemporalGraph.volume G t (vm.S t ω)) := hmem
    have hexc := (Finset.mem_filter.mp hfilt).2
    -- Recall v₀ = Vol G t_j (vm.S t_j ω) = Vol G t_j s_j (by hS_j).
    have hv₀_eq : (v₀ : ℝ) = (TemporalGraph.volume G t_j s_j : ℝ) := by
      show (TemporalGraph.volume G t_j (vm.S t_j ω) : ℝ) = _
      rw [hS_j]
    -- Real-valued conversion of the excursion predicate.
    rcases hexc with hdown | hup
    · -- 2·Vol(min') < v₀. Then Vol(min') < v₀/2, so |Vol(min') - v₀| = v₀ - Vol(min') ≥ v₀/2.
      have hcast : (2 : ℝ) * (TemporalGraph.volume G (candidates.min' hne)
          (vm.S (candidates.min' hne) ω) : ℝ) <
          (v₀ : ℝ) := by exact_mod_cast hdown
      rw [hv₀_eq] at hcast
      have habs_ge :
          (TemporalGraph.volume G t_j s_j : ℝ) -
            (TemporalGraph.volume G (candidates.min' hne)
              (vm.S (candidates.min' hne) ω) : ℝ) ≥
          (1 / 2 : ℝ) * (TemporalGraph.volume G t_j s_j : ℝ) := by linarith
      have habs_eq : |(TemporalGraph.volume G (candidates.min' hne)
            (vm.S (candidates.min' hne) ω) : ℝ) -
          (TemporalGraph.volume G t_j s_j : ℝ)| =
          (TemporalGraph.volume G t_j s_j : ℝ) -
          (TemporalGraph.volume G (candidates.min' hne)
            (vm.S (candidates.min' hne) ω) : ℝ) := by
        rw [abs_of_nonpos (by linarith)]; ring
      rw [habs_eq]; exact habs_ge
    · -- 3·v₀ < 2·Vol(min'). Then Vol(min') > 3·v₀/2, so |Vol(min') - v₀| = Vol(min') - v₀ ≥ v₀/2.
      have hcast : (3 : ℝ) * (v₀ : ℝ) <
          2 * (TemporalGraph.volume G (candidates.min' hne)
            (vm.S (candidates.min' hne) ω) : ℝ) := by exact_mod_cast hup
      rw [hv₀_eq] at hcast
      have habs_ge :
          (TemporalGraph.volume G (candidates.min' hne)
              (vm.S (candidates.min' hne) ω) : ℝ) -
          (TemporalGraph.volume G t_j s_j : ℝ) ≥
          (1 / 2 : ℝ) * (TemporalGraph.volume G t_j s_j : ℝ) := by linarith
      have habs_eq : |(TemporalGraph.volume G (candidates.min' hne)
            (vm.S (candidates.min' hne) ω) : ℝ) -
          (TemporalGraph.volume G t_j s_j : ℝ)| =
          (TemporalGraph.volume G (candidates.min' hne)
              (vm.S (candidates.min' hne) ω) : ℝ) -
          (TemporalGraph.volume G t_j s_j : ℝ) := by
        rw [abs_of_nonneg (by linarith)]
      rw [habs_eq]; exact habs_ge
  · -- candidates.Nonempty is false: volumeExcursionTime = cap + 1, contradicting hexit_fired.
    rw [hvET_eq, dif_neg hne] at hexit_fired
    omega


/-- \label{lem:paper-good-step-from-calendar-window-guarantee}

**L98 — Paper-aligned good-step derivation from calendar-interval conductance bound.**

Given a calendar interval `[I_lo, I_hi]`, an admissible cut `s_j`, and the
per-interval MAX-form hypothesis
`φ_next ≤ maxSetConductanceOnInterval G I_lo I_hi s_j _`,
produces a witness `t' ∈ [t_j, I_hi]` with
`edgesBetween G t' s_j (univ\s_j) ≥ φ_next · vol(t_j, s_j)`,
provided `t_j ≤ I_lo`.

**Strategy.** Unfold `maxSetConductanceOnInterval` as a `Finset.sup'`; pick the
argmax `t' ∈ [I_lo, I_hi]` via `Finset.exists_mem_eq_sup'`. The hypothesis at
the maximizing time gives `φ_next ≤ (G.snapshot t').setConductance s_j`. Then
`t_j ≤ I_lo ≤ t'`, and `t' ≤ I_hi`. Convert the conductance inequality to
`edgesBetween G t' s_j (univ\s_j) ≥ φ_next · vol(t', s_j)` and then to
`φ_next · vol(t_j, s_j)` via `volume_fixed` (`FixedDegrees`). No `/4` factor:
this is the full-strength paper inequality from `3.1_case_1.tex:233-234`.
Pointwise existence comes directly from the max-form, with no averaging or
pigeonhole.

**Bridge at caller.** The L68 caller still consumes `hasWindowGuarantee G φ Δ`;
it derives `hcond` via `hasWindowGuarantee_le_maxSetConductanceOnInterval` at
`t₁ = I_lo` and rewrites the upper bound `I_lo + Δ - 1 = I_hi`.

**Difference from L95.** L95 takes a *pointwise embedded-interval* witness as a
hypothesis and produces the L76 shape. L98 produces the witness from the
*per-interval* max-form bound on `[I_lo, I_hi]`, using only the constraint
`t_j ≤ I_lo` to anchor the witness in `[t_j, I_hi]`.

**Depends on:** D1, D3, D4, D5, D24. -/
theorem paper_good_step_from_calendar_window_guarantee
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraphFixedDegree V)
    -- Per-interval conductance threshold and calendar interval `[I_lo, I_hi]`.
    (φ_next : ℝ) (I_lo I_hi : ℕ) (hI : I_lo ≤ I_hi)
    -- Admissible cut s_j (admissibility is encoded by the hypothesis hcond's
    -- per-interval MAX-form bound at s_j; no separate admissibility argument
    -- is needed here).
    (s_j : Finset V)
    -- Embedded time t_j is at or before the start of the interval.
    (t_j : ℕ) (ht_j_le : t_j ≤ I_lo)
    -- Per-interval MAX-form hypothesis (paper's `φ^{I_{j+1}}(s_j) ≥ φ_{j+1}`).
    (hcond : φ_next ≤
      TemporalGraph.maxSetConductanceOnInterval G I_lo (I_hi - I_lo + 1) s_j) :
    -- Conclusion: ∃ t' ∈ [t_j, I_hi], edgesBetween G t' s_j (univ\s_j) ≥ φ_next·vol(t_j, s_j)
    ∃ t', t_j ≤ t' ∧ t' ≤ I_hi ∧
        (TemporalGraph.edgesBetween G t' s_j (Finset.univ \ s_j) : ℝ) ≥
          φ_next * (TemporalGraph.volume G t_j s_j : ℝ) := by
  classical
  -- Extract the argmax `t'` of `(G.snapshot ·).setConductance s_j` over the window's index set
  -- `[I_lo, I_lo + ((I_hi - I_lo + 1) - 1)] = [I_lo, I_hi]`.
  obtain ⟨t', ht'_mem, ht'_max⟩ :=
    TemporalGraph.exists_mem_eq_maxSetConductanceOnInterval G I_lo (I_hi - I_lo + 1) s_j
  rw [Finset.mem_Icc] at ht'_mem
  obtain ⟨ht'_lo_I, ht'_hi⟩ := ht'_mem
  have ht'_hi_I : t' ≤ I_hi := by omega
  -- φ_next ≤ max = (G.snapshot t').setConductance s_j.
  have hphi : φ_next ≤ (G.snapshot t').setConductance s_j := by
    rwa [ht'_max] at hcond
  refine ⟨t', le_trans ht_j_le ht'_lo_I, ht'_hi_I, ?_⟩
  -- Volume time-invariance (FixedDegrees): vol(t_j, s_j) = vol(t', s_j).
  have hvol_eq : (TemporalGraph.volume G t_j s_j : ℝ) =
      (TemporalGraph.volume G t' s_j : ℝ) := by
    exact_mod_cast G.volume_fixed s_j t_j t'
  rw [hvol_eq]
  -- φ_next ≤ edgesBetween / vol(t', s_j); rearrange to φ_next · vol ≤ edgesBetween.
  unfold SimpleGraph.setConductance at hphi
  by_cases hvol0 : (TemporalGraph.volume G t' s_j : ℝ) = 0
  · rw [hvol0, mul_zero]
    exact_mod_cast Nat.zero_le _
  · have hvol_pos : (0 : ℝ) < TemporalGraph.volume G t' s_j :=
      lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hvol0)
    rw [le_div_iff₀ hvol_pos] at hphi
    exact hphi

/-- \label{lem:psi-chi-combined-drift-dispatch-on-fiber}

**L92 — Joint dispatch wrapper for L68's F_T sub-fiber; combines L90 + L91.**

For the indicator-TRUE sub-fiber `F_T` of L68 (where the `Pind` indicator
triggers `D_j = min(φ_j/2048, 1/2048)`), this lemma dispatches between
the L90 stable case and the L91 unstable case via an `Or` of bundle data
and concludes the F_T-shaped integrated drift bound

  `∫_{F_T} (α · Δψ + Δχ + D_j) dvm.μ ≤ 0`,

where `α = √vol(0, s_0) / d_min`, `Δψ = ψ(T_{j+1}) − ψ(T_j)`,
`Δχ = χ(T_{j+1}, S_{T_{j+1}}) − χ(T_j, S_{T_j})`, and
`D_j = min(φ_j/2048, 1/2048)`.

**Dispatch.** The caller supplies a 3-way disjunction
`(Case1Bundle ∨ Case2Bundle) ∨ UnstableBundle`:
* `Case1Bundle` = `(φ_j > 0, hgood_step, hLarge)` — the L96 bundle. The
  `hLarge` hypothesis is the paper's L30 lower bound on the edge sum
  (`E[Σ cutS | ℱ_{t_j}] ω > (φ_j/8)·Vol(t_j, s_j)` a.e. on `μ.restrict F_T`).
  Applies L96 to get `∫ (α·Δψ + Δχ) ≤ -(φ_j/2048)·μ(F_T)`, then `D_j ≤
  φ_j/2048` makes the constant term cancel.
* `Case2Bundle` = `(φ_j > 0, hgood_step, hedge_sum_small, hC2)` — the L90
  bundle. `hedge_sum_small` is the literal negation of `hLarge`'s strict
  inequality at threshold `(1/8)·Vol/(1/φ_j) = (φ_j/8)·Vol`. Applies L90
  to get `∫ (α·Δψ + Δχ) ≤ -(φ_j/2048)·μ(F_T)`, then `D_j ≤ φ_j/2048`
  cancels.
* `UnstableBundle` = `(hUnstable_F : F-restricted positive-form unstable
  hypothesis at the embedded stopping time `T_j`)`. Applies L91 to get
  `∫ (α·Δψ + Δχ) ≤ -(1/2048)·μ(F_T)`, then `D_j ≤ 1/2048` makes the
  constant term cancel.

**Why split stable into two cases?** L90's `hedge_sum_small` is the *upper*
bound on the edge sum, but the paper's `lem:prob-good-event` (L30) proves a
*lower* bound. They are negations at threshold `(φ_j/8)·Vol`. The L68 caller
dispatches stable→`hLarge` via `Classical.em`: in the hLarge branch, route
to L96 (LB path); in the ¬hLarge branch, ¬hLarge = `hedge_sum_small`, route
to L90 (UB path). This mirrors the paper's internal Case 1 / Case 2 split
in §3.1.

**Depends on:** L90 (`psi_down_drift_stable_from_IsStableInterval_on_fiber`),
L91 (`chi_down_drift_voter_unstable_from_NotIsStableInterval_on_fiber`),
L96 (`psi_chi_combined_drift_case1_from_largeEdgeSum_on_fiber`). -/
theorem psi_chi_combined_drift_dispatch_on_fiber
    {Ω : Type*} [MeasurableSpace Ω]
    (G : TemporalGraphFixedDegree V)
    (vm : G.VoterModelAbstract 2 Ω)
    (d_min : ℕ) (hd : d_min = G.minDegreeAt 0) (hd_pos : 0 < d_min)
    -- Initial set s_0, current fiber state s_j ≠ ∅, realized time t_j
    (s_0 : Finset V) (hs_0_ne : s_0.Nonempty)
    (s_j : Finset V) (hs_j_ne : s_j.Nonempty)
    (t_j : ℕ)
    -- Embedded chain parameters
    (Δ : ℕ → ℕ) (hΔ_pos : ∀ k, 1 ≤ Δ k) (j : ℕ)
    -- Volume sub-fiber bound (from L68's indicator-TRUE selector at index j)
    (hvol_lt : ((G.snapshot 0).volume s_j : ℝ) <
      8 * ((G.snapshot 0).volume s_0 : ℝ))
    -- Fiber F_T: measurable in ℱ_{t_j}, with T_j = t_j and S_{t_j} = s_j on F_T
    (F_T : Set Ω)
    (hF_T_meas : MeasurableSet[vm.ℱ t_j] F_T)
    (hF_T_eq : ∀ ω ∈ F_T, embeddedChainTime G.toTemporalGraph vm Δ j ω = t_j)
    (hF_S_eq : ∀ ω ∈ F_T, vm.S t_j ω = s_j)
    -- t_j is within the cap for the (j+1)-th embedded interval (paper-tight cap)
    (hT_cap : t_j ≤ (∑ k ∈ Finset.range (j + 1), Δ k) - 1)
    -- φ_j ∈ [0, 1] (paper-side conductance lower bound)
    (φ_j : ℝ) (hφ_j_nn : 0 ≤ φ_j)
    -- Or-dispatch: (Case1 ∨ Case2) ∨ unstable. The stable branch is split
    -- internally into Case 1 (large edge sum, paper's L30 LB) and Case 2
    -- (small edge sum, the existing L76/L90 path). See L96 docstring.
    (hdispatch :
      -- (Case1 ∨ Case2): stable cases — outer wrap so the `∨`s nest correctly.
      (-- Case 1 bundle (L96): φ_j > 0, large edge sum on F_T
        -- Note: `hgood_step` removed from this bundle since L96 doesn't use it — `hLarge` is the
        -- driver. This also relieves the caller from needing a tight-cap witness.
        (0 < φ_j ∧
          (∀ᵐ ω ∂((vm.μ : Measure Ω).restrict F_T),
            ((vm.μ : Measure Ω)[fun ω' => ∑ k ∈ Finset.Icc t_j
                (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω' - 1),
              (vm.cutS k ω' : ℝ) | vm.ℱ t_j]) ω
              > (1 / 8 : ℝ) * ((G.snapshot t_j).volume s_j : ℝ) / (1 / φ_j)))
        ∨
        -- Case 2 bundle (L90): φ_j > 0, good-step, F_T-restricted hedge-sum
        -- small (threshold (1/8); F_T-restricted to match L68's
        -- info shape), F_T-restricted hC2.
        (0 < φ_j ∧
          (∃ t', t_j ≤ t' ∧ t' ≤ (∑ k ∈ Finset.range (j + 1), Δ k) - 1 ∧
            (G.edgesBetween t' s_j (Finset.univ \ s_j) : ℝ) ≥
              φ_j * ((G.snapshot t_j).volume s_j : ℝ)) ∧
          (∀ᵐ ω ∂((vm.μ : Measure Ω).restrict F_T),
            ((vm.μ : Measure Ω)[fun ω' => ∑ k ∈ Finset.Icc t_j
                (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω' - 1),
              (vm.cutS k ω' : ℝ) | vm.ℱ t_j]) ω
              ≤ (1 / 8 : ℝ) * ((G.snapshot t_j).volume s_j : ℝ) / (1 / φ_j)) ∧
          (∀ t', t_j ≤ t' → t' ≤ (∑ k ∈ Finset.range (j + 1), Δ k) - 1 →
            Case2Hypotheses G.toTemporalGraph vm s_j t_j
              (embeddedChainTime G.toTemporalGraph vm Δ (j + 1)) t' φ_j F_T)))
      ∨
      -- Unstable bundle (L91): F_T-restricted positive-form unstable hypothesis.
      (∃ (hT_stop : IsStoppingTime vm.ℱ
            (fun ω => (embeddedChainTime G.toTemporalGraph vm Δ j ω : ℕ∞))),
        ∀ᵐ ω ∂((vm.μ : Measure Ω).restrict F_T),
          ((vm.μ : Measure Ω)[fun ω' =>
              |vm.volS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω') ω' -
                vm.volS (embeddedChainTime G.toTemporalGraph vm Δ j ω') ω'|
              | hT_stop.measurableSpace]) ω
            ≥ (1 / 8 : ℝ) * vm.volS (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω)) :
    -- Conclusion: integrated F_T-shaped combined drift (with D_j) ≤ 0.
    ∫ ω in F_T,
      ((Real.sqrt ((G.snapshot 0).volume s_0 : ℝ) / d_min)
          * (vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω
              - vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω)
        + (G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
              (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω)
          - G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ j ω)
              (vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω))
        + min (φ_j / 2048) (1 / 2048 : ℝ))
      ∂vm.μ ≤ 0 := by
  classical
  haveI hprob : IsProbabilityMeasure (vm.μ : Measure Ω) := inferInstance
  -- Top-level measurability of F_T.
  have hF_T_meas_top : MeasurableSet F_T := vm.ℱ.le t_j _ hF_T_meas
  -- Abbreviation: α := √vol(0, s_0)/d_min ≥ 0.
  set α : ℝ := Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) / d_min with hα_def
  have hα_nn : (0 : ℝ) ≤ α :=
    div_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _)
  -- μ(F_T) abbreviation (as a real).
  set μFT : ℝ := ((vm.μ : Measure Ω) F_T).toReal with hμFT_def
  have hμFT_nn : 0 ≤ μFT := ENNReal.toReal_nonneg
  -- D_j abbreviation: D_j := min(φ_j/2048, 1/2048).
  set Dj : ℝ := min (φ_j / 2048) (1 / 2048 : ℝ) with hDj_def
  have hDj_nn : 0 ≤ Dj := by
    refine le_min ?_ (by norm_num)
    exact div_nonneg hφ_j_nn (by norm_num)
  have hDj_le_quarter : Dj ≤ φ_j / 2048 := min_le_left _ _
  have hDj_le_tenth : Dj ≤ (1 / 2048 : ℝ) := min_le_right _ _
  -- ── Integrability scaffolding (shared between the two branches) ───────────────
  -- Universe-bound Vu for measurability/integrability.
  set Vu : ℕ := TemporalGraph.volume G.toTemporalGraph 0 (Finset.univ : Finset V) with hVu_def
  have hVol_le_univ : ∀ t S, TemporalGraph.volume G.toTemporalGraph t S ≤ Vu := by
    intro t S
    have h1 : TemporalGraph.volume G.toTemporalGraph t S ≤ TemporalGraph.volume G.toTemporalGraph t Finset.univ := by
      unfold TemporalGraph.volume SimpleGraph.volume
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have h2 : TemporalGraph.volume G.toTemporalGraph t Finset.univ = Vu :=
      G.volume_fixed _ _ _
    exact h1.trans_eq h2
  -- Stopping-time scaffolding (for measurability of ψ(T_k), χ(T_k, S_{T_k})).
  have hS_meas_ℱ : ∀ t, @Measurable Ω (Finset V) (vm.ℱ t) ⊤ (vm.S t) := fun t =>
    (measurable_of_countable (fun A => VoterModel.minoritySet G.toTemporalGraph t A)).comp
      (vm.A_stronglyAdapted t).measurable
  have hT_stop_all : ∀ k,
      IsStoppingTime vm.ℱ (fun ω => (embeddedChainTime G.toTemporalGraph vm Δ k ω : ℕ∞)) := fun k =>
    embeddedChainTime_isStoppingTime G.toTemporalGraph vm Δ hS_meas_ℱ k
  have hT_meas : ∀ k, Measurable (embeddedChainTime G.toTemporalGraph vm Δ k) := by
    intro k s _
    rw [show (embeddedChainTime G.toTemporalGraph vm Δ k) ⁻¹' s =
        ⋃ u ∈ s, {w | embeddedChainTime G.toTemporalGraph vm Δ k w = u} from by ext ω; simp]
    refine MeasurableSet.biUnion (Set.to_countable s) (fun u _ => ?_)
    have heq2 : {w : Ω | embeddedChainTime G.toTemporalGraph vm Δ k w = u} =
        {w | (embeddedChainTime G.toTemporalGraph vm Δ k w : ℕ∞) = ↑u} := by
      ext w
      exact ⟨fun heq => by exact_mod_cast heq, fun heq => by exact_mod_cast heq⟩
    rw [heq2]; exact vm.ℱ.le u _ ((hT_stop_all k).measurableSet_eq u)
  have hψE_meas : ∀ k, Measurable (fun ω => vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) := by
    intro k S hS
    rw [show (fun ω => vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) ⁻¹' S =
        ⋃ t : ℕ, (embeddedChainTime G.toTemporalGraph vm Δ k) ⁻¹' {t} ∩ (vm.psiS t) ⁻¹' S from by
      ext ω
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_singleton_iff]
      refine ⟨fun h => ⟨embeddedChainTime G.toTemporalGraph vm Δ k ω, rfl, h⟩, ?_⟩
      rintro ⟨t, heq, hp⟩
      show vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω ∈ S
      rw [heq]; exact hp]
    refine MeasurableSet.iUnion (fun t => ?_)
    have hpsi_meas : Measurable (vm.psiS t) := by
      have h1 : Measurable (fun ω => (TemporalGraph.volume G.toTemporalGraph t (vm.S t ω) : ℝ)) := by
        have hvol_fn : Measurable
            (fun s : Finset V => (TemporalGraph.volume G.toTemporalGraph t s : ℝ)) :=
          measurable_of_countable _
        have hS_t : Measurable (vm.S t) := fun S hS => vm.ℱ.le t _ ((hS_meas_ℱ t) hS)
        exact hvol_fn.comp hS_t
      show Measurable (fun ω => Real.sqrt (TemporalGraph.volume G.toTemporalGraph t (vm.S t ω) : ℝ))
      exact Real.continuous_sqrt.measurable.comp h1
    exact (hT_meas k (measurableSet_singleton _)).inter (hpsi_meas hS)
  have hχE_meas : ∀ k, Measurable (fun ω => G.chiPotential
      (embeddedChainTime G.toTemporalGraph vm Δ k ω) (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω)) := by
    intro k S hS
    rw [show (fun ω => G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ k ω)
        (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω)) ⁻¹' S =
        ⋃ t : ℕ, (embeddedChainTime G.toTemporalGraph vm Δ k) ⁻¹' {t} ∩
          (fun ω => G.chiPotential t (vm.S t ω)) ⁻¹' S from by
      ext ω
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_singleton_iff]
      refine ⟨fun h => ⟨embeddedChainTime G.toTemporalGraph vm Δ k ω, rfl, h⟩, ?_⟩
      rintro ⟨t, heq, hp⟩
      show G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ k ω)
        (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) ∈ S
      rw [heq]; exact hp]
    refine MeasurableSet.iUnion (fun t => ?_)
    have hchi_meas : Measurable (fun ω => G.chiPotential t (vm.S t ω)) := by
      have hchi_fn : Measurable (fun s : Finset V => G.chiPotential t s) :=
        measurable_of_countable _
      have hS_t : Measurable (vm.S t) := fun S hS => vm.ℱ.le t _ ((hS_meas_ℱ t) hS)
      exact hchi_fn.comp hS_t
    exact (hT_meas k (measurableSet_singleton _)).inter (hchi_meas hS)
  -- Combined integrand `g(ω) := α · Δψ + Δχ` is integrable (bounded by `α·√Vu + |log(1+Vu)|`).
  set g : Ω → ℝ := fun ω =>
    α * (vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω
            - vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω)
      + (G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
            (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω)
        - G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ j ω)
            (vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω)) with hg_def
  have hg_meas : Measurable g := by
    refine Measurable.add ?_ ?_
    · exact ((hψE_meas (j + 1)).sub (hψE_meas j)).const_mul _
    · exact (hχE_meas (j + 1)).sub (hχE_meas j)
  -- Bound: |g ω| ≤ 2·α·√Vu + 2·|log(1 + Vu)|.
  set Cg : ℝ := 2 * α * Real.sqrt (Vu : ℝ) + 2 * |Real.log (1 + (Vu : ℝ))| with hCg_def
  have hψ_nn_k : ∀ k ω, 0 ≤ vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω := fun k ω => by
    show TemporalGraph.potential G.toTemporalGraph _ _ ≥ 0
    exact Real.sqrt_nonneg _
  have hψ_bnd_k : ∀ k ω, vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω ≤ Real.sqrt (Vu : ℝ) :=
    fun k ω => by
      show TemporalGraph.potential G.toTemporalGraph _ _ ≤ _
      apply Real.sqrt_le_sqrt
      exact_mod_cast hVol_le_univ _ _
  have hχ_nn_k : ∀ k ω, 0 ≤ G.chiPotential
      (embeddedChainTime G.toTemporalGraph vm Δ k ω) (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) := fun k ω => by
    unfold TemporalGraphFixedDegree.chiPotential TemporalGraph.chiPotential
    apply Real.log_nonneg
    have h0 : (0 : ℝ) ≤ (TemporalGraph.volume G.toTemporalGraph (embeddedChainTime G.toTemporalGraph vm Δ k ω)
        (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) : ℝ) := Nat.cast_nonneg _
    linarith
  have hχ_bnd_k : ∀ k ω, G.chiPotential
      (embeddedChainTime G.toTemporalGraph vm Δ k ω) (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) ≤
      Real.log (1 + (Vu : ℝ)) := fun k ω => by
    unfold TemporalGraphFixedDegree.chiPotential TemporalGraph.chiPotential
    have h1 : (0 : ℝ) < 1 + (TemporalGraph.volume G.toTemporalGraph (embeddedChainTime G.toTemporalGraph vm Δ k ω)
        (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) : ℝ) := by
      have h0 : (0 : ℝ) ≤ (TemporalGraph.volume G.toTemporalGraph (embeddedChainTime G.toTemporalGraph vm Δ k ω)
          (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) : ℝ) := Nat.cast_nonneg _
      linarith
    apply Real.log_le_log h1
    have h := hVol_le_univ (embeddedChainTime G.toTemporalGraph vm Δ k ω)
      (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω)
    have h2 : (TemporalGraph.volume G.toTemporalGraph (embeddedChainTime G.toTemporalGraph vm Δ k ω)
        (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) : ℝ) ≤ (Vu : ℝ) := by exact_mod_cast h
    linarith
  have hsqrtVu_nn : 0 ≤ Real.sqrt (Vu : ℝ) := Real.sqrt_nonneg _
  have habs_log_nn : 0 ≤ |Real.log (1 + (Vu : ℝ))| := abs_nonneg _
  have hlog_le : Real.log (1 + (Vu : ℝ)) ≤ |Real.log (1 + (Vu : ℝ))| := le_abs_self _
  have hlog_ge : -|Real.log (1 + (Vu : ℝ))| ≤ Real.log (1 + (Vu : ℝ)) := neg_abs_le _
  have hg_abs : ∀ ω, |g ω| ≤ Cg := by
    intro ω
    have h1 := hψ_nn_k (j + 1) ω
    have h2 := hψ_bnd_k (j + 1) ω
    have h3 := hψ_nn_k j ω
    have h4 := hψ_bnd_k j ω
    have h5 := hχ_nn_k (j + 1) ω
    have h6 := hχ_bnd_k (j + 1) ω
    have h7 := hχ_nn_k j ω
    have h8 := hχ_bnd_k j ω
    have hαmul1 := mul_nonneg hα_nn h1
    have hαmul3 := mul_nonneg hα_nn h3
    have hαmul2 : α * vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω ≤
        α * Real.sqrt (Vu : ℝ) :=
      mul_le_mul_of_nonneg_left h2 hα_nn
    have hαmul4 : α * vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω ≤
        α * Real.sqrt (Vu : ℝ) :=
      mul_le_mul_of_nonneg_left h4 hα_nn
    simp only [hg_def, hCg_def]
    rw [abs_le]
    refine ⟨?_, ?_⟩ <;> linarith
  have hg_int : Integrable g vm.μ := by
    refine MeasureTheory.Integrable.of_bound (C := Cg) hg_meas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs]; exact hg_abs ω
  -- ── Algebraic identity: ∫_{F_T} (g + Dj) = ∫_{F_T} g + Dj · μFT.
  have hint_split : ∫ ω in F_T, (g ω + Dj) ∂vm.μ =
      ∫ ω in F_T, g ω ∂vm.μ + Dj * μFT := by
    rw [integral_add hg_int.integrableOn (integrable_const _), setIntegral_const]
    show ∫ ω in F_T, g ω ∂vm.μ + ((vm.μ : Measure Ω) F_T).toReal • Dj =
         ∫ ω in F_T, g ω ∂vm.μ + Dj * μFT
    rw [smul_eq_mul, mul_comm]
  -- Rewrite goal LHS to expose `g ω + Dj`. After the `set α := …`, `set Dj := …`
  -- abbreviations, the goal's integrand is defeq to `g ω + Dj` (where `g`'s body
  -- references the same `α`).
  change ∫ ω in F_T, (g ω + Dj) ∂vm.μ ≤ 0
  rw [hint_split]
  -- ── Dispatch on the 3-way disjunction: (Case1 ∨ Case2) ∨ Unstable.
  rcases hdispatch with (hCase1 | hCase2) | ⟨hT_stop, hUnstable_F⟩
  · -- ── Case 1 (large edge sum): apply L96.
    obtain ⟨hφ_j_pos, hLarge⟩ := hCase1
    have hL96 := psi_chi_combined_drift_case1_from_largeEdgeSum_on_fiber
      G vm d_min hd hd_pos s_0 hs_0_ne s_j hs_j_ne t_j Δ hΔ_pos j hvol_lt
      F_T hF_T_meas hF_T_eq hF_S_eq hT_cap φ_j hφ_j_pos hLarge
    -- hL96 : ∫_{F_T} g ≤ -(φ_j/2048) · μFT.
    have hL96' : ∫ ω in F_T, g ω ∂vm.μ ≤ -(φ_j / 2048) * μFT := by
      exact hL96
    -- D_j · μFT ≤ (φ_j/2048) · μFT.
    have hDj_mul : Dj * μFT ≤ (φ_j / 2048) * μFT :=
      mul_le_mul_of_nonneg_right hDj_le_quarter hμFT_nn
    have hsum : ∫ ω in F_T, g ω ∂vm.μ + Dj * μFT ≤
        -(φ_j / 2048) * μFT + (φ_j / 2048) * μFT :=
      add_le_add hL96' hDj_mul
    refine le_trans hsum ?_
    have : -(φ_j / 2048) * μFT + (φ_j / 2048) * μFT = 0 := by ring
    linarith
  · -- ── Case 2 (small edge sum / stable): apply L90.
    obtain ⟨hφ_j_pos, hgood_step, hedge_sum_small, hC2⟩ := hCase2
    have hL90 := psi_down_drift_stable_from_IsStableInterval_on_fiber
      G vm d_min hd hd_pos s_0 hs_0_ne s_j hs_j_ne t_j Δ hΔ_pos j hvol_lt
      F_T hF_T_meas hF_T_eq hF_S_eq hT_cap φ_j hφ_j_pos
      hgood_step hedge_sum_small hC2
    -- hL90 : ∫_{F_T} g ≤ -(φ_j/2048) · μFT.
    have hL90' : ∫ ω in F_T, g ω ∂vm.μ ≤ -(φ_j / 2048) * μFT := by
      exact hL90
    -- D_j · μFT ≤ (φ_j/2048) · μFT.
    have hDj_mul : Dj * μFT ≤ (φ_j / 2048) * μFT :=
      mul_le_mul_of_nonneg_right hDj_le_quarter hμFT_nn
    -- Sum: ∫_{F_T} g + D_j · μFT ≤ -(φ_j/2048) μFT + (φ_j/2048) μFT = 0.
    have hsum : ∫ ω in F_T, g ω ∂vm.μ + Dj * μFT ≤
        -(φ_j / 2048) * μFT + (φ_j / 2048) * μFT :=
      add_le_add hL90' hDj_mul
    refine le_trans hsum ?_
    have : -(φ_j / 2048) * μFT + (φ_j / 2048) * μFT = 0 := by ring
    linarith
  · -- ── Unstable case: apply L91.
    have hL91 := chi_down_drift_voter_unstable_from_NotIsStableInterval_on_fiber
      G vm d_min s_0 s_j hs_j_ne t_j Δ hΔ_pos j
      F_T hF_T_meas hF_T_eq hF_S_eq hT_cap hT_stop hUnstable_F
    -- hL91 : ∫_{F_T} g ≤ -(1/2048) · μFT.
    have hL91' : ∫ ω in F_T, g ω ∂vm.μ ≤ -(1 / 2048 : ℝ) * μFT := by
      exact hL91
    -- D_j · μFT ≤ (1/2048) · μFT.
    have hDj_mul : Dj * μFT ≤ (1 / 2048 : ℝ) * μFT :=
      mul_le_mul_of_nonneg_right hDj_le_tenth hμFT_nn
    -- Sum: ∫_{F_T} g + D_j · μFT ≤ -(1/2048) μFT + (1/2048) μFT = 0.
    have hsum : ∫ ω in F_T, g ω ∂vm.μ + Dj * μFT ≤
        -(1 / 2048 : ℝ) * μFT + (1 / 2048 : ℝ) * μFT :=
      add_le_add hL91' hDj_mul
    refine le_trans hsum ?_
    have : -(1 / 2048 : ℝ) * μFT + (1 / 2048 : ℝ) * μFT = 0 := by ring
    linarith


end VoterModel
