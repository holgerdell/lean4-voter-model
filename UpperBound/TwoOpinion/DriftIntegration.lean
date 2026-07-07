module

public import UpperBound.LogMartingale
import VoterProcess.Expectation
public import TemporalGraph.Conductance

public import TemporalGraph.Degree
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Covering.Besicovitch
import TemporalGraph.Basic
import UpperBound.PotentialDecrease.Drift
import UpperBound.TwoOpinion.ConditionalModel
import UpperBound.TwoOpinion.FiberDrift


@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

namespace VoterModel

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]

/-! ## Main results

L68 F_T-closure bridges and the integrated combined drift:
`condExp_eq_of_eq_on_fiber`, `F_T_exit_bound`, integrability helpers,
`psi_chi_combined_F_T_closure_on_fiber`, `psi_chi_combined_setIntegral_on_fiber_le`,
`psi_chi_combined_drift_integrated`. -/

/-! ### Bridges for L68's F_T sub-fiber closure -/

/-- **Helper: integrand-bridge on a fiber.** If two integrable functions agree
pointwise on `F ∈ ℱ_t`, their conditional expectations w.r.t. `ℱ_t` are a.e. equal
on `μ.restrict F`. Uses `condExp_indicator` + `condExp_congr_ae`. -/
private lemma condExp_eq_of_eq_on_fiber
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (μ : Measure Ω) [SigmaFinite μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    [SigmaFinite (μ.trim hm)]
    {F : Set Ω} (hF : MeasurableSet[m] F)
    {f1 f2 : Ω → ℝ}
    (hf1_int : Integrable f1 μ) (hf2_int : Integrable f2 μ)
    (h_eq_on_F : ∀ ω ∈ F, f1 ω = f2 ω) :
    μ[f1 | m] =ᵐ[μ.restrict F] μ[f2 | m] := by
  classical
  have hF_top : @MeasurableSet Ω mΩ F := hm F hF
  -- 1_F · f1 = 1_F · f2 (pointwise).
  have h_ind_eq : Set.indicator F f1 = Set.indicator F f2 := by
    funext ω
    by_cases hω : ω ∈ F
    · simp [Set.indicator_of_mem hω, h_eq_on_F ω hω]
    · simp [Set.indicator_of_notMem hω]
  -- E[1_F · f1 | m] = E[1_F · f2 | m] (definitional, since the inputs are equal).
  have h_condExp_ind_eq :
      μ[Set.indicator F f1 | m] =ᵐ[μ] μ[Set.indicator F f2 | m] := by
    rw [h_ind_eq]
  -- Use condExp_indicator both sides.
  have h_left : μ[Set.indicator F f1 | m] =ᵐ[μ] Set.indicator F (μ[f1 | m]) :=
    condExp_indicator hf1_int hF
  have h_right : μ[Set.indicator F f2 | m] =ᵐ[μ] Set.indicator F (μ[f2 | m]) :=
    condExp_indicator hf2_int hF
  -- 1_F · E[f1 | m] =ᵐ 1_F · E[f2 | m].
  have h_ind_cE : Set.indicator F (μ[f1 | m]) =ᵐ[μ] Set.indicator F (μ[f2 | m]) :=
    (h_left.symm.trans h_condExp_ind_eq).trans h_right
  -- Descend to restrict.
  have h_restrict_eq : μ[f1 | m] =ᵐ[μ.restrict F] μ[f2 | m] := by
    rw [@Filter.EventuallyEq, @ae_restrict_iff' _ mΩ _ _ _ hF_top]
    filter_upwards [h_ind_cE] with ω hω hin
    have h1 : Set.indicator F (μ[f1 | m]) ω = μ[f1 | m] ω := Set.indicator_of_mem hin _
    have h2 : Set.indicator F (μ[f2 | m]) ω = μ[f2 | m] ω := Set.indicator_of_mem hin _
    rw [← h1, ← h2]
    exact hω
  exact h_restrict_eq

/-- **Bridge 2 (L68 F_T-closure helper).** F_T-restricted exit-time bound for the
`Case2Hypotheses.exit` field. Direct lift of L94 (per-ω) to the `μ.restrict F_T` form. -/
private theorem F_T_exit_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (G : TemporalGraph V) (vm : TemporalGraph.VoterModelAbstract G 2 Ω)
    (s_j : Finset V) (t_j : ℕ)
    (Δ : ℕ → ℕ) (j : ℕ)
    (F_T : Set Ω)
    (hF_T_meas : MeasurableSet[vm.ℱ t_j] F_T)
    (hF_T_T : ∀ ω ∈ F_T, embeddedChainTime G vm Δ j ω = t_j)
    (hF_T_S : ∀ ω ∈ F_T, vm.S t_j ω = s_j)
    (t' : ℕ) (ht'_le_cap : t' ≤ (∑ k ∈ Finset.range (j + 1), Δ k) - 1) :
    ∀ᵐ ω ∂((vm.μ : Measure Ω).restrict F_T), embeddedChainTime G vm Δ (j + 1) ω ≤ t' →
      (1 / 2 : ℝ) * (TemporalGraph.volume G t_j s_j : ℝ)
        ≤ |(TemporalGraph.volume G (embeddedChainTime G vm Δ (j + 1) ω)
            (vm.S (embeddedChainTime G vm Δ (j + 1) ω) ω) : ℝ)
            - (TemporalGraph.volume G t_j s_j : ℝ)| := by
  classical
  have hF_T_meas_top : MeasurableSet F_T := vm.ℱ.le t_j _ hF_T_meas
  rw [ae_restrict_iff' hF_T_meas_top]
  refine ae_of_all _ ?_
  intro ω hω hT_next_le
  exact hexit_from_volumeExcursionTime_on_fiber G vm Δ j t_j s_j _ rfl ω
    (hF_T_T ω hω) (hF_T_S ω hω) (le_trans hT_next_le ht'_le_cap)


/-- **Helper: integrability of the L83/L84 dev integrand.** Both
`|vm.volS T_{j+1} - vm.volS T_j|` (L83 form) and
`|vol(T_{j+1}, S_{T_{j+1}}) - vol(t_j, s_j)|` (L84 form) are integrable via the
`voter_integrable_comp_A` + `Set.indicator {T_{j+1} = k}` decomposition. -/
private lemma volDev_integrable
    {Ω : Type*} [MeasurableSpace Ω]
    (G : TemporalGraph V) (vm : TemporalGraph.VoterModelAbstract G 2 Ω)
    (Δ : ℕ → ℕ) (j : ℕ) (c : ℝ) :
    Integrable (fun ω =>
      |(TemporalGraph.volume G (embeddedChainTime G vm Δ (j + 1) ω)
            (vm.S (embeddedChainTime G vm Δ (j + 1) ω) ω) : ℝ)
        - c|) vm.μ := by
  classical
  set cap := (∑ k ∈ Finset.range (j + 1), Δ k) - 1 with hcap_def
  have hvolInt : ∀ k, Integrable (fun ω => (TemporalGraph.volume G k (vm.S k ω) : ℝ)) vm.μ := by
    intro k
    have hA_meas : @Measurable Ω (Finset V) _ ⊤ (vm.opinionZeroSet k) :=
      fun s _ => vm.A_meas k _ ⟨s, trivial, rfl⟩
    set f : Finset V → ℝ := fun s' => (TemporalGraph.volume G k (minoritySet G k s') : ℝ)
    have hbase : Integrable (fun ω => f (vm.opinionZeroSet k ω)) vm.μ :=
      Integrable.of_bound
        (measurable_of_finite f |>.comp hA_meas).aestronglyMeasurable
        (∑ s : Finset V, ‖f s‖)
        (ae_of_all _ fun ω =>
          Finset.single_le_sum (fun s _ => norm_nonneg (f s)) (Finset.mem_univ (vm.opinionZeroSet k ω)))
    exact hbase.congr (Filter.Eventually.of_forall fun ω' => by simp [TemporalGraph.VoterModelAbstract.S, f])
  have hS_meas : ∀ t, @Measurable Ω (Finset V) (vm.ℱ t) ⊤ (vm.S t) := fun t =>
    (measurable_of_countable (fun A => VoterModel.minoritySet G t A)).comp
      (vm.A_stronglyAdapted t).measurable
  have hT_stop : IsStoppingTime vm.ℱ (fun ω => (embeddedChainTime G vm Δ (j + 1) ω : ℕ∞)) :=
    embeddedChainTime_isStoppingTime G vm Δ hS_meas (j + 1)
  have hT_next_bound : ∀ ω, embeddedChainTime G vm Δ (j + 1) ω ≤ cap + 1 := fun ω => by
    show volumeExcursionTime G vm (embeddedChainTime G vm Δ j ω) cap ω ≤ cap + 1
    exact volumeExcursionTime_le_succ G vm _ _ ω
  have hTnext_eq_meas : ∀ k, MeasurableSet {ω | embeddedChainTime G vm Δ (j + 1) ω = k} := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have : {ω | embeddedChainTime G vm Δ (j + 1) ω = 0} =
          {ω | (embeddedChainTime G vm Δ (j + 1) ω : ℕ∞) ≤ 0} := by ext ω; simp
      rw [this]; exact vm.ℱ.le 0 _ (hT_stop 0)
    · have : {ω | embeddedChainTime G vm Δ (j + 1) ω = k} =
          {ω | (embeddedChainTime G vm Δ (j + 1) ω : ℕ∞) ≤ ↑k} \
          {ω | (embeddedChainTime G vm Δ (j + 1) ω : ℕ∞) ≤ ↑(k - 1)} := by
        ext ω; simp only [Set.mem_setOf_eq, Set.mem_sdiff, ENat.coe_le_coe]; omega
      rw [this]
      exact (vm.ℱ.le k _ (hT_stop k)).diff (vm.ℱ.le (k - 1) _ (hT_stop (k - 1)))
  have hvolTnext_int : Integrable
      (fun ω => (TemporalGraph.volume G (embeddedChainTime G vm Δ (j + 1) ω)
        (vm.S (embeddedChainTime G vm Δ (j + 1) ω) ω) : ℝ)) vm.μ := by
    have heq : (fun ω => (TemporalGraph.volume G (embeddedChainTime G vm Δ (j + 1) ω)
          (vm.S (embeddedChainTime G vm Δ (j + 1) ω) ω) : ℝ)) = fun ω =>
        ∑ k ∈ Finset.range (cap + 2),
          Set.indicator {ω | embeddedChainTime G vm Δ (j + 1) ω = k}
            (fun ω => (TemporalGraph.volume G k (vm.S k ω) : ℝ)) ω := by
      funext ω
      rw [Finset.sum_eq_single (embeddedChainTime G vm Δ (j + 1) ω)]
      · simp [Set.indicator]
      · intro k _ hk; simp [Set.indicator, Ne.symm hk]
      · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le (hT_next_bound ω))) h
    rw [heq]
    exact integrable_finsetSum _ fun k _ => (hvolInt k).indicator (hTnext_eq_meas k)
  exact (hvolTnext_int.sub (integrable_const _)).abs

/-- **Helper: integrability of the L83-form integrand.**
`|vm.volS T_{j+1} - vm.volS T_j|` is integrable via per-stopping-time decomposition. -/
private lemma volS_diff_integrable
    {Ω : Type*} [MeasurableSpace Ω]
    (G : TemporalGraph V) (vm : TemporalGraph.VoterModelAbstract G 2 Ω)
    (Δ : ℕ → ℕ) (hΔ_pos : ∀ k, 1 ≤ Δ k) (j : ℕ) :
    Integrable (fun ω =>
      |vm.volS (embeddedChainTime G vm Δ (j + 1) ω) ω -
        vm.volS (embeddedChainTime G vm Δ j ω) ω|) vm.μ := by
  classical
  have hvolInt : ∀ k, Integrable (fun ω => (TemporalGraph.volume G k (vm.S k ω) : ℝ)) vm.μ := by
    intro k
    have hA_meas : @Measurable Ω (Finset V) _ ⊤ (vm.opinionZeroSet k) :=
      fun s _ => vm.A_meas k _ ⟨s, trivial, rfl⟩
    set f : Finset V → ℝ := fun s' => (TemporalGraph.volume G k (minoritySet G k s') : ℝ)
    have hbase : Integrable (fun ω => f (vm.opinionZeroSet k ω)) vm.μ :=
      Integrable.of_bound
        (measurable_of_finite f |>.comp hA_meas).aestronglyMeasurable
        (∑ s : Finset V, ‖f s‖)
        (ae_of_all _ fun ω =>
          Finset.single_le_sum (fun s _ => norm_nonneg (f s)) (Finset.mem_univ (vm.opinionZeroSet k ω)))
    exact hbase.congr (Filter.Eventually.of_forall fun ω' => by simp [TemporalGraph.VoterModelAbstract.S, f])
  have hS_meas : ∀ t, @Measurable Ω (Finset V) (vm.ℱ t) ⊤ (vm.S t) := fun t =>
    (measurable_of_countable (fun A => VoterModel.minoritySet G t A)).comp
      (vm.A_stronglyAdapted t).measurable
  set cap := (∑ k ∈ Finset.range (j + 1), Δ k) - 1 with hcap_def
  have hT_stop_jp1 : IsStoppingTime vm.ℱ
      (fun ω => (embeddedChainTime G vm Δ (j + 1) ω : ℕ∞)) :=
    embeddedChainTime_isStoppingTime G vm Δ hS_meas (j + 1)
  have hT_stop_j : IsStoppingTime vm.ℱ
      (fun ω => (embeddedChainTime G vm Δ j ω : ℕ∞)) :=
    embeddedChainTime_isStoppingTime G vm Δ hS_meas j
  have hT_next_bound : ∀ ω, embeddedChainTime G vm Δ (j + 1) ω ≤ cap + 1 := fun ω => by
    show volumeExcursionTime G vm (embeddedChainTime G vm Δ j ω) cap ω ≤ cap + 1
    exact volumeExcursionTime_le_succ G vm _ _ ω
  -- T_j bound via embeddedChainTime_le_sum_early + arithmetic (cap + 1 = ∑ range(j+1) Δ).
  have hT_j_bound : ∀ ω, embeddedChainTime G vm Δ j ω ≤ cap + 1 := fun ω => by
    have hle := embeddedChainTime_le_sum_early G vm Δ hΔ_pos j ω
    have hpos : 1 ≤ ∑ ℓ ∈ Finset.range (j + 1), Δ ℓ := by
      have h0 : Δ 0 ≤ ∑ ℓ ∈ Finset.range (j + 1), Δ ℓ :=
        Finset.single_le_sum (f := Δ) (fun _ _ => Nat.zero_le _)
          (Finset.mem_range.mpr (by omega))
      exact le_trans (hΔ_pos 0) h0
    omega
  have hTnext_eq_meas : ∀ k, MeasurableSet
      {ω | embeddedChainTime G vm Δ (j + 1) ω = k} := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have : {ω | embeddedChainTime G vm Δ (j + 1) ω = 0} =
          {ω | (embeddedChainTime G vm Δ (j + 1) ω : ℕ∞) ≤ 0} := by ext ω; simp
      rw [this]; exact vm.ℱ.le 0 _ (hT_stop_jp1 0)
    · have : {ω | embeddedChainTime G vm Δ (j + 1) ω = k} =
          {ω | (embeddedChainTime G vm Δ (j + 1) ω : ℕ∞) ≤ ↑k} \
          {ω | (embeddedChainTime G vm Δ (j + 1) ω : ℕ∞) ≤ ↑(k - 1)} := by
        ext ω; simp only [Set.mem_setOf_eq, Set.mem_sdiff, ENat.coe_le_coe]; omega
      rw [this]
      exact (vm.ℱ.le k _ (hT_stop_jp1 k)).diff (vm.ℱ.le (k - 1) _ (hT_stop_jp1 (k - 1)))
  have hTj_eq_meas : ∀ k, MeasurableSet
      {ω | embeddedChainTime G vm Δ j ω = k} := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have : {ω | embeddedChainTime G vm Δ j ω = 0} =
          {ω | (embeddedChainTime G vm Δ j ω : ℕ∞) ≤ 0} := by ext ω; simp
      rw [this]; exact vm.ℱ.le 0 _ (hT_stop_j 0)
    · have : {ω | embeddedChainTime G vm Δ j ω = k} =
          {ω | (embeddedChainTime G vm Δ j ω : ℕ∞) ≤ ↑k} \
          {ω | (embeddedChainTime G vm Δ j ω : ℕ∞) ≤ ↑(k - 1)} := by
        ext ω; simp only [Set.mem_setOf_eq, Set.mem_sdiff, ENat.coe_le_coe]; omega
      rw [this]
      exact (vm.ℱ.le k _ (hT_stop_j k)).diff (vm.ℱ.le (k - 1) _ (hT_stop_j (k - 1)))
  have hvolS_jp1_int : Integrable
      (fun ω => vm.volS (embeddedChainTime G vm Δ (j + 1) ω) ω) vm.μ := by
    have heq : (fun ω => vm.volS (embeddedChainTime G vm Δ (j + 1) ω) ω) = fun ω =>
        ∑ k ∈ Finset.range (cap + 2),
          Set.indicator {ω | embeddedChainTime G vm Δ (j + 1) ω = k}
            (fun ω => (TemporalGraph.volume G k (vm.S k ω) : ℝ)) ω := by
      funext ω
      rw [Finset.sum_eq_single (embeddedChainTime G vm Δ (j + 1) ω)]
      · show (TemporalGraph.volume G (embeddedChainTime G vm Δ (j + 1) ω)
          (vm.S (embeddedChainTime G vm Δ (j + 1) ω) ω) : ℝ) = _
        simp [Set.indicator]
      · intro k _ hk; simp [Set.indicator, Ne.symm hk]
      · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le (hT_next_bound ω))) h
    rw [heq]
    exact integrable_finsetSum _ fun k _ => (hvolInt k).indicator (hTnext_eq_meas k)
  have hvolS_j_int : Integrable
      (fun ω => vm.volS (embeddedChainTime G vm Δ j ω) ω) vm.μ := by
    have heq : (fun ω => vm.volS (embeddedChainTime G vm Δ j ω) ω) = fun ω =>
        ∑ k ∈ Finset.range (cap + 2),
          Set.indicator {ω | embeddedChainTime G vm Δ j ω = k}
            (fun ω => (TemporalGraph.volume G k (vm.S k ω) : ℝ)) ω := by
      funext ω
      rw [Finset.sum_eq_single (embeddedChainTime G vm Δ j ω)]
      · show (TemporalGraph.volume G (embeddedChainTime G vm Δ j ω)
          (vm.S (embeddedChainTime G vm Δ j ω) ω) : ℝ) = _
        simp [Set.indicator]
      · intro k _ hk; simp [Set.indicator, Ne.symm hk]
      · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le (hT_j_bound ω))) h
    rw [heq]
    exact integrable_finsetSum _ fun k _ => (hvolInt k).indicator (hTj_eq_meas k)
  exact (hvolS_jp1_int.sub hvolS_j_int).abs



/-- **L68 F_T-closure helper: the F_T-shaped F-fiber drift bound.**

For a sub-fiber `F_T ⊆ F` with `T_j = t_j` and `S_{t_j} = s_j`, where `s_j`
is admissible, and conductance witness `φ` satisfying the calendar-form
window guarantee, conclude
`∫_{F_T} (α·Δψ + Δχ + D_j) ∂vm.μ ≤ 0`
where `α = √vol(0, s_0) / d_min` and `D_j = min(φ_{j+1}/2048, 1/2048)`.

Extracted as a separate lemma to keep `psi_chi_combined_setIntegral_on_fiber_le`
within heartbeat budget — the dispatch slicing introduces many `set` /
`have`s whose accumulated elaboration cost otherwise times out the whnf
checker.

Strategy:
* `by_cases hφ_pos : 0 < φ (j+1)`.
  - φ = 0 branch: D_j = 0, replicate F_F-branch L75 + L77 derivation
    on F_T directly.
  - φ > 0 branch: slice F_T into F_T_U / F_T_S1 / F_T_S2 via
    `stronglyMeasurable_condExp`, apply L92 (the dispatch wrapper) once
    per sub-fiber. -/
private lemma psi_chi_combined_F_T_closure_on_fiber
    {Ω : Type*} [MeasurableSpace Ω]
    (G : TemporalGraphFixedDegree V)
    (vm : G.VoterModelAbstract 2 Ω)
    (d_min : ℕ) (hd : d_min = G.minDegreeAt 0) (hd_pos : 0 < d_min)
    (s_0 : Finset V) (hs_0_ne : s_0.Nonempty)
    (s_j : Finset V) (hs_j_ne : s_j.Nonempty)
    (t_j : ℕ)
    (Δ : ℕ → ℕ) (hΔ_pos : ∀ k, 1 ≤ Δ k)
    (φ : ℕ → ℝ) (hφ_nn : ∀ k, 0 ≤ φ k)
    (hwin : ∀ k, ∀ S ∈ G.admissibleCuts,
      φ k ≤ G.maxSetConductanceOnInterval (∑ i ∈ Finset.range k, Δ i) (Δ k) S)
    (j : ℕ)
    (hvol_lt : (TemporalGraph.volume G.toTemporalGraph 0 s_j : ℝ) <
      8 * (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ))
    (F_T : Set Ω)
    (hF_T_meas_ℱ : MeasurableSet[vm.ℱ t_j] F_T)
    (hF_T_T : ∀ ω ∈ F_T, embeddedChainTime G.toTemporalGraph vm Δ j ω = t_j)
    (hF_T_S : ∀ ω ∈ F_T, vm.S t_j ω = s_j)
    -- Paper-tight cap: t_j ≤ I_j^+ = (∑_{k<j+1} Δ_k) - 1
    (hT_cap : t_j ≤ (∑ k ∈ Finset.range (j + 1), Δ k) - 1)
    -- Admissibility of s_j (provided by caller).
    (hs_j_adm : s_j ∈ TemporalGraph.admissibleCuts G.toTemporalGraph)
    -- Paper-tight structural bound: t_j ≤ I_j^- = ∑_{k<j} Δ k (provided by caller).
    (ht_j_le_lo : t_j ≤ ∑ k ∈ Finset.range j, Δ k) :
    -- Conclusion: integrated F_T-shaped combined drift (with D_j) ≤ 0.
    ∫ ω in F_T,
      ((Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) / d_min)
          * (vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω
              - vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω)
        + (G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
              (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω)
          - G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ j ω)
              (vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω))
        + min (φ j / 2048) (1 / 2048 : ℝ))
      ∂vm.μ ≤ 0 := by
  classical
  haveI hprob : IsProbabilityMeasure (vm.μ : Measure Ω) := inferInstance
  set α : ℝ := Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) / d_min with hα_def
  have hα_nn : (0 : ℝ) ≤ α :=
    div_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _)
  -- Stopping-time scaffolding.
  have hS_meas_ℱ : ∀ t, @Measurable Ω (Finset V) (vm.ℱ t) ⊤ (vm.S t) := fun t =>
    (measurable_of_countable (fun A => VoterModel.minoritySet G.toTemporalGraph t A)).comp
      (vm.A_stronglyAdapted t).measurable
  have hT_stop : ∀ k,
      IsStoppingTime vm.ℱ (fun ω => (embeddedChainTime G.toTemporalGraph vm Δ k ω : ℕ∞)) := fun k =>
    embeddedChainTime_isStoppingTime G.toTemporalGraph vm Δ hS_meas_ℱ k
  -- Top-level measurability of F_T.
  have hF_T_meas : MeasurableSet F_T := vm.ℱ.le t_j _ hF_T_meas_ℱ
  -- Stopping-time witness for T_j.
  have hT_stop_j : IsStoppingTime vm.ℱ
      (fun ω => (embeddedChainTime G.toTemporalGraph vm Δ j ω : ℕ∞)) := hT_stop j
  -- ── by_cases on φ (j+1). ──────────────────────────────────────────────────
  rcases lt_or_eq_of_le (hφ_nn j) with hφ_pos | hφ_eq_sym
  · -- ── Positive φ branch: slice F_T into three sub-fibers. ──────────────
    -- Shorthand for `f2` (L84 integrand) and `hedge_fn` (hedge sum).
    set f2 : Ω → ℝ := fun ω' =>
      |(TemporalGraph.volume G.toTemporalGraph (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω')
            (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω') ω') : ℝ)
        - (TemporalGraph.volume G.toTemporalGraph t_j s_j : ℝ)| with hf2_def
    set hedge_fn : Ω → ℝ := fun ω' =>
      ∑ k ∈ Finset.Icc t_j (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω' - 1),
        (vm.cutS k ω' : ℝ) with hhedge_fn_def
    -- Conditional expectations.
    set f2_cE : Ω → ℝ := (vm.μ : Measure Ω)[f2 | (vm.ℱ t_j : MeasurableSpace Ω)] with hf2_cE_def
    set hedge_cE : Ω → ℝ := (vm.μ : Measure Ω)[hedge_fn | (vm.ℱ t_j : MeasurableSpace Ω)]
      with hhedge_cE_def
    have hf2_cE_meas : Measurable[vm.ℱ t_j] f2_cE :=
      (stronglyMeasurable_condExp (μ := vm.μ) (m := (vm.ℱ t_j : MeasurableSpace Ω))
        (f := f2)).measurable
    have hhedge_cE_meas : Measurable[vm.ℱ t_j] hedge_cE :=
      (stronglyMeasurable_condExp (μ := vm.μ) (m := (vm.ℱ t_j : MeasurableSpace Ω))
        (f := hedge_fn)).measurable
    -- Apply L98 once: hgood_step witness at paper-aligned interval `I_j`.
    -- `hwin j s_j hs_j_adm` gives the per-interval MAX-form bound at upper endpoint
    -- `(∑_{k<j} Δ_k) + Δ_j - 1 = (∑_{k<j+1} Δ_k) - 1 = I_j^+`.
    have hsum_succ_j1 : ∑ k ∈ Finset.range (j + 1), Δ k =
        (∑ k ∈ Finset.range j, Δ k) + Δ j := Finset.sum_range_succ Δ j
    have hI_le_j : (∑ k ∈ Finset.range j, Δ k) ≤
        (∑ k ∈ Finset.range (j + 1), Δ k) - 1 := by
      have := hΔ_pos j; omega
    have hcond_j : φ j ≤
        TemporalGraph.maxSetConductanceOnInterval G.toTemporalGraph
          (∑ k ∈ Finset.range j, Δ k)
          (((∑ k ∈ Finset.range (j + 1), Δ k) - 1) - (∑ k ∈ Finset.range j, Δ k) + 1) s_j := by
      convert hwin j s_j hs_j_adm using 2
      all_goals first | rfl | (have := hΔ_pos j; omega)
    have hgood_step := paper_good_step_from_calendar_window_guarantee
      G (φ j)
      (∑ k ∈ Finset.range j, Δ k)
      ((∑ k ∈ Finset.range (j + 1), Δ k) - 1) hI_le_j s_j
      t_j ht_j_le_lo hcond_j
    -- Thresholds and sub-fibers.
    set Thr_U : ℝ := (1 / 8 : ℝ) * (TemporalGraph.volume G.toTemporalGraph t_j s_j : ℝ)
      with hThr_U_def
    set Thr_S : ℝ := (1 / 8 : ℝ) *
        (TemporalGraph.volume G.toTemporalGraph t_j s_j : ℝ) / (1 / φ j)
      with hThr_S_def
    set F_T_U : Set Ω := F_T ∩ {ω | f2_cE ω ≥ Thr_U} with hF_T_U_def
    set F_T_S1 : Set Ω := (F_T \ F_T_U) ∩ {ω | hedge_cE ω > Thr_S}
      with hF_T_S1_def
    set F_T_S2 : Set Ω := (F_T \ F_T_U) \ F_T_S1 with hF_T_S2_def
    have hF_T_U_meas_ℱ : MeasurableSet[vm.ℱ t_j] F_T_U :=
      hF_T_meas_ℱ.inter (hf2_cE_meas measurableSet_Ici)
    have hF_T_diff_U_meas_ℱ : MeasurableSet[vm.ℱ t_j] (F_T \ F_T_U) :=
      hF_T_meas_ℱ.diff hF_T_U_meas_ℱ
    have hF_T_S1_meas_ℱ : MeasurableSet[vm.ℱ t_j] F_T_S1 :=
      hF_T_diff_U_meas_ℱ.inter (hhedge_cE_meas measurableSet_Ioi)
    have hF_T_S2_meas_ℱ : MeasurableSet[vm.ℱ t_j] F_T_S2 :=
      hF_T_diff_U_meas_ℱ.diff hF_T_S1_meas_ℱ
    have hF_T_U_meas : MeasurableSet F_T_U := vm.ℱ.le t_j _ hF_T_U_meas_ℱ
    have hF_T_S1_meas : MeasurableSet F_T_S1 := vm.ℱ.le t_j _ hF_T_S1_meas_ℱ
    have hF_T_S2_meas : MeasurableSet F_T_S2 := vm.ℱ.le t_j _ hF_T_S2_meas_ℱ
    have hF_T_U_sub : F_T_U ⊆ F_T := fun ω hω => hω.1
    have hF_T_S1_sub_diff : F_T_S1 ⊆ F_T \ F_T_U := fun ω hω => hω.1
    have hF_T_S1_sub : F_T_S1 ⊆ F_T := fun ω hω => (hF_T_S1_sub_diff hω).1
    have hF_T_S2_sub_diff : F_T_S2 ⊆ F_T \ F_T_U := fun ω hω => hω.1
    have hF_T_S2_sub : F_T_S2 ⊆ F_T := fun ω hω => (hF_T_S2_sub_diff hω).1
    have hF_T_U_T : ∀ ω ∈ F_T_U, embeddedChainTime G.toTemporalGraph vm Δ j ω = t_j :=
      fun ω hω => hF_T_T ω (hF_T_U_sub hω)
    have hF_T_U_S : ∀ ω ∈ F_T_U, vm.S t_j ω = s_j :=
      fun ω hω => hF_T_S ω (hF_T_U_sub hω)
    have hF_T_S1_T : ∀ ω ∈ F_T_S1, embeddedChainTime G.toTemporalGraph vm Δ j ω = t_j :=
      fun ω hω => hF_T_T ω (hF_T_S1_sub hω)
    have hF_T_S1_S : ∀ ω ∈ F_T_S1, vm.S t_j ω = s_j :=
      fun ω hω => hF_T_S ω (hF_T_S1_sub hω)
    have hF_T_S2_T : ∀ ω ∈ F_T_S2, embeddedChainTime G.toTemporalGraph vm Δ j ω = t_j :=
      fun ω hω => hF_T_T ω (hF_T_S2_sub hω)
    have hF_T_S2_S : ∀ ω ∈ F_T_S2, vm.S t_j ω = s_j :=
      fun ω hω => hF_T_S ω (hF_T_S2_sub hω)
    have hUnion : F_T = F_T_U ∪ F_T_S1 ∪ F_T_S2 := by
      ext ω
      constructor
      · intro hω
        by_cases hU : ω ∈ F_T_U
        · exact Or.inl (Or.inl hU)
        · by_cases hS1 : hedge_cE ω > Thr_S
          · exact Or.inl (Or.inr ⟨⟨hω, hU⟩, hS1⟩)
          · refine Or.inr ⟨⟨hω, hU⟩, ?_⟩
            intro hS1'
            exact hS1 hS1'.2
      · rintro ((hU | hS1) | hS2)
        · exact hF_T_U_sub hU
        · exact hF_T_S1_sub hS1
        · exact hF_T_S2_sub hS2
    have hDisj_US1 : Disjoint F_T_U F_T_S1 := by
      rw [Set.disjoint_left]
      rintro ω hU ⟨⟨_, hnU⟩, _⟩
      exact hnU hU
    have hDisj_US2 : Disjoint F_T_U F_T_S2 := by
      rw [Set.disjoint_left]
      rintro ω hU ⟨⟨_, hnU⟩, _⟩
      exact hnU hU
    have hDisj_S1S2 : Disjoint F_T_S1 F_T_S2 := by
      rw [Set.disjoint_left]
      rintro ω hS1 ⟨_, hnS1⟩
      exact hnS1 hS1
    have hDisj_U_S1S2 : Disjoint F_T_U (F_T_S1 ∪ F_T_S2) :=
      hDisj_US1.union_right hDisj_US2
    -- g_main: the F_T integrand (after `set α`).
    set g_main : Ω → ℝ := fun ω =>
      α * (vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω
              - vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω)
        + (G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
              (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω)
          - G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ j ω)
              (vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω))
        + min (φ j / 2048) (1 / 2048 : ℝ) with hg_main_def
    -- Integrability scaffolding.
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
      rw [heq2]; exact vm.ℱ.le u _ ((hT_stop k).measurableSet_eq u)
    have hψE_meas : ∀ k,
        Measurable (fun ω => vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) := by
      intro k S hS
      rw [show (fun ω => vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) ⁻¹' S =
          ⋃ t : ℕ, (embeddedChainTime G.toTemporalGraph vm Δ k) ⁻¹' {t} ∩ (vm.psiS t) ⁻¹' S from by
        ext ω
        simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff,
          Set.mem_singleton_iff]
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
        simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff,
          Set.mem_singleton_iff]
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
    have hg_main_meas : Measurable g_main := by
      refine Measurable.add (Measurable.add ?_ ?_) measurable_const
      · exact ((hψE_meas (j + 1)).sub (hψE_meas j)).const_mul _
      · exact (hχE_meas (j + 1)).sub (hχE_meas j)
    set Cg : ℝ := 2 * α * Real.sqrt (Vu : ℝ) + 2 * |Real.log (1 + (Vu : ℝ))|
        + (1 / 2048 : ℝ) with hCg_def
    have hψ_nn_k : ∀ k ω, 0 ≤ vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω := fun k ω => by
      show TemporalGraph.potential G.toTemporalGraph _ _ ≥ 0
      exact Real.sqrt_nonneg _
    have hψ_bnd_k : ∀ k ω,
        vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω ≤ Real.sqrt (Vu : ℝ) := fun k ω => by
      show TemporalGraph.potential G.toTemporalGraph _ _ ≤ _
      apply Real.sqrt_le_sqrt
      exact_mod_cast hVol_le_univ _ _
    have hχ_nn_k : ∀ k ω, 0 ≤ G.chiPotential
        (embeddedChainTime G.toTemporalGraph vm Δ k ω)
        (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) := fun k ω => by
      unfold TemporalGraphFixedDegree.chiPotential TemporalGraph.chiPotential
      apply Real.log_nonneg
      have h0 : (0 : ℝ) ≤ (TemporalGraph.volume G.toTemporalGraph (embeddedChainTime G.toTemporalGraph vm Δ k ω)
          (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) : ℝ) := Nat.cast_nonneg _
      linarith
    have hχ_bnd_k : ∀ k ω,
        G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ k ω)
          (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) ≤
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
    have hg_main_abs : ∀ ω, |g_main ω| ≤ Cg := by
      intro ω
      have h1 := hψ_nn_k (j + 1) ω
      have h2 := hψ_bnd_k (j + 1) ω
      have h3 := hψ_nn_k j ω
      have h4 := hψ_bnd_k j ω
      have h5 := hχ_nn_k (j + 1) ω
      have h6 := hχ_bnd_k (j + 1) ω
      have h7 := hχ_nn_k j ω
      have h8 := hχ_bnd_k j ω
      have hαmul2 : α * vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω ≤
          α * Real.sqrt (Vu : ℝ) :=
        mul_le_mul_of_nonneg_left h2 hα_nn
      have hαmul4 : α * vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω ≤
          α * Real.sqrt (Vu : ℝ) :=
        mul_le_mul_of_nonneg_left h4 hα_nn
      have hαmul1 : 0 ≤ α * vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω :=
        mul_nonneg hα_nn h1
      have hαmul3 : 0 ≤ α * vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω :=
        mul_nonneg hα_nn h3
      have habs_log_nn : 0 ≤ |Real.log (1 + (Vu : ℝ))| := abs_nonneg _
      have hlog_le : Real.log (1 + (Vu : ℝ)) ≤ |Real.log (1 + (Vu : ℝ))| := le_abs_self _
      have hlog_ge : -|Real.log (1 + (Vu : ℝ))| ≤ Real.log (1 + (Vu : ℝ)) := neg_abs_le _
      have hDj_nn : 0 ≤ min (φ j / 2048) (1 / 2048 : ℝ) :=
        le_min (div_nonneg (hφ_nn j) (by norm_num)) (by norm_num)
      have hDj_le : min (φ j / 2048) (1 / 2048 : ℝ) ≤ (1 / 2048 : ℝ) :=
        min_le_right _ _
      simp only [hg_main_def, hCg_def]
      rw [abs_le]
      refine ⟨?_, ?_⟩ <;> linarith [Real.sqrt_nonneg ((Vu : ℝ))]
    have hg_main_int : Integrable g_main vm.μ := by
      refine MeasureTheory.Integrable.of_bound (C := Cg)
        hg_main_meas.aestronglyMeasurable
        (Filter.Eventually.of_forall (fun ω => ?_))
      rw [Real.norm_eq_abs]; exact hg_main_abs ω
    -- Integral split via setIntegral_union.
    have hF_T_eq_partition : F_T = F_T_U ∪ (F_T_S1 ∪ F_T_S2) := by
      rw [hUnion, Set.union_assoc]
    have hF_T_S1_S2_meas : MeasurableSet (F_T_S1 ∪ F_T_S2) :=
      hF_T_S1_meas.union hF_T_S2_meas
    have h_split_main : ∫ ω in F_T, g_main ω ∂vm.μ =
        ∫ ω in F_T_U, g_main ω ∂vm.μ +
        (∫ ω in F_T_S1, g_main ω ∂vm.μ + ∫ ω in F_T_S2, g_main ω ∂vm.μ) := by
      rw [hF_T_eq_partition,
        MeasureTheory.setIntegral_union hDisj_U_S1S2 hF_T_S1_S2_meas
          hg_main_int.integrableOn hg_main_int.integrableOn,
        MeasureTheory.setIntegral_union hDisj_S1S2 hF_T_S2_meas
          hg_main_int.integrableOn hg_main_int.integrableOn]
    -- ── F_T_U: dispatch to Unstable. ─────────────────────────────────────────
    have hF_T_U_le : ∫ ω in F_T_U, g_main ω ∂vm.μ ≤ 0 := by
      set f1 : Ω → ℝ := fun ω' =>
        |vm.volS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω') ω' -
          vm.volS (embeddedChainTime G.toTemporalGraph vm Δ j ω') ω'| with hf1_def
      have hf1_int : Integrable f1 vm.μ := volS_diff_integrable G.toTemporalGraph vm Δ hΔ_pos j
      have hf2_int : Integrable f2 vm.μ :=
        volDev_integrable G.toTemporalGraph vm Δ j (TemporalGraph.volume G.toTemporalGraph t_j s_j : ℝ)
      have h_f1_f2_on_F_T : ∀ ω ∈ F_T, f1 ω = f2 ω := by
        intro ω hω
        show |vm.volS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω -
                vm.volS (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω| =
            |(TemporalGraph.volume G.toTemporalGraph (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
                  (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω) : ℝ)
              - (TemporalGraph.volume G.toTemporalGraph t_j s_j : ℝ)|
        have hvolS : vm.volS (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω =
            (TemporalGraph.volume G.toTemporalGraph t_j s_j : ℝ) := by
          show (TemporalGraph.volume G.toTemporalGraph (embeddedChainTime G.toTemporalGraph vm Δ j ω)
                (vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω) : ℝ) = _
          rw [hF_T_T ω hω, hF_T_S ω hω]
        rw [hvolS]; rfl
      have h_cE_eq : (vm.μ : Measure Ω)[f1 | (vm.ℱ t_j : MeasurableSpace Ω)] =ᵐ[(vm.μ : Measure Ω).restrict F_T]
          (vm.μ : Measure Ω)[f2 | (vm.ℱ t_j : MeasurableSpace Ω)] :=
        condExp_eq_of_eq_on_fiber (vm.μ : Measure Ω) ((vm.ℱ).le t_j) hF_T_meas_ℱ
          hf1_int hf2_int h_f1_f2_on_F_T
      set Eset : Set Ω := {ω | (embeddedChainTime G.toTemporalGraph vm Δ j ω : ℕ∞) = (t_j : ℕ∞)}
        with hEset_def
      have h_bridge_on_E :
          (vm.μ : Measure Ω)[f1 | hT_stop_j.measurableSpace] =ᵐ[(vm.μ : Measure Ω).restrict Eset]
            (vm.μ : Measure Ω)[f1 | (vm.ℱ t_j : MeasurableSpace Ω)] :=
        condExp_stopping_time_ae_eq_restrict_eq_of_countable hT_stop_j t_j
      have hF_T_subset_E : F_T ⊆ Eset := by
        intro ω hω
        show (embeddedChainTime G.toTemporalGraph vm Δ j ω : ℕ∞) = (t_j : ℕ∞)
        exact_mod_cast hF_T_T ω hω
      have h_volS_on_F_T : ∀ ω ∈ F_T,
          vm.volS (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω =
            (TemporalGraph.volume G.toTemporalGraph t_j s_j : ℝ) := by
        intro ω hω
        show (TemporalGraph.volume G.toTemporalGraph (embeddedChainTime G.toTemporalGraph vm Δ j ω)
              (vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω) : ℝ) =
            (TemporalGraph.volume G.toTemporalGraph t_j s_j : ℝ)
        rw [hF_T_T ω hω, hF_T_S ω hω]
      have hF_T_U_subset_E : F_T_U ⊆ Eset :=
        Set.Subset.trans hF_T_U_sub hF_T_subset_E
      have h_restrict_U_le_E : (vm.μ : Measure Ω).restrict F_T_U ≤ (vm.μ : Measure Ω).restrict Eset :=
        Measure.restrict_mono hF_T_U_subset_E le_rfl
      have h_restrict_U_le_F_T : (vm.μ : Measure Ω).restrict F_T_U ≤ (vm.μ : Measure Ω).restrict F_T :=
        Measure.restrict_mono hF_T_U_sub le_rfl
      have h_bridge_on_F_T_U :
          (vm.μ : Measure Ω)[f1 | hT_stop_j.measurableSpace] =ᵐ[(vm.μ : Measure Ω).restrict F_T_U]
            (vm.μ : Measure Ω)[f1 | (vm.ℱ t_j : MeasurableSpace Ω)] :=
        h_bridge_on_E.filter_mono (MeasureTheory.ae_mono h_restrict_U_le_E)
      have h_cE_eq_on_F_T_U : (vm.μ : Measure Ω)[f1 | (vm.ℱ t_j : MeasurableSpace Ω)]
          =ᵐ[(vm.μ : Measure Ω).restrict F_T_U] (vm.μ : Measure Ω)[f2 | (vm.ℱ t_j : MeasurableSpace Ω)] :=
        h_cE_eq.filter_mono (MeasureTheory.ae_mono h_restrict_U_le_F_T)
      have h_f2_cE_ge_on_F_T_U : ∀ ω ∈ F_T_U, f2_cE ω ≥ Thr_U :=
        fun ω hω => hω.2
      have h_f2_cE_ge_ae : ∀ᵐ ω ∂((vm.μ : Measure Ω).restrict F_T_U), f2_cE ω ≥ Thr_U := by
        rw [ae_restrict_iff' hF_T_U_meas]
        exact ae_of_all _ h_f2_cE_ge_on_F_T_U
      have h_volS_ae_F_T_U : ∀ᵐ ω ∂((vm.μ : Measure Ω).restrict F_T_U),
          vm.volS (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω =
            (TemporalGraph.volume G.toTemporalGraph t_j s_j : ℝ) := by
        rw [ae_restrict_iff' hF_T_U_meas]
        exact ae_of_all _ (fun ω hω => h_volS_on_F_T ω (hF_T_U_sub hω))
      have hUnstable_F_T_U : ∀ᵐ ω ∂((vm.μ : Measure Ω).restrict F_T_U),
          ((vm.μ : Measure Ω)[f1 | hT_stop_j.measurableSpace]) ω
            ≥ (1 / 8 : ℝ) * vm.volS (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω := by
        filter_upwards [h_bridge_on_F_T_U, h_cE_eq_on_F_T_U,
          h_f2_cE_ge_ae, h_volS_ae_F_T_U]
          with ω hσ hcEeq hf2ge hvolS
        rw [hσ, hcEeq, hvolS]
        show f2_cE ω ≥ (1 / 8 : ℝ) * (TemporalGraph.volume G.toTemporalGraph t_j s_j : ℝ)
        exact hf2ge
      refine psi_chi_combined_drift_dispatch_on_fiber G vm d_min hd hd_pos
        s_0 hs_0_ne s_j hs_j_ne t_j Δ hΔ_pos j hvol_lt F_T_U
        hF_T_U_meas_ℱ hF_T_U_T hF_T_U_S hT_cap (φ j) (hφ_nn j) ?_
      exact Or.inr ⟨hT_stop_j, hUnstable_F_T_U⟩
    -- ── F_T_S1: dispatch to Case 1 (large edge sum). ────────────────────────
    have hF_T_S1_le : ∫ ω in F_T_S1, g_main ω ∂vm.μ ≤ 0 := by
      have h_hedge_cE_gt_on_F_T_S1 : ∀ ω ∈ F_T_S1, hedge_cE ω > Thr_S :=
        fun ω hω => hω.2
      have hLarge_F_T_S1 : ∀ᵐ ω ∂((vm.μ : Measure Ω).restrict F_T_S1),
          ((vm.μ : Measure Ω)[fun ω' => ∑ k ∈ Finset.Icc t_j
              (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω' - 1),
            (vm.cutS k ω' : ℝ) | vm.ℱ t_j]) ω
            > (1 / 8 : ℝ) * (TemporalGraph.volume G.toTemporalGraph t_j s_j : ℝ)
                / (1 / φ j) := by
        rw [ae_restrict_iff' hF_T_S1_meas]
        refine ae_of_all _ (fun ω hω => ?_)
        have := h_hedge_cE_gt_on_F_T_S1 ω hω
        show hedge_cE ω > _
        exact this
      refine psi_chi_combined_drift_dispatch_on_fiber G vm d_min hd hd_pos
        s_0 hs_0_ne s_j hs_j_ne t_j Δ hΔ_pos j hvol_lt F_T_S1
        hF_T_S1_meas_ℱ hF_T_S1_T hF_T_S1_S hT_cap (φ j) (hφ_nn j) ?_
      exact Or.inl (Or.inl ⟨hφ_pos, hLarge_F_T_S1⟩)
    -- ── F_T_S2: dispatch to Case 2 (small edge sum + stable). ───────────────
    have hF_T_S2_le : ∫ ω in F_T_S2, g_main ω ∂vm.μ ≤ 0 := by
      have h_hedge_cE_le_on_F_T_S2 : ∀ ω ∈ F_T_S2, hedge_cE ω ≤ Thr_S := by
        intro ω hω
        have hω1 : ω ∈ F_T \ F_T_U := hω.1
        have hω2 : ω ∉ F_T_S1 := hω.2
        by_contra hgt
        push Not at hgt
        exact hω2 ⟨hω1, hgt⟩
      have hedge_small_F_T_S2 : ∀ᵐ ω ∂((vm.μ : Measure Ω).restrict F_T_S2),
          ((vm.μ : Measure Ω)[fun ω' => ∑ k ∈ Finset.Icc t_j
              (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω' - 1),
            (vm.cutS k ω' : ℝ) | vm.ℱ t_j]) ω
            ≤ (1 / 8 : ℝ) * (TemporalGraph.volume G.toTemporalGraph t_j s_j : ℝ)
                / (1 / φ j) := by
        rw [ae_restrict_iff' hF_T_S2_meas]
        refine ae_of_all _ (fun ω hω => ?_)
        have := h_hedge_cE_le_on_F_T_S2 ω hω
        show hedge_cE ω ≤ _
        exact this
      have h_f2_cE_lt_on_F_T_S2 : ∀ ω ∈ F_T_S2, f2_cE ω < Thr_U := by
        intro ω hω
        have hω_diff : ω ∈ F_T \ F_T_U := hω.1
        have hω_F_T : ω ∈ F_T := hω_diff.1
        have hω_not_U : ω ∉ F_T_U := hω_diff.2
        by_contra hge
        push Not at hge
        exact hω_not_U ⟨hω_F_T, hge⟩
      have hstable_F_T_S2 : ∀ᵐ ω ∂((vm.μ : Measure Ω).restrict F_T_S2),
          ((vm.μ : Measure Ω)[fun ω' =>
              |(TemporalGraph.volume G.toTemporalGraph (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω')
                    (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω') ω') : ℝ)
                - (TemporalGraph.volume G.toTemporalGraph t_j s_j : ℝ)|
              | vm.ℱ t_j]) ω
            < (1 / 8 : ℝ) * (TemporalGraph.volume G.toTemporalGraph t_j s_j : ℝ) := by
        rw [ae_restrict_iff' hF_T_S2_meas]
        refine ae_of_all _ (fun ω hω => ?_)
        show f2_cE ω < _
        exact h_f2_cE_lt_on_F_T_S2 ω hω
      have hC2 : ∀ t', t_j ≤ t' → t' ≤ (∑ k ∈ Finset.range (j + 1), Δ k) - 1 →
          Case2Hypotheses G.toTemporalGraph vm s_j t_j
            (embeddedChainTime G.toTemporalGraph vm Δ (j + 1)) t' (φ j) F_T_S2 := by
        intro t' ht'_lo ht'_hi
        have hexit_F_T_S2 :=
          F_T_exit_bound G.toTemporalGraph vm s_j t_j Δ j F_T_S2 hF_T_S2_meas_ℱ
            hF_T_S2_T hF_T_S2_S t' ht'_hi
        exact case2_hypotheses_from_volume_bound_on_fiber
          G.toTemporalGraph vm s_j t_j Δ j F_T_S2 hF_T_S2_meas_ℱ hF_T_S2_T hF_T_S2_S
          (φ j) t' ht'_lo hstable_F_T_S2 hexit_F_T_S2
      refine psi_chi_combined_drift_dispatch_on_fiber G vm d_min hd hd_pos
        s_0 hs_0_ne s_j hs_j_ne t_j Δ hΔ_pos j hvol_lt F_T_S2
        hF_T_S2_meas_ℱ hF_T_S2_T hF_T_S2_S hT_cap (φ j) (hφ_nn j) ?_
      exact Or.inl (Or.inr ⟨hφ_pos, hgood_step, hedge_small_F_T_S2, hC2⟩)
    -- Sum the three sub-fiber integrals.
    have hSum : ∫ ω in F_T, g_main ω ∂vm.μ ≤ 0 := by
      rw [h_split_main]
      have h1 : ∫ ω in F_T_S1, g_main ω ∂vm.μ +
          ∫ ω in F_T_S2, g_main ω ∂vm.μ ≤ 0 :=
        add_nonpos hF_T_S1_le hF_T_S2_le
      exact add_nonpos hF_T_U_le h1
    exact hSum
  · -- ── φ = 0 branch: D_j = 0, replicate F_F-branch L75 + L77 on F_T. ──────
    have hφ_eq : φ j = 0 := hφ_eq_sym.symm
    have hL75_T := psi_down_drift_on_fiber G vm s_j t_j Δ hΔ_pos j F_T
      hF_T_meas_ℱ hF_T_T hF_T_S hT_cap
    have hL77_T := chi_down_drift_voter_on_fiber G vm s_j t_j Δ hΔ_pos j F_T
      hF_T_meas_ℱ hF_T_T hF_T_S hT_cap
    have hψ_Tj_eq_on_F_T : ∀ ω ∈ F_T,
        vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω =
        TemporalGraph.potential G.toTemporalGraph t_j s_j := by
      intro ω hω
      show TemporalGraph.potential G.toTemporalGraph (embeddedChainTime G.toTemporalGraph vm Δ j ω)
          (vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω) = _
      rw [hF_T_T ω hω, hF_T_S ω hω]
    have hχ_Tj_eq_on_F_T : ∀ ω ∈ F_T,
        G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ j ω)
          (vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω)
          = G.chiPotential t_j s_j := by
      intro ω hω
      rw [hF_T_T ω hω, hF_T_S ω hω]
    have hDj_zero : min (φ j / 2048) (1 / 2048 : ℝ) = 0 := by
      rw [hφ_eq]
      simp [show (0 : ℝ) / 2048 = 0 from by norm_num]
    have hinteg_F_T_φ0 : ∀ ω ∈ F_T,
        (α * (vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω
                - vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω)
          + (G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
                (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω)
            - G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ j ω)
                (vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω))
          + min (φ j / 2048) (1 / 2048 : ℝ)) =
        (α * (vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω
                - TemporalGraph.potential G.toTemporalGraph t_j s_j)
          + (G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
                (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω)
            - G.chiPotential t_j s_j)) := by
      intro ω hω
      rw [hDj_zero, hψ_Tj_eq_on_F_T ω hω, hχ_Tj_eq_on_F_T ω hω]
      ring
    rw [setIntegral_congr_fun hF_T_meas (fun ω hω => hinteg_F_T_φ0 ω hω)]
    -- ψ-integrability + χ-integrability bounds (mirror F_F-branch).
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
      rw [heq2]; exact vm.ℱ.le u _ ((hT_stop k).measurableSet_eq u)
    have hψE_meas : ∀ k,
        Measurable (fun ω => vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) := by
      intro k S hS
      rw [show (fun ω => vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) ⁻¹' S =
          ⋃ t : ℕ, (embeddedChainTime G.toTemporalGraph vm Δ k) ⁻¹' {t} ∩ (vm.psiS t) ⁻¹' S from by
        ext ω
        simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff,
          Set.mem_singleton_iff]
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
        simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff,
          Set.mem_singleton_iff]
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
    have hψ_int : Integrable
        (fun ω => vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω -
          TemporalGraph.potential G.toTemporalGraph t_j s_j) vm.μ := by
      refine MeasureTheory.Integrable.of_bound
        (C := Real.sqrt (Vu : ℝ) + TemporalGraph.potential G.toTemporalGraph t_j s_j)
        ((hψE_meas (j + 1)).sub_const _).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs]
      have h_nn : 0 ≤ vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω :=
        Real.sqrt_nonneg _
      have h_bnd : vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω ≤
          Real.sqrt (Vu : ℝ) := by
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
        ((hχE_meas (j + 1)).sub_const _).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs]
      have h_nn : 0 ≤ G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
          (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω) := by
        unfold TemporalGraphFixedDegree.chiPotential TemporalGraph.chiPotential
        apply Real.log_nonneg
        have h0 : (0 : ℝ) ≤ (TemporalGraph.volume G.toTemporalGraph
            (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
            (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω) : ℝ) := Nat.cast_nonneg _
        linarith
      have h_bnd : G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
          (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω) ≤
          Real.log (1 + (Vu : ℝ)) := by
        unfold TemporalGraphFixedDegree.chiPotential TemporalGraph.chiPotential
        have h1 : (0 : ℝ) < 1 + (TemporalGraph.volume G.toTemporalGraph
            (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
            (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω) : ℝ) := by
          have h0 : (0 : ℝ) ≤ (TemporalGraph.volume G.toTemporalGraph
              (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
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
    have hint_eq_φ0 : ∫ ω in F_T,
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
    rw [hint_eq_φ0]
    have h_psi := mul_le_mul_of_nonneg_left hL75_T hα_nn
    simp only [mul_zero] at h_psi
    linarith

/-- **Per-fiber combined-drift bound (Lean-only helper for L51).**

For the deterministic-fiber set `F ⊆ {ω | T_j ω = t_j ∧ vm.S t_j ω = s_j}`,
measurable in `vm.ℱ t_j`, the set-integral of the L51 integrand over `F` is `≤ 0`.

**Proof structure (3-case dichotomy).**
Decompose `F = F_F ⊔ F_T`, where `F_T := F ∩ B` and `F_F := F \ B`, with
`B := {ω | ∀ k ≤ j, S_{T_k} ω ≠ ∅ ∧ vol(S_{T_k} ω) < 8·vol(s_0)}` the
indicator-true set. To get sub-fiber `ℱ_{t_j}`-measurability we use the
proxy `B' := {ω | ∀ k ≤ j, S_{min t_j (T_k)} ω ≠ ∅ ∧ vol(S_{min t_j (T_k)} ω)
< 8·vol(s_0)}`, which equals `B` on `F` (since `T_k ≤ T_j = t_j` there).
The stopped value `ω ↦ vm.S (min t_j (T_k ω)) ω` is `ℱ_{t_j}`-measurable
because `min t_j T_k` is a stopping time bounded by `t_j`.

* **F_F (indicator false).** The `if`-clause is `0`, and the residual
  integrand `α·Δψ + Δχ` is `≤ 0` by L75 (`psi_down_drift_on_fiber`) and L77
  (`chi_down_drift_voter_on_fiber`), each applied to `F_F`. **Closed below.**

* **F_T (indicator true).** Subdivides into stable / unstable. Both
  sub-cases would invoke L76 (`psi_down_drift_stable_on_fiber`) or L78
  (`chi_down_drift_voter_unstable_on_fiber`). However, both require
  fiber-relative stability/jump witnesses that the existing L52/L54/L55
  bridges cannot supply (they are formulated with global
  `∀ω, T_j ω = t_j` hypotheses). -/
private lemma psi_chi_combined_setIntegral_on_fiber_le
    {Ω : Type*} [MeasurableSpace Ω]
    (G : TemporalGraphFixedDegree V)
    (vm : G.VoterModelAbstract 2 Ω)
    (d_min : ℕ) (hd : d_min = G.minDegreeAt 0) (hd_pos : 0 < d_min)
    (s_0 : Finset V) (hs_0_ne : s_0.Nonempty)
    (Δ : ℕ → ℕ) (hΔ_pos : ∀ j, 1 ≤ Δ j)
    (φ : ℕ → ℝ) (hφ_nn : ∀ j, 0 ≤ φ j)
    -- Window-guarantee hypothesis (per-interval MAX-form, paper's
    -- `φ^{I_j}(𝒢) ≥ φ_j`): for each `j` and admissible cut `S`, the
    -- maximum of `(G.snapshot ·).setConductance S` over the calendar
    -- interval `[∑_{k<j} Δ_k, ∑_{k<j} Δ_k + Δ_j - 1]` is at least `φ j`.
    (hwin : ∀ j, ∀ S ∈ G.admissibleCuts,
      φ j ≤ G.maxSetConductanceOnInterval (∑ i ∈ Finset.range j, Δ i) (Δ j) S)
    (j : ℕ) (t_j : ℕ) (s_j : Finset V)
    -- Subset of the (t_j, s_j)-deterministic fiber, measurable in ℱ_{t_j}.
    (F : Set Ω)
    (hF_meas : MeasurableSet[vm.ℱ t_j] F)
    (hF_T : ∀ ω ∈ F, embeddedChainTime G.toTemporalGraph vm Δ j ω = t_j)
    (hF_S : ∀ ω ∈ F, vm.S t_j ω = s_j)
    -- t_j is within the cap for the (j+1)-th embedded interval (paper-tight cap).
    (hT_cap : t_j ≤ (∑ k ∈ Finset.range (j + 1), Δ k) - 1) :
    ∫ ω in F,
      ((Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) / d_min)
          * vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω
        + G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
            (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω)
        - (Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) / d_min)
            * vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω
        - G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ j ω)
            (vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω)
        + if ∀ k ≤ j,
              (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) ≠ ∅ ∧
              (TemporalGraph.volume G.toTemporalGraph 0 (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) : ℝ) <
              8 * (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ)
          then min (φ j / 2048) (1 / 2048 : ℝ) else 0)
      ∂vm.μ ≤ 0 := by
  classical
  haveI hprob : IsProbabilityMeasure (vm.μ : Measure Ω) := inferInstance
  -- Top-level measurability of F.
  have hF_meas_top : MeasurableSet F := vm.ℱ.le t_j _ hF_meas
  -- Abbreviation: α := √vol(s_0)/d_min ≥ 0.
  set α : ℝ := Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) / d_min with hα_def
  have hα_nn : (0 : ℝ) ≤ α :=
    div_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _)
  -- Abbreviation: the indicator-true predicate `Pind ω`.
  set Pind : Ω → Prop := fun ω =>
    ∀ k ≤ j, (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) ≠ ∅ ∧
      (TemporalGraph.volume G.toTemporalGraph 0 (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) : ℝ) <
        8 * (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) with hPind_def
  -- Stopping-time scaffolding for the embedded chain.
  have hS_meas_ℱ : ∀ t, @Measurable Ω (Finset V) (vm.ℱ t) ⊤ (vm.S t) := fun t =>
    (measurable_of_countable (fun A => VoterModel.minoritySet G.toTemporalGraph t A)).comp
      (vm.A_stronglyAdapted t).measurable
  have hT_stop : ∀ k,
      IsStoppingTime vm.ℱ (fun ω => (embeddedChainTime G.toTemporalGraph vm Δ k ω : ℕ∞)) := fun k =>
    embeddedChainTime_isStoppingTime G.toTemporalGraph vm Δ hS_meas_ℱ k
  -- ── Bound T_k ≤ T_j on F (mono). On F, T_j = t_j, so T_k ≤ t_j for k ≤ j.
  -- Inline mono: T_k ≤ T_j by induction on (j - k) using strictMono one-step.
  have hT_mono : ∀ k m, ∀ ω, embeddedChainTime G.toTemporalGraph vm Δ k ω
      ≤ embeddedChainTime G.toTemporalGraph vm Δ (k + m) ω := by
    intro k m ω
    induction m with
    | zero => simp
    | succ m' ih =>
      refine le_trans ih ?_
      -- T_{k+m'} ≤ T_{k+m'+1}: need T_{k+m'} ≤ (∑ range(k+m'+1) Δ) - 1 (paper-tight cap).
      have h_le_sum : embeddedChainTime G.toTemporalGraph vm Δ (k + m') ω ≤
          ∑ ℓ ∈ Finset.range (k + m'), Δ ℓ :=
        embeddedChainTime_le_sum_tight G.toTemporalGraph vm Δ hΔ_pos (k + m') ω
      have h_succ_ge : 1 ≤ Δ (k + m') := hΔ_pos _
      have hsum_succ : ∑ ℓ ∈ Finset.range (k + m' + 1), Δ ℓ =
          ∑ ℓ ∈ Finset.range (k + m'), Δ ℓ + Δ (k + m') := Finset.sum_range_succ Δ (k + m')
      have h_T_le_cap : embeddedChainTime G.toTemporalGraph vm Δ (k + m') ω ≤
          (∑ ℓ ∈ Finset.range (k + m' + 1), Δ ℓ) - 1 := by
        rw [hsum_succ]; omega
      have hstep := embeddedChainTime_strictMono G.toTemporalGraph vm Δ (k + m') ω h_T_le_cap
      show embeddedChainTime G.toTemporalGraph vm Δ (k + m') ω ≤ embeddedChainTime G.toTemporalGraph vm Δ (k + m' + 1) ω
      omega
  have hT_mono_le_t_j_on_F : ∀ k ≤ j, ∀ ω ∈ F, embeddedChainTime G.toTemporalGraph vm Δ k ω ≤ t_j := by
    intro k hk ω hω
    have hmono := hT_mono k (j - k) ω
    have hsum : k + (j - k) = j := by omega
    rw [hsum] at hmono
    have hTj : embeddedChainTime G.toTemporalGraph vm Δ j ω = t_j := hF_T ω hω
    omega
  -- ── Indicator measurability proxy via `min t_j T_k`. Build B' ∈ ℱ_{t_j}.
  -- For each k, define `Tk' ω := min t_j (T_k ω)` (ℕ-valued, bounded by t_j).
  -- Then `ω ↦ vm.S (Tk' ω) ω` is `ℱ_{t_j}`-measurable.
  have hSTk_meas_ℱ : ∀ k,
      @Measurable Ω (Finset V) (vm.ℱ t_j) ⊤
        (fun ω => vm.S (min t_j (embeddedChainTime G.toTemporalGraph vm Δ k ω)) ω) := by
    intro k S hS
    -- ω ↦ S(min t_j T_k ω) ω = Σ_{u ≤ t_j} [min t_j T_k = u] · S_u.
    -- (Decomposition over the finite range {0,...,t_j}.)
    rw [show (fun ω => vm.S (min t_j (embeddedChainTime G.toTemporalGraph vm Δ k ω)) ω) ⁻¹' S =
        ⋃ u ∈ Finset.Iic t_j,
          {ω | min t_j (embeddedChainTime G.toTemporalGraph vm Δ k ω) = u} ∩ (vm.S u) ⁻¹' S from by
      ext ω
      refine ⟨fun h => ?_, ?_⟩
      · refine Set.mem_iUnion.mpr ⟨min t_j (embeddedChainTime G.toTemporalGraph vm Δ k ω), ?_⟩
        refine Set.mem_iUnion.mpr ⟨Finset.mem_Iic.mpr (Nat.min_le_left _ _), ?_⟩
        exact ⟨rfl, h⟩
      · intro hmem
        obtain ⟨u, hu⟩ := Set.mem_iUnion.mp hmem
        obtain ⟨_hu_in, hbody⟩ := Set.mem_iUnion.mp hu
        obtain ⟨hueq, hmem⟩ := hbody
        show vm.S (min t_j (embeddedChainTime G.toTemporalGraph vm Δ k ω)) ω ∈ S
        rw [hueq]; exact hmem]
    refine MeasurableSet.biUnion (Finset.Iic t_j).countable_toSet (fun u hu => ?_)
    have hu_le : u ≤ t_j := Finset.mem_Iic.mp hu
    -- {min t_j T_k = u} ∈ ℱ_{t_j}.
    have hset_meas : MeasurableSet[vm.ℱ t_j]
        {ω | min t_j (embeddedChainTime G.toTemporalGraph vm Δ k ω) = u} := by
      by_cases hu_eq : u = t_j
      · -- {min t_j T_k = t_j} = {T_k ≥ t_j}.
        rw [hu_eq]
        rw [show {ω | min t_j (embeddedChainTime G.toTemporalGraph vm Δ k ω) = t_j} =
            {ω | t_j ≤ embeddedChainTime G.toTemporalGraph vm Δ k ω} from by
              ext ω
              simp only [Set.mem_setOf_eq]
              omega]
        -- {T_k ≥ t_j} = ({T_k < t_j})ᶜ = ({T_k : ℕ∞ ≤ t_j - 1})ᶜ if t_j > 0, else univ.
        rcases Nat.eq_zero_or_pos t_j with rfl | ht_j_pos
        · -- t_j = 0, the set is univ.
          rw [show {ω : Ω | (0 : ℕ) ≤ embeddedChainTime G.toTemporalGraph vm Δ k ω} = Set.univ from by
            ext ω; simp]
          exact MeasurableSet.univ
        · rw [show {ω | t_j ≤ embeddedChainTime G.toTemporalGraph vm Δ k ω} =
            {ω | (embeddedChainTime G.toTemporalGraph vm Δ k ω : ℕ∞) ≤ ↑(t_j - 1)}ᶜ from by
              ext ω
              simp only [Set.mem_setOf_eq, Set.mem_compl_iff,
                ENat.coe_le_coe]
              omega]
          refine MeasurableSet.compl ?_
          have h := (hT_stop k) (t_j - 1)
          exact vm.ℱ.mono (by omega) _ h
      · -- u < t_j. {min t_j T_k = u} = {T_k = u}.
        have hu_lt : u < t_j := lt_of_le_of_ne hu_le hu_eq
        rw [show {ω | min t_j (embeddedChainTime G.toTemporalGraph vm Δ k ω) = u} =
            {ω | embeddedChainTime G.toTemporalGraph vm Δ k ω = u} from by
          ext ω
          simp only [Set.mem_setOf_eq]
          constructor
          · intro hmin; omega
          · intro heq; omega]
        have heq : {ω : Ω | embeddedChainTime G.toTemporalGraph vm Δ k ω = u} =
            {ω | (embeddedChainTime G.toTemporalGraph vm Δ k ω : ℕ∞) = ↑u} := by
          ext w
          exact ⟨fun heq => by exact_mod_cast heq, fun heq => by exact_mod_cast heq⟩
        rw [heq]
        have h := (hT_stop k).measurableSet_eq u
        exact vm.ℱ.mono hu_le _ h
    have hSu_meas : MeasurableSet[vm.ℱ t_j] ((vm.S u) ⁻¹' S) := by
      have h := hS_meas_ℱ u hS
      exact vm.ℱ.mono hu_le _ h
    exact hset_meas.inter hSu_meas
  -- B' (proxy indicator-true set) ∈ ℱ_{t_j}.
  set B' : Set Ω := {ω | ∀ k ≤ j,
      (vm.S (min t_j (embeddedChainTime G.toTemporalGraph vm Δ k ω)) ω) ≠ ∅ ∧
      (TemporalGraph.volume G.toTemporalGraph 0
          (vm.S (min t_j (embeddedChainTime G.toTemporalGraph vm Δ k ω)) ω) : ℝ) <
        8 * (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ)} with hB'_def
  have hB'_meas_ℱ : MeasurableSet[vm.ℱ t_j] B' := by
    rw [show B' = ⋂ k ∈ Finset.Iic j,
        ({ω | (vm.S (min t_j (embeddedChainTime G.toTemporalGraph vm Δ k ω)) ω) ≠ ∅} ∩
          {ω | (TemporalGraph.volume G.toTemporalGraph 0
              (vm.S (min t_j (embeddedChainTime G.toTemporalGraph vm Δ k ω)) ω) : ℝ) <
              8 * (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ)}) from by
      ext ω; simp [B', Finset.mem_Iic, Set.mem_inter_iff]]
    refine MeasurableSet.biInter (Set.to_countable _) (fun k _ => ?_)
    have h_ne : MeasurableSet[vm.ℱ t_j]
        {ω | (vm.S (min t_j (embeddedChainTime G.toTemporalGraph vm Δ k ω)) ω) ≠ ∅} :=
      hSTk_meas_ℱ k (measurableSet_singleton _).compl
    have hvol_fn : Measurable
        (fun s : Finset V => (TemporalGraph.volume G.toTemporalGraph 0 s : ℝ)) :=
      measurable_of_countable _
    have h_lt : MeasurableSet[vm.ℱ t_j]
        {ω | (TemporalGraph.volume G.toTemporalGraph 0
            (vm.S (min t_j (embeddedChainTime G.toTemporalGraph vm Δ k ω)) ω) : ℝ) <
            8 * (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ)} :=
      (hvol_fn.comp (hSTk_meas_ℱ k)) measurableSet_Iio
    exact h_ne.inter h_lt
  -- On F, B' agrees with B (the actual indicator set).
  have hB_eq_on_F : ∀ ω ∈ F, Pind ω ↔ ω ∈ B' := by
    intro ω hω
    have h_min_eq : ∀ k ≤ j,
        min t_j (embeddedChainTime G.toTemporalGraph vm Δ k ω) = embeddedChainTime G.toTemporalGraph vm Δ k ω := by
      intro k hk
      have := hT_mono_le_t_j_on_F k hk ω hω
      omega
    simp only [Pind, B', Set.mem_setOf_eq]
    refine ⟨fun h => fun k hk => ?_, fun h => fun k hk => ?_⟩
    · rw [h_min_eq k hk]; exact h k hk
    · have := h k hk; rw [h_min_eq k hk] at this; exact this
  -- Sub-fibers F_F (indicator false) and F_T (indicator true).
  set F_F : Set Ω := F \ B' with hF_F_def
  set F_T : Set Ω := F ∩ B' with hF_T_def
  have hF_F_meas_ℱ : MeasurableSet[vm.ℱ t_j] F_F :=
    hF_meas.diff hB'_meas_ℱ
  have hF_T_meas_ℱ : MeasurableSet[vm.ℱ t_j] F_T :=
    hF_meas.inter hB'_meas_ℱ
  have hF_F_meas : MeasurableSet F_F := vm.ℱ.le t_j _ hF_F_meas_ℱ
  have hF_T_meas : MeasurableSet F_T := vm.ℱ.le t_j _ hF_T_meas_ℱ
  -- F_F ⊆ F and F_T ⊆ F.
  have hF_F_sub : F_F ⊆ F := fun ω hω => hω.1
  have hF_T_sub : F_T ⊆ F := fun ω hω => hω.1
  -- F = F_F ∪ F_T, disjoint.
  have hF_union : F = F_F ∪ F_T := by
    ext ω
    by_cases hB : ω ∈ B'
    · simp [F_F, F_T]
    · simp [F_F, F_T]
  have hF_disjoint : Disjoint F_F F_T := by
    rw [Set.disjoint_left]
    rintro ω ⟨_, hnB⟩ ⟨_, hB⟩
    exact hnB hB
  -- hF_T and hF_S inherit to F_F.
  have hF_F_T : ∀ ω ∈ F_F, embeddedChainTime G.toTemporalGraph vm Δ j ω = t_j :=
    fun ω hω => hF_T ω (hF_F_sub hω)
  have hF_F_S : ∀ ω ∈ F_F, vm.S t_j ω = s_j :=
    fun ω hω => hF_S ω (hF_F_sub hω)
  -- ── Apply L75 (ψ unconditional fiber) to F_F: ∫_{F_F} (ψ(T_{j+1}) − ψ(t_j,s_j)) ≤ 0.
  have hL75 := psi_down_drift_on_fiber G vm s_j t_j Δ hΔ_pos j F_F
    hF_F_meas_ℱ hF_F_T hF_F_S hT_cap
  -- ── Apply L77 (χ unconditional fiber) to F_F: ∫_{F_F} (χ(T_{j+1}, S_{T_{j+1}}) − χ(t_j, s_j)) ≤ 0.
  have hL77 := chi_down_drift_voter_on_fiber G vm s_j t_j Δ hΔ_pos j F_F
    hF_F_meas_ℱ hF_F_T hF_F_S hT_cap
  -- Define short-hand integrands for the per-piece bounds.
  -- On F_F, the if-clause is 0; the integrand equals α·Δψ + Δχ (with ψ(T_j), χ(T_j) ≡ const).
  -- Define: integrand = α·ψ(T_{j+1}) + χ(T_{j+1}, S_{T_{j+1}}) − α·ψ(T_j) − χ(T_j, S_{T_j}) + if-clause.
  -- We use linearity at the integral level.
  -- ── Integral split: ∫_F = ∫_{F_F} + ∫_{F_T}.
  -- First, need integrability of the integrand on F_F and F_T. Use that the integrand is bounded
  -- (the |f| ≤ Cf argument from L51); but since L68 doesn't import that scaffolding here,
  -- we use the simpler fact: the integrand is the sum of measurable bounded functions, hence
  -- integrable on a probability measure.
  -- We avoid that whole route by proving the F_F integral upper bound directly without integrability:
  --
  -- On F_F, integrand(ω) ≤ (α·(ψ(T_{j+1})ω − ψ(t_j, s_j)) + (χ(T_{j+1}, S_{T_{j+1}}) − χ(t_j, s_j))).
  -- (Equality, because the if-clause is 0 on F_F and ψ(T_j) = ψ(t_j, s_j), χ(T_j, S_{T_j}) = χ(t_j, s_j) on F_F.)
  --
  -- Then `∫_{F_F} integrand ≤ ∫_{F_F} (α·Δψ + Δχ) = α·∫_{F_F} Δψ + ∫_{F_F} Δχ ≤ 0` by L75 + L77.
  --
  -- Combined with `∫_F = ∫_{F_F} + ∫_{F_T}`, we get the conclusion.
  -- ── Pointwise rewrite on F_F: integrand = α·Δψ + Δχ (since ψ(T_j) = ψ(t_j,s_j), etc.).
  -- For ω ∈ F_F, since ω ∈ F: T_j ω = t_j and vm.S t_j ω = s_j, so
  --   ψ(T_j ω) ω = ψ(t_j) ω = √(vol(t_j, vm.S t_j ω)) = √(vol(t_j, s_j)) = potential G.toTemporalGraph t_j s_j.
  -- And χ(T_j ω, vm.S(T_j ω)ω) = χ(t_j, vm.S t_j ω) = χ(t_j, s_j) = chiPotential G.toTemporalGraph t_j s_j.
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
  -- ── Pointwise rewrite of the integrand on F_F ─────────────────────────────────
  -- For ω ∈ F_F (⊆ F), the if-clause is 0 (¬Pind), and ψ(T_j)=potential, χ(T_j,·)=chiPotential.
  -- Integrand(ω) = α·(ψ(T_{j+1}) ω − potential G.toTemporalGraph t_j s_j)
  --              + (χ(T_{j+1}, S_{T_{j+1}}) − chiPotential G.toTemporalGraph t_j s_j).
  have hinteg_F_F : ∀ ω ∈ F_F,
      ((α * vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω
          + G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
              (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω)
          - α * vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω
          - G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ j ω)
              (vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω)
          + if Pind ω then min (φ j / 2048) (1 / 2048 : ℝ) else 0)) =
      (α * (vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω
              - TemporalGraph.potential G.toTemporalGraph t_j s_j)
        + (G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
              (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω)
            - G.chiPotential t_j s_j)) := by
    intro ω hω
    have hωF : ω ∈ F := hF_F_sub hω
    have hnotB' : ω ∉ B' := hω.2
    have hnotPind : ¬ Pind ω := fun hP => hnotB' ((hB_eq_on_F ω hωF).mp hP)
    have hψ_eq := hψ_Tj_eq_on_F ω hωF
    have hχ_eq := hχ_Tj_eq_on_F ω hωF
    simp only [if_neg hnotPind]
    rw [hψ_eq, hχ_eq]
    ring
  -- ── Apply L75 + L77 to F_F ────────────────────────────────────────────────────
  -- L75: ∫_{F_F} (ψ(T_{j+1}) − potential) ≤ 0.
  -- L77: ∫_{F_F} (χ(T_{j+1}, S_{T_{j+1}}) − chiPotential) ≤ 0.
  -- Hence ∫_{F_F} (α·Δψ + Δχ) ≤ 0.
  -- ── F_F integral bound: ∫_{F_F} integrand ≤ 0.
  have hF_F_le : ∫ ω in F_F,
      (α * vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω
        + G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
            (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω)
        - α * vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω
        - G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ j ω)
            (vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω)
        + if Pind ω then min (φ j / 2048) (1 / 2048 : ℝ) else 0)
        ∂vm.μ ≤ 0 := by
    -- Step 1: rewrite the integrand via hinteg_F_F.
    have hrw : ∫ ω in F_F,
        (α * vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω
          + G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
              (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω)
          - α * vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω
          - G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ j ω)
              (vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω)
          + if Pind ω then min (φ j / 2048) (1 / 2048 : ℝ) else 0) ∂vm.μ =
        ∫ ω in F_F,
        (α * (vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω
                - TemporalGraph.potential G.toTemporalGraph t_j s_j)
          + (G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
                (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω)
              - G.chiPotential t_j s_j)) ∂vm.μ := by
      apply setIntegral_congr_fun hF_F_meas
      intro ω hω; exact hinteg_F_F ω hω
    rw [hrw]
    -- Step 2: split into ψ-piece (× α) + χ-piece via linearity. Need integrability of each piece.
    -- We use the bounded-integrand fact (volumes are bounded by Vu = vol(univ)) to get integrability.
    -- Set Vu := vol(univ).
    set Vu : ℕ := TemporalGraph.volume G.toTemporalGraph 0 (Finset.univ : Finset V) with hVu_def
    have hVol_le_univ : ∀ t S, TemporalGraph.volume G.toTemporalGraph t S ≤ Vu := by
      intro t S
      have h1 : TemporalGraph.volume G.toTemporalGraph t S ≤ TemporalGraph.volume G.toTemporalGraph t Finset.univ := by
        unfold TemporalGraph.volume SimpleGraph.volume
        exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      have h2 : TemporalGraph.volume G.toTemporalGraph t Finset.univ = Vu :=
        G.volume_fixed _ _ _
      exact h1.trans_eq h2
    -- Measurability of ω ↦ ψ(T_{j+1}) ω and ω ↦ χ(T_{j+1}, S_{T_{j+1}}) ω.
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
    -- Bounds: ψ(T_k) ≤ √Vu, χ(T_k, ·) ≤ log(1 + Vu).
    have hψ_int : Integrable
        (fun ω => vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω -
          TemporalGraph.potential G.toTemporalGraph t_j s_j) vm.μ := by
      refine MeasureTheory.Integrable.of_bound
        (C := Real.sqrt (Vu : ℝ) + TemporalGraph.potential G.toTemporalGraph t_j s_j)
        ((hψE_meas (j + 1)).sub_const _).aestronglyMeasurable
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
        ((hχE_meas (j + 1)).sub_const _).aestronglyMeasurable
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
    -- Step 3: split the integral by linearity.
    have hint_eq : ∫ ω in F_F,
        (α * (vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω
                - TemporalGraph.potential G.toTemporalGraph t_j s_j)
          + (G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
                (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω)
              - G.chiPotential t_j s_j)) ∂vm.μ =
        α * ∫ ω in F_F,
          (vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω -
            TemporalGraph.potential G.toTemporalGraph t_j s_j) ∂vm.μ +
        ∫ ω in F_F,
          (G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
              (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω) -
            G.chiPotential t_j s_j) ∂vm.μ := by
      rw [integral_add (hψ_int.const_mul _).integrableOn hχ_int.integrableOn]
      rw [integral_const_mul]
    rw [hint_eq]
    have h_psi := mul_le_mul_of_nonneg_left hL75 hα_nn
    simp only [mul_zero] at h_psi
    linarith
  -- ── F_T integral. Cases 2+3 of the dichotomy via L92 joint dispatch. ────────
  -- The F_T integrand matches L92's integrand once we
  -- (a) reduce `if Pind then Dj else 0 = Dj` on F_T (Pind holds since F_T ⊆ B'),
  -- (b) extract `vol(0, s_j) < 8·vol(0, s_0)` and `s_j ≠ ∅` from `Pind` at k = j,
  -- (c) supply L92's `hdispatch : StableBundle ∨ UnstableBundle` (the remaining
  --     residual obligation — see BLOCKER L68-F_T-dispatch).
  have hF_T_le : ∫ ω in F_T,
      (α * vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω
        + G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
            (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω)
        - α * vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω
        - G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ j ω)
            (vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω)
        + if Pind ω then min (φ j / 2048) (1 / 2048 : ℝ) else 0)
        ∂vm.μ ≤ 0 := by
    -- Step A: Handle empty F_T trivially.
    by_cases hF_T_empty : F_T = ∅
    · rw [hF_T_empty]
      simp
    -- Step B: F_T nonempty: extract Pind data from any ω ∈ F_T (specifically k = j).
    have hF_T_ne : F_T.Nonempty := Set.nonempty_iff_ne_empty.mpr hF_T_empty
    obtain ⟨ω₀, hω₀⟩ := hF_T_ne
    have hω₀_F : ω₀ ∈ F := hF_T_sub hω₀
    have hω₀_B' : ω₀ ∈ B' := hω₀.2
    have hω₀_Pind : Pind ω₀ := (hB_eq_on_F ω₀ hω₀_F).mpr hω₀_B'
    -- At k = j, Pind gives `vm.S t_j ω₀ ≠ ∅` and `vol(0, vm.S t_j ω₀) < 8 vol(0, s_0)`.
    -- Combined with hF_S (vm.S t_j ω₀ = s_j), this yields `s_j ≠ ∅` and the volume bound.
    have hPind_j : (vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω₀) ω₀) ≠ ∅ ∧
        (TemporalGraph.volume G.toTemporalGraph 0 (vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω₀) ω₀) : ℝ) <
          8 * (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) := hω₀_Pind j (le_refl j)
    have hTj_ω₀ : embeddedChainTime G.toTemporalGraph vm Δ j ω₀ = t_j := hF_T ω₀ hω₀_F
    have hS_t_j_ω₀ : vm.S t_j ω₀ = s_j := hF_S ω₀ hω₀_F
    have hs_j_ne_empty : s_j ≠ ∅ := by
      have h := hPind_j.1
      rw [hTj_ω₀, hS_t_j_ω₀] at h
      exact h
    have hs_j_ne : s_j.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs_j_ne_empty
    have hvol_lt : (TemporalGraph.volume G.toTemporalGraph 0 s_j : ℝ) <
        8 * (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) := by
      have h := hPind_j.2
      rw [hTj_ω₀, hS_t_j_ω₀] at h
      exact h
    -- Step C: Reduce the integrand on F_T. On F_T, Pind holds, so the if-clause
    -- equals min(φ_j/2048, 1/2048). Also rewrite (α·ψ - α·ψ) as α·(ψ - ψ).
    have hPind_on_F_T : ∀ ω ∈ F_T, Pind ω := fun ω hω =>
      (hB_eq_on_F ω (hF_T_sub hω)).mpr hω.2
    have hintegrand_eq : ∀ ω ∈ F_T,
        ((α * vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω
          + G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
              (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω)
          - α * vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω
          - G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ j ω)
              (vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω)
          + if Pind ω then min (φ j / 2048) (1 / 2048 : ℝ) else 0)) =
        ((α * (vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω
                - vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω)
          + (G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
                (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω)
              - G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ j ω)
                (vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω))
          + min (φ j / 2048) (1 / 2048 : ℝ))) := by
      intro ω hω
      rw [if_pos (hPind_on_F_T ω hω)]
      ring
    rw [setIntegral_congr_fun hF_T_meas (fun ω hω => hintegrand_eq ω hω)]
    -- Step D: Apply L92. Requires the 3-way `(Case1 ∨ Case2) ∨ Unstable` dispatch.
    -- We supply hF_T_meas_ℱ, hF_T_T (restricted to F_T), hF_T_S (restricted to F_T), etc.
    have hF_T_T : ∀ ω ∈ F_T, embeddedChainTime G.toTemporalGraph vm Δ j ω = t_j :=
      fun ω hω => hF_T ω (hF_T_sub hω)
    have hF_T_S : ∀ ω ∈ F_T, vm.S t_j ω = s_j :=
      fun ω hω => hF_S ω (hF_T_sub hω)
    -- ── L68 F_T-dispatch closure ─────────────────────────────────────────
    -- Derive admissibility of s_j (needed by L98 inside the helper), then
    -- delegate to `psi_chi_combined_F_T_closure_on_fiber`.
    -- s_j is a minority set at time t_j (via vm.S t_j ω₀ = s_j).
    have hs_j_minority : TemporalGraph.volume G.toTemporalGraph t_j s_j ≤
        TemporalGraph.volume G.toTemporalGraph t_j (Finset.univ \ s_j) := by
      have h := VoterModel.minoritySet_isMinority G.toTemporalGraph t_j (vm.opinionZeroSet t_j ω₀)
      have h' : TemporalGraph.volume G.toTemporalGraph t_j (vm.S t_j ω₀) ≤
          TemporalGraph.volume G.toTemporalGraph t_j (Finset.univ \ vm.S t_j ω₀) := h
      rw [hS_t_j_ω₀] at h'
      exact h'
    have hVol_sj_pos_nat : 0 < TemporalGraph.volume G.toTemporalGraph t_j s_j := by
      obtain ⟨v, hv⟩ := hs_j_ne
      have hd_le : d_min ≤ G.degree t_j v := by
        rw [hd, G.minDegreeAt_eq 0 t_j]
        exact G.minDegreeAt_le_degree t_j v
      have hv_deg_pos : 0 < G.degree t_j v := lt_of_lt_of_le hd_pos hd_le
      have h_le_vol : G.degree t_j v ≤ TemporalGraph.volume G.toTemporalGraph t_j s_j := by
        unfold TemporalGraph.volume SimpleGraph.volume
        exact Finset.single_le_sum (f := fun u => G.degree t_j u)
          (fun u _ => Nat.zero_le _) hv
      exact lt_of_lt_of_le hv_deg_pos h_le_vol
    have hVol_0_sj_eq_nat :
        TemporalGraph.volume G.toTemporalGraph 0 s_j = TemporalGraph.volume G.toTemporalGraph t_j s_j :=
      G.volume_fixed s_j 0 t_j
    have hVol_0_univ_eq_nat :
        TemporalGraph.volume G.toTemporalGraph 0 (Finset.univ : Finset V) =
        TemporalGraph.volume G.toTemporalGraph t_j (Finset.univ : Finset V) :=
      G.volume_fixed (Finset.univ : Finset V) 0 t_j
    have hVol_0_comp_eq_nat :
        TemporalGraph.volume G.toTemporalGraph 0 (Finset.univ \ s_j) =
        TemporalGraph.volume G.toTemporalGraph t_j (Finset.univ \ s_j) :=
      G.volume_fixed (Finset.univ \ s_j) 0 t_j
    have hVol_univ_split_t_j : TemporalGraph.volume G.toTemporalGraph t_j
        (Finset.univ : Finset V) =
        TemporalGraph.volume G.toTemporalGraph t_j s_j +
        TemporalGraph.volume G.toTemporalGraph t_j (Finset.univ \ s_j) := by
      unfold TemporalGraph.volume SimpleGraph.volume
      rw [← Finset.sum_union (Finset.disjoint_sdiff)]
      congr 1
      rw [Finset.union_sdiff_of_subset (Finset.subset_univ s_j)]
    have hs_j_ne_univ : s_j ≠ Finset.univ := by
      intro hs_j_eq
      rw [hs_j_eq] at hs_j_minority
      have hcomp_eq : Finset.univ \ (Finset.univ : Finset V) = ∅ :=
        Finset.sdiff_self _
      rw [hcomp_eq] at hs_j_minority
      have hvol_empty : TemporalGraph.volume G.toTemporalGraph t_j (∅ : Finset V) = 0 := by
        unfold TemporalGraph.volume SimpleGraph.volume; simp
      rw [hvol_empty] at hs_j_minority
      rw [hs_j_eq] at hVol_sj_pos_nat
      omega
    have hVol_univ_pos_nat : 0 < TemporalGraph.volume G.toTemporalGraph 0
        (Finset.univ : Finset V) := by
      rw [hVol_0_univ_eq_nat, hVol_univ_split_t_j]
      omega
    have hVol_0_sj_pos_nat : 0 < TemporalGraph.volume G.toTemporalGraph 0 s_j := by
      rw [hVol_0_sj_eq_nat]; exact hVol_sj_pos_nat
    have hRel_le_half : TemporalGraph.relativeVolume G.toTemporalGraph s_j ≤ 1 / 2 := by
      show (G.snapshot 0).relativeVolume s_j ≤ 1 / 2
      unfold SimpleGraph.relativeVolume
      have hvol_univ_pos_ℚ : (0 : ℚ) < ((G.snapshot 0).volume Finset.univ : ℚ) := by
        have : 0 < (G.snapshot 0).volume Finset.univ := hVol_univ_pos_nat
        exact_mod_cast this
      rw [div_le_iff₀ hvol_univ_pos_ℚ]
      have hVol_univ_split_0 : (G.snapshot 0).volume Finset.univ =
          (G.snapshot 0).volume s_j + (G.snapshot 0).volume (Finset.univ \ s_j) := by
        have h := hVol_univ_split_t_j
        rw [← hVol_0_sj_eq_nat, ← hVol_0_comp_eq_nat, ← hVol_0_univ_eq_nat] at h
        exact h
      have h_minority_0 : (G.snapshot 0).volume s_j ≤
          (G.snapshot 0).volume (Finset.univ \ s_j) := by
        have h0 : TemporalGraph.volume G.toTemporalGraph 0 s_j ≤
            TemporalGraph.volume G.toTemporalGraph 0 (Finset.univ \ s_j) := by
          rw [hVol_0_sj_eq_nat, hVol_0_comp_eq_nat]; exact hs_j_minority
        exact h0
      rw [hVol_univ_split_0]
      push_cast
      have h_minority_ℚ :
          ((G.snapshot 0).volume s_j : ℚ) ≤
            ((G.snapshot 0).volume (Finset.univ \ s_j) : ℚ) := by
        exact_mod_cast h_minority_0
      linarith
    have hRel_pos : 0 < TemporalGraph.relativeVolume G.toTemporalGraph s_j := by
      show 0 < (G.snapshot 0).relativeVolume s_j
      unfold SimpleGraph.relativeVolume
      have hvol_univ_pos_ℚ : (0 : ℚ) < ((G.snapshot 0).volume Finset.univ : ℚ) := by
        have : 0 < (G.snapshot 0).volume Finset.univ := hVol_univ_pos_nat
        exact_mod_cast this
      have hvol_sj_pos_ℚ : (0 : ℚ) < ((G.snapshot 0).volume s_j : ℚ) := by
        have : 0 < (G.snapshot 0).volume s_j := hVol_0_sj_pos_nat
        exact_mod_cast this
      positivity
    have hs_j_adm : s_j ∈ TemporalGraph.admissibleCuts G.toTemporalGraph :=
      (TemporalGraph.mem_admissibleCuts_iff_relativeVolume G.toTemporalGraph (fun v => G.degrees_pos v 0) s_j).mpr
        ⟨hs_j_ne, hs_j_ne_univ, hRel_pos, hRel_le_half⟩
    have ht_j_le_lo : t_j ≤ ∑ k ∈ Finset.range j, Δ k := by
      have hbd := embeddedChainTime_le_sum_tight G.toTemporalGraph vm Δ hΔ_pos j ω₀
      rw [hTj_ω₀] at hbd
      exact hbd
    exact psi_chi_combined_F_T_closure_on_fiber G vm d_min hd hd_pos
      s_0 hs_0_ne s_j hs_j_ne t_j Δ hΔ_pos φ hφ_nn hwin j hvol_lt F_T
      hF_T_meas_ℱ hF_T_T hF_T_S hT_cap hs_j_adm ht_j_le_lo
  -- ── Final assembly: ∫_F = ∫_{F_F} + ∫_{F_T} ≤ 0 + 0 = 0. ──────────────────────
  have hF_eq_union : F = F_F ∪ F_T := hF_union
  -- Integrability of the integrand on F_F and F_T (needed for additivity).
  -- We bound the integrand by Cf and use Integrable.of_bound (the same argument as in L51).
  set Vu : ℕ := TemporalGraph.volume G.toTemporalGraph 0 (Finset.univ : Finset V) with hVu_def
  have hVol_le_univ : ∀ t S, TemporalGraph.volume G.toTemporalGraph t S ≤ Vu := by
    intro t S
    have h1 : TemporalGraph.volume G.toTemporalGraph t S ≤ TemporalGraph.volume G.toTemporalGraph t Finset.univ := by
      unfold TemporalGraph.volume SimpleGraph.volume
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have h2 : TemporalGraph.volume G.toTemporalGraph t Finset.univ = Vu :=
      G.volume_fixed _ _ _
    exact h1.trans_eq h2
  set Cf : ℝ := 2 * (α * Real.sqrt (Vu : ℝ) + |Real.log (1 + (Vu : ℝ))|) + (1 / 2048 : ℝ)
    with hCf_def
  -- Measurability of the full integrand `f`.
  have hT_meas2 : ∀ k, Measurable (embeddedChainTime G.toTemporalGraph vm Δ k) := by
    intro k s _
    rw [show (embeddedChainTime G.toTemporalGraph vm Δ k) ⁻¹' s =
        ⋃ u ∈ s, {w | embeddedChainTime G.toTemporalGraph vm Δ k w = u} from by ext ω; simp]
    refine MeasurableSet.biUnion (Set.to_countable s) (fun u _ => ?_)
    have heq2 : {w : Ω | embeddedChainTime G.toTemporalGraph vm Δ k w = u} =
        {w | (embeddedChainTime G.toTemporalGraph vm Δ k w : ℕ∞) = ↑u} := by
      ext w
      exact ⟨fun heq => by exact_mod_cast heq, fun heq => by exact_mod_cast heq⟩
    rw [heq2]; exact vm.ℱ.le u _ ((hT_stop k).measurableSet_eq u)
  have hψE_meas2 : ∀ k, Measurable (fun ω => vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) := by
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
    exact (hT_meas2 k (measurableSet_singleton _)).inter (hpsi_meas hS)
  have hχE_meas2 : ∀ k, Measurable (fun ω => G.chiPotential
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
    exact (hT_meas2 k (measurableSet_singleton _)).inter (hchi_meas hS)
  -- Measurability of the indicator-set Pind (at top level).
  have h_set_meas_top : MeasurableSet {ω : Ω | Pind ω} := by
    simp only [Pind]
    rw [show {ω : Ω | ∀ k ≤ j,
        (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) ≠ ∅ ∧
        (TemporalGraph.volume G.toTemporalGraph 0 (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) : ℝ) <
          8 * (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ)} =
        ⋂ k ∈ Finset.Iic j, ({ω : Ω |
          (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) ≠ ∅} ∩
          {ω : Ω |
            (TemporalGraph.volume G.toTemporalGraph 0 (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) : ℝ) <
            8 * (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ)}) from by
          ext ω; simp [Finset.mem_Iic, Set.mem_inter_iff]]
    refine MeasurableSet.biInter (Set.to_countable _) (fun k _ => ?_)
    have hS_emb_meas : Measurable (fun ω => vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) := by
      intro S hS
      rw [show (fun ω => vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) ⁻¹' S =
          ⋃ t : ℕ, (embeddedChainTime G.toTemporalGraph vm Δ k) ⁻¹' {t} ∩ (vm.S t) ⁻¹' S
          from by ext ω; simp [eq_comm]]
      refine MeasurableSet.iUnion (fun t => ?_)
      exact (hT_meas2 k (measurableSet_singleton _)).inter
        (vm.ℱ.le t _ (hS_meas_ℱ t hS))
    have hvol : Measurable (fun s : Finset V => (TemporalGraph.volume G.toTemporalGraph 0 s : ℝ)) :=
      measurable_of_countable _
    have h_ne : MeasurableSet
        {ω : Ω | (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) ≠ ∅} :=
      hS_emb_meas (measurableSet_singleton _).compl
    exact h_ne.inter ((hvol.comp hS_emb_meas) measurableSet_Iio)
  -- Full integrand measurability.
  have hf_meas : Measurable
      (fun ω => α * vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω
        + G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
            (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω)
        - α * vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω
        - G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ j ω)
            (vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω)
        + if Pind ω then min (φ j / 2048) (1 / 2048 : ℝ) else 0) := by
    refine Measurable.add ?_ (Measurable.ite h_set_meas_top measurable_const measurable_const)
    refine Measurable.sub ?_ (hχE_meas2 j)
    refine Measurable.sub ?_ ((hψE_meas2 j).const_mul _)
    exact (hψE_meas2 (j + 1)).const_mul _ |>.add (hχE_meas2 (j + 1))
  -- Bound: |integrand ω| ≤ Cf.
  have hψ_nn : ∀ k ω, 0 ≤ vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω := fun k ω => by
    show TemporalGraph.potential G.toTemporalGraph _ _ ≥ 0
    exact Real.sqrt_nonneg _
  have hψ_bnd : ∀ k ω, vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω ≤ Real.sqrt (Vu : ℝ) :=
    fun k ω => by
      show TemporalGraph.potential G.toTemporalGraph _ _ ≤ _
      apply Real.sqrt_le_sqrt
      exact_mod_cast hVol_le_univ _ _
  have hχ_nn : ∀ k ω, 0 ≤ G.chiPotential
      (embeddedChainTime G.toTemporalGraph vm Δ k ω) (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) := fun k ω => by
    unfold TemporalGraphFixedDegree.chiPotential TemporalGraph.chiPotential
    apply Real.log_nonneg
    have h0 : (0 : ℝ) ≤ (TemporalGraph.volume G.toTemporalGraph (embeddedChainTime G.toTemporalGraph vm Δ k ω)
        (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) : ℝ) := Nat.cast_nonneg _
    linarith
  have hχ_bnd : ∀ k ω, G.chiPotential
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
  have hf_abs : ∀ ω, |α * vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω
        + G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
            (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω)
        - α * vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω
        - G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ j ω)
            (vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω)
        + (if Pind ω then min (φ j / 2048) (1 / 2048 : ℝ) else 0)| ≤ Cf := by
    intro ω
    have h1 := hψ_nn (j + 1) ω
    have h2 := hψ_bnd (j + 1) ω
    have h3 := hψ_nn j ω
    have h4 := hψ_bnd j ω
    have h5 := hχ_nn (j + 1) ω
    have h6 := hχ_bnd (j + 1) ω
    have h7 := hχ_nn j ω
    have h8 := hχ_bnd j ω
    have hsqrtu : 0 ≤ Real.sqrt (Vu : ℝ) := Real.sqrt_nonneg _
    have habs_log_nn : 0 ≤ |Real.log (1 + (Vu : ℝ))| := abs_nonneg _
    have hlog_le : Real.log (1 + (Vu : ℝ)) ≤ |Real.log (1 + (Vu : ℝ))| := le_abs_self _
    have hlog_ge : -|Real.log (1 + (Vu : ℝ))| ≤ Real.log (1 + (Vu : ℝ)) := neg_abs_le _
    have hαmul1 := mul_nonneg hα_nn h1
    have hαmul3 := mul_nonneg hα_nn h3
    have hαmul2 : α * vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω ≤
        α * Real.sqrt (Vu : ℝ) :=
      mul_le_mul_of_nonneg_left h2 hα_nn
    have hαmul4 : α * vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω ≤
        α * Real.sqrt (Vu : ℝ) :=
      mul_le_mul_of_nonneg_left h4 hα_nn
    by_cases hcase : Pind ω
    · simp only [if_pos hcase]
      have hmin_le : min (φ j / 2048) (1 / 2048 : ℝ) ≤ 1 / 2048 := min_le_right _ _
      have hmin_nn : 0 ≤ min (φ j / 2048) (1 / 2048 : ℝ) :=
        le_min (div_nonneg (hφ_nn j) (by norm_num)) (by norm_num)
      simp only [Cf]
      rw [abs_le]
      refine ⟨?_, ?_⟩ <;> linarith
    · simp only [if_neg hcase, add_zero]
      simp only [Cf]
      rw [abs_le]
      refine ⟨?_, ?_⟩ <;> linarith
  have hf_int : Integrable
      (fun ω => α * vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω
        + G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
            (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω)
        - α * vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω
        - G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ j ω)
            (vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω)
        + if Pind ω then min (φ j / 2048) (1 / 2048 : ℝ) else 0) vm.μ := by
    refine MeasureTheory.Integrable.of_bound (C := Cf) hf_meas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs]; exact hf_abs ω
  -- Assemble: ∫_F = ∫_{F_F} + ∫_{F_T} ≤ 0 + 0 = 0.
  have h_split : ∫ ω in F, (α * vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω
        + G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
            (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω)
        - α * vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω
        - G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ j ω)
            (vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω)
        + if Pind ω then min (φ j / 2048) (1 / 2048 : ℝ) else 0) ∂vm.μ =
      (∫ ω in F_F, (α * vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω
        + G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
            (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω)
        - α * vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω
        - G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ j ω)
            (vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω)
        + if Pind ω then min (φ j / 2048) (1 / 2048 : ℝ) else 0) ∂vm.μ) +
      (∫ ω in F_T, (α * vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω
        + G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
            (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω)
        - α * vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω
        - G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ j ω)
            (vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω)
        + if Pind ω then min (φ j / 2048) (1 / 2048 : ℝ) else 0) ∂vm.μ) := by
    rw [hF_eq_union]
    exact MeasureTheory.setIntegral_union hF_disjoint hF_T_meas
      hf_int.integrableOn hf_int.integrableOn
  -- The integrand of L68 is α-rewritten relative to the L68 statement: α = √vol(s_0)/d_min.
  -- The theorem statement uses (Real.sqrt ... / d_min), which is exactly α by definition.
  -- Pind is definitionally equal to the indicator inside the if.
  show ∫ ω in F, _ ∂vm.μ ≤ 0
  have h_integrand_eq : (fun ω =>
      (Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) / d_min)
        * vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω
      + G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
          (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω)
      - (Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) / d_min)
          * vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω
      - G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ j ω)
          (vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω)
      + if ∀ k ≤ j,
            (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) ≠ ∅ ∧
            (TemporalGraph.volume G.toTemporalGraph 0 (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) : ℝ) <
            8 * (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ)
        then min (φ j / 2048) (1 / 2048 : ℝ) else 0) =
      (fun ω =>
      α * vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω
      + G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
          (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω)
      - α * vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω
      - G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ j ω)
          (vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω)
      + if Pind ω then min (φ j / 2048) (1 / 2048 : ℝ) else 0) := by
    funext ω; rfl
  rw [h_integrand_eq]
  rw [h_split]
  linarith [hF_F_le, hF_T_le]

/-- \label{lem:psi-chi-combined-drift-integrated}

**Integrated per-step combined-drift bound** (Lean-only helper for L50).

Let `Ψ_j(ω) = (√vol(s_0)/d_min)·√vol(S_{T_j}(ω)) + log(1 + vol(S_{T_j}(ω)))` and
`D_j(ω) = min(φ_j/2048, 1/2048)` if `vol(S_{T_k}(ω)) < 8·vol(s_0)` for all `k ≤ j`, else 0.

Then `∫ (Ψ_{j+1} − Ψ_j + D_j) dμ ≤ 0`.

Proof strategy: partition Ω by the deterministic fibers
`F_{t,s} := {ω | T_j ω = t ∧ vm.S t ω = s}` for `(t, s) ∈ Finset.Iic K × Finset.univ`,
where `K = ∑ k ∈ range (j+1), Δ k` bounds `T_j` (by `embeddedChainTime_le_sum`).
The fibers form a finite measurable partition of `Ω` (up to a null set, in fact
exhaustively for all ω). Then
  `∫ f dμ = Σ_{(t,s)} ∫_{F_{t,s}} f dμ ≤ 0`
since each summand is ≤ 0 by the per-fiber bound `psi_chi_combined_setIntegral_on_fiber_le`. -/
lemma psi_chi_combined_drift_integrated
    {Ω : Type*} [MeasurableSpace Ω]
    (G : TemporalGraphFixedDegree V)
    (vm : G.VoterModelAbstract 2 Ω)
    (d_min : ℕ) (hd : d_min = G.minDegreeAt 0) (hd_pos : 0 < d_min)
    (s_0 : Finset V) (hs_0_ne : s_0.Nonempty)
    (Δ : ℕ → ℕ) (hΔ_pos : ∀ j, 1 ≤ Δ j)
    (φ : ℕ → ℝ) (hφ_nn : ∀ j, 0 ≤ φ j)
    -- Window-guarantee hypothesis (per-interval MAX-form, paper's
    -- `φ^{I_j}(𝒢) ≥ φ_j`).
    (hwin : ∀ j, ∀ S ∈ G.admissibleCuts,
      φ j ≤ G.maxSetConductanceOnInterval (∑ i ∈ Finset.range j, Δ i) (Δ j) S)
    (j : ℕ) :
    ∫ ω,
      ((Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) / d_min)
          * vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω
        + G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
            (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω)
        - (Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) / d_min)
            * vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω
        - G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ j ω)
            (vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω)
        + if ∀ k ≤ j,
              (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) ≠ ∅ ∧
              (TemporalGraph.volume G.toTemporalGraph 0 (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) : ℝ) <
              8 * (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ)
          then min (φ j / 2048) (1 / 2048 : ℝ) else 0)
      ∂vm.μ ≤ 0 := by
  -- ── Setup: integrand `f`, cap `K`, measurability scaffolding ─────────────────
  classical
  haveI hprob : IsProbabilityMeasure (vm.μ : Measure Ω) := inferInstance
  set f : Ω → ℝ := fun ω =>
      (Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) / d_min)
          * vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω
        + G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
            (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω)
        - (Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) / d_min)
            * vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω
        - G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ j ω)
            (vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω)
        + if ∀ k ≤ j,
              (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) ≠ ∅ ∧
              (TemporalGraph.volume G.toTemporalGraph 0 (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) : ℝ) <
              8 * (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ)
          then min (φ j / 2048) (1 / 2048 : ℝ) else 0 with hf_def
  -- Tight bound for T_j (the partition indexes over t ∈ Iic K with paper-tight K).
  set K : ℕ := ∑ k ∈ Finset.range j, Δ k with hK_def
  have hT_le_K : ∀ ω, embeddedChainTime G.toTemporalGraph vm Δ j ω ≤ K :=
    fun ω => embeddedChainTime_le_sum_tight G.toTemporalGraph vm Δ hΔ_pos j ω
  -- The paper-tight cap for the (j+1)-th interval, t_j ≤ (∑ range(j+1) Δ) - 1.
  have hcap_K : ∀ t, t ≤ K → t ≤ (∑ k ∈ Finset.range (j + 1), Δ k) - 1 := by
    intro t ht
    have hsum_eq : ∑ k ∈ Finset.range (j + 1), Δ k =
        ∑ k ∈ Finset.range j, Δ k + Δ j := Finset.sum_range_succ Δ j
    have h2 : 1 ≤ Δ j := hΔ_pos _
    omega
  -- Stopping-time / measurability scaffolding.
  have hS_meas_ℱ : ∀ t, @Measurable Ω (Finset V) (vm.ℱ t) ⊤ (vm.S t) := fun t =>
    (measurable_of_countable (fun A => VoterModel.minoritySet G.toTemporalGraph t A)).comp
      (vm.A_stronglyAdapted t).measurable
  have hT_stop : ∀ k,
      IsStoppingTime vm.ℱ (fun ω => (embeddedChainTime G.toTemporalGraph vm Δ k ω : ℕ∞)) := fun k =>
    embeddedChainTime_isStoppingTime G.toTemporalGraph vm Δ hS_meas_ℱ k
  -- {T_j = t} ∈ ℱ_t.
  have hT_eq_meas_ℱ : ∀ t, MeasurableSet[vm.ℱ t]
      {ω | embeddedChainTime G.toTemporalGraph vm Δ j ω = t} := by
    intro t
    have h := (hT_stop j).measurableSet_eq t
    have heq : {ω | embeddedChainTime G.toTemporalGraph vm Δ j ω = t} =
        {ω | (embeddedChainTime G.toTemporalGraph vm Δ j ω : ℕ∞) = ↑t} := by
      ext w
      exact ⟨fun heq => by exact_mod_cast heq, fun heq => by exact_mod_cast heq⟩
    rw [heq]; exact h
  -- {S t = s} ∈ ℱ_t.
  have hS_eq_meas_ℱ : ∀ t s, MeasurableSet[vm.ℱ t] {ω | vm.S t ω = s} := fun t s =>
    hS_meas_ℱ t (measurableSet_singleton s)
  -- Define the fiber set.
  set F : ℕ → Finset V → Set Ω := fun t s =>
    {ω | embeddedChainTime G.toTemporalGraph vm Δ j ω = t} ∩ {ω | vm.S t ω = s} with hF_def
  have hF_meas_ℱ : ∀ t s, MeasurableSet[vm.ℱ t] (F t s) := fun t s =>
    (hT_eq_meas_ℱ t).inter (hS_eq_meas_ℱ t s)
  have hF_meas : ∀ t s, MeasurableSet (F t s) := fun t s =>
    vm.ℱ.le t _ (hF_meas_ℱ t s)
  -- F t s satisfies the deterministic-fiber identification.
  have hF_T : ∀ t s ω, ω ∈ F t s → embeddedChainTime G.toTemporalGraph vm Δ j ω = t := by
    intro t s ω hω; exact hω.1
  have hF_S : ∀ t s ω, ω ∈ F t s → vm.S t ω = s := by
    intro t s ω hω; exact hω.2
  -- Pairwise disjoint family over the finite index set Finset.Iic K × Finset.univ.
  set I : Finset (ℕ × Finset V) := (Finset.Iic K) ×ˢ (Finset.univ : Finset (Finset V))
    with hI_def
  have hF_disjoint : (↑I : Set (ℕ × Finset V)).Pairwise
      (Function.onFun Disjoint (fun p => F p.1 p.2)) := by
    intro ⟨t1, s1⟩ _ ⟨t2, s2⟩ _ hne
    refine Set.disjoint_iff_inter_eq_empty.mpr ?_
    ext ω
    simp only [Set.mem_inter_iff, F, Set.mem_inter_iff, Set.mem_setOf_eq,
      Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨hT1, hS1⟩, hT2, hS2⟩
    apply hne
    have ht : t1 = t2 := hT1.symm.trans hT2
    rw [ht] at hS1
    exact Prod.mk.injEq .. |>.mpr ⟨ht, hS1.symm.trans hS2⟩
  -- Cover: every ω lies in F (T_j ω) (vm.S (T_j ω) ω), which has index in I.
  have hF_cover : ∀ ω, ω ∈ ⋃ p ∈ I, F p.1 p.2 := by
    intro ω
    rw [Set.mem_iUnion]
    refine ⟨(embeddedChainTime G.toTemporalGraph vm Δ j ω, vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω), ?_⟩
    rw [Set.mem_iUnion]
    refine ⟨?_, ?_⟩
    · simp only [I, Finset.mem_product, Finset.mem_Iic, Finset.mem_univ, and_true]
      exact hT_le_K ω
    · simp [F]
  -- Per-fiber bound: each summand ≤ 0.
  have hper_fiber : ∀ p ∈ I, ∫ ω in F p.1 p.2, f ω ∂vm.μ ≤ 0 := by
    rintro ⟨t, s⟩ hp
    simp only [I, Finset.mem_product, Finset.mem_Iic, Finset.mem_univ, and_true] at hp
    have htK : t ≤ K := hp
    have hcap_t : t ≤ (∑ k ∈ Finset.range (j + 1), Δ k) - 1 := hcap_K t htK
    exact psi_chi_combined_setIntegral_on_fiber_le G vm d_min hd hd_pos s_0
      hs_0_ne Δ hΔ_pos φ hφ_nn hwin j t s (F t s)
      (hF_meas_ℱ t s) (hF_T t s) (hF_S t s) hcap_t
  -- Integrability of f.
  -- Bounds for the ψ and χ components at any time t.
  set Vu : ℕ := TemporalGraph.volume G.toTemporalGraph 0 (Finset.univ : Finset V) with hVu_def
  have hVol_le_univ : ∀ t S, TemporalGraph.volume G.toTemporalGraph t S ≤ Vu := by
    intro t S
    have h1 : TemporalGraph.volume G.toTemporalGraph t S ≤ TemporalGraph.volume G.toTemporalGraph t Finset.univ := by
      unfold TemporalGraph.volume SimpleGraph.volume
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have h2 : TemporalGraph.volume G.toTemporalGraph t Finset.univ = Vu :=
      G.volume_fixed _ _ _
    exact h1.trans_eq h2
  have hα_nn : (0 : ℝ) ≤ Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) / (d_min : ℝ) :=
    div_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _)
  -- The integrand `f` is bounded pointwise; hence integrable on probability measure.
  -- Pointwise bound: |f ω| ≤ 2·(α·√Vu + |log(1+Vu)|) + 1/2048.
  set Cf : ℝ := 2 * ((Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) / d_min) * Real.sqrt (Vu : ℝ)
      + |Real.log (1 + (Vu : ℝ))|) + (1 / 2048 : ℝ) with hCf_def
  -- Measurability of `f` requires measurability of vm.psiS and chiPotential at embedded times.
  -- We prove `f` is measurable via decomposition (mirrors the integrability proof in L50).
  have hψE_meas : ∀ k, Measurable (fun ω => vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) := by
    intro k S hS
    rw [show (fun ω => vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) ⁻¹' S =
        ⋃ t : ℕ, (embeddedChainTime G.toTemporalGraph vm Δ k) ⁻¹' {t} ∩ (vm.psiS t) ⁻¹' S from by
      ext ω
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_singleton_iff]
      constructor
      · intro h; exact ⟨embeddedChainTime G.toTemporalGraph vm Δ k ω, rfl, h⟩
      · rintro ⟨t, heq, hp⟩
        show vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω ∈ S
        rw [heq]; exact hp]
    refine MeasurableSet.iUnion (fun t => ?_)
    have hT_meas : Measurable (embeddedChainTime G.toTemporalGraph vm Δ k) := by
      intro s _
      rw [show (embeddedChainTime G.toTemporalGraph vm Δ k) ⁻¹' s =
          ⋃ u ∈ s, {w | embeddedChainTime G.toTemporalGraph vm Δ k w = u} from by ext ω; simp]
      refine MeasurableSet.biUnion (Set.to_countable s) (fun u _ => ?_)
      have heq2 : {w : Ω | embeddedChainTime G.toTemporalGraph vm Δ k w = u} =
          {w | (embeddedChainTime G.toTemporalGraph vm Δ k w : ℕ∞) = ↑u} := by
        ext w
        exact ⟨fun heq => by exact_mod_cast heq, fun heq => by exact_mod_cast heq⟩
      rw [heq2]; exact vm.ℱ.le u _ ((hT_stop k).measurableSet_eq u)
    have hpsi_meas : Measurable (vm.psiS t) := by
      have h1 : Measurable (fun ω => (TemporalGraph.volume G.toTemporalGraph t (vm.S t ω) : ℝ)) := by
        have hvol_fn : Measurable
            (fun s : Finset V => (TemporalGraph.volume G.toTemporalGraph t s : ℝ)) :=
          measurable_of_countable _
        have hS_t : Measurable (vm.S t) := fun S hS => vm.ℱ.le t _ ((hS_meas_ℱ t) hS)
        exact hvol_fn.comp hS_t
      show Measurable (fun ω => Real.sqrt (TemporalGraph.volume G.toTemporalGraph t (vm.S t ω) : ℝ))
      exact Real.continuous_sqrt.measurable.comp h1
    exact (hT_meas (measurableSet_singleton _)).inter (hpsi_meas hS)
  have hχE_meas_full : ∀ k, Measurable (fun ω => G.chiPotential
      (embeddedChainTime G.toTemporalGraph vm Δ k ω) (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω)) := by
    intro k S hS
    rw [show (fun ω => G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ k ω)
        (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω)) ⁻¹' S =
        ⋃ t : ℕ, (embeddedChainTime G.toTemporalGraph vm Δ k) ⁻¹' {t} ∩
          (fun ω => G.chiPotential t (vm.S t ω)) ⁻¹' S from by
      ext ω
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_singleton_iff]
      constructor
      · intro h; exact ⟨embeddedChainTime G.toTemporalGraph vm Δ k ω, rfl, h⟩
      · rintro ⟨t, heq, hp⟩
        show G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ k ω)
          (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) ∈ S
        rw [heq]; exact hp]
    refine MeasurableSet.iUnion (fun t => ?_)
    have hT_meas : Measurable (embeddedChainTime G.toTemporalGraph vm Δ k) := by
      intro s _
      rw [show (embeddedChainTime G.toTemporalGraph vm Δ k) ⁻¹' s =
          ⋃ u ∈ s, {w | embeddedChainTime G.toTemporalGraph vm Δ k w = u} from by ext ω; simp]
      refine MeasurableSet.biUnion (Set.to_countable s) (fun u _ => ?_)
      have heq2 : {w : Ω | embeddedChainTime G.toTemporalGraph vm Δ k w = u} =
          {w | (embeddedChainTime G.toTemporalGraph vm Δ k w : ℕ∞) = ↑u} := by
        ext w
        exact ⟨fun heq => by exact_mod_cast heq, fun heq => by exact_mod_cast heq⟩
      rw [heq2]; exact vm.ℱ.le u _ ((hT_stop k).measurableSet_eq u)
    have hchi_meas : Measurable (fun ω => G.chiPotential t (vm.S t ω)) := by
      have hchi_fn : Measurable (fun s : Finset V => G.chiPotential t s) :=
        measurable_of_countable _
      have hS_t : Measurable (vm.S t) := fun S hS => vm.ℱ.le t _ ((hS_meas_ℱ t) hS)
      exact hchi_fn.comp hS_t
    exact (hT_meas (measurableSet_singleton _)).inter (hchi_meas hS)
  -- Pointwise nonneg/upper bounds on ψ and χ at embedded times.
  have hψE_nn : ∀ k ω, 0 ≤ vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω := fun k ω => by
    show TemporalGraph.potential G.toTemporalGraph _ _ ≥ 0
    exact Real.sqrt_nonneg _
  have hψE_bnd : ∀ k ω, vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω ≤ Real.sqrt (Vu : ℝ) :=
    fun k ω => by
      show TemporalGraph.potential G.toTemporalGraph _ _ ≤ _
      apply Real.sqrt_le_sqrt
      exact_mod_cast hVol_le_univ _ _
  have hχE_nn : ∀ k ω, 0 ≤ G.chiPotential
      (embeddedChainTime G.toTemporalGraph vm Δ k ω) (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) := fun k ω => by
    unfold TemporalGraphFixedDegree.chiPotential TemporalGraph.chiPotential
    apply Real.log_nonneg
    have : (0 : ℝ) ≤ (TemporalGraph.volume G.toTemporalGraph (embeddedChainTime G.toTemporalGraph vm Δ k ω)
        (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) : ℝ) := Nat.cast_nonneg _
    linarith
  have hχE_bnd : ∀ k ω, G.chiPotential
      (embeddedChainTime G.toTemporalGraph vm Δ k ω) (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) ≤
      Real.log (1 + (Vu : ℝ)) := fun k ω => by
    unfold TemporalGraphFixedDegree.chiPotential TemporalGraph.chiPotential
    have hvol_nn : (0 : ℝ) ≤ (TemporalGraph.volume G.toTemporalGraph (embeddedChainTime G.toTemporalGraph vm Δ k ω)
        (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) : ℝ) := Nat.cast_nonneg _
    have hpos : (0 : ℝ) < 1 + (TemporalGraph.volume G.toTemporalGraph (embeddedChainTime G.toTemporalGraph vm Δ k ω)
        (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) : ℝ) := by linarith
    apply Real.log_le_log hpos
    have h := hVol_le_univ (embeddedChainTime G.toTemporalGraph vm Δ k ω)
      (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω)
    have h2 : (TemporalGraph.volume G.toTemporalGraph (embeddedChainTime G.toTemporalGraph vm Δ k ω)
        (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) : ℝ) ≤ (Vu : ℝ) := by exact_mod_cast h
    linarith
  -- Pointwise: |f ω| ≤ Cf.
  have hf_abs : ∀ ω, |f ω| ≤ Cf := by
    intro ω
    simp only [f]
    have h1 := hψE_nn (j + 1) ω
    have h2 := hψE_bnd (j + 1) ω
    have h3 := hψE_nn j ω
    have h4 := hψE_bnd j ω
    have h5 := hχE_nn (j + 1) ω
    have h6 := hχE_bnd (j + 1) ω
    have h7 := hχE_nn j ω
    have h8 := hχE_bnd j ω
    have hsqrtu : 0 ≤ Real.sqrt (Vu : ℝ) := Real.sqrt_nonneg _
    have habs_log : |Real.log (1 + (Vu : ℝ))| ≥ 0 := abs_nonneg _
    have hlog_le : Real.log (1 + (Vu : ℝ)) ≤ |Real.log (1 + (Vu : ℝ))| := le_abs_self _
    have hlog_ge : -|Real.log (1 + (Vu : ℝ))| ≤ Real.log (1 + (Vu : ℝ)) :=
      neg_abs_le _
    -- Split on the indicator.
    by_cases hcase :
        ∀ k ≤ j, (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) ≠ ∅ ∧
            (TemporalGraph.volume G.toTemporalGraph 0 (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) : ℝ) <
            8 * (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ)
    · simp only [if_pos hcase]
      have hmin_le : min (φ j / 2048) (1 / 2048 : ℝ) ≤ 1 / 2048 := min_le_right _ _
      have hmin_nn : 0 ≤ min (φ j / 2048) (1 / 2048 : ℝ) :=
        le_min (div_nonneg (hφ_nn j) (by norm_num)) (by norm_num)
      rw [abs_le]
      refine ⟨?_, ?_⟩
      · simp only [Cf]
        have hαmul1 := mul_nonneg hα_nn h1
        have hαmul3 := mul_nonneg hα_nn h3
        have hαmul2 : (Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) / d_min) *
            vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω ≤
            (Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) / d_min) * Real.sqrt (Vu : ℝ) :=
          mul_le_mul_of_nonneg_left h2 hα_nn
        have hαmul4 : (Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) / d_min) *
            vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω ≤
            (Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) / d_min) * Real.sqrt (Vu : ℝ) :=
          mul_le_mul_of_nonneg_left h4 hα_nn
        nlinarith
      · simp only [Cf]
        have hαmul1 := mul_nonneg hα_nn h1
        have hαmul3 := mul_nonneg hα_nn h3
        have hαmul2 : (Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) / d_min) *
            vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω ≤
            (Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) / d_min) * Real.sqrt (Vu : ℝ) :=
          mul_le_mul_of_nonneg_left h2 hα_nn
        have hαmul4 : (Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) / d_min) *
            vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω ≤
            (Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) / d_min) * Real.sqrt (Vu : ℝ) :=
          mul_le_mul_of_nonneg_left h4 hα_nn
        nlinarith
    · simp only [if_neg hcase, add_zero]
      rw [abs_le]
      refine ⟨?_, ?_⟩
      · simp only [Cf]
        have hαmul1 := mul_nonneg hα_nn h1
        have hαmul3 := mul_nonneg hα_nn h3
        have hαmul2 : (Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) / d_min) *
            vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω ≤
            (Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) / d_min) * Real.sqrt (Vu : ℝ) :=
          mul_le_mul_of_nonneg_left h2 hα_nn
        have hαmul4 : (Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) / d_min) *
            vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω ≤
            (Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) / d_min) * Real.sqrt (Vu : ℝ) :=
          mul_le_mul_of_nonneg_left h4 hα_nn
        nlinarith
      · simp only [Cf]
        have hαmul1 := mul_nonneg hα_nn h1
        have hαmul3 := mul_nonneg hα_nn h3
        have hαmul2 : (Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) / d_min) *
            vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω ≤
            (Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) / d_min) * Real.sqrt (Vu : ℝ) :=
          mul_le_mul_of_nonneg_left h2 hα_nn
        have hαmul4 : (Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) / d_min) *
            vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω ≤
            (Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) / d_min) * Real.sqrt (Vu : ℝ) :=
          mul_le_mul_of_nonneg_left h4 hα_nn
        nlinarith
  -- Measurability of `f`.
  have h_set_meas : MeasurableSet
      {ω : Ω | ∀ k ≤ j,
        (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) ≠ ∅ ∧
        (TemporalGraph.volume G.toTemporalGraph 0 (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) : ℝ) <
          8 * (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ)} := by
    rw [show {ω : Ω | ∀ k ≤ j,
        (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) ≠ ∅ ∧
        (TemporalGraph.volume G.toTemporalGraph 0 (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) : ℝ) <
          8 * (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ)} =
        ⋂ k ∈ Finset.Iic j, ({ω : Ω |
          (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) ≠ ∅} ∩
          {ω : Ω |
            (TemporalGraph.volume G.toTemporalGraph 0 (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) : ℝ) <
            8 * (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ)}) from by
          ext ω; simp [Finset.mem_Iic, Set.mem_inter_iff]]
    refine MeasurableSet.biInter (Set.to_countable _) (fun k _ => ?_)
    have hS_emb_meas : Measurable (fun ω => vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) := by
      intro S hS
      rw [show (fun ω => vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) ⁻¹' S =
          ⋃ t : ℕ, (embeddedChainTime G.toTemporalGraph vm Δ k) ⁻¹' {t} ∩ (vm.S t) ⁻¹' S
          from by ext ω; simp [eq_comm]]
      refine MeasurableSet.iUnion (fun t => ?_)
      have hT_meas : Measurable (embeddedChainTime G.toTemporalGraph vm Δ k) := by
        intro s _
        rw [show (embeddedChainTime G.toTemporalGraph vm Δ k) ⁻¹' s =
            ⋃ u ∈ s, {w | embeddedChainTime G.toTemporalGraph vm Δ k w = u} from by ext ω; simp]
        refine MeasurableSet.biUnion (Set.to_countable s) (fun u _ => ?_)
        have heq2 : {w : Ω | embeddedChainTime G.toTemporalGraph vm Δ k w = u} =
            {w | (embeddedChainTime G.toTemporalGraph vm Δ k w : ℕ∞) = ↑u} := by
          ext w
          exact ⟨fun heq => by exact_mod_cast heq, fun heq => by exact_mod_cast heq⟩
        rw [heq2]; exact vm.ℱ.le u _ ((hT_stop k).measurableSet_eq u)
      exact (hT_meas (measurableSet_singleton _)).inter
        (vm.ℱ.le t _ (hS_meas_ℱ t hS))
    have hvol : Measurable (fun s : Finset V => (TemporalGraph.volume G.toTemporalGraph 0 s : ℝ)) :=
      measurable_of_countable _
    have h_ne : MeasurableSet
        {ω : Ω | (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) ≠ ∅} :=
      hS_emb_meas (measurableSet_singleton _).compl
    exact h_ne.inter ((hvol.comp hS_emb_meas) measurableSet_Iio)
  have hf_meas : Measurable f := by
    refine Measurable.add ?_ (Measurable.ite h_set_meas measurable_const measurable_const)
    refine Measurable.sub ?_ (hχE_meas_full j)
    refine Measurable.sub ?_ ((hψE_meas j).const_mul _)
    exact (hψE_meas (j + 1)).const_mul _ |>.add (hχE_meas_full (j + 1))
  have hf_int : Integrable f vm.μ := by
    refine MeasureTheory.Integrable.of_bound (C := Cf) hf_meas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs]; exact hf_abs ω
  -- Assemble: ∫ f dμ = ∫ f over (⋃ p ∈ I, F p.1 p.2) ∂μ (the union is Ω up to μ-null)
  --                  = Σ_{p ∈ I} ∫_{F p.1 p.2} f dμ
  --                  ≤ 0.
  have h_union_univ : (⋃ p ∈ I, F p.1 p.2) = Set.univ := by
    ext ω; refine ⟨fun _ => trivial, fun _ => hF_cover ω⟩
  have h_integral_univ : ∫ ω, f ω ∂vm.μ = ∫ ω in (⋃ p ∈ I, F p.1 p.2), f ω ∂vm.μ := by
    rw [h_union_univ, MeasureTheory.setIntegral_univ]
  have h_partition_meas : ∀ p ∈ I, MeasurableSet (F p.1 p.2) := fun p _ => hF_meas p.1 p.2
  have h_partition_int : ∀ p ∈ I, MeasureTheory.IntegrableOn f (F p.1 p.2) vm.μ :=
    fun p _ => hf_int.integrableOn
  have h_eq_sum := MeasureTheory.integral_biUnion_finset (t := I)
    h_partition_meas hF_disjoint h_partition_int (f := f)
  calc ∫ ω, f ω ∂vm.μ
      = ∫ ω in (⋃ p ∈ I, F p.1 p.2), f ω ∂vm.μ := h_integral_univ
    _ = ∑ p ∈ I, ∫ ω in F p.1 p.2, f ω ∂vm.μ := h_eq_sum
    _ ≤ ∑ _p ∈ I, (0 : ℝ) := Finset.sum_le_sum hper_fiber
    _ = 0 := by simp


end VoterModel
