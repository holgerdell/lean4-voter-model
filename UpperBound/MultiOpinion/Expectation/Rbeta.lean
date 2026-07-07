module

public import VoterProcess.Absorption.Consensus
public import UpperBound.MultiOpinion.Metaphase
public import TemporalGraph.Degree
public import TemporalGraph.Conductance
public import TemporalGraph.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Probability.Notation
import Mathlib.Tactic.Positivity.Finset
import UpperBound.MultiOpinion.Expectation.GeomTail
import UpperBound.MultiOpinion.Expectation.OneBlock

/-! ## Main results

The §3.4 conclusion: telescoping the tight per-metaphase increment bound into
`E[R_β]` (`expected_Rbeta_le_final`, `expected_Rbeta_succ_le_final`), plus the
supporting `sevensixths` / geometric-sum / `log` / residual arithmetic,
`metaphase_telescope`, `metaphase_beta_succ_consensus`, and `phaseTime_le_sum_Delta`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Classical ENNReal

noncomputable section

namespace TemporalGraph

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
variable {κ : ℕ} [NeZero κ] {G : TemporalGraphFixedDegree V}
variable {Ω : Type*} [MeasurableSpace Ω] (vm : VoterModelAbstract G.toTemporalGraph κ Ω)
  (B : ℝ) (m d_min : ℕ) (b : ℝ) (Δ : ℕ → ℕ) (φ : ℕ → ℝ)

/-- **D3 (tight, eq `multi-opinion-2`).** The deterministic increment bound
`E[R_{α+1} − R_α] ≤ 3·xiAlpha(θ_α+1)` with `θ_α = max⌈(6/7)^α κ⌉ 1`. The increment is
`0` off the survival event `E_α = {|𝒪(t_{R_α})| > θ_α}` (`metaphase_succ_eq_of_card_le`);
on `E_α` the count exceeds `θ_α`, so `ξ_α ≤ xiAlpha(θ_α+1)` (`xiAlpha_antitone`). The
`𝒢_{R_α}`-measurability of `E_α` lets `setIntegral_condExp` expose the increment bound. -/
theorem VoterModelAbstract.expected_metaphase_increment_tight
    (hmono : Monotone (TemporalGraph.phaseTime Δ φ))
    (hd : d_min = G.minDegreeAt 0) (hd_pos : 0 < d_min) (hb : 0 ≤ b) (hΔ_pos : ∀ j, 1 ≤ Δ j)
    (hφ_nn : ∀ j, 0 ≤ φ j) (hφ_le1 : ∀ j, φ j ≤ 1)
    (hreach : TemporalGraph.reachUpToRMax B m d_min φ)
    (hwin : ∀ j, ∀ Sc ∈ G.admissibleCuts,
      φ j ≤ G.maxSetConductanceOnInterval (∑ i ∈ Finset.range j, Δ i) (Δ j) Sc)
    (hb_large : (5462 : ℝ) ≤ b) (hm_pos : 0 < m)
    (hvol : ∀ t, (TemporalGraph.volume G.toTemporalGraph t Finset.univ : ℝ) ≤ 2 * m) (α : ℕ) :
    (vm.μ : Measure Ω)[fun ω => (vm.metaphase B m d_min Δ φ (α + 1) ω : ℝ)
          - (vm.metaphase B m d_min Δ φ α ω : ℝ)]
      ≤ 3 * (TemporalGraph.xiAlpha b m d_min (max ⌈(6 / 7 : ℝ) ^ α * (κ : ℝ)⌉₊ 1 + 1) : ℝ) := by
  set hτ := vm.metaphase_isStoppingTime B m d_min Δ φ hmono α with hτdef
  have hm := hτ.measurableSpace_le
  set θ := max ⌈(6 / 7 : ℝ) ^ α * (κ : ℝ)⌉₊ 1 with hθ
  set E : Set Ω := {ω | θ < (vm.opinionSet (TemporalGraph.phaseTime Δ φ
      (vm.metaphase B m d_min Δ φ α ω)) ω).card} with hEdef
  have hE : MeasurableSet[hτ.measurableSpace] E :=
    vm.metaphase_survival_measurableSet_stopped B m d_min Δ φ hmono α θ
  have hEμ : MeasurableSet E := hm E hE
  have hfinal := vm.metaphase_increment_le_final B m d_min b Δ φ hmono hd hd_pos hb hΔ_pos
    hφ_nn hφ_le1 hreach hwin hb_large hm_pos hvol α
  -- increment and its integrability
  set incr : Ω → ℝ := fun ω => (vm.metaphase B m d_min Δ φ (α + 1) ω : ℝ)
      - (vm.metaphase B m d_min Δ φ α ω : ℝ) with hincr
  have hincr_int : Integrable incr vm.μ :=
    (vm.integrable_natCast_le (TemporalGraph.rMax B m d_min)
      (vm.metaphase_measurable B m d_min Δ φ hmono (α + 1))
      (fun ω => vm.metaphase_le_rMax B m d_min Δ φ (α + 1) ω)).sub
    (vm.integrable_natCast_le (TemporalGraph.rMax B m d_min)
      (vm.metaphase_measurable B m d_min Δ φ hmono α)
      (fun ω => vm.metaphase_le_rMax B m d_min Δ φ α ω))
  -- increment is `0` off `E`
  have hincr_off : incr = E.indicator incr := by
    funext ω
    by_cases hωE : ω ∈ E
    · rw [Set.indicator_of_mem hωE]
    · rw [Set.indicator_of_notMem hωE]
      have hcard : (vm.opinionSet (TemporalGraph.phaseTime Δ φ
          (vm.metaphase B m d_min Δ φ α ω)) ω).card ≤ θ := not_lt.mp hωE
      simp only [hincr, vm.metaphase_succ_eq_of_card_le B m d_min Δ φ α ω hcard, sub_self]
  calc ∫ ω, incr ω ∂vm.μ
      = ∫ ω in E, incr ω ∂vm.μ := by
        conv_lhs => rw [hincr_off]
        rw [integral_indicator hEμ]
    _ = ∫ ω in E, ((vm.μ : Measure Ω)[incr | hτ.measurableSpace]) ω ∂vm.μ :=
        (setIntegral_condExp hm hincr_int hE).symm
    _ ≤ ∫ _ω in E, 3 * (TemporalGraph.xiAlpha b m d_min (θ + 1) : ℝ) ∂vm.μ := by
        refine setIntegral_mono_on_ae integrable_condExp.integrableOn
          (integrable_const _).integrableOn hEμ ?_
        filter_upwards [hfinal] with ω hf hωE
        have hc : θ < (vm.opinionSet (TemporalGraph.phaseTime Δ φ
            (vm.metaphase B m d_min Δ φ α ω)) ω).card := hωE
        have hξle : vm.metaphaseXi B m d_min b Δ φ α ω ≤ TemporalGraph.xiAlpha b m d_min (θ + 1) := by
          unfold VoterModelAbstract.metaphaseXi
          exact xiAlpha_antitone b m d_min hb (by exact_mod_cast hd_pos) (by positivity)
            (θ + 1) _ (by omega) (by omega)
        have hξleR : (vm.metaphaseXi B m d_min b Δ φ α ω : ℝ)
            ≤ (TemporalGraph.xiAlpha b m d_min (θ + 1) : ℝ) := by exact_mod_cast hξle
        calc ((vm.μ : Measure Ω)[incr | hτ.measurableSpace]) ω
            ≤ 3 * (vm.metaphaseXi B m d_min b Δ φ α ω : ℝ) := hf
          _ ≤ 3 * (TemporalGraph.xiAlpha b m d_min (θ + 1) : ℝ) := by linarith
    _ = 3 * (TemporalGraph.xiAlpha b m d_min (θ + 1) : ℝ) * ((vm.μ : Measure Ω) E).toReal := by
        rw [setIntegral_const, smul_eq_mul, mul_comm]; rfl
    _ ≤ 3 * (TemporalGraph.xiAlpha b m d_min (θ + 1) : ℝ) := by
        have h1 : ((vm.μ : Measure Ω) E).toReal ≤ 1 := by
          rw [← ENNReal.toReal_one]
          exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
        have h2 : (0 : ℝ) ≤ 3 * (TemporalGraph.xiAlpha b m d_min (θ + 1) : ℝ) := by positivity
        nlinarith [h1, h2, ENNReal.toReal_nonneg (a := (vm.μ : Measure Ω) E)]

/-- **Vacuous metaphase increment.** When the metaphase threshold `θ_α = max⌈(6/7)^α κ⌉ 1`
is at least the number of vertices `n = |V|`, the survival event `E_α` is empty (the opinion
count is always `≤ n ≤ θ_α`), so the metaphase counter does not move:
`E[R_{α+1} − R_α] = 0`. This makes the metaphase increment sum `κ`-independent (only the
`α` with `θ_α < n` — at most `~log n` of them — contribute). -/
theorem VoterModelAbstract.expected_metaphase_increment_zero (α : ℕ)
    (hθn : Fintype.card V ≤ max ⌈(6 / 7 : ℝ) ^ α * (κ : ℝ)⌉₊ 1) :
    (vm.μ : Measure Ω)[fun ω => (vm.metaphase B m d_min Δ φ (α + 1) ω : ℝ)
          - (vm.metaphase B m d_min Δ φ α ω : ℝ)] = 0 := by
  have hzero : (fun ω => (vm.metaphase B m d_min Δ φ (α + 1) ω : ℝ)
        - (vm.metaphase B m d_min Δ φ α ω : ℝ)) = fun _ => (0 : ℝ) := by
    funext ω
    have hcard : (vm.opinionSet (TemporalGraph.phaseTime Δ φ
        (vm.metaphase B m d_min Δ φ α ω)) ω).card ≤ max ⌈(6 / 7 : ℝ) ^ α * (κ : ℝ)⌉₊ 1 :=
      le_trans (vm.numOpinions_le_card _ ω) hθn
    rw [vm.metaphase_succ_eq_of_card_le B m d_min Δ φ α ω hcard]; ring
  rw [hzero]; simp

/-- **Telescoping** `R_β = ∑_{α<β} (R_{α+1} − R_α)` (with `R_0 = 0`). -/
theorem VoterModelAbstract.metaphase_telescope (β : ℕ) (ω : Ω) :
    (vm.metaphase B m d_min Δ φ β ω : ℝ)
      = ∑ α ∈ Finset.range β, ((vm.metaphase B m d_min Δ φ (α + 1) ω : ℝ)
          - (vm.metaphase B m d_min Δ φ α ω : ℝ)) := by
  rw [Finset.sum_range_sub (fun α => (vm.metaphase B m d_min Δ φ α ω : ℝ))]
  simp [VoterModelAbstract.metaphase]

/-- **D4 (filtered telescoped, `κ`-free).** `E[R_β] ≤ 3·∑_{α<β, θ_α<n} xiAlpha(θ_α+1)`, summing
only over metaphases whose threshold `θ_α = max⌈(6/7)^α κ⌉ 1` is below `n = |V|`. The omitted
`α` (with `θ_α ≥ n`) contribute `0` by `expected_metaphase_increment_zero`, which removes the
spurious `κ`-dependence: only `~log n` metaphases survive the filter. -/
theorem VoterModelAbstract.expected_Rbeta_le_tight_filtered
    (hmono : Monotone (TemporalGraph.phaseTime Δ φ))
    (hd : d_min = G.minDegreeAt 0) (hd_pos : 0 < d_min) (hb : 0 ≤ b) (hΔ_pos : ∀ j, 1 ≤ Δ j)
    (hφ_nn : ∀ j, 0 ≤ φ j) (hφ_le1 : ∀ j, φ j ≤ 1)
    (hreach : TemporalGraph.reachUpToRMax B m d_min φ)
    (hwin : ∀ j, ∀ Sc ∈ G.admissibleCuts,
      φ j ≤ G.maxSetConductanceOnInterval (∑ i ∈ Finset.range j, Δ i) (Δ j) Sc)
    (hb_large : (5462 : ℝ) ≤ b) (hm_pos : 0 < m)
    (hvol : ∀ t, (TemporalGraph.volume G.toTemporalGraph t Finset.univ : ℝ) ≤ 2 * m) (β : ℕ) :
    (vm.μ : Measure Ω)[fun ω => (vm.metaphase B m d_min Δ φ β ω : ℝ)]
      ≤ 3 * ∑ α ∈ (Finset.range β).filter
            (fun α => max ⌈(6 / 7 : ℝ) ^ α * (κ : ℝ)⌉₊ 1 < Fintype.card V),
          (TemporalGraph.xiAlpha b m d_min (max ⌈(6 / 7 : ℝ) ^ α * (κ : ℝ)⌉₊ 1 + 1) : ℝ) := by
  have hRint : ∀ γ, Integrable (fun ω => (vm.metaphase B m d_min Δ φ γ ω : ℝ)) vm.μ :=
    fun γ => vm.integrable_natCast_le (TemporalGraph.rMax B m d_min)
      (vm.metaphase_measurable B m d_min Δ φ hmono γ)
      (fun ω => vm.metaphase_le_rMax B m d_min Δ φ γ ω)
  have htel : ∫ ω, (vm.metaphase B m d_min Δ φ β ω : ℝ) ∂vm.μ
      = ∑ α ∈ Finset.range β, ∫ ω, ((vm.metaphase B m d_min Δ φ (α + 1) ω : ℝ)
          - (vm.metaphase B m d_min Δ φ α ω : ℝ)) ∂vm.μ := by
    rw [show (fun ω => (vm.metaphase B m d_min Δ φ β ω : ℝ))
        = (fun ω => ∑ α ∈ Finset.range β, ((vm.metaphase B m d_min Δ φ (α + 1) ω : ℝ)
            - (vm.metaphase B m d_min Δ φ α ω : ℝ)))
        from funext (fun ω => vm.metaphase_telescope B m d_min Δ φ β ω)]
    exact integral_finsetSum _ (fun α _ => (hRint (α + 1)).sub (hRint α))
  rw [htel, ← Finset.sum_filter_add_sum_filter_not (Finset.range β)
    (fun α => max ⌈(6 / 7 : ℝ) ^ α * (κ : ℝ)⌉₊ 1 < Fintype.card V)]
  have hnot : ∑ α ∈ (Finset.range β).filter
        (fun α => ¬ max ⌈(6 / 7 : ℝ) ^ α * (κ : ℝ)⌉₊ 1 < Fintype.card V),
        ∫ ω, ((vm.metaphase B m d_min Δ φ (α + 1) ω : ℝ)
          - (vm.metaphase B m d_min Δ φ α ω : ℝ)) ∂vm.μ = 0 := by
    refine Finset.sum_eq_zero (fun α hα => ?_)
    rw [Finset.mem_filter] at hα
    exact vm.expected_metaphase_increment_zero B m d_min Δ φ α (not_lt.mp hα.2)
  rw [hnot, add_zero, Finset.mul_sum]
  refine Finset.sum_le_sum (fun α _ => ?_)
  exact vm.expected_metaphase_increment_tight B m d_min b Δ φ hmono hd hd_pos hb hΔ_pos hφ_nn
    hφ_le1 hreach hwin hb_large hm_pos hvol α

omit [NeZero κ] in
/-- **Per-`α` real bound (eq `multi-opinion-3` term).** `xiAlpha(θ_α+1) ≤ 2 + b·(τm·(1/ρ)^α/(P·d_min·κ)
+ log(1+τm/P))`, using `θ_α + 1 ≥ ρ^α κ` and `Nat.ceil_lt_add_one`. The `(1/ρ)^α` factor is what
sums geometrically over `α < β`. -/
theorem xiAlpha_tight_le (bb mm dd : ℝ) (hb : 0 ≤ bb) (hd : 0 < dd) (hmm : 0 ≤ mm)
    (hκ : 1 ≤ (κ : ℝ)) (α : ℕ) :
    (TemporalGraph.xiAlpha bb mm dd (max ⌈(6 / 7 : ℝ) ^ α * (κ : ℝ)⌉₊ 1 + 1) : ℝ)
      ≤ 2 + bb * (14 * mm * (7 / 6 : ℝ) ^ α / (3 * (dd * (κ : ℝ))) + Real.log (1 + 14 * mm / 3)) := by
  set c : ℕ := max ⌈(6 / 7 : ℝ) ^ α * (κ : ℝ)⌉₊ 1 + 1 with hc
  have hpow_pos : (0 : ℝ) < (6 / 7 : ℝ) ^ α := by positivity
  have hcκ_pos : (0 : ℝ) < (6 / 7 : ℝ) ^ α * (κ : ℝ) := by positivity
  have hcv : (c : ℝ) = max (⌈(6 / 7 : ℝ) ^ α * (κ : ℝ)⌉₊ : ℝ) 1 + 1 := by
    rw [hc]; push_cast; ring
  have hcR : (6 / 7 : ℝ) ^ α * (κ : ℝ) ≤ (c : ℝ) := by
    have h1 : (6 / 7 : ℝ) ^ α * (κ : ℝ) ≤ (⌈(6 / 7 : ℝ) ^ α * (κ : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈(6 / 7 : ℝ) ^ α * (κ : ℝ)⌉₊ : ℝ)
        ≤ max (⌈(6 / 7 : ℝ) ^ α * (κ : ℝ)⌉₊ : ℝ) 1 := le_max_left _ _
    rw [hcv]; linarith
  have hc_pos : (0 : ℝ) < (c : ℝ) := lt_of_lt_of_le hcκ_pos hcR
  have hc_ge1 : (1 : ℝ) ≤ (c : ℝ) := by
    rw [hcv]; have := le_max_right (⌈(6 / 7 : ℝ) ^ α * (κ : ℝ)⌉₊ : ℝ) 1; linarith
  have hinv : (7 / 6 : ℝ) ^ α = ((6 / 7 : ℝ) ^ α)⁻¹ := by
    rw [show (7 / 6 : ℝ) = (6 / 7 : ℝ)⁻¹ from by norm_num, inv_pow]
  -- the volume term
  have hvolterm : 14 * mm / (3 * (dd * (c : ℝ)))
      ≤ 14 * mm * (7 / 6 : ℝ) ^ α / (3 * (dd * (κ : ℝ))) := by
    have hstep : 14 * mm / (3 * (dd * (c : ℝ)))
        ≤ 14 * mm / (3 * (dd * ((6 / 7 : ℝ) ^ α * (κ : ℝ)))) := by
      gcongr
    have heq : 14 * mm / (3 * (dd * ((6 / 7 : ℝ) ^ α * (κ : ℝ))))
        = 14 * mm * (7 / 6 : ℝ) ^ α / (3 * (dd * (κ : ℝ))) := by
      rw [hinv]; field_simp
    linarith [hstep, heq.le, heq.ge]
  -- the log term
  have hlogterm : Real.log (1 + 14 * mm / (3 * (c : ℝ))) ≤ Real.log (1 + 14 * mm / 3) := by
    have hpos : (0 : ℝ) < 1 + 14 * mm / (3 * (c : ℝ)) := by
      have : (0 : ℝ) ≤ 14 * mm / (3 * (c : ℝ)) :=
        div_nonneg (mul_nonneg (by norm_num) hmm) (by positivity)
      linarith
    have hle : 14 * mm / (3 * (c : ℝ)) ≤ 14 * mm / 3 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [hmm, hc_ge1]
    exact Real.log_le_log hpos (by linarith)
  unfold TemporalGraph.xiAlpha
  push_cast
  have hargnn : (0 : ℝ)
      ≤ bb * (14 * mm / (3 * (dd * (c : ℝ))) + Real.log (1 + 14 * mm / (3 * (c : ℝ)))) := by
    refine mul_nonneg hb (add_nonneg ?_ ?_)
    · exact div_nonneg (mul_nonneg (by norm_num) hmm) (by positivity)
    · refine Real.log_nonneg ?_
      have : (0 : ℝ) ≤ 14 * mm / (3 * (c : ℝ)) :=
        div_nonneg (mul_nonneg (by norm_num) hmm) (by positivity)
      linarith
  have hceil : (⌈bb * (14 * mm / (3 * (dd * (c : ℝ)))
        + Real.log (1 + 14 * mm / (3 * (c : ℝ))))⌉₊ : ℝ)
      ≤ bb * (14 * mm / (3 * (dd * (c : ℝ))) + Real.log (1 + 14 * mm / (3 * (c : ℝ)))) + 1 :=
    (Nat.ceil_lt_add_one hargnn).le
  have harg : bb * (14 * mm / (3 * (dd * (c : ℝ))) + Real.log (1 + 14 * mm / (3 * (c : ℝ))))
      ≤ bb * (14 * mm * (7 / 6 : ℝ) ^ α / (3 * (dd * (κ : ℝ))) + Real.log (1 + 14 * mm / 3)) :=
    mul_le_mul_of_nonneg_left (by linarith [hvolterm, hlogterm]) hb
  linarith

omit [NeZero κ] in
/-- `(1/ρ)^{β} ≤ (1/ρ)·κ` for `β = beta κ = ⌈log_{1/ρ} κ⌉`, via `rpow_logb`. -/
theorem sevensixths_pow_beta_le (hκ : (1 : ℝ) ≤ (κ : ℝ)) :
    (7 / 6 : ℝ) ^ (TemporalGraph.beta κ) ≤ (7 / 6 : ℝ) * (κ : ℝ) := by
  have h76 : (1 : ℝ) < 7 / 6 := by norm_num
  have hκpos : (0 : ℝ) < (κ : ℝ) := by linarith
  unfold TemporalGraph.beta
  rw [← Real.rpow_natCast (7 / 6 : ℝ) ⌈Real.logb (7 / 6) (κ : ℝ)⌉₊]
  calc (7 / 6 : ℝ) ^ ((⌈Real.logb (7 / 6) (κ : ℝ)⌉₊ : ℝ))
      ≤ (7 / 6 : ℝ) ^ (Real.logb (7 / 6) (κ : ℝ) + 1) := by
        refine Real.rpow_le_rpow_of_exponent_le (le_of_lt h76) ?_
        have := Nat.ceil_lt_add_one (Real.logb_nonneg h76 hκ)
        linarith
    _ = (7 / 6 : ℝ) ^ (Real.logb (7 / 6) (κ : ℝ)) * (7 / 6 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_add (by norm_num) _ _
    _ = (κ : ℝ) * (7 / 6 : ℝ) := by
        rw [Real.rpow_logb (by norm_num) (by norm_num) hκpos, Real.rpow_one]
    _ = (7 / 6 : ℝ) * (κ : ℝ) := by ring

omit [NeZero κ] in
/-- `κ ≤ (1/ρ)^{beta κ}` (`beta κ ≥ log_{1/ρ}κ`), so `θ_{beta κ} = max⌈ρ^{beta κ}κ⌉ 1 = 1`. -/
theorem sevensixths_pow_beta_ge (hκ : (1 : ℝ) ≤ (κ : ℝ)) :
    (κ : ℝ) ≤ (7 / 6 : ℝ) ^ (TemporalGraph.beta κ) := by
  have h76 : (1 : ℝ) < 7 / 6 := by norm_num
  have hκpos : (0 : ℝ) < (κ : ℝ) := by linarith
  unfold TemporalGraph.beta
  rw [← Real.rpow_natCast (7 / 6 : ℝ) ⌈Real.logb (7 / 6) (κ : ℝ)⌉₊]
  calc (κ : ℝ) = (7 / 6 : ℝ) ^ (Real.logb (7 / 6) (κ : ℝ)) :=
        (Real.rpow_logb (by norm_num) (by norm_num) hκpos).symm
    _ ≤ (7 / 6 : ℝ) ^ ((⌈Real.logb (7 / 6) (κ : ℝ)⌉₊ : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (le_of_lt h76) (Nat.le_ceil _)

omit [NeZero κ] in
/-- The metaphase threshold at level `beta κ` is `1`: `max ⌈ρ^{beta κ} κ⌉ 1 = 1`. -/
theorem theta_beta_eq_one (hκ : (1 : ℝ) ≤ (κ : ℝ)) :
    max ⌈(6 / 7 : ℝ) ^ (TemporalGraph.beta κ) * (κ : ℝ)⌉₊ 1 = 1 := by
  have hpp : (6 / 7 : ℝ) ^ (TemporalGraph.beta κ) * (7 / 6 : ℝ) ^ (TemporalGraph.beta κ) = 1 := by
    rw [← mul_pow]; norm_num
  have h1 : (6 / 7 : ℝ) ^ (TemporalGraph.beta κ) * (κ : ℝ) ≤ 1 := by
    nlinarith [sevensixths_pow_beta_ge (κ := κ) hκ, hpp,
      pow_pos (show (0 : ℝ) < 6 / 7 by norm_num) (TemporalGraph.beta κ)]
  have h2 : ⌈(6 / 7 : ℝ) ^ (TemporalGraph.beta κ) * (κ : ℝ)⌉₊ ≤ 1 :=
    Nat.ceil_le.mpr (by push_cast; linarith)
  exact max_eq_right h2

omit [NeZero κ] in
/-- `∑_{α<beta κ} (1/ρ)^α ≤ (1/(1−ρ))·κ` (geometric sum + `sevensixths_pow_beta_le`). -/
theorem geom_sum_seven_sixths_le (hκ : (1 : ℝ) ≤ (κ : ℝ)) :
    ∑ α ∈ Finset.range (TemporalGraph.beta κ), (7 / 6 : ℝ) ^ α ≤ 7 * (κ : ℝ) := by
  rw [geom_sum_eq (by norm_num : (7 / 6 : ℝ) ≠ 1)]
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 7 / 6 - 1)]
  nlinarith [sevensixths_pow_beta_le (κ := κ) hκ]

omit [NeZero κ] in
/-- `log(1/ρ) = log(7/6) ≥ 2/13` (from `exp(2/13) ≤ 7/6`, via the degree-3 Taylor
bound on `exp`). This reciprocal is the count coefficient `1/(2/13) = 13/2`. -/
theorem log_seven_sixths_ge : (2 / 13 : ℝ) ≤ Real.log (7 / 6) := by
  rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 7 / 6)]
  have hb := Real.exp_bound (x := (2 / 13 : ℝ)) (by norm_num) (n := 3) (by norm_num)
  rw [abs_le] at hb
  obtain ⟨_, h2⟩ := hb
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h2
  norm_num at h2 ⊢
  nlinarith [h2]

omit [Nonempty V] [Fintype V] [DecidableEq V] [NeZero κ] in
/-- **Contributing-metaphase count (`κ`-free).** At most `(13/2) log n + 1` metaphases `α < beta κ`
have threshold `θ_α = max⌈(6/7)^α κ⌉ 1 < n`. The smallest such `α₀` satisfies
`(6/7)^{α₀} κ ≤ n − 1`, so `α₀ ≥ log_{7/6}(κ/(n−1))`, while `beta κ ≤ log_{7/6}κ + 1`; their
difference is `≤ 1 + log_{7/6}(n−1) ≤ (13/2) log n + 1` (using `1/log(7/6) ≤ 13/2`). Unlike a bound
on `beta κ` itself, this needs no `κ ≤ n` assumption. -/
theorem contributing_count_le {n : ℕ} (hκ1 : (1 : ℝ) ≤ (κ : ℝ)) (hn1 : 1 ≤ n) :
    (((Finset.range (TemporalGraph.beta κ)).filter
        (fun α => max ⌈(6 / 7 : ℝ) ^ α * (κ : ℝ)⌉₊ 1 < n)).card : ℝ)
      ≤ 13 / 2 * Real.log (n : ℝ) + 1 := by
  set S := (Finset.range (TemporalGraph.beta κ)).filter
      (fun α => max ⌈(6 / 7 : ℝ) ^ α * (κ : ℝ)⌉₊ 1 < n) with hSdef
  set L := Real.log (n : ℝ) with hLdef
  have hL_nn : 0 ≤ L := Real.log_nonneg (by exact_mod_cast hn1)
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · rw [hSe, Finset.card_empty]; push_cast; linarith
  · set ℓ := Real.log (7 / 6 : ℝ) with hℓdef
    have hℓ16 : (2 / 13 : ℝ) ≤ ℓ := log_seven_sixths_ge
    have hℓpos : 0 < ℓ := by linarith
    set a₀ := S.min' hSne with ha₀def
    have ha₀S : a₀ ∈ S := S.min'_mem hSne
    rw [hSdef, Finset.mem_filter, Finset.mem_range] at ha₀S
    obtain ⟨ha₀lt, ha₀θ⟩ := ha₀S
    have hn2 : 2 ≤ n := by
      have : 1 ≤ max ⌈(6 / 7 : ℝ) ^ a₀ * (κ : ℝ)⌉₊ 1 := le_max_right _ _
      omega
    have hn1R : (1 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
      have : 1 ≤ n - 1 := by omega
      exact_mod_cast this
    have hn1cast : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
      have : 1 ≤ n := by omega
      rw [Nat.cast_sub this]; simp
    -- `(6/7)^{a₀} κ ≤ n − 1`
    have hceil_le : ⌈(6 / 7 : ℝ) ^ a₀ * (κ : ℝ)⌉₊ ≤ n - 1 := by
      have : ⌈(6 / 7 : ℝ) ^ a₀ * (κ : ℝ)⌉₊ < n := lt_of_le_of_lt (le_max_left _ _) ha₀θ
      omega
    have h5a0 : (6 / 7 : ℝ) ^ a₀ * (κ : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := Nat.ceil_le.mp hceil_le
    -- `a₀ ℓ ≥ log κ − log(n−1)`
    have hlog5a0 : Real.log ((6 / 7 : ℝ) ^ a₀ * (κ : ℝ)) ≤ Real.log ((n - 1 : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) h5a0
    have hlog56 : Real.log (6 / 7 : ℝ) = -ℓ := by
      rw [hℓdef, show (6 / 7 : ℝ) = (7 / 6 : ℝ)⁻¹ by norm_num, Real.log_inv]
    have ha0ℓ : Real.log (κ : ℝ) - Real.log ((n - 1 : ℕ) : ℝ) ≤ (a₀ : ℝ) * ℓ := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, hlog56] at hlog5a0
      linarith
    -- `β ℓ ≤ log κ + ℓ`
    have hβℓ : (TemporalGraph.beta κ : ℝ) * ℓ ≤ Real.log (κ : ℝ) + ℓ := by
      have hβceil : (TemporalGraph.beta κ : ℝ) ≤ Real.logb (7 / 6) (κ : ℝ) + 1 := by
        unfold TemporalGraph.beta
        exact (Nat.ceil_lt_add_one (Real.logb_nonneg (by norm_num) hκ1)).le
      rw [Real.logb] at hβceil
      have h2 : (TemporalGraph.beta κ : ℝ) * ℓ ≤ (Real.log (κ : ℝ) / ℓ + 1) * ℓ :=
        mul_le_mul_of_nonneg_right hβceil hℓpos.le
      rwa [add_mul, div_mul_cancel₀ _ (ne_of_gt hℓpos), one_mul] at h2
    -- `count ≤ β − a₀`
    have ha0leβ : a₀ ≤ TemporalGraph.beta κ := le_of_lt ha₀lt
    have hcount_le : (S.card : ℝ) ≤ (TemporalGraph.beta κ : ℝ) - (a₀ : ℝ) := by
      have hsub : S ⊆ Finset.Ico a₀ (TemporalGraph.beta κ) := by
        intro x hx
        rw [Finset.mem_Ico]
        refine ⟨S.min'_le x hx, ?_⟩
        rw [hSdef, Finset.mem_filter, Finset.mem_range] at hx
        exact hx.1
      have hcard : S.card ≤ TemporalGraph.beta κ - a₀ :=
        le_trans (Finset.card_le_card hsub) (le_of_eq (Nat.card_Ico _ _))
      calc (S.card : ℝ) ≤ ((TemporalGraph.beta κ - a₀ : ℕ) : ℝ) := by exact_mod_cast hcard
        _ = (TemporalGraph.beta κ : ℝ) - (a₀ : ℝ) := by rw [Nat.cast_sub ha0leβ]
    -- assemble
    have hlogn1_le : Real.log ((n - 1 : ℕ) : ℝ) ≤ L :=
      Real.log_le_log (by linarith) hn1cast
    have hcℓ : (S.card : ℝ) * ℓ ≤ ℓ + L := by
      have hprod := mul_le_mul_of_nonneg_right hcount_le hℓpos.le
      nlinarith [hprod, hβℓ, ha0ℓ, hlogn1_le]
    have hkey : (S.card : ℝ) * ℓ ≤ (13 / 2 * L + 1) * ℓ := by
      nlinarith [hcℓ, mul_nonneg hL_nn (show (0 : ℝ) ≤ 13 / 2 * ℓ - 1 by linarith [hℓ16])]
    exact le_of_mul_le_mul_right hkey hℓpos

/-- **D4 (filtered combination, `κ`-free).** `E[R_{beta κ}] ≤ 98·b·m/d_min
+ (6 + 3b·log(1+14m/3))·count`, where `count = |{α < beta κ : θ_α < n}|` is the number of
contributing metaphases. Same shape as `expected_Rbeta_le_combined`, but the constant term
multiplies `count` (bounded by `(13/2) log n + 1`, `κ`-free) instead of `beta κ` (which needed
`κ ≤ n`). The geometric main term `98·b·m/d_min` is unchanged (`κ` still cancels, and
`∑_{filter}(7/6)^α ≤ ∑_{α<beta κ}(7/6)^α ≤ 7κ`). -/
theorem VoterModelAbstract.expected_Rbeta_le_combined_filtered
    (hmono : Monotone (TemporalGraph.phaseTime Δ φ))
    (hd : d_min = G.minDegreeAt 0) (hd_pos : 0 < d_min) (hb : 0 ≤ b) (hΔ_pos : ∀ j, 1 ≤ Δ j)
    (hφ_nn : ∀ j, 0 ≤ φ j) (hφ_le1 : ∀ j, φ j ≤ 1)
    (hreach : TemporalGraph.reachUpToRMax B m d_min φ)
    (hwin : ∀ j, ∀ Sc ∈ G.admissibleCuts,
      φ j ≤ G.maxSetConductanceOnInterval (∑ i ∈ Finset.range j, Δ i) (Δ j) Sc)
    (hb_large : (5462 : ℝ) ≤ b) (hm_pos : 0 < m)
    (hvol : ∀ t, (TemporalGraph.volume G.toTemporalGraph t Finset.univ : ℝ) ≤ 2 * m) :
    (vm.μ : Measure Ω)[fun ω => (vm.metaphase B m d_min Δ φ (TemporalGraph.beta κ) ω : ℝ)]
      ≤ 98 * b * (m : ℝ) / (d_min : ℝ)
          + (6 + 3 * b * Real.log (1 + 14 * (m : ℝ) / 3))
            * (((Finset.range (TemporalGraph.beta κ)).filter
                (fun α => max ⌈(6 / 7 : ℝ) ^ α * (κ : ℝ)⌉₊ 1 < Fintype.card V)).card : ℝ) := by
  have hκ1 : (1 : ℝ) ≤ (κ : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne κ)
  refine le_trans (vm.expected_Rbeta_le_tight_filtered B m d_min b Δ φ hmono hd hd_pos hb hΔ_pos
    hφ_nn hφ_le1 hreach hwin hb_large hm_pos hvol (TemporalGraph.beta κ)) ?_
  set S := (Finset.range (TemporalGraph.beta κ)).filter
      (fun α => max ⌈(6 / 7 : ℝ) ^ α * (κ : ℝ)⌉₊ 1 < Fintype.card V) with hSdef
  have hstep : ∑ α ∈ S,
        (TemporalGraph.xiAlpha b m d_min (max ⌈(6 / 7 : ℝ) ^ α * (κ : ℝ)⌉₊ 1 + 1) : ℝ)
      ≤ ∑ α ∈ S, (2 + b * (14 * (m : ℝ) * (7 / 6 : ℝ) ^ α / (3 * ((d_min : ℝ) * (κ : ℝ)))
          + Real.log (1 + 14 * (m : ℝ) / 3))) :=
    Finset.sum_le_sum (fun α _ => xiAlpha_tight_le b m d_min hb
      (by exact_mod_cast hd_pos) (by positivity) hκ1 α)
  have heval : ∑ α ∈ S, (2 + b * (14 * (m : ℝ) * (7 / 6 : ℝ) ^ α / (3 * ((d_min : ℝ) * (κ : ℝ)))
          + Real.log (1 + 14 * (m : ℝ) / 3)))
      = (14 * b * (m : ℝ) / (3 * ((d_min : ℝ) * (κ : ℝ)))) * (∑ α ∈ S, (7 / 6 : ℝ) ^ α)
          + (S.card : ℝ) * (2 + b * Real.log (1 + 14 * (m : ℝ) / 3)) := by
    rw [show (fun α => 2 + b * (14 * (m : ℝ) * (7 / 6 : ℝ) ^ α / (3 * ((d_min : ℝ) * (κ : ℝ)))
            + Real.log (1 + 14 * (m : ℝ) / 3)))
        = fun α => (14 * b * (m : ℝ) / (3 * ((d_min : ℝ) * (κ : ℝ)))) * (7 / 6 : ℝ) ^ α
            + (2 + b * Real.log (1 + 14 * (m : ℝ) / 3))
        from funext (fun α => by ring)]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  have hgeomS : ∑ α ∈ S, (7 / 6 : ℝ) ^ α ≤ 7 * (κ : ℝ) := by
    calc ∑ α ∈ S, (7 / 6 : ℝ) ^ α
        ≤ ∑ α ∈ Finset.range (TemporalGraph.beta κ), (7 / 6 : ℝ) ^ α := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
          intro i _ _; positivity
      _ ≤ 7 * (κ : ℝ) := geom_sum_seven_sixths_le (κ := κ) hκ1
  have hgeom_le : 3 * ((14 * b * (m : ℝ) / (3 * ((d_min : ℝ) * (κ : ℝ))))
        * (∑ α ∈ S, (7 / 6 : ℝ) ^ α))
      ≤ 98 * b * (m : ℝ) / (d_min : ℝ) := by
    have hco : (0 : ℝ) ≤ 14 * b * (m : ℝ) / (3 * ((d_min : ℝ) * (κ : ℝ))) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hgeomS hco
    have hcancel : 3 * ((14 * b * (m : ℝ) / (3 * ((d_min : ℝ) * (κ : ℝ)))) * (7 * (κ : ℝ)))
        = 98 * b * (m : ℝ) / (d_min : ℝ) := by field_simp; ring
    calc 3 * ((14 * b * (m : ℝ) / (3 * ((d_min : ℝ) * (κ : ℝ)))) * (∑ α ∈ S, (7 / 6 : ℝ) ^ α))
        ≤ 3 * ((14 * b * (m : ℝ) / (3 * ((d_min : ℝ) * (κ : ℝ)))) * (7 * (κ : ℝ))) := by
          linarith [hmul]
      _ = 98 * b * (m : ℝ) / (d_min : ℝ) := hcancel
  calc 3 * ∑ α ∈ S,
          (TemporalGraph.xiAlpha b m d_min (max ⌈(6 / 7 : ℝ) ^ α * (κ : ℝ)⌉₊ 1 + 1) : ℝ)
      ≤ 3 * ∑ α ∈ S, (2 + b * (14 * (m : ℝ) * (7 / 6 : ℝ) ^ α / (3 * ((d_min : ℝ) * (κ : ℝ)))
          + Real.log (1 + 14 * (m : ℝ) / 3))) := mul_le_mul_of_nonneg_left hstep (by norm_num)
    _ = 3 * ((14 * b * (m : ℝ) / (3 * ((d_min : ℝ) * (κ : ℝ)))) * (∑ α ∈ S, (7 / 6 : ℝ) ^ α))
          + (6 + 3 * b * Real.log (1 + 14 * (m : ℝ) / 3)) * (S.card : ℝ) := by rw [heval]; ring
    _ ≤ 98 * b * (m : ℝ) / (d_min : ℝ)
          + (6 + 3 * b * Real.log (1 + 14 * (m : ℝ) / 3)) * (S.card : ℝ) := by linarith [hgeom_le]

/-- **Handshake** `n·d_min ≤ 2m` (`n = Fintype.card V`), derived from the volume
hypothesis `hvol`: `n·d_min ≤ ∑_v deg(v) = volume G 0 univ ≤ 2m`. -/
theorem card_mul_minDegree_le (hd : d_min = G.minDegreeAt 0)
    (hvol : ((G.snapshot 0).volume Finset.univ : ℝ) ≤ 2 * m) :
    (Fintype.card V : ℝ) * (d_min : ℝ) ≤ 2 * (m : ℝ) := by
  have hsum : Fintype.card V * d_min ≤ TemporalGraph.volume G.toTemporalGraph 0 Finset.univ := by
    have hveq : TemporalGraph.volume G.toTemporalGraph 0 Finset.univ = ∑ v : V, (G.snapshot 0).degree v := rfl
    rw [hveq, hd]
    calc Fintype.card V * G.minDegreeAt 0
        = ∑ _v : V, G.minDegreeAt 0 := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
      _ ≤ ∑ v : V, (G.snapshot 0).degree v := Finset.sum_le_sum (fun v _ => G.minDegree_le_deg v)
  calc (Fintype.card V : ℝ) * (d_min : ℝ) = ((Fintype.card V * d_min : ℕ) : ℝ) := by push_cast; ring
    _ ≤ (TemporalGraph.volume G.toTemporalGraph 0 Finset.univ : ℝ) := by exact_mod_cast hsum
    _ ≤ 2 * (m : ℝ) := hvol

omit [Nonempty V] [Fintype V] [DecidableEq V] [NeZero κ] in
/-- For `x ≥ 1`, the increment residual `29/24 + 2·log x` is at most `(7/5)·x`.
Certified via the degree-3 Taylor lower bound on `exp`. -/
theorem increment_log_bound {x : ℝ} (hx : 1 ≤ x) :
    29/24 + 2 * Real.log x ≤ 7/5 * x := by
  have hxpos : (0:ℝ) < x := by linarith
  have hLnn : 0 ≤ Real.log x := Real.log_nonneg hx
  have hexp : ∑ i ∈ Finset.range 4, (Real.log x)^i / (i.factorial : ℝ) ≤ Real.exp (Real.log x) :=
    Real.sum_le_exp_of_nonneg hLnn 4
  rw [Real.exp_log hxpos] at hexp
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hexp
  norm_num at hexp
  set L := Real.log x with hL
  nlinarith [sq_nonneg (L - 3/7), pow_nonneg hLnn 3, hexp, hLnn]

omit [Nonempty V] [Fintype V] [DecidableEq V] [NeZero κ] in
/-- For `x ≥ 1`, the residual polynomial `13·(log x)² + (473/48)·log x + 29/24`
is at most `(41/4)·x`. Certified via the degree-6 Taylor lower bound on `exp`. -/
theorem residual_log_bound {x : ℝ} (hx : 1 ≤ x) :
    13*(Real.log x)^2 + 473/48 * Real.log x + 29/24 ≤ 41/4 * x := by
  have hxpos : (0:ℝ) < x := by linarith
  have hLnn : 0 ≤ Real.log x := Real.log_nonneg hx
  have hexp : ∑ i ∈ Finset.range 7, (Real.log x)^i / (i.factorial : ℝ) ≤ Real.exp (Real.log x) :=
    Real.sum_le_exp_of_nonneg hLnn 7
  rw [Real.exp_log hxpos] at hexp
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hexp
  norm_num at hexp
  set L := Real.log x with hL
  nlinarith [hexp, sq_nonneg (L - 5/3), sq_nonneg (L - 2), sq_nonneg (L*(L - 5/3)),
    sq_nonneg (L^2 - 5/3*L), pow_nonneg hLnn 3, pow_nonneg hLnn 5, hLnn]

/-- **D4 (final, eq `multi-opinion-3`).** `E[R_β] ≤ 160·b·m/d_min` for `β = beta κ`. Folds
the residual of `expected_Rbeta_le_combined_filtered` into `b·m/d_min` via the handshake
`n·d_min ≤ 2m`, the contributing-metaphase count `≤ (13/2) log n + 1`, `m ≤ n²/2`, the
increment bound `29/24 + 2 log n ≤ (7/5) n` (`increment_log_bound`), and the residual
polynomial bound `13 log²n + (473/48) log n + 29/24 ≤ (41/4) n` (`residual_log_bound`). -/
theorem VoterModelAbstract.expected_Rbeta_le_final
    (hmono : Monotone (TemporalGraph.phaseTime Δ φ))
    (hd : d_min = G.minDegreeAt 0) (hd_pos : 0 < d_min) (hb : 0 ≤ b) (hΔ_pos : ∀ j, 1 ≤ Δ j)
    (hφ_nn : ∀ j, 0 ≤ φ j) (hφ_le1 : ∀ j, φ j ≤ 1)
    (hreach : TemporalGraph.reachUpToRMax B G.numEdges d_min φ)
    (hwin : ∀ j, ∀ Sc ∈ G.admissibleCuts,
      φ j ≤ G.maxSetConductanceOnInterval (∑ i ∈ Finset.range j, Δ i) (Δ j) Sc)
    (hb_large : (5462 : ℝ) ≤ b) (hm_pos : 0 < G.numEdges)
    (hvol : ∀ t, (TemporalGraph.volume G.toTemporalGraph t Finset.univ : ℝ) ≤ 2 * G.numEdges) :
    (vm.μ : Measure Ω)[fun ω => (vm.metaphase B G.numEdges d_min Δ φ (TemporalGraph.beta κ) ω : ℝ)]
      ≤ 160 * b * (G.numEdges : ℝ) / (d_min : ℝ) := by
  set m : ℕ := G.numEdges
  have hm_edge : m = (G.snapshot 0).edgeFinset.card := rfl
  set n := Fintype.card V with hndef
  have hn_pos : 0 < n := Fintype.card_pos
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_pos
  have hκ1 : (1 : ℝ) ≤ (κ : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne κ)
  have hb' : (5462 : ℝ) ≤ b := by linarith [hb_large]
  have hd1 : (1 : ℝ) ≤ (d_min : ℝ) := by exact_mod_cast hd_pos
  have hd_nn : (0 : ℝ) ≤ (d_min : ℝ) := by linarith
  have hmR_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  set L := Real.log (n : ℝ) with hLdef
  have hL_nn : 0 ≤ L := Real.log_nonneg hn1
  -- `κ`-free count of contributing metaphases
  have hcount : (((Finset.range (TemporalGraph.beta κ)).filter
        (fun α => max ⌈(6 / 7 : ℝ) ^ α * (κ : ℝ)⌉₊ 1 < n)).card : ℝ) ≤ 13 / 2 * L + 1 := by
    rw [hLdef]; exact contributing_count_le (n := n) hκ1 hn_pos
  have hhand : (n : ℝ) * (d_min : ℝ) ≤ 2 * (m : ℝ) := card_mul_minDegree_le m d_min hd (hvol 0)
  -- `m ≤ n²/2`
  have hm_le : 2 * (m : ℝ) ≤ (n : ℝ) ^ 2 := by
    have hedge : m ≤ n.choose 2 := by
      rw [hm_edge]; exact (G.snapshot 0).card_edgeFinset_le_card_choose_two
    have hchoose : 2 * n.choose 2 ≤ n ^ 2 := by
      rw [Nat.choose_two_right]
      nlinarith [Nat.div_mul_le_self (n * (n - 1)) 2, Nat.sub_le n 1,
        Nat.mul_le_mul_left (k := n) (Nat.sub_le n 1)]
    have h2m : 2 * m ≤ n ^ 2 := le_trans (by omega) hchoose
    exact_mod_cast h2m
  have hdle : (d_min : ℝ) ≤ 2 * (m : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hn1 hd_nn
    linarith [hhand]
  -- `log(1 + τm/P) ≤ 29/24 + 2L`, via `1 + 14m/3 ≤ (10/3) n²` and `log(10/3) ≤ 29/24`
  have hlogτm : Real.log (1 + 14 * (m : ℝ) / 3) ≤ 29 / 24 + 2 * L := by
    have h1 : 1 + 14 * (m : ℝ) / 3 ≤ 10 / 3 * (n : ℝ) ^ 2 := by nlinarith [hm_le, hn1]
    have hlog103 : Real.log (10 / 3 : ℝ) ≤ 29 / 24 := by
      rw [show (29 / 24 : ℝ) = Real.log (Real.exp (29 / 24)) from (Real.log_exp _).symm]
      refine Real.log_le_log (by norm_num) ?_
      have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 29 / 24) 6
      simp only [Finset.sum_range_succ, Finset.sum_range_zero] at he
      norm_num at he ⊢
      linarith [he]
    calc Real.log (1 + 14 * (m : ℝ) / 3)
        ≤ Real.log (10 / 3 * (n : ℝ) ^ 2) := Real.log_le_log (by positivity) h1
      _ = Real.log (10 / 3) + 2 * L := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
      _ ≤ 29 / 24 + 2 * L := by linarith
  -- residual/increment polynomial bounds
  have hres_bound : 13 * L ^ 2 + 473 / 48 * L + 29 / 24 ≤ 41 / 4 * (n : ℝ) :=
    residual_log_bound hn1
  have hincr_bd : 29 / 24 + 2 * L ≤ 7 / 5 * (n : ℝ) := increment_log_bound hn1
  -- combine (filtered, `κ`-free)
  have hcomb := vm.expected_Rbeta_le_combined_filtered B m d_min b Δ φ hmono hd hd_pos hb hΔ_pos
    hφ_nn hφ_le1 hreach hwin hb_large hm_pos hvol
  rw [← hndef] at hcomb
  -- fold the residual `(6 + 3b·log(1+14m/3))·count` into `b·m/d_min`
  have hA : 6 + 3 * b * Real.log (1 + 14 * (m : ℝ) / 3) ≤ 6 + 29 / 8 * b + 6 * b * L := by
    have h := mul_le_mul_of_nonneg_left hlogτm (by linarith : (0 : ℝ) ≤ 3 * b)
    linarith
  have hA_nn : (0 : ℝ) ≤ 6 + 29 / 8 * b + 6 * b * L := by
    have h6bL : (0 : ℝ) ≤ 6 * b * L := mul_nonneg (mul_nonneg (by norm_num) hb) hL_nn
    linarith
  have hAB : (6 + 3 * b * Real.log (1 + 14 * (m : ℝ) / 3))
        * (((Finset.range (TemporalGraph.beta κ)).filter
            (fun α => max ⌈(6 / 7 : ℝ) ^ α * (κ : ℝ)⌉₊ 1 < n)).card : ℝ)
      ≤ (6 + 29 / 8 * b + 6 * b * L) * (13 / 2 * L + 1) :=
    mul_le_mul hA hcount (Nat.cast_nonneg _) hA_nn
  -- b-part: `3b·(residual poly)·d ≤ (123/2)·b·m` via `residual_log_bound` + handshake
  have hbL2 : 3 * b * (13 * L ^ 2 + 473 / 48 * L + 29 / 24) * (d_min : ℝ)
      ≤ 123 / 2 * b * (m : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left hres_bound (by positivity : (0 : ℝ) ≤ 3 * b * (d_min : ℝ))
    have h2 := mul_le_mul_of_nonneg_left hhand (by positivity : (0 : ℝ) ≤ 123 / 4 * b)
    nlinarith [h1, h2]
  -- b-free part: `(39 L + 6)·d ≤ (333/5)·m` via `increment_log_bound` + handshake
  have hLd_fold : (39 * L + 6) * (d_min : ℝ) ≤ 333 / 5 * (m : ℝ) := by
    have hLbound : 39 * L ≤ 273 / 10 * (n : ℝ) := by linarith [hincr_bd]
    have h1 := mul_le_mul_of_nonneg_right hLbound hd_nn
    have h2 := mul_le_mul_of_nonneg_left hhand (by norm_num : (0 : ℝ) ≤ 273 / 10)
    have h3 := mul_le_mul_of_nonneg_left hdle (by norm_num : (0 : ℝ) ≤ (6 : ℝ))
    nlinarith [h1, h2, h3]
  have hres_fold : (6 + 29 / 8 * b + 6 * b * L) * (13 / 2 * L + 1)
      ≤ 62 * b * (m : ℝ) / (d_min : ℝ) := by
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < (d_min : ℝ))]
    nlinarith [hbL2, hLd_fold, mul_le_mul_of_nonneg_right hb' hmR_nn]
  calc (vm.μ : Measure Ω)[fun ω => (vm.metaphase B m d_min Δ φ (TemporalGraph.beta κ) ω : ℝ)]
      ≤ 98 * b * (m : ℝ) / (d_min : ℝ)
          + (6 + 3 * b * Real.log (1 + 14 * (m : ℝ) / 3))
            * (((Finset.range (TemporalGraph.beta κ)).filter
                (fun α => max ⌈(6 / 7 : ℝ) ^ α * (κ : ℝ)⌉₊ 1 < n)).card : ℝ) := hcomb
    _ ≤ 98 * b * (m : ℝ) / (d_min : ℝ) + 62 * b * (m : ℝ) / (d_min : ℝ) := by
        linarith [hAB, hres_fold]
    _ = 160 * b * (m : ℝ) / (d_min : ℝ) := by ring

/-- **D4 (consensus index `beta κ + 1`).** `E[R_{beta κ+1}] ≤ 186·b·m/d_min`. Adds the final
increment `E[R_{beta κ+1} − R_{beta κ}] ≤ 3·xiAlpha(θ_{beta κ}+1)` to `expected_Rbeta_le_final`;
since `(1/ρ)^{beta κ} ≤ (1/ρ)κ`, the increment's volume term folds exactly and its `log`
residual folds via the handshake. `R_{beta κ+1}` reaches `θ_{beta κ}=1` (consensus). -/
theorem VoterModelAbstract.expected_Rbeta_succ_le_final
    (hmono : Monotone (TemporalGraph.phaseTime Δ φ))
    (hd : d_min = G.minDegreeAt 0) (hd_pos : 0 < d_min) (hb : 0 ≤ b) (hΔ_pos : ∀ j, 1 ≤ Δ j)
    (hφ_nn : ∀ j, 0 ≤ φ j) (hφ_le1 : ∀ j, φ j ≤ 1)
    (hreach : TemporalGraph.reachUpToRMax B G.numEdges d_min φ)
    (hwin : ∀ j, ∀ Sc ∈ G.admissibleCuts,
      φ j ≤ G.maxSetConductanceOnInterval (∑ i ∈ Finset.range j, Δ i) (Δ j) Sc)
    (hb_large : (5462 : ℝ) ≤ b) (hm_pos : 0 < G.numEdges)
    (hvol : ∀ t, (TemporalGraph.volume G.toTemporalGraph t Finset.univ : ℝ) ≤ 2 * G.numEdges) :
    (vm.μ : Measure Ω)[fun ω =>
        (vm.metaphase B G.numEdges d_min Δ φ (TemporalGraph.beta κ + 1) ω : ℝ)]
      ≤ 186 * b * (G.numEdges : ℝ) / (d_min : ℝ) := by
  set m : ℕ := G.numEdges
  have hm_edge : m = (G.snapshot 0).edgeFinset.card := rfl
  set n := Fintype.card V with hndef
  have hn_pos : 0 < n := Fintype.card_pos
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_pos
  have hκ1 : (1 : ℝ) ≤ (κ : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne κ)
  have hb' : (5462 : ℝ) ≤ b := by linarith [hb_large]
  have hd1 : (1 : ℝ) ≤ (d_min : ℝ) := by exact_mod_cast hd_pos
  have hd_nn : (0 : ℝ) ≤ (d_min : ℝ) := by linarith
  have hmR_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  set L := Real.log (n : ℝ) with hLdef
  have hL_nn : 0 ≤ L := Real.log_nonneg hn1
  have hhand : (n : ℝ) * (d_min : ℝ) ≤ 2 * (m : ℝ) := card_mul_minDegree_le m d_min hd (hvol 0)
  have hm_le : 2 * (m : ℝ) ≤ (n : ℝ) ^ 2 := by
    have hedge : m ≤ n.choose 2 := by
      rw [hm_edge]; exact (G.snapshot 0).card_edgeFinset_le_card_choose_two
    have hchoose : 2 * n.choose 2 ≤ n ^ 2 := by
      rw [Nat.choose_two_right]
      nlinarith [Nat.div_mul_le_self (n * (n - 1)) 2, Nat.sub_le n 1,
        Nat.mul_le_mul_left (k := n) (Nat.sub_le n 1)]
    exact_mod_cast le_trans (show 2 * m ≤ 2 * n.choose 2 by omega) hchoose
  have hdle : (d_min : ℝ) ≤ 2 * (m : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hn1 hd_nn
    linarith [hhand]
  have hincr_bd : 29 / 24 + 2 * L ≤ 7 / 5 * (n : ℝ) := increment_log_bound hn1
  have hlogτm : Real.log (1 + 14 * (m : ℝ) / 3) ≤ 29 / 24 + 2 * L := by
    have h1 : 1 + 14 * (m : ℝ) / 3 ≤ 10 / 3 * (n : ℝ) ^ 2 := by nlinarith [hm_le, hn1]
    have hlog103 : Real.log (10 / 3 : ℝ) ≤ 29 / 24 := by
      rw [show (29 / 24 : ℝ) = Real.log (Real.exp (29 / 24)) from (Real.log_exp _).symm]
      refine Real.log_le_log (by norm_num) ?_
      have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 29 / 24) 6
      simp only [Finset.sum_range_succ, Finset.sum_range_zero] at he
      norm_num at he ⊢
      linarith [he]
    calc Real.log (1 + 14 * (m : ℝ) / 3)
        ≤ Real.log (10 / 3 * (n : ℝ) ^ 2) := Real.log_le_log (by positivity) h1
      _ = Real.log (10 / 3) + 2 * L := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
      _ ≤ 29 / 24 + 2 * L := by linarith
  -- split `R_{beta κ+1} = R_{beta κ} + increment`
  have hRint : ∀ γ, Integrable (fun ω => (vm.metaphase B m d_min Δ φ γ ω : ℝ)) vm.μ :=
    fun γ => vm.integrable_natCast_le (TemporalGraph.rMax B m d_min)
      (vm.metaphase_measurable B m d_min Δ φ hmono γ)
      (fun ω => vm.metaphase_le_rMax B m d_min Δ φ γ ω)
  have hg : Integrable (fun ω => (vm.metaphase B m d_min Δ φ (TemporalGraph.beta κ + 1) ω : ℝ)
      - (vm.metaphase B m d_min Δ φ (TemporalGraph.beta κ) ω : ℝ)) vm.μ :=
    (hRint (TemporalGraph.beta κ + 1)).sub (hRint (TemporalGraph.beta κ))
  have hsplit : (vm.μ : Measure Ω)[fun ω => (vm.metaphase B m d_min Δ φ (TemporalGraph.beta κ + 1) ω : ℝ)]
      = (vm.μ : Measure Ω)[fun ω => (vm.metaphase B m d_min Δ φ (TemporalGraph.beta κ) ω : ℝ)]
        + (vm.μ : Measure Ω)[fun ω => (vm.metaphase B m d_min Δ φ (TemporalGraph.beta κ + 1) ω : ℝ)
              - (vm.metaphase B m d_min Δ φ (TemporalGraph.beta κ) ω : ℝ)] := by
    rw [← integral_add (hRint (TemporalGraph.beta κ)) hg]
    apply integral_congr_ae; filter_upwards with ω; ring
  -- `E[R_{beta κ}]` from `expected_Rbeta_le_final`
  have hRβ : (vm.μ : Measure Ω)[fun ω =>
        (vm.metaphase B m d_min Δ φ (TemporalGraph.beta κ) ω : ℝ)]
      ≤ 160 * b * (m : ℝ) / (d_min : ℝ) :=
    vm.expected_Rbeta_le_final B d_min b Δ φ hmono hd hd_pos hb hΔ_pos hφ_nn hφ_le1
      hreach hwin hb_large hm_pos hvol
  -- `E[increment] ≤ 3·xiAlpha(θ_{beta κ}+1)`
  have hincr := vm.expected_metaphase_increment_tight B m d_min b Δ φ hmono hd hd_pos hb hΔ_pos
    hφ_nn hφ_le1 hreach hwin hb_large hm_pos hvol (TemporalGraph.beta κ)
  -- `xiAlpha(θ_{beta κ}+1) ≤ 2 + b·((49/9)·m/d_min + log(1+14m/3))`
  have hxi := xiAlpha_tight_le b m d_min hb (by exact_mod_cast hd_pos) (by positivity) hκ1
    (TemporalGraph.beta κ)
  have h65 : (7 / 6 : ℝ) ^ (TemporalGraph.beta κ) ≤ (7 / 6 : ℝ) * (κ : ℝ) :=
    sevensixths_pow_beta_le (κ := κ) hκ1
  have hxivol : 14 * (m : ℝ) * (7 / 6 : ℝ) ^ (TemporalGraph.beta κ) / (3 * ((d_min : ℝ) * (κ : ℝ)))
      ≤ 49 / 9 * (m : ℝ) / (d_min : ℝ) := by
    have hco : (0 : ℝ) ≤ 14 * (m : ℝ) / (3 * ((d_min : ℝ) * (κ : ℝ))) := by positivity
    have hdne : (d_min : ℝ) ≠ 0 := ne_of_gt (by linarith)
    have hκne : (κ : ℝ) ≠ 0 := ne_of_gt (by linarith)
    have h1 : 14 * (m : ℝ) * (7 / 6 : ℝ) ^ (TemporalGraph.beta κ) / (3 * ((d_min : ℝ) * (κ : ℝ)))
        = (14 * (m : ℝ) / (3 * ((d_min : ℝ) * (κ : ℝ)))) * (7 / 6 : ℝ) ^ (TemporalGraph.beta κ) := by
      ring
    have h2 : (14 * (m : ℝ) / (3 * ((d_min : ℝ) * (κ : ℝ)))) * (7 / 6 : ℝ) ^ (TemporalGraph.beta κ)
        ≤ (14 * (m : ℝ) / (3 * ((d_min : ℝ) * (κ : ℝ)))) * ((7 / 6 : ℝ) * (κ : ℝ)) :=
      mul_le_mul_of_nonneg_left h65 hco
    have h3 : (14 * (m : ℝ) / (3 * ((d_min : ℝ) * (κ : ℝ)))) * ((7 / 6 : ℝ) * (κ : ℝ))
        = 49 / 9 * (m : ℝ) / (d_min : ℝ) := by field_simp; ring
    linarith [h1.le, h1.ge, h2, h3.le, h3.ge]
  have hxi' : (TemporalGraph.xiAlpha b m d_min (max ⌈(6 / 7 : ℝ) ^ (TemporalGraph.beta κ)
        * (κ : ℝ)⌉₊ 1 + 1) : ℝ)
      ≤ 2 + b * (49 / 9 * (m : ℝ) / (d_min : ℝ) + Real.log (1 + 14 * (m : ℝ) / 3)) := by
    refine le_trans hxi ?_
    have : b * (14 * (m : ℝ) * (7 / 6 : ℝ) ^ (TemporalGraph.beta κ) / (3 * ((d_min : ℝ) * (κ : ℝ)))
        + Real.log (1 + 14 * (m : ℝ) / 3))
        ≤ b * (49 / 9 * (m : ℝ) / (d_min : ℝ) + Real.log (1 + 14 * (m : ℝ) / 3)) :=
      mul_le_mul_of_nonneg_left (by linarith [hxivol]) hb
    linarith
  -- fold the residual `6 + 3b·log(1+14m/3)` into `b·m/d_min`
  have hres : (6 : ℝ) + 3 * b * Real.log (1 + 14 * (m : ℝ) / 3)
      ≤ 9 * b * (m : ℝ) / (d_min : ℝ) := by
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < (d_min : ℝ))]
    have hlogd := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hlogτm hd_nn) (by linarith : (0 : ℝ) ≤ 3 * b)
    have hincd := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hincr_bd hd_nn) (by linarith : (0 : ℝ) ≤ 3 * b)
    have hnd := mul_le_mul_of_nonneg_left hhand (by linarith : (0 : ℝ) ≤ 21 / 5 * b)
    have hd6 := mul_le_mul_of_nonneg_left hdle (by norm_num : (0 : ℝ) ≤ (6 : ℝ))
    have hbm := mul_le_mul_of_nonneg_right hb' hmR_nn
    nlinarith [hlogd, hincd, hnd, hd6, hbm]
  have hincr' : (vm.μ : Measure Ω)[fun ω => (vm.metaphase B m d_min Δ φ (TemporalGraph.beta κ + 1) ω : ℝ)
        - (vm.metaphase B m d_min Δ φ (TemporalGraph.beta κ) ω : ℝ)]
      ≤ 6 + 49 / 3 * b * (m : ℝ) / (d_min : ℝ) + 3 * b * Real.log (1 + 14 * (m : ℝ) / 3) := by
    refine le_trans hincr ?_
    have heq : 3 * (2 + b * (49 / 9 * (m : ℝ) / (d_min : ℝ) + Real.log (1 + 14 * (m : ℝ) / 3)))
        = 6 + 49 / 3 * b * (m : ℝ) / (d_min : ℝ)
          + 3 * b * Real.log (1 + 14 * (m : ℝ) / 3) := by ring
    linarith [mul_le_mul_of_nonneg_left hxi' (by norm_num : (0 : ℝ) ≤ 3), heq.le, heq.ge]
  have hbmd_nn : (0 : ℝ) ≤ b * (m : ℝ) / (d_min : ℝ) :=
    div_nonneg (mul_nonneg hb hmR_nn) hd_nn
  have hcombine : 160 * b * (m : ℝ) / (d_min : ℝ) + 49 / 3 * b * (m : ℝ) / (d_min : ℝ)
      + 9 * b * (m : ℝ) / (d_min : ℝ) ≤ 186 * b * (m : ℝ) / (d_min : ℝ) := by
    have h1 : 160 * b * (m : ℝ) / (d_min : ℝ) + 49 / 3 * b * (m : ℝ) / (d_min : ℝ)
        + 9 * b * (m : ℝ) / (d_min : ℝ) = 556 / 3 * (b * (m : ℝ) / (d_min : ℝ)) := by ring
    have h2 : 186 * b * (m : ℝ) / (d_min : ℝ) = 186 * (b * (m : ℝ) / (d_min : ℝ)) := by ring
    rw [h1, h2]
    linarith [hbmd_nn]
  rw [hsplit]
  refine le_trans (add_le_add hRβ hincr') ?_
  linarith [hres, hcombine]

/-- **Consensus at `R_{beta κ+1}`.** If the metaphase boundary `R_{beta κ+1}` is reached
before the cap `r_max`, then the opinion count there is `1` (`θ_{beta κ} = 1`), i.e.
consensus, so `consensusTime ω ≤ t_{R_{beta κ+1}}` (via pointwise minimality). -/
theorem VoterModelAbstract.metaphase_beta_succ_consensus (ω : Ω)
    (hlt : vm.metaphase B m d_min Δ φ (TemporalGraph.beta κ + 1) ω
      < TemporalGraph.rMax B m d_min) :
    vm.consensusTime ω ≤ (↑(TemporalGraph.phaseTime Δ φ
      (vm.metaphase B m d_min Δ φ (TemporalGraph.beta κ + 1) ω)) : ℕ∞) := by
  have hκ1 : (1 : ℝ) ≤ (κ : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne κ)
  have hcard : (vm.opinionSet (TemporalGraph.phaseTime Δ φ
      (vm.metaphase B m d_min Δ φ (TemporalGraph.beta κ + 1) ω)) ω).card ≤ 1 := by
    rcases vm.metaphase_succ_opinionCard_le B m d_min Δ φ (TemporalGraph.beta κ) ω with hrmax | hcl
    · exfalso; omega
    · rwa [theta_beta_eq_one hκ1] at hcl
  have hne : (vm.opinionSet (TemporalGraph.phaseTime Δ φ
      (vm.metaphase B m d_min Δ φ (TemporalGraph.beta κ + 1) ω)) ω).Nonempty :=
    (Finset.univ_nonempty).image _
  have hcard1 : (vm.opinionSet (TemporalGraph.phaseTime Δ φ
      (vm.metaphase B m d_min Δ φ (TemporalGraph.beta κ + 1) ω)) ω).card = 1 := by
    have := Finset.Nonempty.card_pos hne; omega
  have hcons : VoterModel.IsConsensus (vm.ξ (TemporalGraph.phaseTime Δ φ
      (vm.metaphase B m d_min Δ φ (TemporalGraph.beta κ + 1) ω)) ω) :=
    (TemporalGraph.isConsensus_iff_opinionSet_card_one vm _ ω).mpr hcard1
  by_contra hcon
  exact vm.not_isConsensus_of_lt_consensusTime ω _ (not_le.mp hcon) hcons

omit [NeZero κ] [Nonempty V] [Fintype V] [DecidableEq V] in
/-- If `R ≤ ∑_{ℓ<J+1} φ` then `t_R = phaseTime R ≤ ∑_{j<J+1} Δ` (`phaseIndex R ≤ J+1`). -/
theorem phaseTime_le_sum_Delta (R J : ℕ)
    (hR : (R : ℝ) ≤ ∑ ℓ ∈ Finset.range (J + 1), φ ℓ) :
    TemporalGraph.phaseTime Δ φ R ≤ ∑ j ∈ Finset.range (J + 1), Δ j := by
  have hle : TemporalGraph.phaseIndex φ R ≤ J + 1 := by
    rw [TemporalGraph.phaseIndex_eq_of_reachable φ ⟨J + 1, hR⟩]
    exact Nat.sInf_le (show J + 1 ∈ {ℓ | (R : ℝ) ≤ ∑ j ∈ Finset.range ℓ, φ j} from hR)
  exact Finset.sum_le_sum_of_subset (fun x hx =>
    Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hle))

end TemporalGraph
