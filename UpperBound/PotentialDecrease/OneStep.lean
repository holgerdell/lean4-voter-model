module

public import TemporalGraph.Degree
import VoterProcess.StepwiseEdgesBound
import VoterProcess.TwoOpinion
import TemporalGraph.Basic
import Mathlib.Algebra.Order.Star.Real
import VoterProcess.Expectation
public import Mathlib.Probability.Process.Stopping
public import VoterProcess.Step
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import UpperBound.PotentialDecrease.Helpers

@[expose] public section
open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators

noncomputable section

namespace VoterModel

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]

/-! ## Main results

One-step potential decrease (Case 1, §3.1): `potential_decrease_one_step`,
`prob_good_event`, and `prob_good_event_on_fiber`. -/
/-! ## One-step potential decrease (Case 1 lemmas from §3.1) -/

/-- \label{lem:potdec-regular}

Suppose that `𝒢` is a temporal graph whose degrees are fixed. In the standard
voter model on `𝒢`, let `S_t = vm.S t ω` be the minority set at time `t`.
For all `t ≥ 0`, on the event `{S_t ≠ ∅}`, almost surely:
`E[ψ(S_{t+1}) | ℱ_t] ≤ ψ(S_t) − (d_min/32) · cutS(t) / ψ(S_t)³`.

Here `vm.psiS t ω = √Vol(S_t)` and `vm.cutS t ω = e_t(S_t, V\S_t)`.

Based on Berenbrink et al. (ICALP 2016, Lemma 2.1),
simplified using `Σ_{u∈s} λ_{u,t} = e_t(s,s̄)` and `d(u) ≥ d_min`. -/
theorem potential_decrease_one_step
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    {Ω : Type*} [MeasurableSpace Ω]
    (G : TemporalGraphFixedDegree V)
    (vm : G.VoterModelAbstract 2 Ω)
    -- Time step
    (t : ℕ) :
    -- Conclusion: a.s. on {S_t ≠ ∅}, E[ψ(S_{t+1}) | ℱ_t] ≤ ψ(S_t) − d_min/32 · cutS / ψ(S_t)³
    ∀ᵐ ω ∂(vm.μ : Measure _),
      vm.S t ω ≠ ∅ →
      (vm.μ : Measure _)[fun ω' => vm.psiS (t + 1) ω' | vm.ℱ t] ω
        ≤ vm.psiS t ω
          - (G.minDegreeAt 0 : ℝ) / 32 * (vm.cutS t ω : ℝ) / vm.psiS t ω ^ 3 := by
  -- Under FixedDegrees, minoritySet and volume are time-independent
  have hmin_eq : ∀ A : Finset V, VoterModel.minoritySet G.toTemporalGraph (t + 1) A =
      VoterModel.minoritySet G.toTemporalGraph t A := by
    intro A; unfold VoterModel.minoritySet
    rw [TemporalGraph.volume_fixed G.toTemporalGraph G.fixed A (t + 1) t,
        TemporalGraph.volume_fixed G.toTemporalGraph G.fixed (univ \ A) (t + 1) t]
  have hvol_eq : ∀ S : Finset V,
      (G.snapshot (t + 1)).volume S = (G.snapshot t).volume S :=
    fun S => G.volume_fixed S (t + 1) t
  -- Key function: f(S') = √Vol_t(minSet_t(S'))
  set f : Finset V → ℝ := fun S' =>
    Real.sqrt ((G.snapshot t).volume (VoterModel.minoritySet G.toTemporalGraph t S') : ℝ) with hf_def
  -- vm.psiS (t+1) = f ∘ vm.opinionZeroSet(t+1) under FixedDegrees
  have hpsi_eq : ∀ ω', vm.psiS (t + 1) ω' = f (vm.opinionZeroSet (t + 1) ω') := by
    intro ω'
    simp only [hf_def, TemporalGraph.VoterModelAbstract.psiS, TemporalGraph.potential,
      TemporalGraph.VoterModelAbstract.S, hmin_eq, hvol_eq]
  -- condExp of psiS(t+1) =ᵃᵉ ∫ f dstepDist₂ via voter_condExp_eq_stepDist₂Avg
  have h_ae : (fun ω' => vm.psiS (t + 1) ω') =ᵐ[(vm.μ : Measure _)]
      fun ω' => f (vm.opinionZeroSet (t + 1) ω') :=
    ae_of_all _ (fun ω' => hpsi_eq ω')
  have hce_psi := (condExp_congr_ae h_ae).trans (voter_condExp_eq_stepDist₂Avg vm f t)
  filter_upwards [hce_psi] with ω hω
  intro hS_ne
  rw [hω]
  -- Goal: ∫ f dstepDist₂ ≤ psiS t ω - d_min/32 · cutS / psiS³
  -- Derive nonemptiness of A_t and its complement from hS_ne
  have hs : (vm.opinionZeroSet t ω).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro h
    exact hS_ne (show vm.S t ω = ∅ by
      simp only [TemporalGraph.VoterModelAbstract.S, VoterModel.minoritySet, h,
        TemporalGraph.volume]
      simp [SimpleGraph.volume])
  have hs_compl : (univ \ vm.opinionZeroSet t ω).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro h
    have hA_univ : vm.opinionZeroSet t ω = univ := by
      rw [Finset.sdiff_eq_empty_iff_subset] at h
      exact Finset.eq_univ_of_forall (fun v => h (Finset.mem_univ v))
    apply hS_ne
    show VoterModel.minoritySet G.toTemporalGraph t (vm.opinionZeroSet t ω) = ∅
    rw [hA_univ, VoterModel.minoritySet]
    simp only [Finset.sdiff_self]
    have : ¬((G.snapshot t).volume univ ≤ (G.snapshot t).volume ∅) := by
      simp only [SimpleGraph.volume, Finset.sum_empty, not_le]
      exact Finset.sum_pos (fun v _ => G.degrees_pos v t) ⟨Classical.arbitrary V, Finset.mem_univ _⟩
    exact if_neg this
  -- Apply the minority-volume helper and connect to goal
  have h_bound := stepDist₂_sqrt_minority_volume_upper G t (vm.opinionZeroSet t ω) hs hs_compl
  calc ∫ S', f S' ∂(stepDist₂ G.toTemporalGraph t (vm.opinionZeroSet t ω)).toMeasure
      = ∫ A', √↑((G.snapshot t).volume (minoritySet G.toTemporalGraph t A')) ∂(stepDist₂ G.toTemporalGraph t (vm.opinionZeroSet t ω)).toMeasure := rfl
    _ ≤ _ := h_bound
    _ = vm.psiS t ω - ↑(G.minDegreeAt 0) / 32 * ↑(vm.cutS t ω) / vm.psiS t ω ^ 3 := by
      simp only [TemporalGraph.VoterModelAbstract.psiS, TemporalGraph.potential,
        TemporalGraph.VoterModelAbstract.S, TemporalGraph.VoterModelAbstract.cutS_eq_edgesBetween_A]
      set v := (↑((G.snapshot t).volume (minoritySet G.toTemporalGraph t (vm.opinionZeroSet t ω))) : ℝ) with hv_def
      have hv : 0 ≤ v := Nat.cast_nonneg _
      have h32 : v ^ (3 / 2 : ℝ) = √v ^ 3 := by
        rw [Real.sqrt_eq_rpow, show (3 : ℝ) / 2 = (1 / 2) * 3 from by ring,
          Real.rpow_mul hv, ← Real.rpow_natCast (v ^ (1/2)) 3]; norm_num
      rw [h32]; ring

/-! ## Good event probability -/

/-- Auxiliary sub-step for `lem:prob-good-event` (see `edge_sum_lower_bound` for the paper statement).

Suppose that `𝒢` is a temporal graph whose degrees are fixed. In the standard
voter model on `𝒢` with `κ = 2`, let `S_t` be the minority set at time `t`.
Let `i, t_i ≥ 0`, and suppose `F_{t_i}` is a stable possible value of
`ℱ_{T_i}`. Let `t_{i+1}^*` and `s_{t_i} ≠ ∅` be determined by `ℱ_{T_i}`.
Assume there exists a step `t_i ≤ t' ≤ t_{i+1}^*` such that
`e_{t'}(s_{t_i}, s̄_{t_i}) ≥ Vol(s_{t_i}) / Δ` and
`E[Σ_{j=t_i}^{T_{i+1}−1} e_j(S_j, S̄_j) | ℱ_{T_i}] ≤ μ · Vol(s_{t_i}) / Δ`.
Let `ℰ` be the event that `T_{i+1} > t'` and
`e_{t'}(S_{t'}, S̄_{t'}) ≥ η · Vol(s_{t_i}) / Δ`.
Then `E[𝟙_ℰ | ℱ_{t_i}] ≥ 1/2` a.s. -/
theorem prob_good_event
    {Ω : Type*} [MeasurableSpace Ω]
    (G : TemporalGraphFixedDegree V)
    (vm : G.VoterModelAbstract 2 Ω)
    -- Stopping time T_{i+1}
    (T_next : Ω → ℕ)
    (hT_stop : IsStoppingTime vm.ℱ (fun ω => (T_next ω : ℕ∞)))
    -- Fixed initial set s₀ ≠ ∅, fixed time t_i
    (s₀ : Finset V) (hs₀ : s₀.Nonempty) (t_i : ℕ)
    -- Interval length Δ = t_{i+1}^* − t_i
    (Δ : ℝ) (hΔ_pos : 0 < Δ)
    -- Stability parameter ν
    (ν : ℝ)
    -- Stability: E[|Vol(S_{T_{i+1}}) − Vol(s₀)| | ℱ_{t_i}] < ν · Vol(s₀)
    (hstable : ∀ᵐ ω ∂(vm.μ : Measure _),
      ((vm.μ : Measure _)[fun ω' => |((G.snapshot (T_next ω')).volume (vm.S (T_next ω') ω') : ℝ)
        - ((G.snapshot t_i).volume s₀ : ℝ)| | vm.ℱ t_i]) ω
        < ν * ((G.snapshot t_i).volume s₀ : ℝ))
    -- Parameters η, μ_param with 2ν + μ/(1−η) ≤ 1/2
    (η μ_param : ℝ) (hη1 : η < 1)
    (hparam : 2 * ν + μ_param / (1 - η) ≤ 1 / 2)
    -- Good step t' (fixed, determined by ℱ_{T_i})
    (t' : ℕ) (ht'_ge : t_i ≤ t')
    -- e_{t'}(s₀, V \ s₀) ≥ Vol(s₀) / Δ
    (hgood_step : (G.edgesBetween t' s₀ (univ \ s₀) : ℝ)
        ≥ ((G.snapshot t_i).volume s₀ : ℝ) / Δ)
    -- Edge sum bound: E[Σ e_j(S_j, S̄_j) | ℱ_{t_i}] ≤ μ · Vol(s₀) / Δ
    (hedge_sum : ∀ᵐ ω ∂(vm.μ : Measure _),
      ((vm.μ : Measure _)[fun ω' => ∑ j ∈ Finset.Icc t_i (T_next ω' - 1),
        (vm.cutS j ω' : ℝ) | vm.ℱ t_i]) ω
        ≤ μ_param * ((G.snapshot t_i).volume s₀ : ℝ) / Δ)
    -- Initial set: S_{t_i} = s₀ a.s. (conditioning on ℱ_{t_i})
    (hS_init : ∀ᵐ ω ∂(vm.μ : Measure _), vm.S t_i ω = s₀)
    -- Exit time property: T_next ≤ t' implies Vol deviated by ≥ ½·Vol(s₀)
    -- (T_next is the exit time from the (½)-stability window)
    (hT_exit : ∀ᵐ ω ∂(vm.μ : Measure _), T_next ω ≤ t' →
        (1 / 2 : ℝ) * ((G.snapshot t_i).volume s₀ : ℝ)
          ≤ |((G.snapshot (T_next ω)).volume (vm.S (T_next ω) ω) : ℝ)
              - ((G.snapshot t_i).volume s₀ : ℝ)|)
    -- Integrability of the volume deviation at stopping time
    (hdev_int : Integrable (fun ω =>
        |((G.snapshot (T_next ω)).volume (vm.S (T_next ω) ω) : ℝ)
          - ((G.snapshot t_i).volume s₀ : ℝ)|) vm.μ)
    -- Integrability of the stopped |Δ_j| sum
    (hsum_abs_int : Integrable (fun ω' =>
        ∑ j ∈ Finset.Icc t_i (T_next ω' - 1),
          |(G.edgesBetween t'
              (vm.S (j + 1) ω') (Finset.univ \ vm.S (j + 1) ω') : ℝ)
            - (G.edgesBetween t'
              (vm.S j ω') (Finset.univ \ vm.S j ω') : ℝ)|) vm.μ)
    -- T_next > 0 (deterministic; weaker than `t_i < T_next ω` and constructible
    -- without fiber-restricted info via the embedded-chain-time structure)
    (hT_pos : ∀ ω, 0 < T_next ω)
    -- T_next is bounded by some deterministic N (in paper: T_{j+1} ≤ I_j^+)
    (N : ℕ) (hT_bound : ∀ ω, T_next ω ≤ N)
    -- Per-step integrability of |Δ_j|
    (hΔ_int : ∀ j, Integrable (fun ω' =>
        |(G.edgesBetween t'
            (vm.S (j + 1) ω') (Finset.univ \ vm.S (j + 1) ω') : ℝ)
          - (G.edgesBetween t'
            (vm.S j ω') (Finset.univ \ vm.S j ω') : ℝ)|) vm.μ)
    -- Per-step integrability of cutS
    (hcut_int : ∀ j, Integrable (fun ω' => (vm.cutS j ω' : ℝ)) vm.μ) :
    -- Conclusion: E[𝟙_ℰ | ℱ_{t_i}] ≥ 1/2 a.s.
    -- where ℰ = {T_next > t'} ∩ {e_{t'}(S_{t'}, S̄_{t'}) ≥ η·Vol(s₀)/Δ}
    ∀ᵐ ω ∂(vm.μ : Measure _),
      ((vm.μ : Measure _)[fun ω' =>
        if t' < T_next ω'
          ∧ (vm.cutS t' ω' : ℝ) ≥ η * ((G.snapshot t_i).volume s₀ : ℝ) / Δ
        then (1 : ℝ) else 0 | vm.ℱ t_i]) ω ≥ 1 / 2 := by
  -- Proof sketch (following §3.1, lines 73–161):
  -- Decompose ℰ = ℰ₁ ∩ ℰ₂ where ℰ₁ = {T_{i+1} > t'}, ℰ₂ = {e_{t'}(S_{t'},S̄_{t'}) ≥ η·Vol/Δ}.
  -- P(ℰ) = 1 − P(ℰ̄₁) − P(ℰ₁ ∩ ℰ̄₂).
  -- Step 1: P(ℰ̄₁) ≤ 2ν (Markov + stability).
  -- Step 2: P(ℰ₁ ∩ ℰ̄₂) ≤ μ/(1−η) (Markov + edge sum bound + stepwise edges bound).
  -- Step 3: P(ℰ) ≥ 1 − 2ν − μ/(1−η) ≥ 1/2 (by hparam).
  -- Sub-lemma 1: P(T_{i+1} ≤ t') ≤ 2ν
  -- Strategy (Markov + stability): by Markov's inequality,
  --   P(|Vol(S_{T_next}) - Vol(s₀)| ≥ Vol(s₀)/2 | ℱ_{t_i})
  --     ≤ E[|Vol(S_{T_next}) - Vol(s₀)| | ℱ_{t_i}] / (Vol(s₀)/2)
  --     < ν·Vol(s₀) / (Vol(s₀)/2) = 2ν.
  -- When T_next ≤ t', the stability window exited early, which (by the definition of T_next
  -- as the exit time from the 3/2-stability window) implies |Vol(S_{T_next}) - Vol(s₀)|
  -- ≥ Vol(s₀)/2. Hence P(T_next ≤ t') ≤ P(|Vol(S_{T_next}) - Vol(s₀)| ≥ Vol(s₀)/2) ≤ 2ν.
  -- This requires a formal hypothesis that T_next is the exit time of the stability window,
  -- which is not captured in the current abstract theorem signature.
  have h_prob_E1_bar : ∀ᵐ ω ∂(vm.μ : Measure _),
      ((vm.μ : Measure _)[fun ω' =>
        if T_next ω' ≤ t' then (1 : ℝ) else 0 | vm.ℱ t_i]) ω ≤ 2 * ν := by
    -- Abbreviate Vol₀
    set Vol₀ := ((G.snapshot t_i).volume s₀ : ℝ) with hVol₀_def
    -- Vol₀ > 0: s₀ is nonempty and all degrees are positive
    have hVol_pos : (0 : ℝ) < Vol₀ := by
      obtain ⟨v, hv⟩ := hs₀
      have hd := G.degrees_pos v t_i
      have h_nat : 0 < (G.snapshot t_i).volume s₀ :=
        Nat.lt_of_lt_of_le hd
          (Finset.single_le_sum (f := fun v => (G.snapshot t_i).degree v)
            (fun v _ => Nat.zero_le _) hv)
      exact Nat.cast_pos.mpr h_nat
    have hc_pos : (0 : ℝ) < (2 : ℝ)⁻¹ * Vol₀ := by positivity
    -- Abbreviate the deviation function
    set dev := fun ω' : Ω =>
      |((G.snapshot (T_next ω')).volume (vm.S (T_next ω') ω') : ℝ) - Vol₀|
    set ind := fun ω' : Ω => if T_next ω' ≤ t' then (1 : ℝ) else 0
    -- Pointwise: (1/2) * Vol₀ * ind ≤ dev (from hT_exit)
    have h_pw : ∀ᵐ ω' ∂(vm.μ : Measure _), (2 : ℝ)⁻¹ * Vol₀ * ind ω' ≤ dev ω' := by
      filter_upwards [hT_exit] with ω' h_exit
      simp only [ind, dev]
      by_cases h : T_next ω' ≤ t'
      · simp [h]
        convert h_exit h using 1
        ring
      · simp [h]
    -- Integrability of ind and dev
    have hT_le_meas' : MeasurableSet {ω : Ω | T_next ω ≤ t'} := by
      have h := vm.ℱ.le' t' _ (hT_stop t')
      convert h using 1; ext ω; simp only [Set.mem_setOf_eq]; exact Nat.cast_le.symm
    have hind_int : Integrable ind vm.μ := by
      have : ind = Set.indicator {ω | T_next ω ≤ t'} 1 := by
        ext ω; simp [ind, Set.indicator_apply]
      rw [this]; exact (integrable_const 1).indicator hT_le_meas'
    have hdev_int' : Integrable dev vm.μ := hdev_int
    have hscaled_int : Integrable (fun ω' => (2 : ℝ)⁻¹ * Vol₀ * ind ω') vm.μ := by
      have : (fun ω' => (2 : ℝ)⁻¹ * Vol₀ * ind ω') =
          ((2 : ℝ)⁻¹ * Vol₀) • ind := by ext; simp [smul_eq_mul]
      rw [this]; exact hind_int.smul _
    -- condExp_mono: E[(1/2)*Vol₀*ind | ℱ] ≤ E[dev | ℱ]
    have h_mono := condExp_mono (m := vm.ℱ t_i) hscaled_int hdev_int' h_pw
    -- Factor out constant: E[(1/2)*Vol₀*ind | ℱ] = (1/2)*Vol₀ * E[ind | ℱ]
    have h_fun_eq : (fun ω' => (2 : ℝ)⁻¹ * Vol₀ * ind ω') =
        ((2 : ℝ)⁻¹ * Vol₀) • ind := by ext; simp [smul_eq_mul]
    have h_const_mul : ∀ᵐ ω ∂(vm.μ : Measure _),
        ((vm.μ : Measure _)[fun ω' => (2 : ℝ)⁻¹ * Vol₀ * ind ω' | vm.ℱ t_i]) ω =
        (2 : ℝ)⁻¹ * Vol₀ * ((vm.μ : Measure _)[ind | vm.ℱ t_i]) ω := by
      rw [h_fun_eq]
      have := condExp_smul ((2 : ℝ)⁻¹ * Vol₀) ind (vm.ℱ t_i) (μ := (vm.μ : Measure Ω))
      filter_upwards [this] with ω hω
      simp [Pi.smul_apply, smul_eq_mul] at hω; exact hω
    -- Combine: (1/2)*Vol₀ * E[ind | ℱ] ≤ E[dev | ℱ] < ν * Vol₀
    -- So E[ind | ℱ] < 2ν
    filter_upwards [h_mono, h_const_mul, hstable] with ω hmono hconst hstab
    -- hmono : E[(1/2)*Vol₀*ind | ℱ](ω) ≤ E[dev | ℱ](ω)
    -- hconst : E[(1/2)*Vol₀*ind | ℱ](ω) = (1/2)*Vol₀ * E[ind | ℱ](ω)
    -- hstab : E[dev | ℱ](ω) < ν * Vol₀
    rw [hconst] at hmono
    -- (2⁻¹)*Vol₀ * E[ind | ℱ](ω) ≤ E[dev | ℱ](ω) < ν * Vol₀
    -- So E[ind | ℱ](ω) ≤ 2*ν
    have h_le : (2 : ℝ)⁻¹ * Vol₀ * ((vm.μ : Measure _)[ind | vm.ℱ t_i]) ω < ν * Vol₀ :=
      lt_of_le_of_lt hmono hstab
    -- (2⁻¹)*Vol₀ * x < ν * Vol₀  implies  x ≤ 2*ν
    -- Since Vol₀ > 0 and 2⁻¹ > 0, dividing: x < ν*Vol₀ / (2⁻¹*Vol₀) = 2*ν
    have h_lt : ((vm.μ : Measure _)[ind | vm.ℱ t_i]) ω < 2 * ν := by
      by_contra h_neg
      push Not at h_neg
      -- h_neg: 2*ν ≤ x, so 2⁻¹*Vol₀*x ≥ 2⁻¹*Vol₀*(2*ν) = ν*Vol₀
      nlinarith
    linarith
  -- Sub-lemma 2: P(ℰ₁ ∩ ℰ̄₂) ≤ μ/(1−η)
  -- Strategy (Markov + edge sum): on event {T>t'} ∩ {cutS_{t'} < η·Vol/Δ},
  --   if we sum the contributions, the edge sum bound from hedge_sum gives
  --   E[𝟙_{T>t'} · 𝟙_{cutS_{t'}<η·Vol/Δ}] · η·Vol/Δ ≤ E[Σ cutS] ≤ μ·Vol/Δ,
  --   so P(ℰ₁ ∩ ℰ̄₂) ≤ μ/η. The factor (1-η) comes from a more refined argument
  --   splitting the cutS sum over steps before and at t'. Full formalization requires
  --   extracting the t'-th term from the conditional sum, which depends on measurability
  --   and the exact definition of the cutS sum range.
  have h_prob_E1_E2_bar : ∀ᵐ ω ∂(vm.μ : Measure _),
      ((vm.μ : Measure _)[fun ω' =>
        if t' < T_next ω'
          ∧ ¬((vm.cutS t' ω' : ℝ) ≥ η * ((G.snapshot t_i).volume s₀ : ℝ) / Δ)
        then (1 : ℝ) else 0 | vm.ℱ t_i]) ω ≤ μ_param / (1 - η) := by
    set Vol₀ := ((G.snapshot t_i).volume s₀ : ℝ)
    set ind_E2bar := fun ω' : Ω =>
      if t' < T_next ω'
        ∧ ¬((vm.cutS t' ω' : ℝ) ≥ η * Vol₀ / Δ)
      then (1 : ℝ) else 0
    -- Vol₀ > 0
    have hVol_pos : (0 : ℝ) < Vol₀ := by
      obtain ⟨v, hv⟩ := hs₀
      exact Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (G.degrees_pos v t_i)
        (Finset.single_le_sum (f := fun v => (G.snapshot t_i).degree v)
          (fun v _ => Nat.zero_le _) hv))
    have h_1_sub_η_pos : (0 : ℝ) < 1 - η := by linarith
    have h_coeff_pos : (0 : ℝ) < (1 - η) * Vol₀ / Δ := by positivity
    -- Step A: Pointwise bound on Ē₂
    -- On Ē₂ = {T>t', cutS(t') < η·Vol₀/Δ}:
    --   edgesBetween(t',s₀) ≥ Vol₀/Δ (hgood_step) and cutS(t') < η·Vol₀/Δ,
    --   so edgesBetween(t',s₀) - cutS(t') ≥ (1-η)·Vol₀/Δ.
    have h_pw_Markov : ∀ ω' : Ω,
        (1 - η) * Vol₀ / Δ * ind_E2bar ω' ≤
          |(G.edgesBetween t' s₀ (univ \ s₀) : ℝ)
            - (vm.cutS t' ω' : ℝ)| := by
      intro ω'
      simp only [ind_E2bar]
      by_cases h : t' < T_next ω' ∧
          ¬((vm.cutS t' ω' : ℝ) ≥ η * Vol₀ / Δ)
      · simp [h, mul_one]
        push Not at h
        have hcut_small := h.2
        -- edgesBetween(t', s₀) ≥ Vol₀/Δ and cutS(t') < η·Vol₀/Δ
        -- So |edgesBetween - cutS| ≥ edgesBetween - cutS ≥ (1-η)·Vol₀/Δ
        have h1 : (vm.cutS t' ω' : ℝ) < η * Vol₀ / Δ := hcut_small
        have h2 : Vol₀ / Δ ≤ (G.edgesBetween t' s₀ (univ \ s₀) : ℝ) := hgood_step
        calc (1 - η) * Vol₀ / Δ
            = Vol₀ / Δ - η * Vol₀ / Δ := by ring
          _ ≤ (G.edgesBetween t' s₀ (univ \ s₀) : ℝ) -
              (vm.cutS t' ω' : ℝ) := by linarith
          _ ≤ |(G.edgesBetween t' s₀ (univ \ s₀) : ℝ) -
              (vm.cutS t' ω' : ℝ)| := le_abs_self _
      · rw [if_neg h]; simp
    -- Step B: Bound (1-η)·Vol₀/Δ · ind_E2bar ≤ Σ_{Icc(t_i,T-1)} |Δ_j| pointwise,
    -- then use stopped-sum tower to get E[Σ|Δ_j||ℱ] ≤ E[Σ cutS|ℱ] ≤ μ·Vol₀/Δ.
    -- Integrability of ind_E2bar
    have hT_le_meas' : MeasurableSet {ω : Ω | T_next ω ≤ t'} := by
      have h := vm.ℱ.le' t' _ (hT_stop t')
      convert h using 1; ext ω; simp only [Set.mem_setOf_eq]; exact Nat.cast_le.symm
    have hA_meas' : @Measurable Ω (Finset V) _ ⊤ (vm.opinionZeroSet t') :=
      fun s _ => vm.A_meas t' _ ⟨s, trivial, rfl⟩
    have hS_meas : Measurable (vm.S t') :=
      measurable_from_top.comp hA_meas'
    have hcut_meas' : Measurable (vm.cutS t') := by
      have : vm.cutS t' = (fun s =>
          G.edgesBetween t' s (Finset.univ \ s)) ∘ vm.S t' := by
        ext ω; simp [TemporalGraph.VoterModelAbstract.cutS]
      rw [this]
      exact measurable_from_top.comp hS_meas
    have hcut_real_meas' : Measurable (fun ω : Ω => (vm.cutS t' ω : ℝ)) :=
      measurable_from_nat.comp hcut_meas'
    have hcut_set_meas' : MeasurableSet {ω : Ω |
        (vm.cutS t' ω : ℝ) ≥ η * Vol₀ / Δ} :=
      hcut_real_meas' measurableSet_Ici
    have hind_E2bar_int : Integrable ind_E2bar vm.μ := by
      have hmeas : MeasurableSet ({ω : Ω | t' < T_next ω} ∩
          {ω | ¬(vm.cutS t' ω : ℝ) ≥ η * Vol₀ / Δ}) := by
        convert hT_le_meas'.compl.inter hcut_set_meas'.compl using 1
        ext ω; simp [not_le]
      have heq : ind_E2bar = Set.indicator
          ({ω : Ω | t' < T_next ω} ∩
            {ω | ¬(vm.cutS t' ω : ℝ) ≥ η * Vol₀ / Δ}) 1 := by
        ext ω; simp [ind_E2bar, Set.indicator_apply,
          Set.mem_inter_iff, Set.mem_setOf_eq]
      rw [heq]; exact (integrable_const 1).indicator hmeas
    -- Scaled indicator integrability
    have hscaled_ind_int : Integrable
        (fun ω' => (1 - η) * Vol₀ / Δ * ind_E2bar ω') vm.μ := by
      have : (fun ω' => (1 - η) * Vol₀ / Δ * ind_E2bar ω') =
          ((1 - η) * Vol₀ / Δ) • ind_E2bar := by ext; simp [smul_eq_mul]
      rw [this]; exact hind_E2bar_int.smul _
    -- Factor out constant: E[(1-η)·Vol₀/Δ · ind_E2bar | ℱ] = (1-η)·Vol₀/Δ · E[ind_E2bar | ℱ]
    have h_const_factor : ∀ᵐ ω ∂(vm.μ : Measure _),
        ((vm.μ : Measure _)[fun ω' => (1 - η) * Vol₀ / Δ * ind_E2bar ω' | vm.ℱ t_i]) ω =
        (1 - η) * Vol₀ / Δ * ((vm.μ : Measure _)[ind_E2bar | vm.ℱ t_i]) ω := by
      have hfun : (fun ω' => (1 - η) * Vol₀ / Δ * ind_E2bar ω') =
          ((1 - η) * Vol₀ / Δ) • ind_E2bar := by ext; simp [smul_eq_mul]
      rw [hfun]
      have := condExp_smul ((1 - η) * Vol₀ / Δ) ind_E2bar (vm.ℱ t_i) (μ := (vm.μ : Measure Ω))
      filter_upwards [this] with ω hω
      simp [Pi.smul_apply, smul_eq_mul] at hω; exact hω
    -- Stopped-sum tower: E[Σ_{Icc} |Δ_j| | ℱ_{t_i}] ≤ E[Σ_{Icc} cutS(j) | ℱ_{t_i}]
    -- where Δ_j = edgesBetween(t', S_{j+1}, V\S_{j+1}) - edgesBetween(t', S_j, V\S_j).
    -- Proof: write sum as Σ_j 𝟙_{T>j}·|Δ_j|, then per-term:
    --   E[𝟙_{T>j}·|Δ_j| | ℱ_{t_i}]
    --     = E[E[𝟙_{T>j}·|Δ_j| | ℱ_j] | ℱ_{t_i}]  (tower: condExp_condExp_of_le)
    --     = E[𝟙_{T>j}·E[|Δ_j| | ℱ_j] | ℱ_{t_i}]  (pull-out: 𝟙_{T>j} ℱ_j-meas)
    --     ≤ E[𝟙_{T>j}·cutS(j) | ℱ_{t_i}]          (condExp_mono + stepwise bound)
    -- Sum: Σ_j 𝟙_{T>j}·cutS(j) = Σ_{Icc(t_i,T-1)} cutS(j).
    have h_stopped_tower : ∀ᵐ ω ∂(vm.μ : Measure _),
        ((vm.μ : Measure _)[fun ω' => ∑ j ∈ Finset.Icc t_i (T_next ω' - 1),
            |(G.edgesBetween t'
                (vm.S (j + 1) ω') (univ \ vm.S (j + 1) ω') : ℝ)
              - (G.edgesBetween t'
                (vm.S j ω') (univ \ vm.S j ω') : ℝ)|
            | vm.ℱ t_i]) ω ≤
        ((vm.μ : Measure _)[fun ω' => ∑ j ∈ Finset.Icc t_i (T_next ω' - 1),
            (vm.cutS j ω' : ℝ) | vm.ℱ t_i]) ω := by
      -- Abbreviate the per-step absolute difference
      let Δ_abs (j : ℕ) (ω' : Ω) : ℝ :=
        |(G.edgesBetween t'
            (vm.S (j + 1) ω') (univ \ vm.S (j + 1) ω') : ℝ)
          - (G.edgesBetween t'
            (vm.S j ω') (univ \ vm.S j ω') : ℝ)|
      -- Indicator-weighted term functions
      let f_Δ (j : ℕ) (ω' : Ω) : ℝ :=
        if j < T_next ω' then Δ_abs j ω' else 0
      let f_cut (j : ℕ) (ω' : Ω) : ℝ :=
        if j < T_next ω' then (vm.cutS j ω' : ℝ) else 0
      -- {j < T_next} is measurable (from stopping time)
      have hT_gt_meas : ∀ j, MeasurableSet {ω : Ω | j < T_next ω} := by
        intro j
        have h := hT_stop j
        have hle_meas : MeasurableSet {ω : Ω | T_next ω ≤ j} := by
          convert vm.ℱ.le' j _ h using 1; ext ω
          simp only [Set.mem_setOf_eq]; exact Nat.cast_le.symm
        have : {ω : Ω | j < T_next ω} = {ω | T_next ω ≤ j}ᶜ := by
          ext ω; simp [not_le]
        rw [this]; exact hle_meas.compl
      -- Integrability of indicator-weighted terms
      have hf_Δ_int : ∀ j, Integrable (f_Δ j) vm.μ := by
        intro j
        have heq : f_Δ j = Set.indicator {ω | j < T_next ω}
            (fun ω' => Δ_abs j ω') := by
          ext ω'; simp [f_Δ, Set.indicator_apply]
        rw [heq]; exact (hΔ_int j).indicator (hT_gt_meas j)
      have hf_cut_int : ∀ j, Integrable (f_cut j) vm.μ := by
        intro j
        have heq : f_cut j = Set.indicator {ω | j < T_next ω}
            (fun ω' => (vm.cutS j ω' : ℝ)) := by
          ext ω'; simp [f_cut, Set.indicator_apply]
        rw [heq]; exact (hcut_int j).indicator (hT_gt_meas j)
      -- Step A: The random-range sum equals the indicator sum
      have hIcc_eq_filter : ∀ ω', Finset.Icc t_i (T_next ω' - 1) =
          (Finset.Icc t_i N).filter (fun j => j < T_next ω') := by
        intro ω'
        have hpos := hT_pos ω'
        ext j; simp only [Finset.mem_Icc, Finset.mem_filter]
        by_cases hge : t_i < T_next ω'
        · constructor
          · intro ⟨hle, hlt⟩
            exact ⟨⟨hle, le_trans (by omega) (hT_bound ω')⟩, by omega⟩
          · intro ⟨⟨hle, _⟩, hlt⟩
            exact ⟨hle, by omega⟩
        · -- T_next ω' ≤ t_i and T_next ω' ≥ 1: both sides empty
          push Not at hge
          constructor
          · intro ⟨hle, hlt⟩; omega
          · intro ⟨⟨hle, _⟩, hlt⟩; omega
      have hF_eq : ∀ ω', (∑ j ∈ Finset.Icc t_i N, f_Δ j ω') =
          ∑ j ∈ Finset.Icc t_i (T_next ω' - 1), Δ_abs j ω' := by
        intro ω'
        show ∑ j ∈ Finset.Icc t_i N, (if j < T_next ω' then Δ_abs j ω' else 0) =
          ∑ j ∈ Finset.Icc t_i (T_next ω' - 1), Δ_abs j ω'
        rw [← Finset.sum_filter]
        congr 1; exact (hIcc_eq_filter ω').symm
      have hG_eq : ∀ ω', (∑ j ∈ Finset.Icc t_i N, f_cut j ω') =
          ∑ j ∈ Finset.Icc t_i (T_next ω' - 1), (vm.cutS j ω' : ℝ) := by
        intro ω'
        show ∑ j ∈ Finset.Icc t_i N, (if j < T_next ω' then (vm.cutS j ω' : ℝ) else 0) =
          ∑ j ∈ Finset.Icc t_i (T_next ω' - 1), (vm.cutS j ω' : ℝ)
        rw [← Finset.sum_filter]
        congr 1; exact (hIcc_eq_filter ω').symm
      -- Rewrite LHS and RHS
      have hLHS_eq : (fun ω' => ∑ j ∈ Finset.Icc t_i (T_next ω' - 1), Δ_abs j ω') =
          fun ω' => ∑ j ∈ Finset.Icc t_i N, f_Δ j ω' := by
        ext ω'; exact (hF_eq ω').symm
      have hRHS_eq : (fun ω' => ∑ j ∈ Finset.Icc t_i (T_next ω' - 1),
          (vm.cutS j ω' : ℝ)) = fun ω' => ∑ j ∈ Finset.Icc t_i N, f_cut j ω' := by
        ext ω'; exact (hG_eq ω').symm
      -- Step B: Per-term condExp inequality
      have h_per_term : ∀ j ∈ Finset.Icc t_i N, ∀ᵐ ω ∂(vm.μ : Measure _),
          ((vm.μ : Measure _)[f_Δ j | vm.ℱ t_i]) ω ≤ ((vm.μ : Measure _)[f_cut j | vm.ℱ t_i]) ω := by
        intro j hj
        have htij : t_i ≤ j := (Finset.mem_Icc.mp hj).1
        -- {j < T_next} ∈ ℱ_j (stopping time)
        have hT_le_meas_j : MeasurableSet[vm.ℱ j] {ω : Ω | T_next ω ≤ j} := by
          have h := hT_stop j; convert h using 1; ext ω
          simp only [Set.mem_setOf_eq]; exact Nat.cast_le.symm
        have hT_gt_meas_j : MeasurableSet[vm.ℱ j] {ω : Ω | j < T_next ω} := by
          have : {ω : Ω | j < T_next ω} = {ω | T_next ω ≤ j}ᶜ := by
            ext ω; simp [not_le]
          rw [this]; exact hT_le_meas_j.compl
        -- Indicator is ℱ_j-strongly measurable and bounded
        have hind_sm : StronglyMeasurable[vm.ℱ j]
            (fun ω' => if j < T_next ω' then (1 : ℝ) else 0) :=
          StronglyMeasurable.ite hT_gt_meas_j stronglyMeasurable_one
            stronglyMeasurable_zero
        have hind_bound : ∀ ω', ‖(if j < T_next ω' then (1 : ℝ) else 0)‖ ≤ 1 := by
          intro ω'; split <;> simp
        -- Stepwise bound: E[|Δ_j| | ℱ_j] ≤ cutS_j a.s.
        have hstep := vm.stepwise_edges_bound (G := G) j t'
        -- Write indicator products
        have hind_mul_Δ : f_Δ j =
            (fun ω' => (if j < T_next ω' then (1 : ℝ) else 0) * Δ_abs j ω') := by
          ext ω'; simp only [f_Δ]; split <;> simp
        have hind_mul_cut : f_cut j =
            (fun ω' => (if j < T_next ω' then (1 : ℝ) else 0) *
              (vm.cutS j ω' : ℝ)) := by
          ext ω'; simp only [f_cut]; split <;> simp
        -- Pull-out: E[ind·|Δ_j| | ℱ_j] =ᵃᵉ ind · E[|Δ_j| | ℱ_j]
        have hpullout := condExp_stronglyMeasurable_mul_of_bound
          (vm.ℱ.le j) hind_sm (hΔ_int j) 1 (Filter.Eventually.of_forall hind_bound)
        -- Inner bound: ind · E[|Δ_j| | ℱ_j] ≤ ind · cutS_j
        have h_inner_le : ∀ᵐ ω' ∂(vm.μ : Measure _),
            (if j < T_next ω' then (1 : ℝ) else 0) *
              ((vm.μ : Measure _)[fun ω'' => Δ_abs j ω'' | vm.ℱ j]) ω' ≤
            (if j < T_next ω' then (1 : ℝ) else 0) *
              (vm.cutS j ω' : ℝ) := by
          filter_upwards [hstep] with ω' hω'
          apply mul_le_mul_of_nonneg_left hω'
          split <;> simp
        -- Combine: E[f_Δ j | ℱ_j] ≤ f_cut j a.s.
        have h_cond_j_bound : ∀ᵐ ω' ∂(vm.μ : Measure _),
            ((vm.μ : Measure _)[f_Δ j | vm.ℱ j]) ω' ≤ f_cut j ω' := by
          rw [hind_mul_Δ, hind_mul_cut]
          have hpullout' : (vm.μ : Measure _)[(fun ω' => (if j < T_next ω' then (1 : ℝ) else 0) *
              Δ_abs j ω') | vm.ℱ j] =ᵐ[(vm.μ : Measure _)]
              (fun ω' => (if j < T_next ω' then (1 : ℝ) else 0) *
                ((vm.μ : Measure _)[fun ω'' => Δ_abs j ω'' | vm.ℱ j]) ω') := by
            exact hpullout
          filter_upwards [hpullout', h_inner_le] with ω' hpull hinner
          linarith
        -- Tower: E[f | ℱ_{t_i}] =ᵃᵉ E[E[f | ℱ_j] | ℱ_{t_i}]
        have htower := condExp_condExp_of_le (vm.ℱ.mono htij) (vm.ℱ.le j)
          (μ := (vm.μ : Measure Ω)) (f := f_Δ j)
        -- condExp_mono: E[E[f_Δ|ℱ_j] | ℱ_{t_i}] ≤ E[f_cut | ℱ_{t_i}]
        have h_mono := condExp_mono (m := vm.ℱ t_i)
          integrable_condExp (hf_cut_int j) h_cond_j_bound
        filter_upwards [htower, h_mono] with ω htow hmono
        linarith
      -- Step C: Sum the per-term bounds
      -- Rewrite using condExp_finsetSum
      have hfun_Δ : (fun ω' => ∑ j ∈ Finset.Icc t_i N, f_Δ j ω') =
          ∑ j ∈ Finset.Icc t_i N, f_Δ j := by
        ext ω'; simp [Finset.sum_apply]
      have hfun_cut : (fun ω' => ∑ j ∈ Finset.Icc t_i N, f_cut j ω') =
          ∑ j ∈ Finset.Icc t_i N, f_cut j := by
        ext ω'; simp [Finset.sum_apply]
      have hcondΔ := condExp_finsetSum (s := Finset.Icc t_i N)
        (f := f_Δ) (fun j _ => hf_Δ_int j) (vm.ℱ t_i) (μ := (vm.μ : Measure Ω))
      have hcondCut := condExp_finsetSum (s := Finset.Icc t_i N)
        (f := f_cut) (fun j _ => hf_cut_int j) (vm.ℱ t_i) (μ := (vm.μ : Measure Ω))
      -- Combine per-term ae bounds into sum bound
      have h_sum_bound : ∀ᵐ ω ∂(vm.μ : Measure _),
          (∑ j ∈ Finset.Icc t_i N, ((vm.μ : Measure _)[f_Δ j | vm.ℱ t_i]) ω) ≤
          (∑ j ∈ Finset.Icc t_i N, ((vm.μ : Measure _)[f_cut j | vm.ℱ t_i]) ω) := by
        -- Combine finitely many ae bounds via filter_upwards on their conjunction
        have : ∀ᵐ ω ∂(vm.μ : Measure _), ∀ j ∈ Finset.Icc t_i N,
            ((vm.μ : Measure _)[f_Δ j | vm.ℱ t_i]) ω ≤ ((vm.μ : Measure _)[f_cut j | vm.ℱ t_i]) ω := by
          rw [Filter.eventually_all_finset]
          exact h_per_term
        filter_upwards [this] with ω hω
        exact Finset.sum_le_sum hω
      -- Final chain: rw condExp of sums, apply sum bound
      rw [hLHS_eq, hRHS_eq, hfun_Δ, hfun_cut]
      filter_upwards [hcondΔ, hcondCut, h_sum_bound] with ω hΔ hcut hbound
      simp only [Finset.sum_apply] at hΔ hcut
      linarith
    -- Pointwise: (1-η)·Vol₀/Δ · ind_E2bar ≤ Σ_{Icc(t_i,T-1)} |Δ_j|
    -- On Ē₂ = {T>t', cutS(t') < η·Vol₀/Δ}:
    --   h_pw_Markov: (1-η)·Vol₀/Δ ≤ |e_{t'}(s₀) - cutS(t')|
    --   Telescope: |e_{t'}(s₀) - cutS(t')| ≤ Σ_{Ico(t_i,t')} |Δ_j| (using S_{t_i}=s₀)
    --   Set inclusion: Ico(t_i,t') ⊆ Icc(t_i,T-1) since T>t' on Ē₂
    -- Off Ē₂: ind_E2bar = 0 ≤ sum.
    have h_pw_combined : ∀ᵐ ω' ∂(vm.μ : Measure _),
        (1 - η) * Vol₀ / Δ * ind_E2bar ω' ≤
          ∑ j ∈ Finset.Icc t_i (T_next ω' - 1),
            |(G.edgesBetween t'
                (vm.S (j + 1) ω') (univ \ vm.S (j + 1) ω') : ℝ)
              - (G.edgesBetween t'
                (vm.S j ω') (univ \ vm.S j ω') : ℝ)| := by
      filter_upwards [hS_init] with ω' hS_eq
      simp only [ind_E2bar]
      by_cases h : t' < T_next ω' ∧
          ¬((vm.cutS t' ω' : ℝ) ≥ η * Vol₀ / Δ)
      · simp [h]
        -- Abbreviate the function whose telescoping sum we need
        set f : ℕ → ℝ := fun j =>
          (G.edgesBetween t' (vm.S j ω') (univ \ vm.S j ω') : ℝ)
        -- Step 1: Lower bound from h_pw_Markov
        have h_lower : (1 - η) * Vol₀ / Δ ≤
            ∑ j ∈ Finset.Ico t_i t', |f (j + 1) - f j| := by
          have hmk := h_pw_Markov ω'
          simp only [ind_E2bar, if_pos h, mul_one] at hmk
          -- Rewrite cutS and s₀ in terms of f
          rw [TemporalGraph.VoterModelAbstract.cutS] at hmk
          rw [show s₀ = vm.S t_i ω' from hS_eq.symm] at hmk
          -- hmk : (1-η)*Vol₀/Δ ≤ |f t_i - f t'|
          change (1 - η) * Vol₀ / Δ ≤ |f t_i - f t'| at hmk
          -- Telescope: f t' - f t_i = Σ_{Ico t_i t'} (f(j+1) - f j)
          have h_tele : ∑ j ∈ Finset.Ico t_i t', (f (j + 1) - f j) =
              f t' - f t_i := by
            rw [Finset.sum_Ico_eq_sum_range]
            set g : ℕ → ℝ := fun i => f (t_i + i)
            show ∑ k ∈ Finset.range (t' - t_i), (g (k + 1) - g k) = f t' - f t_i
            rw [Finset.sum_range_sub g]
            have h1 : g 0 = f t_i := by simp [g]
            have h2 : g (t' - t_i) = f t' := by
              simp only [g]; congr 1; omega
            rw [h1, h2]
          -- |f t_i - f t'| = |Σ ...| ≤ Σ |...|
          calc (1 - η) * Vol₀ / Δ
              ≤ |f t_i - f t'| := hmk
            _ = |f t' - f t_i| := abs_sub_comm _ _
            _ = |∑ j ∈ Finset.Ico t_i t', (f (j + 1) - f j)| := by rw [h_tele]
            _ ≤ ∑ j ∈ Finset.Ico t_i t', |f (j + 1) - f j| :=
                Finset.abs_sum_le_sum_abs _ _
        -- Step 2: Ico t_i t' ⊆ Icc t_i (T_next ω' - 1)
        have h_subset : Finset.Ico t_i t' ⊆ Finset.Icc t_i (T_next ω' - 1) := by
          intro j hj
          simp only [Finset.mem_Ico] at hj
          simp only [Finset.mem_Icc]
          exact ⟨hj.1, by omega⟩
        -- Combine: extend the sum over the larger index set
        calc (1 - η) * Vol₀ / Δ
            ≤ ∑ j ∈ Finset.Ico t_i t', |f (j + 1) - f j| := h_lower
          _ ≤ ∑ j ∈ Finset.Icc t_i (T_next ω' - 1), |f (j + 1) - f j| :=
              Finset.sum_le_sum_of_subset_of_nonneg h_subset (fun _ _ _ => abs_nonneg _)
      · simp only [if_neg h, mul_zero]
        exact Finset.sum_nonneg fun j _ => abs_nonneg _
    -- Integrability of the |Δ_j| stopped sum
    have hsum_abs_int' : Integrable (fun ω' =>
        ∑ j ∈ Finset.Icc t_i (T_next ω' - 1),
          |(G.edgesBetween t'
              (vm.S (j + 1) ω') (univ \ vm.S (j + 1) ω') : ℝ)
            - (G.edgesBetween t'
              (vm.S j ω') (univ \ vm.S j ω') : ℝ)|) vm.μ := hsum_abs_int
    -- condExp_mono: E[(1-η)·Vol₀/Δ · ind_E2bar | ℱ] ≤ E[Σ |Δ_j| | ℱ]
    have h_ce_mono := condExp_mono (m := vm.ℱ t_i)
      hscaled_ind_int hsum_abs_int' h_pw_combined
    -- Combine: (1-η)·Vol₀/Δ · E[ind_E2bar | ℱ] ≤ E[Σ|Δ_j||ℱ] ≤ E[Σ cutS|ℱ] ≤ μ·Vol₀/Δ
    filter_upwards [h_ce_mono, h_const_factor, h_stopped_tower, hedge_sum]
      with ω h_mono h_factor h_tower h_hedge
    rw [h_factor] at h_mono
    have h_chain : (1 - η) * Vol₀ / Δ * ((vm.μ : Measure _)[ind_E2bar | vm.ℱ t_i]) ω ≤
        μ_param * Vol₀ / Δ :=
      le_trans h_mono (le_trans h_tower h_hedge)
    -- Divide by (1-η)·Vol₀/Δ > 0 to get E[ind_E2bar | ℱ] ≤ μ/(1-η)
    have hVD_pos : (0 : ℝ) < Vol₀ / Δ := div_pos hVol_pos hΔ_pos
    -- x * (1-η) ≤ μ (cancel Vol₀/Δ > 0)
    have h_step : ((vm.μ : Measure _)[ind_E2bar | vm.ℱ t_i]) ω * (1 - η) ≤ μ_param := by
      by_contra h_neg
      push Not at h_neg
      -- h_neg: μ < x * (1-η), hVD_pos: 0 < Vol₀/Δ
      have h_rw1 : (1 - η) * Vol₀ / Δ *
          ((vm.μ : Measure _)[ind_E2bar | vm.ℱ t_i]) ω =
          ((vm.μ : Measure _)[ind_E2bar | vm.ℱ t_i]) ω * (1 - η) * (Vol₀ / Δ) := by ring
      have h_rw2 : μ_param * Vol₀ / Δ = μ_param * (Vol₀ / Δ) := by ring
      rw [h_rw1, h_rw2] at h_chain
      have : μ_param * (Vol₀ / Δ) <
          ((vm.μ : Measure _)[ind_E2bar | vm.ℱ t_i]) ω * (1 - η) * (Vol₀ / Δ) :=
        mul_lt_mul_of_pos_right h_neg hVD_pos
      linarith
    -- x ≤ μ/(1-η)
    rwa [le_div_iff₀ h_1_sub_η_pos]
  -- Sub-lemma 3: Combine using P(ℰ) ≥ 1 − P(ℰ̄₁) − P(ℰ₁ ∩ ℰ̄₂) ≥ 1 − 2ν − μ/(1−η)
  -- Pointwise: 1_ℰ ≥ 1 − 1_{ℰ̄₁} − 1_{ℰ₁∩ℰ̄₂}, then condexp monotonicity + linearity.
  have h_combine : ∀ᵐ ω ∂(vm.μ : Measure _),
      ((vm.μ : Measure _)[fun ω' =>
        if t' < T_next ω'
          ∧ (vm.cutS t' ω' : ℝ) ≥ η * ((G.snapshot t_i).volume s₀ : ℝ) / Δ
        then (1 : ℝ) else 0 | vm.ℱ t_i]) ω
        ≥ 1 - 2 * ν - μ_param / (1 - η) := by
    -- Abbreviations for the three indicator functions
    set f_good := fun ω' : Ω =>
      if t' < T_next ω'
        ∧ (vm.cutS t' ω' : ℝ) ≥ η * ((G.snapshot t_i).volume s₀ : ℝ) / Δ
      then (1 : ℝ) else 0
    set f_bar1 := fun ω' : Ω => if T_next ω' ≤ t' then (1 : ℝ) else 0
    set f_bar2 := fun ω' : Ω =>
      if t' < T_next ω'
        ∧ ¬((vm.cutS t' ω' : ℝ) ≥ η * ((G.snapshot t_i).volume s₀ : ℝ) / Δ)
      then (1 : ℝ) else 0
    -- Pointwise partition: f_good + f_bar1 + f_bar2 = 1 for all ω'
    have h_partition : ∀ ω', f_good ω' + f_bar1 ω' + f_bar2 ω' = 1 := by
      intro ω'
      simp only [f_good, f_bar1, f_bar2]
      by_cases h1 : T_next ω' ≤ t'
      · have h1' : ¬(t' < T_next ω') := not_lt.mpr h1
        simp [h1, h1']
      · push Not at h1
        by_cases h2 : (vm.cutS t' ω' : ℝ) ≥ η * ((G.snapshot t_i).volume s₀ : ℝ) / Δ
        · simp [h1, h2, not_le.mpr h1]
        · simp [h1, h2, not_le.mpr h1]
    -- Pointwise: f_good ω' ≥ 1 - f_bar1 ω' - f_bar2 ω' (from partition)
    have h_pw : ∀ ω', (1 : ℝ) - f_bar1 ω' - f_bar2 ω' ≤ f_good ω' := by
      intro ω'; linarith [h_partition ω']
    -- Measurability: {T_next ≤ t'} is measurable from the stopping
    -- time, and cutS t' is measurable as a composition through A t'.
    have hT_le_meas : MeasurableSet {ω : Ω | T_next ω ≤ t'} := by
      have h := vm.ℱ.le' t' _ (hT_stop t')
      convert h using 1; ext ω; simp only [Set.mem_setOf_eq]; exact Nat.cast_le.symm
    have hA_meas : @Measurable Ω (Finset V) _ ⊤ (vm.opinionZeroSet t') :=
      fun s _ => vm.A_meas t' _ ⟨s, trivial, rfl⟩
    have hcut_meas : Measurable (vm.cutS t') := by
      have : vm.cutS t' = (fun s =>
          G.edgesBetween t' s (Finset.univ \ s))
          ∘ vm.S t' := by
        ext ω; simp [TemporalGraph.VoterModelAbstract.cutS]
      rw [this]
      have hS_meas : @Measurable Ω (Finset V) _ ⊤ (vm.S t') := by
        intro B _
        have : vm.S t' ⁻¹' B =
            vm.opinionZeroSet t' ⁻¹' {a | VoterModel.minoritySet G.toTemporalGraph t' a ∈ B} := by
          ext ω; simp [TemporalGraph.VoterModelAbstract.S]
        rw [this]; exact hA_meas trivial
      exact measurable_from_top.comp hS_meas
    have hcut_real_meas : Measurable (fun ω : Ω =>
        (vm.cutS t' ω : ℝ)) :=
      measurable_from_nat.comp hcut_meas
    have hcut_set_meas : MeasurableSet {ω : Ω |
        (vm.cutS t' ω : ℝ) ≥
          η * ((G.snapshot t_i).volume s₀ : ℝ) / Δ} :=
      hcut_real_meas measurableSet_Ici
    -- Integrability: each indicator is of a measurable set.
    have hf_bar1_int : Integrable f_bar1 vm.μ := by
      have : f_bar1 = Set.indicator {ω | T_next ω ≤ t'} 1 := by
        ext ω; simp [f_bar1, Set.indicator_apply]
      rw [this]; exact (integrable_const 1).indicator hT_le_meas
    have hf_bar2_int : Integrable f_bar2 vm.μ := by
      have hmeas : MeasurableSet ({ω : Ω | t' < T_next ω} ∩
          {ω | ¬(vm.cutS t' ω : ℝ) ≥
            η * ((G.snapshot t_i).volume s₀ : ℝ) / Δ}) := by
        convert hT_le_meas.compl.inter hcut_set_meas.compl using 1
        ext ω; simp [not_le]
      have heq : f_bar2 = Set.indicator
          ({ω : Ω | t' < T_next ω} ∩ {ω | ¬(vm.cutS t' ω : ℝ) ≥
            η * ((G.snapshot t_i).volume s₀ : ℝ) / Δ}) 1 := by
        ext ω; simp [f_bar2, Set.indicator_apply,
          Set.mem_inter_iff, Set.mem_setOf_eq]
      rw [heq]; exact (integrable_const 1).indicator hmeas
    have hf_good_int : Integrable f_good vm.μ := by
      have hmeas : MeasurableSet ({ω : Ω | t' < T_next ω} ∩
          {ω | (vm.cutS t' ω : ℝ) ≥
            η * ((G.snapshot t_i).volume s₀ : ℝ) / Δ}) := by
        convert hT_le_meas.compl.inter hcut_set_meas using 1
        ext ω; simp [not_le]
      have heq : f_good = Set.indicator
          ({ω : Ω | t' < T_next ω} ∩ {ω | (vm.cutS t' ω : ℝ) ≥
            η * ((G.snapshot t_i).volume s₀ : ℝ) / Δ}) 1 := by
        ext ω; simp [f_good, Set.indicator_apply,
          Set.mem_inter_iff, Set.mem_setOf_eq]
      rw [heq]; exact (integrable_const 1).indicator hmeas
    have hconst_int : Integrable (fun _ : Ω => (1 : ℝ)) vm.μ := integrable_const 1
    -- condExp_mono: from pointwise bound to ae condExp bound
    have h_condexp_mono := @condExp_mono Ω ℝ (vm.ℱ t_i) _ vm.μ
      _ _ _ _ _ _ _ _ _
      ((hconst_int.sub hf_bar1_int).sub hf_bar2_int) hf_good_int
      (Filter.Eventually.of_forall h_pw)
    -- condExp linearity: E[1 - f_bar1 - f_bar2 | F] =ᵃᵉ E[1|F] - E[f_bar1|F] - E[f_bar2|F]
    have h_condexp_sub := condExp_sub (hconst_int.sub hf_bar1_int) hf_bar2_int (vm.ℱ t_i)
    have h_condexp_sub1 := condExp_sub hconst_int hf_bar1_int (vm.ℱ t_i)
    -- E[1 | F] = 1 (true equality, not just a.e.)
    have h_condexp_one : (vm.μ : Measure _)[fun _ : Ω => (1 : ℝ) | vm.ℱ t_i] = fun _ => (1 : ℝ) :=
      condExp_const (vm.ℱ.le' t_i) (1 : ℝ)
    -- Combine: use condExp decomposition to relate the three condExps
    filter_upwards [h_prob_E1_bar, h_prob_E1_E2_bar, h_condexp_mono,
      h_condexp_sub, h_condexp_sub1] with ω hE1 hE2 hmono hsub hsub1
    -- hmono : ((vm.μ : Measure _)[(1:ℝ) - f_bar1 - f_bar2 | F])(ω) ≤ ((vm.μ : Measure _)[f_good | F])(ω)
    -- hsub : ((vm.μ : Measure _)[(1 - f_bar1) - f_bar2 | F])(ω) = ((vm.μ : Measure _)[1 - f_bar1 | F])(ω) - ((vm.μ : Measure _)[f_bar2 | F])(ω)
    -- hsub1 : ((vm.μ : Measure _)[1 - f_bar1 | F])(ω) = ((vm.μ : Measure _)[1 | F])(ω) - ((vm.μ : Measure _)[f_bar1 | F])(ω)
    -- Use h_condexp_one to simplify ((vm.μ : Measure _)[1 | F])(ω) = 1
    have h1_val : ((vm.μ : Measure _)[fun _ : Ω => (1 : ℝ) | vm.ℱ t_i]) ω = 1 := by
      rw [h_condexp_one]
    -- Chain: hmono gives lower bound, hsub + hsub1 + h1_val decompose LHS
    simp only [Pi.sub_apply] at hsub hsub1
    linarith
  -- Final step: 1 − 2ν − μ/(1−η) ≥ 1/2 by hparam
  exact h_combine.mono fun ω hω => le_trans (by linarith [hparam]) hω

/-- \label{lem:prob-good-event}
\label{stmt:prob-good-event-on-fiber} (Fiber-relative variant of `lem:prob-good-event`;
Lean-only sub-task L82 enabling L79.)

The paper's `lem:prob-good-event` conditions on `ℋ_{T_j} = H_{t_j}`, which this
fiber-relative form (`F ∈ ℱ_{t_i}`, `T_j = t_j`, `S_{t_j} = s_j` on `F`) formalizes.

Fiber-relative version of `prob_good_event`. Same setup as the parent except the global
a.e. hypotheses `hstable`, `hedge_sum`, `hT_exit` are restricted to a measurable fiber
`F ∈ ℱ_{t_i}`, and the global a.e. hypothesis `hS_init` becomes a pointwise statement on
`F`. The conclusion is the corresponding a.e. bound on `μ.restrict F`.

**Proof strategy.** Mirrors the parent proof: steps 1 and 2 each use a small bridge
helper to lift `condExp_mono` from a global pointwise-a.e. bound to a `μ.restrict F`
bound (using `F ∈ ℱ_{t_i}` and the indicator pull-out). Step 3 (`h_combine`) is purely
deterministic so its global form transfers directly. The final assembly is on
`μ.restrict F`. -/
theorem prob_good_event_on_fiber
    {Ω : Type*} [MeasurableSpace Ω]
    (G : TemporalGraphFixedDegree V)
    (vm : G.VoterModelAbstract 2 Ω)
    -- Stopping time T_{i+1}
    (T_next : Ω → ℕ)
    (hT_stop : IsStoppingTime vm.ℱ (fun ω => (T_next ω : ℕ∞)))
    -- Fixed initial set s₀ ≠ ∅, fixed time t_i
    (s₀ : Finset V) (hs₀ : s₀.Nonempty) (t_i : ℕ)
    -- Interval length Δ = t_{i+1}^* − t_i
    (Δ : ℝ) (hΔ_pos : 0 < Δ)
    -- Stability parameter ν
    (ν : ℝ)
    -- Fiber F ∈ ℱ_{t_i}
    (F : Set Ω) (hF_meas : MeasurableSet[vm.ℱ t_i] F)
    -- Stability on F: E[|Vol(S_{T_{i+1}}) − Vol(s₀)| | ℱ_{t_i}] < ν · Vol(s₀), a.s. on F
    (hstable : ∀ᵐ ω ∂((vm.μ : Measure _).restrict F),
      ((vm.μ : Measure _)[fun ω' => |((G.snapshot (T_next ω')).volume (vm.S (T_next ω') ω') : ℝ)
        - ((G.snapshot t_i).volume s₀ : ℝ)| | vm.ℱ t_i]) ω
        < ν * ((G.snapshot t_i).volume s₀ : ℝ))
    -- Parameters η, μ_param with 2ν + μ/(1−η) ≤ 1/2
    (η μ_param : ℝ) (hη1 : η < 1)
    (hparam : 2 * ν + μ_param / (1 - η) ≤ 1 / 2)
    -- Good step t' (fixed, determined by ℱ_{T_i})
    (t' : ℕ) (ht'_ge : t_i ≤ t')
    -- e_{t'}(s₀, V \ s₀) ≥ Vol(s₀) / Δ
    (hgood_step : (G.edgesBetween t' s₀ (univ \ s₀) : ℝ)
        ≥ ((G.snapshot t_i).volume s₀ : ℝ) / Δ)
    -- Edge sum bound on F: E[Σ e_j(S_j, S̄_j) | ℱ_{t_i}] ≤ μ · Vol(s₀) / Δ a.s. on F
    (hedge_sum : ∀ᵐ ω ∂((vm.μ : Measure _).restrict F),
      ((vm.μ : Measure _)[fun ω' => ∑ j ∈ Finset.Icc t_i (T_next ω' - 1),
        (vm.cutS j ω' : ℝ) | vm.ℱ t_i]) ω
        ≤ μ_param * ((G.snapshot t_i).volume s₀ : ℝ) / Δ)
    -- Initial set: S_{t_i} = s₀ on F (pointwise)
    (hF_S : ∀ ω ∈ F, vm.S t_i ω = s₀)
    -- Exit time property on F: T_next ≤ t' implies Vol deviated by ≥ ½·Vol(s₀), a.s. on F
    (hT_exit : ∀ᵐ ω ∂((vm.μ : Measure _).restrict F), T_next ω ≤ t' →
        (1 / 2 : ℝ) * ((G.snapshot t_i).volume s₀ : ℝ)
          ≤ |((G.snapshot (T_next ω)).volume (vm.S (T_next ω) ω) : ℝ)
              - ((G.snapshot t_i).volume s₀ : ℝ)|)
    -- Global integrability of the volume deviation at stopping time
    (hdev_int : Integrable (fun ω =>
        |((G.snapshot (T_next ω)).volume (vm.S (T_next ω) ω) : ℝ)
          - ((G.snapshot t_i).volume s₀ : ℝ)|) vm.μ)
    -- Global integrability of the stopped |Δ_j| sum
    (hsum_abs_int : Integrable (fun ω' =>
        ∑ j ∈ Finset.Icc t_i (T_next ω' - 1),
          |(G.edgesBetween t'
              (vm.S (j + 1) ω') (Finset.univ \ vm.S (j + 1) ω') : ℝ)
            - (G.edgesBetween t'
              (vm.S j ω') (Finset.univ \ vm.S j ω') : ℝ)|) vm.μ)
    -- T_next > 0 (deterministic; weaker than `t_i < T_next ω` and constructible
    -- without fiber-restricted info via the embedded-chain-time structure)
    (hT_pos : ∀ ω, 0 < T_next ω)
    -- T_next is bounded by some deterministic N
    (N : ℕ) (hT_bound : ∀ ω, T_next ω ≤ N)
    -- Per-step integrability of |Δ_j|
    (hΔ_int : ∀ j, Integrable (fun ω' =>
        |(G.edgesBetween t'
            (vm.S (j + 1) ω') (Finset.univ \ vm.S (j + 1) ω') : ℝ)
          - (G.edgesBetween t'
            (vm.S j ω') (Finset.univ \ vm.S j ω') : ℝ)|) vm.μ)
    -- Per-step integrability of cutS
    (hcut_int : ∀ j, Integrable (fun ω' => (vm.cutS j ω' : ℝ)) vm.μ) :
    -- Conclusion: E[𝟙_ℰ | ℱ_{t_i}] ≥ 1/2 a.s. on F
    ∀ᵐ ω ∂((vm.μ : Measure _).restrict F),
      ((vm.μ : Measure _)[fun ω' =>
        if t' < T_next ω'
          ∧ (vm.cutS t' ω' : ℝ) ≥ η * ((G.snapshot t_i).volume s₀ : ℝ) / Δ
        then (1 : ℝ) else 0 | vm.ℱ t_i]) ω ≥ 1 / 2 := by
  -- Helper: F as a measurable set in the ambient σ-algebra
  have hF_meas_top : MeasurableSet F := vm.ℱ.le t_i _ hF_meas
  -- Bridge helper: f ≤ g a.e. on μ.restrict F + F ∈ ℱ_{t_i} ⇒
  -- E[f | ℱ_{t_i}] ≤ E[g | ℱ_{t_i}] a.e. on μ.restrict F.
  have hcondExp_le_on_F : ∀ (f g : Ω → ℝ),
      Integrable f vm.μ → Integrable g vm.μ →
      (∀ᵐ ω ∂((vm.μ : Measure _).restrict F), f ω ≤ g ω) →
      ∀ᵐ ω ∂((vm.μ : Measure _).restrict F),
        ((vm.μ : Measure _)[f | vm.ℱ t_i]) ω ≤ ((vm.μ : Measure _)[g | vm.ℱ t_i]) ω := by
    intro f g hf_int hg_int hfg_restrict
    -- ω ∈ F a.e. ⇒ f ω ≤ g ω, equivalently g - f ≥ 0 on F a.e.
    have hfg_global : ∀ᵐ ω ∂(vm.μ : Measure _), ω ∈ F → f ω ≤ g ω :=
      (ae_restrict_iff' hF_meas_top).mp hfg_restrict
    -- 1_F · (g - f) ≥ 0 a.e. globally.
    have h1F_nn : ∀ᵐ ω ∂(vm.μ : Measure _),
        (0 : ℝ) ≤ Set.indicator F (fun ω => g ω - f ω) ω := by
      filter_upwards [hfg_global] with ω hω
      by_cases hωF : ω ∈ F
      · rw [Set.indicator_of_mem hωF]; linarith [hω hωF]
      · rw [Set.indicator_of_notMem hωF]
    -- Integrability of g - f and its indicator.
    have hsub_int : Integrable (fun ω => g ω - f ω) vm.μ := hg_int.sub hf_int
    have hind_int : Integrable (Set.indicator F (fun ω => g ω - f ω)) vm.μ :=
      hsub_int.indicator hF_meas_top
    -- condExp_mono on (0, indicator): 0 ≤ E[1_F · (g - f) | ℱ_{t_i}] a.e.
    have h_condExp_indc_nn : ∀ᵐ ω ∂(vm.μ : Measure _),
        (0 : ℝ) ≤ ((vm.μ : Measure _)[Set.indicator F (fun ω => g ω - f ω) | vm.ℱ t_i]) ω := by
      have hzero_int : Integrable (fun _ : Ω => (0 : ℝ)) vm.μ := integrable_zero _ _ _
      have h0 := condExp_mono (m := vm.ℱ t_i) hzero_int hind_int h1F_nn
      have h0_eq : (vm.μ : Measure _)[fun _ : Ω => (0 : ℝ) | vm.ℱ t_i] =ᵐ[(vm.μ : Measure _)] 0 := by
        have := condExp_const (m := vm.ℱ t_i) (μ := (vm.μ : Measure Ω)) (vm.ℱ.le' t_i) (0 : ℝ)
        rw [this]; rfl
      filter_upwards [h0, h0_eq] with ω hω hz
      have : ((vm.μ : Measure _)[fun _ : Ω => (0 : ℝ) | vm.ℱ t_i]) ω = 0 := hz
      linarith
    -- Pull out indicator: E[1_F · (g - f) | ℱ_{t_i}] =ᵃᵉ 1_F · E[g - f | ℱ_{t_i}].
    have h1F_pullout :
        (vm.μ : Measure _)[Set.indicator F (fun ω => g ω - f ω) | vm.ℱ t_i] =ᵐ[(vm.μ : Measure _)]
        Set.indicator F ((vm.μ : Measure _)[fun ω => g ω - f ω | vm.ℱ t_i]) :=
      condExp_indicator hsub_int hF_meas
    -- Combine: 1_F · E[g - f | ℱ_{t_i}] ≥ 0 a.e.
    have h_indc_subF_nn : ∀ᵐ ω ∂(vm.μ : Measure _),
        (0 : ℝ) ≤ Set.indicator F ((vm.μ : Measure _)[fun ω => g ω - f ω | vm.ℱ t_i]) ω := by
      filter_upwards [h_condExp_indc_nn, h1F_pullout] with ω hω hpo
      rwa [← hpo]
    -- On F: E[g - f | ℱ_{t_i}] ≥ 0 a.e. on restrict F.
    have h_sub_nn_restrict : ∀ᵐ ω ∂((vm.μ : Measure _).restrict F),
        (0 : ℝ) ≤ ((vm.μ : Measure _)[fun ω => g ω - f ω | vm.ℱ t_i]) ω := by
      rw [ae_restrict_iff' hF_meas_top]
      filter_upwards [h_indc_subF_nn] with ω hω hωF
      rwa [Set.indicator_of_mem hωF] at hω
    -- Use condExp_sub: E[g - f | ℱ_{t_i}] =ᵃᵉ E[g | ℱ_{t_i}] - E[f | ℱ_{t_i}].
    have hcondExp_sub :
        (vm.μ : Measure _)[fun ω => g ω - f ω | vm.ℱ t_i] =ᵐ[(vm.μ : Measure _)]
        (vm.μ : Measure _)[g | vm.ℱ t_i] - (vm.μ : Measure _)[f | vm.ℱ t_i] :=
      condExp_sub hg_int hf_int (vm.ℱ t_i)
    have hcondExp_sub_restrict :=
      ae_restrict_of_ae (μ := (vm.μ : Measure Ω)) (s := F) hcondExp_sub
    filter_upwards [h_sub_nn_restrict, hcondExp_sub_restrict] with ω hnn hsub
    have hsub' : ((vm.μ : Measure _)[fun ω => g ω - f ω | vm.ℱ t_i]) ω =
        ((vm.μ : Measure _)[g | vm.ℱ t_i]) ω - ((vm.μ : Measure _)[f | vm.ℱ t_i]) ω := by
      have : ((vm.μ : Measure _)[fun ω => g ω - f ω | vm.ℱ t_i]) ω =
          (((vm.μ : Measure _)[g | vm.ℱ t_i]) - ((vm.μ : Measure _)[f | vm.ℱ t_i])) ω := hsub
      simpa [Pi.sub_apply] using this
    linarith
  -- ===== Sub-lemma 1: P(ℰ̄₁ | ℱ_{t_i}) ≤ 2ν, a.s. on F =====
  have h_prob_E1_bar : ∀ᵐ ω ∂((vm.μ : Measure _).restrict F),
      ((vm.μ : Measure _)[fun ω' =>
        if T_next ω' ≤ t' then (1 : ℝ) else 0 | vm.ℱ t_i]) ω ≤ 2 * ν := by
    set Vol₀ := ((G.snapshot t_i).volume s₀ : ℝ) with hVol₀_def
    have hVol_pos : (0 : ℝ) < Vol₀ := by
      obtain ⟨v, hv⟩ := hs₀
      have hd := G.degrees_pos v t_i
      have h_nat : 0 < (G.snapshot t_i).volume s₀ :=
        Nat.lt_of_lt_of_le hd
          (Finset.single_le_sum (f := fun v => (G.snapshot t_i).degree v)
            (fun v _ => Nat.zero_le _) hv)
      exact Nat.cast_pos.mpr h_nat
    have hc_pos : (0 : ℝ) < (2 : ℝ)⁻¹ * Vol₀ := by positivity
    set dev := fun ω' : Ω =>
      |((G.snapshot (T_next ω')).volume (vm.S (T_next ω') ω') : ℝ) - Vol₀|
    set ind := fun ω' : Ω => if T_next ω' ≤ t' then (1 : ℝ) else 0
    -- Pointwise on F (a.e.): (1/2) * Vol₀ * ind ≤ dev
    have h_pw_F : ∀ᵐ ω' ∂((vm.μ : Measure _).restrict F),
        (2 : ℝ)⁻¹ * Vol₀ * ind ω' ≤ dev ω' := by
      filter_upwards [hT_exit] with ω' h_exit
      simp only [ind, dev]
      by_cases h : T_next ω' ≤ t'
      · simp [h]
        convert h_exit h using 1
        ring
      · simp [h]
    -- Measurability of {T_next ≤ t'}
    have hT_le_meas' : MeasurableSet {ω : Ω | T_next ω ≤ t'} := by
      have h := vm.ℱ.le' t' _ (hT_stop t')
      convert h using 1; ext ω; simp only [Set.mem_setOf_eq]; exact Nat.cast_le.symm
    have hind_int : Integrable ind vm.μ := by
      have : ind = Set.indicator {ω | T_next ω ≤ t'} 1 := by
        ext ω; simp [ind, Set.indicator_apply]
      rw [this]; exact (integrable_const 1).indicator hT_le_meas'
    have hdev_int' : Integrable dev vm.μ := hdev_int
    have hscaled_int : Integrable (fun ω' => (2 : ℝ)⁻¹ * Vol₀ * ind ω') vm.μ := by
      have : (fun ω' => (2 : ℝ)⁻¹ * Vol₀ * ind ω') =
          ((2 : ℝ)⁻¹ * Vol₀) • ind := by ext; simp [smul_eq_mul]
      rw [this]; exact hind_int.smul _
    -- condExp_mono on restrict F: E[(1/2)*Vol₀*ind | ℱ] ≤ E[dev | ℱ] a.e. on F
    have h_mono := hcondExp_le_on_F (fun ω' => (2 : ℝ)⁻¹ * Vol₀ * ind ω') dev
      hscaled_int hdev_int' h_pw_F
    -- Constant-pullout (global): E[(1/2)*Vol₀*ind | ℱ] = (1/2)*Vol₀ * E[ind | ℱ]
    have h_fun_eq : (fun ω' => (2 : ℝ)⁻¹ * Vol₀ * ind ω') =
        ((2 : ℝ)⁻¹ * Vol₀) • ind := by ext; simp [smul_eq_mul]
    have h_const_mul : ∀ᵐ ω ∂(vm.μ : Measure _),
        ((vm.μ : Measure _)[fun ω' => (2 : ℝ)⁻¹ * Vol₀ * ind ω' | vm.ℱ t_i]) ω =
        (2 : ℝ)⁻¹ * Vol₀ * ((vm.μ : Measure _)[ind | vm.ℱ t_i]) ω := by
      rw [h_fun_eq]
      have := condExp_smul ((2 : ℝ)⁻¹ * Vol₀) ind (vm.ℱ t_i) (μ := (vm.μ : Measure Ω))
      filter_upwards [this] with ω hω
      simp [Pi.smul_apply, smul_eq_mul] at hω; exact hω
    have h_const_mul_restrict := ae_restrict_of_ae (μ := (vm.μ : Measure Ω)) (s := F) h_const_mul
    -- Combine using hstable (already on restrict F)
    filter_upwards [h_mono, h_const_mul_restrict, hstable] with ω hmono hconst hstab
    rw [hconst] at hmono
    have h_le : (2 : ℝ)⁻¹ * Vol₀ * ((vm.μ : Measure _)[ind | vm.ℱ t_i]) ω < ν * Vol₀ :=
      lt_of_le_of_lt hmono hstab
    have h_lt : ((vm.μ : Measure _)[ind | vm.ℱ t_i]) ω < 2 * ν := by
      by_contra h_neg
      push Not at h_neg
      nlinarith
    linarith
  -- ===== Sub-lemma 2: P(ℰ₁ ∩ ℰ̄₂ | ℱ_{t_i}) ≤ μ/(1−η), a.s. on F =====
  have h_prob_E1_E2_bar : ∀ᵐ ω ∂((vm.μ : Measure _).restrict F),
      ((vm.μ : Measure _)[fun ω' =>
        if t' < T_next ω'
          ∧ ¬((vm.cutS t' ω' : ℝ) ≥ η * ((G.snapshot t_i).volume s₀ : ℝ) / Δ)
        then (1 : ℝ) else 0 | vm.ℱ t_i]) ω ≤ μ_param / (1 - η) := by
    set Vol₀ := ((G.snapshot t_i).volume s₀ : ℝ)
    set ind_E2bar := fun ω' : Ω =>
      if t' < T_next ω'
        ∧ ¬((vm.cutS t' ω' : ℝ) ≥ η * Vol₀ / Δ)
      then (1 : ℝ) else 0
    have hVol_pos : (0 : ℝ) < Vol₀ := by
      obtain ⟨v, hv⟩ := hs₀
      exact Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (G.degrees_pos v t_i)
        (Finset.single_le_sum (f := fun v => (G.snapshot t_i).degree v)
          (fun v _ => Nat.zero_le _) hv))
    have h_1_sub_η_pos : (0 : ℝ) < 1 - η := by linarith
    have h_coeff_pos : (0 : ℝ) < (1 - η) * Vol₀ / Δ := by positivity
    -- Pointwise (global): on Ē₂, (1-η)*Vol₀/Δ ≤ |edgesBetween(t',s₀) - cutS(t')|
    have h_pw_Markov : ∀ ω' : Ω,
        (1 - η) * Vol₀ / Δ * ind_E2bar ω' ≤
          |(G.edgesBetween t' s₀ (univ \ s₀) : ℝ)
            - (vm.cutS t' ω' : ℝ)| := by
      intro ω'
      simp only [ind_E2bar]
      by_cases h : t' < T_next ω' ∧
          ¬((vm.cutS t' ω' : ℝ) ≥ η * Vol₀ / Δ)
      · simp [h, mul_one]
        push Not at h
        have hcut_small := h.2
        have h1 : (vm.cutS t' ω' : ℝ) < η * Vol₀ / Δ := hcut_small
        have h2 : Vol₀ / Δ ≤ (G.edgesBetween t' s₀ (univ \ s₀) : ℝ) := hgood_step
        calc (1 - η) * Vol₀ / Δ
            = Vol₀ / Δ - η * Vol₀ / Δ := by ring
          _ ≤ (G.edgesBetween t' s₀ (univ \ s₀) : ℝ) -
              (vm.cutS t' ω' : ℝ) := by linarith
          _ ≤ |(G.edgesBetween t' s₀ (univ \ s₀) : ℝ) -
              (vm.cutS t' ω' : ℝ)| := le_abs_self _
      · rw [if_neg h]; simp
    -- Measurability of indicator pieces
    have hT_le_meas' : MeasurableSet {ω : Ω | T_next ω ≤ t'} := by
      have h := vm.ℱ.le' t' _ (hT_stop t')
      convert h using 1; ext ω; simp only [Set.mem_setOf_eq]; exact Nat.cast_le.symm
    have hA_meas' : @Measurable Ω (Finset V) _ ⊤ (vm.opinionZeroSet t') :=
      fun s _ => vm.A_meas t' _ ⟨s, trivial, rfl⟩
    have hS_meas : Measurable (vm.S t') :=
      measurable_from_top.comp hA_meas'
    have hcut_meas' : Measurable (vm.cutS t') := by
      have : vm.cutS t' = (fun s =>
          G.edgesBetween t' s (Finset.univ \ s)) ∘ vm.S t' := by
        ext ω; simp [TemporalGraph.VoterModelAbstract.cutS]
      rw [this]
      exact measurable_from_top.comp hS_meas
    have hcut_real_meas' : Measurable (fun ω : Ω => (vm.cutS t' ω : ℝ)) :=
      measurable_from_nat.comp hcut_meas'
    have hcut_set_meas' : MeasurableSet {ω : Ω |
        (vm.cutS t' ω : ℝ) ≥ η * Vol₀ / Δ} :=
      hcut_real_meas' measurableSet_Ici
    have hind_E2bar_int : Integrable ind_E2bar vm.μ := by
      have hmeas : MeasurableSet ({ω : Ω | t' < T_next ω} ∩
          {ω | ¬(vm.cutS t' ω : ℝ) ≥ η * Vol₀ / Δ}) := by
        convert hT_le_meas'.compl.inter hcut_set_meas'.compl using 1
        ext ω; simp [not_le]
      have heq : ind_E2bar = Set.indicator
          ({ω : Ω | t' < T_next ω} ∩
            {ω | ¬(vm.cutS t' ω : ℝ) ≥ η * Vol₀ / Δ}) 1 := by
        ext ω; simp [ind_E2bar, Set.indicator_apply,
          Set.mem_inter_iff, Set.mem_setOf_eq]
      rw [heq]; exact (integrable_const 1).indicator hmeas
    have hscaled_ind_int : Integrable
        (fun ω' => (1 - η) * Vol₀ / Δ * ind_E2bar ω') vm.μ := by
      have : (fun ω' => (1 - η) * Vol₀ / Δ * ind_E2bar ω') =
          ((1 - η) * Vol₀ / Δ) • ind_E2bar := by ext; simp [smul_eq_mul]
      rw [this]; exact hind_E2bar_int.smul _
    -- Constant-pullout (global)
    have h_const_factor : ∀ᵐ ω ∂(vm.μ : Measure _),
        ((vm.μ : Measure _)[fun ω' => (1 - η) * Vol₀ / Δ * ind_E2bar ω' | vm.ℱ t_i]) ω =
        (1 - η) * Vol₀ / Δ * ((vm.μ : Measure _)[ind_E2bar | vm.ℱ t_i]) ω := by
      have hfun : (fun ω' => (1 - η) * Vol₀ / Δ * ind_E2bar ω') =
          ((1 - η) * Vol₀ / Δ) • ind_E2bar := by ext; simp [smul_eq_mul]
      rw [hfun]
      have := condExp_smul ((1 - η) * Vol₀ / Δ) ind_E2bar (vm.ℱ t_i) (μ := (vm.μ : Measure Ω))
      filter_upwards [this] with ω hω
      simp [Pi.smul_apply, smul_eq_mul] at hω; exact hω
    -- Stopped-sum tower (GLOBAL, same proof as L30): E[Σ |Δ_j| | ℱ_{t_i}] ≤ E[Σ cutS | ℱ_{t_i}]
    have h_stopped_tower : ∀ᵐ ω ∂(vm.μ : Measure _),
        ((vm.μ : Measure _)[fun ω' => ∑ j ∈ Finset.Icc t_i (T_next ω' - 1),
            |(G.edgesBetween t'
                (vm.S (j + 1) ω') (univ \ vm.S (j + 1) ω') : ℝ)
              - (G.edgesBetween t'
                (vm.S j ω') (univ \ vm.S j ω') : ℝ)|
            | vm.ℱ t_i]) ω ≤
        ((vm.μ : Measure _)[fun ω' => ∑ j ∈ Finset.Icc t_i (T_next ω' - 1),
            (vm.cutS j ω' : ℝ) | vm.ℱ t_i]) ω := by
      let Δ_abs (j : ℕ) (ω' : Ω) : ℝ :=
        |(G.edgesBetween t'
            (vm.S (j + 1) ω') (univ \ vm.S (j + 1) ω') : ℝ)
          - (G.edgesBetween t'
            (vm.S j ω') (univ \ vm.S j ω') : ℝ)|
      let f_Δ (j : ℕ) (ω' : Ω) : ℝ :=
        if j < T_next ω' then Δ_abs j ω' else 0
      let f_cut (j : ℕ) (ω' : Ω) : ℝ :=
        if j < T_next ω' then (vm.cutS j ω' : ℝ) else 0
      have hT_gt_meas : ∀ j, MeasurableSet {ω : Ω | j < T_next ω} := by
        intro j
        have h := hT_stop j
        have hle_meas : MeasurableSet {ω : Ω | T_next ω ≤ j} := by
          convert vm.ℱ.le' j _ h using 1; ext ω
          simp only [Set.mem_setOf_eq]; exact Nat.cast_le.symm
        have : {ω : Ω | j < T_next ω} = {ω | T_next ω ≤ j}ᶜ := by
          ext ω; simp [not_le]
        rw [this]; exact hle_meas.compl
      have hf_Δ_int : ∀ j, Integrable (f_Δ j) vm.μ := by
        intro j
        have heq : f_Δ j = Set.indicator {ω | j < T_next ω}
            (fun ω' => Δ_abs j ω') := by
          ext ω'; simp [f_Δ, Set.indicator_apply]
        rw [heq]; exact (hΔ_int j).indicator (hT_gt_meas j)
      have hf_cut_int : ∀ j, Integrable (f_cut j) vm.μ := by
        intro j
        have heq : f_cut j = Set.indicator {ω | j < T_next ω}
            (fun ω' => (vm.cutS j ω' : ℝ)) := by
          ext ω'; simp [f_cut, Set.indicator_apply]
        rw [heq]; exact (hcut_int j).indicator (hT_gt_meas j)
      have hIcc_eq_filter : ∀ ω', Finset.Icc t_i (T_next ω' - 1) =
          (Finset.Icc t_i N).filter (fun j => j < T_next ω') := by
        intro ω'
        have hpos := hT_pos ω'
        ext j; simp only [Finset.mem_Icc, Finset.mem_filter]
        by_cases hge : t_i < T_next ω'
        · constructor
          · intro ⟨hle, hlt⟩
            exact ⟨⟨hle, le_trans (by omega) (hT_bound ω')⟩, by omega⟩
          · intro ⟨⟨hle, _⟩, hlt⟩
            exact ⟨hle, by omega⟩
        · -- T_next ω' ≤ t_i and T_next ω' ≥ 1: both sides empty
          push Not at hge
          constructor
          · intro ⟨hle, hlt⟩; omega
          · intro ⟨⟨hle, _⟩, hlt⟩; omega
      have hF_eq : ∀ ω', (∑ j ∈ Finset.Icc t_i N, f_Δ j ω') =
          ∑ j ∈ Finset.Icc t_i (T_next ω' - 1), Δ_abs j ω' := by
        intro ω'
        show ∑ j ∈ Finset.Icc t_i N, (if j < T_next ω' then Δ_abs j ω' else 0) =
          ∑ j ∈ Finset.Icc t_i (T_next ω' - 1), Δ_abs j ω'
        rw [← Finset.sum_filter]
        congr 1; exact (hIcc_eq_filter ω').symm
      have hG_eq : ∀ ω', (∑ j ∈ Finset.Icc t_i N, f_cut j ω') =
          ∑ j ∈ Finset.Icc t_i (T_next ω' - 1), (vm.cutS j ω' : ℝ) := by
        intro ω'
        show ∑ j ∈ Finset.Icc t_i N, (if j < T_next ω' then (vm.cutS j ω' : ℝ) else 0) =
          ∑ j ∈ Finset.Icc t_i (T_next ω' - 1), (vm.cutS j ω' : ℝ)
        rw [← Finset.sum_filter]
        congr 1; exact (hIcc_eq_filter ω').symm
      have hLHS_eq : (fun ω' => ∑ j ∈ Finset.Icc t_i (T_next ω' - 1), Δ_abs j ω') =
          fun ω' => ∑ j ∈ Finset.Icc t_i N, f_Δ j ω' := by
        ext ω'; exact (hF_eq ω').symm
      have hRHS_eq : (fun ω' => ∑ j ∈ Finset.Icc t_i (T_next ω' - 1),
          (vm.cutS j ω' : ℝ)) = fun ω' => ∑ j ∈ Finset.Icc t_i N, f_cut j ω' := by
        ext ω'; exact (hG_eq ω').symm
      have h_per_term : ∀ j ∈ Finset.Icc t_i N, ∀ᵐ ω ∂(vm.μ : Measure _),
          ((vm.μ : Measure _)[f_Δ j | vm.ℱ t_i]) ω ≤ ((vm.μ : Measure _)[f_cut j | vm.ℱ t_i]) ω := by
        intro j hj
        have htij : t_i ≤ j := (Finset.mem_Icc.mp hj).1
        have hT_le_meas_j : MeasurableSet[vm.ℱ j] {ω : Ω | T_next ω ≤ j} := by
          have h := hT_stop j; convert h using 1; ext ω
          simp only [Set.mem_setOf_eq]; exact Nat.cast_le.symm
        have hT_gt_meas_j : MeasurableSet[vm.ℱ j] {ω : Ω | j < T_next ω} := by
          have : {ω : Ω | j < T_next ω} = {ω | T_next ω ≤ j}ᶜ := by
            ext ω; simp [not_le]
          rw [this]; exact hT_le_meas_j.compl
        have hind_sm : StronglyMeasurable[vm.ℱ j]
            (fun ω' => if j < T_next ω' then (1 : ℝ) else 0) :=
          StronglyMeasurable.ite hT_gt_meas_j stronglyMeasurable_one
            stronglyMeasurable_zero
        have hind_bound : ∀ ω', ‖(if j < T_next ω' then (1 : ℝ) else 0)‖ ≤ 1 := by
          intro ω'; split <;> simp
        have hstep := vm.stepwise_edges_bound (G := G) j t'
        have hind_mul_Δ : f_Δ j =
            (fun ω' => (if j < T_next ω' then (1 : ℝ) else 0) * Δ_abs j ω') := by
          ext ω'; simp only [f_Δ]; split <;> simp
        have hind_mul_cut : f_cut j =
            (fun ω' => (if j < T_next ω' then (1 : ℝ) else 0) *
              (vm.cutS j ω' : ℝ)) := by
          ext ω'; simp only [f_cut]; split <;> simp
        have hpullout := condExp_stronglyMeasurable_mul_of_bound
          (vm.ℱ.le j) hind_sm (hΔ_int j) 1 (Filter.Eventually.of_forall hind_bound)
        have h_inner_le : ∀ᵐ ω' ∂(vm.μ : Measure _),
            (if j < T_next ω' then (1 : ℝ) else 0) *
              ((vm.μ : Measure _)[fun ω'' => Δ_abs j ω'' | vm.ℱ j]) ω' ≤
            (if j < T_next ω' then (1 : ℝ) else 0) *
              (vm.cutS j ω' : ℝ) := by
          filter_upwards [hstep] with ω' hω'
          apply mul_le_mul_of_nonneg_left hω'
          split <;> simp
        have h_cond_j_bound : ∀ᵐ ω' ∂(vm.μ : Measure _),
            ((vm.μ : Measure _)[f_Δ j | vm.ℱ j]) ω' ≤ f_cut j ω' := by
          rw [hind_mul_Δ, hind_mul_cut]
          have hpullout' : (vm.μ : Measure _)[(fun ω' => (if j < T_next ω' then (1 : ℝ) else 0) *
              Δ_abs j ω') | vm.ℱ j] =ᵐ[(vm.μ : Measure _)]
              (fun ω' => (if j < T_next ω' then (1 : ℝ) else 0) *
                ((vm.μ : Measure _)[fun ω'' => Δ_abs j ω'' | vm.ℱ j]) ω') := by
            exact hpullout
          filter_upwards [hpullout', h_inner_le] with ω' hpull hinner
          linarith
        have htower := condExp_condExp_of_le (vm.ℱ.mono htij) (vm.ℱ.le j)
          (μ := (vm.μ : Measure Ω)) (f := f_Δ j)
        have h_mono := condExp_mono (m := vm.ℱ t_i)
          integrable_condExp (hf_cut_int j) h_cond_j_bound
        filter_upwards [htower, h_mono] with ω htow hmono
        linarith
      have hfun_Δ : (fun ω' => ∑ j ∈ Finset.Icc t_i N, f_Δ j ω') =
          ∑ j ∈ Finset.Icc t_i N, f_Δ j := by
        ext ω'; simp [Finset.sum_apply]
      have hfun_cut : (fun ω' => ∑ j ∈ Finset.Icc t_i N, f_cut j ω') =
          ∑ j ∈ Finset.Icc t_i N, f_cut j := by
        ext ω'; simp [Finset.sum_apply]
      have hcondΔ := condExp_finsetSum (s := Finset.Icc t_i N)
        (f := f_Δ) (fun j _ => hf_Δ_int j) (vm.ℱ t_i) (μ := (vm.μ : Measure Ω))
      have hcondCut := condExp_finsetSum (s := Finset.Icc t_i N)
        (f := f_cut) (fun j _ => hf_cut_int j) (vm.ℱ t_i) (μ := (vm.μ : Measure Ω))
      have h_sum_bound : ∀ᵐ ω ∂(vm.μ : Measure _),
          (∑ j ∈ Finset.Icc t_i N, ((vm.μ : Measure _)[f_Δ j | vm.ℱ t_i]) ω) ≤
          (∑ j ∈ Finset.Icc t_i N, ((vm.μ : Measure _)[f_cut j | vm.ℱ t_i]) ω) := by
        have : ∀ᵐ ω ∂(vm.μ : Measure _), ∀ j ∈ Finset.Icc t_i N,
            ((vm.μ : Measure _)[f_Δ j | vm.ℱ t_i]) ω ≤ ((vm.μ : Measure _)[f_cut j | vm.ℱ t_i]) ω := by
          rw [Filter.eventually_all_finset]
          exact h_per_term
        filter_upwards [this] with ω hω
        exact Finset.sum_le_sum hω
      rw [hLHS_eq, hRHS_eq, hfun_Δ, hfun_cut]
      filter_upwards [hcondΔ, hcondCut, h_sum_bound] with ω hΔ hcut hbound
      simp only [Finset.sum_apply] at hΔ hcut
      linarith
    -- Pointwise on F (a.e.): (1-η)·Vol₀/Δ · ind_E2bar ≤ Σ |Δ_j|
    -- (uses hF_S : ∀ ω ∈ F, vm.S t_i ω = s₀)
    have hsum_abs_int' : Integrable (fun ω' =>
        ∑ j ∈ Finset.Icc t_i (T_next ω' - 1),
          |(G.edgesBetween t'
              (vm.S (j + 1) ω') (univ \ vm.S (j + 1) ω') : ℝ)
            - (G.edgesBetween t'
              (vm.S j ω') (univ \ vm.S j ω') : ℝ)|) vm.μ := hsum_abs_int
    -- The pointwise inequality, on restrict F.
    -- We use hF_S directly (pointwise on F), which is stronger than a.e. on restrict F.
    have h_pw_combined : ∀ᵐ ω' ∂((vm.μ : Measure _).restrict F),
        (1 - η) * Vol₀ / Δ * ind_E2bar ω' ≤
          ∑ j ∈ Finset.Icc t_i (T_next ω' - 1),
            |(G.edgesBetween t'
                (vm.S (j + 1) ω') (univ \ vm.S (j + 1) ω') : ℝ)
              - (G.edgesBetween t'
                (vm.S j ω') (univ \ vm.S j ω') : ℝ)| := by
      rw [ae_restrict_iff' hF_meas_top]
      refine Filter.Eventually.of_forall fun ω' hωF => ?_
      have hS_eq : vm.S t_i ω' = s₀ := hF_S ω' hωF
      simp only [ind_E2bar]
      by_cases h : t' < T_next ω' ∧
          ¬((vm.cutS t' ω' : ℝ) ≥ η * Vol₀ / Δ)
      · simp [h]
        set f : ℕ → ℝ := fun j =>
          (G.edgesBetween t' (vm.S j ω') (univ \ vm.S j ω') : ℝ)
        have h_lower : (1 - η) * Vol₀ / Δ ≤
            ∑ j ∈ Finset.Ico t_i t', |f (j + 1) - f j| := by
          have hmk := h_pw_Markov ω'
          simp only [ind_E2bar, if_pos h, mul_one] at hmk
          rw [TemporalGraph.VoterModelAbstract.cutS] at hmk
          rw [show s₀ = vm.S t_i ω' from hS_eq.symm] at hmk
          change (1 - η) * Vol₀ / Δ ≤ |f t_i - f t'| at hmk
          have h_tele : ∑ j ∈ Finset.Ico t_i t', (f (j + 1) - f j) =
              f t' - f t_i := by
            rw [Finset.sum_Ico_eq_sum_range]
            set g : ℕ → ℝ := fun i => f (t_i + i)
            show ∑ k ∈ Finset.range (t' - t_i), (g (k + 1) - g k) = f t' - f t_i
            rw [Finset.sum_range_sub g]
            have h1 : g 0 = f t_i := by simp [g]
            have h2 : g (t' - t_i) = f t' := by
              simp only [g]; congr 1; omega
            rw [h1, h2]
          calc (1 - η) * Vol₀ / Δ
              ≤ |f t_i - f t'| := hmk
            _ = |f t' - f t_i| := abs_sub_comm _ _
            _ = |∑ j ∈ Finset.Ico t_i t', (f (j + 1) - f j)| := by rw [h_tele]
            _ ≤ ∑ j ∈ Finset.Ico t_i t', |f (j + 1) - f j| :=
                Finset.abs_sum_le_sum_abs _ _
        have h_subset : Finset.Ico t_i t' ⊆ Finset.Icc t_i (T_next ω' - 1) := by
          intro j hj
          simp only [Finset.mem_Ico] at hj
          simp only [Finset.mem_Icc]
          exact ⟨hj.1, by omega⟩
        calc (1 - η) * Vol₀ / Δ
            ≤ ∑ j ∈ Finset.Ico t_i t', |f (j + 1) - f j| := h_lower
          _ ≤ ∑ j ∈ Finset.Icc t_i (T_next ω' - 1), |f (j + 1) - f j| :=
              Finset.sum_le_sum_of_subset_of_nonneg h_subset (fun _ _ _ => abs_nonneg _)
      · simp only [if_neg h, mul_zero]
        exact Finset.sum_nonneg fun j _ => abs_nonneg _
    -- condExp_mono on restrict F: E[(1-η)·Vol₀/Δ · ind_E2bar | ℱ] ≤ E[Σ |Δ_j| | ℱ] a.e. on F
    have h_ce_mono := hcondExp_le_on_F
      (fun ω' => (1 - η) * Vol₀ / Δ * ind_E2bar ω')
      (fun ω' => ∑ j ∈ Finset.Icc t_i (T_next ω' - 1),
        |(G.edgesBetween t'
            (vm.S (j + 1) ω') (univ \ vm.S (j + 1) ω') : ℝ)
          - (G.edgesBetween t'
            (vm.S j ω') (univ \ vm.S j ω') : ℝ)|)
      hscaled_ind_int hsum_abs_int' h_pw_combined
    -- Combine on restrict F
    have h_const_factor_restrict := ae_restrict_of_ae (μ := (vm.μ : Measure Ω)) (s := F) h_const_factor
    have h_stopped_tower_restrict := ae_restrict_of_ae (μ := (vm.μ : Measure Ω)) (s := F) h_stopped_tower
    filter_upwards [h_ce_mono, h_const_factor_restrict, h_stopped_tower_restrict, hedge_sum]
      with ω h_mono h_factor h_tower h_hedge
    rw [h_factor] at h_mono
    have h_chain : (1 - η) * Vol₀ / Δ * ((vm.μ : Measure _)[ind_E2bar | vm.ℱ t_i]) ω ≤
        μ_param * Vol₀ / Δ :=
      le_trans h_mono (le_trans h_tower h_hedge)
    have hVD_pos : (0 : ℝ) < Vol₀ / Δ := div_pos hVol_pos hΔ_pos
    have h_step : ((vm.μ : Measure _)[ind_E2bar | vm.ℱ t_i]) ω * (1 - η) ≤ μ_param := by
      by_contra h_neg
      push Not at h_neg
      have h_rw1 : (1 - η) * Vol₀ / Δ *
          ((vm.μ : Measure _)[ind_E2bar | vm.ℱ t_i]) ω =
          ((vm.μ : Measure _)[ind_E2bar | vm.ℱ t_i]) ω * (1 - η) * (Vol₀ / Δ) := by ring
      have h_rw2 : μ_param * Vol₀ / Δ = μ_param * (Vol₀ / Δ) := by ring
      rw [h_rw1, h_rw2] at h_chain
      have : μ_param * (Vol₀ / Δ) <
          ((vm.μ : Measure _)[ind_E2bar | vm.ℱ t_i]) ω * (1 - η) * (Vol₀ / Δ) :=
        mul_lt_mul_of_pos_right h_neg hVD_pos
      linarith
    rwa [le_div_iff₀ h_1_sub_η_pos]
  -- ===== Sub-lemma 3: Combine — purely global (uses no F hypothesis) =====
  -- Pointwise: 1_ℰ ≥ 1 − 1_{ℰ̄₁} − 1_{ℰ₁∩ℰ̄₂}, condexp monotonicity + linearity (global).
  have h_combine : ∀ᵐ ω ∂(vm.μ : Measure _),
      ((vm.μ : Measure _)[fun ω' =>
        if t' < T_next ω'
          ∧ (vm.cutS t' ω' : ℝ) ≥ η * ((G.snapshot t_i).volume s₀ : ℝ) / Δ
        then (1 : ℝ) else 0 | vm.ℱ t_i]) ω
        ≥ ((vm.μ : Measure _)[fun _ : Ω => (1 : ℝ) | vm.ℱ t_i]) ω
        - ((vm.μ : Measure _)[fun ω' =>
            if T_next ω' ≤ t' then (1 : ℝ) else 0 | vm.ℱ t_i]) ω
        - ((vm.μ : Measure _)[fun ω' =>
            if t' < T_next ω'
              ∧ ¬((vm.cutS t' ω' : ℝ) ≥ η * ((G.snapshot t_i).volume s₀ : ℝ) / Δ)
            then (1 : ℝ) else 0 | vm.ℱ t_i]) ω := by
    set f_good := fun ω' : Ω =>
      if t' < T_next ω'
        ∧ (vm.cutS t' ω' : ℝ) ≥ η * ((G.snapshot t_i).volume s₀ : ℝ) / Δ
      then (1 : ℝ) else 0
    set f_bar1 := fun ω' : Ω => if T_next ω' ≤ t' then (1 : ℝ) else 0
    set f_bar2 := fun ω' : Ω =>
      if t' < T_next ω'
        ∧ ¬((vm.cutS t' ω' : ℝ) ≥ η * ((G.snapshot t_i).volume s₀ : ℝ) / Δ)
      then (1 : ℝ) else 0
    have h_partition : ∀ ω', f_good ω' + f_bar1 ω' + f_bar2 ω' = 1 := by
      intro ω'
      simp only [f_good, f_bar1, f_bar2]
      by_cases h1 : T_next ω' ≤ t'
      · have h1' : ¬(t' < T_next ω') := not_lt.mpr h1
        simp [h1, h1']
      · push Not at h1
        by_cases h2 : (vm.cutS t' ω' : ℝ) ≥ η * ((G.snapshot t_i).volume s₀ : ℝ) / Δ
        · simp [h1, h2, not_le.mpr h1]
        · simp [h1, h2, not_le.mpr h1]
    have h_pw : ∀ ω', (1 : ℝ) - f_bar1 ω' - f_bar2 ω' ≤ f_good ω' := by
      intro ω'; linarith [h_partition ω']
    have hT_le_meas : MeasurableSet {ω : Ω | T_next ω ≤ t'} := by
      have h := vm.ℱ.le' t' _ (hT_stop t')
      convert h using 1; ext ω; simp only [Set.mem_setOf_eq]; exact Nat.cast_le.symm
    have hA_meas : @Measurable Ω (Finset V) _ ⊤ (vm.opinionZeroSet t') :=
      fun s _ => vm.A_meas t' _ ⟨s, trivial, rfl⟩
    have hcut_meas : Measurable (vm.cutS t') := by
      have : vm.cutS t' = (fun s =>
          G.edgesBetween t' s (Finset.univ \ s))
          ∘ vm.S t' := by
        ext ω; simp [TemporalGraph.VoterModelAbstract.cutS]
      rw [this]
      have hS_meas : @Measurable Ω (Finset V) _ ⊤ (vm.S t') := by
        intro B _
        have : vm.S t' ⁻¹' B =
            vm.opinionZeroSet t' ⁻¹' {a | VoterModel.minoritySet G.toTemporalGraph t' a ∈ B} := by
          ext ω; simp [TemporalGraph.VoterModelAbstract.S]
        rw [this]; exact hA_meas trivial
      exact measurable_from_top.comp hS_meas
    have hcut_real_meas : Measurable (fun ω : Ω =>
        (vm.cutS t' ω : ℝ)) :=
      measurable_from_nat.comp hcut_meas
    have hcut_set_meas : MeasurableSet {ω : Ω |
        (vm.cutS t' ω : ℝ) ≥
          η * ((G.snapshot t_i).volume s₀ : ℝ) / Δ} :=
      hcut_real_meas measurableSet_Ici
    have hf_bar1_int : Integrable f_bar1 vm.μ := by
      have : f_bar1 = Set.indicator {ω | T_next ω ≤ t'} 1 := by
        ext ω; simp [f_bar1, Set.indicator_apply]
      rw [this]; exact (integrable_const 1).indicator hT_le_meas
    have hf_bar2_int : Integrable f_bar2 vm.μ := by
      have hmeas : MeasurableSet ({ω : Ω | t' < T_next ω} ∩
          {ω | ¬(vm.cutS t' ω : ℝ) ≥
            η * ((G.snapshot t_i).volume s₀ : ℝ) / Δ}) := by
        convert hT_le_meas.compl.inter hcut_set_meas.compl using 1
        ext ω; simp [not_le]
      have heq : f_bar2 = Set.indicator
          ({ω : Ω | t' < T_next ω} ∩ {ω | ¬(vm.cutS t' ω : ℝ) ≥
            η * ((G.snapshot t_i).volume s₀ : ℝ) / Δ}) 1 := by
        ext ω; simp [f_bar2, Set.indicator_apply,
          Set.mem_inter_iff, Set.mem_setOf_eq]
      rw [heq]; exact (integrable_const 1).indicator hmeas
    have hf_good_int : Integrable f_good vm.μ := by
      have hmeas : MeasurableSet ({ω : Ω | t' < T_next ω} ∩
          {ω | (vm.cutS t' ω : ℝ) ≥
            η * ((G.snapshot t_i).volume s₀ : ℝ) / Δ}) := by
        convert hT_le_meas.compl.inter hcut_set_meas using 1
        ext ω; simp [not_le]
      have heq : f_good = Set.indicator
          ({ω : Ω | t' < T_next ω} ∩ {ω | (vm.cutS t' ω : ℝ) ≥
            η * ((G.snapshot t_i).volume s₀ : ℝ) / Δ}) 1 := by
        ext ω; simp [f_good, Set.indicator_apply,
          Set.mem_inter_iff, Set.mem_setOf_eq]
      rw [heq]; exact (integrable_const 1).indicator hmeas
    have hconst_int : Integrable (fun _ : Ω => (1 : ℝ)) vm.μ := integrable_const 1
    have h_condexp_mono := @condExp_mono Ω ℝ (vm.ℱ t_i) _ vm.μ
      _ _ _ _ _ _ _ _ _
      ((hconst_int.sub hf_bar1_int).sub hf_bar2_int) hf_good_int
      (Filter.Eventually.of_forall h_pw)
    have h_condexp_sub := condExp_sub (hconst_int.sub hf_bar1_int) hf_bar2_int (vm.ℱ t_i)
    have h_condexp_sub1 := condExp_sub hconst_int hf_bar1_int (vm.ℱ t_i)
    filter_upwards [h_condexp_mono, h_condexp_sub, h_condexp_sub1]
      with ω hmono hsub hsub1
    simp only [Pi.sub_apply] at hsub hsub1
    linarith
  -- Final assembly on restrict F: combine global h_combine with restricted h_prob_E1_bar
  -- and h_prob_E1_E2_bar, and use E[1 | ℱ_{t_i}] = 1 plus the global hparam bound.
  have h_condexp_one : (vm.μ : Measure _)[fun _ : Ω => (1 : ℝ) | vm.ℱ t_i] = fun _ => (1 : ℝ) :=
    condExp_const (vm.ℱ.le' t_i) (1 : ℝ)
  have h_combine_restrict := ae_restrict_of_ae (μ := (vm.μ : Measure Ω)) (s := F) h_combine
  filter_upwards [h_combine_restrict, h_prob_E1_bar, h_prob_E1_E2_bar]
    with ω hcomb hE1 hE2
  have h1_val : ((vm.μ : Measure _)[fun _ : Ω => (1 : ℝ) | vm.ℱ t_i]) ω = 1 := by
    rw [h_condexp_one]
  -- hcomb gives lower bound; substitute h1_val, hE1, hE2 to conclude ≥ 1/2.
  have hfinal_ineq : (1 : ℝ) - 2 * ν - μ_param / (1 - η) ≤ 1 - 2 * ν - μ_param / (1 - η) :=
    le_refl _
  -- Use hcomb, hE1, hE2, hparam: target ≥ 1/2.
  have : (1 : ℝ) - 2 * ν - μ_param / (1 - η) ≥ 1 / 2 := by linarith [hparam]
  -- Chain: target ≥ 1 - E[f_bar1|F] - E[f_bar2|F] ≥ 1 - 2ν - μ/(1-η) ≥ 1/2
  linarith [hcomb, hE1, hE2, h1_val]


end VoterModel
