module

public import UpperBound.EmbeddedChain
public import TemporalGraph.Degree
import VoterProcess.TwoOpinion
import Mathlib.Algebra.Order.Star.Real
import VoterProcess.Expectation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import UpperBound.PotentialDecrease.Helpers
import UpperBound.PotentialDecrease.OneStep

@[expose] public section
open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators

noncomputable section

namespace VoterModel

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]

/-! ## Main results

Potential decrease over a stable interval: `potential_decrease_stable_interval_*`,
the `Case2Hypotheses` structure, `case2_telescope_bound`, `case2_*`, and the
`..._combined_unconditional*` theorems. -/
/-! ## Potential decrease over a stable interval -/

/-- \label{cor:potdec-regular} Part 1 (edge-sum bound; Lean constant `24√6`, paper has `24√6`).

Suppose `𝒢` is a temporal graph with fixed degrees. In the standard voter
model with `κ = 2`, let `S_t` be the minority set. Let `i, t_i ≥ 0`,
`s_{t_i} ≠ ∅`, `F_{t_i}` a stable value of `ℱ_{T_i}` with `S_{T_i} = s_{t_i}`.
Let `t_{i+1}^*` be the conductance threshold time, `d_min` the minimum degree.
If `E[Σ_{j} 𝟙_{T_{i+1}>j} e_j(S_j, S̄_j) | ℱ_{T_i}] > μ·Vol(s_{t_i})/(t*−t_i)`,
then `E[ψ(S_{T_{i+1}}) − ψ(s_{t_i}) | ℱ_{T_i}] ≤ −μ·d_min / (24√6·(t*−t_i)·ψ(s_{t_i}))`.

**Proof uses** `potential_decrease_one_step` internally to bound each step. -/
theorem potential_decrease_stable_interval_large
    {Ω : Type*} [MeasurableSpace Ω]
    (G : TemporalGraphFixedDegree V)
    (vm : G.VoterModelAbstract 2 Ω)
    -- Fixed initial set s₀ ≠ ∅ and time t_i
    (s₀ : Finset V) (hs₀ : s₀.Nonempty)
    (t_i : ℕ)
    -- Stopping times T_{i+1}
    (T_next : Ω → ℕ)
    -- T_next is a stopping time
    (hT_stop : IsStoppingTime vm.ℱ (fun ω => (T_next ω : ℕ∞)))
    -- Deterministic bound on T_next
    (t' : ℕ) (hT_next_le : ∀ ω, T_next ω ≤ t')
    -- T_next ≥ t_i a.s.
    (hT_next_ge : ∀ᵐ ω ∂(vm.μ : Measure _), t_i ≤ T_next ω)
    -- T_next > 0 a.s. (needed for Ico/Icc conversion in ℕ)
    (hT_next_pos : ∀ᵐ ω ∂(vm.μ : Measure _), 0 < T_next ω)
    -- psiS(t_i) ≤ ψ₀ (minority set at t_i has potential ≤ that of s₀)
    (hpsi_init : ∀ᵐ ω ∂(vm.μ : Measure _),
      vm.psiS t_i ω ≤ G.potential t_i s₀)
    -- Interval length (t* − t_i)
    (Δ : ℝ) (hΔ_pos : 0 < Δ)
    -- Stability: Vol(S_j) ≤ (3/2)·Vol(s₀) throughout [t_i, T_next)
    (hstable_vol : ∀ ω, ∀ j, t_i ≤ j → j < T_next ω →
      ((G.snapshot j).volume (vm.S j ω) : ℝ) ≤
        3 / 2 * ((G.snapshot t_i).volume s₀ : ℝ))
    -- S_j is nonempty throughout [t_i, T_next)
    (hS_nonempty : ∀ ω, ∀ j, t_i ≤ j → j < T_next ω →
      (vm.S j ω).Nonempty)
    -- Large edge sum: E[Σ e_j(S_j, S̄_j)] > μ · Vol(s₀) / Δ
    (μ_param : ℝ)
    (hedge_sum_large : ∀ᵐ ω ∂(vm.μ : Measure _),
      ((vm.μ : Measure _)[fun ω' => ∑ j ∈ Finset.Icc t_i (T_next ω' - 1),
        (vm.cutS j ω' : ℝ) | vm.ℱ t_i]) ω
        > μ_param * ((G.snapshot t_i).volume s₀ : ℝ) / Δ) :
    -- Conclusion: E[ψ(S_{T_{i+1}}) − ψ(s₀) | ℱ_{T_i}] ≤ −μ·d_min/(24√6·Δ·ψ(s₀))
    ∀ᵐ ω ∂(vm.μ : Measure _),
      ((vm.μ : Measure _)[fun ω' => vm.psiS (T_next ω') ω'
        - G.potential t_i s₀ | vm.ℱ t_i]) ω
        ≤ -((μ_param * (G.minDegreeAt 0 : ℝ)) / (24 * Real.sqrt 6 * Δ
          * G.potential t_i s₀)) := by
  -- Proof sketch (following §3.1, lines 169–213):
  -- Step 1: By potential_decrease_one_step, each step gives
  --   E[ψ(S_{t+1}) | S_t = s] ≤ ψ(s) − (d_min/32) · e_t(s,s̄)/ψ(s)³.
  -- Step 2: Telescope over [t_i, T_{i+1}), using tower property and indicator trick.
  --   E[ψ(S_{T_{i+1}}) − ψ(s₀)] ≤ −(d_min/32) · E[Σ e_t(S_t,S̄_t)/ψ(S_t)³]
  -- Step 3: In stable interval, Vol(S_t) ≤ (3/2)Vol(s₀), so ψ(S_t) ≤ (3/2)^{1/2}·ψ(s₀).
  --   Hence 1/ψ(S_t)³ ≥ 1/((3/2)^{3/2}·ψ(s₀)³) = 1/(24√6 · ψ(s₀)³ / d_min ... )
  -- Step 4: Factor out and use edge sum hypothesis.
  -- Sub-lemma: Telescoping with one-step bound
  have h_telescope : ∀ᵐ ω ∂(vm.μ : Measure _),
      ((vm.μ : Measure _)[fun ω' => vm.psiS (T_next ω') ω'
        - G.potential t_i s₀ | vm.ℱ t_i]) ω
        ≤ -(G.minDegreeAt 0 : ℝ) / (24 * Real.sqrt 6 * G.potential t_i s₀ ^ 3)
          * ((vm.μ : Measure _)[fun ω' => ∑ j ∈ Finset.Icc t_i (T_next ω' - 1),
              (vm.cutS j ω' : ℝ) | vm.ℱ t_i]) ω := by
    -- Step A: One-step weighted-edge bound from the axiom.
    -- For each j and s = S_j(ω), potential_decrease_one_step gives:
    --   ∫ S', ψ(S') ∂stepDist₂(j, s) ≤ ψ(s) - (1/32)·∑_u d(u)·e_j(u,V\s) / ψ(s)³
    -- Since d(u) ≥ d_min for all u, and ∑_{u∈s} e_j(u,V\s) = edgesBetween(j,s,V\s) = cutS j:
    --   ≤ ψ(s) - (d_min/32)·cutS j / ψ(s)³
    -- (Each edge (u,v) with u∈s,v∈V\s is counted once from u's side; u∈V\s side counts
    --  internal-complement edges which do not appear in cutS, so ≥ d_min·cutS is valid
    --  by restricting the sum to u∈s.)
    --
    -- Step B: Stability of Vol(S_j) over [t_i, T_next).
    -- In the "stable interval" context, Vol(S_j) ≤ (3/2)·Vol(s₀) a.e., so:
    --   ψ(S_j)³ ≤ ((3/2)·Vol(s₀))^{3/2} = (3/2)^{3/2}·ψ(s₀)³
    --   ⟹ (d_min/32)/ψ(S_j)³ ≥ d_min/(32·(3/2)^{3/2}·ψ(s₀)³) = d_min/(24√6·ψ(s₀)³)
    -- Note: 32·(3/2)^{3/2} = 32·3√3/(2√2) = 32·3/(2√2)·√3 = 24√6.
    --
    -- Step C: Telescope over the interval + tower property.
    -- By the tower property applied iteratively from j = t_i to T_next - 1:
    --   E[ψ(S_{T_next}) - ψ(s₀) | ℱ_{t_i}]
    --   = ∑_{j=t_i}^{T_next-1} E[ψ(S_{j+1}) - ψ(S_j) | ℱ_{t_i}]
    --   ≤ ∑_{j=t_i}^{T_next-1} E[-d_min/(24√6·ψ(s₀)³)·cutS j | ℱ_{t_i}]
    --   = -d_min/(24√6·ψ(s₀)³) · E[∑_{j=t_i}^{T_next-1} cutS j | ℱ_{t_i}]
    --
    -- Missing prerequisites (document the proof gap):
    --
    -- (i) Stability hypothesis: Vol(S_j) ≤ (3/2)·Vol(s₀) for j ∈ [t_i, T_next - 1].
    --     Requires T_next to be defined as the exit time of the stability window.
    --     Not derivable from the current theorem hypotheses.
    --
    -- (ii) The one-step bound in terms of cutS (from potential_decrease_one_step):
    --     ∫ S', ψ(S') ∂stepDist₂(j,s) ≤ ψ(s) - d_min/(32) · cutS(s) / ψ(s)³
    --     follows because d(u) ≥ d_min for all u, and
    --     ∑_u d(u)·degreeIn(u, V\s) ≥ ∑_{u∈s} d(u)·degreeIn(u, V\s)
    --                                    ≥ d_min · ∑_{u∈s} degreeIn(u, V\s)
    --                                    = d_min · edgesBetween(s, V\s).
    --
    -- (iii) With stability (i): ψ(S_j)³ ≤ (3/2)^{3/2} · ψ(s₀)³, so
    --     d_min/(32·ψ(S_j)³) ≥ d_min/(32·(3/2)^{3/2}·ψ(s₀)³) = d_min/(24√6·ψ(s₀)³).
    --     Arithmetic: 32·(3/2)^{3/2} = 32·(3√6/4) = 24√6.
    --     (Since (3/2)^{3/2} = (3/2)·√(3/2) = (3/2)·√6/2 = 3√6/4.)
    --
    -- (iv) Telescoping via tower property:
    --     E[ψ(S_T) - ψ(s₀) | ℱ_{t_i}]
    --     = Σ_{j=t_i}^{T-1} E[ψ(S_{j+1}) - ψ(S_j) | ℱ_{t_i}]    (tower + telescope)
    --     ≤ Σ_{j=t_i}^{T-1} E[-d_min/(24√6·ψ(s₀)³)·cutS j | ℱ_{t_i}]    (steps ii–iii)
    --     = -d_min/(24√6·ψ(s₀)³) · E[Σ cutS j | ℱ_{t_i}].
    --
    -- This full proof requires measure-theoretic tower property infrastructure over
    -- a variable-length stopped interval, not yet formalized in this file.
    --
    -- Proof sketch for the hard steps:
    --
    -- Abbreviate the coefficient for readability.
    set coeff' := -(G.minDegreeAt 0 : ℝ) /
        (24 * Real.sqrt 6 * G.potential t_i s₀ ^ 3) with hcoeff'_def
    -- Step 1: One-step conditional expectation bound.
    -- For each j in [t_i, T_next ω) and for a.e. ω:
    --   E[psiS(j+1) - psiS(j) | ℱ_j](ω) ≤ coeff' · cutS(j)(ω)
    -- Proof outline:
    --   (a) voter_condExp_eq_stepDist₂Avg gives
    --         E[psiS(j+1) | ℱ_j] =ᵃᵉ ∫ S', potential(j+1, S') ∂stepDist₂(j, vm.opinionZeroSet j)
    --       (using psiS ≤ potential and minority-set monotonicity)
    --   (b) potential_decrease_one_step gives the integral bound in terms of cutS and psiS(j)
    --   (c) Stability (hstable_vol) gives psiS(j)³ ≤ (3/2)^{3/2} · ψ₀³ = 12√6/16 · ψ₀³,
    --       so the coefficient 1/psiS(j)³ ≥ 1/((3/2)^{3/2}·ψ₀³) and
    --       d_min/16/psiS(j)³ ≥ d_min/(24√6·ψ₀³) = -coeff'.
    -- This step requires both the one-step axiom and the stability hypothesis.
    -- One-step conditional expectation bound (with stable interval guards).
    -- For j ∈ [t_i, T_next ω) and a.e. ω:
    --   E[psiS(j+1) - psiS(j) | ℱ_j](ω) ≤ coeff' · cutS(j)(ω)
    -- Proof:
    --   (a) potential_decrease_one_step gives
    --         E[psiS(j+1) | ℱ_j] ≤ psiS(j) − (d_min/16)·cutS/psiS(j)³
    --   (b) Stability (hstable_vol) gives psiS(j)² ≤ (3/2)·ψ₀², hence
    --       psiS(j)³ ≤ (3/2)^{3/2}·ψ₀³, so 1/psiS(j)³ ≥ 1/((3/2)^{3/2}·ψ₀³).
    --   (c) 16·(3/2)^{3/2} = 12√6 ≤ 24√6, giving d_min/(16·psiS³) ≥ coeff'.
    have h_onestep : ∀ j, ∀ᵐ ω ∂(vm.μ : Measure _),
        t_i ≤ j → j < T_next ω →
        ((vm.μ : Measure _)[fun ω' => vm.psiS (j + 1) ω' - vm.psiS j ω' | vm.ℱ j]) ω
          ≤ coeff' * (vm.cutS j ω : ℝ) := by
      intro j
      -- Integrability and measurability setup
      let f_succ : Finset V → ℝ :=
        fun s' => G.potential (j + 1) (minoritySet G.toTemporalGraph (j + 1) s')
      have hpsi_eq : ∀ ω', vm.psiS (j + 1) ω' = f_succ (vm.opinionZeroSet (j + 1) ω') :=
        fun ω' => show G.potential (j + 1) (vm.S (j + 1) ω') =
            G.potential (j + 1) (minoritySet G.toTemporalGraph (j + 1) (vm.opinionZeroSet (j + 1) ω'))
          from by simp [TemporalGraph.VoterModelAbstract.S]
      have hpsi1_int : Integrable (fun ω' => vm.psiS (j + 1) ω') vm.μ :=
        (voter_integrable_comp_A vm f_succ (j + 1)).congr
          (Filter.Eventually.of_forall fun ω' => (hpsi_eq ω').symm)
      have hpsi_j_int : Integrable (fun ω' => vm.psiS j ω') vm.μ :=
        (voter_integrable_comp_A vm
          (fun s' => G.potential j (minoritySet G.toTemporalGraph j s')) j).congr
          (Filter.Eventually.of_forall fun ω' => by
            simp [TemporalGraph.VoterModelAbstract.psiS, TemporalGraph.VoterModelAbstract.S])
      have hAj_Fmeas : @Measurable Ω (Finset V) (vm.ℱ j) ⊤ (vm.opinionZeroSet j) :=
        (vm.A_stronglyAdapted j).measurable
      have hpsi_j_sm : StronglyMeasurable[vm.ℱ j] (fun ω' => vm.psiS j ω') := by
        have hfact : (fun ω' => vm.psiS j ω') =
            (fun s' => G.potential j (minoritySet G.toTemporalGraph j s')) ∘ (vm.opinionZeroSet j) := by
          funext ω'
          simp [TemporalGraph.VoterModelAbstract.psiS, TemporalGraph.VoterModelAbstract.S]
        rw [hfact]
        exact ((measurable_of_finite _).comp hAj_Fmeas).stronglyMeasurable
      -- Split condExp of difference: E[psiS(j+1) - psiS(j) | ℱ_j] =ᵃᵉ E[psiS(j+1) | ℱ_j] - psiS(j)
      have hcE_split : (vm.μ : Measure _)[fun ω' => vm.psiS (j + 1) ω' - vm.psiS j ω' | vm.ℱ j]
          =ᵐ[(vm.μ : Measure _)]
          (vm.μ : Measure _)[fun ω' => vm.psiS (j + 1) ω' | vm.ℱ j] - fun ω' => vm.psiS j ω' := by
        have h1 := condExp_sub hpsi1_int hpsi_j_int (vm.ℱ j)
        have h2 := condExp_of_stronglyMeasurable (vm.ℱ.le j) hpsi_j_sm hpsi_j_int
        rw [h2] at h1
        exact h1
      -- Use potential_decrease_one_step for step j
      filter_upwards [hcE_split, potential_decrease_one_step G vm j] with ω h_split h_pdos
      intro hj_ge hj_lt
      rw [h_split]; simp only [Pi.sub_apply]
      -- S_j(ω) is nonempty in the stable interval
      have hS_ne : (vm.S j ω).Nonempty := hS_nonempty ω j hj_ge hj_lt
      -- From potential_decrease_one_step: E[psiS(j+1)|F_j](ω) ≤ psiS(j)(ω) − (d_min/32)·cutS(j)/psiS(j)³
      have h_ax := h_pdos hS_ne.ne_empty
      -- Need: −(d_min/32)·cutS/psiS(j)³ ≤ coeff'·cutS = −d_min/(24√6·ψ₀³)·cutS
      -- Suffices: 32·psiS(j)³ ≤ 24√6·ψ₀³
      -- From stability: Vol(S_j) ≤ (3/2)·Vol(s₀), so psiS(j)² ≤ (3/2)·ψ₀²
      -- Hence psiS(j)³ ≤ (3/2)^{3/2}·ψ₀³ and 32·(3/2)^{3/2} = 24√6.
      set ψ₀ := G.potential t_i s₀
      set ψ_j := vm.psiS j ω
      set c_j := (vm.cutS j ω : ℝ)
      set d_min := (G.minDegreeAt 0 : ℝ)
      -- Stability: Vol(S_j) ≤ (3/2)·Vol(s₀)
      have hstab := hstable_vol ω j hj_ge hj_lt
      -- psiS(j)² = Vol(S_j) and ψ₀² = Vol(s₀)
      have hψ_j_sq : ψ_j ^ 2 = ((G.snapshot j).volume (vm.S j ω) : ℝ) := by
        simp only [ψ_j, TemporalGraph.VoterModelAbstract.psiS, TemporalGraph.potential]
        exact Real.sq_sqrt (Nat.cast_nonneg _)
      have hψ₀_sq : ψ₀ ^ 2 = ((G.snapshot t_i).volume s₀ : ℝ) := by
        simp only [ψ₀, TemporalGraph.potential]
        exact Real.sq_sqrt (Nat.cast_nonneg _)
      -- psiS(j)² ≤ (3/2)·ψ₀²
      have hψ_sq_le : ψ_j ^ 2 ≤ 3 / 2 * ψ₀ ^ 2 := by rw [hψ_j_sq, hψ₀_sq]; exact hstab
      -- Nonnegativity
      have hψ_j_nn : 0 ≤ ψ_j := Real.sqrt_nonneg _
      have hψ₀_nn : 0 ≤ ψ₀ := Real.sqrt_nonneg _
      have hc_nn : 0 ≤ c_j := Nat.cast_nonneg _
      have hd_nn : 0 ≤ d_min := Nat.cast_nonneg _
      -- Key inequality: 16·ψ_j³ ≤ 24√6·ψ₀³
      -- Positivity: ψ₀ > 0 from hs₀.Nonempty, ψ_j > 0 from hS_ne.
      have hVol₀_pos : (0 : ℝ) < (G.snapshot t_i).volume s₀ :=
        Nat.cast_pos.mpr ((G.snapshot t_i).volume_pos_of_nonempty hs₀ (fun v => G.degrees_pos v t_i))
      have hVol_j_pos : (0 : ℝ) < (G.snapshot j).volume (vm.S j ω) :=
        Nat.cast_pos.mpr ((G.snapshot j).volume_pos_of_nonempty hS_ne (fun v => G.degrees_pos v j))
      have hψ₀_pos : 0 < ψ₀ := by
        simp only [ψ₀, TemporalGraph.potential]; exact Real.sqrt_pos_of_pos hVol₀_pos
      have hψ_j_pos : 0 < ψ_j := by
        simp only [ψ_j, TemporalGraph.VoterModelAbstract.psiS, TemporalGraph.potential]
        exact Real.sqrt_pos_of_pos hVol_j_pos
      -- 32·ψ_j³ ≤ 24·√6·ψ₀³ via squaring trick
      -- Proof: (32·ψ_j³)² = 1024·(ψ_j²)³ ≤ 1024·(3/2·ψ₀²)³ = 3456·ψ₀⁶
      --        (24·√6·ψ₀³)² = 3456·ψ₀⁶ (exact equality at boundary)
      have h_cube_bound : 32 * ψ_j ^ 3 ≤ 24 * Real.sqrt 6 * ψ₀ ^ 3 := by
        have h_lhs_nn : 0 ≤ 32 * ψ_j ^ 3 := by positivity
        have h_rhs_nn : 0 ≤ 24 * Real.sqrt 6 * ψ₀ ^ 3 := by positivity
        -- Reduce to squared comparison
        calc 32 * ψ_j ^ 3
            = Real.sqrt ((32 * ψ_j ^ 3) ^ 2) := (Real.sqrt_sq h_lhs_nn).symm
          _ ≤ Real.sqrt ((24 * Real.sqrt 6 * ψ₀ ^ 3) ^ 2) := by
              apply Real.sqrt_le_sqrt
              have h_lhs : (32 * ψ_j ^ 3) ^ 2 = 1024 * (ψ_j ^ 2) ^ 3 := by ring
              have hsq6 : Real.sqrt 6 ^ 2 = 6 :=
                Real.sq_sqrt (by norm_num : (6 : ℝ) ≥ 0)
              have h_rhs : (24 * Real.sqrt 6 * ψ₀ ^ 3) ^ 2 = 3456 * ψ₀ ^ 6 := by
                have e : (24 * Real.sqrt 6 * ψ₀ ^ 3) ^ 2 = 24 ^ 2 * Real.sqrt 6 ^ 2 * (ψ₀ ^ 3) ^ 2 := by
                  ring
                rw [e, hsq6]; ring
              rw [h_lhs, h_rhs]
              have h_cube : (ψ_j ^ 2) ^ 3 ≤ (3 / 2 * ψ₀ ^ 2) ^ 3 :=
                pow_le_pow_left₀ (by positivity) hψ_sq_le 3
              calc 1024 * (ψ_j ^ 2) ^ 3 ≤ 1024 * (3 / 2 * ψ₀ ^ 2) ^ 3 :=
                    mul_le_mul_of_nonneg_left h_cube (by norm_num)
                _ = 3456 * ψ₀ ^ 6 := by ring
          _ = 24 * Real.sqrt 6 * ψ₀ ^ 3 := Real.sqrt_sq h_rhs_nn
      -- Chain: E[psiS(j+1)|F_j] - ψ_j ≤ -d_min/32 * c_j / ψ_j³ ≤ coeff' * c_j
      have h32_pos : 0 < 32 * ψ_j ^ 3 := by positivity
      have h24_pos : 0 < 24 * Real.sqrt 6 * ψ₀ ^ 3 := by positivity
      have h_div_bound : d_min * c_j / (24 * Real.sqrt 6 * ψ₀ ^ 3)
          ≤ d_min * c_j / (32 * ψ_j ^ 3) :=
        div_le_div_of_nonneg_left (mul_nonneg hd_nn hc_nn) h32_pos h_cube_bound
      have h_ax_sub : ((vm.μ : Measure _)[fun ω' => vm.psiS (j + 1) ω' | vm.ℱ j]) ω - ψ_j
          ≤ -(d_min / 32 * c_j / ψ_j ^ 3) := by linarith
      have h_neg_rw : -(d_min / 32 * c_j / ψ_j ^ 3) =
          -(d_min * c_j / (32 * ψ_j ^ 3)) := by ring
      have h_coeff_rw : coeff' * c_j =
          -(d_min * c_j / (24 * Real.sqrt 6 * ψ₀ ^ 3)) := by
        simp only [coeff']
        ring
      rw [h_coeff_rw]
      linarith [h_neg_rw, h_div_bound]
    -- Step 2: Telescope via tower property.
    -- Given h_onestep, the tower property gives:
    --   E[psiS(T_next) - ψ₀ | ℱ_{t_i}]
    --   = Σ_{j=t_i}^{T_next-1} E[psiS(j+1) - psiS(j) | ℱ_{t_i}]   (tower + telescope)
    --   ≤ Σ_{j=t_i}^{T_next-1} E[coeff' · cutS(j) | ℱ_{t_i}]       (h_onestep + tower)
    --   = coeff' · E[Σ_{j∈Icc t_i (T_next-1)} cutS(j) | ℱ_{t_i}].  (linearity of E)
    haveI : SigmaFiniteFiltration vm.μ vm.ℱ := inferInstance
    -- Define indicator: ind j ω = 1 if j < T_next ω, else 0
    let ind : ℕ → Ω → ℝ := fun j ω => if j < T_next ω then 1 else 0
    -- Define the one-step difference
    let δ : ℕ → Ω → ℝ := fun j ω => vm.psiS (j + 1) ω - vm.psiS j ω
    -- Integrability of psiS j
    have hpsiS_int : ∀ j, Integrable (fun ω => vm.psiS j ω) vm.μ := by
      intro j
      exact (voter_integrable_comp_A vm
        (fun s' => G.potential j (minoritySet G.toTemporalGraph j s')) j).congr
        (Filter.Eventually.of_forall fun ω' => by
          simp [TemporalGraph.VoterModelAbstract.psiS, TemporalGraph.VoterModelAbstract.S])
    -- Integrability of δ j
    have hδ_int : ∀ j, Integrable (δ j) vm.μ := fun j =>
      (hpsiS_int (j + 1)).sub (hpsiS_int j)
    -- Measurability of {j < T_next} w.r.t. ℱ j (from stopping time)
    have hind_meas_set : ∀ j, MeasurableSet[vm.ℱ j] {ω | j < T_next ω} := by
      intro j
      -- {j < T_next ω} = {¬(T_next ω ≤ j)} = {(T_next ω : ℕ∞) ≤ j}ᶜ
      have hset : {ω | j < T_next ω} = {ω | (T_next ω : ℕ∞) ≤ ↑j}ᶜ := by
        ext ω; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le,
          ENat.coe_lt_coe]
      rw [hset]; exact (hT_stop j).compl
    -- StronglyMeasurable of ind j w.r.t. ℱ j
    have hind_sm : ∀ j, StronglyMeasurable[vm.ℱ j] (ind j) :=
      fun j => StronglyMeasurable.ite (hind_meas_set j)
        stronglyMeasurable_one stronglyMeasurable_zero
    -- Integrability of ind j * δ j
    have hind_δ_int : ∀ j, Integrable (fun ω => ind j ω * δ j ω) vm.μ := by
      intro j
      have heq : (fun ω => ind j ω * δ j ω) =
          Set.indicator {ω | j < T_next ω} (δ j) := by
        funext ω; simp only [ind, Set.indicator, Set.mem_setOf_eq]
        split <;> simp
      rw [heq]
      exact (hδ_int j).indicator (vm.ℱ.le j _ (hind_meas_set j))
    -- Integrability of cutS j (ℕ-valued, finite)
    have hcutS_int : ∀ j, Integrable (fun ω => (vm.cutS j ω : ℝ)) vm.μ := by
      intro j
      have heq : (fun ω => (vm.cutS j ω : ℝ)) =
          (fun s' => (G.edgesBetween j (minoritySet G.toTemporalGraph j s')
            (univ \ minoritySet G.toTemporalGraph j s') : ℝ)) ∘ (vm.opinionZeroSet j) := by
        funext ω'
        simp [TemporalGraph.VoterModelAbstract.cutS, TemporalGraph.VoterModelAbstract.S]
      rw [heq]
      exact voter_integrable_comp_A vm
        (fun s' => (G.edgesBetween j (minoritySet G.toTemporalGraph j s') (univ \ minoritySet G.toTemporalGraph j s') : ℝ)) j
    -- Telescoping identity: for ω with t_i ≤ T_next ω,
    -- psiS(T_next ω, ω) - psiS(t_i, ω)
    --   = Σ_{j ∈ Ico t_i t'} ind(j,ω) * δ(j,ω)
    have htelescope_pw : ∀ ω, t_i ≤ T_next ω →
        vm.psiS (T_next ω) ω - vm.psiS t_i ω =
        ∑ j ∈ Ico t_i t', ind j ω * δ j ω := by
      intro ω hge
      -- ind j ω = 1 for j < T_next ω, 0 otherwise
      -- So Σ_{Ico t_i t'} ind*δ = Σ_{Ico t_i (T_next ω)} δ
      --   = psiS(T_next ω) - psiS(t_i)  (telescope)
      have hle := hT_next_le ω
      rw [← Finset.sum_Ico_consecutive _ hge hle]
      have htail : ∑ j ∈ Ico (T_next ω) t', ind j ω * δ j ω = 0 := by
        apply Finset.sum_eq_zero; intro j hj
        rw [Finset.mem_Ico] at hj
        simp only [ind, if_neg (by omega : ¬ j < T_next ω), zero_mul]
      rw [htail, add_zero]
      have hhead : ∑ j ∈ Ico t_i (T_next ω), ind j ω * δ j ω =
          ∑ j ∈ Ico t_i (T_next ω), δ j ω := by
        apply Finset.sum_congr rfl; intro j hj
        rw [Finset.mem_Ico] at hj
        simp only [ind, if_pos hj.2, one_mul]
      rw [hhead]
      -- Telescope: Σ_{Ico t_i (T_next ω)} (psiS(j+1) - psiS(j)) = psiS(T_next ω) - psiS(t_i)
      simp only [δ]
      have : ∀ a b, a ≤ b →
          ∑ j ∈ Ico a b, (vm.psiS (j + 1) ω - vm.psiS j ω) =
          vm.psiS b ω - vm.psiS a ω := by
        intro a b hab
        induction b with
        | zero => simp [Nat.le_zero.mp hab]
        | succ n ih =>
          rcases Nat.eq_or_lt_of_le hab with rfl | hlt
          · simp
          · rw [Finset.sum_Ico_succ_top (by omega : a ≤ n), ih (by omega)]
            ring
      exact (this t_i (T_next ω) hge).symm
    -- Also need: Σ_{Ico t_i t'} ind(j,ω) * cutS(j,ω)
    --   = Σ_{j ∈ Icc t_i (T_next ω - 1)} cutS(j, ω)
    -- when t_i ≤ T_next ω ≤ t'
    have hcut_sum_eq : ∀ ω, t_i ≤ T_next ω → 0 < T_next ω →
        ∑ j ∈ Ico t_i t', ind j ω * (vm.cutS j ω : ℝ) =
        ∑ j ∈ Icc t_i (T_next ω - 1), (vm.cutS j ω : ℝ) := by
      intro ω hge hpos
      have hle := hT_next_le ω
      rw [← Finset.sum_Ico_consecutive _ hge hle]
      have htail : ∑ j ∈ Ico (T_next ω) t', ind j ω * (vm.cutS j ω : ℝ) = 0 := by
        apply Finset.sum_eq_zero; intro j hj
        rw [Finset.mem_Ico] at hj
        simp only [ind, if_neg (by omega : ¬ j < T_next ω), zero_mul]
      rw [htail, add_zero]
      have hhead : ∑ j ∈ Ico t_i (T_next ω), ind j ω * (vm.cutS j ω : ℝ) =
          ∑ j ∈ Ico t_i (T_next ω), (vm.cutS j ω : ℝ) := by
        apply Finset.sum_congr rfl; intro j hj
        rw [Finset.mem_Ico] at hj
        simp only [ind, if_pos hj.2, one_mul]
      rw [hhead]
      -- Ico t_i (T_next ω) = Icc t_i (T_next ω - 1) when T_next ω > 0
      have hnotmin : ¬ IsMin (T_next ω) :=
        fun hmin => absurd (hmin (Nat.zero_le (T_next ω))) (by omega)
      rw [← Finset.Icc_sub_one_right_eq_Ico_of_not_isMin hnotmin]
    -- Step A: For each j ∈ Ico t_i t',
    -- E[ind j * δ j | ℱ t_i] ≤ coeff' * E[ind j * cutS j | ℱ t_i]  a.s.
    have hterm_bound : ∀ j, j ∈ Ico t_i t' → ∀ᵐ ω ∂(vm.μ : Measure _),
        ((vm.μ : Measure _)[fun ω' => ind j ω' * δ j ω' | vm.ℱ t_i]) ω ≤
        coeff' * ((vm.μ : Measure _)[fun ω' => ind j ω' * (vm.cutS j ω' : ℝ) | vm.ℱ t_i]) ω := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      obtain ⟨hj_ge, _⟩ := hj
      -- Tower: E[ind*δ | ℱ t_i] = E[E[ind*δ | ℱ j] | ℱ t_i]
      have htower_δ : (vm.μ : Measure _)[fun ω => ind j ω * δ j ω | vm.ℱ t_i] =ᵐ[(vm.μ : Measure _)]
          (vm.μ : Measure _)[(vm.μ : Measure _)[fun ω => ind j ω * δ j ω | vm.ℱ j] | vm.ℱ t_i] :=
        (condExp_condExp_of_le (vm.ℱ.mono hj_ge) (vm.ℱ.le j)).symm
      -- Pull-out: E[ind j * δ j | ℱ j] = ind j * E[δ j | ℱ j]
      have hpullout_δ : (vm.μ : Measure _)[fun ω => ind j ω * δ j ω | vm.ℱ j] =ᵐ[(vm.μ : Measure _)]
          fun ω => ind j ω * ((vm.μ : Measure _)[δ j | vm.ℱ j]) ω :=
        condExp_stronglyMeasurable_mul_of_bound (vm.ℱ.le j) (hind_sm j) (hδ_int j) 1
          (Filter.Eventually.of_forall fun ω => by simp [ind]; split <;> norm_num)
      -- h_onestep at j: E[δ j | ℱ j] ≤ coeff' * cutS j on {j < T_next}
      -- Pull-out for cutS: E[ind j * cutS j | ℱ j] = ind j * cutS j
      --   since cutS j is ℱ j-measurable
      have hcutS_sm : StronglyMeasurable[vm.ℱ j]
          (fun ω => (vm.cutS j ω : ℝ)) := by
        have : (fun ω => (vm.cutS j ω : ℝ)) =
            (fun s' => (G.edgesBetween j (minoritySet G.toTemporalGraph j s')
              (univ \ minoritySet G.toTemporalGraph j s') : ℝ)) ∘ (vm.opinionZeroSet j) := by
          funext ω
          simp [TemporalGraph.VoterModelAbstract.cutS, TemporalGraph.VoterModelAbstract.S]
        rw [this]
        have hAj_meas : @Measurable Ω (Finset V) (vm.ℱ j) ⊤ (vm.opinionZeroSet j) :=
          (vm.A_stronglyAdapted j).measurable
        exact ((measurable_of_finite _).comp hAj_meas).stronglyMeasurable
      -- ind j * cutS j is ℱ j-measurable
      have hind_cutS_sm : StronglyMeasurable[vm.ℱ j]
          (fun ω => ind j ω * (vm.cutS j ω : ℝ)) :=
        (hind_sm j).mul hcutS_sm
      -- ind j * cutS j is integrable
      have hind_cutS_int : Integrable (fun ω => ind j ω * (vm.cutS j ω : ℝ)) vm.μ := by
        have heq : (fun ω => ind j ω * (vm.cutS j ω : ℝ)) =
            Set.indicator {ω | j < T_next ω} (fun ω => (vm.cutS j ω : ℝ)) := by
          funext ω; simp only [ind, Set.indicator, Set.mem_setOf_eq]; split <;> simp
        rw [heq]; exact (hcutS_int j).indicator (vm.ℱ.le j _ (hind_meas_set j))
      -- E[ind j * cutS j | ℱ j] = ind j * cutS j (ℱ j-measurable)
      have hcondExp_cutS : (vm.μ : Measure _)[fun ω => ind j ω * (vm.cutS j ω : ℝ) | vm.ℱ j] =ᵐ[(vm.μ : Measure _)]
          fun ω => ind j ω * (vm.cutS j ω : ℝ) :=
        (condExp_of_stronglyMeasurable (vm.ℱ.le j) hind_cutS_sm hind_cutS_int).eventuallyEq
      -- Tower for cutS: E[ind*cutS | ℱ t_i] = E[E[ind*cutS | ℱ j] | ℱ t_i]
      --   = E[ind*cutS | ℱ t_i] (this is trivially true)
      -- Actually use: E[ind*cutS | ℱ t_i] = E[ind*cutS | ℱ t_i]  (just identity)
      -- What we need: ind j * E[δ j | ℱ j] ≤ coeff' * ind j * cutS j a.s.
      have hpw_bound : ∀ᵐ ω ∂(vm.μ : Measure _),
          ind j ω * ((vm.μ : Measure _)[δ j | vm.ℱ j]) ω ≤
          coeff' * (ind j ω * (vm.cutS j ω : ℝ)) := by
        filter_upwards [h_onestep j] with ω honestep_ω
        by_cases hlt : j < T_next ω
        · -- On {j < T_next}: ind = 1, use h_onestep
          simp only [ind, if_pos hlt, one_mul]
          have h := honestep_ω (by omega : t_i ≤ j) hlt
          linarith
        · -- On {j ≥ T_next}: ind = 0, both sides are 0
          simp only [ind, if_neg hlt, zero_mul, mul_zero, le_refl]
      -- Now chain: E[ind*δ | ℱ t_i]
      --   =ᵃᵉ E[E[ind*δ | ℱ j] | ℱ t_i]   (tower)
      --   =ᵃᵉ E[ind * E[δ | ℱ j] | ℱ t_i]  (pull-out)
      --   ≤ᵃᵉ E[coeff' * ind * cutS | ℱ t_i] (monotonicity + hpw_bound)
      --   = coeff' * E[ind * cutS | ℱ t_i]   (pull-out constant)
      -- Step 1: E[ind*δ | ℱ t_i] =ᵃᵉ E[ind * E[δ | ℱ j] | ℱ t_i]
      have h1 : (vm.μ : Measure _)[fun ω => ind j ω * δ j ω | vm.ℱ t_i] =ᵐ[(vm.μ : Measure _)]
          (vm.μ : Measure _)[fun ω => ind j ω * ((vm.μ : Measure _)[δ j | vm.ℱ j]) ω | vm.ℱ t_i] := by
        exact htower_δ.trans (condExp_congr_ae hpullout_δ)
      -- Step 2: ind * E[δ | ℱ j] ≤ coeff' * ind * cutS a.s.
      -- So E[ind * E[δ | ℱ j] | ℱ t_i] ≤ E[coeff' * ind * cutS | ℱ t_i] a.s.
      have h2 : (vm.μ : Measure _)[fun ω => ind j ω * ((vm.μ : Measure _)[δ j | vm.ℱ j]) ω | vm.ℱ t_i] ≤ᵐ[(vm.μ : Measure _)]
          (vm.μ : Measure _)[fun ω => coeff' * (ind j ω * (vm.cutS j ω : ℝ)) | vm.ℱ t_i] := by
        apply condExp_mono
        · -- Integrability of ind * condExp(δ|ℱ j)
          exact integrable_condExp.congr hpullout_δ
        · exact hind_cutS_int.const_mul coeff'
        · exact hpw_bound
      -- Step 3: E[coeff' * ind * cutS | ℱ t_i] = coeff' * E[ind * cutS | ℱ t_i]
      have h3 : (vm.μ : Measure _)[fun ω => coeff' * (ind j ω * (vm.cutS j ω : ℝ)) | vm.ℱ t_i] =ᵐ[(vm.μ : Measure _)]
          fun ω => coeff' * ((vm.μ : Measure _)[fun ω' => ind j ω' * (vm.cutS j ω' : ℝ) | vm.ℱ t_i]) ω := by
        have : (fun ω => coeff' * (ind j ω * (vm.cutS j ω : ℝ))) =
            fun ω => coeff' • (fun ω' => ind j ω' * (vm.cutS j ω' : ℝ)) ω := by
          funext ω; simp [smul_eq_mul]
        rw [this]
        refine (condExp_smul coeff' _ (vm.ℱ t_i)).trans ?_
        exact Filter.EventuallyEq.of_eq (funext fun ω => by simp [Pi.smul_apply, smul_eq_mul])
      -- Combine
      filter_upwards [h1, h2, h3] with ω h1ω h2ω h3ω
      linarith
    -- Step B: Combine per-term bounds into a bound on the sum.
    -- E[Σ ind*δ | ℱ t_i] ≤ coeff' * E[Σ ind*cutS | ℱ t_i]
    -- Convert function sums
    have hfun_δ : (fun ω => ∑ j ∈ Ico t_i t', ind j ω * δ j ω) =
        ∑ j ∈ Ico t_i t', fun ω => ind j ω * δ j ω := by
      funext ω; simp [Finset.sum_apply]
    have hfun_cutS : (fun ω => ∑ j ∈ Ico t_i t', ind j ω * (vm.cutS j ω : ℝ)) =
        ∑ j ∈ Ico t_i t', fun ω => ind j ω * (vm.cutS j ω : ℝ) := by
      funext ω; simp [Finset.sum_apply]
    -- Integrability of ind * cutS j
    have hind_cutS_int' : ∀ j, Integrable (fun ω => ind j ω * (vm.cutS j ω : ℝ)) vm.μ := by
      intro j
      by_cases hj : j ∈ Ico t_i t'
      · have heq : (fun ω => ind j ω * (vm.cutS j ω : ℝ)) =
            Set.indicator {ω | j < T_next ω} (fun ω => (vm.cutS j ω : ℝ)) := by
          funext ω; simp only [ind, Set.indicator, Set.mem_setOf_eq]; split <;> simp
        rw [heq]
        exact (hcutS_int j).indicator (vm.ℱ.le j _ (hind_meas_set j))
      · -- For j outside Ico, ind could be anything, but we can still bound
        have heq : (fun ω => ind j ω * (vm.cutS j ω : ℝ)) =
            Set.indicator {ω | j < T_next ω} (fun ω => (vm.cutS j ω : ℝ)) := by
          funext ω; simp only [ind, Set.indicator, Set.mem_setOf_eq]; split <;> simp
        rw [heq]
        exact (hcutS_int j).indicator (vm.ℱ.le j _ (hind_meas_set j))
    -- Sum condExp splitting
    have hcondExp_sum_δ :
        (vm.μ : Measure _)[fun ω => ∑ j ∈ Ico t_i t', ind j ω * δ j ω | vm.ℱ t_i] =ᵐ[(vm.μ : Measure _)]
        ∑ j ∈ Ico t_i t', (vm.μ : Measure _)[fun ω => ind j ω * δ j ω | vm.ℱ t_i] := by
      rw [hfun_δ]
      exact condExp_finsetSum (fun j _ => hind_δ_int j) (vm.ℱ t_i)
    have hcondExp_sum_cutS :
        (vm.μ : Measure _)[fun ω => ∑ j ∈ Ico t_i t', ind j ω * (vm.cutS j ω : ℝ) | vm.ℱ t_i] =ᵐ[(vm.μ : Measure _)]
        ∑ j ∈ Ico t_i t', (vm.μ : Measure _)[fun ω => ind j ω * (vm.cutS j ω : ℝ) | vm.ℱ t_i] := by
      rw [hfun_cutS]
      exact condExp_finsetSum (fun j _ => hind_cutS_int' j) (vm.ℱ t_i)
    -- Combine: Σ E[ind*δ | ℱ t_i] ≤ coeff' * Σ E[ind*cutS | ℱ t_i]
    have hsum_bound : ∀ᵐ ω ∂(vm.μ : Measure _),
        (∑ j ∈ Ico t_i t', ((vm.μ : Measure _)[fun ω' => ind j ω' * δ j ω' | vm.ℱ t_i]) ω) ≤
        coeff' * (∑ j ∈ Ico t_i t',
          ((vm.μ : Measure _)[fun ω' => ind j ω' * (vm.cutS j ω' : ℝ) | vm.ℱ t_i]) ω) := by
      have : ∀ j ∈ Ico t_i t', ∀ᵐ ω ∂(vm.μ : Measure _),
          ((vm.μ : Measure _)[fun ω' => ind j ω' * δ j ω' | vm.ℱ t_i]) ω ≤
          coeff' * ((vm.μ : Measure _)[fun ω' => ind j ω' * (vm.cutS j ω' : ℝ) | vm.ℱ t_i]) ω :=
        hterm_bound
      rw [← Filter.eventually_all_finset] at this
      filter_upwards [this] with ω hω
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun j hj => hω j hj
    -- Step C: Connect telescope to condExp.
    -- psiS(T_next) - psiS(t_i) =ᵃᵉ Σ ind*δ (by htelescope_pw)
    -- So E[psiS(T_next) - psiS(t_i) | ℱ t_i] =ᵃᵉ E[Σ ind*δ | ℱ t_i]
    have hpsiS_ti_sm : StronglyMeasurable[vm.ℱ t_i] (fun ω => vm.psiS t_i ω) := by
      have : (fun ω => vm.psiS t_i ω) =
          (fun s' => G.potential t_i (minoritySet G.toTemporalGraph t_i s')) ∘ (vm.opinionZeroSet t_i) := by
        funext ω; simp [TemporalGraph.VoterModelAbstract.psiS, TemporalGraph.VoterModelAbstract.S]
      rw [this]
      have hA_meas : @Measurable Ω (Finset V) (vm.ℱ t_i) ⊤ (vm.opinionZeroSet t_i) :=
        (vm.A_stronglyAdapted t_i).measurable
      exact ((measurable_of_finite _).comp hA_meas).stronglyMeasurable
    -- Measurability of {T_next = k} w.r.t. the ambient σ-algebra
    have hTnext_eq_meas : ∀ k, MeasurableSet {ω | T_next ω = k} := by
      intro k
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · -- {T_next = 0} = {(T_next : ℕ∞) ≤ 0}
        have : {ω | T_next ω = 0} = {ω | (T_next ω : ℕ∞) ≤ ↑0} := by
          ext ω; simp
        rw [this]; exact vm.ℱ.le 0 _ (hT_stop 0)
      · -- {T_next = k} = {(T_next : ℕ∞) ≤ k} \ {(T_next : ℕ∞) ≤ k-1}
        have : {ω | T_next ω = k} = {ω | (T_next ω : ℕ∞) ≤ ↑k} \
            {ω | (T_next ω : ℕ∞) ≤ ↑(k - 1)} := by
          ext ω; simp only [Set.mem_setOf_eq, Set.mem_sdiff, ENat.coe_le_coe]
          omega
        rw [this]
        exact (vm.ℱ.le k _ (hT_stop k)).diff (vm.ℱ.le (k - 1) _ (hT_stop (k - 1)))
    -- Integrability of psiS(T_next ·, ·)
    have hpsiS_Tnext_int : Integrable (fun ω => vm.psiS (T_next ω) ω) vm.μ := by
      have heq : (fun ω => vm.psiS (T_next ω) ω) = fun ω =>
          ∑ k ∈ range (t' + 1),
            Set.indicator {ω | T_next ω = k} (fun ω => vm.psiS k ω) ω := by
        funext ω
        rw [Finset.sum_eq_single (T_next ω)]
        · simp [Set.indicator]
        · intro k _ hk; simp [Set.indicator, Ne.symm hk]
        · intro h
          exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le (hT_next_le ω))) h
      rw [heq]; exact integrable_finsetSum _ fun k _ =>
        (hpsiS_int k).indicator (hTnext_eq_meas k)
    -- Integrability of the difference psiS(T_next) - ψ₀
    have hpsiS_diff_int : Integrable
        (fun ω => vm.psiS (T_next ω) ω - G.potential t_i s₀) vm.μ :=
      hpsiS_Tnext_int.sub (integrable_const _)
    -- Integrability of psiS(T_next) - psiS(t_i)
    have hpsiS_diff_ti_int : Integrable
        (fun ω => vm.psiS (T_next ω) ω - vm.psiS t_i ω) vm.μ :=
      hpsiS_Tnext_int.sub (hpsiS_int t_i)
    -- Integrability of the Ico sum of ind*δ
    have hsum_ind_δ_int : Integrable
        (fun ω => ∑ j ∈ Ico t_i t', ind j ω * δ j ω) vm.μ :=
      integrable_finsetSum _ fun j _ => hind_δ_int j
    -- ae equality: psiS(T_next) - psiS(t_i) =ᵃᵉ Σ ind*δ
    have hae_tele : ∀ᵐ ω ∂(vm.μ : Measure _),
        vm.psiS (T_next ω) ω - vm.psiS t_i ω =
        ∑ j ∈ Ico t_i t', ind j ω * δ j ω := by
      filter_upwards [hT_next_ge] with ω hω
      exact htelescope_pw ω hω
    -- condExp of psiS(T_next) - psiS(t_i) =ᵃᵉ condExp of Σ ind*δ
    have hcondExp_tele : (vm.μ : Measure _)[fun ω => vm.psiS (T_next ω) ω - vm.psiS t_i ω | vm.ℱ t_i]
        =ᵐ[(vm.μ : Measure _)] (vm.μ : Measure _)[fun ω => ∑ j ∈ Ico t_i t', ind j ω * δ j ω | vm.ℱ t_i] :=
      condExp_congr_ae hae_tele
    -- Split condExp: E[psiS(T_next) - psiS(t_i) | ℱ t_i]
    --   = E[psiS(T_next) | ℱ t_i] - psiS(t_i)
    have hcondExp_split_ti :
        (vm.μ : Measure _)[fun ω => vm.psiS (T_next ω) ω - vm.psiS t_i ω | vm.ℱ t_i] =ᵐ[(vm.μ : Measure _)]
        (vm.μ : Measure _)[fun ω => vm.psiS (T_next ω) ω | vm.ℱ t_i] -
          fun ω => vm.psiS t_i ω := by
      have h1 := condExp_sub hpsiS_Tnext_int (hpsiS_int t_i) (vm.ℱ t_i)
      have h2 := condExp_of_stronglyMeasurable (vm.ℱ.le t_i) hpsiS_ti_sm (hpsiS_int t_i)
      rw [h2] at h1; exact h1
    -- Similarly for ψ₀:
    -- E[psiS(T_next) - ψ₀ | ℱ t_i] = E[psiS(T_next) | ℱ t_i] - ψ₀
    have hcondExp_split_ψ₀ :
        (vm.μ : Measure _)[fun ω => vm.psiS (T_next ω) ω -
          G.potential t_i s₀ | vm.ℱ t_i] =ᵐ[(vm.μ : Measure _)]
        (vm.μ : Measure _)[fun ω => vm.psiS (T_next ω) ω | vm.ℱ t_i] -
          fun _ => G.potential t_i s₀ := by
      have h1 := condExp_sub hpsiS_Tnext_int
        (integrable_const (G.potential t_i s₀)) (vm.ℱ t_i)
      rw [condExp_const (vm.ℱ.le t_i)] at h1; exact h1
    -- ae equality: Σ ind*cutS =ᵃᵉ Σ_{Icc t_i (T_next-1)} cutS
    have hae_cut : ∀ᵐ ω ∂(vm.μ : Measure _),
        ∑ j ∈ Ico t_i t', ind j ω * (vm.cutS j ω : ℝ) =
        ∑ j ∈ Icc t_i (T_next ω - 1), (vm.cutS j ω : ℝ) := by
      filter_upwards [hT_next_ge, hT_next_pos] with ω hω hpos
      exact hcut_sum_eq ω hω hpos
    -- condExp of Σ ind*cutS =ᵃᵉ condExp of Σ_{Icc} cutS
    have hcondExp_cut : (vm.μ : Measure _)[fun ω =>
          ∑ j ∈ Ico t_i t', ind j ω * (vm.cutS j ω : ℝ) | vm.ℱ t_i] =ᵐ[(vm.μ : Measure _)]
        (vm.μ : Measure _)[fun ω => ∑ j ∈ Icc t_i (T_next ω - 1),
          (vm.cutS j ω : ℝ) | vm.ℱ t_i] :=
      condExp_congr_ae hae_cut
    -- Now combine everything.
    -- Goal: E[psiS(T_next) - ψ₀ | ℱ t_i] ≤ coeff' * E[Σ_{Icc} cutS | ℱ t_i]
    -- Chain:
    --   E[psiS(T_next) - ψ₀ | ℱ t_i](ω)
    --   = E[psiS(T_next) | ℱ t_i](ω) - ψ₀           (hcondExp_split_ψ₀)
    --   = E[psiS(T_next) - psiS(t_i) | ℱ t_i](ω) + psiS(t_i,ω) - ψ₀  (hcondExp_split_ti)
    --   ≤ E[psiS(T_next) - psiS(t_i) | ℱ t_i](ω)    (since psiS(t_i) ≤ ψ₀ by hpsi_init)
    --   = E[Σ ind*δ | ℱ t_i](ω)                       (hcondExp_tele)
    --   = Σ E[ind*δ | ℱ t_i](ω)                       (hcondExp_sum_δ)
    --   ≤ coeff' * Σ E[ind*cutS | ℱ t_i](ω)           (hsum_bound)
    --   = coeff' * E[Σ ind*cutS | ℱ t_i](ω)           (hcondExp_sum_cutS)
    --   = coeff' * E[Σ_{Icc} cutS | ℱ t_i](ω)         (hcondExp_cut)
    filter_upwards [hcondExp_split_ψ₀, hcondExp_split_ti, hpsi_init,
        hcondExp_tele, hcondExp_sum_δ, hsum_bound, hcondExp_sum_cutS,
        hcondExp_cut] with ω
        hψ₀_split hti_split hpsi_le htele hsum_δ hbound hsum_cutS hcut_eq
    simp only [Pi.sub_apply] at hψ₀_split hti_split
    -- Rearrange: from hψ₀_split and hti_split
    -- hψ₀_split: E[psiS(T_next) - ψ₀ | ℱ t_i](ω) = E[psiS(T_next)|ℱ t_i](ω) - ψ₀
    -- hti_split: E[psiS(T_next) - psiS(t_i)|ℱ t_i](ω) = E[psiS(T_next)|ℱ t_i](ω) - psiS(t_i,ω)
    -- So E[psiS(T_next) - ψ₀ | ℱ t_i](ω)
    --   = E[psiS(T_next) - psiS(t_i) | ℱ t_i](ω) + (psiS(t_i,ω) - ψ₀)
    have h_relate : ((vm.μ : Measure _)[fun ω' => vm.psiS (T_next ω') ω' -
        G.potential t_i s₀ | vm.ℱ t_i]) ω =
        ((vm.μ : Measure _)[fun ω' => vm.psiS (T_next ω') ω' - vm.psiS t_i ω' | vm.ℱ t_i]) ω +
        (vm.psiS t_i ω - G.potential t_i s₀) := by linarith
    rw [h_relate]
    -- E[psiS(T_next) - psiS(t_i) | ℱ t_i](ω) ≤ coeff' * E[Σ cutS | ℱ t_i](ω)
    -- via htele, hsum_δ, hbound, hsum_cutS, hcut_eq
    have h_tele_bound : ((vm.μ : Measure _)[fun ω' => vm.psiS (T_next ω') ω' -
        vm.psiS t_i ω' | vm.ℱ t_i]) ω ≤
        coeff' * ((vm.μ : Measure _)[fun ω' => ∑ j ∈ Icc t_i (T_next ω' - 1),
          (vm.cutS j ω' : ℝ) | vm.ℱ t_i]) ω := by
      have hsum_δ' : ((vm.μ : Measure _)[fun ω' => ∑ j ∈ Ico t_i t',
            ind j ω' * δ j ω' | vm.ℱ t_i]) ω =
          ∑ j ∈ Ico t_i t',
            ((vm.μ : Measure _)[fun ω' => ind j ω' * δ j ω' | vm.ℱ t_i]) ω := by
        rw [show (∑ j ∈ Ico t_i t',
              ((vm.μ : Measure _)[fun ω' => ind j ω' * δ j ω' | vm.ℱ t_i]) ω) =
            (∑ j ∈ Ico t_i t',
              (vm.μ : Measure _)[fun ω' => ind j ω' * δ j ω' | vm.ℱ t_i]) ω
          from (Finset.sum_apply ω (Ico t_i t') _).symm]
        exact hsum_δ
      have hsum_cutS' : coeff' * (∑ j ∈ Ico t_i t',
            ((vm.μ : Measure _)[fun ω' => ind j ω' * (vm.cutS j ω' : ℝ) | vm.ℱ t_i]) ω) =
          coeff' * ((vm.μ : Measure _)[fun ω' => ∑ j ∈ Ico t_i t',
            ind j ω' * (vm.cutS j ω' : ℝ) | vm.ℱ t_i]) ω := by
        congr 1
        rw [show (∑ j ∈ Ico t_i t',
              ((vm.μ : Measure _)[fun ω' => ind j ω' * (vm.cutS j ω' : ℝ) | vm.ℱ t_i]) ω) =
            (∑ j ∈ Ico t_i t',
              (vm.μ : Measure _)[fun ω' => ind j ω' * (vm.cutS j ω' : ℝ) | vm.ℱ t_i]) ω
          from (Finset.sum_apply ω (Ico t_i t') _).symm]
        exact hsum_cutS.symm
      calc ((vm.μ : Measure _)[fun ω' => vm.psiS (T_next ω') ω' - vm.psiS t_i ω' | vm.ℱ t_i]) ω
          = ((vm.μ : Measure _)[fun ω' => ∑ j ∈ Ico t_i t', ind j ω' * δ j ω' | vm.ℱ t_i]) ω := htele
        _ = ∑ j ∈ Ico t_i t',
              ((vm.μ : Measure _)[fun ω' => ind j ω' * δ j ω' | vm.ℱ t_i]) ω := hsum_δ'
        _ ≤ coeff' * ∑ j ∈ Ico t_i t',
              ((vm.μ : Measure _)[fun ω' => ind j ω' * (vm.cutS j ω' : ℝ) | vm.ℱ t_i]) ω := hbound
        _ = coeff' * ((vm.μ : Measure _)[fun ω' => ∑ j ∈ Ico t_i t',
              ind j ω' * (vm.cutS j ω' : ℝ) | vm.ℱ t_i]) ω := hsum_cutS'
        _ = coeff' * ((vm.μ : Measure _)[fun ω' => ∑ j ∈ Icc t_i (T_next ω' - 1),
              (vm.cutS j ω' : ℝ) | vm.ℱ t_i]) ω := by rw [hcut_eq]
    -- psiS(t_i, ω) - ψ₀ ≤ 0 (from hpsi_le)
    have h_init_le : vm.psiS t_i ω - G.potential t_i s₀ ≤ 0 := by linarith
    -- coeff' * E[Σ cutS | ℱ t_i](ω) ≤ 0
    -- (coeff' ≤ 0 and Σ cutS ≥ 0, so condExp ≥ 0)
    linarith
  -- Combine telescope with edge sum bound
  have h_combine : ∀ᵐ ω ∂(vm.μ : Measure _),
      ((vm.μ : Measure _)[fun ω' => vm.psiS (T_next ω') ω'
        - G.potential t_i s₀ | vm.ℱ t_i]) ω
        ≤ -((μ_param * (G.minDegreeAt 0 : ℝ)) / (24 * Real.sqrt 6 * Δ
          * G.potential t_i s₀)) := by
    -- Combine h_telescope (E[change] ≤ -C · E[sum]) with
    -- hedge_sum_large (E[sum] > μ·Vol/Δ) to get E[change] ≤ -C·μ·Vol/Δ.
    -- Since C = d_min/(24√6·ψ³) > 0 and -C < 0, larger E[sum] gives more negative bound.
    filter_upwards [h_telescope, hedge_sum_large] with ω h_tel h_sum
    -- h_tel : E[ψ change](ω) ≤ -(d_min/(24√6·ψ³)) · E[sum](ω)
    -- h_sum : E[sum](ω) > μ·Vol/Δ
    -- Need: E[ψ change](ω) ≤ -(μ·d_min/(24√6·Δ·ψ))
    -- Step 1: Since the coefficient is ≤ 0 and sum > μ*Vol/Δ, we get the bound.
    set sum_val := ((vm.μ : Measure _)[fun ω' => ∑ j ∈ Finset.Icc t_i (T_next ω' - 1),
        (vm.cutS j ω' : ℝ) | vm.ℱ t_i]) ω
    set M := μ_param * ((G.snapshot t_i).volume s₀ : ℝ) / Δ
    set coeff := -(G.minDegreeAt 0 : ℝ) / (24 * Real.sqrt 6 *
      G.potential t_i s₀ ^ 3)
    -- coeff ≤ 0
    have hcoeff : coeff ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg (G.minDegreeAt 0)))
      apply mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 24) (Real.sqrt_nonneg _))
      exact pow_nonneg (Real.sqrt_nonneg _) 3
    -- h_tel already in terms of coeff * sum_val
    -- sum_val > M
    have h_sum' : M ≤ sum_val := le_of_lt h_sum
    -- coeff * sum_val ≤ coeff * M (since coeff ≤ 0, flip direction)
    have h_step : coeff * sum_val ≤ coeff * M :=
      mul_le_mul_of_nonpos_left h_sum' hcoeff
    -- Now connect: coeff * M = target
    have h_eq : coeff * M = -((μ_param * (G.minDegreeAt 0 : ℝ)) / (24 * Real.sqrt 6 * Δ
        * G.potential t_i s₀)) := by
      -- ψ = √Vol, so ψ³ = Vol^{3/2} and Vol/ψ³ = 1/ψ
      simp only [TemporalGraph.potential]
      have hVol : 0 ≤ ((G.snapshot t_i).volume s₀ : ℝ) := Nat.cast_nonneg _
      -- √Vol ^ 3 = √Vol * Vol (since √Vol ^ 2 = Vol)
      set sv := Real.sqrt ((G.snapshot t_i).volume s₀ : ℝ)
      have hsq : sv ^ 2 = ((G.snapshot t_i).volume s₀ : ℝ) := Real.sq_sqrt hVol
      -- sv ^ 3 = sv * sv ^ 2 = sv * Vol
      have hcube : sv ^ 3 = sv * ((G.snapshot t_i).volume s₀ : ℝ) := by
        rw [show sv ^ 3 = sv * sv ^ 2 from by ring, hsq]
      -- coeff * M = -(d_min) / (24 * √6 * sv³) * (μ * Vol / Δ)
      -- = -(μ * d_min * Vol) / (24 * √6 * sv * Vol * Δ)
      -- = -(μ * d_min) / (24 * √6 * sv * Δ)
      -- = target
      by_cases hsv0 : sv = 0
      · -- If sv = 0 then Vol = 0, so M = 0 and target involves division by 0.
        have hVol_eq : ((G.snapshot t_i).volume s₀ : ℝ) = 0 := by
          rw [← hsq, hsv0]; ring
        have hM0 : M = 0 := by
          change μ_param * ((G.snapshot t_i).volume s₀ : ℝ) / Δ = 0
          rw [hVol_eq]; ring
        rw [hM0, mul_zero]
        -- RHS: -(μ * d_min / (24 * √6 * Δ * sv))
        -- sv = 0 so denominator = 0, division by 0 = 0, neg 0 = 0
        simp [hsv0]
      have hsv_pos : 0 < sv := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hsv0)
      have hVol_pos : (0 : ℝ) < ((G.snapshot t_i).volume s₀ : ℝ) := by
        rw [← hsq]; positivity
      -- coeff = -(d_min) / (24 * √6 * sv³) and M = μ * Vol / Δ
      -- coeff * M = -(d_min * μ * Vol) / (24 * √6 * sv³ * Δ)
      -- sv³ = sv * Vol (from hcube), so:
      -- = -(d_min * μ * Vol) / (24 * √6 * sv * Vol * Δ)
      -- = -(d_min * μ) / (24 * √6 * sv * Δ)        (cancel Vol ≠ 0)
      -- = -(μ * d_min / (24 * √6 * Δ * sv))         (rearrange)
      have hVol_ne : ((G.snapshot t_i).volume s₀ : ℝ) ≠ 0 := ne_of_gt hVol_pos
      -- Use hcube to simplify sv³
      show coeff * M = _
      -- coeff = -(d_min) / (24 * √6 * (sv * Vol))    [using hcube for sv^3]
      -- M = μ * Vol / Δ
      -- Product: -(d_min) * μ * Vol / (24 * √6 * sv * Vol * Δ)
      -- = -(μ * d_min) / (24 * √6 * Δ * sv)
      have hsv_ne : sv ≠ 0 := ne_of_gt hsv_pos
      have hsqrt6_ne : Real.sqrt 6 ≠ 0 := ne_of_gt (Real.sqrt_pos_of_pos (by norm_num))
      have hΔ_ne : Δ ≠ 0 := ne_of_gt hΔ_pos
      -- Rewrite Vol in terms of sv: Vol = sv^2
      have hVol_sv : ((G.snapshot t_i).volume s₀ : ℝ) = sv ^ 2 := hsq.symm
      -- Unfold set definitions and compute
      change -(↑(G.minDegreeAt 0)) / (24 * Real.sqrt 6 *
        sv ^ 3) * (μ_param * ((G.snapshot t_i).volume s₀ : ℝ) / Δ)
        = -(μ_param * ↑(G.minDegreeAt 0) / (24 * Real.sqrt 6 * Δ * sv))
      rw [hVol_sv]
      field_simp
    linarith
  exact h_combine

/-- (Fiber-relative variant; Lean-only sub-task L81 enabling L79.)

Fiber-relative version of `potential_decrease_stable_interval_large`. Same setup as the
parent except the global pointwise stability hypotheses `hstable_vol`, `hS_nonempty` are
restricted to a measurable fiber `F ∈ ℱ_{t_i}`, and the a.e. hypotheses `hT_next_ge`,
`hT_next_pos`, `hpsi_init`, `hedge_sum_large` are a.e. on `μ.restrict F`. The conclusion
is the corresponding a.e. bound on `μ.restrict F`.

**Proof strategy.** Mirrors the parent proof verbatim, with the global indicator
`ind j ω := if j < T_next ω then 1 else 0` replaced by
`ind' j ω := 1_F(ω) · (if j < T_next ω then 1 else 0)`. Since `F ∈ ℱ_{t_i} ⊆ ℱ_j`
for `j ≥ t_i`, `ind'` remains `ℱ_j`-strongly-measurable. The key pointwise inequality
`ind' · E[δ|ℱ_j] ≤ coeff' · ind' · cutS` then holds **globally a.e.** (vacuously off F),
so `condExp_mono` applies. The final conclusion is restricted to `μ.restrict F` via
`ae_restrict_of_ae` on the global a.e. result times `1_F`. -/
theorem potential_decrease_stable_interval_large_on_fiber
    {Ω : Type*} [MeasurableSpace Ω]
    (G : TemporalGraphFixedDegree V)
    (vm : G.VoterModelAbstract 2 Ω)
    -- Fixed initial set s₀ ≠ ∅ and time t_i
    (s₀ : Finset V) (hs₀ : s₀.Nonempty)
    (t_i : ℕ)
    -- Stopping times T_{i+1}
    (T_next : Ω → ℕ)
    -- T_next is a stopping time
    (hT_stop : IsStoppingTime vm.ℱ (fun ω => (T_next ω : ℕ∞)))
    -- Deterministic bound on T_next
    (t' : ℕ) (hT_next_le : ∀ ω, T_next ω ≤ t')
    -- Fiber F: measurable in ℱ_{t_i}
    (F : Set Ω) (hF_meas : MeasurableSet[vm.ℱ t_i] F)
    -- T_next ≥ t_i a.s. on F
    (hT_next_ge : ∀ᵐ ω ∂((vm.μ : Measure _).restrict F), t_i ≤ T_next ω)
    -- T_next > 0 a.s. on F
    (hT_next_pos : ∀ᵐ ω ∂((vm.μ : Measure _).restrict F), 0 < T_next ω)
    -- psiS(t_i) ≤ ψ₀ a.s. on F
    (hpsi_init : ∀ᵐ ω ∂((vm.μ : Measure _).restrict F),
      vm.psiS t_i ω ≤ G.potential t_i s₀)
    -- Interval length (t* − t_i)
    (Δ : ℝ) (hΔ_pos : 0 < Δ)
    -- Stability on F: Vol(S_j) ≤ (3/2)·Vol(s₀) throughout [t_i, T_next), for ω ∈ F
    (hstable_vol : ∀ ω ∈ F, ∀ j, t_i ≤ j → j < T_next ω →
      ((G.snapshot j).volume (vm.S j ω) : ℝ) ≤
        3 / 2 * ((G.snapshot t_i).volume s₀ : ℝ))
    -- S_j nonempty on F throughout [t_i, T_next)
    (hS_nonempty : ∀ ω ∈ F, ∀ j, t_i ≤ j → j < T_next ω →
      (vm.S j ω).Nonempty)
    -- Large edge sum: E[Σ e_j(S_j, S̄_j)] > μ · Vol(s₀) / Δ, a.s. on F
    (μ_param : ℝ)
    (hedge_sum_large : ∀ᵐ ω ∂((vm.μ : Measure _).restrict F),
      ((vm.μ : Measure _)[fun ω' => ∑ j ∈ Finset.Icc t_i (T_next ω' - 1),
        (vm.cutS j ω' : ℝ) | vm.ℱ t_i]) ω
        > μ_param * ((G.snapshot t_i).volume s₀ : ℝ) / Δ) :
    -- Conclusion: a.e. on μ.restrict F,
    --   E[ψ(S_{T_{i+1}}) − ψ(s₀) | ℱ_{t_i}] ≤ −μ·d_min / (24√6·Δ·ψ(s₀))
    ∀ᵐ ω ∂((vm.μ : Measure _).restrict F),
      ((vm.μ : Measure _)[fun ω' => vm.psiS (T_next ω') ω'
        - G.potential t_i s₀ | vm.ℱ t_i]) ω
        ≤ -((μ_param * (G.minDegreeAt 0 : ℝ)) / (24 * Real.sqrt 6 * Δ
          * G.potential t_i s₀)) := by
  classical
  -- Strategy: mirror the parent body, with the indicator `ind j ω` replaced by
  -- `indF j ω := (if ω ∈ F then 1 else 0) * (if j < T_next ω then 1 else 0)`.
  -- `F ∈ ℱ_{t_i} ⊆ ℱ_j` for `j ≥ t_i`, so `indF` is `ℱ_j`-strongly-measurable.
  set coeff' := -(G.minDegreeAt 0 : ℝ) /
      (24 * Real.sqrt 6 * G.potential t_i s₀ ^ 3) with hcoeff'_def
  have hF_meas_top : MeasurableSet F := vm.ℱ.le t_i _ hF_meas
  -- Indicator scalar 1_F
  let indF_scalar : Ω → ℝ := fun ω => if ω ∈ F then 1 else 0
  -- F is in ℱ_j for any j ≥ t_i (filtration monotone)
  have hF_in_Fj : ∀ j, t_i ≤ j → MeasurableSet[vm.ℱ j] F := by
    intro j hj; exact vm.ℱ.mono hj _ hF_meas
  -- Combined indicator: 1_F(ω) * 1_{j < T_next ω}
  let indF : ℕ → Ω → ℝ := fun j ω =>
    (if ω ∈ F then 1 else 0) * (if j < T_next ω then 1 else 0)
  -- One-step difference δ j ω = ψ(j+1, ω) − ψ(j, ω)
  let δ : ℕ → Ω → ℝ := fun j ω => vm.psiS (j + 1) ω - vm.psiS j ω
  -- Integrability of psiS j
  have hpsiS_int : ∀ j, Integrable (fun ω => vm.psiS j ω) vm.μ := by
    intro j
    exact (voter_integrable_comp_A vm
      (fun s' => G.potential j (minoritySet G.toTemporalGraph j s')) j).congr
      (Filter.Eventually.of_forall fun ω' => by
        simp [TemporalGraph.VoterModelAbstract.psiS, TemporalGraph.VoterModelAbstract.S])
  have hδ_int : ∀ j, Integrable (δ j) vm.μ := fun j =>
    (hpsiS_int (j + 1)).sub (hpsiS_int j)
  -- Measurability of {j < T_next} w.r.t. ℱ j
  have hind_meas_set : ∀ j, MeasurableSet[vm.ℱ j] {ω | j < T_next ω} := by
    intro j
    have hset : {ω | j < T_next ω} = {ω | (T_next ω : ℕ∞) ≤ ↑j}ᶜ := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le,
        ENat.coe_lt_coe]
    rw [hset]; exact (hT_stop j).compl
  -- StronglyMeasurable of indF j w.r.t. ℱ j (when t_i ≤ j)
  have hindF_sm : ∀ j, t_i ≤ j → StronglyMeasurable[vm.ℱ j] (indF j) := by
    intro j hj
    refine StronglyMeasurable.mul ?_ ?_
    · exact StronglyMeasurable.ite (hF_in_Fj j hj)
        stronglyMeasurable_one stronglyMeasurable_zero
    · exact StronglyMeasurable.ite (hind_meas_set j)
        stronglyMeasurable_one stronglyMeasurable_zero
  -- StronglyMeasurable of indF j w.r.t. the ambient σ-algebra always
  have hindF_sm_top : ∀ j, StronglyMeasurable (indF j) := by
    intro j
    refine StronglyMeasurable.mul ?_ ?_
    · exact StronglyMeasurable.ite hF_meas_top
        stronglyMeasurable_one stronglyMeasurable_zero
    · exact StronglyMeasurable.ite (vm.ℱ.le j _ (hind_meas_set j))
        stronglyMeasurable_one stronglyMeasurable_zero
  -- Bound: |indF j ω| ≤ 1 globally
  have hindF_bound : ∀ j, ∀ω, ‖indF j ω‖ ≤ (1 : ℝ) := by
    intro j ω
    simp only [indF, Real.norm_eq_abs]
    split_ifs <;> simp
  -- Integrability of indF j * δ j: bounded by |δ j|
  have hindF_δ_int : ∀ j, Integrable (fun ω => indF j ω * δ j ω) vm.μ := by
    intro j
    refine Integrable.bdd_mul (c := 1) (hδ_int j) (hindF_sm_top j).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun ω => by
      simpa [Real.norm_eq_abs] using hindF_bound j ω
  -- Integrability of cutS j (ℕ-valued)
  have hcutS_int : ∀ j, Integrable (fun ω => (vm.cutS j ω : ℝ)) vm.μ := by
    intro j
    have heq : (fun ω => (vm.cutS j ω : ℝ)) =
        (fun s' => (G.edgesBetween j (minoritySet G.toTemporalGraph j s')
          (univ \ minoritySet G.toTemporalGraph j s') : ℝ)) ∘ (vm.opinionZeroSet j) := by
      funext ω'
      simp [TemporalGraph.VoterModelAbstract.cutS, TemporalGraph.VoterModelAbstract.S]
    rw [heq]
    exact voter_integrable_comp_A vm
      (fun s' => (G.edgesBetween j (minoritySet G.toTemporalGraph j s')
        (univ \ minoritySet G.toTemporalGraph j s') : ℝ)) j
  -- One-step bound a.e. on F (mirrors parent's h_onestep, with F-restricted hypotheses):
  -- For j ∈ [t_i, T_next ω) and ω ∈ F a.e.:
  --   E[psiS(j+1) - psiS(j) | ℱ_j](ω) ≤ coeff' * (cutS j ω : ℝ)
  have h_onestep : ∀ j, ∀ᵐ ω ∂(vm.μ : Measure _), ω ∈ F → t_i ≤ j → j < T_next ω →
      ((vm.μ : Measure _)[fun ω' => vm.psiS (j + 1) ω' - vm.psiS j ω' | vm.ℱ j]) ω
        ≤ coeff' * (vm.cutS j ω : ℝ) := by
    intro j
    let f_succ : Finset V → ℝ :=
      fun s' => G.potential (j + 1) (minoritySet G.toTemporalGraph (j + 1) s')
    have hpsi_eq : ∀ ω', vm.psiS (j + 1) ω' = f_succ (vm.opinionZeroSet (j + 1) ω') :=
      fun ω' => show G.potential (j + 1) (vm.S (j + 1) ω') =
          G.potential (j + 1) (minoritySet G.toTemporalGraph (j + 1) (vm.opinionZeroSet (j + 1) ω'))
        from by simp [TemporalGraph.VoterModelAbstract.S]
    have hpsi1_int : Integrable (fun ω' => vm.psiS (j + 1) ω') vm.μ :=
      (voter_integrable_comp_A vm f_succ (j + 1)).congr
        (Filter.Eventually.of_forall fun ω' => (hpsi_eq ω').symm)
    have hpsi_j_int : Integrable (fun ω' => vm.psiS j ω') vm.μ := hpsiS_int j
    have hAj_Fmeas : @Measurable Ω (Finset V) (vm.ℱ j) ⊤ (vm.opinionZeroSet j) :=
      (vm.A_stronglyAdapted j).measurable
    have hpsi_j_sm : StronglyMeasurable[vm.ℱ j] (fun ω' => vm.psiS j ω') := by
      have hfact : (fun ω' => vm.psiS j ω') =
          (fun s' => G.potential j (minoritySet G.toTemporalGraph j s')) ∘ (vm.opinionZeroSet j) := by
        funext ω'
        simp [TemporalGraph.VoterModelAbstract.psiS, TemporalGraph.VoterModelAbstract.S]
      rw [hfact]
      exact ((measurable_of_finite _).comp hAj_Fmeas).stronglyMeasurable
    have hcE_split : (vm.μ : Measure _)[fun ω' => vm.psiS (j + 1) ω' - vm.psiS j ω' | vm.ℱ j]
        =ᵐ[(vm.μ : Measure _)]
        (vm.μ : Measure _)[fun ω' => vm.psiS (j + 1) ω' | vm.ℱ j] - fun ω' => vm.psiS j ω' := by
      have h1 := condExp_sub hpsi1_int hpsi_j_int (vm.ℱ j)
      have h2 := condExp_of_stronglyMeasurable (vm.ℱ.le j) hpsi_j_sm hpsi_j_int
      rw [h2] at h1
      exact h1
    filter_upwards [hcE_split, potential_decrease_one_step G vm j] with ω h_split h_pdos
    intro hωF hj_ge hj_lt
    rw [h_split]; simp only [Pi.sub_apply]
    have hS_ne : (vm.S j ω).Nonempty := hS_nonempty ω hωF j hj_ge hj_lt
    have h_ax := h_pdos hS_ne.ne_empty
    set ψ₀ := G.potential t_i s₀
    set ψ_j := vm.psiS j ω
    set c_j := (vm.cutS j ω : ℝ)
    set d_min := (G.minDegreeAt 0 : ℝ)
    have hstab := hstable_vol ω hωF j hj_ge hj_lt
    have hψ_j_sq : ψ_j ^ 2 = ((G.snapshot j).volume (vm.S j ω) : ℝ) := by
      simp only [ψ_j, TemporalGraph.VoterModelAbstract.psiS, TemporalGraph.potential]
      exact Real.sq_sqrt (Nat.cast_nonneg _)
    have hψ₀_sq : ψ₀ ^ 2 = ((G.snapshot t_i).volume s₀ : ℝ) := by
      simp only [ψ₀, TemporalGraph.potential]
      exact Real.sq_sqrt (Nat.cast_nonneg _)
    have hψ_sq_le : ψ_j ^ 2 ≤ 3 / 2 * ψ₀ ^ 2 := by rw [hψ_j_sq, hψ₀_sq]; exact hstab
    have hψ_j_nn : 0 ≤ ψ_j := Real.sqrt_nonneg _
    have hψ₀_nn : 0 ≤ ψ₀ := Real.sqrt_nonneg _
    have hc_nn : 0 ≤ c_j := Nat.cast_nonneg _
    have hd_nn : 0 ≤ d_min := Nat.cast_nonneg _
    have hVol₀_pos : (0 : ℝ) < (G.snapshot t_i).volume s₀ :=
      Nat.cast_pos.mpr ((G.snapshot t_i).volume_pos_of_nonempty hs₀ (fun v => G.degrees_pos v t_i))
    have hVol_j_pos : (0 : ℝ) < (G.snapshot j).volume (vm.S j ω) :=
      Nat.cast_pos.mpr ((G.snapshot j).volume_pos_of_nonempty hS_ne (fun v => G.degrees_pos v j))
    have hψ₀_pos : 0 < ψ₀ := by
      simp only [ψ₀, TemporalGraph.potential]; exact Real.sqrt_pos_of_pos hVol₀_pos
    have hψ_j_pos : 0 < ψ_j := by
      simp only [ψ_j, TemporalGraph.VoterModelAbstract.psiS, TemporalGraph.potential]
      exact Real.sqrt_pos_of_pos hVol_j_pos
    have h_cube_bound : 32 * ψ_j ^ 3 ≤ 24 * Real.sqrt 6 * ψ₀ ^ 3 := by
      have h_lhs_nn : 0 ≤ 32 * ψ_j ^ 3 := by positivity
      have h_rhs_nn : 0 ≤ 24 * Real.sqrt 6 * ψ₀ ^ 3 := by positivity
      calc 32 * ψ_j ^ 3
          = Real.sqrt ((32 * ψ_j ^ 3) ^ 2) := (Real.sqrt_sq h_lhs_nn).symm
        _ ≤ Real.sqrt ((24 * Real.sqrt 6 * ψ₀ ^ 3) ^ 2) := by
            apply Real.sqrt_le_sqrt
            have h_lhs : (32 * ψ_j ^ 3) ^ 2 = 1024 * (ψ_j ^ 2) ^ 3 := by ring
            have hsq6 : Real.sqrt 6 ^ 2 = 6 :=
              Real.sq_sqrt (by norm_num : (6 : ℝ) ≥ 0)
            have h_rhs : (24 * Real.sqrt 6 * ψ₀ ^ 3) ^ 2 = 3456 * ψ₀ ^ 6 := by
              have e : (24 * Real.sqrt 6 * ψ₀ ^ 3) ^ 2 = 24 ^ 2 * Real.sqrt 6 ^ 2 * (ψ₀ ^ 3) ^ 2 := by
                ring
              rw [e, hsq6]; ring
            rw [h_lhs, h_rhs]
            have h_cube : (ψ_j ^ 2) ^ 3 ≤ (3 / 2 * ψ₀ ^ 2) ^ 3 :=
              pow_le_pow_left₀ (by positivity) hψ_sq_le 3
            calc 1024 * (ψ_j ^ 2) ^ 3 ≤ 1024 * (3 / 2 * ψ₀ ^ 2) ^ 3 :=
                  mul_le_mul_of_nonneg_left h_cube (by norm_num)
              _ = 3456 * ψ₀ ^ 6 := by ring
        _ = 24 * Real.sqrt 6 * ψ₀ ^ 3 := Real.sqrt_sq h_rhs_nn
    have h32_pos : 0 < 32 * ψ_j ^ 3 := by positivity
    have h24_pos : 0 < 24 * Real.sqrt 6 * ψ₀ ^ 3 := by positivity
    have h_div_bound : d_min * c_j / (24 * Real.sqrt 6 * ψ₀ ^ 3)
        ≤ d_min * c_j / (32 * ψ_j ^ 3) :=
      div_le_div_of_nonneg_left (mul_nonneg hd_nn hc_nn) h32_pos h_cube_bound
    have h_ax_sub : ((vm.μ : Measure _)[fun ω' => vm.psiS (j + 1) ω' | vm.ℱ j]) ω - ψ_j
        ≤ -(d_min / 32 * c_j / ψ_j ^ 3) := by linarith
    have h_neg_rw : -(d_min / 32 * c_j / ψ_j ^ 3) =
        -(d_min * c_j / (32 * ψ_j ^ 3)) := by ring
    have h_coeff_rw : coeff' * c_j =
        -(d_min * c_j / (24 * Real.sqrt 6 * ψ₀ ^ 3)) := by
      simp only [coeff']
      ring
    rw [h_coeff_rw]
    linarith [h_neg_rw, h_div_bound]
  -- ↑ End h_onestep. Now build the analogue of h_telescope, with `indF` in place of `ind`.
  haveI : SigmaFiniteFiltration vm.μ vm.ℱ := inferInstance
  -- Integrability of indF j * cutS j (bounded indicator * integrable)
  have hindF_cutS_int : ∀ j, Integrable (fun ω => indF j ω * (vm.cutS j ω : ℝ)) vm.μ := by
    intro j
    refine Integrable.bdd_mul (c := 1) (hcutS_int j)
      (hindF_sm_top j).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun ω => by
      simpa [Real.norm_eq_abs] using hindF_bound j ω
  -- Telescoping identity on F: psiS(T_next ω) ω - psiS(t_i, ω) = Σ_{j ∈ Ico t_i t'} indF j ω · δ j ω
  -- when ω ∈ F and t_i ≤ T_next ω
  have htelescope_pw : ∀ ω, ω ∈ F → t_i ≤ T_next ω →
      vm.psiS (T_next ω) ω - vm.psiS t_i ω =
      ∑ j ∈ Ico t_i t', indF j ω * δ j ω := by
    intro ω hωF hge
    have hle := hT_next_le ω
    rw [← Finset.sum_Ico_consecutive _ hge hle]
    -- On F, indF j ω = if j < T_next ω then 1 else 0
    have hindF_on_F : ∀ k, indF k ω = if k < T_next ω then 1 else 0 := by
      intro k
      simp only [indF, if_pos hωF, one_mul]
    have htail : ∑ j ∈ Ico (T_next ω) t', indF j ω * δ j ω = 0 := by
      apply Finset.sum_eq_zero; intro j hj
      rw [Finset.mem_Ico] at hj
      rw [hindF_on_F]
      simp [if_neg (by omega : ¬ j < T_next ω)]
    rw [htail, add_zero]
    have hhead : ∑ j ∈ Ico t_i (T_next ω), indF j ω * δ j ω =
        ∑ j ∈ Ico t_i (T_next ω), δ j ω := by
      apply Finset.sum_congr rfl; intro j hj
      rw [Finset.mem_Ico] at hj
      rw [hindF_on_F]; simp [if_pos hj.2]
    rw [hhead]
    simp only [δ]
    have : ∀ a b, a ≤ b →
        ∑ j ∈ Ico a b, (vm.psiS (j + 1) ω - vm.psiS j ω) =
        vm.psiS b ω - vm.psiS a ω := by
      intro a b hab
      induction b with
      | zero => simp [Nat.le_zero.mp hab]
      | succ n ih =>
        rcases Nat.eq_or_lt_of_le hab with rfl | hlt
        · simp
        · rw [Finset.sum_Ico_succ_top (by omega : a ≤ n), ih (by omega)]
          ring
    exact (this t_i (T_next ω) hge).symm
  -- Cut-sum identity on F: Σ indF * cutS = Σ_{Icc t_i (T_next - 1)} cutS on F when t_i ≤ T_next, T_next > 0
  have hcut_sum_eq : ∀ ω, ω ∈ F → t_i ≤ T_next ω → 0 < T_next ω →
      ∑ j ∈ Ico t_i t', indF j ω * (vm.cutS j ω : ℝ) =
      ∑ j ∈ Icc t_i (T_next ω - 1), (vm.cutS j ω : ℝ) := by
    intro ω hωF hge hpos
    have hle := hT_next_le ω
    rw [← Finset.sum_Ico_consecutive _ hge hle]
    have hindF_on_F : ∀ k, indF k ω = if k < T_next ω then 1 else 0 := by
      intro k
      simp only [indF, if_pos hωF, one_mul]
    have htail : ∑ j ∈ Ico (T_next ω) t', indF j ω * (vm.cutS j ω : ℝ) = 0 := by
      apply Finset.sum_eq_zero; intro j hj
      rw [Finset.mem_Ico] at hj
      rw [hindF_on_F]
      simp [if_neg (by omega : ¬ j < T_next ω)]
    rw [htail, add_zero]
    have hhead : ∑ j ∈ Ico t_i (T_next ω), indF j ω * (vm.cutS j ω : ℝ) =
        ∑ j ∈ Ico t_i (T_next ω), (vm.cutS j ω : ℝ) := by
      apply Finset.sum_congr rfl; intro j hj
      rw [Finset.mem_Ico] at hj
      rw [hindF_on_F]; simp [if_pos hj.2]
    rw [hhead]
    have hnotmin : ¬ IsMin (T_next ω) :=
      fun hmin => absurd (hmin (Nat.zero_le (T_next ω))) (by omega)
    rw [← Finset.Icc_sub_one_right_eq_Ico_of_not_isMin hnotmin]
  -- Step A: per-term bound. For each j ∈ Ico t_i t':
  --   E[indF j * δ j | ℱ t_i] ≤ coeff' * E[indF j * cutS j | ℱ t_i] a.s. globally
  -- This is GLOBAL a.e. because indF = 0 off F (vacuous case).
  have hterm_bound : ∀ j, j ∈ Ico t_i t' → ∀ᵐ ω ∂(vm.μ : Measure _),
      ((vm.μ : Measure _)[fun ω' => indF j ω' * δ j ω' | vm.ℱ t_i]) ω ≤
      coeff' * ((vm.μ : Measure _)[fun ω' => indF j ω' * (vm.cutS j ω' : ℝ) | vm.ℱ t_i]) ω := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    obtain ⟨hj_ge, _⟩ := hj
    -- Tower: E[indF*δ | ℱ t_i] = E[E[indF*δ | ℱ j] | ℱ t_i]
    have htower_δ : (vm.μ : Measure _)[fun ω => indF j ω * δ j ω | vm.ℱ t_i] =ᵐ[(vm.μ : Measure _)]
        (vm.μ : Measure _)[(vm.μ : Measure _)[fun ω => indF j ω * δ j ω | vm.ℱ j] | vm.ℱ t_i] :=
      (condExp_condExp_of_le (vm.ℱ.mono hj_ge) (vm.ℱ.le j)).symm
    -- Pull-out: E[indF j * δ j | ℱ j] = indF j * E[δ j | ℱ j]
    have hpullout_δ : (vm.μ : Measure _)[fun ω => indF j ω * δ j ω | vm.ℱ j] =ᵐ[(vm.μ : Measure _)]
        fun ω => indF j ω * ((vm.μ : Measure _)[δ j | vm.ℱ j]) ω :=
      condExp_stronglyMeasurable_mul_of_bound (vm.ℱ.le j) (hindF_sm j hj_ge) (hδ_int j) 1
        (Filter.Eventually.of_forall fun ω => by
          simpa [Real.norm_eq_abs] using hindF_bound j ω)
    -- cutS j is ℱ j-measurable
    have hcutS_sm : StronglyMeasurable[vm.ℱ j]
        (fun ω => (vm.cutS j ω : ℝ)) := by
      have : (fun ω => (vm.cutS j ω : ℝ)) =
          (fun s' => (G.edgesBetween j (minoritySet G.toTemporalGraph j s')
            (univ \ minoritySet G.toTemporalGraph j s') : ℝ)) ∘ (vm.opinionZeroSet j) := by
        funext ω
        simp [TemporalGraph.VoterModelAbstract.cutS, TemporalGraph.VoterModelAbstract.S]
      rw [this]
      have hAj_meas : @Measurable Ω (Finset V) (vm.ℱ j) ⊤ (vm.opinionZeroSet j) :=
        (vm.A_stronglyAdapted j).measurable
      exact ((measurable_of_finite _).comp hAj_meas).stronglyMeasurable
    have hindF_cutS_sm : StronglyMeasurable[vm.ℱ j]
        (fun ω => indF j ω * (vm.cutS j ω : ℝ)) :=
      (hindF_sm j hj_ge).mul hcutS_sm
    -- Pointwise inequality, GLOBAL a.e.:
    --   indF j ω * E[δ j | ℱ_j](ω) ≤ coeff' * (indF j ω * cutS j ω)
    have hpw_bound : ∀ᵐ ω ∂(vm.μ : Measure _),
        indF j ω * ((vm.μ : Measure _)[δ j | vm.ℱ j]) ω ≤
        coeff' * (indF j ω * (vm.cutS j ω : ℝ)) := by
      filter_upwards [h_onestep j] with ω honestep_ω
      by_cases hωF : ω ∈ F
      · by_cases hlt : j < T_next ω
        · -- On F ∩ {j < T_next}: indF = 1, use h_onestep
          have hindF1 : indF j ω = 1 := by simp [indF, if_pos hωF, if_pos hlt]
          rw [hindF1, one_mul, one_mul]
          have h := honestep_ω hωF (by omega : t_i ≤ j) hlt
          linarith
        · -- On F \ {j < T_next}: indF = 0
          have hindF0 : indF j ω = 0 := by simp [indF, if_neg hlt]
          rw [hindF0]; simp
      · -- Off F: indF = 0
        have hindF0 : indF j ω = 0 := by simp [indF, if_neg hωF]
        rw [hindF0]; simp
    -- E[indF j * cutS j | ℱ j] = indF j * cutS j (ℱ j-measurable)
    have hindF_cutS_condExp : (vm.μ : Measure _)[fun ω => indF j ω * (vm.cutS j ω : ℝ) | vm.ℱ j] =ᵐ[(vm.μ : Measure _)]
        fun ω => indF j ω * (vm.cutS j ω : ℝ) :=
      (condExp_of_stronglyMeasurable (vm.ℱ.le j) hindF_cutS_sm (hindF_cutS_int j)).eventuallyEq
    -- Chain: E[indF*δ | ℱ t_i]
    --   =ᵃᵉ E[E[indF*δ | ℱ j] | ℱ t_i]      (tower)
    --   =ᵃᵉ E[indF * E[δ | ℱ j] | ℱ t_i]     (pull-out)
    --   ≤ᵃᵉ E[coeff' * indF * cutS | ℱ t_i] (mono + hpw_bound)
    --   = coeff' * E[indF * cutS | ℱ t_i]    (pull-out constant)
    have h1 : (vm.μ : Measure _)[fun ω => indF j ω * δ j ω | vm.ℱ t_i] =ᵐ[(vm.μ : Measure _)]
        (vm.μ : Measure _)[fun ω => indF j ω * ((vm.μ : Measure _)[δ j | vm.ℱ j]) ω | vm.ℱ t_i] :=
      htower_δ.trans (condExp_congr_ae hpullout_δ)
    have h2 : (vm.μ : Measure _)[fun ω => indF j ω * ((vm.μ : Measure _)[δ j | vm.ℱ j]) ω | vm.ℱ t_i] ≤ᵐ[(vm.μ : Measure _)]
        (vm.μ : Measure _)[fun ω => coeff' * (indF j ω * (vm.cutS j ω : ℝ)) | vm.ℱ t_i] := by
      apply condExp_mono
      · exact integrable_condExp.congr hpullout_δ
      · exact (hindF_cutS_int j).const_mul coeff'
      · exact hpw_bound
    have h3 : (vm.μ : Measure _)[fun ω => coeff' * (indF j ω * (vm.cutS j ω : ℝ)) | vm.ℱ t_i] =ᵐ[(vm.μ : Measure _)]
        fun ω => coeff' * ((vm.μ : Measure _)[fun ω' => indF j ω' * (vm.cutS j ω' : ℝ) | vm.ℱ t_i]) ω := by
      have : (fun ω => coeff' * (indF j ω * (vm.cutS j ω : ℝ))) =
          fun ω => coeff' • (fun ω' => indF j ω' * (vm.cutS j ω' : ℝ)) ω := by
        funext ω; simp [smul_eq_mul]
      rw [this]
      refine (condExp_smul coeff' _ (vm.ℱ t_i)).trans ?_
      exact Filter.EventuallyEq.of_eq (funext fun ω => by simp [Pi.smul_apply, smul_eq_mul])
    filter_upwards [h1, h2, h3] with ω h1ω h2ω h3ω
    linarith
  -- Step B: Sum the per-term bounds
  have hfun_δ : (fun ω => ∑ j ∈ Ico t_i t', indF j ω * δ j ω) =
      ∑ j ∈ Ico t_i t', fun ω => indF j ω * δ j ω := by
    funext ω; simp [Finset.sum_apply]
  have hfun_cutS : (fun ω => ∑ j ∈ Ico t_i t', indF j ω * (vm.cutS j ω : ℝ)) =
      ∑ j ∈ Ico t_i t', fun ω => indF j ω * (vm.cutS j ω : ℝ) := by
    funext ω; simp [Finset.sum_apply]
  have hcondExp_sum_δ :
      (vm.μ : Measure _)[fun ω => ∑ j ∈ Ico t_i t', indF j ω * δ j ω | vm.ℱ t_i] =ᵐ[(vm.μ : Measure _)]
      ∑ j ∈ Ico t_i t', (vm.μ : Measure _)[fun ω => indF j ω * δ j ω | vm.ℱ t_i] := by
    rw [hfun_δ]
    exact condExp_finsetSum (fun j _ => hindF_δ_int j) (vm.ℱ t_i)
  have hcondExp_sum_cutS :
      (vm.μ : Measure _)[fun ω => ∑ j ∈ Ico t_i t', indF j ω * (vm.cutS j ω : ℝ) | vm.ℱ t_i] =ᵐ[(vm.μ : Measure _)]
      ∑ j ∈ Ico t_i t', (vm.μ : Measure _)[fun ω => indF j ω * (vm.cutS j ω : ℝ) | vm.ℱ t_i] := by
    rw [hfun_cutS]
    exact condExp_finsetSum (fun j _ => hindF_cutS_int j) (vm.ℱ t_i)
  have hsum_bound : ∀ᵐ ω ∂(vm.μ : Measure _),
      (∑ j ∈ Ico t_i t', ((vm.μ : Measure _)[fun ω' => indF j ω' * δ j ω' | vm.ℱ t_i]) ω) ≤
      coeff' * (∑ j ∈ Ico t_i t',
        ((vm.μ : Measure _)[fun ω' => indF j ω' * (vm.cutS j ω' : ℝ) | vm.ℱ t_i]) ω) := by
    have : ∀ j ∈ Ico t_i t', ∀ᵐ ω ∂(vm.μ : Measure _),
        ((vm.μ : Measure _)[fun ω' => indF j ω' * δ j ω' | vm.ℱ t_i]) ω ≤
        coeff' * ((vm.μ : Measure _)[fun ω' => indF j ω' * (vm.cutS j ω' : ℝ) | vm.ℱ t_i]) ω :=
      hterm_bound
    rw [← Filter.eventually_all_finset] at this
    filter_upwards [this] with ω hω
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j hj => hω j hj
  -- Step C: Connect telescope to condExp
  have hpsiS_ti_sm : StronglyMeasurable[vm.ℱ t_i] (fun ω => vm.psiS t_i ω) := by
    have : (fun ω => vm.psiS t_i ω) =
        (fun s' => G.potential t_i (minoritySet G.toTemporalGraph t_i s')) ∘ (vm.opinionZeroSet t_i) := by
      funext ω; simp [TemporalGraph.VoterModelAbstract.psiS, TemporalGraph.VoterModelAbstract.S]
    rw [this]
    have hA_meas : @Measurable Ω (Finset V) (vm.ℱ t_i) ⊤ (vm.opinionZeroSet t_i) :=
      (vm.A_stronglyAdapted t_i).measurable
    exact ((measurable_of_finite _).comp hA_meas).stronglyMeasurable
  have hTnext_eq_meas : ∀ k, MeasurableSet {ω | T_next ω = k} := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have : {ω | T_next ω = 0} = {ω | (T_next ω : ℕ∞) ≤ ↑0} := by
        ext ω; simp
      rw [this]; exact vm.ℱ.le 0 _ (hT_stop 0)
    · have : {ω | T_next ω = k} = {ω | (T_next ω : ℕ∞) ≤ ↑k} \
          {ω | (T_next ω : ℕ∞) ≤ ↑(k - 1)} := by
        ext ω; simp only [Set.mem_setOf_eq, Set.mem_sdiff, ENat.coe_le_coe]
        omega
      rw [this]
      exact (vm.ℱ.le k _ (hT_stop k)).diff (vm.ℱ.le (k - 1) _ (hT_stop (k - 1)))
  have hpsiS_Tnext_int : Integrable (fun ω => vm.psiS (T_next ω) ω) vm.μ := by
    have heq : (fun ω => vm.psiS (T_next ω) ω) = fun ω =>
        ∑ k ∈ range (t' + 1),
          Set.indicator {ω | T_next ω = k} (fun ω => vm.psiS k ω) ω := by
      funext ω
      rw [Finset.sum_eq_single (T_next ω)]
      · simp [Set.indicator]
      · intro k _ hk; simp [Set.indicator, Ne.symm hk]
      · intro h
        exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le (hT_next_le ω))) h
    rw [heq]; exact integrable_finsetSum _ fun k _ =>
      (hpsiS_int k).indicator (hTnext_eq_meas k)
  have hpsiS_diff_int : Integrable
      (fun ω => vm.psiS (T_next ω) ω - G.potential t_i s₀) vm.μ :=
    hpsiS_Tnext_int.sub (integrable_const _)
  have hpsiS_diff_ti_int : Integrable
      (fun ω => vm.psiS (T_next ω) ω - vm.psiS t_i ω) vm.μ :=
    hpsiS_Tnext_int.sub (hpsiS_int t_i)
  have hsum_indF_δ_int : Integrable
      (fun ω => ∑ j ∈ Ico t_i t', indF j ω * δ j ω) vm.μ :=
    integrable_finsetSum _ fun j _ => hindF_δ_int j
  -- The key telescoping equality, expressed as `indF_scalar(ω) · (psiS(T_next) - psiS(t_i)) = Σ indF * δ`
  -- a.e. on `μ.restrict F` (since on F, indF_scalar = 1).
  -- We use `htelescope_pw` directly: holds for ω ∈ F with t_i ≤ T_next ω.
  -- ae equality on restrict F
  have hae_tele_restrict : ∀ᵐ ω ∂((vm.μ : Measure _).restrict F),
      vm.psiS (T_next ω) ω - vm.psiS t_i ω =
      ∑ j ∈ Ico t_i t', indF j ω * δ j ω := by
    rw [ae_restrict_iff' hF_meas_top]
    filter_upwards [(ae_restrict_iff' hF_meas_top).mp hT_next_ge] with ω hωT hωF
    exact htelescope_pw ω hωF (hωT hωF)
  -- Likewise for cut sum
  have hae_cut_restrict : ∀ᵐ ω ∂((vm.μ : Measure _).restrict F),
      ∑ j ∈ Ico t_i t', indF j ω * (vm.cutS j ω : ℝ) =
      ∑ j ∈ Icc t_i (T_next ω - 1), (vm.cutS j ω : ℝ) := by
    rw [ae_restrict_iff' hF_meas_top]
    filter_upwards [(ae_restrict_iff' hF_meas_top).mp hT_next_ge,
      (ae_restrict_iff' hF_meas_top).mp hT_next_pos] with ω hωT hωP hωF
    exact hcut_sum_eq ω hωF (hωT hωF) (hωP hωF)
  -- Split condExp at t_i
  have hcondExp_split_ti :
      (vm.μ : Measure _)[fun ω => vm.psiS (T_next ω) ω - vm.psiS t_i ω | vm.ℱ t_i] =ᵐ[(vm.μ : Measure _)]
      (vm.μ : Measure _)[fun ω => vm.psiS (T_next ω) ω | vm.ℱ t_i] -
        fun ω => vm.psiS t_i ω := by
    have h1 := condExp_sub hpsiS_Tnext_int (hpsiS_int t_i) (vm.ℱ t_i)
    have h2 := condExp_of_stronglyMeasurable (vm.ℱ.le t_i) hpsiS_ti_sm (hpsiS_int t_i)
    rw [h2] at h1; exact h1
  have hcondExp_split_ψ₀ :
      (vm.μ : Measure _)[fun ω => vm.psiS (T_next ω) ω -
        G.potential t_i s₀ | vm.ℱ t_i] =ᵐ[(vm.μ : Measure _)]
      (vm.μ : Measure _)[fun ω => vm.psiS (T_next ω) ω | vm.ℱ t_i] -
        fun _ => G.potential t_i s₀ := by
    have h1 := condExp_sub hpsiS_Tnext_int
      (integrable_const (G.potential t_i s₀)) (vm.ℱ t_i)
    rw [condExp_const (vm.ℱ.le t_i)] at h1; exact h1
  -- Approach: derive the global a.e. inequality
  --   E[Σ indF * δ | ℱ t_i] ≤ coeff' * E[Σ indF * cutS | ℱ t_i]  GLOBAL
  -- using hsum_bound, hcondExp_sum_δ, hcondExp_sum_cutS.
  have h_global_telescope_le : ∀ᵐ ω ∂(vm.μ : Measure _),
      ((vm.μ : Measure _)[fun ω' => ∑ j ∈ Ico t_i t', indF j ω' * δ j ω' | vm.ℱ t_i]) ω ≤
      coeff' * ((vm.μ : Measure _)[fun ω' => ∑ j ∈ Ico t_i t', indF j ω' * (vm.cutS j ω' : ℝ) |
        vm.ℱ t_i]) ω := by
    filter_upwards [hcondExp_sum_δ, hsum_bound, hcondExp_sum_cutS] with ω hSδ hbnd hScS
    have hSδ' : ((vm.μ : Measure _)[fun ω' => ∑ j ∈ Ico t_i t', indF j ω' * δ j ω' | vm.ℱ t_i]) ω =
        ∑ j ∈ Ico t_i t', ((vm.μ : Measure _)[fun ω' => indF j ω' * δ j ω' | vm.ℱ t_i]) ω := by
      rw [show (∑ j ∈ Ico t_i t',
            ((vm.μ : Measure _)[fun ω' => indF j ω' * δ j ω' | vm.ℱ t_i]) ω) =
          (∑ j ∈ Ico t_i t',
            (vm.μ : Measure _)[fun ω' => indF j ω' * δ j ω' | vm.ℱ t_i]) ω
        from (Finset.sum_apply ω (Ico t_i t') _).symm]
      exact hSδ
    have hScS' : ((vm.μ : Measure _)[fun ω' => ∑ j ∈ Ico t_i t', indF j ω' * (vm.cutS j ω' : ℝ) |
          vm.ℱ t_i]) ω =
        ∑ j ∈ Ico t_i t', ((vm.μ : Measure _)[fun ω' =>
          indF j ω' * (vm.cutS j ω' : ℝ) | vm.ℱ t_i]) ω := by
      rw [show (∑ j ∈ Ico t_i t',
            ((vm.μ : Measure _)[fun ω' => indF j ω' * (vm.cutS j ω' : ℝ) | vm.ℱ t_i]) ω) =
          (∑ j ∈ Ico t_i t',
            (vm.μ : Measure _)[fun ω' => indF j ω' * (vm.cutS j ω' : ℝ) | vm.ℱ t_i]) ω
        from (Finset.sum_apply ω (Ico t_i t') _).symm]
      exact hScS
    rw [hSδ', hScS']; exact hbnd
  -- Telescope on restrict F: E[Σ indF * δ | ℱ t_i](ω) = E[ψ(T_next) - ψ(t_i) | ℱ t_i](ω) a.e. on restrict F
  have hcondExp_tele_restrictF :
      ∀ᵐ ω ∂((vm.μ : Measure _).restrict F),
        ((vm.μ : Measure _)[fun ω' => vm.psiS (T_next ω') ω' - vm.psiS t_i ω' | vm.ℱ t_i]) ω =
        ((vm.μ : Measure _)[fun ω' => ∑ j ∈ Ico t_i t', indF j ω' * δ j ω' | vm.ℱ t_i]) ω := by
    -- The two function sources are equal on `μ.restrict F` (by hae_tele_restrict)
    -- So their condExp agree a.e. globally on a `μ.restrict F`-null-complement-style argument.
    -- Use condExp_indicator-like approach: since indF off F is 0, the telescoping sum is
    -- 0 off F, while ψ(T_next) - ψ(t_i) may not be. So they're NOT globally a.e. equal.
    -- Workaround: take `1_F · (LHS)` and `1_F · (RHS)`.
    -- Concretely, on F: indF j ω = 1_{j < T_next ω}, so Σ indF*δ = Σ_{j ∈ Ico t_i (T_next ω)} δ.
    -- And ψ(T_next ω) ω - ψ(t_i, ω) = that telescope (by htelescope_pw).
    -- Off F: indF = 0, so Σ indF*δ = 0; ψ(T_next) - ψ(t_i) may be anything.
    -- KEY OBSERVATION: we need this equality only ON F, not globally.
    -- We're computing E[X | ℱ t_i] for two different X's, but ω is on F.
    -- The conditional expectation of f and g where f =ᵐ g on F (a.e. μ.restrict F)
    -- gives E[f | ℱ t_i] = E[g | ℱ t_i] a.e. on μ.restrict F when F ∈ ℱ t_i.
    -- Proof: E[1_F * (f - g) | ℱ t_i] = 1_F * E[f - g | ℱ t_i] (F ∈ ℱ t_i).
    -- But 1_F · (f - g) = 0 a.e. globally (since f - g = 0 a.e. on F, and indicator is 0 off F).
    -- Hence 1_F · E[f - g | ℱ t_i] = 0 a.e. globally, so E[f - g | ℱ t_i] = 0 a.e. on F.
    -- Make this precise via mul_indicator.
    set f : Ω → ℝ := fun ω => vm.psiS (T_next ω) ω - vm.psiS t_i ω
    set g : Ω → ℝ := fun ω => ∑ j ∈ Ico t_i t', indF j ω * δ j ω
    have hf_int : Integrable f vm.μ := hpsiS_diff_ti_int
    have hg_int : Integrable g vm.μ := hsum_indF_δ_int
    have hsub_int : Integrable (fun ω => f ω - g ω) vm.μ := hf_int.sub hg_int
    -- f = g a.e. on μ.restrict F (by hae_tele_restrict)
    have hfg_restrict : ∀ᵐ ω ∂((vm.μ : Measure _).restrict F), f ω = g ω := hae_tele_restrict
    -- Equivalently: ∀ᵐ ω ∂μ, ω ∈ F → f ω = g ω
    have hfg_global : ∀ᵐ ω ∂(vm.μ : Measure _), ω ∈ F → f ω = g ω :=
      (ae_restrict_iff' hF_meas_top).mp hfg_restrict
    -- E[f | ℱ t_i] - E[g | ℱ t_i] =ᵃᵉ E[f - g | ℱ t_i] (globally)
    have hcondExp_sub : (vm.μ : Measure _)[f | vm.ℱ t_i] - (vm.μ : Measure _)[g | vm.ℱ t_i] =ᵐ[(vm.μ : Measure _)]
        (vm.μ : Measure _)[fun ω => f ω - g ω | vm.ℱ t_i] := (condExp_sub hf_int hg_int (vm.ℱ t_i)).symm
    -- 1_F * (f - g) = 0 a.e. globally (since (f-g) = 0 on F a.e.)
    have h1F_fg_zero_ae : ∀ᵐ ω ∂(vm.μ : Measure _),
        (Set.indicator F (fun ω => f ω - g ω) ω) = 0 := by
      filter_upwards [hfg_global] with ω hω
      by_cases hωF : ω ∈ F
      · simp [Set.indicator_of_mem hωF, hω hωF]
      · simp [Set.indicator_of_notMem hωF]
    -- E[1_F * (f - g) | ℱ t_i] = 1_F * E[f - g | ℱ t_i]  (F ∈ ℱ t_i)
    have h1F_pullout : (vm.μ : Measure _)[Set.indicator F (fun ω => f ω - g ω) | vm.ℱ t_i] =ᵐ[(vm.μ : Measure _)]
        Set.indicator F ((vm.μ : Measure _)[fun ω => f ω - g ω | vm.ℱ t_i]) :=
      condExp_indicator hsub_int hF_meas
    -- E[1_F * (f - g) | ℱ t_i] =ᵐ 0 (since 1_F * (f - g) = 0 a.e.)
    have hcondExp_indFsub_zero : (vm.μ : Measure _)[Set.indicator F (fun ω => f ω - g ω) | vm.ℱ t_i]
        =ᵐ[(vm.μ : Measure _)] (0 : Ω → ℝ) := by
      have hcong := condExp_congr_ae (μ := (vm.μ : Measure Ω)) (m := vm.ℱ t_i)
        (f := Set.indicator F (fun ω => f ω - g ω))
        (g := 0) h1F_fg_zero_ae
      exact hcong.trans (Filter.EventuallyEq.of_eq condExp_zero)
    -- Combine: 1_F · E[f - g | ℱ t_i] = 0 a.e.
    have h_indc_fg_zero : ∀ᵐ ω ∂(vm.μ : Measure _),
        Set.indicator F ((vm.μ : Measure _)[fun ω => f ω - g ω | vm.ℱ t_i]) ω = 0 := by
      filter_upwards [h1F_pullout, hcondExp_indFsub_zero] with ω hpo hzero
      rw [← hpo, hzero]; rfl
    -- On F: E[f - g | ℱ t_i] = 0 a.e. on restrict F
    have h_fg_zero_restrict : ∀ᵐ ω ∂((vm.μ : Measure _).restrict F),
        ((vm.μ : Measure _)[fun ω => f ω - g ω | vm.ℱ t_i]) ω = 0 := by
      rw [ae_restrict_iff' hF_meas_top]
      filter_upwards [h_indc_fg_zero] with ω hω hωF
      rwa [Set.indicator_of_mem hωF] at hω
    -- Convert to E[f | ℱ t_i] = E[g | ℱ t_i] on restrict F
    have h_fg_eq_restrict : ∀ᵐ ω ∂((vm.μ : Measure _).restrict F),
        ((vm.μ : Measure _)[f | vm.ℱ t_i]) ω = ((vm.μ : Measure _)[g | vm.ℱ t_i]) ω := by
      have hsub_restrict := ae_restrict_of_ae (μ := (vm.μ : Measure Ω)) (s := F) hcondExp_sub
      filter_upwards [h_fg_zero_restrict, hsub_restrict] with ω hzero hsub
      have : ((vm.μ : Measure _)[f | vm.ℱ t_i]) ω - ((vm.μ : Measure _)[g | vm.ℱ t_i]) ω = 0 := by
        have hsub' : (((vm.μ : Measure _)[f | vm.ℱ t_i]) - ((vm.μ : Measure _)[g | vm.ℱ t_i])) ω = _ := hsub
        simp only [Pi.sub_apply] at hsub'
        rw [hsub']; exact hzero
      linarith
    exact h_fg_eq_restrict
  -- Now we similarly want: E[Σ indF * cutS | ℱ t_i](ω) = E[Σ_{Icc t_i (T_next-1)} cutS | ℱ t_i](ω) a.e. on restrict F.
  have hsum_indF_cutS_int : Integrable
      (fun ω => ∑ j ∈ Ico t_i t', indF j ω * (vm.cutS j ω : ℝ)) vm.μ :=
    integrable_finsetSum _ fun j _ => hindF_cutS_int j
  -- For this, we need the corresponding "indicator-of-cut-sum" integrability
  -- Integrability of the (T_next ω)-dependent Icc sum: rewrite as indicator sum over Icc t_i t'
  -- (which subsumes Icc t_i (T_next ω - 1) ⊆ Icc t_i t' since T_next ω - 1 ≤ t').
  have hcutS_Icc_subset : ∀ ω, Icc t_i (T_next ω - 1) ⊆ Icc t_i t' := by
    intro ω j hj
    rw [Finset.mem_Icc] at hj ⊢
    refine ⟨hj.1, ?_⟩
    have := hT_next_le ω
    omega
  have hsum_cutS_Icc_int : Integrable
      (fun ω => ∑ j ∈ Icc t_i (T_next ω - 1), (vm.cutS j ω : ℝ)) vm.μ := by
    -- Rewrite as ∑_{j ∈ Icc t_i t'} (if j ≤ T_next ω - 1 then cutS else 0)
    have heq : (fun ω => ∑ j ∈ Icc t_i (T_next ω - 1), (vm.cutS j ω : ℝ)) =
        fun ω => ∑ j ∈ Icc t_i t',
          (if j ∈ Icc t_i (T_next ω - 1) then (vm.cutS j ω : ℝ) else 0) := by
      funext ω
      rw [← Finset.sum_filter]
      apply Finset.sum_congr ?_ (fun _ _ => rfl)
      ext j
      simp only [Finset.mem_filter]
      refine ⟨fun hj => ⟨hcutS_Icc_subset ω hj, hj⟩, fun ⟨_, hj⟩ => hj⟩
    rw [heq]
    refine integrable_finsetSum _ fun j _ => ?_
    -- For each j, (if j ∈ Icc t_i (T_next ω - 1) then cutS j ω else 0)
    -- = Set.indicator {ω | j ∈ Icc t_i (T_next ω - 1)} (cutS j) ω
    -- The set {ω | j ∈ Icc t_i (T_next ω - 1)} = {ω | t_i ≤ j ∧ j + 1 ≤ T_next ω} = {ω | t_i ≤ j} ∩ {ω | j < T_next ω}.
    have hset_meas : MeasurableSet {ω | j ∈ Icc t_i (T_next ω - 1)} := by
      -- The set decomposes as union over T_next ω = k.
      have hset_eq : {ω | j ∈ Icc t_i (T_next ω - 1)} =
          ⋃ k ∈ Finset.range (t' + 1),
            ({ω | T_next ω = k} ∩ {ω | j ∈ Icc t_i (k - 1)}) := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff,
          Finset.mem_range]
        refine ⟨fun hjω => ⟨T_next ω, Nat.lt_succ_of_le (hT_next_le ω), rfl, hjω⟩,
          fun ⟨k, _, hk_eq, hjk⟩ => ?_⟩
        rw [hk_eq]; exact hjk
      rw [hset_eq]
      refine Finset.measurableSet_biUnion _ fun k _ => ?_
      by_cases hjk : j ∈ Icc t_i (k - 1)
      · have : {ω | T_next ω = k} ∩ {ω | j ∈ Icc t_i (k - 1)} = {ω | T_next ω = k} := by
          ext ω
          simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
          tauto
        rw [this]; exact hTnext_eq_meas k
      · have : {ω | T_next ω = k} ∩ {ω | j ∈ Icc t_i (k - 1)} = ∅ := by
          ext ω
          simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false,
            iff_false, not_and]
          intro _ h2; exact hjk h2
        rw [this]; exact MeasurableSet.empty
    have hind_eq : (fun ω => if j ∈ Icc t_i (T_next ω - 1) then (vm.cutS j ω : ℝ) else 0) =
        Set.indicator {ω | j ∈ Icc t_i (T_next ω - 1)} (fun ω => (vm.cutS j ω : ℝ)) := by
      funext ω; simp only [Set.indicator, Set.mem_setOf_eq]
    rw [hind_eq]
    exact (hcutS_int j).indicator hset_meas
  have hcondExp_cut_restrictF :
      ∀ᵐ ω ∂((vm.μ : Measure _).restrict F),
        ((vm.μ : Measure _)[fun ω' => ∑ j ∈ Ico t_i t', indF j ω' * (vm.cutS j ω' : ℝ) | vm.ℱ t_i]) ω =
        ((vm.μ : Measure _)[fun ω' => ∑ j ∈ Icc t_i (T_next ω' - 1),
          (vm.cutS j ω' : ℝ) | vm.ℱ t_i]) ω := by
    -- Same 1_F-localization trick: f = Σ indF*cutS, g = Σ_{Icc} cutS, equal on F
    set f : Ω → ℝ := fun ω => ∑ j ∈ Ico t_i t', indF j ω * (vm.cutS j ω : ℝ)
    set g : Ω → ℝ := fun ω => ∑ j ∈ Icc t_i (T_next ω - 1), (vm.cutS j ω : ℝ)
    have hf_int : Integrable f vm.μ := hsum_indF_cutS_int
    have hg_int : Integrable g vm.μ := hsum_cutS_Icc_int
    have hsub_int : Integrable (fun ω => f ω - g ω) vm.μ := hf_int.sub hg_int
    have hfg_restrict : ∀ᵐ ω ∂((vm.μ : Measure _).restrict F), f ω = g ω := hae_cut_restrict
    have hfg_global : ∀ᵐ ω ∂(vm.μ : Measure _), ω ∈ F → f ω = g ω :=
      (ae_restrict_iff' hF_meas_top).mp hfg_restrict
    have hcondExp_sub : (vm.μ : Measure _)[f | vm.ℱ t_i] - (vm.μ : Measure _)[g | vm.ℱ t_i] =ᵐ[(vm.μ : Measure _)]
        (vm.μ : Measure _)[fun ω => f ω - g ω | vm.ℱ t_i] := (condExp_sub hf_int hg_int (vm.ℱ t_i)).symm
    have h1F_fg_zero_ae : ∀ᵐ ω ∂(vm.μ : Measure _),
        (Set.indicator F (fun ω => f ω - g ω) ω) = 0 := by
      filter_upwards [hfg_global] with ω hω
      by_cases hωF : ω ∈ F
      · simp [Set.indicator_of_mem hωF, hω hωF]
      · simp [Set.indicator_of_notMem hωF]
    have h1F_pullout : (vm.μ : Measure _)[Set.indicator F (fun ω => f ω - g ω) | vm.ℱ t_i] =ᵐ[(vm.μ : Measure _)]
        Set.indicator F ((vm.μ : Measure _)[fun ω => f ω - g ω | vm.ℱ t_i]) :=
      condExp_indicator hsub_int hF_meas
    have hcondExp_indFsub_zero : (vm.μ : Measure _)[Set.indicator F (fun ω => f ω - g ω) | vm.ℱ t_i]
        =ᵐ[(vm.μ : Measure _)] (0 : Ω → ℝ) := by
      have hcong := condExp_congr_ae (μ := (vm.μ : Measure Ω)) (m := vm.ℱ t_i)
        (f := Set.indicator F (fun ω => f ω - g ω))
        (g := 0) h1F_fg_zero_ae
      exact hcong.trans (Filter.EventuallyEq.of_eq condExp_zero)
    have h_indc_fg_zero : ∀ᵐ ω ∂(vm.μ : Measure _),
        Set.indicator F ((vm.μ : Measure _)[fun ω => f ω - g ω | vm.ℱ t_i]) ω = 0 := by
      filter_upwards [h1F_pullout, hcondExp_indFsub_zero] with ω hpo hzero
      rw [← hpo, hzero]; rfl
    have h_fg_zero_restrict : ∀ᵐ ω ∂((vm.μ : Measure _).restrict F),
        ((vm.μ : Measure _)[fun ω => f ω - g ω | vm.ℱ t_i]) ω = 0 := by
      rw [ae_restrict_iff' hF_meas_top]
      filter_upwards [h_indc_fg_zero] with ω hω hωF
      rwa [Set.indicator_of_mem hωF] at hω
    have hsub_restrict := ae_restrict_of_ae (μ := (vm.μ : Measure Ω)) (s := F) hcondExp_sub
    filter_upwards [h_fg_zero_restrict, hsub_restrict] with ω hzero hsub
    have hsub' : (((vm.μ : Measure _)[f | vm.ℱ t_i]) - ((vm.μ : Measure _)[g | vm.ℱ t_i])) ω = _ := hsub
    simp only [Pi.sub_apply] at hsub'
    linarith
  -- h_combine analogue: assemble the final bound.
  -- E[ψ(T_next) - ψ₀ | ℱ_{t_i}] = E[ψ(T_next) - ψ(t_i) | ℱ_{t_i}] + (psi(t_i) - ψ₀)
  -- ≤ E[ψ(T_next) - ψ(t_i) | ℱ_{t_i}]  (since psi(t_i) ≤ ψ₀ a.e. on F)
  -- = E[Σ indF*δ | ℱ_{t_i}]  (on restrict F)
  -- ≤ coeff' * E[Σ indF*cutS | ℱ_{t_i}]  (global)
  -- = coeff' * E[Σ_{Icc} cutS | ℱ_{t_i}]  (on restrict F)
  -- < coeff' * (μ_param * Vol(s₀) / Δ)  (when coeff' ≤ 0 and edge sum is large)
  -- = target
  -- ae version of hcondExp_split_ti on restrict F
  have hsplit_ti_restrict := ae_restrict_of_ae (μ := (vm.μ : Measure Ω)) (s := F) hcondExp_split_ti
  have hsplit_ψ₀_restrict := ae_restrict_of_ae (μ := (vm.μ : Measure Ω)) (s := F) hcondExp_split_ψ₀
  have hgblTele_restrict := ae_restrict_of_ae (μ := (vm.μ : Measure Ω)) (s := F) h_global_telescope_le
  -- Finish
  filter_upwards [hsplit_ti_restrict, hsplit_ψ₀_restrict, hpsi_init,
    hcondExp_tele_restrictF, hgblTele_restrict, hcondExp_cut_restrictF,
    hedge_sum_large] with ω hti_split hψ₀_split hpsi_le htele hbound hcut_eq hedge
  simp only [Pi.sub_apply] at hti_split hψ₀_split
  have h_relate : ((vm.μ : Measure _)[fun ω' => vm.psiS (T_next ω') ω' -
      G.potential t_i s₀ | vm.ℱ t_i]) ω =
      ((vm.μ : Measure _)[fun ω' => vm.psiS (T_next ω') ω' - vm.psiS t_i ω' | vm.ℱ t_i]) ω +
      (vm.psiS t_i ω - G.potential t_i s₀) := by linarith
  rw [h_relate]
  have h_tele_bound : ((vm.μ : Measure _)[fun ω' => vm.psiS (T_next ω') ω' -
      vm.psiS t_i ω' | vm.ℱ t_i]) ω ≤
      coeff' * ((vm.μ : Measure _)[fun ω' => ∑ j ∈ Icc t_i (T_next ω' - 1),
        (vm.cutS j ω' : ℝ) | vm.ℱ t_i]) ω := by
    -- chain: htele then hbound then hcut_eq
    have h_step1 : ((vm.μ : Measure _)[fun ω' => vm.psiS (T_next ω') ω' - vm.psiS t_i ω' | vm.ℱ t_i]) ω =
        ((vm.μ : Measure _)[fun ω' => ∑ j ∈ Ico t_i t', indF j ω' * δ j ω' | vm.ℱ t_i]) ω := htele
    have h_step2 : ((vm.μ : Measure _)[fun ω' => ∑ j ∈ Ico t_i t', indF j ω' * δ j ω' | vm.ℱ t_i]) ω ≤
        coeff' * ((vm.μ : Measure _)[fun ω' => ∑ j ∈ Ico t_i t',
          indF j ω' * (vm.cutS j ω' : ℝ) | vm.ℱ t_i]) ω := hbound
    have h_step3 : ((vm.μ : Measure _)[fun ω' => ∑ j ∈ Ico t_i t',
        indF j ω' * (vm.cutS j ω' : ℝ) | vm.ℱ t_i]) ω =
        ((vm.μ : Measure _)[fun ω' => ∑ j ∈ Icc t_i (T_next ω' - 1),
          (vm.cutS j ω' : ℝ) | vm.ℱ t_i]) ω := hcut_eq
    linarith [h_step3 ▸ h_step2]
  -- psiS(t_i, ω) - ψ₀ ≤ 0 (from hpsi_le a.e. on restrict F)
  have h_init_le : vm.psiS t_i ω - G.potential t_i s₀ ≤ 0 := by linarith
  -- Now use hedge_sum_large (a.e. on restrict F) to push the bound through.
  -- coeff' ≤ 0
  have hcoeff_nonpos : coeff' ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (Nat.cast_nonneg (G.minDegreeAt 0)))
    apply mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 24) (Real.sqrt_nonneg _))
    exact pow_nonneg (Real.sqrt_nonneg _) 3
  -- combine
  set sum_val := ((vm.μ : Measure _)[fun ω' => ∑ j ∈ Finset.Icc t_i (T_next ω' - 1),
      (vm.cutS j ω' : ℝ) | vm.ℱ t_i]) ω
  set M := μ_param * ((G.snapshot t_i).volume s₀ : ℝ) / Δ
  have h_sum' : M ≤ sum_val := le_of_lt hedge
  have h_step : coeff' * sum_val ≤ coeff' * M :=
    mul_le_mul_of_nonpos_left h_sum' hcoeff_nonpos
  have h_eq : coeff' * M = -((μ_param * (G.minDegreeAt 0 : ℝ)) / (24 * Real.sqrt 6 * Δ
      * G.potential t_i s₀)) := by
    simp only [coeff', M, TemporalGraph.potential]
    have hVol : 0 ≤ ((G.snapshot t_i).volume s₀ : ℝ) := Nat.cast_nonneg _
    set sv := Real.sqrt ((G.snapshot t_i).volume s₀ : ℝ)
    have hsq : sv ^ 2 = ((G.snapshot t_i).volume s₀ : ℝ) := Real.sq_sqrt hVol
    have hcube : sv ^ 3 = sv * ((G.snapshot t_i).volume s₀ : ℝ) := by
      rw [show sv ^ 3 = sv * sv ^ 2 from by ring, hsq]
    by_cases hsv0 : sv = 0
    · have hVol_eq : ((G.snapshot t_i).volume s₀ : ℝ) = 0 := by
        rw [← hsq, hsv0]; ring
      have hM0 : μ_param * ((G.snapshot t_i).volume s₀ : ℝ) / Δ = 0 := by
        rw [hVol_eq]; ring
      rw [hM0, mul_zero]
      simp [hsv0]
    have hsv_pos : 0 < sv := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hsv0)
    have hVol_pos : (0 : ℝ) < ((G.snapshot t_i).volume s₀ : ℝ) := by
      rw [← hsq]; positivity
    have hVol_ne : ((G.snapshot t_i).volume s₀ : ℝ) ≠ 0 := ne_of_gt hVol_pos
    have hsv_ne : sv ≠ 0 := ne_of_gt hsv_pos
    have hsqrt6_ne : Real.sqrt 6 ≠ 0 := ne_of_gt (Real.sqrt_pos_of_pos (by norm_num))
    have hΔ_ne : Δ ≠ 0 := ne_of_gt hΔ_pos
    have hVol_sv : ((G.snapshot t_i).volume s₀ : ℝ) = sv ^ 2 := hsq.symm
    rw [hVol_sv]
    field_simp
  linarith


/-- \label{lem:pot-change-vol-constant-combine}

Let `j ≥ 0` and `t_j ≥ 0`. Let `T_j = embeddedChainTime G.toTemporalGraph vm Δ i` with realized value
`t_i`, and `T_{j+1} = embeddedChainTime G.toTemporalGraph vm Δ (i+1)`. Let `s₀ = S_{T_j}` be the initial
minority set at time `T_j`. Let `φ_j > 0` be a lower bound on the conductance of the
interval `[T_j, T_{j+1})`. Then
`E[ψ(S_{T_{j+1}}) − ψ(s₀) | ℱ_{t_i}] ≤ −d_min · φ_j / (96√6 · ψ(s₀))`.

Note: paper states constant 500; computing both cases exactly gives
`96√6 ≈ 235.2`. -/
theorem potential_decrease_stable_interval_combined
    {Ω : Type*} [MeasurableSpace Ω]
    (G : TemporalGraphFixedDegree V)
    (vm : G.VoterModelAbstract 2 Ω)
    -- Fixed initial set s₀ ≠ ∅ and realized time t_i
    (s₀ : Finset V) (hs₀ : s₀.Nonempty)
    (t_i : ℕ)
    -- Embedded chain parameters: T_{i+1} = embeddedChainTime G.toTemporalGraph vm Δ (i+1)
    (Δ : ℕ → ℕ) (i : ℕ)
    -- T_i realizes to t_i pointwise
    (hT_val : ∀ ω, embeddedChainTime G.toTemporalGraph vm Δ i ω = t_i)
    -- S_{t_i} = s₀ pointwise
    (hS_init : ∀ ω, vm.S t_i ω = s₀)
    -- φ_j: lower bound on interval conductance
    (φ_j : ℝ) (hφ_j : 0 < φ_j)
    -- Well-formedness: t_i lies within the cap for interval i+1
    (hT_cap : t_i ≤ (∑ j ∈ Finset.range (i + 1), Δ j) - 1)
    -- Cut sum lower bound: E[∑_{j=t_i}^{T_{i+1}−1} e_j | ℱ_{t_i}] > φ_j·Vol(s₀)/4
    (hedge_sum : ∀ᵐ ω ∂(vm.μ : Measure _),
      ((vm.μ : Measure _)[fun ω' => ∑ j ∈ Finset.Icc t_i (embeddedChainTime G.toTemporalGraph vm Δ (i + 1) ω' - 1),
        (vm.cutS j ω' : ℝ) | vm.ℱ t_i]) ω
        > φ_j * ((G.snapshot t_i).volume s₀ : ℝ) / 4) :
    -- Conclusion: E[ψ(S_{T_{i+1}}) − ψ(s₀) | ℱ_{t_i}] ≤ −d_min·φ_j / (96√6·ψ(s₀))
    ∀ᵐ ω ∂(vm.μ : Measure _),
      ((vm.μ : Measure _)[fun ω' => vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (i + 1) ω') ω'
        - G.potential t_i s₀ | vm.ℱ t_i]) ω
        ≤ -((G.minDegreeAt 0 : ℝ) * φ_j)
          / (96 * Real.sqrt 6 * G.potential t_i s₀) := by
  -- Derive hstable_vol from volumeExcursionTime_vol_le:
  -- before the excursion time, 2·Vol(j) ≤ 3·Vol(t_i) = 3·Vol(s₀)
  have hstable_vol : ∀ ω, ∀ j, t_i ≤ j → j < embeddedChainTime G.toTemporalGraph vm Δ (i + 1) ω →
      ((G.snapshot j).volume (vm.S j ω) : ℝ) ≤
        3 / 2 * ((G.snapshot t_i).volume s₀ : ℝ) := by
    intro ω j h_lo h_hi
    -- Unfold T_{i+1} = volumeExcursionTime at t_i
    have hT_next : embeddedChainTime G.toTemporalGraph vm Δ (i + 1) ω =
        volumeExcursionTime G.toTemporalGraph vm t_i ((∑ k ∈ Finset.range (i + 1), Δ k) - 1) ω := by
      simp only [embeddedChainTime]; rw [hT_val ω]
    rw [hT_next] at h_hi
    have hbound := volumeExcursionTime_vol_le G.toTemporalGraph vm t_i _ j ω h_lo h_hi
    rw [hS_init ω] at hbound
    have hbound_r : (2 : ℝ) * ((G.snapshot j).volume (vm.S j ω) : ℝ) ≤
        3 * ((G.snapshot t_i).volume s₀ : ℝ) := by exact_mod_cast hbound
    linarith
  -- Derive hS_nonempty from volumeExcursionTime_S_nonempty:
  -- before the excursion time and given s₀ nonempty, S_j is nonempty
  have hS_nonempty : ∀ ω, ∀ j, t_i ≤ j → j < embeddedChainTime G.toTemporalGraph vm Δ (i + 1) ω →
      (vm.S j ω).Nonempty := by
    intro ω j h_lo h_hi
    have hT_next : embeddedChainTime G.toTemporalGraph vm Δ (i + 1) ω =
        volumeExcursionTime G.toTemporalGraph vm t_i ((∑ k ∈ Finset.range (i + 1), Δ k) - 1) ω := by
      simp only [embeddedChainTime]; rw [hT_val ω]
    rw [hT_next] at h_hi
    exact volumeExcursionTime_S_nonempty G vm t_i _ j ω h_lo h_hi
      (hS_init ω ▸ hs₀)
  -- Measurability of S: S t = minoritySet G.toTemporalGraph t ∘ A t, and A is adapted
  have hS_meas : ∀ t, @Measurable Ω (Finset V) (vm.ℱ t) ⊤ (vm.S t) := fun t =>
    (measurable_of_countable (fun A => VoterModel.minoritySet G.toTemporalGraph t A)).comp
      (vm.A_stronglyAdapted t).measurable
  -- T_{i+1} is a stopping time
  have hT_stop : IsStoppingTime vm.ℱ (fun ω => (embeddedChainTime G.toTemporalGraph vm Δ (i + 1) ω : ℕ∞)) :=
    embeddedChainTime_isStoppingTime G.toTemporalGraph vm Δ hS_meas (i + 1)
  -- Deterministic bound: T_{i+1} ≤ cap + 1
  have hT_next_le : ∀ ω, embeddedChainTime G.toTemporalGraph vm Δ (i + 1) ω ≤
      (∑ j ∈ Finset.range (i + 1), Δ j) - 1 + 1 := fun ω => by
    have hT_next_eq : embeddedChainTime G.toTemporalGraph vm Δ (i + 1) ω =
        volumeExcursionTime G.toTemporalGraph vm t_i ((∑ j ∈ Finset.range (i + 1), Δ j) - 1) ω := by
      simp only [embeddedChainTime]; rw [hT_val ω]
    rw [hT_next_eq]
    exact volumeExcursionTime_le_succ G.toTemporalGraph vm t_i ((∑ j ∈ Finset.range (i + 1), Δ j) - 1) ω
  -- T_{i+1} > t_i (strictly), using embeddedChainTime_strictMono
  have hT_strict : ∀ ω, t_i < embeddedChainTime G.toTemporalGraph vm Δ (i + 1) ω := fun ω => by
    have hle : embeddedChainTime G.toTemporalGraph vm Δ i ω ≤ (∑ j ∈ Finset.range (i + 1), Δ j) - 1 :=
      hT_val ω ▸ hT_cap
    have hmono := embeddedChainTime_strictMono G.toTemporalGraph vm Δ i ω hle
    rwa [hT_val ω] at hmono
  have hT_next_ge : ∀ᵐ ω ∂(vm.μ : Measure _), t_i ≤ embeddedChainTime G.toTemporalGraph vm Δ (i + 1) ω :=
    ae_of_all _ fun ω => le_of_lt (hT_strict ω)
  have hT_next_pos : ∀ᵐ ω ∂(vm.μ : Measure _), 0 < embeddedChainTime G.toTemporalGraph vm Δ (i + 1) ω :=
    ae_of_all _ fun ω => Nat.lt_of_le_of_lt (Nat.zero_le t_i) (hT_strict ω)
  -- t_i ≤ cap + 1
  have ht_i_le : t_i ≤ (∑ j ∈ Finset.range (i + 1), Δ j) - 1 + 1 := Nat.le_succ_of_le hT_cap
  -- psiS t_i ω = potential G.toTemporalGraph t_i s₀ (pointwise, from hS_init)
  have hpsi_init : ∀ᵐ ω ∂(vm.μ : Measure _), vm.psiS t_i ω ≤ G.potential t_i s₀ :=
    ae_of_all _ fun ω => by
      have : vm.psiS t_i ω = G.potential t_i s₀ := by
        change G.potential t_i (vm.S t_i ω) = _; rw [hS_init ω]
      linarith
  -- Rewrite hedge_sum to match _large's interface (μ_param=1, Δ=4/φ_j)
  have hΔ : (0 : ℝ) < 4 / φ_j := div_pos (by norm_num) hφ_j
  have hedge_sum_large : ∀ᵐ ω ∂(vm.μ : Measure _),
      ((vm.μ : Measure _)[fun ω' => ∑ j ∈ Finset.Icc t_i (embeddedChainTime G.toTemporalGraph vm Δ (i + 1) ω' - 1),
        (vm.cutS j ω' : ℝ) | vm.ℱ t_i]) ω
        > 1 * ((G.snapshot t_i).volume s₀ : ℝ) / (4 / φ_j) := by
    filter_upwards [hedge_sum] with ω hω
    have heq : 1 * ((G.snapshot t_i).volume s₀ : ℝ) / (4 / φ_j)
        = φ_j * ((G.snapshot t_i).volume s₀ : ℝ) / 4 := by
      have hφ_ne : φ_j ≠ 0 := ne_of_gt hφ_j
      field_simp
    rw [heq]; exact hω
  -- Apply the large interval bound
  refine (potential_decrease_stable_interval_large G vm s₀ hs₀ t_i
      (embeddedChainTime G.toTemporalGraph vm Δ (i + 1))
      hT_stop ((∑ j ∈ Finset.range (i + 1), Δ j) - 1 + 1)
      hT_next_le hT_next_ge hT_next_pos hpsi_init
      (4 / φ_j) hΔ
      hstable_vol hS_nonempty
      1 hedge_sum_large).mono
    fun ω hω => le_trans hω ?_
  have hsq6 : Real.sqrt 6 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  by_cases hψ0 : G.potential t_i s₀ = 0
  · simp [hψ0]
  · have hφ_ne : φ_j ≠ 0 := ne_of_gt hφ_j
    have h : -((1 * ↑(G.minDegreeAt 0)) / (24 * Real.sqrt 6 *
        (4 / φ_j) * G.potential t_i s₀)) =
        -(↑(G.minDegreeAt 0) * φ_j) / (96 * Real.sqrt 6 * G.potential t_i s₀) := by
      field_simp [hsq6, hφ_ne, hψ0]
      ring
    linarith [h]

/-- Bundle of stability + integrability hypotheses required by `prob_good_event`
(see `lem:prob-good-event`) and consumed by the Case 2 small-μ dispatch
`potential_decrease_stable_interval_case2`. Collecting these into a single
structure keeps the top-level signatures of `combined_unconditional` and
`intervals_exist_stable` readable.

The fields mirror — in order — the hypothesis list of `prob_good_event`
(line 3321 of this file). -/
structure Case2Hypotheses
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    {Ω : Type*} [MeasurableSpace Ω]
    (G : TemporalGraph V) (vm : G.VoterModelAbstract 2 Ω)
    (s₀ : Finset V) (t_i : ℕ) (T_next : Ω → ℕ) (t' : ℕ) (φ_j : ℝ)
    -- F-parameterization: restrict the stability/exit fields to a
    -- measurable fiber `F`. Non-fiber callers instantiate `F = Set.univ`.
    (F : Set Ω) : Prop where
  /-- Stability on F: `E[|Vol(S_{T_next}) − Vol(s₀)| | ℱ_{t_i}] < (1/8) · Vol(s₀)`
  a.e. on `(vm.μ : Measure _).restrict F`. Threshold matches the paper's `D27 (ν=1/8)` stable
  predicate (used by `IsStableInterval` at L91/L83 for the dichotomy). -/
  stable : ∀ᵐ ω ∂((vm.μ : Measure _).restrict F),
    ((vm.μ : Measure _)[fun ω' => |((G.snapshot (T_next ω')).volume (vm.S (T_next ω') ω') : ℝ)
      - ((G.snapshot t_i).volume s₀ : ℝ)| | vm.ℱ t_i]) ω
      < (1 / 8 : ℝ) * ((G.snapshot t_i).volume s₀ : ℝ)
  /-- Exit-time on F: if `T_next ≤ t'` then the (1/2)-deviation threshold is
  exceeded, a.e. on `(vm.μ : Measure _).restrict F`. -/
  exit : ∀ᵐ ω ∂((vm.μ : Measure _).restrict F), T_next ω ≤ t' →
    (1 / 2 : ℝ) * ((G.snapshot t_i).volume s₀ : ℝ)
      ≤ |((G.snapshot (T_next ω)).volume (vm.S (T_next ω) ω) : ℝ)
          - ((G.snapshot t_i).volume s₀ : ℝ)|
  /-- Integrability of the volume deviation. -/
  devInt : Integrable (fun ω =>
      |((G.snapshot (T_next ω)).volume (vm.S (T_next ω) ω) : ℝ)
        - ((G.snapshot t_i).volume s₀ : ℝ)|) vm.μ
  /-- Integrability of stopped |Δ_j| sum (edge-flow variations at `t'`). -/
  sumAbsInt : Integrable (fun ω' =>
      ∑ j ∈ Finset.Icc t_i (T_next ω' - 1),
        |(G.edgesBetween t'
            (vm.S (j + 1) ω') (Finset.univ \ vm.S (j + 1) ω') : ℝ)
          - (G.edgesBetween t'
            (vm.S j ω') (Finset.univ \ vm.S j ω') : ℝ)|) vm.μ
  /-- Per-step integrability of `|Δ_j|`. -/
  deltaInt : ∀ j, Integrable (fun ω' =>
      |(G.edgesBetween t'
          (vm.S (j + 1) ω') (Finset.univ \ vm.S (j + 1) ω') : ℝ)
        - (G.edgesBetween t'
          (vm.S j ω') (Finset.univ \ vm.S j ω') : ℝ)|) vm.μ
  /-- Per-step integrability of `cutS`. -/
  cutInt : ∀ j, Integrable (fun ω' => (vm.cutS j ω' : ℝ)) vm.μ
  /-- `T_next` is bounded by a deterministic `N`. -/
  bound : ∃ N : ℕ, ∀ ω, T_next ω ≤ N
  /-- The good-step time `t'` lies at or after `t_i`. -/
  t'_ge : t_i ≤ t'

/-- Telescoping+one-step bound extracted from `potential_decrease_stable_interval_case2`.
Split out as a private theorem purely to keep the enclosing proof within the default
heartbeat budget — the original inline block triggered a heartbeat timeout around
the `htower_t'` step. -/
private theorem case2_telescope_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (G : TemporalGraphFixedDegree V)
    (vm : G.VoterModelAbstract 2 Ω)
    (s₀ : Finset V) (hs₀ : s₀.Nonempty)
    (t_i : ℕ) (Δ : ℕ → ℕ) (i : ℕ)
    (hT_val : ∀ ω, embeddedChainTime G.toTemporalGraph vm Δ i ω = t_i)
    (hS_init : ∀ ω, vm.S t_i ω = s₀)
    (φ_j : ℝ) (hφ_j : 0 < φ_j)
    (hVol_pos : (0 : ℝ) < (G.snapshot t_i).volume s₀)
    (t' : ℕ) (ht'_lo : t_i ≤ t')
    (hT_stop : IsStoppingTime vm.ℱ (fun ω => (embeddedChainTime G.toTemporalGraph vm Δ (i + 1) ω : ℕ∞)))
    (N : ℕ) (hN : ∀ ω, embeddedChainTime G.toTemporalGraph vm Δ (i + 1) ω ≤ N)
    (hgt : ∀ ω, t_i < embeddedChainTime G.toTemporalGraph vm Δ (i + 1) ω) :
    ∀ᵐ ω ∂(vm.μ : Measure _),
      ((vm.μ : Measure _)[fun ω' => vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (i + 1) ω') ω' -
        G.potential t_i s₀ | vm.ℱ t_i]) ω
      ≤ -((1 / 4 : ℝ) * (G.minDegreeAt 0 : ℝ) * φ_j /
          (24 * Real.sqrt 6 * G.potential t_i s₀))
        * ((vm.μ : Measure _)[fun ω' =>
            if t' < embeddedChainTime G.toTemporalGraph vm Δ (i + 1) ω'
              ∧ (vm.cutS t' ω' : ℝ) ≥
                (1 / 4 : ℝ) * ((G.snapshot t_i).volume s₀ : ℝ) / (1 / φ_j)
            then (1 : ℝ) else 0 | vm.ℱ t_i]) ω := by
  set Vol₀ : ℝ := ((G.snapshot t_i).volume s₀ : ℝ) with hVol₀_def
  set ψ₀ : ℝ := G.potential t_i s₀ with hψ₀_def
  -- \label{case2-telescope-gap}
  -- Step 0: hstable_vol and hS_nonempty (same derivation as in _combined)
  have hstable_vol : ∀ ω, ∀ j, t_i ≤ j → j < embeddedChainTime G.toTemporalGraph vm Δ (i + 1) ω →
      ((G.snapshot j).volume (vm.S j ω) : ℝ) ≤ 3 / 2 * Vol₀ := by
    intro ω j h_lo h_hi
    have hT_eq : embeddedChainTime G.toTemporalGraph vm Δ (i + 1) ω =
        volumeExcursionTime G.toTemporalGraph vm t_i ((∑ k ∈ Finset.range (i + 1), Δ k) - 1) ω := by
      simp only [embeddedChainTime]; rw [hT_val ω]
    rw [hT_eq] at h_hi
    have hb := volumeExcursionTime_vol_le G.toTemporalGraph vm t_i _ j ω h_lo h_hi
    rw [hS_init ω] at hb
    have hcast : (2 : ℝ) * ((G.snapshot j).volume (vm.S j ω) : ℝ) ≤
        3 * ((G.snapshot t_i).volume s₀ : ℝ) := by exact_mod_cast hb
    nlinarith [hcast, show Vol₀ = ((G.snapshot t_i).volume s₀ : ℝ) from hVol₀_def]
  have hS_nonempty : ∀ ω, ∀ j, t_i ≤ j → j < embeddedChainTime G.toTemporalGraph vm Δ (i + 1) ω →
      (vm.S j ω).Nonempty := by
    intro ω j h_lo h_hi
    have hT_eq : embeddedChainTime G.toTemporalGraph vm Δ (i + 1) ω =
        volumeExcursionTime G.toTemporalGraph vm t_i ((∑ k ∈ Finset.range (i + 1), Δ k) - 1) ω := by
      simp only [embeddedChainTime]; rw [hT_val ω]
    rw [hT_eq] at h_hi
    exact volumeExcursionTime_S_nonempty G vm t_i _ j ω h_lo h_hi (hS_init ω ▸ hs₀)
  -- Step 1: psiS(t_i) = ψ₀ pointwise (equality, not just ≤)
  have hpsi_ti_eq : ∀ ω, vm.psiS t_i ω = ψ₀ := fun ω => by
    change G.potential t_i (vm.S t_i ω) = _; rw [hS_init ω]
  -- Step 2: extended deterministic bound N' ≥ T_next ω and t' < N'
  let N' : ℕ := N + t' + 1
  have hN'_bound : ∀ ω, embeddedChainTime G.toTemporalGraph vm Δ (i + 1) ω ≤ N' :=
    fun ω => Nat.le_trans (hN ω) (by omega)
  have ht'_lt_N' : t' < N' := by omega
  -- Step 3: standard telescope infrastructure
  haveI : SigmaFiniteFiltration vm.μ vm.ℱ := inferInstance
  let T_next_fn := fun ω => embeddedChainTime G.toTemporalGraph vm Δ (i + 1) ω
  let ind : ℕ → Ω → ℝ := fun j ω => if j < T_next_fn ω then 1 else 0
  let δ : ℕ → Ω → ℝ := fun j ω => vm.psiS (j + 1) ω - vm.psiS j ω
  have hpsiS_int : ∀ j, Integrable (fun ω => vm.psiS j ω) vm.μ := fun j =>
    (voter_integrable_comp_A vm
      (fun s' => G.potential j (minoritySet G.toTemporalGraph j s')) j).congr
      (Filter.Eventually.of_forall fun ω' => by
        simp [TemporalGraph.VoterModelAbstract.psiS, TemporalGraph.VoterModelAbstract.S])
  have hδ_int : ∀ j, Integrable (δ j) vm.μ := fun j => (hpsiS_int (j + 1)).sub (hpsiS_int j)
  have hind_meas_set : ∀ j, MeasurableSet[vm.ℱ j] {ω | j < T_next_fn ω} := by
    intro j
    have hset : {ω | j < T_next_fn ω} = {ω | (T_next_fn ω : ℕ∞) ≤ ↑j}ᶜ := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le, ENat.coe_lt_coe]
    rw [hset]; exact (hT_stop j).compl
  have hind_sm : ∀ j, StronglyMeasurable[vm.ℱ j] (ind j) :=
    fun j => StronglyMeasurable.ite (hind_meas_set j) stronglyMeasurable_one stronglyMeasurable_zero
  have hind_δ_int : ∀ j, Integrable (fun ω => ind j ω * δ j ω) vm.μ := by
    intro j
    have heq : (fun ω => ind j ω * δ j ω) = Set.indicator {ω | j < T_next_fn ω} (δ j) := by
      funext ω; simp only [ind, Set.indicator, Set.mem_setOf_eq]; split <;> simp
    rw [heq]; exact (hδ_int j).indicator (vm.ℱ.le j _ (hind_meas_set j))
  -- Telescoping identity: psiS(T_next) - psiS(t_i) = Σ_{Ico t_i N'} ind * δ
  have htelescope_pw : ∀ ω, t_i ≤ T_next_fn ω →
      vm.psiS (T_next_fn ω) ω - vm.psiS t_i ω =
      ∑ j ∈ Finset.Ico t_i N', ind j ω * δ j ω := by
    intro ω hge
    have hle := hN'_bound ω
    rw [← Finset.sum_Ico_consecutive _ hge hle]
    have htail : ∑ j ∈ Finset.Ico (T_next_fn ω) N', ind j ω * δ j ω = 0 :=
      Finset.sum_eq_zero fun j hj => by
        rw [Finset.mem_Ico] at hj
        simp only [ind, if_neg (by omega : ¬ j < T_next_fn ω), zero_mul]
    rw [htail, add_zero]
    have hhead : ∑ j ∈ Finset.Ico t_i (T_next_fn ω), ind j ω * δ j ω =
        ∑ j ∈ Finset.Ico t_i (T_next_fn ω), δ j ω :=
      Finset.sum_congr rfl fun j hj => by
        rw [Finset.mem_Ico] at hj; simp only [ind, if_pos hj.2, one_mul]
    rw [hhead]
    simp only [δ]
    have htele : ∀ a b, a ≤ b →
        ∑ j ∈ Finset.Ico a b, (vm.psiS (j + 1) ω - vm.psiS j ω) = vm.psiS b ω - vm.psiS a ω := by
      intro a b hab
      induction b with
      | zero => simp [Nat.le_zero.mp hab]
      | succ n ih =>
        rcases Nat.eq_or_lt_of_le hab with rfl | hlt
        · simp
        · rw [Finset.sum_Ico_succ_top (by omega : a ≤ n), ih (by omega)]; ring
    exact (htele t_i (T_next_fn ω) hge).symm
  -- ae equality
  have hae_tele : ∀ᵐ ω ∂(vm.μ : Measure _),
      vm.psiS (T_next_fn ω) ω - vm.psiS t_i ω =
      ∑ j ∈ Finset.Ico t_i N', ind j ω * δ j ω :=
    Filter.Eventually.of_forall fun ω => htelescope_pw ω (le_of_lt (hgt ω))
  -- Integrability of psiS(T_next)
  have hTnext_eq_meas : ∀ k, MeasurableSet {ω | T_next_fn ω = k} := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have : {ω | T_next_fn ω = 0} = {ω | (T_next_fn ω : ℕ∞) ≤ ↑0} := by
        ext ω; simp
      rw [this]; exact vm.ℱ.le 0 _ (hT_stop 0)
    · have : {ω | T_next_fn ω = k} = {ω | (T_next_fn ω : ℕ∞) ≤ ↑k} \
          {ω | (T_next_fn ω : ℕ∞) ≤ ↑(k - 1)} := by
        ext ω; simp only [Set.mem_setOf_eq, Set.mem_sdiff, ENat.coe_le_coe]; omega
      rw [this]
      exact (vm.ℱ.le k _ (hT_stop k)).diff (vm.ℱ.le (k - 1) _ (hT_stop (k - 1)))
  have hpsiS_Tnext_int : Integrable (fun ω => vm.psiS (T_next_fn ω) ω) vm.μ := by
    have heq : (fun ω => vm.psiS (T_next_fn ω) ω) = fun ω =>
        ∑ k ∈ Finset.range (N' + 1),
          Set.indicator {ω | T_next_fn ω = k} (fun ω => vm.psiS k ω) ω := by
      funext ω; rw [Finset.sum_eq_single (T_next_fn ω)]
      · simp [Set.indicator]
      · intro k _ hk; simp [Set.indicator, Ne.symm hk]
      · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le (hN'_bound ω))) h
    rw [heq]; exact integrable_finsetSum _ fun k _ => (hpsiS_int k).indicator (hTnext_eq_meas k)
  -- condExp machinery: connect E[psiS(T_next) - ψ₀ | ℱ t_i] to Σ terms
  have hpsiS_ti_sm : StronglyMeasurable[vm.ℱ t_i] (fun ω => vm.psiS t_i ω) := by
    have hfact : (fun ω => vm.psiS t_i ω) =
        (fun s' => G.potential t_i (minoritySet G.toTemporalGraph t_i s')) ∘ (vm.opinionZeroSet t_i) := by
      funext ω; simp [TemporalGraph.VoterModelAbstract.psiS, TemporalGraph.VoterModelAbstract.S]
    rw [hfact]
    exact ((measurable_of_finite _).comp
      ((vm.A_stronglyAdapted t_i).measurable)).stronglyMeasurable
  have hcondExp_split_ψ₀ :
      (vm.μ : Measure _)[fun ω => vm.psiS (T_next_fn ω) ω - ψ₀ | vm.ℱ t_i] =ᵐ[(vm.μ : Measure _)]
      (vm.μ : Measure _)[fun ω => vm.psiS (T_next_fn ω) ω | vm.ℱ t_i] - fun _ => ψ₀ := by
    have h1 := condExp_sub hpsiS_Tnext_int (integrable_const ψ₀) (vm.ℱ t_i)
    rw [condExp_const (vm.ℱ.le t_i)] at h1; exact h1
  have hcondExp_split_ti :
      (vm.μ : Measure _)[fun ω => vm.psiS (T_next_fn ω) ω - vm.psiS t_i ω | vm.ℱ t_i] =ᵐ[(vm.μ : Measure _)]
      (vm.μ : Measure _)[fun ω => vm.psiS (T_next_fn ω) ω | vm.ℱ t_i] - fun ω => vm.psiS t_i ω := by
    have h1 := condExp_sub hpsiS_Tnext_int (hpsiS_int t_i) (vm.ℱ t_i)
    have h2 := condExp_of_stronglyMeasurable (vm.ℱ.le t_i) hpsiS_ti_sm (hpsiS_int t_i)
    rw [h2] at h1; exact h1
  have hcondExp_tele :
      (vm.μ : Measure _)[fun ω => vm.psiS (T_next_fn ω) ω - vm.psiS t_i ω | vm.ℱ t_i] =ᵐ[(vm.μ : Measure _)]
      (vm.μ : Measure _)[fun ω => ∑ j ∈ Finset.Ico t_i N', ind j ω * δ j ω | vm.ℱ t_i] :=
    condExp_congr_ae hae_tele
  have hcondExp_sum_δ :
      (vm.μ : Measure _)[fun ω => ∑ j ∈ Finset.Ico t_i N', ind j ω * δ j ω | vm.ℱ t_i] =ᵐ[(vm.μ : Measure _)]
      ∑ j ∈ Finset.Ico t_i N', (vm.μ : Measure _)[fun ω => ind j ω * δ j ω | vm.ℱ t_i] := by
    rw [show (fun ω => ∑ j ∈ Finset.Ico t_i N', ind j ω * δ j ω) =
          ∑ j ∈ Finset.Ico t_i N', fun ω => ind j ω * δ j ω from by funext; simp [Finset.sum_apply]]
    exact condExp_finsetSum (fun j _ => hind_δ_int j) (vm.ℱ t_i)
  -- Step 4: one-step bound (same as h_onestep in _large but using hstable_vol above)
  set coeff' := -(G.minDegreeAt 0 : ℝ) / (24 * Real.sqrt 6 * ψ₀ ^ 3) with hcoeff'_def
  have hψ₀_nn' : (0 : ℝ) ≤ ψ₀ := Real.sqrt_nonneg _
  have hcoeff'_nonpos : coeff' ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) (by positivity)
  have h_onestep : ∀ j, ∀ᵐ ω ∂(vm.μ : Measure _),
      t_i ≤ j → j < T_next_fn ω →
      ((vm.μ : Measure _)[fun ω' => vm.psiS (j + 1) ω' - vm.psiS j ω' | vm.ℱ j]) ω
        ≤ coeff' * (vm.cutS j ω : ℝ) := by
    intro j
    have hpsi1_int : Integrable (fun ω' => vm.psiS (j + 1) ω') vm.μ :=
      (voter_integrable_comp_A vm
        (fun s' => G.potential (j+1) (minoritySet G.toTemporalGraph (j+1) s')) (j+1)).congr
        (Filter.Eventually.of_forall fun ω' => by
          simp [TemporalGraph.VoterModelAbstract.psiS, TemporalGraph.VoterModelAbstract.S])
    have hpsi_j_int : Integrable (fun ω' => vm.psiS j ω') vm.μ := hpsiS_int j
    have hAj_Fmeas : @Measurable Ω (Finset V) (vm.ℱ j) ⊤ (vm.opinionZeroSet j) :=
      (vm.A_stronglyAdapted j).measurable
    have hpsi_j_sm : StronglyMeasurable[vm.ℱ j] (fun ω' => vm.psiS j ω') := by
      have : (fun ω' => vm.psiS j ω') =
          (fun s' => G.potential j (minoritySet G.toTemporalGraph j s')) ∘ (vm.opinionZeroSet j) := by
        funext ω'; simp [TemporalGraph.VoterModelAbstract.psiS, TemporalGraph.VoterModelAbstract.S]
      rw [this]; exact ((measurable_of_finite _).comp hAj_Fmeas).stronglyMeasurable
    have hcE_split : (vm.μ : Measure _)[fun ω' => vm.psiS (j + 1) ω' - vm.psiS j ω' | vm.ℱ j] =ᵐ[(vm.μ : Measure _)]
        (vm.μ : Measure _)[fun ω' => vm.psiS (j + 1) ω' | vm.ℱ j] - fun ω' => vm.psiS j ω' := by
      have h1 := condExp_sub hpsi1_int hpsi_j_int (vm.ℱ j)
      have h2 := condExp_of_stronglyMeasurable (vm.ℱ.le j) hpsi_j_sm hpsi_j_int
      rw [h2] at h1; exact h1
    filter_upwards [hcE_split, potential_decrease_one_step G vm j] with ω h_split h_pdos
    intro hj_ge hj_lt
    rw [h_split]; simp only [Pi.sub_apply]
    have hS_ne : (vm.S j ω).Nonempty := hS_nonempty ω j hj_ge hj_lt
    have h_ax := h_pdos hS_ne.ne_empty
    set ψ_j := vm.psiS j ω
    set c_j := (vm.cutS j ω : ℝ)
    set d_min := (G.minDegreeAt 0 : ℝ)
    have hstab := hstable_vol ω j hj_ge hj_lt
    have hψ_j_sq : ψ_j ^ 2 = ((G.snapshot j).volume (vm.S j ω) : ℝ) := by
      simp only [ψ_j, TemporalGraph.VoterModelAbstract.psiS, TemporalGraph.potential]
      exact Real.sq_sqrt (Nat.cast_nonneg _)
    have hψ₀_sq : ψ₀ ^ 2 = Vol₀ := by
      simp only [ψ₀, TemporalGraph.potential]; exact Real.sq_sqrt (Nat.cast_nonneg _)
    have hψ_sq_le : ψ_j ^ 2 ≤ 3 / 2 * ψ₀ ^ 2 := by rw [hψ_j_sq, hψ₀_sq]; exact hstab
    have hVol_j_pos : (0 : ℝ) < (G.snapshot j).volume (vm.S j ω) :=
      Nat.cast_pos.mpr ((G.snapshot j).volume_pos_of_nonempty hS_ne (fun v => G.degrees_pos v j))
    have hψ_j_pos : 0 < ψ_j := by
      simp only [ψ_j, TemporalGraph.VoterModelAbstract.psiS, TemporalGraph.potential]
      exact Real.sqrt_pos_of_pos hVol_j_pos
    have hψ₀_pos : 0 < ψ₀ := by
      simp only [ψ₀, TemporalGraph.potential]; exact Real.sqrt_pos_of_pos hVol_pos
    have h_cube_bound : 32 * ψ_j ^ 3 ≤ 24 * Real.sqrt 6 * ψ₀ ^ 3 := by
      have h_lhs_nn : 0 ≤ 32 * ψ_j ^ 3 := by positivity
      have h_rhs_nn : 0 ≤ 24 * Real.sqrt 6 * ψ₀ ^ 3 := by positivity
      calc 32 * ψ_j ^ 3
          = Real.sqrt ((32 * ψ_j ^ 3) ^ 2) := (Real.sqrt_sq h_lhs_nn).symm
        _ ≤ Real.sqrt ((24 * Real.sqrt 6 * ψ₀ ^ 3) ^ 2) := by
            apply Real.sqrt_le_sqrt
            have h_lhs : (32 * ψ_j ^ 3) ^ 2 = 1024 * (ψ_j ^ 2) ^ 3 := by ring
            have hsq6 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num : (6 : ℝ) ≥ 0)
            have h_rhs : (24 * Real.sqrt 6 * ψ₀ ^ 3) ^ 2 = 3456 * ψ₀ ^ 6 := by
              have e : (24 * Real.sqrt 6 * ψ₀ ^ 3) ^ 2 = 24 ^ 2 * Real.sqrt 6 ^ 2 * (ψ₀ ^ 3) ^ 2 := by
                ring
              rw [e, hsq6]; ring
            rw [h_lhs, h_rhs]
            have h_cube : (ψ_j ^ 2) ^ 3 ≤ (3 / 2 * ψ₀ ^ 2) ^ 3 :=
              pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ ψ_j ^ 2) hψ_sq_le 3
            calc 1024 * (ψ_j ^ 2) ^ 3 ≤ 1024 * (3 / 2 * ψ₀ ^ 2) ^ 3 :=
                  mul_le_mul_of_nonneg_left h_cube (by norm_num)
              _ = 3456 * ψ₀ ^ 6 := by ring
        _ = 24 * Real.sqrt 6 * ψ₀ ^ 3 := Real.sqrt_sq h_rhs_nn
    have h_div_bound : (G.minDegreeAt 0 : ℝ) * c_j / (24 * Real.sqrt 6 * ψ₀ ^ 3) ≤
        (G.minDegreeAt 0 : ℝ) * c_j / (32 * ψ_j ^ 3) :=
      div_le_div_of_nonneg_left (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (by positivity) h_cube_bound
    have h_ax_sub : ((vm.μ : Measure _)[fun ω' => vm.psiS (j + 1) ω' | vm.ℱ j]) ω - ψ_j ≤
        -(d_min / 32 * c_j / ψ_j ^ 3) :=
      (sub_le_sub_right h_ax ψ_j).trans_eq (by ring)
    rw [show coeff' * c_j = -(d_min * c_j / (24 * Real.sqrt 6 * ψ₀ ^ 3)) by
          simp only [coeff']; ring]
    exact h_ax_sub.trans (calc -(d_min / 32 * c_j / ψ_j ^ 3)
        = -(d_min * c_j / (32 * ψ_j ^ 3)) := by ring
      _ ≤ -(d_min * c_j / (24 * Real.sqrt 6 * ψ₀ ^ 3)) := neg_le_neg h_div_bound)
  -- Step 5: define the good-event indicator ind_ℰ (ℱ t'-measurable)
  let ind_ℰ : Ω → ℝ := fun ω =>
    if t' < T_next_fn ω ∧ (vm.cutS t' ω : ℝ) ≥ (1/4) * Vol₀ / (1/φ_j) then 1 else 0
  have hℰ_meas : MeasurableSet[vm.ℱ t']
      {ω | t' < T_next_fn ω ∧ (vm.cutS t' ω : ℝ) ≥ (1/4) * Vol₀ / (1/φ_j)} := by
    apply MeasurableSet.inter (hind_meas_set t')
    have hfact : (fun ω => (vm.cutS t' ω : ℝ)) =
        (fun s' => (G.edgesBetween t' (minoritySet G.toTemporalGraph t' s')
          (Finset.univ \ minoritySet G.toTemporalGraph t' s') : ℝ)) ∘ (vm.opinionZeroSet t') := by
      funext ω; simp [TemporalGraph.VoterModelAbstract.cutS, TemporalGraph.VoterModelAbstract.S]
    have hcutS_meas : @Measurable Ω ℝ (vm.ℱ t') _ (fun ω => (vm.cutS t' ω : ℝ)) := by
      rw [hfact]
      exact (measurable_of_finite _).comp
        ((vm.A_stronglyAdapted t').measurable)
    exact hcutS_meas measurableSet_Ici
  have hind_ℰ_sm : StronglyMeasurable[vm.ℱ t'] ind_ℰ :=
    StronglyMeasurable.ite hℰ_meas stronglyMeasurable_one stronglyMeasurable_zero
  have hind_ℰ_int : Integrable ind_ℰ vm.μ :=
    (integrable_const (1 : ℝ)).mono (hind_ℰ_sm.mono (vm.ℱ.le t')).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        show ‖ind_ℰ ω‖ ≤ ‖(1 : ℝ)‖
        simp only [ind_ℰ]; split_ifs <;> norm_num)
  -- ind_ℰ coincides with the ℰ indicator in h_prob_good
  have hind_ℰ_eq : ∀ ω, ind_ℰ ω =
      if t' < embeddedChainTime G.toTemporalGraph vm Δ (i + 1) ω ∧
        (vm.cutS t' ω : ℝ) ≥ (1/4) * Vol₀ / (1/φ_j) then (1 : ℝ) else 0 := fun ω => rfl
  -- Step 6: per-term bound — all terms ≤ 0
  have h_allterms_le : ∀ j, j ∈ Finset.Ico t_i N' → ∀ᵐ ω ∂(vm.μ : Measure _),
      ((vm.μ : Measure _)[fun ω' => ind j ω' * δ j ω' | vm.ℱ t_i]) ω ≤ 0 := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    have htower : (vm.μ : Measure _)[fun ω => ind j ω * δ j ω | vm.ℱ t_i] =ᵐ[(vm.μ : Measure _)]
        (vm.μ : Measure _)[(vm.μ : Measure _)[fun ω => ind j ω * δ j ω | vm.ℱ j] | vm.ℱ t_i] :=
      (condExp_condExp_of_le (vm.ℱ.mono hj.1) (vm.ℱ.le j)).symm
    have hpullout : (vm.μ : Measure _)[fun ω => ind j ω * δ j ω | vm.ℱ j] =ᵐ[(vm.μ : Measure _)]
        fun ω => ind j ω * ((vm.μ : Measure _)[δ j | vm.ℱ j]) ω :=
      condExp_stronglyMeasurable_mul_of_bound (vm.ℱ.le j) (hind_sm j) (hδ_int j) 1
        (Filter.Eventually.of_forall fun ω => by simp [ind]; split <;> norm_num)
    have hpw : ∀ᵐ ω ∂(vm.μ : Measure _), ind j ω * ((vm.μ : Measure _)[δ j | vm.ℱ j]) ω ≤ 0 := by
      filter_upwards [h_onestep j] with ω honestep_ω
      by_cases hlt : j < T_next_fn ω
      · simp only [ind, if_pos hlt, one_mul]
        have h := honestep_ω hj.1 hlt
        have := mul_nonpos_of_nonpos_of_nonneg hcoeff'_nonpos (Nat.cast_nonneg (vm.cutS j ω))
        linarith
      · simp only [ind, if_neg hlt, zero_mul, le_refl]
    have h_ce0 : (vm.μ : Measure _)[(fun _ => (0 : ℝ)) | vm.ℱ t_i] =ᵐ[(vm.μ : Measure _)] (0 : Ω → ℝ) :=
      Filter.EventuallyEq.of_eq condExp_zero
    have h_mono : (vm.μ : Measure _)[fun ω => ind j ω * ((vm.μ : Measure _)[δ j | vm.ℱ j]) ω | vm.ℱ t_i] ≤ᵐ[(vm.μ : Measure _)]
        (vm.μ : Measure _)[(fun _ => (0 : ℝ)) | vm.ℱ t_i] := by
      apply condExp_mono (integrable_condExp.congr hpullout) (integrable_const (0 : ℝ)) hpw
    filter_upwards [htower, condExp_congr_ae hpullout, h_mono, h_ce0]
      with ω h1 h2 h3 h4
    simp only [Pi.zero_apply] at h4
    rw [h1, h2]
    exact h3.trans h4.le
  -- Step 7: the t'-term bound — E[ind_{t'} * δ_{t'} | ℱ_{t_i}] ≤ -K * E[ind_ℰ | ℱ_{t_i}]
  -- First: pointwise bound ind_{t'} * E[δ_{t'}|ℱ_{t'}] ≤ -η*d_min*φ_j/(24*√6*ψ₀) * ind_ℰ
  have h_t'_pw : ∀ᵐ ω ∂(vm.μ : Measure _),
      ind t' ω * ((vm.μ : Measure _)[δ t' | vm.ℱ t']) ω ≤
      -((1/4 : ℝ) * (G.minDegreeAt 0 : ℝ) * φ_j / (24 * Real.sqrt 6 * ψ₀)) * ind_ℰ ω := by
    filter_upwards [h_onestep t'] with ω honestep_ω
    by_cases hlt : t' < T_next_fn ω
    · simp only [ind, if_pos hlt, one_mul]
      have hS_ne' : (vm.S t' ω).Nonempty := hS_nonempty ω t' ht'_lo hlt
      have honestep := honestep_ω ht'_lo hlt
      have hψ₀_pos : 0 < ψ₀ := by
        simp only [ψ₀, TemporalGraph.potential]; exact Real.sqrt_pos_of_pos hVol_pos
      have hψ₀_sq : ψ₀ ^ 2 = Vol₀ := by
        simp only [ψ₀, TemporalGraph.potential]; exact Real.sq_sqrt (Nat.cast_nonneg _)
      by_cases hgood : (vm.cutS t' ω : ℝ) ≥ (1/4) * Vol₀ / (1/φ_j)
      · -- ω ∈ ℰ: ind_ℰ = 1, need E[δ_{t'}|ℱ_{t'}] ≤ -η*d_min*φ_j/(24*√6*ψ₀)
        have hind_ℰ_one : ind_ℰ ω = 1 := by
          simp only [ind_ℰ]; exact if_pos ⟨hlt, hgood⟩
        rw [hind_ℰ_one, mul_one]
        have hcut_low : (vm.cutS t' ω : ℝ) ≥ (1/4) * Vol₀ * φ_j := by
          have : (1/4) * Vol₀ / (1/φ_j) = (1/4) * Vol₀ * φ_j := by field_simp
          exact this ▸ hgood
        -- coeff' ≤ 0 and cutS ≥ η*Vol₀*φ_j, so coeff'*cutS ≤ coeff'*η*Vol₀*φ_j
        have h_bound : coeff' * (vm.cutS t' ω : ℝ) ≤ coeff' * ((1/4) * Vol₀ * φ_j) :=
          mul_le_mul_of_nonpos_left hcut_low hcoeff'_nonpos
        have h_rhs_eq : coeff' * ((1/4) * Vol₀ * φ_j) =
            -((1/4 : ℝ) * (G.minDegreeAt 0 : ℝ) * φ_j / (24 * Real.sqrt 6 * ψ₀)) := by
          simp only [coeff']; rw [← hψ₀_sq]; field_simp
        exact (honestep_ω ht'_lo hlt).trans (h_bound.trans h_rhs_eq.le)
      · -- ω ∉ ℰ (T_next > t' but cut small): ind_ℰ = 0, need E[δ_{t'}|ℱ_{t'}] ≤ 0
        have hind_ℰ_zero : ind_ℰ ω = 0 := by
          simp only [ind_ℰ]
          exact if_neg (fun h => hgood h.2)
        rw [hind_ℰ_zero, mul_zero]
        have := mul_nonpos_of_nonpos_of_nonneg hcoeff'_nonpos (Nat.cast_nonneg (vm.cutS t' ω))
        linarith
    · -- T_next ω ≤ t': ind = 0, ind_ℰ = 0
      simp only [ind, if_neg hlt, zero_mul]
      have hind_ℰ_zero : ind_ℰ ω = 0 := by
        simp only [ind_ℰ]; exact if_neg (fun h => hlt h.1)
      simp [hind_ℰ_zero]
  -- Tower + pull-out for t'-term
  have htower_t' : (vm.μ : Measure _)[fun ω => ind t' ω * δ t' ω | vm.ℱ t_i] =ᵐ[(vm.μ : Measure _)]
      (vm.μ : Measure _)[(vm.μ : Measure _)[fun ω => ind t' ω * δ t' ω | vm.ℱ t'] | vm.ℱ t_i] := by
    have h_mono_ti : vm.ℱ t_i ≤ vm.ℱ t' := vm.ℱ.mono ht'_lo
    have h_le_m := vm.ℱ.le t'
    exact (condExp_condExp_of_le h_mono_ti h_le_m).symm
  have hpullout_t' : (vm.μ : Measure _)[fun ω => ind t' ω * δ t' ω | vm.ℱ t'] =ᵐ[(vm.μ : Measure _)]
      fun ω => ind t' ω * ((vm.μ : Measure _)[δ t' | vm.ℱ t']) ω :=
    condExp_stronglyMeasurable_mul_of_bound (vm.ℱ.le t') (hind_sm t') (hδ_int t') 1
      (Filter.Eventually.of_forall fun ω => by simp [ind]; split <;> norm_num)
  -- ind_ℰ * (-K) is ℱ t'-strongly measurable and integrable
  have hmul_ℰ_sm : StronglyMeasurable[vm.ℱ t']
      (fun ω => -((1/4 : ℝ) * (G.minDegreeAt 0 : ℝ) * φ_j / (24 * Real.sqrt 6 * ψ₀)) * ind_ℰ ω) :=
    stronglyMeasurable_const.mul hind_ℰ_sm
  have hmul_ℰ_int : Integrable
      (fun ω => -((1/4 : ℝ) * (G.minDegreeAt 0 : ℝ) * φ_j / (24 * Real.sqrt 6 * ψ₀)) * ind_ℰ ω)
      vm.μ := hind_ℰ_int.const_mul _
  -- E[ind_{t'} * E[δ_{t'}|ℱ_{t'}] | ℱ_{t_i}] ≤ E[-K * ind_ℰ | ℱ_{t_i}]
  have h_t'_ce : ∀ᵐ ω ∂(vm.μ : Measure _),
      ((vm.μ : Measure _)[fun ω => ind t' ω * ((vm.μ : Measure _)[δ t' | vm.ℱ t']) ω | vm.ℱ t_i]) ω ≤
      ((vm.μ : Measure _)[fun ω => -((1/4 : ℝ) * (G.minDegreeAt 0 : ℝ) * φ_j / (24 * Real.sqrt 6 * ψ₀)) *
          ind_ℰ ω | vm.ℱ t_i]) ω :=
    condExp_mono (integrable_condExp.congr hpullout_t') hmul_ℰ_int h_t'_pw
  -- E[-K * ind_ℰ | ℱ_{t_i}] = -K * E[ind_ℰ | ℱ_{t_i}]
  have h_K_pullout : (vm.μ : Measure _)[fun ω => -((1/4 : ℝ) * (G.minDegreeAt 0 : ℝ) * φ_j /
          (24 * Real.sqrt 6 * ψ₀)) * ind_ℰ ω | vm.ℱ t_i] =ᵐ[(vm.μ : Measure _)]
      fun ω => -((1/4 : ℝ) * (G.minDegreeAt 0 : ℝ) * φ_j / (24 * Real.sqrt 6 * ψ₀)) *
          ((vm.μ : Measure _)[ind_ℰ | vm.ℱ t_i]) ω := by
    have hsmul : (fun ω => -((1/4 : ℝ) * (G.minDegreeAt 0 : ℝ) * φ_j /
            (24 * Real.sqrt 6 * ψ₀)) * ind_ℰ ω) =
        fun ω => -((1/4 : ℝ) * (G.minDegreeAt 0 : ℝ) * φ_j / (24 * Real.sqrt 6 * ψ₀)) •
            ind_ℰ ω := by funext ω; simp [smul_eq_mul]
    rw [hsmul]
    exact (condExp_smul (μ := (vm.μ : Measure Ω))
        (-((1/4 : ℝ) * (G.minDegreeAt 0 : ℝ) * φ_j / (24 * Real.sqrt 6 * ψ₀))) ind_ℰ
        (vm.ℱ t_i)).trans
      (Filter.EventuallyEq.of_eq (funext fun ω => by simp [Pi.smul_apply, smul_eq_mul]))
  -- t'-term final bound: E[ind_{t'} * δ_{t'} | ℱ_{t_i}] ≤ -K * E[ind_ℰ | ℱ_{t_i}]
  have h_t'_bound : ∀ᵐ ω ∂(vm.μ : Measure _),
      ((vm.μ : Measure _)[fun ω' => ind t' ω' * δ t' ω' | vm.ℱ t_i]) ω ≤
      -((1/4 : ℝ) * (G.minDegreeAt 0 : ℝ) * φ_j / (24 * Real.sqrt 6 * ψ₀)) *
          ((vm.μ : Measure _)[ind_ℰ | vm.ℱ t_i]) ω := by
    filter_upwards [htower_t', condExp_congr_ae hpullout_t', h_t'_ce, h_K_pullout]
      with ω h1 h2 h3 h4
    calc ((vm.μ : Measure _)[fun ω' => ind t' ω' * δ t' ω' | vm.ℱ t_i]) ω
        = ((vm.μ : Measure _)[(vm.μ : Measure _)[fun ω => ind t' ω * δ t' ω | vm.ℱ t'] | vm.ℱ t_i]) ω := h1
      _ = ((vm.μ : Measure _)[fun ω => ind t' ω * ((vm.μ : Measure _)[δ t' | vm.ℱ t']) ω | vm.ℱ t_i]) ω := h2
      _ ≤ _ := h3
      _ = -((1/4 : ℝ) * (G.minDegreeAt 0 : ℝ) * φ_j / (24 * Real.sqrt 6 * ψ₀)) *
          ((vm.μ : Measure _)[ind_ℰ | vm.ℱ t_i]) ω := h4
  -- Step 8: combine all terms into sum bound
  -- Σ_{j∈Ico t_i N'} E[ind_j * δ_j | ℱ_{t_i}]
  --   = E[ind_{t'} * δ_{t'} | ℱ_{t_i}] + Σ_{j≠t'} E[ind_j * δ_j | ℱ_{t_i}]
  --   ≤ -K * E[ind_ℰ | ℱ_{t_i}] + 0
  have hsum_bound : ∀ᵐ ω ∂(vm.μ : Measure _),
      ∑ j ∈ Finset.Ico t_i N', ((vm.μ : Measure _)[fun ω' => ind j ω' * δ j ω' | vm.ℱ t_i]) ω ≤
      -((1/4 : ℝ) * (G.minDegreeAt 0 : ℝ) * φ_j / (24 * Real.sqrt 6 * ψ₀)) *
          ((vm.μ : Measure _)[ind_ℰ | vm.ℱ t_i]) ω := by
    have hall := (Filter.eventually_all_finset (Finset.Ico t_i N')).mpr h_allterms_le
    filter_upwards [h_t'_bound, hall] with ω h_tp hterms
    have ht'_mem : t' ∈ Finset.Ico t_i N' := Finset.mem_Ico.mpr ⟨ht'_lo, ht'_lt_N'⟩
    have hsplit : ∑ j ∈ Finset.Ico t_i N', ((vm.μ : Measure _)[fun ω' => ind j ω' * δ j ω' | vm.ℱ t_i]) ω =
        ((vm.μ : Measure _)[fun ω' => ind t' ω' * δ t' ω' | vm.ℱ t_i]) ω +
        ∑ j ∈ (Finset.Ico t_i N').erase t', ((vm.μ : Measure _)[fun ω' => ind j ω' * δ j ω' | vm.ℱ t_i]) ω := by
      rw [← Finset.add_sum_erase _ _ ht'_mem]
    have hrest_le : ∑ j ∈ (Finset.Ico t_i N').erase t',
          ((vm.μ : Measure _)[fun ω' => ind j ω' * δ j ω' | vm.ℱ t_i]) ω ≤ 0 :=
      Finset.sum_nonpos fun j hj => hterms j (Finset.mem_of_mem_erase hj)
    calc ∑ j ∈ Finset.Ico t_i N', ((vm.μ : Measure _)[fun ω' => ind j ω' * δ j ω' | vm.ℱ t_i]) ω
        = ((vm.μ : Measure _)[fun ω' => ind t' ω' * δ t' ω' | vm.ℱ t_i]) ω +
          ∑ j ∈ (Finset.Ico t_i N').erase t', ((vm.μ : Measure _)[fun ω' => ind j ω' * δ j ω' | vm.ℱ t_i]) ω := hsplit
      _ ≤ -((1/4 : ℝ) * (G.minDegreeAt 0 : ℝ) * φ_j / (24 * Real.sqrt 6 * ψ₀)) *
          ((vm.μ : Measure _)[ind_ℰ | vm.ℱ t_i]) ω + 0 := add_le_add h_tp hrest_le
      _ = -((1/4 : ℝ) * (G.minDegreeAt 0 : ℝ) * φ_j / (24 * Real.sqrt 6 * ψ₀)) *
          ((vm.μ : Measure _)[ind_ℰ | vm.ℱ t_i]) ω := add_zero _
  -- Step 9: connect sum to condExp of sum, then to psiS(T_next) - ψ₀
  have hcondExp_sum_eq : ∀ᵐ ω ∂(vm.μ : Measure _),
      ((vm.μ : Measure _)[fun ω' => ∑ j ∈ Finset.Ico t_i N', ind j ω' * δ j ω' | vm.ℱ t_i]) ω =
      ∑ j ∈ Finset.Ico t_i N', ((vm.μ : Measure _)[fun ω' => ind j ω' * δ j ω' | vm.ℱ t_i]) ω := by
    filter_upwards [hcondExp_sum_δ] with ω hω
    rw [show ∑ j ∈ Finset.Ico t_i N', ((vm.μ : Measure _)[fun ω' => ind j ω' * δ j ω' | vm.ℱ t_i]) ω =
            (∑ j ∈ Finset.Ico t_i N', (vm.μ : Measure _)[fun ω' => ind j ω' * δ j ω' | vm.ℱ t_i]) ω
          from (Finset.sum_apply ω _ _).symm]
    exact hω
  -- ind_ℰ = the indicator used in the goal statement
  have hind_ℰ_goal_eq : ∀ ω,
      ind_ℰ ω = (if t' < embeddedChainTime G.toTemporalGraph vm Δ (i + 1) ω ∧
        (vm.cutS t' ω : ℝ) ≥ (1/4) * Vol₀ / (1/φ_j) then (1 : ℝ) else 0) := fun ω => rfl
  -- Final assembly
  have hind_ℰ_ae_eq : ind_ℰ =ᵐ[(vm.μ : Measure _)] (fun ω' =>
      if t' < embeddedChainTime G.toTemporalGraph vm Δ (i + 1) ω' ∧
        (vm.cutS t' ω' : ℝ) ≥ (1/4) * Vol₀ / (1/φ_j) then (1:ℝ) else 0) :=
    Filter.Eventually.of_forall (fun ω => hind_ℰ_goal_eq ω)
  filter_upwards [hcondExp_split_ψ₀, hcondExp_split_ti, hcondExp_tele,
      hcondExp_sum_eq, hsum_bound, condExp_congr_ae hind_ℰ_ae_eq]
    with ω hψ₀_split hti_split htele hsum_eq hbound hce_ℰ
  simp only [Pi.sub_apply] at hψ₀_split hti_split
  have hpsi_ti_ω : vm.psiS t_i ω = ψ₀ := hpsi_ti_eq ω
  have h_relate : ((vm.μ : Measure _)[fun ω' => vm.psiS (T_next_fn ω') ω' - ψ₀ | vm.ℱ t_i]) ω =
      ((vm.μ : Measure _)[fun ω' => vm.psiS (T_next_fn ω') ω' - vm.psiS t_i ω' | vm.ℱ t_i]) ω +
      (vm.psiS t_i ω - ψ₀) := by
    rw [hψ₀_split, hti_split]; ring_nf
  have h_ti_zero : vm.psiS t_i ω - ψ₀ = 0 := by rw [hpsi_ti_ω]; ring
  rw [h_relate, h_ti_zero, add_zero]
  calc ((vm.μ : Measure _)[fun ω' => vm.psiS (T_next_fn ω') ω' - vm.psiS t_i ω' | vm.ℱ t_i]) ω
      = ((vm.μ : Measure _)[fun ω' => ∑ j ∈ Finset.Ico t_i N', ind j ω' * δ j ω' | vm.ℱ t_i]) ω := htele
    _ = ∑ j ∈ Finset.Ico t_i N', ((vm.μ : Measure _)[fun ω' => ind j ω' * δ j ω' | vm.ℱ t_i]) ω := hsum_eq
    _ ≤ -((1/4 : ℝ) * (G.minDegreeAt 0 : ℝ) * φ_j / (24 * Real.sqrt 6 * ψ₀)) *
            ((vm.μ : Measure _)[ind_ℰ | vm.ℱ t_i]) ω := hbound
    _ = -((1/4 : ℝ) * (G.minDegreeAt 0 : ℝ) * φ_j / (24 * Real.sqrt 6 * ψ₀)) *
            ((vm.μ : Measure _)[fun ω' =>
              if t' < embeddedChainTime G.toTemporalGraph vm Δ (i + 1) ω' ∧
                (vm.cutS t' ω' : ℝ) ≥ (1/4) * Vol₀ / (1/φ_j) then (1:ℝ) else 0 |
              vm.ℱ t_i]) ω := by rw [hce_ℰ]

/-- \label{lem:pot-change-vol-constant-combine}

**Case 2 helper** (small-μ path). Extracts the small-μ branch of
`potential_decrease_stable_interval_combined_unconditional`: on the complement
of Case 1, where the caller supplies the edge-sum upper bound `hedge_sum_small`
(shape `E[∑ e_j | ℱ_{t_i}] ≤ μ_param·Vol(s₀)/Δ`), together with the
`Case2Hypotheses` bundle providing stability (`ν = 1/8`), integrability, exit
and boundedness hypotheses, the classical paper argument (§3.1 Case 2) applies
`prob_good_event` with `Δ = 1/φ_j` and a cut fraction `η` chosen so that
`2ν + μ_param/(1−η) ≤ 1/2`, and combines it with
`potential_decrease_one_step` on the good event ℰ.

-/
theorem potential_decrease_stable_interval_case2
    {Ω : Type*} [MeasurableSpace Ω]
    (G : TemporalGraphFixedDegree V)
    (vm : G.VoterModelAbstract 2 Ω)
    -- Fixed initial set s₀ ≠ ∅ and realized time t_i
    (s₀ : Finset V) (hs₀ : s₀.Nonempty)
    (t_i : ℕ)
    -- Embedded chain parameters
    (Δ : ℕ → ℕ) (i : ℕ)
    (hT_val : ∀ ω, embeddedChainTime G.toTemporalGraph vm Δ i ω = t_i)
    (hS_init : ∀ ω, vm.S t_i ω = s₀)
    -- φ_j > 0, φ_j ≤ 1
    (φ_j : ℝ) (hφ_j : 0 < φ_j)
    -- Well-formedness: t_i lies within the cap for interval i+1
    (hT_cap : t_i ≤ (∑ k ∈ Finset.range (i + 1), Δ k) - 1)
    -- Good-step witness at time `t'`
    (t' : ℕ) (ht'_lo : t_i ≤ t')
    (hgood_step : (G.edgesBetween t' s₀ (Finset.univ \ s₀) : ℝ) ≥
        φ_j * ((G.snapshot t_i).volume s₀ : ℝ))
    -- Case 2 premise: hedge_sum upper bound E[Σ e_j | ℱ_{t_i}] ≤ μ_param·Vol/Δ,
    -- with μ_param matching the parameter choice for `prob_good_event` below.
    (hedge_sum_small : ∀ᵐ ω ∂(vm.μ : Measure _),
      ((vm.μ : Measure _)[fun ω' => ∑ j ∈ Finset.Icc t_i (embeddedChainTime G.toTemporalGraph vm Δ (i + 1) ω' - 1),
        (vm.cutS j ω' : ℝ) | vm.ℱ t_i]) ω
        ≤ (1 / 8 : ℝ) * ((G.snapshot t_i).volume s₀ : ℝ) / (1 / φ_j))
    -- Stability + integrability bundle. F=Set.univ because L70 is the non-fiber
    -- version; F-restricted callers go through L79.
    (hC2 : Case2Hypotheses G.toTemporalGraph vm s₀ t_i (embeddedChainTime G.toTemporalGraph vm Δ (i + 1)) t' φ_j Set.univ) :
    ∀ᵐ ω ∂(vm.μ : Measure _),
      ((vm.μ : Measure _)[fun ω' => vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (i + 1) ω') ω'
        - G.potential t_i s₀ | vm.ℱ t_i]) ω
        ≤ -((G.minDegreeAt 0 : ℝ) * φ_j)
          / (192 * Real.sqrt 6 * G.potential t_i s₀) := by
  -- Proof strategy (paper §3.1 Case 2, lines 483–536):
  -- 1. Apply `prob_good_event` with Δ = 1/φ_j and parameters (ν, μ_param, η)
  --    satisfying `2ν + μ_param/(1−η) ≤ 1/2`.
  --    Conclusion: `E[𝟙_ℰ | ℱ_{t_i}] ≥ 1/2` where
  --    `ℰ = {T_next > t'} ∩ {cutS(t') ≥ η·Vol/(1/φ_j) = η·φ_j·Vol}`.
  -- 2. Apply `potential_decrease_one_step` at `t'` on ℰ together with stability
  --    ψ(S_{t'}) ≤ √(3/2)·ψ(s₀), obtaining a single-step bound
  --      E[ψ(S_{t'+1}) - ψ(S_{t'}) | ℱ_{t'}] ≤ -η·d_min·φ_j/(24√6·ψ(s₀)).
  -- 3. Telescope over [t_i, T_{i+1}) using the one-step bound: all steps outside
  --    {t'} have conditional expectation ≤ 0, so the telescope sum is bounded by
  --    the t'-term alone, weighted by 𝟙_ℰ; integrating via tower gives
  --      E[ψ(T_next) - ψ(s₀) | ℱ_{t_i}]
  --        ≤ -η·d_min·φ_j/(24√6·ψ(s₀)) · E[𝟙_ℰ | ℱ_{t_i}].
  -- 4. Combine with P(ℰ | ℱ_{t_i}) ≥ 1/2 to reach the target bound.
  --
  -- Setup: abbreviations and basic positivity facts.
  set Vol₀ : ℝ := ((G.snapshot t_i).volume s₀ : ℝ) with hVol₀_def
  set ψ₀ : ℝ := G.potential t_i s₀ with hψ₀_def
  have hΔ_pos : (0 : ℝ) < 1 / φ_j := by positivity
  have hφ_ne : φ_j ≠ 0 := ne_of_gt hφ_j
  have hVol_pos : (0 : ℝ) < Vol₀ := by
    obtain ⟨v, hv⟩ := hs₀
    have hd := G.degrees_pos v t_i
    have h_nat : 0 < (G.snapshot t_i).volume s₀ :=
      Nat.lt_of_lt_of_le hd (Finset.single_le_sum (f := fun v => (G.snapshot t_i).degree v)
        (fun v _ => Nat.zero_le _) hv)
    exact Nat.cast_pos.mpr h_nat
  -- Step 1: assemble the prob_good_event call.
  -- Rewrite hedge_sum_small to the exact form `≤ μ_param * Vol₀ / Δ` (Δ = 1/φ_j).
  have hedge_sum_pg : ∀ᵐ ω ∂(vm.μ : Measure _),
      ((vm.μ : Measure _)[fun ω' => ∑ j ∈ Finset.Icc t_i (embeddedChainTime G.toTemporalGraph vm Δ (i + 1) ω' - 1),
        (vm.cutS j ω' : ℝ) | vm.ℱ t_i]) ω
        ≤ (1 / 8 : ℝ) * Vol₀ / (1 / φ_j) := hedge_sum_small
  -- Rewrite hgood_step similarly: `e_{t'}(s₀,V\s₀) ≥ Vol₀ / (1/φ_j) = φ_j·Vol₀`.
  have hgood_pg : (G.edgesBetween t' s₀ (univ \ s₀) : ℝ) ≥ Vol₀ / (1 / φ_j) := by
    have hrw : Vol₀ / (1 / φ_j) = φ_j * Vol₀ := by field_simp
    rw [hrw]; exact hgood_step
  -- S_{t_i} = s₀ holds pointwise, hence a.e.
  have hS_init_ae : ∀ᵐ ω ∂(vm.μ : Measure _), vm.S t_i ω = s₀ := ae_of_all _ hS_init
  -- Measurability of S and stopping-time property of T_next.
  have hS_meas : ∀ t, @Measurable Ω (Finset V) (vm.ℱ t) ⊤ (vm.S t) := fun t =>
    (measurable_of_countable (fun A => VoterModel.minoritySet G.toTemporalGraph t A)).comp
      (vm.A_stronglyAdapted t).measurable
  have hT_stop : IsStoppingTime vm.ℱ
      (fun ω => (embeddedChainTime G.toTemporalGraph vm Δ (i + 1) ω : ℕ∞)) :=
    embeddedChainTime_isStoppingTime G.toTemporalGraph vm Δ hS_meas (i + 1)
  obtain ⟨N, hN⟩ := hC2.bound
  -- Parameter inequality `2ν + μ_param/(1−η) ≤ 1/2` for `prob_good_event`.
  have h_param : (2 : ℝ) * (1 / 8) + (1 / 8) / (1 - (1 / 4 : ℝ)) ≤ 1 / 2 := by norm_num
  -- T_{i+1} ω > t_i pointwise (from hT_val + hT_cap + embeddedChainTime_strictMono).
  have hT_gt : ∀ ω, t_i < embeddedChainTime G.toTemporalGraph vm Δ (i + 1) ω := by
    intro ω
    have hle : embeddedChainTime G.toTemporalGraph vm Δ i ω ≤ (∑ k ∈ Finset.range (i + 1), Δ k) - 1 :=
      hT_val ω ▸ hT_cap
    have hmono := embeddedChainTime_strictMono G.toTemporalGraph vm Δ i ω hle
    linarith [hT_val ω]
  -- T_{i+1} ω > 0 follows from t_i ≥ 0 + hT_gt.
  have hT_pos : ∀ ω, 0 < embeddedChainTime G.toTemporalGraph vm Δ (i + 1) ω :=
    fun ω => Nat.lt_of_le_of_lt (Nat.zero_le _) (hT_gt ω)
  -- Bridge F-restricted-to-univ a.e. hypotheses to global a.e.
  have hstable_global : ∀ᵐ ω ∂(vm.μ : Measure _),
      ((vm.μ : Measure _)[fun ω' => |((G.snapshot (embeddedChainTime G.toTemporalGraph vm Δ (i + 1) ω')).volume
            (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (i + 1) ω') ω') : ℝ)
        - ((G.snapshot t_i).volume s₀ : ℝ)| | vm.ℱ t_i]) ω
        < (1 / 8 : ℝ) * ((G.snapshot t_i).volume s₀ : ℝ) := by
    have := hC2.stable
    rwa [Measure.restrict_univ] at this
  have hexit_global : ∀ᵐ ω ∂(vm.μ : Measure _), embeddedChainTime G.toTemporalGraph vm Δ (i + 1) ω ≤ t' →
      (1 / 2 : ℝ) * ((G.snapshot t_i).volume s₀ : ℝ) ≤
        |((G.snapshot (embeddedChainTime G.toTemporalGraph vm Δ (i + 1) ω)).volume
            (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (i + 1) ω) ω) : ℝ)
          - ((G.snapshot t_i).volume s₀ : ℝ)| := by
    have := hC2.exit
    rwa [Measure.restrict_univ] at this
  have h_prob_good : ∀ᵐ ω ∂(vm.μ : Measure _),
      ((vm.μ : Measure _)[fun ω' =>
        if t' < embeddedChainTime G.toTemporalGraph vm Δ (i + 1) ω'
          ∧ (vm.cutS t' ω' : ℝ) ≥ (1 / 4 : ℝ) * Vol₀ / (1 / φ_j)
        then (1 : ℝ) else 0 | vm.ℱ t_i]) ω ≥ 1 / 2 :=
    prob_good_event G vm (embeddedChainTime G.toTemporalGraph vm Δ (i + 1)) hT_stop s₀ hs₀ t_i
      (1 / φ_j) hΔ_pos (1 / 8) hstable_global
      (1 / 4) (1 / 8) (by norm_num) h_param
      t' ht'_lo hgood_pg hedge_sum_pg hS_init_ae hexit_global hC2.devInt hC2.sumAbsInt
      hT_pos N hN hC2.deltaInt hC2.cutInt
  -- Step 2 + 3 (telescope + one-step bound on ℰ): the per-step→aggregate conversion.
  -- The body of this `have` has been extracted to `case2_telescope_bound` purely to
  -- keep this theorem within the default heartbeat budget (the original inline proof
  -- timed out around the `htower_t'` tower step).
  have h_telescope_bound : ∀ᵐ ω ∂(vm.μ : Measure _),
      ((vm.μ : Measure _)[fun ω' => vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (i + 1) ω') ω' - ψ₀ | vm.ℱ t_i]) ω
        ≤ -((1 / 4 : ℝ) * (G.minDegreeAt 0 : ℝ) * φ_j / (24 * Real.sqrt 6 * ψ₀))
          * ((vm.μ : Measure _)[fun ω' =>
              if t' < embeddedChainTime G.toTemporalGraph vm Δ (i + 1) ω'
                ∧ (vm.cutS t' ω' : ℝ) ≥ (1 / 4 : ℝ) * Vol₀ / (1 / φ_j)
              then (1 : ℝ) else 0 | vm.ℱ t_i]) ω :=
    case2_telescope_bound G vm s₀ hs₀ t_i Δ i hT_val hS_init φ_j hφ_j hVol_pos
      t' ht'_lo hT_stop N hN hT_gt
  -- Step 4: combine h_prob_good (P_ℰ ≥ 1/2) with h_telescope_bound to reach the target.
  filter_upwards [h_prob_good, h_telescope_bound] with ω h_prob h_tel
  -- Abbreviate the P_ℰ conditional expectation
  set P_ℰ : ℝ :=
    ((vm.μ : Measure _)[fun ω' =>
      if t' < embeddedChainTime G.toTemporalGraph vm Δ (i + 1) ω'
        ∧ (vm.cutS t' ω' : ℝ) ≥ (1 / 4 : ℝ) * Vol₀ / (1 / φ_j)
      then (1 : ℝ) else 0 | vm.ℱ t_i]) ω with hP_ℰ_def
  -- Nonnegativity of the coefficient factor (d_min ≥ 0, φ_j > 0, √6 > 0, ψ₀ ≥ 0).
  have hdmin : (0 : ℝ) ≤ (G.minDegreeAt 0 : ℝ) := Nat.cast_nonneg _
  have hsq6_pos : (0 : ℝ) < Real.sqrt 6 := Real.sqrt_pos.mpr (by norm_num)
  have hψ₀_nn : (0 : ℝ) ≤ ψ₀ := by
    show (0 : ℝ) ≤ Real.sqrt _
    exact Real.sqrt_nonneg _
  -- Coefficient ≥ 0
  have hcoeff_nn : (0 : ℝ) ≤
      (1 / 4 : ℝ) * (G.minDegreeAt 0 : ℝ) * φ_j / (24 * Real.sqrt 6 * ψ₀) := by
    have hnum : (0 : ℝ) ≤ (1 / 4 : ℝ) * (G.minDegreeAt 0 : ℝ) * φ_j := by
      have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) hdmin) (le_of_lt hφ_j)
      linarith
    have hden : (0 : ℝ) ≤ 24 * Real.sqrt 6 * ψ₀ := by
      have : (0 : ℝ) ≤ 24 * Real.sqrt 6 := by positivity
      exact mul_nonneg this hψ₀_nn
    exact div_nonneg hnum hden
  -- From h_prob: P_ℰ ≥ 1/2, so -coeff·P_ℰ ≤ -coeff·(1/2).
  have hstep1 :
      -((1 / 4 : ℝ) * (G.minDegreeAt 0 : ℝ) * φ_j / (24 * Real.sqrt 6 * ψ₀)) * P_ℰ
        ≤ -((1 / 4 : ℝ) * (G.minDegreeAt 0 : ℝ) * φ_j / (24 * Real.sqrt 6 * ψ₀)) * (1 / 2) := by
    have := mul_le_mul_of_nonneg_left h_prob hcoeff_nn
    -- `hcoeff_nn * P_ℰ ≥ hcoeff_nn * (1/2)` (mul-le-mul with coeff_nn on left, P ≥ 1/2)
    -- We need: -coeff·P ≤ -coeff·(1/2), i.e. coeff·(1/2) ≤ coeff·P. That's `this`.
    linarith
  -- Chain h_tel ≤ -coeff·P ≤ -coeff·(1/2) and rewrite as the target bound.
  have h_chain :
      ((vm.μ : Measure _)[fun ω' => vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (i + 1) ω') ω' - ψ₀ | vm.ℱ t_i]) ω
        ≤ -((1 / 4 : ℝ) * (G.minDegreeAt 0 : ℝ) * φ_j / (24 * Real.sqrt 6 * ψ₀)) * (1 / 2) :=
    le_trans h_tel hstep1
  -- Case split on ψ₀ = 0 or > 0:
  by_cases hψ₀_zero : ψ₀ = 0
  · -- When ψ₀ = 0, both sides degenerate to 0 (division by 0 is 0).
    simp only [hψ₀_zero, mul_zero, div_zero, neg_zero, zero_mul] at h_chain ⊢
    exact h_chain
  · have hψ₀_pos : (0 : ℝ) < ψ₀ := lt_of_le_of_ne hψ₀_nn (Ne.symm hψ₀_zero)
    have hsq6_ne : Real.sqrt 6 ≠ 0 := ne_of_gt hsq6_pos
    -- Rewrite the RHS of h_chain as the target bound.
    have h_rhs_eq :
        -((1 / 4 : ℝ) * (G.minDegreeAt 0 : ℝ) * φ_j / (24 * Real.sqrt 6 * ψ₀)) * (1 / 2)
          = -((G.minDegreeAt 0 : ℝ) * φ_j) / (192 * Real.sqrt 6 * ψ₀) := by
      rw [neg_div]
      field_simp
      ring
    rw [h_rhs_eq] at h_chain
    exact h_chain

/-- \label{lem:pot-change-vol-constant-combine}

Unconditional version of `potential_decrease_stable_interval_combined`: same
conclusion as `combined`, but does **not** require the edge-sum hypothesis
`hedge_sum`. Instead it takes a `hgood_step` witness (a time `t'` in the
interval with `e_{t'}(s₀, V\s₀) ≥ φ_j · Vol(s₀)`) together with a `Case2Hypotheses`
bundle, and performs an internal Case 1 / Case 2 dispatch following §3.1.

- **Case 1** (μ = E[Σ e_j] > φ_j · Vol(s₀) / 4 a.e.): delegates to
  `potential_decrease_stable_interval_combined`.
- **Case 2** (otherwise, i.e. `¬hLarge`): delegates to
  `potential_decrease_stable_interval_case2`.

-/
theorem potential_decrease_stable_interval_combined_unconditional
    {Ω : Type*} [MeasurableSpace Ω]
    (G : TemporalGraphFixedDegree V)
    (vm : G.VoterModelAbstract 2 Ω)
    -- Fixed initial set s₀ ≠ ∅ and realized time t_i
    (s₀ : Finset V) (hs₀ : s₀.Nonempty)
    (t_i : ℕ)
    -- Embedded chain parameters: T_{i+1} = embeddedChainTime G.toTemporalGraph vm Δ (i+1)
    (Δ : ℕ → ℕ) (i : ℕ)
    -- T_i realizes to t_i pointwise
    (hT_val : ∀ ω, embeddedChainTime G.toTemporalGraph vm Δ i ω = t_i)
    -- S_{t_i} = s₀ pointwise
    (hS_init : ∀ ω, vm.S t_i ω = s₀)
    -- φ_j: lower bound on interval conductance
    (φ_j : ℝ) (hφ_j : 0 < φ_j)
    -- Well-formedness: t_i lies within the cap for interval i+1
    (hT_cap : t_i ≤ (∑ j ∈ Finset.range (i + 1), Δ j) - 1)
    -- Good-step witness: ∃ t' ∈ [t_i, cap] with e_{t'}(s₀, V\s₀) ≥ φ_j·Vol(s₀)
    (hgood_step : ∃ t', t_i ≤ t' ∧ t' ≤ (∑ j ∈ Finset.range (i + 1), Δ j) - 1 ∧
        (G.edgesBetween t' s₀ (Finset.univ \ s₀) : ℝ) ≥
          φ_j * ((G.snapshot t_i).volume s₀ : ℝ))
    -- Case 2 hedge-sum UPPER bound (shape μ_param·Vol/Δ with Δ = 1/φ_j), supplied
    -- by the caller. In the paper this is derivable from stability + `¬hLarge`;
    -- here we thread it as an explicit premise so the dispatch stays clean.
    (hedge_sum_small : ∀ᵐ ω ∂(vm.μ : Measure _),
      ((vm.μ : Measure _)[fun ω' => ∑ j ∈ Finset.Icc t_i (embeddedChainTime G.toTemporalGraph vm Δ (i + 1) ω' - 1),
        (vm.cutS j ω' : ℝ) | vm.ℱ t_i]) ω
        ≤ (1 / 8 : ℝ) * ((G.snapshot t_i).volume s₀ : ℝ) / (1 / φ_j))
    -- Case 2 stability+integrability bundle, indexed by a concrete good-step time;
    -- F = Set.univ since this is the non-fiber wrapper.
    (hC2 : ∀ t', t_i ≤ t' → t' ≤ (∑ j ∈ Finset.range (i + 1), Δ j) - 1 →
        Case2Hypotheses G.toTemporalGraph vm s₀ t_i (embeddedChainTime G.toTemporalGraph vm Δ (i + 1)) t' φ_j Set.univ) :
    -- Conclusion: E[ψ(S_{T_{i+1}}) − ψ(s₀) | ℱ_{t_i}] ≤ −d_min·φ_j / (192√6·ψ(s₀))
    ∀ᵐ ω ∂(vm.μ : Measure _),
      ((vm.μ : Measure _)[fun ω' => vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (i + 1) ω') ω'
        - G.potential t_i s₀ | vm.ℱ t_i]) ω
        ≤ -((G.minDegreeAt 0 : ℝ) * φ_j)
          / (192 * Real.sqrt 6 * G.potential t_i s₀) := by
  -- Potential-level Case 1 / Case 2 dispatch (paper §3.1, lines 483–536).
  by_cases hLarge : ∀ᵐ ω ∂(vm.μ : Measure _),
      ((vm.μ : Measure _)[fun ω' => ∑ j ∈ Finset.Icc t_i (embeddedChainTime G.toTemporalGraph vm Δ (i + 1) ω' - 1),
        (vm.cutS j ω' : ℝ) | vm.ℱ t_i]) ω
        > φ_j * ((G.snapshot t_i).volume s₀ : ℝ) / 4
  · -- Case 1: delegate to `combined`, then relax its sharper constant to the
    -- Case 2 constant.
    have hcase1 := potential_decrease_stable_interval_combined G vm s₀ hs₀ t_i Δ i
      hT_val hS_init φ_j hφ_j hT_cap hLarge
    have hψ_nn : (0 : ℝ) ≤ G.potential t_i s₀ := Real.sqrt_nonneg _
    have hnum_nn : (0 : ℝ) ≤ (G.minDegreeAt 0 : ℝ) * φ_j :=
      mul_nonneg (Nat.cast_nonneg _) hφ_j.le
    have hbound :
        -((G.minDegreeAt 0 : ℝ) * φ_j) / (96 * Real.sqrt 6 * G.potential t_i s₀) ≤
        -((G.minDegreeAt 0 : ℝ) * φ_j) / (192 * Real.sqrt 6 * G.potential t_i s₀) := by
      rcases eq_or_lt_of_le hψ_nn with hψ_eq | hψ_pos
      · simp [← hψ_eq]
      · have hsq6_pos : (0 : ℝ) < Real.sqrt 6 := Real.sqrt_pos.mpr (by norm_num)
        have h96_pos : (0 : ℝ) < 96 * Real.sqrt 6 * G.potential t_i s₀ :=
          mul_pos (by positivity) hψ_pos
        have hdenom_le : (96 : ℝ) * Real.sqrt 6 * G.potential t_i s₀ ≤
            192 * Real.sqrt 6 * G.potential t_i s₀ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by norm_num : (96 : ℝ) ≤ 192) hsq6_pos.le)
            hψ_nn
        rw [neg_div, neg_div, neg_le_neg_iff]
        exact div_le_div_of_nonneg_left hnum_nn h96_pos hdenom_le
    filter_upwards [hcase1] with ω hω
    exact le_trans hω hbound
  · -- Case 2 (small-μ path): delegate to `_case2` helper.
    obtain ⟨t', ht'_lo, ht'_hi, hgood⟩ := hgood_step
    exact potential_decrease_stable_interval_case2 G vm s₀ hs₀ t_i Δ i
      hT_val hS_init φ_j hφ_j hT_cap t' ht'_lo hgood
      hedge_sum_small (hC2 t' ht'_lo ht'_hi)

/-- \label{stmt:potential-decrease-stable-interval-combined-unconditional-on-fiber}

**Fiber-relative `potential_decrease_stable_interval_combined_unconditional`**
(Lean-only refactor enabling `psi_down_drift_stable_on_fiber` = L76).

Same as `potential_decrease_stable_interval_combined_unconditional`, except
the deterministic-fiber hypotheses `hT_val : ∀ω, T_j ω = t_j` and
`hS_init : ∀ω, vm.S t_j ω = s_j` are restricted to a measurable
`F ∈ vm.ℱ t_j` (hypotheses `hF_T`, `hF_S`); the conclusion is the a.e.
conditional-expectation bound on `μ.restrict F`.

**Proof.** Composes L82 (`prob_good_event_on_fiber`, parameters
`ν = 1/8, η = 1/2, μ_param = 1/8`, so `2ν + μ/(1−η) = 1/2 ≤ 1/2`) with L81
(`potential_decrease_stable_interval_large_on_fiber`, `μ_param = 1, Δ = 8/φ_j`):
the good event delivers `E[Σ cutS | ℱ_{t_j}] ≥ (1/2)·φ_j·Vol·(1/2) = (1/4)·φ_j·Vol
> φ_j·Vol/8` (strict), which L81 converts into the ψ-drift bound with
constant `24·√6·(8/φ_j) = (192/φ_j)·√6` — the edge-sum threshold and
conclusion constant of `potential_decrease_stable_interval_combined_unconditional`.

L76 (`psi_down_drift_stable_on_fiber`) delegates to this via
`setIntegral_condExp` + `setIntegral_mono_ae_restrict` + `setIntegral_const`,
the same finishing pattern L75/L77/L78 use. -/
theorem potential_decrease_stable_interval_combined_unconditional_on_fiber
    {Ω : Type*} [MeasurableSpace Ω]
    (G : TemporalGraphFixedDegree V)
    (vm : G.VoterModelAbstract 2 Ω)
    -- Fixed value s_j ≠ ∅ at realized time t_j
    (s_j : Finset V) (hs_j : s_j.Nonempty) (t_j : ℕ)
    -- Embedded chain parameters
    (Δ : ℕ → ℕ) (j : ℕ)
    -- Fiber F: measurable in ℱ_{t_j}, with T_j = t_j and S_{t_j} = s_j on F
    (F : Set Ω)
    (hF_meas : MeasurableSet[vm.ℱ t_j] F)
    (hF_T : ∀ ω ∈ F, embeddedChainTime G.toTemporalGraph vm Δ j ω = t_j)
    (hF_S : ∀ ω ∈ F, vm.S t_j ω = s_j)
    -- φ_j: lower bound on interval conductance
    (φ_j : ℝ) (hφ_j : 0 < φ_j)
    -- Well-formedness: t_j lies within the cap for interval j+1
    (hT_cap : t_j ≤ (∑ k ∈ Finset.range (j + 1), Δ k) - 1)
    -- Good-step witness: ∃ t' ∈ [t_j, cap] with e_{t'}(s_j, V\s_j) ≥ φ_j·Vol(s_j)
    (hgood_step : ∃ t', t_j ≤ t' ∧ t' ≤ (∑ k ∈ Finset.range (j + 1), Δ k) - 1 ∧
        (G.edgesBetween t' s_j (Finset.univ \ s_j) : ℝ) ≥
          φ_j * ((G.snapshot t_j).volume s_j : ℝ))
    -- F-restricted hedge-sum UPPER bound at the Case-2 dichotomy threshold.
    (hedge_sum_small : ∀ᵐ ω ∂((vm.μ : Measure _).restrict F),
      ((vm.μ : Measure _)[fun ω' => ∑ k ∈ Finset.Icc t_j (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω' - 1),
        (vm.cutS k ω' : ℝ) | vm.ℱ t_j]) ω
        ≤ (1 / 8 : ℝ) * ((G.snapshot t_j).volume s_j : ℝ) / (1 / φ_j))
    -- Stability + integrability bundle, indexed by a concrete good-step time.
    (hC2 : ∀ t', t_j ≤ t' → t' ≤ (∑ k ∈ Finset.range (j + 1), Δ k) - 1 →
        Case2Hypotheses G.toTemporalGraph vm s_j t_j (embeddedChainTime G.toTemporalGraph vm Δ (j + 1)) t' φ_j F) :
    -- Conclusion: a.e. on μ.restrict F,
    --   E[ψ(S_{T_{j+1}}) − ψ(t_j, s_j) | ℱ_{t_j}] ≤ −d_min·φ_j / (192·√6·ψ(t_j, s_j))
    ∀ᵐ ω ∂((vm.μ : Measure _).restrict F),
      ((vm.μ : Measure _)[fun ω' => vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω') ω'
        - G.potential t_j s_j | vm.ℱ t_j]) ω
        ≤ -((G.minDegreeAt 0 : ℝ) * φ_j)
          / (192 * Real.sqrt 6 * G.potential t_j s_j) := by
  classical
  -- Strategy: compose L82 + L81. L82 provides the good-event probability
  -- bound `E[𝟙_ℰ | ℱ_{t_j}] ≥ 1/2` a.e. on F, where ℰ includes the strict
  -- `t' < T_next` clause and the cut-bound `cutS t' ≥ (1/2)·Vol·φ_j`. The
  -- tower property + cutS ≥ 0 deliver
  --   E[Σ cutS | ℱ_{t_j}] ≥ (1/2)·Vol·φ_j · (1/2) = (1/4)·φ_j·Vol > φ_j·Vol/8
  -- (strict). Feeding this into L81 (μ_param=1, Δ=8/φ_j) yields the target
  -- bound `-d_min·φ_j/(192·√6·ψ)`.
  set Vol₀ : ℝ := ((G.snapshot t_j).volume s_j : ℝ) with hVol₀_def
  set ψ₀ : ℝ := G.potential t_j s_j with hψ₀_def
  have hVol_pos : (0 : ℝ) < Vol₀ := by
    obtain ⟨v, hv⟩ := hs_j
    exact Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (G.degrees_pos v t_j)
      (Finset.single_le_sum (f := fun v => (G.snapshot t_j).degree v)
        (fun v _ => Nat.zero_le _) hv))
  have hVol_nn : (0 : ℝ) ≤ Vol₀ := le_of_lt hVol_pos
  obtain ⟨t', ht'_lo, ht'_hi, hgood⟩ := hgood_step
  have hC2_t' := hC2 t' ht'_lo ht'_hi
  -- Stopping-time auxiliaries
  have hS_meas : ∀ t, @Measurable Ω (Finset V) (vm.ℱ t) ⊤ (vm.S t) := fun t =>
    (measurable_of_countable (fun A => VoterModel.minoritySet G.toTemporalGraph t A)).comp
      (vm.A_stronglyAdapted t).measurable
  have hT_stop : IsStoppingTime vm.ℱ
      (fun ω => (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω : ℕ∞)) :=
    embeddedChainTime_isStoppingTime G.toTemporalGraph vm Δ hS_meas (j + 1)
  obtain ⟨N, hN⟩ := hC2_t'.bound
  have hF_meas_top : MeasurableSet F := vm.ℱ.le t_j _ hF_meas
  -- Step 1: apply L82 (`prob_good_event_on_fiber`) with parameters
  --   ν = 1/8, η = 1/2, μ_param = 1/8, Δ_L82 = 1/φ_j.
  -- Verify `2ν + μ/(1−η) = 1/4 + (1/8)/(1/2) = 1/2 ≤ 1/2`.
  have hΔ_L82 : (0 : ℝ) < 1 / φ_j := by positivity
  have h_param : (2 : ℝ) * (1 / 8) + (1 / 8) / (1 - (1 / 2 : ℝ)) ≤ 1 / 2 := by norm_num
  -- Rewrite hgood: `e_{t'}(s_j, V\s_j) ≥ φ_j·Vol = Vol/(1/φ_j)`.
  have hgood_pg : (G.edgesBetween t' s_j (Finset.univ \ s_j) : ℝ) ≥ Vol₀ / (1 / φ_j) := by
    have hrw : Vol₀ / (1 / φ_j) = φ_j * Vol₀ := by field_simp
    rw [hrw]; exact hgood
  -- Rewrite hedge_sum_small to L82's input form `≤ μ·Vol/Δ` with μ=1/8, Δ=1/φ_j.
  -- Already F-restricted, so no need to restrict.
  have hedge_sum_pg : ∀ᵐ ω ∂((vm.μ : Measure _).restrict F),
      ((vm.μ : Measure _)[fun ω' => ∑ k ∈ Finset.Icc t_j (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω' - 1),
        (vm.cutS k ω' : ℝ) | vm.ℱ t_j]) ω
        ≤ (1 / 8 : ℝ) * Vol₀ / (1 / φ_j) :=
    hedge_sum_small
  -- hC2_t'.stable, hC2_t'.exit are already F-restricted (∀ᵐ ∂ (vm.μ : Measure _).restrict F).
  have hstable_F := hC2_t'.stable
  have hT_exit_F := hC2_t'.exit
  -- Apply L82. Construct `hT_pos : ∀ ω, 0 < T_{j+1} ω` globally (no fiber needed):
  -- `T_{j+1} ω = volumeExcursionTime G.toTemporalGraph vm (T_j ω) cap ω`, and this is ≥ 1 always
  -- (either `T_j ω ≤ cap` and `lt_volumeExcursionTime` applies, or `T_j ω > cap`
  -- so the candidates set is empty and vET = cap + 1 ≥ 1).
  have hT_pos : ∀ ω, 0 < embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω := by
    intro ω
    show 0 < volumeExcursionTime G.toTemporalGraph vm (embeddedChainTime G.toTemporalGraph vm Δ j ω)
        ((∑ k ∈ Finset.range (j + 1), Δ k) - 1) ω
    set t₀ := embeddedChainTime G.toTemporalGraph vm Δ j ω
    set cap := (∑ k ∈ Finset.range (j + 1), Δ k) - 1
    by_cases h : t₀ ≤ cap
    · exact Nat.lt_of_le_of_lt (Nat.zero_le _) (lt_volumeExcursionTime G.toTemporalGraph vm t₀ cap ω h)
    · -- t₀ > cap: Icc t₀ cap is empty so candidates is empty, vET = cap + 1 ≥ 1
      push Not at h
      unfold volumeExcursionTime
      dsimp only
      have hIcc_empty : Finset.Icc t₀ cap = ∅ := Finset.Icc_eq_empty (by omega)
      have hcand_empty : ((Finset.Icc t₀ cap).filter fun t =>
          2 * (G.snapshot t).volume (vm.S t ω) <
            (G.snapshot t₀).volume (vm.S t₀ ω) ∨
          3 * (G.snapshot t₀).volume (vm.S t₀ ω) <
            2 * (G.snapshot t).volume (vm.S t ω)) = ∅ := by
        rw [hIcc_empty]; rfl
      rw [hcand_empty]
      simp only [Finset.not_nonempty_empty, ↓reduceDIte]
      omega
  have h_prob_good : ∀ᵐ ω ∂((vm.μ : Measure _).restrict F),
      ((vm.μ : Measure _)[fun ω' =>
        if t' < embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω'
          ∧ (vm.cutS t' ω' : ℝ) ≥ (1 / 2 : ℝ) * Vol₀ / (1 / φ_j)
        then (1 : ℝ) else 0 | vm.ℱ t_j]) ω ≥ 1 / 2 :=
    prob_good_event_on_fiber G vm (embeddedChainTime G.toTemporalGraph vm Δ (j + 1)) hT_stop
      s_j hs_j t_j (1 / φ_j) hΔ_L82 (1 / 8) F hF_meas hstable_F
      (1 / 2) (1 / 8) (by norm_num) h_param
      t' ht'_lo hgood_pg hedge_sum_pg hF_S hT_exit_F hC2_t'.devInt hC2_t'.sumAbsInt
      hT_pos N hN hC2_t'.deltaInt hC2_t'.cutInt
  -- Step 2: derive `E[Σ cutS | ℱ_{t_j}] > 1·Vol/(8/φ_j)` a.e. on F.
  -- Abbreviate the good-event indicator function.
  set indℰ : Ω → ℝ := fun ω' =>
    if t' < embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω'
      ∧ (vm.cutS t' ω' : ℝ) ≥ (1 / 2 : ℝ) * Vol₀ / (1 / φ_j)
    then (1 : ℝ) else 0 with hindℰ_def
  -- Pointwise bound: Σ cutS ≥ (1/2)·φ_j·Vol · 𝟙_ℰ globally.
  have h_pw_sum :
      ∀ ω', (1 / 2 : ℝ) * φ_j * Vol₀ * indℰ ω' ≤
        ∑ k ∈ Finset.Icc t_j (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω' - 1),
          (vm.cutS k ω' : ℝ) := by
    intro ω'
    by_cases hℰ : t' < embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω' ∧
        (vm.cutS t' ω' : ℝ) ≥ (1 / 2 : ℝ) * Vol₀ / (1 / φ_j)
    · -- On ℰ: t' lies in Icc t_j (T_next-1), so the t'-summand is ≥ (1/2)·φ_j·Vol.
      simp only [indℰ, if_pos hℰ, mul_one]
      obtain ⟨ht'_lt, hcut_ge⟩ := hℰ
      have ht'_in : t' ∈ Finset.Icc t_j (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω' - 1) := by
        refine Finset.mem_Icc.mpr ⟨ht'_lo, ?_⟩
        have hT_pos : 1 ≤ embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω' := by omega
        omega
      have h_t'_term : (1 / 2 : ℝ) * φ_j * Vol₀ ≤ (vm.cutS t' ω' : ℝ) := by
        have heq : (1 / 2 : ℝ) * Vol₀ / (1 / φ_j) = (1 / 2 : ℝ) * φ_j * Vol₀ := by
          field_simp
        linarith [heq ▸ hcut_ge]
      -- Single-elt split: sum ≥ cutS t' since other terms are nonneg
      have h_sum_ge : (vm.cutS t' ω' : ℝ) ≤
          ∑ k ∈ Finset.Icc t_j (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω' - 1),
            (vm.cutS k ω' : ℝ) := by
        have h_erase : (vm.cutS t' ω' : ℝ) +
            ∑ k ∈ (Finset.Icc t_j (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω' - 1)).erase t',
              (vm.cutS k ω' : ℝ) =
            ∑ k ∈ Finset.Icc t_j (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω' - 1),
              (vm.cutS k ω' : ℝ) := by
          rw [← Finset.sum_erase_add _ _ ht'_in]; ring
        have h_rest_nn : (0 : ℝ) ≤
            ∑ k ∈ (Finset.Icc t_j (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω' - 1)).erase t',
              (vm.cutS k ω' : ℝ) := Finset.sum_nonneg fun k _ => Nat.cast_nonneg _
        linarith
      linarith
    · simp only [indℰ, if_neg hℰ, mul_zero]
      exact Finset.sum_nonneg fun k _ => Nat.cast_nonneg _
  -- Take E[· | ℱ_{t_j}] of the pointwise bound using condExp_mono.
  -- Integrability of LHS: (1/2)·φ_j·Vol·indℰ is bounded.
  have hT_lt_meas : MeasurableSet
      {ω : Ω | t' < embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω} := by
    have h := (hT_stop t').compl
    have hset : {ω : Ω | t' < embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω} =
        {ω | (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω : ℕ∞) ≤ ↑t'}ᶜ := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le, ENat.coe_lt_coe]
    rw [hset]; exact vm.ℱ.le t' _ h
  have hcut_meas_real : Measurable (fun ω' => (vm.cutS t' ω' : ℝ)) := by
    have hA_meas' : @Measurable Ω (Finset V) _ ⊤ (vm.opinionZeroSet t') :=
      fun s _ => vm.A_meas t' _ ⟨s, trivial, rfl⟩
    have heq : (fun ω' => (vm.cutS t' ω' : ℝ)) =
        (fun s' => (G.edgesBetween t'
          (minoritySet G.toTemporalGraph t' s') (Finset.univ \ minoritySet G.toTemporalGraph t' s') : ℝ)) ∘ vm.opinionZeroSet t' := by
      funext ω'
      simp [TemporalGraph.VoterModelAbstract.cutS, TemporalGraph.VoterModelAbstract.S]
    rw [heq]
    exact (measurable_of_finite _).comp hA_meas'
  have hindℰ_meas : Measurable indℰ := by
    have h_set_meas : MeasurableSet {ω' : Ω | t' < embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω' ∧
        (vm.cutS t' ω' : ℝ) ≥ (1 / 2 : ℝ) * Vol₀ / (1 / φ_j)} :=
      hT_lt_meas.inter (hcut_meas_real measurableSet_Ici)
    exact Measurable.ite h_set_meas measurable_const measurable_const
  have hindℰ_bound : ∀ ω', ‖indℰ ω'‖ ≤ (1 : ℝ) := by
    intro ω'; simp only [indℰ]; split_ifs <;> simp
  have hindℰ_int : Integrable indℰ vm.μ :=
    Integrable.mono (integrable_const (1 : ℝ)) hindℰ_meas.aestronglyMeasurable
      (ae_of_all _ fun ω' => by simpa [Real.norm_eq_abs] using hindℰ_bound ω')
  have hLHS_int : Integrable (fun ω' => (1 / 2 : ℝ) * φ_j * Vol₀ * indℰ ω') vm.μ := by
    have : (fun ω' => (1 / 2 : ℝ) * φ_j * Vol₀ * indℰ ω') =
        ((1 / 2 : ℝ) * φ_j * Vol₀) • indℰ := by ext; simp [smul_eq_mul]
    rw [this]; exact hindℰ_int.smul _
  -- Integrability of Σ_{k ∈ Icc t_j (T_next ω' - 1)} cutS k ω'.
  -- Express as Σ_{k ∈ Ico t_j (N+1)} (if k < T_next then cutS k else 0).
  -- {ω | k < T_next ω} is measurable, so each indicator-cutS term is integrable.
  have hT_lt_meas_all : ∀ k, MeasurableSet[vm.ℱ k]
      {ω : Ω | k < embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω} := by
    intro k
    have h := (hT_stop k).compl
    have hset : {ω : Ω | k < embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω} =
        {ω | (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω : ℕ∞) ≤ ↑k}ᶜ := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le, ENat.coe_lt_coe]
    rw [hset]; exact h
  have hRHS_eq : ∀ ω',
      ∑ k ∈ Finset.Icc t_j (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω' - 1),
        (vm.cutS k ω' : ℝ) =
      ∑ k ∈ Finset.Ico t_j (N + 1),
        (if k < embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω' then (vm.cutS k ω' : ℝ) else 0) := by
    intro ω'
    have hT_le : embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω' ≤ N := hN ω'
    have hT_pos1 : 1 ≤ embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω' := hT_pos ω'
    by_cases hgt : t_j < embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω'
    · -- Icc t_j (T_next - 1) = (Ico t_j T_next) since T_next ≥ 1
      have h_Icc_eq : Finset.Icc t_j (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω' - 1) =
          Finset.Ico t_j (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω') := by
        ext k
        rw [Finset.mem_Icc, Finset.mem_Ico]
        omega
      rw [h_Icc_eq]
      -- Now rewrite Σ_{k ∈ Ico t_j T_next} f k = Σ_{k ∈ Ico t_j (N+1)} (if k < T_next then f k else 0)
      have h_split : Finset.Ico t_j (N + 1) =
          Finset.Ico t_j (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω') ∪
          Finset.Ico (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω') (N + 1) := by
        rw [← Finset.Ico_union_Ico_eq_Ico (Nat.le_of_lt hgt) (by omega)]
      have h_disj : Disjoint (Finset.Ico t_j (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω'))
          (Finset.Ico (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω') (N + 1)) := by
        simp only [Finset.disjoint_left, Finset.mem_Ico]; intro a h1 h2; omega
      rw [h_split, Finset.sum_union h_disj]
      have h_first : ∑ k ∈ Finset.Ico t_j (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω'),
          (if k < embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω' then (vm.cutS k ω' : ℝ) else 0) =
          ∑ k ∈ Finset.Ico t_j (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω'),
            (vm.cutS k ω' : ℝ) :=
        Finset.sum_congr rfl fun k hk => by
          rw [if_pos (Finset.mem_Ico.mp hk).2]
      have h_second : ∑ k ∈ Finset.Ico (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω') (N + 1),
          (if k < embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω' then (vm.cutS k ω' : ℝ) else 0) = 0 :=
        Finset.sum_eq_zero fun k hk => by
          rw [if_neg (by simp only [Finset.mem_Ico] at hk; omega)]
      rw [h_first, h_second, add_zero]
    · -- T_{j+1} ω' ≤ t_j with T_{j+1} ω' ≥ 1: LHS empty (Icc t_j (T-1) where T-1 < t_j),
      -- RHS each term has if-cond `k < T_{j+1}` false for k ∈ Ico t_j (N+1) (so k ≥ t_j ≥ T_{j+1}).
      push Not at hgt
      have hLHS : Finset.Icc t_j (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω' - 1) = ∅ :=
        Finset.Icc_eq_empty (by omega)
      rw [hLHS, Finset.sum_empty]
      symm
      apply Finset.sum_eq_zero
      intro k hk
      rw [if_neg]
      simp only [Finset.mem_Ico] at hk
      omega
  -- Integrability of the indicator-sum form (deterministic range).
  have hIcc_sum_int : Integrable (fun ω' =>
      ∑ k ∈ Finset.Ico t_j (N + 1),
        (if k < embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω' then (vm.cutS k ω' : ℝ) else 0)) vm.μ := by
    refine integrable_finsetSum _ fun k _ => ?_
    have hset_meas_top : MeasurableSet {ω : Ω | k < embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω} :=
      vm.ℱ.le k _ (hT_lt_meas_all k)
    have heq : (fun ω' => if k < embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω' then
        (vm.cutS k ω' : ℝ) else 0) =
        Set.indicator {ω : Ω | k < embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω}
          (fun ω' => (vm.cutS k ω' : ℝ)) := by
      funext ω'; simp [Set.indicator_apply]
    rw [heq]
    exact (hC2_t'.cutInt k).indicator hset_meas_top
  have hRHS_int : Integrable (fun ω' =>
      ∑ k ∈ Finset.Icc t_j (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω' - 1),
        (vm.cutS k ω' : ℝ)) vm.μ := by
    refine hIcc_sum_int.congr ?_
    refine ae_of_all _ fun ω' => ?_
    exact (hRHS_eq ω').symm
  -- Take condExp_mono
  have h_condExp_mono :=
    condExp_mono (m := vm.ℱ t_j) hLHS_int hRHS_int (ae_of_all _ h_pw_sum)
  -- Constant pull-out: E[c·indℰ | ℱ] = c·E[indℰ | ℱ].
  have h_const_pull : ∀ᵐ ω ∂(vm.μ : Measure _),
      ((vm.μ : Measure _)[fun ω' => (1 / 2 : ℝ) * φ_j * Vol₀ * indℰ ω' | vm.ℱ t_j]) ω =
      (1 / 2 : ℝ) * φ_j * Vol₀ * ((vm.μ : Measure _)[indℰ | vm.ℱ t_j]) ω := by
    have hfun_eq : (fun ω' => (1 / 2 : ℝ) * φ_j * Vol₀ * indℰ ω') =
        ((1 / 2 : ℝ) * φ_j * Vol₀) • indℰ := by ext; simp [smul_eq_mul]
    rw [hfun_eq]
    have := condExp_smul ((1 / 2 : ℝ) * φ_j * Vol₀) indℰ (vm.ℱ t_j) (μ := (vm.μ : Measure Ω))
    filter_upwards [this] with ω hω
    simpa [Pi.smul_apply, smul_eq_mul] using hω
  -- Combine and restrict to F.
  have hcoeff_pos : (0 : ℝ) < (1 / 2 : ℝ) * φ_j * Vol₀ := by positivity
  have h_edge_lower : ∀ᵐ ω ∂((vm.μ : Measure _).restrict F),
      ((vm.μ : Measure _)[fun ω' => ∑ k ∈ Finset.Icc t_j (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω' - 1),
        (vm.cutS k ω' : ℝ) | vm.ℱ t_j]) ω ≥ (1 / 4 : ℝ) * φ_j * Vol₀ := by
    filter_upwards [ae_restrict_of_ae h_condExp_mono, ae_restrict_of_ae h_const_pull,
      h_prob_good] with ω hmono hconst hgood'
    rw [hconst] at hmono
    -- hmono: (1/2)·φ_j·Vol · E[indℰ|ℱ] ≤ E[Σ cutS | ℱ]
    -- hgood': E[indℰ | ℱ] ≥ 1/2
    have h_step : (1 / 2 : ℝ) * φ_j * Vol₀ * (1 / 2) ≤
        (1 / 2 : ℝ) * φ_j * Vol₀ * ((vm.μ : Measure _)[indℰ | vm.ℱ t_j]) ω :=
      mul_le_mul_of_nonneg_left hgood' (le_of_lt hcoeff_pos)
    have heq : (1 / 2 : ℝ) * φ_j * Vol₀ * (1 / 2) = (1 / 4 : ℝ) * φ_j * Vol₀ := by ring
    linarith only [hmono, heq ▸ h_step]
  -- Strict bound: (1/4)·φ_j·Vol > φ_j·Vol/8, using Vol > 0 and φ_j > 0
  -- (since 1/4 > 1/8).
  have h_edge_strict : ∀ᵐ ω ∂((vm.μ : Measure _).restrict F),
      ((vm.μ : Measure _)[fun ω' => ∑ k ∈ Finset.Icc t_j (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω' - 1),
        (vm.cutS k ω' : ℝ) | vm.ℱ t_j]) ω
        > 1 * Vol₀ / (8 / φ_j) := by
    filter_upwards [h_edge_lower] with ω hω
    have h34 : φ_j * Vol₀ / 8 < (1 / 4 : ℝ) * φ_j * Vol₀ := by
      have : (0 : ℝ) < φ_j * Vol₀ := mul_pos hφ_j hVol_pos
      linarith only [this]
    have hrw : (1 : ℝ) * Vol₀ / (8 / φ_j) = φ_j * Vol₀ / 8 := by
      have hφ_ne : φ_j ≠ 0 := ne_of_gt hφ_j
      field_simp
    linarith only [hω, hrw ▸ h34]
  -- Step 3: derive L81's other hypotheses.
  -- T_next deterministic upper bound from hC2_t'.bound: T_next ≤ N.
  have hT_next_le : ∀ ω, embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω ≤ N := hN
  -- T_next ≥ t_j on F: from hF_T (T_j = t_j on F) + embeddedChainTime_strictMono.
  have hT_next_ge : ∀ᵐ ω ∂((vm.μ : Measure _).restrict F), t_j ≤ embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω := by
    refine ae_restrict_of_forall_mem hF_meas_top ?_
    intro ω hωF
    have hle : embeddedChainTime G.toTemporalGraph vm Δ j ω ≤ (∑ k ∈ Finset.range (j + 1), Δ k) - 1 :=
      hF_T ω hωF ▸ hT_cap
    have hmono := embeddedChainTime_strictMono G.toTemporalGraph vm Δ j ω hle
    linarith [hF_T ω hωF]
  have hT_next_pos : ∀ᵐ ω ∂((vm.μ : Measure _).restrict F), 0 < embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω :=
    ae_of_all _ hT_pos
  -- ψ(t_j) = ψ₀ pointwise on F (via hF_S).
  have hpsi_init : ∀ᵐ ω ∂((vm.μ : Measure _).restrict F),
      vm.psiS t_j ω ≤ G.potential t_j s_j := by
    apply ae_restrict_of_forall_mem hF_meas_top
    intro ω hω
    have : vm.psiS t_j ω = G.potential t_j s_j := by
      change G.potential t_j (vm.S t_j ω) = _; rw [hF_S ω hω]
    linarith only [this]
  -- Stability on F: derived from hF_T + hF_S + volumeExcursionTime_vol_le.
  have hstable_vol : ∀ ω ∈ F, ∀ k, t_j ≤ k →
      k < embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω →
      ((G.snapshot k).volume (vm.S k ω) : ℝ) ≤ 3 / 2 * Vol₀ := by
    intro ω hωF k h_lo h_hi
    have hT_next : embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω =
        volumeExcursionTime G.toTemporalGraph vm t_j ((∑ ℓ ∈ Finset.range (j + 1), Δ ℓ) - 1) ω := by
      simp only [embeddedChainTime]; rw [hF_T ω hωF]
    rw [hT_next] at h_hi
    have hbound := volumeExcursionTime_vol_le G.toTemporalGraph vm t_j _ k ω h_lo h_hi
    rw [hF_S ω hωF] at hbound
    have hbound_r : (2 : ℝ) * ((G.snapshot k).volume (vm.S k ω) : ℝ) ≤
        3 * ((G.snapshot t_j).volume s_j : ℝ) := by exact_mod_cast hbound
    show ((G.snapshot k).volume (vm.S k ω) : ℝ) ≤ 3 / 2 * Vol₀
    linarith only [hbound_r]
  have hS_nonempty : ∀ ω ∈ F, ∀ k, t_j ≤ k →
      k < embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω →
      (vm.S k ω).Nonempty := by
    intro ω hωF k h_lo h_hi
    have hT_next : embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω =
        volumeExcursionTime G.toTemporalGraph vm t_j ((∑ ℓ ∈ Finset.range (j + 1), Δ ℓ) - 1) ω := by
      simp only [embeddedChainTime]; rw [hF_T ω hωF]
    rw [hT_next] at h_hi
    exact volumeExcursionTime_S_nonempty G vm t_j _ k ω h_lo h_hi
      (hF_S ω hωF ▸ hs_j)
  -- Step 4: apply L81 (`potential_decrease_stable_interval_large_on_fiber`)
  -- with μ_param=1, Δ=8/φ_j.
  have hΔ_L81 : (0 : ℝ) < 8 / φ_j := by positivity
  have h_L81 := potential_decrease_stable_interval_large_on_fiber
    G vm s_j hs_j t_j (embeddedChainTime G.toTemporalGraph vm Δ (j + 1)) hT_stop N hT_next_le
    F hF_meas hT_next_ge hT_next_pos hpsi_init (8 / φ_j) hΔ_L81
    hstable_vol hS_nonempty 1 h_edge_strict
  -- Step 5: arithmetic — normalize L81's bound to the target form.
  refine h_L81.mono fun ω hω => le_trans hω ?_
  -- L81 output: -(1·d_min)/(24·√6·(8/φ_j)·ψ₀)
  -- Target:    -(d_min·φ_j)/(192·√6·ψ₀)
  show -(1 * (G.minDegreeAt 0 : ℝ) / (24 * Real.sqrt 6 *
      (8 / φ_j) * G.potential t_j s_j)) ≤
    -((G.minDegreeAt 0 : ℝ) * φ_j) / (192 * Real.sqrt 6 *
      G.potential t_j s_j)
  have hsq6 : Real.sqrt 6 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  by_cases hψ0 : G.potential t_j s_j = 0
  · simp [hψ0]
  · have hφ_ne : φ_j ≠ 0 := ne_of_gt hφ_j
    have h : -((1 * (G.minDegreeAt 0 : ℝ)) / (24 * Real.sqrt 6 *
        (8 / φ_j) * G.potential t_j s_j)) =
        -((G.minDegreeAt 0 : ℝ) * φ_j) / (192 * Real.sqrt 6 *
          G.potential t_j s_j) := by
      field_simp [hsq6, hφ_ne, hψ0]
      ring
    linarith [h]

end VoterModel
