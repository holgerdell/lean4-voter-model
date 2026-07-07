module

import Mathlib.Probability.Martingale.OptionalStopping
import VoterProcess.Martingale
public import UpperBound.EmbeddedChain
import Probability.Preliminaries
import Mathlib.Algebra.Order.Star.Real


@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

namespace VoterModel

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]

/-! ### χ-potential and χ-down-drift (paper §3.2 case 2) -/

/-- \label{def:chi-potential}

The χ-potential of a set `S` at time `t`: `χ(S) = log(1 + Vol(S))`. -/
def _root_.TemporalGraph.chiPotential (G : TemporalGraph V) (t : ℕ) (S : Finset V) : ℝ :=
  Real.log (1 + (TemporalGraph.volume G t S : ℝ))

/-- The χ-potential of a fixed-degree temporal graph, via the underlying `TemporalGraph`. -/
@[reducible] noncomputable def _root_.TemporalGraphFixedDegree.chiPotential
    (G : TemporalGraphFixedDegree V) (t : ℕ) (S : Finset V) : ℝ :=
  G.toTemporalGraph.chiPotential t S

/-! #### Helper lemmas for `chi_down_drift_generic` -/

-- Taylor bound: log(1+z) ≤ z - z²/2 for z ∈ (-1, 0).
-- Proof: f(w) := w - w²/2 - log(1+w) satisfies f(0) = 0 and f' < 0 on (-1,0)
-- (since f'(w) = 1 - w - 1/(1+w) = -w²/(1+w) < 0 for w ∈ (-1,0)),
-- so f is increasing toward 0, hence f(z) > 0 for z < 0.
private lemma chi_aux_log_one_add_le_of_neg (z : ℝ) (hz_lb : -1 < z) (hz_ub : z < 0) :
    Real.log (1 + z) ≤ z - z ^ 2 / 2 := by
  set g : ℝ → ℝ := fun w => w - w ^ 2 / 2 - Real.log (1 + w)
  have hg0 : g 0 = 0 := by simp [g]
  have hg_cont : ContinuousOn g (Set.Icc z 0) :=
    (continuousOn_id.sub ((continuousOn_pow 2).div_const 2)).sub
    (Real.continuousOn_log.comp (continuousOn_const.add continuousOn_id)
      (fun x hx => ne_of_gt (by simp only [Set.mem_Icc] at hx; linarith)))
  have hg_deriv : ∀ w ∈ Set.Ioo z 0, HasDerivAt g (1 - w - (1 + w)⁻¹) w := by
    intro w ⟨hwz, _⟩
    have h1w : 0 < 1 + w := by linarith [hz_lb, hwz]
    have hd2 : HasDerivAt (fun w => w ^ 2 / 2) w w :=
      ((hasDerivAt_pow 2 w).div_const 2).congr_deriv
        (by simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]; ring)
    have hd3 := Real.hasDerivAt_log (ne_of_gt h1w) |>.comp w (hasDerivAt_id w |>.const_add 1)
    simp only [mul_one] at hd3
    exact (hasDerivAt_id w).sub hd2 |>.sub hd3
  obtain ⟨c, hc_mem, hc_eq⟩ := exists_hasDerivAt_eq_slope g _ hz_ub hg_cont hg_deriv
  -- f'(c) < 0: (1+c)(1-c) = 1 - c² < 1 for c ∈ (-1, 0)
  have h1c : (0:ℝ) < 1 + c := by linarith [hc_mem.1, hz_lb]
  have hc_neg : 1 - c - (1 + c)⁻¹ < 0 := by
    have hc_ub : c < 0 := hc_mem.2
    nlinarith [mul_inv_cancel₀ (ne_of_gt h1c), mul_pos_of_neg_of_neg hc_ub hc_ub,
      inv_pos.mpr h1c]
  have hlt : (g 0 - g z) / (0 - z) < 0 := hc_eq ▸ hc_neg
  rw [div_neg_iff] at hlt
  have hgz_pos : 0 < g z := by
    rcases hlt with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · linarith
    · rw [hg0] at h1; linarith
  linarith [show g z = z - z ^ 2 / 2 - Real.log (1 + z) from rfl]

-- Pointwise bound: log(1+y) - log(1+x) ≤ (y-x)/(1+x) - 1_{y<x} · (y-x)²/(2(1+x)²)
-- for x > 0 and y ≥ 0.
-- This is the key Taylor inequality applied to z = (y-x)/(1+x).
private lemma chi_aux_log_diff_le (y x : ℝ) (hx : 0 < x) (hy : 0 ≤ y) :
    Real.log (1 + y) - Real.log (1 + x) ≤
    (y - x) / (1 + x) - if y < x then (y - x) ^ 2 / (2 * (1 + x) ^ 2) else 0 := by
  have h1x : (0:ℝ) < 1 + x := by linarith
  have h1y : (0:ℝ) < 1 + y := by linarith
  have hlog_rw : Real.log (1 + y) - Real.log (1 + x) =
      Real.log (1 + (y - x) / (1 + x)) := by
    rw [show 1 + (y - x) / (1 + x) = (1 + y) / (1 + x) from by field_simp; ring]
    rw [Real.log_div (ne_of_gt h1y) (ne_of_gt h1x)]
  have hz_gt_m1 : -1 < (y - x) / (1 + x) := by rw [lt_div_iff₀ h1x]; linarith
  rw [hlog_rw]
  split_ifs with hyx
  · -- Downward move: z = (y-x)/(1+x) < 0, apply chi_aux_log_one_add_le_of_neg
    have hz_ub : (y - x) / (1 + x) < 0 := div_neg_of_neg_of_pos (sub_neg.mpr hyx) h1x
    have hbound := chi_aux_log_one_add_le_of_neg _ hz_gt_m1 hz_ub
    have heq : ((y - x) / (1 + x)) ^ 2 / 2 = (y - x) ^ 2 / (2 * (1 + x) ^ 2) := by field_simp
    linarith
  · -- Upward move: z ≥ 0, apply log(1+z) ≤ z (from log(1+z) ≤ (1+z) - 1 = z)
    simp only [sub_zero]
    push Not at hyx
    have hz_nn : 0 ≤ (y - x) / (1 + x) := div_nonneg (by linarith) (le_of_lt h1x)
    linarith [Real.log_le_sub_one_of_pos (show 0 < 1 + (y - x) / (1 + x) by linarith)]



/-- \label{cor:chi-down-drift-voter}
\label{lem:chi-down-drift-voter-on-fiber}

**Fiber-relative unconditional χ-drift** (Lean-only helper for L68 cases 1 and 2;
set-integral form of `chi_down_drift_voter` over a measurable fiber `F ∈ ℱ_{t_j}`).

Let `F ⊆ Ω` be a set measurable in `vm.ℱ t_j`, with `T_j ω = t_j` and
`vm.S t_j ω = s_j` for all `ω ∈ F`. Then
`∫_F (χ(T_{j+1}, S_{T_{j+1}}) − χ(t_j, s_j)) dvm.μ ≤ 0`.

This is the set-integral form of `chi_down_drift_voter`, but with the deterministic
fiber conditions `T_j = t_j` and `S_{t_j} = s_j` localized to `F` rather than
imposed globally. The proof uses a modified stopping time
`τ' ω := max t_j (T_{j+1} ω)` (which globally satisfies `t_j ≤ τ' ω ≤ t'` for
`t' = ∑ k < j+2, Δ k`) to run the (-vol) submartingale optional-stopping argument
unconditionally, then restricts to `F` (where `τ' ω = T_{j+1} ω` by strict
monotonicity of the embedded chain) via `setIntegral_condExp`.

Since `v₀ := volume G t_j s_j` is a *true scalar*, the `(1 + v₀)⁻¹` pull-out from
the log-difference bound becomes plain scalar arithmetic on `∫_F`, sidestepping the
`condExp_mul_of_stronglyMeasurable_left` machinery of `chi_down_drift_voter`. -/
theorem chi_down_drift_voter_on_fiber
    {Ω : Type*} [MeasurableSpace Ω]
    (G : TemporalGraphFixedDegree V)
    (vm : G.VoterModelAbstract 2 Ω)
    -- Fixed value s_j (paper: s_{t_j}) and realized time t_j
    (s_j : Finset V) (t_j : ℕ)
    -- Embedded chain parameters
    (Δ : ℕ → ℕ) (hΔ_pos : ∀ k, 1 ≤ Δ k) (j : ℕ)
    -- Fiber F: measurable in ℱ_{t_j}, with T_j = t_j and S_{t_j} = s_j on F
    (F : Set Ω)
    (hF_meas : MeasurableSet[vm.ℱ t_j] F)
    (hF_T : ∀ ω ∈ F, embeddedChainTime G.toTemporalGraph vm Δ j ω = t_j)
    (hF_S : ∀ ω ∈ F, vm.S t_j ω = s_j)
    -- t_j cap: needed for strict monotonicity T_j < T_{j+1} on F
    (hT_cap : t_j ≤ (∑ k ∈ Finset.range (j + 1), Δ k) - 1) :
    -- Conclusion: ∫_F (χ(T_{j+1}, S_{T_{j+1}}) − chiPotential G t_j s_j) dvm.μ ≤ 0
    ∫ ω in F,
      (G.chiPotential
            (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
            (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω)
        - G.chiPotential t_j s_j)
      ∂vm.μ ≤ 0 := by
  classical
  -- Cap value t' bounds T_{j+1} globally (proved inline; mirrors L75).
  set t' : ℕ := ∑ k ∈ Finset.range (j + 2), Δ k with ht'_def
  have hT_next_le_global : ∀ ω, embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω ≤ t' := by
    intro ω
    suffices h : ∀ i ω, embeddedChainTime G.toTemporalGraph vm Δ i ω ≤ ∑ k ∈ Finset.range (i + 1), Δ k by
      exact h (j + 1) ω
    intro i
    induction i with
    | zero => intro ω; simp [embeddedChainTime]
    | succ i' _ =>
      intro ω
      simp only [embeddedChainTime]
      -- After def change, T_{i'+1} ω = vET (T_{i'} ω) ((∑ range (i'+1) Δ) - 1) ω.
      have h := volumeExcursionTime_le_succ G.toTemporalGraph vm (embeddedChainTime G.toTemporalGraph vm Δ i' ω)
        ((∑ k ∈ Finset.range (i' + 1), Δ k) - 1) ω
      have h_pos : 1 ≤ ∑ k ∈ Finset.range (i' + 1), Δ k := by
        have h0 : Δ 0 ≤ ∑ k ∈ Finset.range (i' + 1), Δ k :=
          Finset.single_le_sum (f := Δ) (fun k _ => Nat.zero_le _)
            (Finset.mem_range.mpr (by omega))
        exact le_trans (hΔ_pos 0) h0
      have hsub : ((∑ k ∈ Finset.range (i' + 1), Δ k) - 1) + 1 =
          ∑ k ∈ Finset.range (i' + 1), Δ k :=
        Nat.sub_add_cancel h_pos
      -- The outer claim has range (i'+1+1); the inner def now gives ≤ range (i'+1).
      -- Bridge via monotonicity of partial sums.
      have hmono : ∑ k ∈ Finset.range (i' + 1), Δ k ≤ ∑ k ∈ Finset.range (i' + 1 + 1), Δ k :=
        Finset.sum_le_sum_of_subset (fun k hk => Finset.mem_range.mpr
          (lt_of_lt_of_le (Finset.mem_range.mp hk) (Nat.le_succ _)))
      linarith
  have ht_j_le_t' : t_j ≤ t' := by
    -- t_j ≤ (∑ k < j+1, Δ k) - 1 ≤ ∑ k < j+1, Δ k ≤ ∑ k < j+2, Δ k = t'.
    have h1 : (∑ k ∈ Finset.range (j + 1), Δ k) - 1 ≤ ∑ k ∈ Finset.range (j + 1), Δ k :=
      Nat.sub_le _ _
    have h2 : ∑ k ∈ Finset.range (j + 1), Δ k ≤ t' :=
      Finset.sum_le_sum_of_subset (fun k hk => Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp hk) (Nat.le_succ _)))
    exact hT_cap.trans (h1.trans h2)
  -- Measurability scaffolding.
  have hS_meas : ∀ t, @Measurable Ω (Finset V) (vm.ℱ t) ⊤ (vm.S t) := fun t =>
    (measurable_of_countable (fun A => VoterModel.minoritySet G.toTemporalGraph t A)).comp
      (vm.A_stronglyAdapted t).measurable
  have hT_stop : IsStoppingTime vm.ℱ (fun ω => (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω : ℕ∞)) :=
    embeddedChainTime_isStoppingTime G.toTemporalGraph vm Δ hS_meas (j + 1)
  -- Modified stopping time: τ' ω = max t_j (T_{j+1} ω). Globally t_j ≤ τ' ω ≤ t'.
  let τ' : Ω → ℕ∞ := fun ω => max (t_j : ℕ∞) (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω : ℕ∞)
  have hτ'_stop : IsStoppingTime vm.ℱ τ' := by
    have hconst : IsStoppingTime vm.ℱ (fun (_ : Ω) => (t_j : ℕ∞)) :=
      isStoppingTime_const vm.ℱ t_j
    exact hconst.max hT_stop
  have hτ'_ge_lo : ∀ ω, (t_j : ℕ∞) ≤ τ' ω := fun ω => le_max_left _ _
  have hτ'_le_hi : ∀ ω, τ' ω ≤ (t' : ℕ∞) := fun ω => by
    refine max_le ?_ ?_
    · exact_mod_cast ht_j_le_t'
    · exact_mod_cast hT_next_le_global ω
  -- On F: T_{j+1} ω > t_j, hence τ' ω = T_{j+1} ω.
  have hT_strict_on_F : ∀ ω ∈ F, t_j < embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω := by
    intro ω hω
    have hTj : embeddedChainTime G.toTemporalGraph vm Δ j ω = t_j := hF_T ω hω
    have hcap' : embeddedChainTime G.toTemporalGraph vm Δ j ω ≤
        (∑ k ∈ Finset.range (j + 1), Δ k) - 1 := hTj.symm ▸ hT_cap
    have hmono := embeddedChainTime_strictMono G.toTemporalGraph vm Δ j ω hcap'
    omega
  -- Natural-number version τ'Nat ω = max t_j (T_{j+1} ω).
  let τ'Nat : Ω → ℕ := fun ω => max t_j (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
  have hτ'_eq_cast : ∀ ω, τ' ω = (τ'Nat ω : ℕ∞) := fun ω => by
    show max (t_j : ℕ∞) (_ : ℕ∞) = ((max _ _ : ℕ) : ℕ∞)
    rfl
  -- (-vol) submartingale, stopped at τ'.
  haveI : IsFiniteMeasure (vm.μ : Measure Ω) := inferInstance
  have hVolSub : Submartingale
      (fun t ω => -(TemporalGraph.volume G.toTemporalGraph t (vm.S t ω) : ℝ)) vm.ℱ vm.μ :=
    (TemporalGraph.vol_minority_supermartingale vm).neg
  have hStop : Submartingale
      (stoppedProcess
        (fun t ω => -(TemporalGraph.volume G.toTemporalGraph t (vm.S t ω) : ℝ)) τ') vm.ℱ vm.μ :=
    hVolSub.stoppedProcess hτ'_stop
  have hcond_vol :=
    Submartingale.ae_le_condExp hStop (i := t_j) (j := t') ht_j_le_t'
  -- Global rewrites of stoppedProcess at t_j and t' (using τ' globally).
  have hLHS_eq :
      stoppedProcess
          (fun t ω => -(TemporalGraph.volume G.toTemporalGraph t (vm.S t ω) : ℝ)) τ' t_j
      = fun ω => -(TemporalGraph.volume G.toTemporalGraph t_j (vm.S t_j ω) : ℝ) :=
    funext fun ω => stoppedProcess_eq_of_le (hτ'_ge_lo ω)
  have hRHS_eq :
      stoppedProcess
          (fun t ω => -(TemporalGraph.volume G.toTemporalGraph t (vm.S t ω) : ℝ)) τ' t'
      = fun ω => -(TemporalGraph.volume G.toTemporalGraph (τ'Nat ω) (vm.S (τ'Nat ω) ω) : ℝ) :=
    funext fun ω => by
      rw [stoppedProcess_eq_of_ge (hτ'_le_hi ω)]
      simp only [τ', WithTop.untopA, hτ'_eq_cast]
      norm_cast
  rw [hLHS_eq, hRHS_eq] at hcond_vol
  -- Integrabilities.
  have hInt_negvol_τ' : Integrable
      (fun ω => -(TemporalGraph.volume G.toTemporalGraph (τ'Nat ω) (vm.S (τ'Nat ω) ω) : ℝ)) vm.μ :=
    hRHS_eq ▸ hStop.2.2 t'
  have hInt_vol_τ' : Integrable
      (fun ω => (TemporalGraph.volume G.toTemporalGraph (τ'Nat ω) (vm.S (τ'Nat ω) ω) : ℝ)) vm.μ :=
    hInt_negvol_τ'.neg.congr (Filter.Eventually.of_forall (fun ω => neg_neg _))
  have hInt_vol_t_j : Integrable
      (fun ω => (TemporalGraph.volume G.toTemporalGraph t_j (vm.S t_j ω) : ℝ)) vm.μ :=
    (hVolSub.integrable t_j).neg.congr (Filter.Eventually.of_forall (fun ω => neg_neg _))
  -- E[vol(τ'Nat) | ℱ_{t_j}] ω ≤ vol(t_j, S_{t_j} ω) a.s.
  have hce_neg :
      (vm.μ : Measure _)[fun ω => -(TemporalGraph.volume G.toTemporalGraph (τ'Nat ω) (vm.S (τ'Nat ω) ω) : ℝ) | vm.ℱ t_j]
      =ᵐ[(vm.μ : Measure _)] -(vm.μ : Measure _)[fun ω =>
          (TemporalGraph.volume G.toTemporalGraph (τ'Nat ω) (vm.S (τ'Nat ω) ω) : ℝ) | vm.ℱ t_j] :=
    condExp_neg _ _
  have hvol_cond_le : ∀ᵐ ω ∂(vm.μ : Measure _),
      ((vm.μ : Measure _)[fun ω' => (TemporalGraph.volume G.toTemporalGraph (τ'Nat ω') (vm.S (τ'Nat ω') ω') : ℝ)
          | vm.ℱ t_j]) ω
        ≤ (TemporalGraph.volume G.toTemporalGraph t_j (vm.S t_j ω) : ℝ) := by
    filter_upwards [hcond_vol, hce_neg] with ω hcond_ω hceneg_ω
    have h := hcond_ω.trans_eq hceneg_ω
    simp only [Pi.neg_apply] at h
    linarith
  -- Notation: v₀ = volume G t_j s_j (true scalar).
  set v₀ : ℕ := TemporalGraph.volume G.toTemporalGraph t_j s_j with hv₀_def
  have hv₀_nn : (0 : ℝ) ≤ (v₀ : ℝ) := Nat.cast_nonneg _
  have h1v0_pos : (0 : ℝ) < 1 + (v₀ : ℝ) := by linarith
  -- On F: vol(t_j, S_{t_j} ω) = v₀ and chi(t_j, S_{t_j} ω) = log(1+v₀).
  have hvol_eq_on_F : ∀ ω ∈ F,
      (TemporalGraph.volume G.toTemporalGraph t_j (vm.S t_j ω) : ℝ) = (v₀ : ℝ) := by
    intro ω hω
    have : TemporalGraph.volume G.toTemporalGraph t_j (vm.S t_j ω) = v₀ := by
      rw [hF_S ω hω]
    exact_mod_cast this
  -- On F: τ'Nat ω = T_{j+1} ω.
  have hT_eq_τ'Nat_on_F : ∀ ω ∈ F,
      embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω = τ'Nat ω := by
    intro ω hω
    have hlt := hT_strict_on_F ω hω
    show _ = max t_j _
    omega
  -- Pointwise log-difference bound (from chi_down_drift_voter, applied to vol(τ'Nat ω) and v₀).
  have hpw : ∀ ω,
      Real.log (1 + (TemporalGraph.volume G.toTemporalGraph (τ'Nat ω) (vm.S (τ'Nat ω) ω) : ℝ))
        - Real.log (1 + (v₀ : ℝ))
      ≤ ((TemporalGraph.volume G.toTemporalGraph (τ'Nat ω) (vm.S (τ'Nat ω) ω) : ℝ) - (v₀ : ℝ))
          / (1 + (v₀ : ℝ)) := by
    intro ω
    set y := (TemporalGraph.volume G.toTemporalGraph (τ'Nat ω) (vm.S (τ'Nat ω) ω) : ℝ)
    set x := (v₀ : ℝ)
    have hx_nn : (0 : ℝ) ≤ x := Nat.cast_nonneg _
    have hy_nn : (0 : ℝ) ≤ y := Nat.cast_nonneg _
    have h1x : (0 : ℝ) < 1 + x := by linarith
    have hlog_rw : Real.log (1 + y) - Real.log (1 + x) =
        Real.log (1 + (y - x) / (1 + x)) := by
      rw [show 1 + (y - x) / (1 + x) = (1 + y) / (1 + x) from by field_simp; ring]
      rw [Real.log_div (by linarith) (ne_of_gt h1x)]
    rw [hlog_rw]
    have hz_gt_m1 : -1 < (y - x) / (1 + x) := by rw [lt_div_iff₀ h1x]; linarith
    have h1z_pos : (0 : ℝ) < 1 + (y - x) / (1 + x) := by linarith
    have := Real.log_le_sub_one_of_pos h1z_pos
    linarith
  -- Integrability of log diff (mirrors chi_down_drift_voter's hchi_int).
  have hchi_int : Integrable (fun ω =>
      Real.log (1 + (TemporalGraph.volume G.toTemporalGraph (τ'Nat ω) (vm.S (τ'Nat ω) ω) : ℝ)) -
      Real.log (1 + (v₀ : ℝ))) vm.μ := by
    apply (hInt_vol_τ'.add (integrable_const (v₀ : ℝ))).mono
    · apply AEStronglyMeasurable.sub
      · exact (Real.measurable_log.comp_aemeasurable
            (aemeasurable_const.add hInt_vol_τ'.1.aemeasurable)).aestronglyMeasurable
      · exact aestronglyMeasurable_const
    · filter_upwards with ω
      set vol' := (TemporalGraph.volume G.toTemporalGraph (τ'Nat ω) (vm.S (τ'Nat ω) ω) : ℝ)
      have hnn : (0 : ℝ) ≤ vol' := Nat.cast_nonneg _
      have hlog_nn : 0 ≤ Real.log (1 + vol') := Real.log_nonneg (by linarith)
      have hlog_le : Real.log (1 + vol') ≤ vol' := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + vol' by linarith)
        linarith
      have hlogv0_nn : 0 ≤ Real.log (1 + (v₀ : ℝ)) := Real.log_nonneg (by linarith)
      have hlogv0_le : Real.log (1 + (v₀ : ℝ)) ≤ (v₀ : ℝ) := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + (v₀ : ℝ) by linarith)
        linarith
      simp only [Pi.add_apply]
      rw [Real.norm_of_nonneg (show (0 : ℝ) ≤ vol' + ↑v₀ by linarith)]
      rw [Real.norm_eq_abs]
      rw [abs_le]
      refine ⟨by linarith, by linarith⟩
  -- Integrability of the volume-difference bound divided by (1+v₀).
  have hdiff_int : Integrable (fun ω =>
      ((TemporalGraph.volume G.toTemporalGraph (τ'Nat ω) (vm.S (τ'Nat ω) ω) : ℝ) - (v₀ : ℝ))
          / (1 + (v₀ : ℝ))) vm.μ :=
    (hInt_vol_τ'.sub (integrable_const (v₀ : ℝ))).div_const _
  -- Measurable F at ambient level.
  have hF_meas_top : MeasurableSet F := vm.ℱ.le t_j _ hF_meas
  -- Step 1: rewrite the integrand on F using defs and hF_S, hT_eq_τ'Nat.
  -- ∫_F (χ(T_{j+1},S_{T_{j+1}}) - χ(t_j, s_j)) dμ
  --   = ∫_F (log(1+vol(τ'Nat, S_{τ'Nat})) - log(1+v₀)) dμ
  set c : ℝ := TemporalGraph.chiPotential G.toTemporalGraph t_j s_j with hc_def
  have hc_eq_log : c = Real.log (1 + (v₀ : ℝ)) := by
    simp [c, TemporalGraph.chiPotential, hv₀_def]
  have hrw1 :
      ∫ ω in F,
        (TemporalGraph.chiPotential G.toTemporalGraph (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
              (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω) - c) ∂vm.μ
      = ∫ ω in F,
          (Real.log (1 + (TemporalGraph.volume G.toTemporalGraph (τ'Nat ω) (vm.S (τ'Nat ω) ω) : ℝ))
            - Real.log (1 + (v₀ : ℝ))) ∂vm.μ := by
    refine setIntegral_congr_fun hF_meas_top ?_
    intro ω hω
    have heq := hT_eq_τ'Nat_on_F ω hω
    show TemporalGraph.chiPotential G.toTemporalGraph (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
            (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω) - c = _
    rw [heq, hc_eq_log]
    rfl
  rw [hrw1]
  -- Step 2: bound the log-difference integrand by the affine bound via setIntegral_mono_ae.
  have hbound1 :
      ∫ ω in F,
          (Real.log (1 + (TemporalGraph.volume G.toTemporalGraph (τ'Nat ω) (vm.S (τ'Nat ω) ω) : ℝ))
            - Real.log (1 + (v₀ : ℝ))) ∂vm.μ
      ≤ ∫ ω in F,
          ((TemporalGraph.volume G.toTemporalGraph (τ'Nat ω) (vm.S (τ'Nat ω) ω) : ℝ) - (v₀ : ℝ))
            / (1 + (v₀ : ℝ)) ∂vm.μ := by
    apply setIntegral_mono_ae hchi_int.integrableOn hdiff_int.integrableOn
    exact Filter.Eventually.of_forall (fun ω => hpw ω)
  refine le_trans hbound1 ?_
  -- Step 3: factor out (1+v₀)⁻¹ — scalar pull-out, no condExp_mul.
  have hscalar :
      ∫ ω in F,
          ((TemporalGraph.volume G.toTemporalGraph (τ'Nat ω) (vm.S (τ'Nat ω) ω) : ℝ) - (v₀ : ℝ))
            / (1 + (v₀ : ℝ)) ∂vm.μ
      = (1 + (v₀ : ℝ))⁻¹ *
          (∫ ω in F,
              ((TemporalGraph.volume G.toTemporalGraph (τ'Nat ω) (vm.S (τ'Nat ω) ω) : ℝ) - (v₀ : ℝ))
              ∂vm.μ) := by
    have hcongr :
        ∫ ω in F,
            ((TemporalGraph.volume G.toTemporalGraph (τ'Nat ω) (vm.S (τ'Nat ω) ω) : ℝ) - (v₀ : ℝ))
              / (1 + (v₀ : ℝ)) ∂vm.μ
        = ∫ ω in F,
            (1 + (v₀ : ℝ))⁻¹ *
              ((TemporalGraph.volume G.toTemporalGraph (τ'Nat ω) (vm.S (τ'Nat ω) ω) : ℝ) - (v₀ : ℝ))
            ∂vm.μ := by
      refine setIntegral_congr_fun hF_meas_top ?_
      intro ω _
      show ((TemporalGraph.volume G.toTemporalGraph (τ'Nat ω) (vm.S (τ'Nat ω) ω) : ℝ) - (v₀ : ℝ))
            / (1 + (v₀ : ℝ))
        = (1 + (v₀ : ℝ))⁻¹ *
            ((TemporalGraph.volume G.toTemporalGraph (τ'Nat ω) (vm.S (τ'Nat ω) ω) : ℝ) - (v₀ : ℝ))
      rw [div_eq_inv_mul]
    rw [hcongr, integral_const_mul]
  rw [hscalar]
  -- Step 4: split the inner integral.
  have hsplit :
      ∫ ω in F,
          ((TemporalGraph.volume G.toTemporalGraph (τ'Nat ω) (vm.S (τ'Nat ω) ω) : ℝ) - (v₀ : ℝ)) ∂vm.μ
      = (∫ ω in F, (TemporalGraph.volume G.toTemporalGraph (τ'Nat ω) (vm.S (τ'Nat ω) ω) : ℝ) ∂vm.μ)
          - ∫ ω in F, (v₀ : ℝ) ∂vm.μ := by
    rw [integral_sub hInt_vol_τ'.integrableOn (integrable_const (v₀ : ℝ)).integrableOn]
  rw [hsplit]
  -- Step 5: replace ∫_F vol(τ'Nat) with ∫_F E[vol(τ'Nat) | ℱ_{t_j}] via setIntegral_condExp.
  have hsic := setIntegral_condExp (vm.ℱ.le t_j) hInt_vol_τ' hF_meas
  -- Step 6: bound ∫_F E[vol(τ'Nat) | ℱ_{t_j}] ≤ ∫_F vol(t_j, S_{t_j}).
  have hbound2 :
      ∫ ω in F, (TemporalGraph.volume G.toTemporalGraph (τ'Nat ω) (vm.S (τ'Nat ω) ω) : ℝ) ∂vm.μ
        ≤ ∫ ω in F, (TemporalGraph.volume G.toTemporalGraph t_j (vm.S t_j ω) : ℝ) ∂vm.μ := by
    rw [← hsic]
    apply setIntegral_mono_ae integrable_condExp.integrableOn hInt_vol_t_j.integrableOn
    filter_upwards [hvol_cond_le] with ω hω; exact hω
  -- Step 7: ∫_F vol(t_j, S_{t_j}) = ∫_F v₀ on F.
  have heq_v₀ :
      ∫ ω in F, (TemporalGraph.volume G.toTemporalGraph t_j (vm.S t_j ω) : ℝ) ∂vm.μ
      = ∫ ω in F, (v₀ : ℝ) ∂vm.μ := by
    refine setIntegral_congr_fun hF_meas_top ?_
    intro ω hω; exact hvol_eq_on_F ω hω
  -- Combine: ∫_F vol(τ'Nat) ≤ ∫_F v₀, so the inner difference ≤ 0, then * inv ≤ 0.
  have hdiff_le : (∫ ω in F,
        (TemporalGraph.volume G.toTemporalGraph (τ'Nat ω) (vm.S (τ'Nat ω) ω) : ℝ) ∂vm.μ)
        - ∫ ω in F, (v₀ : ℝ) ∂vm.μ ≤ 0 := by
    have := hbound2.trans_eq heq_v₀
    linarith
  have hinv_nn : (0 : ℝ) ≤ (1 + (v₀ : ℝ))⁻¹ := inv_nonneg.mpr (le_of_lt h1v0_pos)
  exact mul_nonpos_of_nonneg_of_nonpos hinv_nn hdiff_le


/-- **Fiber-relative unstable χ-drift** (Lean-only helper for L68 case 3;
set-integral form of `chi_down_drift_voter_unstable` over a measurable fiber
`F ∈ ℱ_{t_j}`).

Setup as `chi_down_drift_voter_on_fiber` (L77), plus `s_j ≠ ∅` and a
fiber-relative jump hypothesis on `F`:
  `∀ᵐ ω ∂((vm.μ : Measure _).restrict F),
    E[|vol(T_{j+1}) − vol(s_j)| | ℱ_{t_j}](ω) ≥ (1/8) · vol(s_j)`.

Then `∫_F (χ(T_{j+1}, S_{T_{j+1}}) − χ(t_j, s_j)) dvm.μ ≤ −(1/2048)·(vm.μ F).toReal`.

The constant `−1/2048 = −(1/8)²/32` matches L34's unstable constant.

**Proof.** Mirror `chi_down_drift_voter_on_fiber` (L77) for the τ' globalization,
but use the quadratic log bound from `chi_aux_log_diff_le` (rather than the
simpler `log(1+y) − log(1+x) ≤ (y−x)/(1+x)` of L77) to obtain a sharper
fiber-conditional bound. The hjump_F hypothesis is converted using on-F
identities for `volS` at `T_j` (via `hF_S`/`hF_T`). The final bound integrates
against `μ.restrict F` via `setIntegral_condExp` / `setIntegral_const`. -/
theorem chi_down_drift_voter_unstable_on_fiber
    {Ω : Type*} [MeasurableSpace Ω]
    (G : TemporalGraphFixedDegree V)
    (vm : G.VoterModelAbstract 2 Ω)
    -- Fixed value s_j ≠ ∅ (paper: s_{t_j}) and realized time t_j
    (s_j : Finset V) (hs_j : s_j.Nonempty) (t_j : ℕ)
    -- Embedded chain parameters
    (Δ : ℕ → ℕ) (hΔ_pos : ∀ k, 1 ≤ Δ k) (j : ℕ)
    -- Fiber F: measurable in ℱ_{t_j}, with T_j = t_j and S_{t_j} = s_j on F
    (F : Set Ω)
    (hF_meas : MeasurableSet[vm.ℱ t_j] F)
    (hF_T : ∀ ω ∈ F, embeddedChainTime G.toTemporalGraph vm Δ j ω = t_j)
    (hF_S : ∀ ω ∈ F, vm.S t_j ω = s_j)
    -- t_j cap: needed for strict monotonicity T_j < T_{j+1} on F
    (hT_cap : t_j ≤ (∑ k ∈ Finset.range (j + 1), Δ k) - 1)
    -- Fiber-relative jump hypothesis (a.e. on μ.restrict F)
    (hjump_F : ∀ᵐ ω ∂((vm.μ : Measure _).restrict F),
        ((vm.μ : Measure _)[fun ω' =>
            |vm.volS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω') ω' -
              vm.volS (embeddedChainTime G.toTemporalGraph vm Δ j ω') ω'| | vm.ℱ t_j]) ω
          ≥ 1 / 8 * ((G.snapshot t_j).volume s_j : ℝ)) :
    -- Conclusion: ∫_F (χ(T_{j+1}, S_{T_{j+1}}) − chiPotential G t_j s_j) dvm.μ
    --   ≤ −1/2048 · (vm.μ F).toReal
    ∫ ω in F,
      (G.chiPotential
            (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
            (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω)
        - G.chiPotential t_j s_j)
      ∂vm.μ ≤ -1 / 2048 * (vm.μ F).toReal := by
  classical
  -- ── PART A: τ' globalization scaffold (mirrors L77) ─────────────────────────
  set t' : ℕ := ∑ k ∈ Finset.range (j + 2), Δ k with ht'_def
  have hT_next_le_global : ∀ ω, embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω ≤ t' := by
    intro ω
    suffices h : ∀ i ω, embeddedChainTime G.toTemporalGraph vm Δ i ω ≤ ∑ k ∈ Finset.range (i + 1), Δ k by
      exact h (j + 1) ω
    intro i
    induction i with
    | zero => intro ω; simp [embeddedChainTime]
    | succ i' _ =>
      intro ω
      simp only [embeddedChainTime]
      -- After def change, T_{i'+1} ω = vET (T_{i'} ω) ((∑ range (i'+1) Δ) - 1) ω.
      have h := volumeExcursionTime_le_succ G.toTemporalGraph vm (embeddedChainTime G.toTemporalGraph vm Δ i' ω)
        ((∑ k ∈ Finset.range (i' + 1), Δ k) - 1) ω
      have h_pos : 1 ≤ ∑ k ∈ Finset.range (i' + 1), Δ k := by
        have h0 : Δ 0 ≤ ∑ k ∈ Finset.range (i' + 1), Δ k :=
          Finset.single_le_sum (f := Δ) (fun k _ => Nat.zero_le _)
            (Finset.mem_range.mpr (by omega))
        exact le_trans (hΔ_pos 0) h0
      have hsub : ((∑ k ∈ Finset.range (i' + 1), Δ k) - 1) + 1 =
          ∑ k ∈ Finset.range (i' + 1), Δ k :=
        Nat.sub_add_cancel h_pos
      -- The outer claim has range (i'+1+1); the inner def now gives ≤ range (i'+1).
      -- Bridge via monotonicity of partial sums.
      have hmono : ∑ k ∈ Finset.range (i' + 1), Δ k ≤ ∑ k ∈ Finset.range (i' + 1 + 1), Δ k :=
        Finset.sum_le_sum_of_subset (fun k hk => Finset.mem_range.mpr
          (lt_of_lt_of_le (Finset.mem_range.mp hk) (Nat.le_succ _)))
      linarith
  have ht_j_le_t' : t_j ≤ t' := by
    -- t_j ≤ (∑ k < j+1, Δ k) - 1 ≤ ∑ k < j+1, Δ k ≤ ∑ k < j+2, Δ k = t'.
    have h1 : (∑ k ∈ Finset.range (j + 1), Δ k) - 1 ≤ ∑ k ∈ Finset.range (j + 1), Δ k :=
      Nat.sub_le _ _
    have h2 : ∑ k ∈ Finset.range (j + 1), Δ k ≤ t' :=
      Finset.sum_le_sum_of_subset (fun k hk => Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp hk) (Nat.le_succ _)))
    exact hT_cap.trans (h1.trans h2)
  have hS_meas : ∀ t, @Measurable Ω (Finset V) (vm.ℱ t) ⊤ (vm.S t) := fun t =>
    (measurable_of_countable (fun A => VoterModel.minoritySet G.toTemporalGraph t A)).comp
      (vm.A_stronglyAdapted t).measurable
  have hT_stop : IsStoppingTime vm.ℱ (fun ω => (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω : ℕ∞)) :=
    embeddedChainTime_isStoppingTime G.toTemporalGraph vm Δ hS_meas (j + 1)
  -- Modified stopping time τ' ω = max t_j (T_{j+1} ω) (cast to ℕ∞).
  let τ' : Ω → ℕ∞ := fun ω => max (t_j : ℕ∞) (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω : ℕ∞)
  have hτ'_stop : IsStoppingTime vm.ℱ τ' := by
    have hconst : IsStoppingTime vm.ℱ (fun (_ : Ω) => (t_j : ℕ∞)) :=
      isStoppingTime_const vm.ℱ t_j
    exact hconst.max hT_stop
  have hτ'_ge_lo : ∀ ω, (t_j : ℕ∞) ≤ τ' ω := fun ω => le_max_left _ _
  have hτ'_le_hi : ∀ ω, τ' ω ≤ (t' : ℕ∞) := fun ω => by
    refine max_le ?_ ?_
    · exact_mod_cast ht_j_le_t'
    · exact_mod_cast hT_next_le_global ω
  -- On F: T_{j+1} ω > t_j, hence τ' ω = T_{j+1} ω.
  have hT_strict_on_F : ∀ ω ∈ F, t_j < embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω := by
    intro ω hω
    have hTj : embeddedChainTime G.toTemporalGraph vm Δ j ω = t_j := hF_T ω hω
    have hcap' : embeddedChainTime G.toTemporalGraph vm Δ j ω ≤
        (∑ k ∈ Finset.range (j + 1), Δ k) - 1 := hTj.symm ▸ hT_cap
    have hmono := embeddedChainTime_strictMono G.toTemporalGraph vm Δ j ω hcap'
    omega
  -- ℕ version τ'Nat ω = max t_j (T_{j+1} ω).
  let τ'Nat : Ω → ℕ := fun ω => max t_j (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
  have hτ'_eq_cast : ∀ ω, τ' ω = (τ'Nat ω : ℕ∞) := fun ω => by
    show max (t_j : ℕ∞) (_ : ℕ∞) = ((max _ _ : ℕ) : ℕ∞)
    rfl
  -- (-vol) submartingale, stopped at τ'.
  haveI : IsFiniteMeasure (vm.μ : Measure Ω) := inferInstance
  haveI : SigmaFiniteFiltration vm.μ vm.ℱ := inferInstance
  have hVolSub : Submartingale
      (fun t ω => -(TemporalGraph.volume G.toTemporalGraph t (vm.S t ω) : ℝ)) vm.ℱ vm.μ :=
    (TemporalGraph.vol_minority_supermartingale vm).neg
  have hStop : Submartingale
      (stoppedProcess
        (fun t ω => -(TemporalGraph.volume G.toTemporalGraph t (vm.S t ω) : ℝ)) τ') vm.ℱ vm.μ :=
    hVolSub.stoppedProcess hτ'_stop
  have hcond_vol :=
    Submartingale.ae_le_condExp hStop (i := t_j) (j := t') ht_j_le_t'
  have hLHS_eq :
      stoppedProcess
          (fun t ω => -(TemporalGraph.volume G.toTemporalGraph t (vm.S t ω) : ℝ)) τ' t_j
      = fun ω => -(TemporalGraph.volume G.toTemporalGraph t_j (vm.S t_j ω) : ℝ) :=
    funext fun ω => stoppedProcess_eq_of_le (hτ'_ge_lo ω)
  have hRHS_eq :
      stoppedProcess
          (fun t ω => -(TemporalGraph.volume G.toTemporalGraph t (vm.S t ω) : ℝ)) τ' t'
      = fun ω => -(TemporalGraph.volume G.toTemporalGraph (τ'Nat ω) (vm.S (τ'Nat ω) ω) : ℝ) :=
    funext fun ω => by
      rw [stoppedProcess_eq_of_ge (hτ'_le_hi ω)]
      simp only [τ', WithTop.untopA, hτ'_eq_cast]
      norm_cast
  rw [hLHS_eq, hRHS_eq] at hcond_vol
  -- ── Step 2: integrabilities for vol(τ'Nat) and vol(t_j) ─────────────────────
  have hInt_negvol_τ' : Integrable
      (fun ω => -(TemporalGraph.volume G.toTemporalGraph (τ'Nat ω) (vm.S (τ'Nat ω) ω) : ℝ)) vm.μ :=
    hRHS_eq ▸ hStop.2.2 t'
  have hInt_vol_τ' : Integrable
      (fun ω => (TemporalGraph.volume G.toTemporalGraph (τ'Nat ω) (vm.S (τ'Nat ω) ω) : ℝ)) vm.μ :=
    hInt_negvol_τ'.neg.congr (Filter.Eventually.of_forall (fun ω => neg_neg _))
  have hInt_vol_t_j : Integrable
      (fun ω => (TemporalGraph.volume G.toTemporalGraph t_j (vm.S t_j ω) : ℝ)) vm.μ :=
    (hVolSub.integrable t_j).neg.congr (Filter.Eventually.of_forall (fun ω => neg_neg _))
  -- ── Step 3: v₀, basic positivity, on-F identities ───────────────────────────
  set v₀ : ℕ := TemporalGraph.volume G.toTemporalGraph t_j s_j with hv₀_def
  have hv₀_pos : 0 < v₀ := by
    simp only [hv₀_def, TemporalGraph.volume]
    exact SimpleGraph.volume_pos_of_nonempty hs_j (fun v => G.degrees_pos v t_j)
  have hv₀_ge_one : (1 : ℝ) ≤ (v₀ : ℝ) := Nat.one_le_cast.mpr hv₀_pos
  have hv₀_nn : (0 : ℝ) ≤ (v₀ : ℝ) := Nat.cast_nonneg _
  have h1v0_pos : (0 : ℝ) < 1 + (v₀ : ℝ) := by linarith
  -- On F: vol(t_j, S_{t_j} ω) = v₀.
  have hvol_eq_on_F : ∀ ω ∈ F,
      (TemporalGraph.volume G.toTemporalGraph t_j (vm.S t_j ω) : ℝ) = (v₀ : ℝ) := by
    intro ω hω
    have : TemporalGraph.volume G.toTemporalGraph t_j (vm.S t_j ω) = v₀ := by
      rw [hF_S ω hω]
    exact_mod_cast this
  -- On F: τ'Nat ω = T_{j+1} ω.
  have hT_eq_τ'Nat_on_F : ∀ ω ∈ F,
      embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω = τ'Nat ω := by
    intro ω hω
    have hlt := hT_strict_on_F ω hω
    show _ = max t_j _
    omega
  -- ── Step 4: define vol_next := vol(τ'Nat) and the difference functionals ───
  set vol_next : Ω → ℕ := fun ω' =>
    TemporalGraph.volume G.toTemporalGraph (τ'Nat ω') (vm.S (τ'Nat ω') ω')
  have hInt_vol : Integrable (fun ω' => (vol_next ω' : ℝ)) vm.μ := hInt_vol_τ'
  -- E[vol(τ'Nat) | ℱ_{t_j}] ω ≤ vol(t_j, S_{t_j} ω) a.s.
  have hce_neg :
      (vm.μ : Measure _)[fun ω => -(vol_next ω : ℝ) | vm.ℱ t_j]
      =ᵐ[(vm.μ : Measure _)] -(vm.μ : Measure _)[fun ω => (vol_next ω : ℝ) | vm.ℱ t_j] :=
    condExp_neg _ _
  have hvol_cond_le_global : ∀ᵐ ω ∂(vm.μ : Measure _),
      ((vm.μ : Measure _)[fun ω' => (vol_next ω' : ℝ) | vm.ℱ t_j]) ω
        ≤ (TemporalGraph.volume G.toTemporalGraph t_j (vm.S t_j ω) : ℝ) := by
    filter_upwards [hcond_vol, hce_neg] with ω hcond_ω hceneg_ω
    have h := hcond_ω.trans_eq hceneg_ω
    simp only [Pi.neg_apply] at h
    linarith
  -- ── Step 5: Δ_fn, Δminus_fn, Jensen, integrabilities ───────────────────────
  set Δ_fn : Ω → ℝ := fun ω' => (vol_next ω' : ℝ) - (v₀ : ℝ)
  set Δminus_fn : Ω → ℝ := fun ω' => max (-(Δ_fn ω')) 0
  have hΔ_int : Integrable Δ_fn vm.μ :=
    hInt_vol.sub (integrable_const (v₀ : ℝ))
  have hΔminus_nn : ∀ ω', 0 ≤ Δminus_fn ω' := fun ω' => le_max_right _ _
  have hΔminus_bdd : ∀ ω', Δminus_fn ω' ≤ (v₀ : ℝ) := fun ω' => by
    simp only [Δminus_fn, Δ_fn]
    apply max_le
    · have : (0 : ℝ) ≤ (vol_next ω' : ℝ) := Nat.cast_nonneg _
      linarith
    · exact Nat.cast_nonneg _
  have hΔminus_aesm : AEStronglyMeasurable Δminus_fn vm.μ :=
    hΔ_int.1.neg.sup aestronglyMeasurable_const
  have hΔminus_L2 : MemLp Δminus_fn 2 vm.μ :=
    MemLp.of_bound hΔminus_aesm (v₀ : ℝ) (Filter.Eventually.of_forall fun ω' => by
      rw [Real.norm_of_nonneg (hΔminus_nn ω')]
      exact hΔminus_bdd ω')
  have hΔminus_int : Integrable Δminus_fn vm.μ := hΔminus_L2.integrable one_le_two
  have hΔminus_sq_int : Integrable (fun ω' => Δminus_fn ω' ^ 2) vm.μ :=
    hΔminus_L2.integrable_sq
  have hJensen : ∀ᵐ ω ∂(vm.μ : Measure _),
      ((vm.μ : Measure _)[Δminus_fn | vm.ℱ t_j]) ω ^ 2
        ≤ ((vm.μ : Measure _)[fun ω'' => Δminus_fn ω'' ^ 2 | vm.ℱ t_j]) ω :=
    sq_condExp_le_condExp_sq (vm.ℱ.le t_j) hΔminus_L2
  -- Δminus = (|Δ_fn| - Δ_fn) / 2
  have hΔminus_negpart : ∀ ω', Δminus_fn ω' = (|Δ_fn ω'| - Δ_fn ω') / 2 := fun ω' => by
    simp only [Δminus_fn]
    by_cases h : Δ_fn ω' ≤ 0
    · rw [max_eq_left (neg_nonneg.mpr h), abs_of_nonpos h]; ring
    · push Not at h
      rw [max_eq_right (neg_nonpos.mpr (le_of_lt h)), abs_of_pos h]; ring
  have hΔminus_condexp : (vm.μ : Measure _)[Δminus_fn | vm.ℱ t_j] =ᵐ[(vm.μ : Measure _)]
      fun ω' => (((vm.μ : Measure _)[fun ω'' => |Δ_fn ω''| | vm.ℱ t_j]) ω' -
        ((vm.μ : Measure _)[Δ_fn | vm.ℱ t_j]) ω') / 2 := by
    have habs_int : Integrable (fun ω' => |Δ_fn ω'|) vm.μ := hΔ_int.norm
    have hΔminus_eq : Δminus_fn = fun ω' => (|Δ_fn ω'| - Δ_fn ω') / 2 :=
      funext hΔminus_negpart
    rw [hΔminus_eq]
    have hcongr : (vm.μ : Measure _)[fun ω' => (|Δ_fn ω'| - Δ_fn ω') / 2 | vm.ℱ t_j] =ᵐ[(vm.μ : Measure _)]
        (vm.μ : Measure _)[(2 : ℝ)⁻¹ • ((fun ω' => |Δ_fn ω'|) - Δ_fn) | vm.ℱ t_j] := by
      apply condExp_congr_ae
      filter_upwards with ω''
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
    have hsub := condExp_sub habs_int hΔ_int (vm.ℱ t_j)
    have hsmul := condExp_smul (2 : ℝ)⁻¹ ((fun ω' => |Δ_fn ω'|) - Δ_fn) (vm.ℱ t_j)
        (μ := vm.μ)
    filter_upwards [hcongr, hsub, hsmul] with ω' hc h1 h2
    simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at h1 h2 hc ⊢
    linarith
  -- E[Δ_fn | ℱ_{t_j}] ω ≤ vol(t_j, S_{t_j} ω) - v₀ a.s. (globally, modulo on-F identity)
  have hΔ_condexp_eq : (vm.μ : Measure _)[Δ_fn | vm.ℱ t_j] =ᵐ[(vm.μ : Measure _)]
      (vm.μ : Measure _)[fun ω' => (vol_next ω' : ℝ) | vm.ℱ t_j] - fun _ => (v₀ : ℝ) := by
    have hsub := condExp_sub hInt_vol (integrable_const (v₀ : ℝ)) (vm.ℱ t_j)
    have hconst : (vm.μ : Measure _)[fun _ => (v₀ : ℝ) | vm.ℱ t_j] = fun _ => (v₀ : ℝ) :=
      condExp_const (μ := vm.μ) (vm.ℱ.le t_j) (v₀ : ℝ)
    filter_upwards [hsub] with ω' h1
    simp only [Pi.sub_apply] at h1 ⊢
    rw [hconst] at h1
    exact h1
  -- ── Step 6: hjump_F conversion to vol_next/v₀ ──────────────────────────────
  -- On F, volS(T_j ω') ω' = v₀ (uses hF_T ω' hω' and hF_S ω' hω').
  have hvolS_j_on_F : ∀ ω' ∈ F,
      vm.volS (embeddedChainTime G.toTemporalGraph vm Δ j ω') ω' = (v₀ : ℝ) := fun ω' hω' => by
    simp only [TemporalGraph.VoterModelAbstract.volS, hF_T ω' hω', hF_S ω' hω', hv₀_def]
  have hvolS_next : ∀ ω', vm.volS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω') ω' =
      (TemporalGraph.volume G.toTemporalGraph (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω')
        (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω') ω') : ℝ) := fun ω' => by
    simp only [TemporalGraph.VoterModelAbstract.volS]
  -- On F, also volS(T_{j+1} ω') ω' = vol_next ω' (uses hT_eq_τ'Nat_on_F).
  have hvolS_next_eq_vol_next_on_F : ∀ ω' ∈ F,
      vm.volS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω') ω' = (vol_next ω' : ℝ) := by
    intro ω' hω'
    rw [hvolS_next ω']
    have heq := hT_eq_τ'Nat_on_F ω' hω'
    show (TemporalGraph.volume G.toTemporalGraph _ (vm.S _ ω') : ℝ) = (TemporalGraph.volume G.toTemporalGraph _ (vm.S _ ω') : ℝ)
    rw [heq]
  -- ── PART B: hjump_F integrand conversion ────────────────────────────────────
  -- Define the hjump_F integrand and compare with |Δ_fn|. They agree on F.
  set X_orig : Ω → ℝ := fun ω' =>
    |vm.volS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω') ω' -
      vm.volS (embeddedChainTime G.toTemporalGraph vm Δ j ω') ω'|
  have hF_meas_top : MeasurableSet F := vm.ℱ.le t_j _ hF_meas
  -- On F: X_orig ω' = |Δ_fn ω'|.
  have hX_eq_on_F : ∀ ω' ∈ F, X_orig ω' = |Δ_fn ω'| := by
    intro ω' hω'
    simp only [X_orig, Δ_fn]
    rw [hvolS_next_eq_vol_next_on_F ω' hω', hvolS_j_on_F ω' hω']
  -- F-indicator of X_orig equals F-indicator of |Δ_fn| pointwise globally.
  have hindicator_eq : ∀ ω' : Ω,
      F.indicator X_orig ω' = F.indicator (fun ω'' => |Δ_fn ω''|) ω' := by
    intro ω'
    by_cases hω' : ω' ∈ F
    · rw [Set.indicator_of_mem hω', Set.indicator_of_mem hω', hX_eq_on_F ω' hω']
    · rw [Set.indicator_of_notMem hω', Set.indicator_of_notMem hω']
  -- Integrability of |Δ_fn| (from hΔ_int).
  have hΔ_abs_int : Integrable (fun ω' => |Δ_fn ω'|) vm.μ := hΔ_int.norm
  -- Integrability of F.indicator X_orig: equal a.e. to F.indicator |Δ_fn|.
  have hind_eq_ae : (fun ω' => F.indicator X_orig ω') =ᵐ[(vm.μ : Measure _)]
      fun ω' => F.indicator (fun ω'' => |Δ_fn ω''|) ω' :=
    Filter.Eventually.of_forall hindicator_eq
  have hind_int_new : Integrable (fun ω' => F.indicator (fun ω'' => |Δ_fn ω''|) ω') vm.μ :=
    hΔ_abs_int.indicator hF_meas_top
  have hind_int_orig : Integrable (fun ω' => F.indicator X_orig ω') vm.μ :=
    hind_int_new.congr hind_eq_ae.symm
  -- Define convenience aliases.
  set Y_orig : Ω → ℝ := fun ω' => F.indicator X_orig ω' with hY_orig_def
  set Y_new : Ω → ℝ := fun ω' => F.indicator (fun ω'' => |Δ_fn ω''|) ω' with hY_new_def
  have hY_eq : Y_orig =ᵐ[(vm.μ : Measure _)] Y_new := hind_eq_ae
  have hY_int_orig : Integrable Y_orig vm.μ := hind_int_orig
  have hY_int_new : Integrable Y_new vm.μ := hind_int_new
  -- Cond.exp.s of Y_orig and Y_new agree μ-a.e.
  have hcondY_eq : (vm.μ : Measure _)[Y_orig | vm.ℱ t_j] =ᵐ[(vm.μ : Measure _)] (vm.μ : Measure _)[Y_new | vm.ℱ t_j] :=
    condExp_congr_ae hY_eq
  -- For X_orig integrable, μ[F.indicator X_orig | ℱ_{t_j}] = F.indicator (μ[X_orig | ℱ_{t_j}]) a.e.
  -- However, hjump_F provides the cond.exp. of X_orig (defined as 0 if not integrable).
  -- We need: ∀ᵐ ω ∂(μ.restrict F), μ[Y_orig | ℱ_{t_j}] ω = μ[X_orig | ℱ_{t_j}] ω.
  -- This follows from `condExp_indicator` IF X_orig is integrable. We derive
  -- integrability of X_orig from hjump_F by a finite-measure argument: X_orig
  -- is bounded by sum of two volumes at variable times. Under hfix, all
  -- per-vertex degrees agree across time, but the volume at vm.S(t) ω' depends
  -- on the set S — bounded by volume univ which IS time-invariant under hfix.
  -- Volume_univ in a fixed-degree graph: ∑_v G.degree v at time t = ∑_v G.degree v at 0.
  -- We bound X_orig ≤ 2 * volU where volU = G.volume 0 univ.
  set volU : ℕ := TemporalGraph.volume G.toTemporalGraph 0 Finset.univ with hvolU_def
  have hvolume_le_volU : ∀ (t : ℕ) (S : Finset V),
      (TemporalGraph.volume G.toTemporalGraph t S : ℝ) ≤ (volU : ℝ) := by
    intro t S
    -- volume G t S ≤ volume G t univ (monotonicity) = volume G 0 univ (FixedDegrees).
    have h1 : TemporalGraph.volume G.toTemporalGraph t S ≤ TemporalGraph.volume G.toTemporalGraph t Finset.univ := by
      simp only [TemporalGraph.volume]
      exact SimpleGraph.volume_mono (Finset.subset_univ S)
    have h2 : TemporalGraph.volume G.toTemporalGraph t Finset.univ = volU := by
      simp only [TemporalGraph.volume, hvolU_def, SimpleGraph.volume]
      refine Finset.sum_congr rfl ?_
      intro v _
      exact G.degrees_fixed v t 0
    exact_mod_cast h1.trans h2.le
  have hX_orig_bound : ∀ ω' : Ω, X_orig ω' ≤ (2 * volU : ℝ) := by
    intro ω'
    simp only [X_orig, TemporalGraph.VoterModelAbstract.volS]
    have h1 := hvolume_le_volU (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω')
      (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω') ω')
    have h2 := hvolume_le_volU (embeddedChainTime G.toTemporalGraph vm Δ j ω')
      (vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω') ω')
    have h1nn : (0 : ℝ) ≤
        (TemporalGraph.volume G.toTemporalGraph (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω')
          (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω') ω') : ℝ) := Nat.cast_nonneg _
    have h2nn : (0 : ℝ) ≤
        (TemporalGraph.volume G.toTemporalGraph (embeddedChainTime G.toTemporalGraph vm Δ j ω')
          (vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω') ω') : ℝ) := Nat.cast_nonneg _
    have habs : |(TemporalGraph.volume G.toTemporalGraph (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω')
        (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω') ω') : ℝ) -
        (TemporalGraph.volume G.toTemporalGraph (embeddedChainTime G.toTemporalGraph vm Δ j ω')
          (vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω') ω') : ℝ)| ≤ 2 * (volU : ℝ) := by
      rw [abs_le]; constructor <;> linarith
    exact habs
  -- Integrability of X_orig via finite indicator decomposition over T_j and T_{j+1}.
  -- T_j ≤ cap (since hT_cap gives T_j ω ≤ cap = ∑ range (j+2) Δ - 1) — but we need
  -- a uniform bound on T_j. Use: T_j ≤ ∑ range (j+1) Δ pointwise (proved like
  -- hT_next_le_global). Set capJ := ∑ range (j+1) Δ.
  set capJ : ℕ := ∑ k ∈ Finset.range (j + 1), Δ k with hcapJ_def
  have hT_j_le_global : ∀ ω, embeddedChainTime G.toTemporalGraph vm Δ j ω ≤ capJ := by
    intro ω
    suffices h : ∀ i ω, embeddedChainTime G.toTemporalGraph vm Δ i ω ≤ ∑ k ∈ Finset.range (i + 1), Δ k by
      exact h j ω
    intro i
    induction i with
    | zero => intro ω; simp [embeddedChainTime]
    | succ i' _ =>
      intro ω
      simp only [embeddedChainTime]
      -- After def change, T_{i'+1} ω = vET (T_{i'} ω) ((∑ range (i'+1) Δ) - 1) ω.
      have h := volumeExcursionTime_le_succ G.toTemporalGraph vm (embeddedChainTime G.toTemporalGraph vm Δ i' ω)
        ((∑ k ∈ Finset.range (i' + 1), Δ k) - 1) ω
      have h_pos : 1 ≤ ∑ k ∈ Finset.range (i' + 1), Δ k := by
        have h0 : Δ 0 ≤ ∑ k ∈ Finset.range (i' + 1), Δ k :=
          Finset.single_le_sum (f := Δ) (fun k _ => Nat.zero_le _)
            (Finset.mem_range.mpr (by omega))
        exact le_trans (hΔ_pos 0) h0
      have hsub : ((∑ k ∈ Finset.range (i' + 1), Δ k) - 1) + 1 =
          ∑ k ∈ Finset.range (i' + 1), Δ k :=
        Nat.sub_add_cancel h_pos
      -- The outer claim has range (i'+1+1); the inner def now gives ≤ range (i'+1).
      -- Bridge via monotonicity of partial sums.
      have hmono : ∑ k ∈ Finset.range (i' + 1), Δ k ≤ ∑ k ∈ Finset.range (i' + 1 + 1), Δ k :=
        Finset.sum_le_sum_of_subset (fun k hk => Finset.mem_range.mpr
          (lt_of_lt_of_le (Finset.mem_range.mp hk) (Nat.le_succ _)))
      linarith
  -- Stopping time for T_j.
  have hT_j_stop : IsStoppingTime vm.ℱ
      (fun ω => (embeddedChainTime G.toTemporalGraph vm Δ j ω : ℕ∞)) :=
    embeddedChainTime_isStoppingTime G.toTemporalGraph vm Δ hS_meas j
  -- Measurability of {T_j = k} and {T_{j+1} = k}.
  have hTj_eq_meas : ∀ k, MeasurableSet {ω | embeddedChainTime G.toTemporalGraph vm Δ j ω = k} := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have : {ω | embeddedChainTime G.toTemporalGraph vm Δ j ω = 0} =
          {ω | (embeddedChainTime G.toTemporalGraph vm Δ j ω : ℕ∞) ≤ 0} := by ext ω; simp
      rw [this]; exact vm.ℱ.le 0 _ (hT_j_stop 0)
    · have : {ω | embeddedChainTime G.toTemporalGraph vm Δ j ω = k} =
          {ω | (embeddedChainTime G.toTemporalGraph vm Δ j ω : ℕ∞) ≤ ↑k} \
          {ω | (embeddedChainTime G.toTemporalGraph vm Δ j ω : ℕ∞) ≤ ↑(k - 1)} := by
        ext ω; simp only [Set.mem_setOf_eq, Set.mem_sdiff, ENat.coe_le_coe]; omega
      rw [this]
      exact (vm.ℱ.le k _ (hT_j_stop k)).diff (vm.ℱ.le (k - 1) _ (hT_j_stop (k - 1)))
  have hTnext_eq_meas : ∀ k, MeasurableSet
      {ω | embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω = k} := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have : {ω | embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω = 0} =
          {ω | (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω : ℕ∞) ≤ 0} := by ext ω; simp
      rw [this]; exact vm.ℱ.le 0 _ (hT_stop 0)
    · have : {ω | embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω = k} =
          {ω | (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω : ℕ∞) ≤ ↑k} \
          {ω | (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω : ℕ∞) ≤ ↑(k - 1)} := by
        ext ω; simp only [Set.mem_setOf_eq, Set.mem_sdiff, ENat.coe_le_coe]; omega
      rw [this]
      exact (vm.ℱ.le k _ (hT_stop k)).diff (vm.ℱ.le (k - 1) _ (hT_stop (k - 1)))
  -- A_t measurability into discrete Finset V.
  have hA_meas : ∀ k, @Measurable Ω (Finset V) (vm.ℱ k) ⊤ (vm.opinionZeroSet k) := fun k =>
    (vm.A_stronglyAdapted k).measurable
  -- ψ_fn (k₁, s₁, k₂, s₂) := |volume G k₂ s₂ - volume G k₁ s₁|.
  let ψ_fn : ℕ → Finset V → ℕ → Finset V → ℝ :=
    fun k₁ s₁ k₂ s₂ => |(TemporalGraph.volume G.toTemporalGraph k₂ s₂ : ℝ) - (TemporalGraph.volume G.toTemporalGraph k₁ s₁ : ℝ)|
  -- Per-time-index integrability of ω ↦ ψ_fn k₁ (S k₁ ω) k₂ (S k₂ ω).
  have hψ_int_indexed : ∀ k₁ k₂,
      Integrable (fun ω => ψ_fn k₁ (vm.S k₁ ω) k₂ (vm.S k₂ ω)) vm.μ := by
    intro k₁ k₂
    refine Integrable.of_bound (μ := vm.μ)
      (f := fun ω => ψ_fn k₁ (vm.S k₁ ω) k₂ (vm.S k₂ ω))
      ?_ (2 * (volU : ℝ)) ?_
    · -- ψ_fn k₁ (S k₁ ω) k₂ (S k₂ ω) is bounded by a finite max ‖·‖ over (Finset V)²,
      -- so integrable_const dominates and we just need ae-strong-measurability.
      -- Use the SAME pattern as IntervalChain's hφS_int: factor through vm.opinionZeroSet k_i,
      -- but for two indices we need the pair to be measurable. Take max of the
      -- two source σ-algebras (vm.ℱ k₁ ⊔ vm.ℱ k₂) ≤ ambient.
      have hψ_eq : (fun ω => ψ_fn k₁ (vm.S k₁ ω) k₂ (vm.S k₂ ω)) =
          (fun ω => ψ_fn k₁ (VoterModel.minoritySet G.toTemporalGraph k₁ (vm.opinionZeroSet k₁ ω))
                          k₂ (VoterModel.minoritySet G.toTemporalGraph k₂ (vm.opinionZeroSet k₂ ω))) := by
        funext ω; rfl
      rw [hψ_eq]
      -- Split via indicator over the FINITE product (Finset V × Finset V).
      -- Sum over (s₁, s₂) of indicator {vm.opinionZeroSet k₁ = s₁ ∧ vm.opinionZeroSet k₂ = s₂} of constant value.
      have hsum_eq : (fun ω => ψ_fn k₁ (VoterModel.minoritySet G.toTemporalGraph k₁ (vm.opinionZeroSet k₁ ω))
                          k₂ (VoterModel.minoritySet G.toTemporalGraph k₂ (vm.opinionZeroSet k₂ ω))) =
          fun ω => ∑ s₁ : Finset V, ∑ s₂ : Finset V,
            Set.indicator
              ({ω | vm.opinionZeroSet k₁ ω = s₁} ∩ {ω | vm.opinionZeroSet k₂ ω = s₂})
              (fun _ => ψ_fn k₁ (VoterModel.minoritySet G.toTemporalGraph k₁ s₁)
                              k₂ (VoterModel.minoritySet G.toTemporalGraph k₂ s₂)) ω := by
        funext ω
        rw [Finset.sum_eq_single (vm.opinionZeroSet k₁ ω)]
        · rw [Finset.sum_eq_single (vm.opinionZeroSet k₂ ω)]
          · rw [Set.indicator_of_mem (by exact ⟨Set.mem_setOf.mpr rfl, Set.mem_setOf.mpr rfl⟩)]
          · intro s₂ _ hs₂
            rw [Set.indicator_of_notMem (by rintro ⟨_, hh⟩; exact hs₂ (Set.mem_setOf.mp hh).symm)]
          · intro h; exact absurd (Finset.mem_univ _) h
        · intro s₁ _ hs₁
          rw [Finset.sum_eq_zero]
          intro s₂ _
          rw [Set.indicator_of_notMem (by rintro ⟨hh, _⟩; exact hs₁ (Set.mem_setOf.mp hh).symm)]
        · intro h; exact absurd (Finset.mem_univ _) h
      rw [hsum_eq]
      -- Each indicator-of-constant is measurable: the underlying set is measurable.
      refine Finset.aestronglyMeasurable_fun_sum (M := ℝ) _ fun s₁ _ => ?_
      refine Finset.aestronglyMeasurable_fun_sum (M := ℝ) _ fun s₂ _ => ?_
      have hms₁ : MeasurableSet {ω | vm.opinionZeroSet k₁ ω = s₁} := by
        have : @MeasurableSet Ω (vm.ℱ k₁) {ω | vm.opinionZeroSet k₁ ω = s₁} :=
          hA_meas k₁ (MeasurableSpace.measurableSet_top (s := ({s₁} : Set (Finset V))))
        exact vm.ℱ.le k₁ _ this
      have hms₂ : MeasurableSet {ω | vm.opinionZeroSet k₂ ω = s₂} := by
        have : @MeasurableSet Ω (vm.ℱ k₂) {ω | vm.opinionZeroSet k₂ ω = s₂} :=
          hA_meas k₂ (MeasurableSpace.measurableSet_top (s := ({s₂} : Set (Finset V))))
        exact vm.ℱ.le k₂ _ this
      exact (aestronglyMeasurable_const.indicator (hms₁.inter hms₂))
    · refine ae_of_all _ fun ω => ?_
      simp only [ψ_fn]
      have h1 := hvolume_le_volU k₂ (VoterModel.minoritySet G.toTemporalGraph k₂ (vm.opinionZeroSet k₂ ω))
      have h2 := hvolume_le_volU k₁ (VoterModel.minoritySet G.toTemporalGraph k₁ (vm.opinionZeroSet k₁ ω))
      have h1nn : (0 : ℝ) ≤ (TemporalGraph.volume G.toTemporalGraph k₂
          (VoterModel.minoritySet G.toTemporalGraph k₂ (vm.opinionZeroSet k₂ ω)) : ℝ) := Nat.cast_nonneg _
      have h2nn : (0 : ℝ) ≤ (TemporalGraph.volume G.toTemporalGraph k₁
          (VoterModel.minoritySet G.toTemporalGraph k₁ (vm.opinionZeroSet k₁ ω)) : ℝ) := Nat.cast_nonneg _
      rw [Real.norm_of_nonneg (abs_nonneg _)]
      have habs_bd : |(TemporalGraph.volume G.toTemporalGraph k₂ (vm.S k₂ ω) : ℝ) -
            (TemporalGraph.volume G.toTemporalGraph k₁ (vm.S k₁ ω) : ℝ)| ≤ 2 * (volU : ℝ) := by
        rw [abs_le]
        have h1' := hvolume_le_volU k₂ (vm.S k₂ ω)
        have h2' := hvolume_le_volU k₁ (vm.S k₁ ω)
        have h1nn' : (0 : ℝ) ≤ (TemporalGraph.volume G.toTemporalGraph k₂ (vm.S k₂ ω) : ℝ) := Nat.cast_nonneg _
        have h2nn' : (0 : ℝ) ≤ (TemporalGraph.volume G.toTemporalGraph k₁ (vm.S k₁ ω) : ℝ) := Nat.cast_nonneg _
        constructor <;> linarith
      show |(TemporalGraph.volume G.toTemporalGraph k₂ (VoterModel.minoritySet G.toTemporalGraph k₂ (vm.opinionZeroSet k₂ ω)) : ℝ) -
          (TemporalGraph.volume G.toTemporalGraph k₁ (VoterModel.minoritySet G.toTemporalGraph k₁ (vm.opinionZeroSet k₁ ω)) : ℝ)|
        ≤ 2 * (volU : ℝ)
      exact habs_bd
  -- Decompose X_orig as a double finite sum of indicators.
  have hX_orig_eq_sum : X_orig = fun ω =>
      ∑ k₁ ∈ Finset.range (capJ + 1),
        ∑ k₂ ∈ Finset.range (t' + 1),
          Set.indicator (
            {ω | embeddedChainTime G.toTemporalGraph vm Δ j ω = k₁} ∩
            {ω | embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω = k₂})
            (fun ω => ψ_fn k₁ (vm.S k₁ ω) k₂ (vm.S k₂ ω)) ω := by
    funext ω
    -- For each ω the double sum collapses to the single term (T_j ω, T_{j+1} ω).
    have hT_j_bd : embeddedChainTime G.toTemporalGraph vm Δ j ω ∈ Finset.range (capJ + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le (hT_j_le_global ω))
    have hT_next_bd : embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω ∈ Finset.range (t' + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le (hT_next_le_global ω))
    rw [Finset.sum_eq_single (embeddedChainTime G.toTemporalGraph vm Δ j ω)]
    · rw [Finset.sum_eq_single (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)]
      · rw [Set.indicator_of_mem (by
          exact ⟨Set.mem_setOf.mpr rfl, Set.mem_setOf.mpr rfl⟩)]
        show X_orig ω = _
        simp only [X_orig, TemporalGraph.VoterModelAbstract.volS, ψ_fn]
      · intro k₂ _ hk₂
        rw [Set.indicator_of_notMem (by
          rintro ⟨_, hh⟩
          exact hk₂ (Set.mem_setOf.mp hh).symm)]
      · intro h; exact absurd hT_next_bd h
    · intro k₁ _ hk₁
      rw [Finset.sum_eq_zero]
      intro k₂ _
      rw [Set.indicator_of_notMem (by
        rintro ⟨hh, _⟩
        exact hk₁ (Set.mem_setOf.mp hh).symm)]
    · intro h; exact absurd hT_j_bd h
  -- Integrability of the double-sum.
  have hX_orig_int : Integrable X_orig vm.μ := by
    rw [hX_orig_eq_sum]
    refine integrable_finsetSum _ fun k₁ _ => ?_
    refine integrable_finsetSum _ fun k₂ _ => ?_
    refine (hψ_int_indexed k₁ k₂).indicator ?_
    exact (hTj_eq_meas k₁).inter (hTnext_eq_meas k₂)
  -- With X_orig integrable, we now use `condExp_indicator`.
  -- μ[F.indicator X_orig | ℱ_{t_j}] =ᵐ[μ] F.indicator (μ[X_orig | ℱ_{t_j}]).
  have hci_orig : (vm.μ : Measure _)[fun ω' => F.indicator X_orig ω' | vm.ℱ t_j] =ᵐ[(vm.μ : Measure _)]
      F.indicator ((vm.μ : Measure _)[X_orig | vm.ℱ t_j]) :=
    condExp_indicator hX_orig_int hF_meas
  -- Similarly for |Δ_fn|.
  have hci_new : (vm.μ : Measure _)[fun ω' => F.indicator (fun ω'' => |Δ_fn ω''|) ω' | vm.ℱ t_j] =ᵐ[(vm.μ : Measure _)]
      F.indicator ((vm.μ : Measure _)[fun ω' => |Δ_fn ω'| | vm.ℱ t_j]) :=
    condExp_indicator hΔ_abs_int hF_meas
  -- Combining: F.indicator (μ[X_orig | ℱ_{t_j}]) = F.indicator (μ[|Δ_fn| | ℱ_{t_j}]) a.e.
  have hcondX_eq_F :
      F.indicator ((vm.μ : Measure _)[X_orig | vm.ℱ t_j]) =ᵐ[(vm.μ : Measure _)]
        F.indicator ((vm.μ : Measure _)[fun ω' => |Δ_fn ω'| | vm.ℱ t_j]) := by
    have h1 := hci_orig.symm
    have h2 := hcondY_eq
    have h3 := hci_new
    -- hcondY_eq is μ[Y_orig | _] =ᵐ μ[Y_new | _].
    -- Combine h1 (F.indicator (μ[X_orig|_]) =ᵐ μ[Y_orig|_]), h2, h3.
    filter_upwards [h1, h2, h3] with ω h1ω h2ω h3ω
    exact h1ω.trans (h2ω.trans h3ω)
  -- On F (indicator = 1), this gives `μ[X_orig | ℱ_{t_j}] = μ[|Δ_fn| | ℱ_{t_j}]`.
  have hcondX_eq_on_F : ∀ᵐ ω ∂((vm.μ : Measure _).restrict F),
      ((vm.μ : Measure _)[X_orig | vm.ℱ t_j]) ω = ((vm.μ : Measure _)[fun ω' => |Δ_fn ω'| | vm.ℱ t_j]) ω := by
    rw [ae_restrict_iff' hF_meas_top]
    filter_upwards [hcondX_eq_F] with ω hω hω_in_F
    rw [Set.indicator_of_mem hω_in_F, Set.indicator_of_mem hω_in_F] at hω
    exact hω
  -- Now hjump_F gives a bound on μ[X_orig | ℱ_{t_j}] a.e. on F. Convert to a
  -- bound on μ[|Δ_fn| | ℱ_{t_j}] a.e. on F.
  have hjump_F_abs : ∀ᵐ ω ∂((vm.μ : Measure _).restrict F),
      ((vm.μ : Measure _)[fun ω' => |Δ_fn ω'| | vm.ℱ t_j]) ω ≥ 1 / 8 * (v₀ : ℝ) := by
    filter_upwards [hjump_F, hcondX_eq_on_F] with ω hjump_ω hcond_ω
    rw [← hcond_ω]
    exact hjump_ω
  -- ── PART C: log-difference machinery (mirrors chi_down_drift_voter_unstable) ─
  -- Integrability of log-diff (using vol_next = vol(τ'Nat)).
  have hchi_int : Integrable (fun ω' =>
      Real.log (1 + (vol_next ω' : ℝ)) - Real.log (1 + (v₀ : ℝ))) vm.μ := by
    apply (hInt_vol.add (integrable_const (v₀ : ℝ))).mono
    · apply AEStronglyMeasurable.sub
      · exact (Real.measurable_log.comp_aemeasurable
            (aemeasurable_const.add hInt_vol.1.aemeasurable)).aestronglyMeasurable
      · exact aestronglyMeasurable_const
    · filter_upwards with ω'
      set vol' := (vol_next ω' : ℝ)
      have hnn : (0:ℝ) ≤ vol' := Nat.cast_nonneg _
      have hv0_nn : (0:ℝ) ≤ (v₀ : ℝ) := Nat.cast_nonneg _
      have hlog_nn : 0 ≤ Real.log (1 + vol') := Real.log_nonneg (by linarith)
      have hlog_le : Real.log (1 + vol') ≤ vol' := by
        linarith [Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + vol' by linarith)]
      have hlogv0_nn : 0 ≤ Real.log (1 + (v₀ : ℝ)) := Real.log_nonneg (by linarith)
      have hlogv0_le : Real.log (1 + (v₀ : ℝ)) ≤ (v₀ : ℝ) := by
        linarith [Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + (v₀ : ℝ) by linarith)]
      simp only [Pi.add_apply]
      rw [Real.norm_of_nonneg (show (0:ℝ) ≤ vol' + ↑v₀ by linarith)]
      rw [Real.norm_eq_abs]; rw [abs_le]
      constructor <;> linarith
  -- g_fn and the pointwise log-difference bound (from chi_aux_log_diff_le).
  set g_fn : Ω → ℝ := fun ω' =>
    Δ_fn ω' / (1 + (v₀ : ℝ)) -
    if (vol_next ω' : ℝ) < (v₀ : ℝ) then
      (Δ_fn ω') ^ 2 / (2 * (1 + (v₀ : ℝ)) ^ 2)
    else 0
  have hg_split : g_fn = fun ω' =>
      (1 + (v₀ : ℝ))⁻¹ * Δ_fn ω' -
      (2 * (1 + (v₀ : ℝ)) ^ 2)⁻¹ * Δminus_fn ω' ^ 2 := by
    ext ω'
    simp only [g_fn, Δ_fn, Δminus_fn]
    split_ifs with hlt
    · have hnn : 0 ≤ -((vol_next ω' : ℝ) - (v₀ : ℝ)) := by linarith
      rw [max_eq_left hnn]; field_simp
    · push Not at hlt
      rw [max_eq_right (by linarith), zero_pow (by norm_num), mul_zero, sub_zero]
      field_simp; ring
  have hf1_int_bd : Integrable (fun ω' => (1 + (v₀ : ℝ))⁻¹ * Δ_fn ω') vm.μ :=
    hΔ_int.mono (aestronglyMeasurable_const.mul hΔ_int.1)
      (Filter.Eventually.of_forall fun ω' => by
        rw [norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr (le_of_lt h1v0_pos))]
        exact mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ (by linarith)))
  have hf2_int_bd : Integrable (fun ω' => (2 * (1 + (v₀ : ℝ)) ^ 2)⁻¹ * Δminus_fn ω' ^ 2) vm.μ :=
    hΔminus_sq_int.mono (aestronglyMeasurable_const.mul hΔminus_sq_int.1)
      (Filter.Eventually.of_forall fun ω' => by
        have hden_pos : (0:ℝ) < 2 * (1 + (v₀ : ℝ)) ^ 2 := by positivity
        rw [norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr (le_of_lt hden_pos))]
        exact mul_le_of_le_one_left (norm_nonneg _)
          (inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg (1 + (v₀ : ℝ))])))
  have hg_int : Integrable g_fn vm.μ := by
    rw [hg_split]
    exact hf1_int_bd.sub hf2_int_bd
  -- Pointwise log-diff bound: μ-a.e. globally.
  have hlog_le_g : ∀ᵐ ω ∂(vm.μ : Measure _),
      ((vm.μ : Measure _)[fun ω' => Real.log (1 + (vol_next ω' : ℝ)) -
          Real.log (1 + (v₀ : ℝ)) | vm.ℱ t_j]) ω
        ≤ ((vm.μ : Measure _)[g_fn | vm.ℱ t_j]) ω :=
    condExp_mono hchi_int hg_int (ae_of_all (vm.μ : Measure Ω) fun ω' => by
      simp only [g_fn]
      exact chi_aux_log_diff_le _ _ (Nat.cast_pos.mpr hv₀_pos) (Nat.cast_nonneg _))
  -- Pullouts (constants).
  have hf1_pullout : (vm.μ : Measure _)[fun ω' => (1 + (v₀ : ℝ))⁻¹ * Δ_fn ω' | vm.ℱ t_j]
      =ᵐ[(vm.μ : Measure _)] fun ω' => (1 + (v₀ : ℝ))⁻¹ * ((vm.μ : Measure _)[Δ_fn | vm.ℱ t_j]) ω' :=
    condExp_mul_of_stronglyMeasurable_left stronglyMeasurable_const hf1_int_bd hΔ_int
  have hf2_pullout :
      (vm.μ : Measure _)[fun ω' => (2 * (1 + (v₀ : ℝ)) ^ 2)⁻¹ * Δminus_fn ω' ^ 2 | vm.ℱ t_j]
        =ᵐ[(vm.μ : Measure _)] fun ω' =>
          (2 * (1 + (v₀ : ℝ)) ^ 2)⁻¹ * ((vm.μ : Measure _)[fun ω'' => Δminus_fn ω'' ^ 2 | vm.ℱ t_j]) ω' :=
    condExp_mul_of_stronglyMeasurable_left stronglyMeasurable_const hf2_int_bd hΔminus_sq_int
  -- E[g_fn | ℱ t_j] = E[f1 | ℱ t_j] - E[f2 | ℱ t_j].
  have hg_condexp : (vm.μ : Measure _)[g_fn | vm.ℱ t_j] =ᵐ[(vm.μ : Measure _)]
      (vm.μ : Measure _)[fun ω' => (1 + (v₀ : ℝ))⁻¹ * Δ_fn ω' | vm.ℱ t_j] -
      (vm.μ : Measure _)[fun ω' => (2 * (1 + (v₀ : ℝ)) ^ 2)⁻¹ * Δminus_fn ω' ^ 2 | vm.ℱ t_j] := by
    rw [hg_split]; exact condExp_sub hf1_int_bd hf2_int_bd (vm.ℱ t_j)
  -- ── PART D: E[Δ_fn | ℱ_{t_j}] ω ≤ 0 a.e. on F ──────────────────────────────
  -- From hvol_cond_le_global and hvol_eq_on_F (only ≤ 0 holds on F, since
  -- the supermartingale bound RHS is v₀ only on F).
  have hΔ_le_on_F : ∀ᵐ ω ∂((vm.μ : Measure _).restrict F),
      ((vm.μ : Measure _)[Δ_fn | vm.ℱ t_j]) ω ≤ 0 := by
    -- On F, hvol_eq_on_F says vol(t_j, S_{t_j} ω) = v₀, so the RHS of
    -- hvol_cond_le_global becomes v₀. Combined with hΔ_condexp_eq, we get
    -- E[Δ_fn|ℱ_{t_j}] ω ≤ 0 on F.
    have h_vol_eq_F : ∀ᵐ ω ∂((vm.μ : Measure _).restrict F),
        (TemporalGraph.volume G.toTemporalGraph t_j (vm.S t_j ω) : ℝ) = (v₀ : ℝ) :=
      (ae_restrict_iff' hF_meas_top).mpr (Filter.Eventually.of_forall hvol_eq_on_F)
    filter_upwards [ae_restrict_of_ae hΔ_condexp_eq, ae_restrict_of_ae hvol_cond_le_global,
      h_vol_eq_F] with ω hΔeq hcondle hveq
    simp only [Pi.sub_apply] at hΔeq
    rw [hveq] at hcondle
    linarith
  -- ── PART E: final bound on E[log_diff | ℱ_{t_j}] ω ≤ -1/2048 a.e. on F ────
  have hfinal_cond : ∀ᵐ ω ∂((vm.μ : Measure _).restrict F),
      ((vm.μ : Measure _)[fun ω' => Real.log (1 + (vol_next ω' : ℝ)) -
          Real.log (1 + (v₀ : ℝ)) | vm.ℱ t_j]) ω ≤ -1 / 2048 := by
    filter_upwards [ae_restrict_of_ae hlog_le_g, ae_restrict_of_ae hJensen,
      hΔ_le_on_F, ae_restrict_of_ae hΔminus_condexp, ae_restrict_of_ae hg_condexp,
      ae_restrict_of_ae hf1_pullout, ae_restrict_of_ae hf2_pullout, hjump_F_abs]
      with ω hlogleg hJensen_ω hΔ_le hΔminus_cond hg_cond hf1_po hf2_po hjump_ω
    -- Collect intermediate values.
    set A := ((vm.μ : Measure _)[Δ_fn | vm.ℱ t_j]) ω
    set B := ((vm.μ : Measure _)[fun ω' => |Δ_fn ω'| | vm.ℱ t_j]) ω
    set Cm := ((vm.μ : Measure _)[Δminus_fn | vm.ℱ t_j]) ω
    set Csq := ((vm.μ : Measure _)[fun ω'' => Δminus_fn ω'' ^ 2 | vm.ℱ t_j]) ω
    have hA_le : A ≤ 0 := hΔ_le
    have hB_ge : 1 / 8 * (v₀ : ℝ) ≤ B := hjump_ω
    have hCm_eq : Cm = (B - A) / 2 := hΔminus_cond
    have hCm_ge : 1 / 8 * (v₀ : ℝ) / 2 ≤ Cm := by linarith
    have hCsq_ge : Cm ^ 2 ≤ Csq := hJensen_ω
    have hg_val : ((vm.μ : Measure _)[g_fn | vm.ℱ t_j]) ω =
        (1 + (v₀ : ℝ))⁻¹ * A - (2 * (1 + (v₀ : ℝ)) ^ 2)⁻¹ * Csq := by
      simp only [Pi.sub_apply] at hg_cond hf1_po hf2_po
      linarith [hg_cond, hf1_po, hf2_po]
    calc (vm.μ : Measure _)[fun ω' => Real.log (1 + (vol_next ω' : ℝ)) -
            Real.log (1 + (v₀ : ℝ)) | vm.ℱ t_j] ω
        ≤ ((vm.μ : Measure _)[g_fn | vm.ℱ t_j]) ω := hlogleg
      _ = (1 + (v₀ : ℝ))⁻¹ * A - (2 * (1 + (v₀ : ℝ)) ^ 2)⁻¹ * Csq := hg_val
      _ ≤ 0 - (2 * (1 + (v₀ : ℝ)) ^ 2)⁻¹ * Cm ^ 2 := by
            have hterm1 : (1 + (v₀ : ℝ))⁻¹ * A ≤ 0 :=
              mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (le_of_lt h1v0_pos)) hA_le
            have hterm2 : (2 * (1 + (v₀ : ℝ)) ^ 2)⁻¹ * Cm ^ 2 ≤
                (2 * (1 + (v₀ : ℝ)) ^ 2)⁻¹ * Csq :=
              mul_le_mul_of_nonneg_left hCsq_ge (inv_nonneg.mpr (by positivity))
            linarith
      _ ≤ 0 - (2 * (1 + (v₀ : ℝ)) ^ 2)⁻¹ * (1 / 8 * (v₀ : ℝ) / 2) ^ 2 := by
            apply sub_le_sub_left
            apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (by positivity))
            exact pow_le_pow_left₀ (by positivity) hCm_ge 2
      _ ≤ -1 / 2048 := by
            have h4v2 : (1 + (v₀ : ℝ)) ^ 2 ≤ 4 * (v₀ : ℝ) ^ 2 := by nlinarith
            have hden_pos : (0:ℝ) < 2 * (1 + (v₀ : ℝ)) ^ 2 := by positivity
            have hkey : 1 / 2048 ≤ (1 / 8 * (v₀ : ℝ) / 2) ^ 2 / (2 * (1 + (v₀ : ℝ)) ^ 2) := by
              rw [le_div_iff₀ hden_pos]
              nlinarith [sq_nonneg (v₀ : ℝ)]
            linarith [show (2 * (1 + (v₀ : ℝ)) ^ 2)⁻¹ * (1 / 8 * (v₀ : ℝ) / 2) ^ 2 =
              (1 / 8 * (v₀ : ℝ) / 2) ^ 2 / (2 * (1 + (v₀ : ℝ)) ^ 2) from by ring]
  -- ── PART F: integration over F ──────────────────────────────────────────────
  -- (i) χ(T_{j+1}, S_{T_{j+1}}) - χ(t_j, s_j) equals the log diff on F (uses
  -- hT_eq_τ'Nat_on_F + hchi_s₀-style identity).
  have hchi_s_j : TemporalGraph.chiPotential G.toTemporalGraph t_j s_j = Real.log (1 + (v₀ : ℝ)) := by
    simp [TemporalGraph.chiPotential, hv₀_def]
  -- Integrand on F equals the log diff (vol_next form).
  have hrw_F :
      ∫ ω in F,
        (TemporalGraph.chiPotential G.toTemporalGraph (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
              (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω) -
          TemporalGraph.chiPotential G.toTemporalGraph t_j s_j) ∂vm.μ
      = ∫ ω in F,
          (Real.log (1 + (vol_next ω : ℝ)) - Real.log (1 + (v₀ : ℝ))) ∂vm.μ := by
    refine setIntegral_congr_fun hF_meas_top ?_
    intro ω hω
    have heq := hT_eq_τ'Nat_on_F ω hω
    show TemporalGraph.chiPotential G.toTemporalGraph (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
            (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω) -
          TemporalGraph.chiPotential G.toTemporalGraph t_j s_j = _
    rw [heq, hchi_s_j]
    rfl
  rw [hrw_F]
  -- (ii) setIntegral_condExp: ∫_F log_diff = ∫_F E[log_diff | ℱ_{t_j}].
  have hsic := setIntegral_condExp (vm.ℱ.le t_j) hchi_int hF_meas
  rw [← hsic]
  -- (iii) setIntegral_mono_ae_restrict using hfinal_cond.
  have hbound :
      ∫ ω in F, ((vm.μ : Measure _)[fun ω' => Real.log (1 + (vol_next ω' : ℝ)) -
            Real.log (1 + (v₀ : ℝ)) | vm.ℱ t_j]) ω ∂vm.μ
        ≤ ∫ _ in F, (-1 / 2048 : ℝ) ∂vm.μ := by
    apply setIntegral_mono_ae_restrict integrable_condExp.integrableOn
      (integrable_const _).integrableOn
    exact hfinal_cond
  refine le_trans hbound ?_
  -- (iv) setIntegral_const = -1/2048 · μ(F).toReal.
  rw [setIntegral_const, smul_eq_mul, mul_comm]
  rfl

end VoterModel
