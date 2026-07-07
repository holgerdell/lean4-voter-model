module

import VoterProcess.Martingale
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Algebra.Order.Star.Real
import VoterProcess.Expectation
public import UpperBound.PotentialDecrease.StableInterval
import UpperBound.PotentialDecrease.Helpers

@[expose] public section
open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators

noncomputable section

namespace VoterModel

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]

/-! ## Main results

Embedded-chain ψ-drift: `psi_down_drift_on_fiber` and
`case2_hypotheses_from_volume_bound_on_fiber`. -/
/-! ## Embedded-chain ψ-drift (paper `lem:psi-down-drift`)

The paper's `lem:psi-down-drift` packages two conclusions about the embedded
chain `(T_j)_{j ≥ 0}`:

1. **Unconditional** (always): `E[ψ(S_{T_{j+1}}) − ψ(s_{t_j}) | H_{T_j} = H_{t_j}] ≤ 0`.
2. **Stable + nonempty**:
   `E[ψ(S_{T_{j+1}}) − ψ(s_{t_j}) | H_{T_j} = H_{t_j}] ≤ −d_min·φ_j / (500·ψ(s_{t_j}))`.

We split these into two theorems (`psi_down_drift` and `psi_down_drift_stable`)
because the hypothesis bundles differ substantially. Both take the same
"`H_{t_j}` is a possible value of `H_{T_j}`" encoding as elsewhere in this file:
pointwise hypotheses `hT_val : ∀ ω, embeddedChainTime G.toTemporalGraph vm Δ j ω = t_j` and
`hS_init : ∀ ω, vm.S t_j ω = s₀`.

We do not import `IntervalChain.lean` for `IsStableInterval`; stability is
encoded by the same volume-difference bound that `prob_good_event` consumes
(see `potential_decrease_stable_interval_combined_unconditional`).

The stable bound uses constant `192·√6 ≈ 470.4` rather than the paper's `500`;
this matches the existing `potential_decrease_stable_interval_*` family which
computes both Case 1/2 constants exactly. `192·√6 < 500`, so the Lean bound is
stronger than the paper's stated bound. -/


/-- \label{lem:psi-down-drift}
\label{lem:psi-down-drift-on-fiber}

**Unconditional embedded-chain ψ-drift on a fiber** (Lean-only helper for L68;
set-integral form of `psi_down_drift` over a measurable fiber `F ∈ ℱ_{t_j}`).

Let `F ⊆ Ω` be a set measurable in `vm.ℱ t_j`, with `T_j ω = t_j` and
`vm.S t_j ω = s_j` for all `ω ∈ F`. Then
`∫_F (ψ(S_{T_{j+1}}) − ψ(s_j)) dvm.μ ≤ 0`.

This is the set-integral form of `psi_down_drift`, but with the deterministic
fiber conditions `T_j = t_j` and `S_{t_j} = s_j` localized to `F` rather than
imposed globally. The proof uses a modified stopping time
`τ' ω := max t_j (T_{j+1} ω)` (which globally satisfies `t_j ≤ τ' ω ≤ t'` for
`t' = ∑ k < j+2, Δ k`) to run the supermartingale optional-stopping argument
unconditionally, then restricts to `F` (where `τ' ω = T_{j+1} ω` by strict
monotonicity of the embedded chain). -/
theorem psi_down_drift_on_fiber
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
    -- Conclusion: ∫_F (ψ(S_{T_{j+1}}) − potential G.toTemporalGraph t_j s_j) dvm.μ ≤ 0
    ∫ ω in F,
      (vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω
        - G.potential t_j s_j)
      ∂vm.μ ≤ 0 := by
  classical
  -- Cap value t' bounds T_{j+1} globally (proved inline since
  -- `embeddedChainTime_le_sum_early` is private to TheoremUpperBound).
  set t' : ℕ := ∑ k ∈ Finset.range (j + 2), Δ k with ht'_def
  have hT_next_le_global : ∀ ω, embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω ≤ t' := by
    intro ω
    -- Generalize: ∀ i ω, T_i ω ≤ ∑ k < i+1, Δ k. We then specialize at i = j+1.
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
      -- The outer claim has range (i'+1+1) = (i'+2); the inner def now gives ≤ range (i'+1).
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
    -- τ' ω = max (t_j : ℕ∞) (T_{j+1} ω : ℕ∞). The constant t_j is a stopping time.
    have hconst : IsStoppingTime vm.ℱ (fun (_ : Ω) => (t_j : ℕ∞)) := by
      have h := isStoppingTime_const vm.ℱ t_j
      -- h : IsStoppingTime vm.ℱ (fun _ => t_j) where t_j : ℕ, but the target uses (t_j : ℕ∞)
      exact h
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
  have hτ'_eq_on_F : ∀ ω ∈ F,
      τ' ω = (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω : ℕ∞) := by
    intro ω hω
    have h := hT_strict_on_F ω hω
    refine max_eq_right ?_
    exact_mod_cast le_of_lt h
  -- Submartingale of -ψ.
  haveI : IsFiniteMeasure (vm.μ : Measure Ω) := inferInstance
  have hSub : Submartingale (fun t ω => -vm.psiS t ω) vm.ℱ vm.μ :=
    Supermartingale.neg (TemporalGraph.psiS_supermartingale vm)
  have hStop : Submartingale (stoppedProcess (fun t ω => -vm.psiS t ω) τ') vm.ℱ vm.μ :=
    Submartingale.stoppedProcess hSub hτ'_stop
  have hcond := Submartingale.ae_le_condExp hStop (i := t_j) (j := t') ht_j_le_t'
  -- Global rewrites of stoppedProcess at t_j and t'.
  have hLHS_eq : stoppedProcess (fun t ω => -vm.psiS t ω) τ' t_j =
      fun ω => -vm.psiS t_j ω :=
    funext fun ω => stoppedProcess_eq_of_le (hτ'_ge_lo ω)
  -- Helper: on F, τ' ω = T_{j+1} ω, hence ψ at τ' ω equals ψ at T_{j+1} ω.
  -- At t', stoppedProcess (-ψ) τ' t' = -ψ(τ' ω) ω globally (since τ' ≤ t' globally).
  -- Coerce: τ' ω : ℕ∞, and we need to extract the underlying ℕ.
  -- Define `τ'Nat ω : ℕ := max t_j (T_{j+1} ω)`.
  let τ'Nat : Ω → ℕ := fun ω => max t_j (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω)
  have hτ'_eq_cast : ∀ ω, τ' ω = (τ'Nat ω : ℕ∞) := fun ω => by
    show max (t_j : ℕ∞) (_ : ℕ∞) = ((max _ _ : ℕ) : ℕ∞)
    rfl
  have hRHS_eq : stoppedProcess (fun t ω => -vm.psiS t ω) τ' t' =
      fun ω => -vm.psiS (τ'Nat ω) ω :=
    funext fun ω => by
      rw [stoppedProcess_eq_of_ge (hτ'_le_hi ω)]
      simp only [τ', WithTop.untopA, hτ'_eq_cast]
      norm_cast
  rw [hLHS_eq, hRHS_eq] at hcond
  -- Integrability of ψ ∘ τ'Nat (we'll need this for the cond exp manipulations).
  have hInt_neg : Integrable (fun ω => -vm.psiS (τ'Nat ω) ω) vm.μ :=
    hRHS_eq ▸ hStop.2.2 t'
  have hInt : Integrable (fun ω => vm.psiS (τ'Nat ω) ω) vm.μ :=
    hInt_neg.neg.congr (Filter.Eventually.of_forall (fun ω => neg_neg _))
  -- Cond exp of negation: μ[-f|m] =ᵐ -μ[f|m].
  have hce_neg :
      (vm.μ : Measure _)[fun ω => -vm.psiS (τ'Nat ω) ω | vm.ℱ t_j]
      =ᵐ[(vm.μ : Measure _)] -(vm.μ : Measure _)[fun ω => vm.psiS (τ'Nat ω) ω | vm.ℱ t_j] :=
    condExp_neg _ _
  -- The conditional bound, after sign flip: μ[ψ(τ'Nat) | ℱ_{t_j}] ω ≤ ψ(t_j) ω a.e.
  have hpsi_cond_le : ∀ᵐ ω ∂(vm.μ : Measure _),
      ((vm.μ : Measure _)[fun ω' => vm.psiS (τ'Nat ω') ω' | vm.ℱ t_j]) ω
        ≤ vm.psiS t_j ω := by
    filter_upwards [hcond, hce_neg] with ω hcond_ω hceneg_ω
    have h := hcond_ω.trans_eq hceneg_ω
    simp only [Pi.neg_apply] at h
    linarith
  -- Now integrate over F. The strategy:
  --   ∫_F (ψ(T_{j+1}) - c) dμ
  --     = ∫_F (ψ(τ'Nat) - c) dμ                              (since τ'Nat = T_{j+1} on F)
  --     = ∫_F μ[ψ(τ'Nat) | ℱ_{t_j}] dμ - ∫_F c dμ            (setIntegral_condExp on F)
  --     ≤ ∫_F vm.psiS t_j dμ - ∫_F c dμ                     (hpsi_cond_le on F)
  --     = ∫_F (vm.psiS t_j - c) dμ
  --     = 0                                                  (vm.psiS t_j = c on F by hF_S)
  -- where c = potential G.toTemporalGraph t_j s_j.
  set c : ℝ := G.potential t_j s_j with hc_def
  -- Identify the integrand on F via τ'Nat = T_{j+1} on F.
  have hT_eq_τ'Nat_on_F : ∀ ω ∈ F, embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω = τ'Nat ω := by
    intro ω hω
    have hlt := hT_strict_on_F ω hω
    show _ = max t_j _
    omega
  -- Rewrite the integrand using this identification.
  have hF_meas_top : MeasurableSet F := vm.ℱ.le t_j _ hF_meas
  have hrw1 : ∫ ω in F,
      (vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω - c) ∂vm.μ
      = ∫ ω in F, (vm.psiS (τ'Nat ω) ω - c) ∂vm.μ := by
    refine setIntegral_congr_fun hF_meas_top ?_
    intro ω hω
    have heq := hT_eq_τ'Nat_on_F ω hω
    show vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ (j + 1) ω) ω - c
      = vm.psiS (τ'Nat ω) ω - c
    rw [heq]
  -- Rewrite c = vm.psiS t_j ω on F.
  have hpsi_eq_on_F : ∀ ω ∈ F, vm.psiS t_j ω = c := by
    intro ω hω
    show G.potential t_j (vm.S t_j ω) = _
    rw [hF_S ω hω]
  -- Decompose ∫_F (ψ(τ'Nat) - c) = ∫_F μ[ψ(τ'Nat) | ℱ_{t_j}] - ∫_F c (using setIntegral_condExp on F).
  -- Step: ∫_F (ψ(τ'Nat) - c) ≤ 0.
  rw [hrw1]
  -- Rewrite ψ(τ'Nat) on F using setIntegral_condExp.
  have hF_integrable : Integrable (fun ω => vm.psiS (τ'Nat ω) ω) vm.μ := hInt
  have hF_const_integrable : Integrable (fun _ : Ω => c) vm.μ := integrable_const c
  -- Split the integral.
  have hsplit : ∫ ω in F, (vm.psiS (τ'Nat ω) ω - c) ∂vm.μ
      = ∫ ω in F, vm.psiS (τ'Nat ω) ω ∂vm.μ - ∫ ω in F, c ∂vm.μ := by
    rw [integral_sub hF_integrable.integrableOn hF_const_integrable.integrableOn]
  rw [hsplit]
  -- Use setIntegral_condExp: ∫_F μ[ψ(τ'Nat) | ℱ_{t_j}] = ∫_F ψ(τ'Nat).
  have hsic := setIntegral_condExp (vm.ℱ.le t_j) hF_integrable hF_meas
  -- Now compare with ∫_F vm.psiS t_j.
  have hpsi_t_j_int : Integrable (vm.psiS t_j) vm.μ :=
    (TemporalGraph.psiS_supermartingale vm).integrable t_j
  have hbound : ∫ ω in F, vm.psiS (τ'Nat ω) ω ∂vm.μ
      ≤ ∫ ω in F, vm.psiS t_j ω ∂vm.μ := by
    rw [← hsic]
    -- ∫_F μ[ψ(τ'Nat) | ℱ_{t_j}] ≤ ∫_F ψ(t_j) since the integrand is ≤ a.e.
    apply setIntegral_mono_ae
    · exact (integrable_condExp).integrableOn
    · exact hpsi_t_j_int.integrableOn
    · filter_upwards [hpsi_cond_le] with ω hω; exact hω
  -- Now show ∫_F ψ(t_j) = ∫_F c (since ψ(t_j) = c on F).
  have heq_c : ∫ ω in F, vm.psiS t_j ω ∂vm.μ = ∫ ω in F, c ∂vm.μ := by
    refine setIntegral_congr_fun hF_meas_top ?_
    intro ω hω; exact hpsi_eq_on_F ω hω
  linarith

/-- \label{stmt:case2-hypotheses-on-fiber}

**Fiber-relative `case2_hypotheses_from_volume_bound`** (Lean-only L84, enabling
the Case 2 dispatch in L68). Given a fiber `F ∈ ℱ_{t_j}` with `T_j = t_j` and
`S_{t_j} = s_j` on `F`, plus the **F-restricted** `hstable` and `hexit`
hypotheses (a.e. on `(vm.μ : Measure _).restrict F`; supplied by the caller via L85/L94),
produce `Case2Hypotheses G vm s_j t_j (embeddedChainTime G vm Δ (j+1)) t' φ_j F`.

The non-fiber-dependent fields (`devInt`, `sumAbsInt`, `deltaInt`, `cutInt`,
`bound`, `t'_ge`) are derived exactly as in `case2_hypotheses_from_volume_bound`,
using only the structural properties of `embeddedChainTime` /
`volumeExcursionTime` (and not relying on the `hT_val` / `hS_init` global
identifications).

Threshold (1/8) in the struct field.
Hypotheses are now F-restricted, enabling L68's F_T dispatch. -/
theorem case2_hypotheses_from_volume_bound_on_fiber
    {Ω : Type*} [MeasurableSpace Ω]
    (G : TemporalGraph V) (vm : G.VoterModelAbstract 2 Ω)
    -- Fiber identification: T_j = t_j and S_{t_j} = s_j on F
    (s_j : Finset V) (t_j : ℕ) (Δ : ℕ → ℕ) (j : ℕ)
    (F : Set Ω) (_hF_meas : MeasurableSet[vm.ℱ t_j] F)
    (_hF_T : ∀ ω ∈ F, embeddedChainTime G vm Δ j ω = t_j)
    (_hF_S : ∀ ω ∈ F, vm.S t_j ω = s_j)
    -- Conductance tag
    (φ_j : ℝ)
    -- Good-step time
    (t' : ℕ) (ht'_ge : t_j ≤ t')
    -- Stability and exit hypotheses (F-restricted a.e.; supplied by caller).
    (hstable : ∀ᵐ ω ∂((vm.μ : Measure _).restrict F),
        ((vm.μ : Measure _)[fun ω' =>
          |(G.volume (embeddedChainTime G vm Δ (j + 1) ω')
              (vm.S (embeddedChainTime G vm Δ (j + 1) ω') ω') : ℝ)
          - (G.volume t_j s_j : ℝ)|
          | vm.ℱ t_j]) ω
          < (1 / 8 : ℝ) * (G.volume t_j s_j : ℝ))
    (hexit : ∀ᵐ ω ∂((vm.μ : Measure _).restrict F), embeddedChainTime G vm Δ (j + 1) ω ≤ t' →
        (1 / 2 : ℝ) * (G.volume t_j s_j : ℝ)
          ≤ |(G.volume (embeddedChainTime G vm Δ (j + 1) ω)
              (vm.S (embeddedChainTime G vm Δ (j + 1) ω) ω) : ℝ)
              - (G.volume t_j s_j : ℝ)|) :
    Case2Hypotheses G vm s_j t_j (embeddedChainTime G vm Δ (j + 1)) t' φ_j F := by
  set cap := (∑ k ∈ Finset.range (j + 1), Δ k) - 1 with hcap_def
  -- Measurability of vm.S and stopping time for T_{j+1}
  have hS_meas : ∀ t, @Measurable Ω (Finset V) (vm.ℱ t) ⊤ (vm.S t) := fun t =>
    (measurable_of_countable (fun A => VoterModel.minoritySet G t A)).comp
      (vm.A_stronglyAdapted t).measurable
  have hT_stop : IsStoppingTime vm.ℱ (fun ω => (embeddedChainTime G vm Δ (j + 1) ω : ℕ∞)) :=
    embeddedChainTime_isStoppingTime G vm Δ hS_meas (j + 1)
  -- Bound: T_{j+1}(ω) ≤ N for some deterministic N; here we use a structural cap
  -- that does NOT depend on hT_val. We use the recursion: T_{j+1}(ω) = vET (T_j ω) cap' ω
  -- where cap' = (∑ k ∈ range(j+2), Δ k) - 1. By volumeExcursionTime_le_succ,
  -- T_{j+1}(ω) ≤ cap' + 1. But this only works if we know T_j ω's relation to cap'.
  -- Actually, by definition: T_{j+1}(ω) = vET (T_j ω) cap' ω, and vET t_0 tMax ω ≤ tMax + 1
  -- ALWAYS (regardless of t_0). So we can use cap' + 1 as a global bound.
  have hT_next_bound : ∀ ω, embeddedChainTime G vm Δ (j + 1) ω ≤ cap + 1 := fun ω => by
    show volumeExcursionTime G vm (embeddedChainTime G vm Δ j ω) cap ω ≤ cap + 1
    exact volumeExcursionTime_le_succ G vm _ _ ω
  -- Measurability of {T_{j+1} = k}
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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- stable: passed by caller
    exact hstable
  · -- exit: passed by caller
    exact hexit
  · -- devInt: integrability of |Vol(S_{T_{j+1}}) − Vol(s_j)|
    have hvolInt : ∀ k, Integrable (fun ω => (G.volume k (vm.S k ω) : ℝ)) vm.μ :=
      fun k => (voter_integrable_comp_A vm
        (fun s' => (G.volume k (minoritySet G k s') : ℝ)) k).congr
        (Filter.Eventually.of_forall fun ω' => by
          simp [TemporalGraph.VoterModelAbstract.S])
    have hvolTnext_int : Integrable
        (fun ω => (G.volume (embeddedChainTime G vm Δ (j + 1) ω)
          (vm.S (embeddedChainTime G vm Δ (j + 1) ω) ω) : ℝ)) vm.μ := by
      have heq : (fun ω => (G.volume (embeddedChainTime G vm Δ (j + 1) ω)
            (vm.S (embeddedChainTime G vm Δ (j + 1) ω) ω) : ℝ)) = fun ω =>
          ∑ k ∈ Finset.range (cap + 2),
            Set.indicator {ω | embeddedChainTime G vm Δ (j + 1) ω = k}
              (fun ω => (G.volume k (vm.S k ω) : ℝ)) ω := by
        funext ω
        rw [Finset.sum_eq_single (embeddedChainTime G vm Δ (j + 1) ω)]
        · simp [Set.indicator]
        · intro k _ hk; simp [Set.indicator, Ne.symm hk]
        · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le (hT_next_bound ω))) h
      rw [heq]
      exact integrable_finsetSum _ fun k _ => (hvolInt k).indicator (hTnext_eq_meas k)
    exact hvolTnext_int.sub (integrable_const _) |>.abs
  · -- sumAbsInt: integrability of stopped |Δ_j| sum
    have hcutDiff_int : ∀ k, Integrable (fun ω' =>
        |(G.edgesBetween t' (vm.S (k + 1) ω') (Finset.univ \ vm.S (k + 1) ω') : ℝ)
          - (G.edgesBetween t' (vm.S k ω') (Finset.univ \ vm.S k ω') : ℝ)|) vm.μ := by
      intro k
      have h1 : Integrable (fun ω' =>
          (G.edgesBetween t' (vm.S (k + 1) ω') (Finset.univ \ vm.S (k + 1) ω') : ℝ))
          vm.μ :=
        (voter_integrable_comp_A vm
          (fun s' => (G.edgesBetween t' (minoritySet G (k+1) s')
            (Finset.univ \ minoritySet G (k+1) s') : ℝ)) (k+1)).congr
          (Filter.Eventually.of_forall fun ω' => by simp [TemporalGraph.VoterModelAbstract.S])
      have h2 : Integrable (fun ω' =>
          (G.edgesBetween t' (vm.S k ω') (Finset.univ \ vm.S k ω') : ℝ))
          vm.μ :=
        (voter_integrable_comp_A vm
          (fun s' => (G.edgesBetween t' (minoritySet G k s')
            (Finset.univ \ minoritySet G k s') : ℝ)) k).congr
          (Filter.Eventually.of_forall fun ω' => by simp [TemporalGraph.VoterModelAbstract.S])
      exact (h1.sub h2).abs
    have hind_meas : ∀ k, MeasurableSet {ω' | k < embeddedChainTime G vm Δ (j + 1) ω'} := by
      intro k
      have : {ω' | k < embeddedChainTime G vm Δ (j + 1) ω'} =
          {ω' | (embeddedChainTime G vm Δ (j + 1) ω' : ℕ∞) ≤ ↑k}ᶜ := by
        ext ω'; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le, ENat.coe_lt_coe]
      rw [this]; exact (vm.ℱ.le k _ (hT_stop k)).compl
    -- Index-set rewrite. Without `hT_gt` (which required hT_val + strictMono), we
    -- handle both cases of `T_{j+1} ω' > t_j` and `T_{j+1} ω' ≤ t_j` (both empty).
    -- In the latter case, the sum-of-indicators side requires `0 < T_{j+1} ω'` to
    -- ensure `T_{j+1} ω' - 1 < t_j` (so LHS is empty); this positivity is global.
    have hT_pos : ∀ ω, 0 < embeddedChainTime G vm Δ (j + 1) ω := by
      intro ω
      show 0 < volumeExcursionTime G vm (embeddedChainTime G vm Δ j ω) cap ω
      set t₀ := embeddedChainTime G vm Δ j ω
      by_cases h : t₀ ≤ cap
      · exact Nat.lt_of_le_of_lt (Nat.zero_le _) (lt_volumeExcursionTime G vm t₀ cap ω h)
      · push Not at h
        unfold volumeExcursionTime
        dsimp only
        have hIcc_empty : Finset.Icc t₀ cap = ∅ := Finset.Icc_eq_empty (by omega)
        have hcand_empty : ((Finset.Icc t₀ cap).filter fun t =>
            2 * G.volume t (vm.S t ω) <
              G.volume t₀ (vm.S t₀ ω) ∨
            3 * G.volume t₀ (vm.S t₀ ω) <
              2 * G.volume t (vm.S t ω)) = ∅ := by
          rw [hIcc_empty]; rfl
        rw [hcand_empty]
        simp only [Finset.not_nonempty_empty, ↓reduceDIte]
        omega
    have heq_sum : (fun ω' =>
        ∑ k ∈ Finset.Icc t_j (embeddedChainTime G vm Δ (j + 1) ω' - 1),
          |(G.edgesBetween t' (vm.S (k + 1) ω') (Finset.univ \ vm.S (k + 1) ω') : ℝ)
            - (G.edgesBetween t' (vm.S k ω') (Finset.univ \ vm.S k ω') : ℝ)|) =
        fun ω' =>
        ∑ k ∈ Finset.Icc t_j cap,
          Set.indicator {ω' | k < embeddedChainTime G vm Δ (j + 1) ω'}
            (fun ω' =>
              |(G.edgesBetween t' (vm.S (k + 1) ω') (Finset.univ \ vm.S (k + 1) ω') : ℝ)
                - (G.edgesBetween t' (vm.S k ω') (Finset.univ \ vm.S k ω') : ℝ)|)
            ω' := by
      funext ω'
      have hT_bound : embeddedChainTime G vm Δ (j + 1) ω' ≤ cap + 1 := hT_next_bound ω'
      have hT_pos1 : 0 < embeddedChainTime G vm Δ (j + 1) ω' := hT_pos ω'
      simp only [Set.indicator, Set.mem_setOf_eq]
      have hfinset_eq : Finset.Icc t_j (embeddedChainTime G vm Δ (j + 1) ω' - 1) =
          (Finset.Icc t_j cap).filter (fun k => k < embeddedChainTime G vm Δ (j + 1) ω') := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_filter]
        omega
      rw [hfinset_eq, Finset.sum_filter]
    rw [heq_sum]
    exact integrable_finsetSum _ fun k _ =>
      (hcutDiff_int k).indicator (hind_meas k)
  · -- deltaInt: per-step integrability of |Δ_j|
    intro k
    have h1 : Integrable (fun ω' =>
        (G.edgesBetween t' (vm.S (k + 1) ω') (Finset.univ \ vm.S (k + 1) ω') : ℝ))
        vm.μ :=
      (voter_integrable_comp_A vm
        (fun s' => (G.edgesBetween t' (minoritySet G (k+1) s')
          (Finset.univ \ minoritySet G (k+1) s') : ℝ)) (k+1)).congr
        (Filter.Eventually.of_forall fun ω' => by simp [TemporalGraph.VoterModelAbstract.S])
    have h2 : Integrable (fun ω' =>
        (G.edgesBetween t' (vm.S k ω') (Finset.univ \ vm.S k ω') : ℝ))
        vm.μ :=
      (voter_integrable_comp_A vm
        (fun s' => (G.edgesBetween t' (minoritySet G k s')
          (Finset.univ \ minoritySet G k s') : ℝ)) k).congr
        (Filter.Eventually.of_forall fun ω' => by simp [TemporalGraph.VoterModelAbstract.S])
    exact (h1.sub h2).abs
  · -- cutInt: per-step integrability of cutS
    intro k
    have heq : (fun ω' => (vm.cutS k ω' : ℝ)) =
        (fun s' => (G.edgesBetween k (minoritySet G k s')
          (Finset.univ \ minoritySet G k s') : ℝ)) ∘ (vm.opinionZeroSet k) := by
      funext ω'; simp [TemporalGraph.VoterModelAbstract.cutS, TemporalGraph.VoterModelAbstract.S]
    rw [heq]
    exact voter_integrable_comp_A vm
      (fun s' => (G.edgesBetween k (minoritySet G k s')
        (Finset.univ \ minoritySet G k s') : ℝ)) k
  · -- bound: T_{j+1}(ω) ≤ cap + 1
    exact ⟨cap + 1, hT_next_bound⟩
  · -- t'_ge: t_j ≤ t'
    exact ht'_ge


end VoterModel
