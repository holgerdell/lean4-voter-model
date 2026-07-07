module

public import UpperBound.MultiOpinion.Metaphase
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Positivity.Finset

/-! ## Main results

Abstract set-integral / geometric-tail kernels for §3.4 (Tier D), independent of
the voter-model definitions:
`condExp_le_const_of_forall_setIntegral_le`, `condExp_geom_tail_le_three` (D1),
`condExp_le_of_le_mul_of_condExp_le_three` (D2), and the `xiAlpha` /
phase-budget arithmetic lemmas. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Classical ENNReal

noncomputable section

namespace TemporalGraph

/-! ### Set-integral characterisation of an a.e. condExp upper bound -/

/-- If `f` is integrable and `∫_s f ≤ ∫_s C` for every `m`-measurable set `s`,
then `μ[f | m] ≤ C` almost everywhere. Proved on the trimmed measure
`μ.trim hm`, where `m`-measurable sets are *all* the measurable sets, via
`ae_le_of_forall_setIntegral_le` together with `setIntegral_condExp`. -/
theorem condExp_le_const_of_forall_setIntegral_le
    {Ω : Type*} {m m₀ : MeasurableSpace Ω} (hm : m ≤ m₀) {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : Integrable f μ) {C : ℝ}
    (h : ∀ s, MeasurableSet[m] s → ∫ ω in s, f ω ∂μ ≤ ∫ _ω in s, C ∂μ) :
    μ[f | m] ≤ᵐ[μ] (fun _ => C) := by
  haveI hsf : SigmaFinite (μ.trim hm) := by
    haveI : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim hm
    infer_instance
  rw [← (stronglyMeasurable_condExp (m := m) (μ := μ) (f := f)).ae_le_trim_iff hm
        stronglyMeasurable_const]
  refine ae_le_of_forall_setIntegral_le
    (integrable_condExp.trim hm stronglyMeasurable_condExp)
    ((integrable_const C).trim hm stronglyMeasurable_const) ?_
  intro s hs _hslt
  rw [← setIntegral_trim hm stronglyMeasurable_condExp hs,
      ← setIntegral_trim hm stronglyMeasurable_const hs,
      setIntegral_condExp hm hf hs]
  exact h s hs

/-! ### D1: conditional geometric-tail bound -/

/-- **D1 (abstract).** Let `N : Ω → ℕ` be integrable with, for every `k`, the
conditional tail bound `μ[𝟙{N ≥ k+1} | m] ≤ (2/3)^k` a.e. Then the conditional
mean satisfies `μ[N | m] ≤ 3` a.e. — the mean of a `Geom(1/3)` variable.

The proof bounds `∫_s N dμ` for each `m`-measurable `s` by the geometric series:
`∫_s N = ∑_k ∫_s 𝟙{N ≥ k+1} = ∑_k ∫_s μ[𝟙{N ≥ k+1}|m] ≤ ∑_k (2/3)^k μ(s) = 3 μ(s)`,
then applies `condExp_le_const_of_forall_setIntegral_le`. -/
theorem condExp_geom_tail_le_three
    {Ω : Type*} {m m₀ : MeasurableSpace Ω} (hm : m ≤ m₀) {μ : Measure Ω}
    [IsProbabilityMeasure μ] {N : Ω → ℕ} (hNmeas : Measurable N)
    (hNint : Integrable (fun ω => (N ω : ℝ)) μ)
    (htail : ∀ k, μ[Set.indicator {ω | k + 1 ≤ N ω} (fun _ => (1 : ℝ)) | m]
      ≤ᵐ[μ] (fun _ => ((2 : ℝ) / 3) ^ k)) :
    μ[(fun ω => (N ω : ℝ)) | m] ≤ᵐ[μ] (fun _ => (3 : ℝ)) := by
  apply condExp_le_const_of_forall_setIntegral_le hm hNint
  intro s hsm
  have hsm₀ : MeasurableSet s := hm s hsm
  -- abbreviations
  set Jset : ℕ → Set Ω := fun k => {ω | k + 1 ≤ N ω} with hJset
  have hJset_meas : ∀ k, MeasurableSet (Jset k) := fun k => hNmeas measurableSet_Ici
  set J : ℕ → Ω → ℝ := fun k => Set.indicator (Jset k) (fun _ => (1 : ℝ)) with hJ
  have hJ_int : ∀ k, Integrable (J k) μ := fun k => (integrable_const 1).indicator (hJset_meas k)
  -- pointwise tail-sum identity (layer cake)
  have hpw : ∀ ω, (N ω : ℝ) = ∑' k, J k ω := by
    intro ω
    rw [show (N ω : ℝ) = (Finset.range (N ω)).sum (fun _ => (1 : ℝ)) by simp]
    rw [tsum_eq_sum (s := Finset.range (N ω)) (fun n hn => ?_)]
    · refine Finset.sum_congr rfl fun n hn => ?_
      rw [Finset.mem_range] at hn
      simp only [hJ, Set.indicator_apply, hJset, Set.mem_setOf_eq, if_pos (by omega : n + 1 ≤ N ω)]
    · rw [Finset.mem_range] at hn
      simp only [hJ, Set.indicator_apply, hJset, Set.mem_setOf_eq, if_neg (by omega : ¬ n + 1 ≤ N ω)]
  -- pointwise: s.indicator N = ∑' k, s.indicator (J k)
  have hpw_s : (fun ω => s.indicator (fun ω' => (N ω' : ℝ)) ω)
      = (fun ω => ∑' k, s.indicator (J k) ω) := by
    funext ω
    by_cases hω : ω ∈ s
    · simp only [Set.indicator_of_mem hω]
      rw [hpw ω]
    · simp [Set.indicator_of_notMem hω]
  -- each per-level set-integral bound
  have hterm_le : ∀ k, ∫ ω, s.indicator (J k) ω ∂μ ≤ ((2 : ℝ) / 3) ^ k * μ.real s := by
    intro k
    rw [integral_indicator hsm₀]
    calc ∫ ω in s, J k ω ∂μ
        = ∫ ω in s, μ[J k | m] ω ∂μ := (setIntegral_condExp hm (hJ_int k) hsm).symm
      _ ≤ ∫ _ω in s, ((2 : ℝ) / 3) ^ k ∂μ := by
            refine setIntegral_mono_on_ae integrable_condExp.integrableOn
              (integrable_const _).integrableOn hsm₀ ?_
            filter_upwards [htail k] with ω hω _ using hω
      _ = ((2 : ℝ) / 3) ^ k * μ.real s := by
            rw [setIntegral_const, smul_eq_mul, mul_comm]
  -- nonnegativity of LHS terms
  have hterm_nn : ∀ k, 0 ≤ ∫ ω, s.indicator (J k) ω ∂μ := by
    intro k
    refine integral_nonneg fun ω => ?_
    exact Set.indicator_nonneg
      (fun ω' _ => Set.indicator_nonneg (fun _ _ => zero_le_one) ω') ω
  -- summability of RHS
  have hRHS_sum : Summable (fun k => ((2 : ℝ) / 3) ^ k * μ.real s) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _
  have hLHS_sum : Summable (fun k => ∫ ω, s.indicator (J k) ω ∂μ) :=
    Summable.of_nonneg_of_le hterm_nn hterm_le hRHS_sum
  -- swap integral and tsum
  have hswap : ∫ ω in s, (N ω : ℝ) ∂μ = ∑' k, ∫ ω, s.indicator (J k) ω ∂μ := by
    rw [← integral_indicator hsm₀]
    rw [hpw_s]
    refine MeasureTheory.integral_tsum (fun k => ((hJ_int k).indicator hsm₀).1) ?_
    rw [show (fun k => ∫⁻ ω, ‖s.indicator (J k) ω‖ₑ ∂μ)
        = (fun k => ENNReal.ofReal (∫ ω, s.indicator (J k) ω ∂μ)) from funext fun k => by
      have hnn : 0 ≤ᵐ[μ] s.indicator (J k) :=
        .of_forall fun ω => Set.indicator_nonneg
          (fun ω' _ => Set.indicator_nonneg (fun _ _ => zero_le_one) ω') ω
      rw [lintegral_congr fun a => by
        rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg
          (Set.indicator_nonneg (fun ω' _ => Set.indicator_nonneg
            (fun _ _ => zero_le_one) ω') a)]]
      exact (ofReal_integral_eq_lintegral_ofReal ((hJ_int k).indicator hsm₀) hnn).symm]
    exact Summable.tsum_ofReal_ne_top hLHS_sum
  -- assemble
  rw [hswap]
  calc ∑' k, ∫ ω, s.indicator (J k) ω ∂μ
      ≤ ∑' k, ((2 : ℝ) / 3) ^ k * μ.real s := hLHS_sum.tsum_le_tsum hterm_le hRHS_sum
    _ = (∑' k, ((2 : ℝ) / 3) ^ k) * μ.real s := by rw [tsum_mul_right]
    _ = 3 * μ.real s := by
        rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
    _ = ∫ _ω in s, (3 : ℝ) ∂μ := by rw [setIntegral_const, smul_eq_mul, mul_comm]

/-! ### D2: conditional metaphase-increment bound (abstract) -/

/-- **D2 (abstract, `m`-measurable factor).** Variant of
`condExp_le_of_le_smul_of_condExp_le_three` where the multiplier `c` is an
`m`-measurable nonnegative function rather than a constant — the form needed for
the metaphase, where the block length `ξ_α` is `𝒢_{R_α}`-measurable (it is
determined by `|O_α|` at the random metaphase start). If `g ≤ c·N` a.e. with `c`
`m`-measurable, `0 ≤ c`, and `μ[N | m] ≤ 3`, then `μ[g | m] ≤ 3·c` a.e. -/
theorem condExp_le_of_le_mul_of_condExp_le_three
    {Ω : Type*} {m m₀ : MeasurableSpace Ω} (_hm : m ≤ m₀) {μ : Measure Ω}
    [IsProbabilityMeasure μ] {N g c : Ω → ℝ}
    (hc_meas : StronglyMeasurable[m] c) (hc_nn : 0 ≤ᵐ[μ] c)
    (hNint : Integrable N μ) (hgint : Integrable g μ) (hcN_int : Integrable (c * N) μ)
    (hgN : g ≤ᵐ[μ] c * N)
    (hN3 : μ[N | m] ≤ᵐ[μ] (fun _ => (3 : ℝ))) :
    μ[g | m] ≤ᵐ[μ] (fun ω => 3 * c ω) := by
  have h1 : μ[g | m] ≤ᵐ[μ] μ[c * N | m] := condExp_mono hgint hcN_int hgN
  have h2 : μ[c * N | m] =ᵐ[μ] c * μ[N | m] :=
    condExp_mul_of_stronglyMeasurable_left hc_meas hcN_int hNint
  filter_upwards [h1, h2, hN3, hc_nn] with ω ha hb hc3 hcnn
  rw [Pi.mul_apply] at hb
  rw [Pi.zero_apply] at hcnn
  calc μ[g | m] ω ≤ μ[c * N | m] ω := ha
    _ = c ω * μ[N | m] ω := hb
    _ ≤ c ω * 3 := mul_le_mul_of_nonneg_left hc3 hcnn
    _ = 3 * c ω := by ring

/-! ### Threshold reconciliation (piece A, arithmetic kernel)

The §3.4 "small opinion" condition `Vol(a_q) ≤ τm/(P|O_α|)` makes the two-opinion
absorption threshold of `condExp_Xq_le_half` fire within a single `ξ_α`-block.
The arithmetic heart of that reconciliation (paper eq `small-2`,
`J' ≤ ℓ_{r+ξ}−1`): the increasing function `x ↦ x/d_min + log(1+x)` evaluated at
the small-opinion volume bound is `≤ ξ_α − 1`, by the very definition of
`xiAlpha`. -/

/-- If `0 ≤ x ≤ τm/(P|O_α|)` (the small-opinion volume bound) then
`b·(x/d_min + log(1+x)) ≤ ξ_α − 1`, where `ξ_α = xiAlpha b m d_min |O_α|`.
Monotonicity of `x/d_min + log(1+x)` plus `Nat.le_ceil`. This is the arithmetic
kernel discharging the `hsmallbnd` threshold of `per_metaphase_two_thirds` (the
volume `Vol(minoritySet(phiQ q ξ_r))` plays the role of `x`, bounded by the
small-opinion threshold). -/
theorem xiAlpha_sub_one_ge
    (b m d_min : ℝ) (hb : 0 ≤ b) (hd : 0 < d_min) (Oα_card : ℕ) (hO : 0 < Oα_card)
    (x : ℝ) (hx_nn : 0 ≤ x) (hx_le : x ≤ 14 * m / (3 * (Oα_card : ℝ))) :
    b * (x / d_min + Real.log (1 + x)) ≤ (TemporalGraph.xiAlpha b m d_min Oα_card : ℝ) - 1 := by
  have hOR : (0 : ℝ) < Oα_card := by exact_mod_cast hO
  set T := b * (14 * m / (3 * (d_min * (Oα_card : ℝ)))
    + Real.log (1 + 14 * m / (3 * (Oα_card : ℝ)))) with hT
  have hmono : b * (x / d_min + Real.log (1 + x)) ≤ T := by
    rw [hT]
    apply mul_le_mul_of_nonneg_left _ hb
    have he : 14 * m / (3 * (d_min * (Oα_card : ℝ))) = (14 * m / (3 * (Oα_card : ℝ))) / d_min := by
      rw [div_div]; ring_nf
    rw [he]
    gcongr
  have hceil : T ≤ (⌈T⌉₊ : ℝ) := Nat.le_ceil T
  have hxi : (TemporalGraph.xiAlpha b m d_min Oα_card : ℝ) - 1 = (⌈T⌉₊ : ℝ) := by
    unfold TemporalGraph.xiAlpha
    rw [← hT]; push_cast; ring
  linarith [hmono, hceil, hxi]

/-- `xiAlpha` is antitone in the opinion count `c` (a larger opinion set means a
smaller volume bound `6m/c`, hence a shorter block). Needs `0 ≤ b`, `0 < d_min`,
`0 ≤ m`, `1 ≤ c`. -/
theorem xiAlpha_antitone (b m d_min : ℝ) (hb : 0 ≤ b) (hd : 0 < d_min) (hm : 0 ≤ m)
    (c c' : ℕ) (hc : 1 ≤ c) (hcc' : c ≤ c') :
    TemporalGraph.xiAlpha b m d_min c' ≤ TemporalGraph.xiAlpha b m d_min c := by
  have hcR : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  have hcc'R : (c : ℝ) ≤ (c' : ℝ) := by exact_mod_cast hcc'
  unfold TemporalGraph.xiAlpha
  refine Nat.add_le_add_left (Nat.ceil_mono ?_) 1
  refine mul_le_mul_of_nonneg_left ?_ hb
  gcongr

/-! ### Phase-budget accumulation over a block (paper eq `small-2`)

The §3.4 Claim needs that the `φ`-budget accumulated across the `ξ`-block of
phases `[r, r+ξ)` is at least `ξ − 1`. This is a purely deterministic fact about
`phaseIndex`, using only `0 ≤ φ ≤ 1` and reachability. -/

/-- The prefix budget at the phase index `ℓ_r = phaseIndex φ r` lies in `[r, r+1)`:
it reaches `r` (membership of the defining `sInf`) and overshoots by less than `1`
(since `φ ≤ 1`). -/
theorem phaseIndex_prefix_lt (φ : ℕ → ℝ) (hφ_le1 : ∀ j, φ j ≤ 1) (r : ℕ)
    (hr : ∃ ℓ, (r : ℝ) ≤ ∑ j ∈ Finset.range ℓ, φ j) :
    (∑ j ∈ Finset.range (phaseIndex φ r), φ j) < (r : ℝ) + 1 := by
  rw [phaseIndex_eq_of_reachable φ hr]
  set i := sInf {ℓ | (r : ℝ) ≤ ∑ j ∈ Finset.range ℓ, φ j} with hi
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · rw [h0, Finset.sum_range_zero]; positivity
  · obtain ⟨ℓ, hℓ⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    have hnot : ¬ ((r : ℝ) ≤ ∑ j ∈ Finset.range ℓ, φ j) := by
      intro hmem
      have hle : i ≤ ℓ := Nat.sInf_le hmem
      rw [hℓ] at hle; omega
    rw [hℓ, Finset.sum_range_succ]
    have := hφ_le1 ℓ
    rw [not_le] at hnot
    linarith

/-- **Phase-budget block bound (eq `small-2`).** Under `0 ≤ φ ≤ 1` and
reachability, the `φ`-budget over the block of phase indices
`[ℓ_r, ℓ_{r+ξ})` is at least `ξ − 1`. -/
theorem phase_budget_block_ge (φ : ℕ → ℝ) (hφ_le1 : ∀ j, φ j ≤ 1) (r ξ : ℕ)
    (hr : ∃ ℓ, (r : ℝ) ≤ ∑ j ∈ Finset.range ℓ, φ j)
    (hrξ : ∃ ℓ, ((r + ξ : ℕ) : ℝ) ≤ ∑ j ∈ Finset.range ℓ, φ j) :
    (ξ : ℝ) - 1 ≤ ∑ j ∈ Finset.Ico (phaseIndex φ r) (phaseIndex φ (r + ξ)), φ j := by
  have hmonoL : phaseIndex φ r ≤ phaseIndex φ (r + ξ) :=
    phaseIndex_mono φ (Nat.le_add_right r ξ)
  have hkey1 : ((r + ξ : ℕ) : ℝ) ≤ ∑ j ∈ Finset.range (phaseIndex φ (r + ξ)), φ j :=
    phaseIndex_reach_ge φ hrξ
  have hkey2 := phaseIndex_prefix_lt φ hφ_le1 r hr
  rw [Finset.sum_Ico_eq_sub _ hmonoL]
  push_cast at hkey1
  linarith

/-- The phase index strictly increases over a block of length `ξ ≥ 1`:
`ℓ_r < ℓ_{r+ξ}` (so the shifted block has at least one phase). Needs `0 ≤ φ ≤ 1`
and reachability. -/
theorem phaseIndex_lt_of_pos (φ : ℕ → ℝ) (hφ_nn : ∀ j, 0 ≤ φ j) (hφ_le1 : ∀ j, φ j ≤ 1)
    (r ξ : ℕ) (hξ : 1 ≤ ξ)
    (hr : ∃ ℓ, (r : ℝ) ≤ ∑ j ∈ Finset.range ℓ, φ j)
    (hrξ : ∃ ℓ, ((r + ξ : ℕ) : ℝ) ≤ ∑ j ∈ Finset.range ℓ, φ j) :
    phaseIndex φ r < phaseIndex φ (r + ξ) := by
  have hkey1 : ((r + ξ : ℕ) : ℝ) ≤ ∑ j ∈ Finset.range (phaseIndex φ (r + ξ)), φ j :=
    phaseIndex_reach_ge φ hrξ
  have hkey2 := phaseIndex_prefix_lt φ hφ_le1 r hr
  by_contra hcon
  rw [not_lt] at hcon
  have hsub : ∑ j ∈ Finset.range (phaseIndex φ (r + ξ)), φ j
      ≤ ∑ j ∈ Finset.range (phaseIndex φ r), φ j :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (fun x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hcon))
      (fun i _ _ => hφ_nn i)
  have hξR : (1 : ℝ) ≤ (ξ : ℝ) := by exact_mod_cast hξ
  push_cast at hkey1
  linarith

/-- **Shifted phase-time identity.** Summing the shifted gaps `Δ_{ℓ_a + i}` over
`i < j` and adding `t_a = phaseTime Δ φ a` recovers the global prefix
`∑_{i < ℓ_a + j} Δ_i`. This matches `condExp_Xq_le_half`'s base-offset interval. -/
theorem phaseTime_add_sum_shift (Δ : ℕ → ℕ) (φ : ℕ → ℝ) (a j : ℕ) :
    (∑ i ∈ Finset.range j, Δ (phaseIndex φ a + i)) + TemporalGraph.phaseTime Δ φ a
      = ∑ i ∈ Finset.range (phaseIndex φ a + j), Δ i := by
  rw [TemporalGraph.phaseTime, Finset.sum_range_add, add_comm]

end TemporalGraph
