module

import Probability.Preliminaries
import VoterProcess.Martingale
import Probability.OptionalStopping
import VoterProcess.Expectation
import Mathlib.Algebra.Order.Star.Real
public import TemporalGraph.Conductance

public import TemporalGraph.Degree
public import UpperBound.EmbeddedChain
import TemporalGraph.Basic
import UpperBound.TwoOpinion.DriftIntegration
import VoterProcess.Absorption.Time


@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

namespace VoterModel

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]

/-! ## Main results

Embedded-chain stopping-time bounds and combined-potential accumulation:
`embeddedChainTime_le_sum`, `embeddedChainTime_mono`, `combined_potential_dj_bound`,
`vol8fold_bound`. -/

/-- Bound `T_i ω ≤ ∑_{j < i+1} Δ_j`. The proof is by induction on `i`; the
inductive step uses `volumeExcursionTime_le_succ`. -/
private lemma embeddedChainTime_le_sum
    {Ω : Type*} [MeasurableSpace Ω]
    (G : TemporalGraph V) (vm : TemporalGraph.VoterModelAbstract G 2 Ω)
    (Δ : ℕ → ℕ) (hΔ_pos : ∀ j, 1 ≤ Δ j) (i : ℕ) (ω : Ω) :
    embeddedChainTime G vm Δ i ω ≤ ∑ j ∈ Finset.range (i + 1), Δ j := by
  induction i with
  | zero => simp [embeddedChainTime]
  | succ i' _ =>
    simp only [embeddedChainTime]
    have h := volumeExcursionTime_le_succ G vm (embeddedChainTime G vm Δ i' ω)
      ((∑ j ∈ Finset.range (i' + 1), Δ j) - 1) ω
    have h_pos : 1 ≤ ∑ j ∈ Finset.range (i' + 1), Δ j := by
      have h0 : Δ 0 ≤ ∑ j ∈ Finset.range (i' + 1), Δ j :=
        Finset.single_le_sum (f := Δ) (fun _ _ => Nat.zero_le _)
          (Finset.mem_range.mpr (by omega))
      exact le_trans (hΔ_pos 0) h0
    have hsub : (∑ j ∈ Finset.range (i' + 1), Δ j) - 1 + 1 =
        ∑ j ∈ Finset.range (i' + 1), Δ j := Nat.sub_add_cancel h_pos
    have h' : volumeExcursionTime G vm (embeddedChainTime G vm Δ i' ω)
        ((∑ j ∈ Finset.range (i' + 1), Δ j) - 1) ω ≤
        ∑ j ∈ Finset.range (i' + 1), Δ j := by
      rw [← hsub]; exact h
    have hmono : ∑ j ∈ Finset.range (i' + 1), Δ j ≤
        ∑ j ∈ Finset.range (i' + 1 + 1), Δ j :=
      Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (by omega))
    exact h'.trans hmono

/-- Monotonicity of `embeddedChainTime` in the index `i`. The proof reduces to
the one-step case `T_i ≤ T_{i+1}`, which uses `embeddedChainTime_strictMono`
once we know `T_i ω ≤ I_i^+` (i.e. `T_i ω ≤ cap_i = (∑ range(i+1) Δ) - 1`).
We derive the required tight bound `T_k ≤ ∑ range k Δ` inline. -/
private lemma embeddedChainTime_mono
    {Ω : Type*} [MeasurableSpace Ω]
    (G : TemporalGraph V) (vm : TemporalGraph.VoterModelAbstract G 2 Ω)
    (Δ : ℕ → ℕ) (hΔ_pos : ∀ j, 1 ≤ Δ j)
    {i j : ℕ} (hij : i ≤ j) (ω : Ω) :
    embeddedChainTime G vm Δ i ω ≤ embeddedChainTime G vm Δ j ω := by
  -- First, derive a tight bound T_k ≤ ∑ range k Δ inline (NOT exported).
  have h_tight : ∀ k, embeddedChainTime G vm Δ k ω ≤ ∑ m ∈ Finset.range k, Δ m := by
    intro k
    induction k with
    | zero => simp [embeddedChainTime]
    | succ k' _ =>
      simp only [embeddedChainTime]
      have h := volumeExcursionTime_le_succ G vm (embeddedChainTime G vm Δ k' ω)
        ((∑ m ∈ Finset.range (k' + 1), Δ m) - 1) ω
      have h_pos : 1 ≤ ∑ m ∈ Finset.range (k' + 1), Δ m := by
        have h0 : Δ 0 ≤ ∑ m ∈ Finset.range (k' + 1), Δ m :=
          Finset.single_le_sum (f := Δ) (fun _ _ => Nat.zero_le _)
            (Finset.mem_range.mpr (by omega))
        exact le_trans (hΔ_pos 0) h0
      omega
  induction hij with
  | refl => exact le_rfl
  | step _ ih =>
    rename_i j' _
    refine le_trans ih ?_
    -- Need T_{j'} ≤ (∑ range(j'+1) Δ) - 1 to feed embeddedChainTime_strictMono.
    have h_tj' : embeddedChainTime G vm Δ j' ω ≤ ∑ m ∈ Finset.range j', Δ m := h_tight j'
    have h_succ_ge : 1 ≤ Δ j' := hΔ_pos _
    have h_sum_split : (∑ m ∈ Finset.range j', Δ m) + Δ j' =
        ∑ m ∈ Finset.range (j' + 1), Δ m := by
      rw [Finset.sum_range_succ]
    have h_le_cap : embeddedChainTime G vm Δ j' ω ≤
        (∑ m ∈ Finset.range (j' + 1), Δ m) - 1 := by omega
    exact (embeddedChainTime_strictMono G vm Δ j' ω h_le_cap).le

/-- L50: Combined potential D_j accumulation bound (corrected conclusion).

Per-step drift: E[Ψ_{j+1} - Ψ_j | ℱ_{T_j}] ≤ -D_j a.s. where
  Ψ_j(ω) = (√vol(s_0)/d_min)·√vol(S_{T_j}) + log(1+vol(S_{T_j}))
  D_j = 1_{T_j < τ'} · (φ_j/2048 ∧ 1/2048)
  τ' = first embedded time with vol(S_{T_j}) ≥ 8·vol(s_0).

Consequence: Pr[S_{T_J} ≠ ∅ ∧ (vol(S_{T_j}) < 8·vol(s_0) for all j ≤ J)] ≤ 3/8.
(Not P(B) ≤ 3/8 where B = Aᶜ — that would be inconsistent with P(A) ≤ 1/8 via Doob.
Budget: P(A) ≤ 1/8 and this bound ≤ 3/8 sum to 1/2.) -/
lemma combined_potential_dj_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (G : TemporalGraphFixedDegree V)
    (vm : G.VoterModelAbstract 2 Ω)
    (d_min : ℕ) (hd : d_min = G.minDegreeAt 0) (hd_pos : 0 < d_min)
    (s_0 : Finset V) (hs_0_ne : s_0.Nonempty)
    (hs_0 : ∀ ω, vm.S 0 ω = s_0)
    (Δ : ℕ → ℕ) (hΔ_pos : ∀ j, 1 ≤ Δ j)
    (φ : ℕ → ℝ) (hφ_nn : ∀ j, 0 ≤ φ j) (hφ_le1 : ∀ j, φ j ≤ 1)
    -- Window-guarantee hypothesis (per-interval MAX-form, paper's
    -- `φ^{I_j}(𝒢) ≥ φ_j`).
    (hwin : ∀ j, ∀ S ∈ G.admissibleCuts,
      φ j ≤ G.maxSetConductanceOnInterval (∑ i ∈ Finset.range j, Δ i) (Δ j) S)
    (b : ℝ) (hb_large : (5462 : ℝ) ≤ b)
    (J : ℕ)
    -- Threshold: ∑_{ℓ=0}^{J} φ_ℓ ≥ b·(Vol(s₀)/d_min + log(1+Vol(s₀))).
    -- The log term is required by the Lyapunov argument (Φ = α·ψ + χ, both components
    -- contribute to Φ₀). Because s₀ varies per fiber, the log cannot be uniformly bounded
    -- by a constant multiple of Vol(s₀)/d_min at this level of generality.
    (hJ : b * ((TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) / d_min
               + Real.log (1 + (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ)))
          ≤ ∑ ℓ ∈ Finset.range (J + 1), φ ℓ) :
    -- Pr[S_{T_J} ≠ ∅ ∧ vol(S_{T_j}) < 8·vol(s_0) for all j ≤ J] ≤ 3/8
    ((vm.μ : Measure Ω) {ω | vm.S (embeddedChainTime G.toTemporalGraph vm Δ J ω) ω ≠ ∅ ∧
        ∀ j ≤ J,
        (TemporalGraph.volume G.toTemporalGraph 0 (vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω) : ℝ) <
        8 * (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ)}).toReal ≤ 3 / 8 := by
  -- ── Abbreviations ─────────────────────────────────────────────────────────────
  set C := {ω : Ω | vm.S (embeddedChainTime G.toTemporalGraph vm Δ J ω) ω ≠ ∅ ∧
      ∀ j ≤ J, (TemporalGraph.volume G.toTemporalGraph 0 (vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω) : ℝ) <
        8 * (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ)} with hC_def
  -- ── Initial potential Ψ₀ = vol(s₀)/d_min + log(1 + vol(s₀)) ─────────────────
  set Ψ₀ : ℝ := (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) / d_min +
      Real.log (1 + (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ)) with hΨ₀_def
  -- ── Step 1: Ψ₀ > 0 ──────────────────────────────────────────────────────────
  have hvol_pos : (0 : ℝ) < TemporalGraph.volume G.toTemporalGraph 0 s_0 := by
    have hd_deg : ∀ v : V, 0 < (G.snapshot 0).degree v := fun v => G.degrees_pos v 0
    exact_mod_cast SimpleGraph.volume_pos_of_nonempty hs_0_ne hd_deg
  have hΨ₀_pos : 0 < Ψ₀ := by
    apply add_pos_of_nonneg_of_pos
    · positivity
    · apply Real.log_pos; linarith
  -- ── Step 2: Compensator U_J ──────────────────────────────────────────────────
  -- U_J ω := Σ_{j ∈ range (J+1)} D_j(ω)
  -- D_j(ω) = min(φ_j/2048, 1/2048) if vol never 8-folds through step j, else 0.
  -- On C: D_j(ω) = min(φ_j/2048, 1/2048) ≥ (1/2048)·φ_j for all j ≤ J.
  let U_J : Ω → ℝ := fun ω =>
    ∑ j ∈ Finset.range (J + 1),
      if ∀ k ≤ j, (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) ≠ ∅ ∧
          (TemporalGraph.volume G.toTemporalGraph 0 (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) : ℝ) <
          8 * (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ)
      then min (φ j / 2048) (1 / 2048)
      else 0
  -- ── Step 3: U_J ≥ 0 pointwise ────────────────────────────────────────────────
  have hU_nn : ∀ ω, 0 ≤ U_J ω := fun ω =>
    Finset.sum_nonneg fun j _ => by
      split_ifs with h
      · exact le_min (div_nonneg (hφ_nn j) (by norm_num)) (by norm_num)
      · linarith
  -- ── Step 4: U_J is bounded above ──────────────────────────────────────────────
  -- Each term ≤ 1/2048, so U_J ≤ (J+1)/2048.
  have hU_bnd : ∀ ω, U_J ω ≤ (J + 1 : ℝ) / 2048 := by
    intro ω
    have hterm : ∀ j ∈ Finset.range (J + 1),
        (if ∀ k ≤ j, (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) ≠ ∅ ∧
            (TemporalGraph.volume G.toTemporalGraph 0 (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) : ℝ) <
            8 * (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ)
         then min (φ j / 2048) (1 / 2048 : ℝ) else 0) ≤ 1 / 2048 := by
      intro j _; split_ifs with h
      · exact min_le_right _ _
      · norm_num
    calc U_J ω = ∑ j ∈ Finset.range (J + 1), _ := rfl
      _ ≤ ∑ _j ∈ Finset.range (J + 1), (1 / 2048 : ℝ) := Finset.sum_le_sum hterm
      _ = (J + 1 : ℝ) / 2048 := by
            rw [Finset.sum_const, Finset.card_range]
            simp only [nsmul_eq_mul]; push_cast; ring
  -- ── Step 5: U_J is integrable (probability measure + bounded) ─────────────────
  haveI hprob : IsProbabilityMeasure (vm.μ : Measure Ω) := inferInstance
  have hU_int : Integrable U_J vm.μ := by
    -- U_J is a finite sum of bounded indicator-weighted constants; hence integrable.
    apply MeasureTheory.Integrable.of_bound (C := (J + 1 : ℝ) / 2048)
    · -- Measurability: build via stopping-time machinery for embedded chain.
      have hS_meas : ∀ t, @Measurable Ω (Finset V) (vm.ℱ t) ⊤ (vm.S t) := fun t =>
        (measurable_of_countable (fun A => VoterModel.minoritySet G.toTemporalGraph t A)).comp
          (vm.A_stronglyAdapted t).measurable
      have hT_meas : ∀ k, Measurable (embeddedChainTime G.toTemporalGraph vm Δ k) := by
        intro k s _
        rw [show (embeddedChainTime G.toTemporalGraph vm Δ k) ⁻¹' s =
            ⋃ t ∈ s, {w | embeddedChainTime G.toTemporalGraph vm Δ k w = t} from by ext ω; simp]
        refine MeasurableSet.biUnion (Set.to_countable s) (fun t _ => ?_)
        rw [show {w : Ω | embeddedChainTime G.toTemporalGraph vm Δ k w = t} =
            {w | (embeddedChainTime G.toTemporalGraph vm Δ k w : ℕ∞) = ↑t} from by
              ext w; simp [Nat.cast_inj]]
        exact vm.ℱ.le t _
          (embeddedChainTime_isStoppingTime G.toTemporalGraph vm Δ hS_meas k |>.measurableSet_eq t)
      have h_S_emb : ∀ k, Measurable (fun ω => vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) := by
        intro k S hS
        rw [show (fun ω => vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) ⁻¹' S =
            ⋃ t : ℕ, (embeddedChainTime G.toTemporalGraph vm Δ k) ⁻¹' {t} ∩ (vm.S t) ⁻¹' S
            from by ext ω; simp [eq_comm]]
        refine MeasurableSet.iUnion (fun t => ?_)
        exact (hT_meas k (measurableSet_singleton _)).inter (vm.ℱ.le t _ (hS_meas t hS))
      have h_set_meas : ∀ j, MeasurableSet
          {ω | ∀ k ≤ j,
            (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) ≠ ∅ ∧
            (TemporalGraph.volume G.toTemporalGraph 0 (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) : ℝ) <
              8 * (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ)} := by
        intro j
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
        have hvol : Measurable (fun s : Finset V => (TemporalGraph.volume G.toTemporalGraph 0 s : ℝ)) :=
          measurable_of_countable _
        have h_ne : MeasurableSet
            {ω : Ω | (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) ≠ ∅} :=
          (h_S_emb k) (measurableSet_singleton _).compl
        exact h_ne.inter ((hvol.comp (h_S_emb k)) measurableSet_Iio)
      refine Measurable.aestronglyMeasurable ?_
      refine Finset.measurable_sum _ (fun j _ => ?_)
      exact Measurable.ite (h_set_meas j) measurable_const measurable_const
    · exact Filter.Eventually.of_forall fun ω => by
        simp only [Real.norm_of_nonneg (hU_nn ω)]; exact hU_bnd ω
  -- ── Step 6: ∫ U_J ≤ Ψ₀ via telescoping over the L51 per-step bound ────────────
  -- Strategy: write each summand of U_J as the "D_j" term of L51's integrand and
  -- absorb the ψ/χ difference into a telescoping sum.  Specifically L51 gives
  -- ∫ (α·ψ_{j+1} + χ_{j+1} - α·ψ_j - χ_j + D_j) dμ ≤ 0, so
  -- ∫ D_j ≤ ∫ Φ_j - ∫ Φ_{j+1} where Φ_k := α·ψ_k + χ_k (with T_k embedded).
  -- Summing over j ∈ range (J+1) and dropping the nonneg term -∫ Φ_{J+1} yields
  -- ∫ U_J ≤ ∫ Φ_0 = α·√vol(s₀) + log(1 + vol(s₀)) = Ψ₀.
  have hEU_J : ∫ ω, U_J ω ∂vm.μ ≤ Ψ₀ := by
    -- α = √vol(s_0) / d_min ≥ 0.
    set α : ℝ := Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) / (d_min : ℝ) with hα_def
    have hα_nn : 0 ≤ α := by
      apply div_nonneg (Real.sqrt_nonneg _)
      exact Nat.cast_nonneg _
    -- ψ_emb k ω = vm.psiS (T_k ω) ω, χ_emb k ω = chiPotential (T_k ω) (S_{T_k ω} ω).
    set ψE : ℕ → Ω → ℝ := fun k ω => vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω with hψE_def
    set χE : ℕ → Ω → ℝ := fun k ω => G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ k ω)
        (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) with hχE_def
    -- D j ω = the j-th summand of U_J.
    set D : ℕ → Ω → ℝ := fun j ω =>
      if ∀ k ≤ j, (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) ≠ ∅ ∧
          (TemporalGraph.volume G.toTemporalGraph 0 (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) : ℝ) <
          8 * (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ)
      then min (φ j / 2048) (1 / 2048 : ℝ) else 0 with hD_def
    -- Φ k ω = α · ψE k ω + χE k ω
    set Φ : ℕ → Ω → ℝ := fun k ω => α * ψE k ω + χE k ω with hΦ_def
    -- Bound: ψE k ω ≤ √vol(univ) and χE k ω ≤ log(1 + vol(univ)), with vol time-invariant.
    set Vu : ℕ := TemporalGraph.volume G.toTemporalGraph 0 (Finset.univ : Finset V) with hVu_def
    have hVu_nn : (0 : ℝ) ≤ (Vu : ℝ) := by exact_mod_cast Nat.zero_le _
    have hVol_le_univ : ∀ t S, TemporalGraph.volume G.toTemporalGraph t S ≤ Vu := by
      intro t S
      have h1 : TemporalGraph.volume G.toTemporalGraph t S ≤ TemporalGraph.volume G.toTemporalGraph t Finset.univ := by
        unfold TemporalGraph.volume SimpleGraph.volume
        exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      have h2 : TemporalGraph.volume G.toTemporalGraph t Finset.univ = Vu :=
        G.volume_fixed _ _ _
      exact h1.trans_eq h2
    -- Pointwise bounds on ψE, χE.
    have hψE_nn : ∀ k ω, 0 ≤ ψE k ω := fun k ω => by
      simp only [ψE, TemporalGraph.VoterModelAbstract.psiS, TemporalGraph.potential]
      exact Real.sqrt_nonneg _
    have hψE_bnd : ∀ k ω, ψE k ω ≤ Real.sqrt (Vu : ℝ) := fun k ω => by
      simp only [ψE, TemporalGraph.VoterModelAbstract.psiS, TemporalGraph.potential]
      apply Real.sqrt_le_sqrt
      exact_mod_cast hVol_le_univ _ _
    have hχE_nn : ∀ k ω, 0 ≤ χE k ω := fun k ω => by
      simp only [χE, TemporalGraph.chiPotential]
      apply Real.log_nonneg
      have h : (0 : ℝ) ≤ (TemporalGraph.volume G.toTemporalGraph (embeddedChainTime G.toTemporalGraph vm Δ k ω)
          (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) : ℝ) := by exact_mod_cast Nat.zero_le _
      linarith
    have hχE_bnd : ∀ k ω, χE k ω ≤ Real.log (1 + (Vu : ℝ)) := fun k ω => by
      simp only [χE, TemporalGraph.chiPotential]
      apply Real.log_le_log (by linarith [show (0 : ℝ) ≤
        (TemporalGraph.volume G.toTemporalGraph (embeddedChainTime G.toTemporalGraph vm Δ k ω)
          (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) : ℝ) from by exact_mod_cast Nat.zero_le _])
      have := hVol_le_univ (embeddedChainTime G.toTemporalGraph vm Δ k ω)
        (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω)
      have : (TemporalGraph.volume G.toTemporalGraph (embeddedChainTime G.toTemporalGraph vm Δ k ω)
          (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) : ℝ) ≤ (Vu : ℝ) := by exact_mod_cast this
      linarith
    -- Measurability of ψE k and χE k (via stopping-time decomposition).
    have hS_meas_ℱ : ∀ t, @Measurable Ω (Finset V) (vm.ℱ t) ⊤ (vm.S t) := fun t =>
      (measurable_of_countable (fun A => VoterModel.minoritySet G.toTemporalGraph t A)).comp
        (vm.A_stronglyAdapted t).measurable
    have hT_meas : ∀ k, Measurable (embeddedChainTime G.toTemporalGraph vm Δ k) := by
      intro k s _
      rw [show (embeddedChainTime G.toTemporalGraph vm Δ k) ⁻¹' s =
          ⋃ t ∈ s, {w | embeddedChainTime G.toTemporalGraph vm Δ k w = t} from by ext ω; simp]
      refine MeasurableSet.biUnion (Set.to_countable s) (fun t _ => ?_)
      rw [show {w : Ω | embeddedChainTime G.toTemporalGraph vm Δ k w = t} =
          {w | (embeddedChainTime G.toTemporalGraph vm Δ k w : ℕ∞) = ↑t} from by
            ext w; simp [Nat.cast_inj]]
      exact vm.ℱ.le t _
        (embeddedChainTime_isStoppingTime G.toTemporalGraph vm Δ hS_meas_ℱ k |>.measurableSet_eq t)
    have hψE_meas : ∀ k, Measurable (ψE k) := by
      intro k S hS
      rw [show (ψE k) ⁻¹' S = ⋃ t : ℕ, (embeddedChainTime G.toTemporalGraph vm Δ k) ⁻¹' {t} ∩
            (vm.psiS t) ⁻¹' S from by
        ext ω
        simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_singleton_iff]
        constructor
        · intro h
          exact ⟨embeddedChainTime G.toTemporalGraph vm Δ k ω, rfl, h⟩
        · rintro ⟨t, heq, hp⟩
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
    have hχE_meas : ∀ k, Measurable (χE k) := by
      intro k S hS
      rw [show (χE k) ⁻¹' S = ⋃ t : ℕ, (embeddedChainTime G.toTemporalGraph vm Δ k) ⁻¹' {t} ∩
            (fun ω => G.chiPotential t (vm.S t ω)) ⁻¹' S from by
        ext ω
        simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_singleton_iff]
        constructor
        · intro h
          exact ⟨embeddedChainTime G.toTemporalGraph vm Δ k ω, rfl, h⟩
        · rintro ⟨t, heq, hp⟩
          show G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ k ω)
            (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) ∈ S
          rw [heq]; exact hp]
      refine MeasurableSet.iUnion (fun t => ?_)
      have hchi_meas : Measurable (fun ω => G.chiPotential t (vm.S t ω)) := by
        have hchi_fn : Measurable
            (fun s : Finset V => G.chiPotential t s) :=
          measurable_of_countable _
        have hS_t : Measurable (vm.S t) := fun S hS => vm.ℱ.le t _ ((hS_meas_ℱ t) hS)
        exact hchi_fn.comp hS_t
      exact (hT_meas k (measurableSet_singleton _)).inter (hchi_meas hS)
    -- Integrability of ψE k and χE k (bounded ⇒ integrable on probability measure).
    have hψE_int : ∀ k, Integrable (ψE k) vm.μ := fun k =>
      MeasureTheory.Integrable.of_bound (C := Real.sqrt (Vu : ℝ))
        (hψE_meas k).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => by
          rw [Real.norm_of_nonneg (hψE_nn k ω)]; exact hψE_bnd k ω)
    have hχE_int : ∀ k, Integrable (χE k) vm.μ := fun k => by
      refine MeasureTheory.Integrable.of_bound (C := |Real.log (1 + (Vu : ℝ))|)
        (hχE_meas k).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_of_nonneg (hχE_nn k ω)]
      exact (hχE_bnd k ω).trans (le_abs_self _)
    have hΦ_int : ∀ k, Integrable (Φ k) vm.μ := fun k =>
      ((hψE_int k).const_mul α).add (hχE_int k)
    -- Measurability of D j (the j-th summand of U_J).
    have h_set_meas : ∀ j, MeasurableSet
        {ω | ∀ k ≤ j,
          (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) ≠ ∅ ∧
          (TemporalGraph.volume G.toTemporalGraph 0 (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) : ℝ) <
            8 * (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ)} := by
      intro j
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
        exact (hT_meas k (measurableSet_singleton _)).inter
          (vm.ℱ.le t _ (hS_meas_ℱ t hS))
      have hvol : Measurable (fun s : Finset V => (TemporalGraph.volume G.toTemporalGraph 0 s : ℝ)) :=
        measurable_of_countable _
      have h_ne : MeasurableSet
          {ω : Ω | (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) ≠ ∅} :=
        hS_emb_meas (measurableSet_singleton _).compl
      exact h_ne.inter ((hvol.comp hS_emb_meas) measurableSet_Iio)
    have hD_meas : ∀ j, Measurable (D j) := fun j => by
      simp only [D]
      exact Measurable.ite (h_set_meas j) measurable_const measurable_const
    have hD_nn : ∀ j ω, 0 ≤ D j ω := fun j ω => by
      simp only [D]
      split_ifs with h
      · exact le_min (div_nonneg (hφ_nn j) (by norm_num)) (by norm_num)
      · linarith
    have hD_bnd : ∀ j ω, D j ω ≤ 1 / 2048 := fun j ω => by
      simp only [D]
      split_ifs with h
      · exact min_le_right _ _
      · norm_num
    have hD_int : ∀ j, Integrable (D j) vm.μ := fun j =>
      MeasureTheory.Integrable.of_bound (C := (1 / 2048 : ℝ))
        (hD_meas j).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => by
          rw [Real.norm_of_nonneg (hD_nn j ω)]; exact hD_bnd j ω)
    -- L51's per-step bound, restated using ψE, χE, D, α.
    have hL51 : ∀ j, ∫ ω, (Φ (j + 1) ω - Φ j ω + D j ω) ∂vm.μ ≤ 0 := by
      intro j
      have h := psi_chi_combined_drift_integrated G vm d_min hd hd_pos s_0
        hs_0_ne Δ hΔ_pos φ hφ_nn hwin j
      convert h using 2
      funext ω
      simp only [Φ, ψE, χE, D, α]
      ring
    -- From L51: ∫ D_j ≤ ∫ Φ_j - ∫ Φ_{j+1}.
    have hL51_rearr : ∀ j, ∫ ω, D j ω ∂vm.μ ≤
        (∫ ω, Φ j ω ∂vm.μ) - (∫ ω, Φ (j + 1) ω ∂vm.μ) := by
      intro j
      have h := hL51 j
      have hsplit : ∫ ω, (Φ (j + 1) ω - Φ j ω + D j ω) ∂vm.μ =
          (∫ ω, Φ (j + 1) ω ∂vm.μ) - (∫ ω, Φ j ω ∂vm.μ) +
          (∫ ω, D j ω ∂vm.μ) := by
        have hint1 : Integrable (fun ω => Φ (j + 1) ω - Φ j ω) vm.μ :=
          (hΦ_int (j + 1)).sub (hΦ_int j)
        have hadd : ∫ ω, ((fun ω => Φ (j + 1) ω - Φ j ω) ω + D j ω) ∂vm.μ =
            (∫ ω, (fun ω => Φ (j + 1) ω - Φ j ω) ω ∂vm.μ) +
            (∫ ω, D j ω ∂vm.μ) := integral_add hint1 (hD_int j)
        have hsub : ∫ ω, (Φ (j + 1) ω - Φ j ω) ∂vm.μ =
            (∫ ω, Φ (j + 1) ω ∂vm.μ) - (∫ ω, Φ j ω ∂vm.μ) :=
          integral_sub (hΦ_int (j + 1)) (hΦ_int j)
        linarith [hadd, hsub]
      linarith [h, hsplit]
    -- Sum: ∫ U_J = Σ ∫ D_j over range (J+1), and Σ ∫ D_j telescopes to ≤ ∫ Φ_0 - ∫ Φ_{J+1}.
    have hU_eq_sum : ∫ ω, U_J ω ∂vm.μ = ∑ j ∈ Finset.range (J + 1), ∫ ω, D j ω ∂vm.μ := by
      have : ∀ ω, U_J ω = ∑ j ∈ Finset.range (J + 1), D j ω := fun ω => by
        simp only [U_J, D]
      simp_rw [this]
      exact integral_finsetSum (Finset.range (J + 1)) (fun j _ => hD_int j)
    have hΦJ1_nn : 0 ≤ ∫ ω, Φ (J + 1) ω ∂vm.μ := by
      apply integral_nonneg
      intro ω
      show (0 : ℝ) ≤ α * ψE (J + 1) ω + χE (J + 1) ω
      have h1 : 0 ≤ α * ψE (J + 1) ω := mul_nonneg hα_nn (hψE_nn _ _)
      linarith [hχE_nn (J + 1) ω]
    -- ∫ Φ_0 = α · √vol(s_0) + log(1 + vol(s_0)) = Ψ₀.
    have hΦ0_eq_Ψ₀ : ∫ ω, Φ 0 ω ∂vm.μ = Ψ₀ := by
      have hT0 : ∀ ω, embeddedChainTime G.toTemporalGraph vm Δ 0 ω = 0 := fun _ => rfl
      have hpsi0 : ∀ ω, ψE 0 ω = Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) := fun ω => by
        show vm.psiS (embeddedChainTime G.toTemporalGraph vm Δ 0 ω) ω =
          Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ)
        rw [hT0 ω]
        show TemporalGraph.potential G.toTemporalGraph 0 (vm.S 0 ω) = _
        rw [hs_0 ω]; rfl
      have hchi0 : ∀ ω, χE 0 ω = Real.log (1 + (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ)) := fun ω => by
        show G.chiPotential (embeddedChainTime G.toTemporalGraph vm Δ 0 ω)
          (vm.S (embeddedChainTime G.toTemporalGraph vm Δ 0 ω) ω) = _
        rw [hT0 ω, hs_0 ω]; rfl
      have h_const : ∀ ω, Φ 0 ω = Ψ₀ := fun ω => by
        show α * ψE 0 ω + χE 0 ω = Ψ₀
        rw [hpsi0 ω, hchi0 ω]
        have hv_nn : (0 : ℝ) ≤ (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) := Nat.cast_nonneg _
        have hd_pos_r : (0 : ℝ) < (d_min : ℝ) := by exact_mod_cast hd_pos
        have hsqrt_sq : Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) *
            Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) =
            (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) := Real.mul_self_sqrt hv_nn
        show Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) / (d_min : ℝ) *
            Real.sqrt (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) +
            Real.log (1 + (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ)) = Ψ₀
        rw [div_mul_eq_mul_div, hsqrt_sq, hΨ₀_def]
      simp_rw [h_const]
      simp
    -- Telescoping sum bound.
    have h_tele : ∑ j ∈ Finset.range (J + 1), ∫ ω, D j ω ∂vm.μ ≤
        (∫ ω, Φ 0 ω ∂vm.μ) - (∫ ω, Φ (J + 1) ω ∂vm.μ) := by
      have hsum_diff : ∀ J', ∑ j ∈ Finset.range (J' + 1),
          ((∫ ω, Φ j ω ∂vm.μ) - (∫ ω, Φ (j + 1) ω ∂vm.μ)) =
          (∫ ω, Φ 0 ω ∂vm.μ) - (∫ ω, Φ (J' + 1) ω ∂vm.μ) := by
        intro J'
        induction J' with
        | zero => simp
        | succ K ih =>
            rw [Finset.sum_range_succ, ih]
            ring
      have hsum_diff_J := hsum_diff J
      calc ∑ j ∈ Finset.range (J + 1), ∫ ω, D j ω ∂vm.μ
          ≤ ∑ j ∈ Finset.range (J + 1),
              ((∫ ω, Φ j ω ∂vm.μ) - (∫ ω, Φ (j + 1) ω ∂vm.μ)) :=
            Finset.sum_le_sum (fun j _ => hL51_rearr j)
        _ = (∫ ω, Φ 0 ω ∂vm.μ) - (∫ ω, Φ (J + 1) ω ∂vm.μ) := hsum_diff_J
    -- Final: ∫ U_J = Σ ∫ D_j ≤ ∫ Φ_0 - ∫ Φ_{J+1} ≤ ∫ Φ_0 = Ψ₀.
    calc ∫ ω, U_J ω ∂vm.μ
        = ∑ j ∈ Finset.range (J + 1), ∫ ω, D j ω ∂vm.μ := hU_eq_sum
      _ ≤ (∫ ω, Φ 0 ω ∂vm.μ) - (∫ ω, Φ (J + 1) ω ∂vm.μ) := h_tele
      _ ≤ ∫ ω, Φ 0 ω ∂vm.μ := by linarith
      _ = Ψ₀ := hΦ0_eq_Ψ₀
  -- ── Step 7: Lower bound of U_J on event C ─────────────────────────────────────
  -- On C, D_j(ω) = min(φ_j/2048, 1/2048) ≥ (1/2048)·φ_j (since φ_j ≤ 1).
  -- So U_J(ω) ≥ (1/2048)·Σ_{j≤J} φ_j ≥ (b/2048)·Ψ₀ ≥ (5462/2048)·Ψ₀ > 8/3·Ψ₀.
  -- Stated a.e. (rather than for every `ω`): the only step needing absorption
  -- permanence (`hS_nonempty_all` below) is a.e. via `ae_minoritySet_empty_of_absorptionTime_le`.
  have hU_lower : ∀ᵐ ω ∂(vm.μ : Measure Ω), ω ∈ C → 8 / 3 * Ψ₀ ≤ U_J ω := by
    filter_upwards [vm.ae_minoritySet_empty_of_absorptionTime_le] with ω hperm hω
    obtain ⟨hSJ_ne, hvol_lt⟩ := hω
    -- On C, the if-branch fires for all j ≤ J.
    -- The new conjunction `vm.S (T_k ω) ω ≠ ∅ ∧ vol < 8·vol(s_0)` requires showing
    -- (i) `vm.S (T_k ω) ω ≠ ∅`: by absorption monotonicity, since `vm.S (T_J ω) ω ≠ ∅`
    --     and `T_k ω ≤ T_J ω` (`embeddedChainTime_mono`), absorption hasn't happened yet.
    -- (ii) `vol < 8·vol(s_0)`: direct from `hvol_lt`.
    have hS_nonempty_all : ∀ k ≤ J, vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω ≠ ∅ := by
      intro k hkJ hSk_empty
      -- `vm.S (T_k ω) ω = minoritySet G.toTemporalGraph (T_k ω) (vm.opinionZeroSet (T_k ω) ω)`.
      -- If empty, `absorptionTime ω ≤ T_k` directly (first-hitting characterization).
      have hSk_eq : VoterModel.minoritySet G.toTemporalGraph (embeddedChainTime G.toTemporalGraph vm Δ k ω)
          (vm.opinionZeroSet (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) = ∅ := hSk_empty
      have hTabs_le_Tk : vm.absorptionTime ω ≤ (embeddedChainTime G.toTemporalGraph vm Δ k ω : ℕ∞) :=
        (vm.absorptionTime_le_coe_iff_exists ω (embeddedChainTime G.toTemporalGraph vm Δ k ω)).mpr
          ⟨embeddedChainTime G.toTemporalGraph vm Δ k ω, le_refl _, hSk_eq⟩
      -- By `embeddedChainTime_mono`, `T_k ω ≤ T_J ω`, hence `absorptionTime ω ≤ T_J ω`.
      have hTk_le_TJ : embeddedChainTime G.toTemporalGraph vm Δ k ω ≤
          embeddedChainTime G.toTemporalGraph vm Δ J ω :=
        embeddedChainTime_mono G.toTemporalGraph vm Δ hΔ_pos hkJ ω
      have hTabs_le_TJ : vm.absorptionTime ω ≤ (embeddedChainTime G.toTemporalGraph vm Δ J ω : ℕ∞) :=
        le_trans hTabs_le_Tk (by exact_mod_cast hTk_le_TJ)
      -- Then `vm.S (T_J ω) ω = ∅` by a.e. permanence, contradicting `hSJ_ne`.
      exact hSJ_ne (hperm (embeddedChainTime G.toTemporalGraph vm Δ J ω) hTabs_le_TJ)
    -- On C, the if-branch fires for all j ≤ J
    have hD_eq : U_J ω = ∑ j ∈ Finset.range (J + 1), min (φ j / 2048) (1 / 2048 : ℝ) :=
      Finset.sum_congr rfl fun j hj => by
        simp only [Finset.mem_range] at hj
        have hj_le : j ≤ J := Nat.lt_succ_iff.mp hj
        -- The if-condition holds at this j since for all k ≤ j ≤ J,
        -- both clauses follow from membership in C.
        have hcond_pos : ∀ k ≤ j,
            (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) ≠ ∅ ∧
            (TemporalGraph.volume G.toTemporalGraph 0 (vm.S (embeddedChainTime G.toTemporalGraph vm Δ k ω) ω) : ℝ) <
            8 * (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) := by
          intro k hkj
          have hkJ : k ≤ J := Nat.le_trans hkj hj_le
          exact ⟨hS_nonempty_all k hkJ, hvol_lt k hkJ⟩
        simp only [if_pos hcond_pos]
    -- min(φ(j+1)/2048, 1/2048) ≥ (1/2048)·φ(j+1) (since φ(j+1) ≤ 1)
    have hD_lb : ∀ j, min (φ j / 2048) (1 / 2048 : ℝ) ≥ (1 / 2048) * φ j := by
      intro j
      have hle : φ j ≤ 1 := hφ_le1 j
      have hnn : 0 ≤ φ j := hφ_nn j
      simp only [ge_iff_le, min_def]; split_ifs with h
      · linarith
      · push Not at h; linarith
    calc (8 / 3 * Ψ₀ : ℝ)
        ≤ b / 2048 * Ψ₀ := by nlinarith [hb_large, hΨ₀_pos]
      _ = (1 / 2048) * (b * Ψ₀) := by ring
      _ ≤ (1 / 2048) * ∑ j ∈ Finset.range (J + 1), φ j := by
            apply mul_le_mul_of_nonneg_left hJ; norm_num
      _ = ∑ j ∈ Finset.range (J + 1), (1 / 2048 : ℝ) * φ j := by rw [Finset.mul_sum]
      _ ≤ ∑ j ∈ Finset.range (J + 1), min (φ j / 2048) (1 / 2048 : ℝ) :=
            Finset.sum_le_sum (fun j _ => hD_lb j)
      _ = U_J ω := hD_eq.symm
  -- ── Step 8: Markov's inequality ──────────────────────────────────────────────
  -- P(C) ≤ P(U_J ≥ 8/3·Ψ₀) ≤ E[U_J]/(8/3·Ψ₀) ≤ Ψ₀/(8/3·Ψ₀) = 3/8.
  have h3Ψ₀_pos : 0 < 8 / 3 * Ψ₀ := by linarith
  -- markov_inequality gives: μ{U_J ≥ 3Ψ₀} ≤ ofReal ((∫ U_J) / (3Ψ₀))
  have hmarkov := markov_inequality (Filter.Eventually.of_forall hU_nn) hU_int h3Ψ₀_pos
  -- hmarkov : (vm.μ : Measure Ω) {ω | 8 / 3 * Ψ₀ ≤ U_J ω} ≤ ENNReal.ofReal ((∫ x, U_J x ∂vm.μ) / (8 / 3 * Ψ₀))
  set EUJ := ∫ x, U_J x ∂vm.μ with hEUJ_def
  calc ((vm.μ : Measure Ω) C).toReal
      ≤ ((vm.μ : Measure Ω) {ω | 8 / 3 * Ψ₀ ≤ U_J ω}).toReal :=
          ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hU_lower)
    _ ≤ (ENNReal.ofReal (EUJ / (8 / 3 * Ψ₀))).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hmarkov
    _ = EUJ / (8 / 3 * Ψ₀) :=
          ENNReal.toReal_ofReal (div_nonneg (integral_nonneg hU_nn) h3Ψ₀_pos.le)
    _ ≤ Ψ₀ / (8 / 3 * Ψ₀) := by
          apply div_le_div_of_nonneg_right hEU_J h3Ψ₀_pos.le
    _ = 3 / 8 := by field_simp [ne_of_gt hΨ₀_pos]


/-- Doob's maximal inequality applied to the nonneg supermartingale
`vol(t, S_t ω)`. Specifically: the probability that the volume of the minority
process 8-folds at some embedded time `T_j(ω)` with `j ≤ J` is at most `1/8`.

Proof: define a hitting stopping time `σ(ω) := T_{firstHit ω}` where
`firstHit ω` is the first `j ∈ {0,…,J}` with `8·vol(s_0) ≤ vol(0, S_{T_j} ω)`,
or `J` otherwise. By OST on the supermartingale `vol(·,·)`,
`∫ vol(σ ω, S_{σ ω} ω) dμ ≤ vol(s_0)`. On the hit event `A`,
`vol(σ ω, S_{σ ω} ω) ≥ 8·vol(s_0)` (via FixedDegrees, time-invariance of `vol`).
Markov: `8·vol(s_0)·μ(A) ≤ vol(s_0)`, hence `μ(A) ≤ 1/8`. -/
lemma vol8fold_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (G : TemporalGraphFixedDegree V)
    (vm : G.VoterModelAbstract 2 Ω)
    (d_min : ℕ) (hd : d_min = G.minDegreeAt 0) (hd_pos : 0 < d_min)
    (s_0 : Finset V) (hs_0_ne : s_0.Nonempty) (hs_0 : ∀ ω, vm.S 0 ω = s_0)
    (Δ : ℕ → ℕ) (hΔ_pos : ∀ j, 1 ≤ Δ j) (J : ℕ) :
    ((vm.μ : Measure Ω) {ω | ∃ j ≤ J,
        8 * ((G.snapshot 0).volume s_0 : ℝ) ≤
        ((G.snapshot 0).volume (vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω) : ℝ)}).toReal ≤
    1 / 8 := by
  haveI hprob : IsProbabilityMeasure (vm.μ : Measure Ω) := inferInstance
  classical
  -- Measurability of vm.S t w.r.t. vm.ℱ t.
  have hS_meas : ∀ t, @Measurable Ω (Finset V) (vm.ℱ t) ⊤ (vm.S t) := fun t =>
    (measurable_of_countable (fun A => VoterModel.minoritySet G.toTemporalGraph t A)).comp
      (vm.A_stronglyAdapted t).measurable
  -- Volume of s_0 as ℝ; positive since s_0 nonempty and min degree = d_min > 0.
  set c : ℝ := (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) with hc_def
  have hc_nn : 0 ≤ c := Nat.cast_nonneg _
  have hc_pos : 0 < c := by
    obtain ⟨v, hv⟩ := hs_0_ne
    have hsum : (G.snapshot 0).degree v ≤ TemporalGraph.volume G.toTemporalGraph 0 s_0 :=
      Finset.single_le_sum (f := fun u => (G.snapshot 0).degree u)
        (fun _ _ => Nat.zero_le _) hv
    have hge_dmin : d_min ≤ (G.snapshot 0).degree v := by
      rw [hd]; exact TemporalGraph.minDegreeAt_le_degree G.toTemporalGraph 0 v
    have h_pos_nat : 0 < TemporalGraph.volume G.toTemporalGraph 0 s_0 :=
      Nat.lt_of_lt_of_le hd_pos (Nat.le_trans hge_dmin hsum)
    exact Nat.cast_pos.mpr h_pos_nat
  -- Stopping-time scaffolding.
  have hT_stop : ∀ k,
      IsStoppingTime vm.ℱ (fun ω => (embeddedChainTime G.toTemporalGraph vm Δ k ω : ℕ∞)) := fun k =>
    embeddedChainTime_isStoppingTime G.toTemporalGraph vm Δ hS_meas k
  -- {T_k = t} ∈ ℱ t.
  have hT_eq_meas : ∀ k t, MeasurableSet[vm.ℱ t]
      {ω | embeddedChainTime G.toTemporalGraph vm Δ k ω = t} := by
    intro k t
    have h := (hT_stop k).measurableSet_eq t
    have heq : {ω | embeddedChainTime G.toTemporalGraph vm Δ k ω = t} =
        {ω | (embeddedChainTime G.toTemporalGraph vm Δ k ω : ℕ∞) = ↑t} := by
      ext w
      exact ⟨fun heq => by exact_mod_cast heq, fun heq => by exact_mod_cast heq⟩
    rw [heq]
    exact h
  -- vol(0, S_t ω) is ℱ_t-measurable.
  have hvol_S_t_meas : ∀ t, @Measurable Ω ℝ (vm.ℱ t) _
      (fun ω => (TemporalGraph.volume G.toTemporalGraph 0 (vm.S t ω) : ℝ)) := by
    intro t
    exact (measurable_of_countable (fun s : Finset V =>
      (TemporalGraph.volume G.toTemporalGraph 0 s : ℝ))).comp (hS_meas t)
  -- Predicate hit j ω := 8c ≤ vol(0, S_{T_j ω} ω).
  let hit : ℕ → Ω → Prop := fun j ω =>
    8 * c ≤ (TemporalGraph.volume G.toTemporalGraph 0 (vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω) : ℝ)
  -- {hit j ω ∧ T_j ω ≤ n} ∈ ℱ n.
  have h_hit_le_meas : ∀ j n, MeasurableSet[vm.ℱ n]
      {ω | hit j ω ∧ embeddedChainTime G.toTemporalGraph vm Δ j ω ≤ n} := by
    intro j n
    have hset : {ω | hit j ω ∧ embeddedChainTime G.toTemporalGraph vm Δ j ω ≤ n} =
        ⋃ t ∈ Finset.Iic n, ({ω | embeddedChainTime G.toTemporalGraph vm Δ j ω = t} ∩
          {ω | 8 * c ≤ (TemporalGraph.volume G.toTemporalGraph 0 (vm.S t ω) : ℝ)}) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq,
        Finset.mem_Iic, exists_prop, hit]
      constructor
      · rintro ⟨hh, hle⟩
        exact ⟨embeddedChainTime G.toTemporalGraph vm Δ j ω, hle, rfl, hh⟩
      · rintro ⟨t, hle, heq, hh⟩
        refine ⟨?_, heq ▸ hle⟩
        rw [heq]; exact hh
    rw [hset]
    refine MeasurableSet.biUnion (Finset.Iic n).countable_toSet (fun t htle => ?_)
    simp only [Finset.mem_coe, Finset.mem_Iic] at htle
    have hmono : vm.ℱ t ≤ vm.ℱ n := vm.ℱ.mono htle
    have h1 : MeasurableSet[vm.ℱ n] {ω | embeddedChainTime G.toTemporalGraph vm Δ j ω = t} :=
      hmono _ (hT_eq_meas j t)
    have h2 : MeasurableSet[vm.ℱ n]
        {ω | 8 * c ≤ (TemporalGraph.volume G.toTemporalGraph 0 (vm.S t ω) : ℝ)} :=
      hmono _ ((hvol_S_t_meas t) measurableSet_Ici)
    exact h1.inter h2
  -- Global measurability of {hit j ω}.
  have h_hit_meas_global : ∀ j, MeasurableSet {ω | hit j ω} := by
    intro j
    have h_S_emb : Measurable (fun ω => vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω) := by
      intro S hS
      rw [show (fun ω => vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω) ⁻¹' S =
          ⋃ t : ℕ, (embeddedChainTime G.toTemporalGraph vm Δ j) ⁻¹' {t} ∩ (vm.S t) ⁻¹' S
          from by ext ω; simp [eq_comm]]
      refine MeasurableSet.iUnion (fun t => ?_)
      have hT_glob : Measurable (embeddedChainTime G.toTemporalGraph vm Δ j) := by
        intro s _
        rw [show (embeddedChainTime G.toTemporalGraph vm Δ j) ⁻¹' s =
            ⋃ t ∈ s, {w | embeddedChainTime G.toTemporalGraph vm Δ j w = t} from by ext ω; simp]
        refine MeasurableSet.biUnion (Set.to_countable s) (fun t' _ => ?_)
        exact vm.ℱ.le t' _ (hT_eq_meas j t')
      exact (hT_glob (measurableSet_singleton _)).inter (vm.ℱ.le t _ (hS_meas t hS))
    exact ((measurable_of_countable (fun s : Finset V =>
      (TemporalGraph.volume G.toTemporalGraph 0 s : ℝ))).comp h_S_emb) measurableSet_Ici
  -- ── Step 3: define firstHit and σ ─────────────────────────────────────────
  -- firstHit ω : ℕ — the smallest j ∈ {0,…,J} with hit j ω, else J (default).
  let firstHit : Ω → ℕ := fun ω =>
    if h : ∃ j ∈ Finset.range (J + 1), hit j ω
    then ((Finset.range (J + 1)).filter (hit · ω)).min'
          (by obtain ⟨j, hj_mem, hj_hit⟩ := h
              exact ⟨j, Finset.mem_filter.mpr ⟨hj_mem, hj_hit⟩⟩)
    else J
  have hfH_le_J : ∀ ω, firstHit ω ≤ J := fun ω => by
    simp only [firstHit]
    split_ifs with hex
    · have hmem := ((Finset.range (J + 1)).filter (hit · ω)).min'_mem
        (by obtain ⟨j, hj_mem, hj_hit⟩ := hex
            exact ⟨j, Finset.mem_filter.mpr ⟨hj_mem, hj_hit⟩⟩)
      rw [Finset.mem_filter, Finset.mem_range] at hmem
      omega
    · exact le_rfl
  -- Spec for firstHit.
  have hfH_spec : ∀ ω j, j < J + 1 →
      (firstHit ω = j ↔
        ((hit j ω ∧ ∀ i < j, ¬ hit i ω) ∨
         (j = J ∧ ∀ i ∈ Finset.range (J + 1), ¬ hit i ω))) := by
    intro ω j hjJ
    simp only [firstHit]
    constructor
    · intro hfH
      split_ifs at hfH with hex
      · have hmem := ((Finset.range (J + 1)).filter (hit · ω)).min'_mem
            (by obtain ⟨j', hj'_mem, hj'_hit⟩ := hex
                exact ⟨j', Finset.mem_filter.mpr ⟨hj'_mem, hj'_hit⟩⟩)
        rw [Finset.mem_filter] at hmem
        left
        refine ⟨hfH ▸ hmem.2, ?_⟩
        intro i hi
        by_contra h_hit
        have hi_lt_J1 : i < J + 1 := by
          have : i < j := hi
          omega
        have h_in_filter : i ∈ (Finset.range (J + 1)).filter (hit · ω) :=
          Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi_lt_J1, h_hit⟩
        have hge := ((Finset.range (J + 1)).filter (hit · ω)).min'_le _ h_in_filter
        omega
      · right
        refine ⟨hfH.symm, ?_⟩
        intro i hi h_hit
        exact hex ⟨i, hi, h_hit⟩
    · rintro (⟨hh, hmin⟩ | ⟨hjeq, hnone⟩)
      · have hex : ∃ j' ∈ Finset.range (J + 1), hit j' ω :=
          ⟨j, Finset.mem_range.mpr hjJ, hh⟩
        rw [dif_pos hex]
        apply le_antisymm
        · exact ((Finset.range (J + 1)).filter (hit · ω)).min'_le _
            (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjJ, hh⟩)
        · have hmem := ((Finset.range (J + 1)).filter (hit · ω)).min'_mem
            ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjJ, hh⟩⟩
          rw [Finset.mem_filter] at hmem
          by_contra hlt
          push Not at hlt
          exact hmin _ hlt hmem.2
      · rw [dif_neg (by
          push Not
          intro i hi
          exact hnone i hi)]
        exact hjeq.symm
  -- σ ω := embeddedChainTime G.toTemporalGraph vm Δ (firstHit ω) ω.
  let σ : Ω → ℕ := fun ω => embeddedChainTime G.toTemporalGraph vm Δ (firstHit ω) ω
  -- σ ω ≤ K := ∑ range(J+1) Δ.
  set K : ℕ := ∑ j ∈ Finset.range (J + 1), Δ j with hK_def
  have hσ_le_K : ∀ ω, σ ω ≤ K := fun ω => by
    -- σ ω ≤ T_J ω ≤ K.
    have hmono := embeddedChainTime_mono G.toTemporalGraph vm Δ hΔ_pos (hfH_le_J ω) ω
    have hT_J_le_K : embeddedChainTime G.toTemporalGraph vm Δ J ω ≤ K :=
      embeddedChainTime_le_sum G.toTemporalGraph vm Δ hΔ_pos J ω
    exact hmono.trans hT_J_le_K
  -- σ is a stopping time.
  have hσ_stop : IsStoppingTime vm.ℱ (fun ω => (σ ω : ℕ∞)) := by
    intro n
    show MeasurableSet[vm.ℱ n] {ω | (σ ω : ℕ∞) ≤ ↑n}
    have hset : {ω | (σ ω : ℕ∞) ≤ ↑n} =
        ⋃ j ∈ Finset.range (J + 1),
          {ω | firstHit ω = j ∧ embeddedChainTime G.toTemporalGraph vm Δ j ω ≤ n} := by
      ext ω
      simp only [σ, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_range,
        Nat.cast_le, exists_prop]
      constructor
      · intro hle
        refine ⟨firstHit ω, Nat.lt_succ_of_le (hfH_le_J ω), rfl, ?_⟩
        exact_mod_cast hle
      · rintro ⟨j, _, heq, hle⟩
        rw [heq]; exact_mod_cast hle
    rw [hset]
    refine MeasurableSet.biUnion (Finset.range (J + 1)).countable_toSet (fun j hj => ?_)
    simp only [Finset.mem_coe, Finset.mem_range] at hj
    -- {firstHit = j ∧ T_j ω ≤ n} decomposition.
    -- Use: T_i ≤ T_j when i ≤ j (so we don't need a separate measurability inside).
    have hT_le_n_meas : ∀ i, MeasurableSet[vm.ℱ n]
        {ω | embeddedChainTime G.toTemporalGraph vm Δ i ω ≤ n} := by
      intro i
      have h := (hT_stop i) n
      have heq : {ω | embeddedChainTime G.toTemporalGraph vm Δ i ω ≤ n} =
          {ω | (embeddedChainTime G.toTemporalGraph vm Δ i ω : ℕ∞) ≤ ↑n} := by
        ext w
        exact ⟨fun hle => by exact_mod_cast hle, fun hle => by exact_mod_cast hle⟩
      rw [heq]
      exact h
    -- {¬ hit i ω ∧ T_j ω ≤ n} ∈ ℱ_n for i ≤ j (using monotonicity to lift T_i ≤ n).
    have h_nohit_with_Tj : ∀ i ≤ j, MeasurableSet[vm.ℱ n]
        {ω | ¬ hit i ω ∧ embeddedChainTime G.toTemporalGraph vm Δ j ω ≤ n} := by
      intro i hij
      -- Rewrite: {¬ hit i ω ∧ T_j ω ≤ n}
      --        = {T_j ω ≤ n} \ {hit i ω ∧ T_j ω ≤ n}
      have hcompl : {ω | ¬ hit i ω ∧ embeddedChainTime G.toTemporalGraph vm Δ j ω ≤ n} =
          {ω | embeddedChainTime G.toTemporalGraph vm Δ j ω ≤ n} \
          {ω | hit i ω ∧ embeddedChainTime G.toTemporalGraph vm Δ j ω ≤ n} := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_sdiff]
        tauto
      rw [hcompl]
      refine MeasurableSet.diff (hT_le_n_meas j) ?_
      -- {hit i ω ∧ T_j ω ≤ n} ⊆ {hit i ω ∧ T_i ω ≤ n} (via monotonicity T_i ≤ T_j ≤ n).
      -- So {hit i ω ∧ T_j ω ≤ n} = {hit i ω ∧ T_i ω ≤ n} ∩ {T_j ω ≤ n}.
      have heq : {ω | hit i ω ∧ embeddedChainTime G.toTemporalGraph vm Δ j ω ≤ n} =
          {ω | hit i ω ∧ embeddedChainTime G.toTemporalGraph vm Δ i ω ≤ n} ∩
          {ω | embeddedChainTime G.toTemporalGraph vm Δ j ω ≤ n} := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
        constructor
        · rintro ⟨hh, hTj⟩
          refine ⟨⟨hh, ?_⟩, hTj⟩
          have := embeddedChainTime_mono G.toTemporalGraph vm Δ hΔ_pos hij ω
          linarith
        · rintro ⟨⟨hh, _⟩, hTj⟩
          exact ⟨hh, hTj⟩
      rw [heq]
      exact (h_hit_le_meas i n).inter (hT_le_n_meas j)
    -- Decompose: split into j < J case and j = J case.
    by_cases hjJ : j = J
    · -- Case j = J. {firstHit = J ∧ T_J ω ≤ n} = ({hit J ω ∧ ...} ∪ {no hits}) ∩ {prior no-hits}.
      -- Use: {firstHit = J} = (∀ i < J, ¬ hit i ω) ∧ ((hit J ω) ∨ (¬ hit J ω))
      -- which is simply (∀ i < J, ¬ hit i ω), so {firstHit = J ∧ T_J ω ≤ n}
      -- = (⋂ i < J, {¬ hit i ω}) ∩ {T_J ω ≤ n}.
      subst hjJ
      have hrewrite : {ω | firstHit ω = j ∧ embeddedChainTime G.toTemporalGraph vm Δ j ω ≤ n} =
          (⋂ i ∈ Finset.range j, {ω | ¬ hit i ω ∧ embeddedChainTime G.toTemporalGraph vm Δ j ω ≤ n}) ∩
          {ω | embeddedChainTime G.toTemporalGraph vm Δ j ω ≤ n} := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Finset.mem_range,
          Set.mem_setOf_eq]
        constructor
        · rintro ⟨hfH, hTle⟩
          refine ⟨fun i hi => ⟨?_, hTle⟩, hTle⟩
          rcases (hfH_spec ω j hj).mp hfH with ⟨_, hmin⟩ | ⟨_, hnone⟩
          · exact hmin i hi
          · -- hi : i < j; hj : j < J + 1, so i ∈ Finset.range (J + 1).
            exact hnone i (Finset.mem_range.mpr (lt_trans hi hj))
        · rintro ⟨h_inter, hTle⟩
          refine ⟨?_, hTle⟩
          -- All ¬ hit i ω for i < j = J. So firstHit ω = J = j.
          apply (hfH_spec ω j hj).mpr
          by_cases hhit_j : hit j ω
          · left
            refine ⟨hhit_j, fun i hi => (h_inter i hi).1⟩
          · right
            refine ⟨rfl, ?_⟩
            intro i hi_mem
            rcases Nat.lt_or_ge i j with hlt | hge
            · exact (h_inter i hlt).1
            · -- i ≥ j = J and i ∈ range(J+1) so i = J = j.
              have : i = j := by
                have := Finset.mem_range.mp hi_mem
                omega
              rw [this]; exact hhit_j
      rw [hrewrite]
      refine MeasurableSet.inter ?_ (hT_le_n_meas j)
      refine MeasurableSet.biInter (Finset.range j).countable_toSet (fun i hi => ?_)
      simp only [Finset.mem_coe, Finset.mem_range] at hi
      exact h_nohit_with_Tj i (Nat.le_of_lt hi)
    · -- Case j < J. {firstHit = j} = {hit j ω ∧ ∀ i < j, ¬ hit i ω} (default case excluded since j ≠ J).
      have hj_lt_J : j < J := by omega
      have hrewrite : {ω | firstHit ω = j ∧ embeddedChainTime G.toTemporalGraph vm Δ j ω ≤ n} =
          (⋂ i ∈ Finset.range j,
              {ω | ¬ hit i ω ∧ embeddedChainTime G.toTemporalGraph vm Δ j ω ≤ n}) ∩
          {ω | hit j ω ∧ embeddedChainTime G.toTemporalGraph vm Δ j ω ≤ n} := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Finset.mem_range,
          Set.mem_setOf_eq]
        constructor
        · rintro ⟨hfH, hTle⟩
          rcases (hfH_spec ω j hj).mp hfH with ⟨hh, hmin⟩ | ⟨hjeq, _⟩
          · exact ⟨fun i hi => ⟨hmin i hi, hTle⟩, ⟨hh, hTle⟩⟩
          · exact absurd hjeq hjJ
        · rintro ⟨h_before, ⟨h_at, hTle⟩⟩
          refine ⟨(hfH_spec ω j hj).mpr (Or.inl ⟨h_at, fun i hi => (h_before i hi).1⟩), hTle⟩
      rw [hrewrite]
      refine MeasurableSet.inter ?_ (h_hit_le_meas j n)
      refine MeasurableSet.biInter (Finset.range j).countable_toSet (fun i hi => ?_)
      simp only [Finset.mem_coe, Finset.mem_range] at hi
      exact h_nohit_with_Tj i (Nat.le_of_lt hi)
  -- ── Step 6: apply OST ──────────────────────────────────────────────────────
  have hSuper : Supermartingale (fun t ω => (TemporalGraph.volume G.toTemporalGraph t (vm.S t ω) : ℝ))
      vm.ℱ vm.μ := TemporalGraph.vol_minority_supermartingale vm
  have hOST : ∫ ω, (TemporalGraph.volume G.toTemporalGraph (σ ω) (vm.S (σ ω) ω) : ℝ) ∂vm.μ ≤
      ∫ ω, (TemporalGraph.volume G.toTemporalGraph 0 (vm.S 0 ω) : ℝ) ∂vm.μ :=
    optional_stopping_time_supermartingale_of_bounded_stopping_time
      (μ := vm.μ) (ℱ := vm.ℱ) hSuper hσ_stop hσ_le_K
  -- RHS = c.
  have hRHS : ∫ ω, (TemporalGraph.volume G.toTemporalGraph 0 (vm.S 0 ω) : ℝ) ∂vm.μ = c := by
    have h_eq : ∀ ω, (TemporalGraph.volume G.toTemporalGraph 0 (vm.S 0 ω) : ℝ) = c := fun ω => by
      rw [hs_0 ω]
    simp_rw [h_eq]
    simp
  -- vol(σ ω, S_{σ ω} ω) = vol(0, S_{σ ω} ω) (FixedDegrees).
  have hvol_eq : ∀ ω,
      (TemporalGraph.volume G.toTemporalGraph (σ ω) (vm.S (σ ω) ω) : ℝ) =
      (TemporalGraph.volume G.toTemporalGraph 0 (vm.S (σ ω) ω) : ℝ) := fun ω => by
    have : TemporalGraph.volume G.toTemporalGraph (σ ω) (vm.S (σ ω) ω) =
           TemporalGraph.volume G.toTemporalGraph 0 (vm.S (σ ω) ω) :=
      G.volume_fixed _ _ _
    exact_mod_cast this
  -- A = {∃ j ≤ J, hit j ω}.
  set A : Set Ω := {ω | ∃ j ≤ J,
      8 * c ≤ (TemporalGraph.volume G.toTemporalGraph 0 (vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω) : ℝ)}
      with hA_def
  have hA_meas : MeasurableSet A := by
    have : A = ⋃ j ∈ Finset.range (J + 1), {ω | hit j ω} := by
      ext ω
      simp only [A, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_setOf_eq,
        Finset.mem_range, exists_prop, hit]
      constructor
      · rintro ⟨j, hjJ, hh⟩; exact ⟨j, Nat.lt_succ_of_le hjJ, hh⟩
      · rintro ⟨j, hj, hh⟩; exact ⟨j, Nat.le_of_lt_succ hj, hh⟩
    rw [this]
    exact MeasurableSet.biUnion (Finset.range (J + 1)).countable_toSet (fun j _ =>
      h_hit_meas_global j)
  have h_bound_on_A : ∀ ω, ω ∈ A →
      8 * c ≤ (TemporalGraph.volume G.toTemporalGraph (σ ω) (vm.S (σ ω) ω) : ℝ) := by
    intro ω hω
    rw [hvol_eq ω]
    show 8 * c ≤ (TemporalGraph.volume G.toTemporalGraph 0
      (vm.S (embeddedChainTime G.toTemporalGraph vm Δ (firstHit ω) ω) ω) : ℝ)
    have hex : ∃ j ∈ Finset.range (J + 1), hit j ω := by
      obtain ⟨j, hjJ, hh⟩ := hω
      exact ⟨j, Finset.mem_range.mpr (Nat.lt_succ_of_le hjJ), hh⟩
    have hfH_val := hfH_le_J ω
    rcases (hfH_spec ω (firstHit ω) (Nat.lt_succ_of_le hfH_val)).mp rfl with
      ⟨hh, _⟩ | ⟨_, hnone⟩
    · exact hh
    · obtain ⟨j, hj_mem, hj_hit⟩ := hex
      exact absurd hj_hit (hnone j hj_mem)
  -- Integrability of fun ω => vol(σ ω, S_{σ ω} ω).
  -- Avoid pair-measurability and use decomposition over σ ω = t.
  have hσ_meas : Measurable σ := by
    intro s _
    rw [show σ ⁻¹' s = ⋃ t ∈ s, {ω | σ ω = t} from by ext ω; simp]
    refine MeasurableSet.biUnion (Set.to_countable s) (fun t _ => ?_)
    have h_eq : MeasurableSet[vm.ℱ t] {ω | (σ ω : ℕ∞) = ↑t} := hσ_stop.measurableSet_eq t
    have hcong : {ω | σ ω = t} = {ω | (σ ω : ℕ∞) = ↑t} := by
      ext ω
      exact ⟨fun heq => by exact_mod_cast heq, fun heq => by exact_mod_cast heq⟩
    rw [hcong]
    exact vm.ℱ.le t _ h_eq
  have hf_σ_meas : Measurable
      (fun ω => (TemporalGraph.volume G.toTemporalGraph (σ ω) (vm.S (σ ω) ω) : ℝ)) := by
    -- Decompose by σ ω = t: f σ ω = vol(t, vm.S t ω) when σ ω = t.
    intro S hS
    rw [show (fun ω => (TemporalGraph.volume G.toTemporalGraph (σ ω) (vm.S (σ ω) ω) : ℝ)) ⁻¹' S =
        ⋃ t : ℕ, σ ⁻¹' {t} ∩
          ((fun ω => (TemporalGraph.volume G.toTemporalGraph t (vm.S t ω) : ℝ)) ⁻¹' S) from by
      ext ω
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_singleton_iff]
      constructor
      · intro h; exact ⟨σ ω, rfl, h⟩
      · rintro ⟨t, heq, h⟩; rw [heq]; exact h]
    refine MeasurableSet.iUnion (fun t => ?_)
    have hσ_t : MeasurableSet (σ ⁻¹' {t}) := hσ_meas (measurableSet_singleton _)
    -- vm.S t is ℱ_t-measurable, hence Measurable. vol(t, ·) on Finset V is measurable.
    have h_vol_t : Measurable (fun ω => (TemporalGraph.volume G.toTemporalGraph t (vm.S t ω) : ℝ)) := by
      have hvol_fn : @Measurable (Finset V) ℝ ⊤ _
          (fun s : Finset V => (TemporalGraph.volume G.toTemporalGraph t s : ℝ)) :=
        measurable_of_countable _
      -- vm.S t : Ω → Finset V is Measurable w.r.t. (vm.ℱ t) ≤ mΩ.
      have hS_t : Measurable (vm.S t) := fun S hS => vm.ℱ.le t _ ((hS_meas t) hS)
      exact hvol_fn.comp hS_t
    exact hσ_t.inter (h_vol_t hS)
  have hf_σ_int : Integrable
      (fun ω => (TemporalGraph.volume G.toTemporalGraph (σ ω) (vm.S (σ ω) ω) : ℝ)) vm.μ := by
    refine MeasureTheory.Integrable.of_bound (C := (TemporalGraph.volume G.toTemporalGraph 0 Finset.univ : ℝ))
      hf_σ_meas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun ω => ?_)
    simp only [Real.norm_of_nonneg (by exact_mod_cast Nat.zero_le _ :
      (0 : ℝ) ≤ (TemporalGraph.volume G.toTemporalGraph (σ ω) (vm.S (σ ω) ω) : ℝ))]
    have h_le_univ : TemporalGraph.volume G.toTemporalGraph (σ ω) (vm.S (σ ω) ω) ≤
        TemporalGraph.volume G.toTemporalGraph (σ ω) Finset.univ := by
      unfold TemporalGraph.volume SimpleGraph.volume
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have h_univ_eq : TemporalGraph.volume G.toTemporalGraph (σ ω) Finset.univ =
        TemporalGraph.volume G.toTemporalGraph 0 Finset.univ :=
      G.volume_fixed _ _ _
    exact_mod_cast (h_le_univ.trans_eq h_univ_eq)
  -- ∫_A 8c ≤ ∫ vol(σ ω, S_σ ω) dμ.
  have markovMarginal : 8 * c * ((vm.μ : Measure Ω) A).toReal ≤
      ∫ ω, (TemporalGraph.volume G.toTemporalGraph (σ ω) (vm.S (σ ω) ω) : ℝ) ∂vm.μ := by
    have hindic_le : ∀ ω,
        A.indicator (fun _ => (8 * c : ℝ)) ω ≤
        (TemporalGraph.volume G.toTemporalGraph (σ ω) (vm.S (σ ω) ω) : ℝ) := by
      intro ω
      by_cases hω : ω ∈ A
      · rw [Set.indicator_of_mem hω]
        exact h_bound_on_A ω hω
      · rw [Set.indicator_of_notMem hω]
        exact_mod_cast Nat.zero_le _
    calc 8 * c * ((vm.μ : Measure Ω) A).toReal
        = ∫ ω, A.indicator (fun _ => (8 * c : ℝ)) ω ∂vm.μ := by
          rw [integral_indicator_const _ hA_meas]
          simp [measureReal_def, smul_eq_mul, mul_comm]
      _ ≤ ∫ ω, (TemporalGraph.volume G.toTemporalGraph (σ ω) (vm.S (σ ω) ω) : ℝ) ∂vm.μ :=
          integral_mono
            (Integrable.indicator (integrable_const (8 * c)) hA_meas) hf_σ_int hindic_le
  -- Conclude.
  have h_final : 8 * c * ((vm.μ : Measure Ω) A).toReal ≤ c := by
    calc 8 * c * ((vm.μ : Measure Ω) A).toReal
        ≤ ∫ ω, (TemporalGraph.volume G.toTemporalGraph (σ ω) (vm.S (σ ω) ω) : ℝ) ∂vm.μ := markovMarginal
      _ ≤ ∫ ω, (TemporalGraph.volume G.toTemporalGraph 0 (vm.S 0 ω) : ℝ) ∂vm.μ := hOST
      _ = c := hRHS
  have h8c_pos : 0 < 8 * c := by linarith
  have h_ratio : ((vm.μ : Measure Ω) A).toReal ≤ c / (8 * c) := by
    rw [le_div_iff₀ h8c_pos]; linarith
  have hdiv : c / (8 * c) = 1 / 8 := by field_simp
  linarith [h_ratio.trans_eq hdiv]


end VoterModel
