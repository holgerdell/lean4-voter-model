module

import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import VoterProcess.Absorption.Time
import VoterProcess.Expectation
public import TemporalGraph.Basic
import Mathlib.Algebra.Order.Star.Real
public import TemporalGraph.Conductance

public import TemporalGraph.Degree
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Covering.Besicovitch
import UpperBound.TwoOpinion.ConditionalModel
import UpperBound.TwoOpinion.StoppingBound


@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

namespace VoterModel

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]

/-! ## Main results

Two-opinion upper bound theorems: `voter_absorb_two_opinion`,
`cond_fiber_absorption`, `log_one_add_m_le_m_div_d_min`, `upper_bound`,
`consensus_time_upper_bound`. -/

/-- \label{thm:voter-absorb-two-opinion}

There exists a constant `b > 0` such that the following holds. Let `G` be a temporal
graph with fixed vertex degrees and minimum degree `d_min`. Let `(S_t)` be the
standard two-opinion voter model on `G` with arbitrary deterministic initial
minority set `s_0` (i.e., `vm.S 0 ω = s_0` for every `ω`). Let `Δ_0, Δ_1, … ≥ 1`
be positive integers and `φ_0, φ_1, … ∈ [0,1]` real numbers, and suppose
`φ^{I_j}(G) ≥ φ_j` for every `j ≥ 0`. Let
`J = min{j : φ_0 + … + φ_j ≥ b·(Vol(s_0)/d_min + log(1 + Vol(s_0)))}` (required
to exist). Then with probability at least `1/2`, the consensus time is at most
`I_{J+1}^- = Δ_0 + … + Δ_J`. -/
theorem voter_absorb_two_opinion
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    -- Temporal graph with fixed degrees
    (G : TemporalGraphFixedDegree V)
    -- Voter model process
    (vm : G.VoterModelAbstract 2 Ω)
    -- Minimum degree d_min = G.minDegreeAt 0
    (d_min : ℕ) (hd : d_min = G.minDegreeAt 0) (hd_pos : 0 < d_min)
    -- Deterministic initial minority set s_0
    (s_0 : Finset V) (hs_0 : ∀ ω, vm.S 0 ω = s_0)
    -- Interval lengths Δ_0, Δ_1, … ≥ 1
    (Δ : ℕ → ℕ) (hΔ_pos : ∀ j, 1 ≤ Δ j)
    -- Conductance lower bounds φ_0, φ_1, … ∈ [0, 1]
    (φ : ℕ → ℝ) (hφ_nn : ∀ j, 0 ≤ φ j) (hφ_le1 : ∀ j, φ j ≤ 1)
    -- Hypothesis: per-interval MAX-form window guarantee (paper's
    -- `φ^{I_j}(𝒢) ≥ φ_j`): for each `j` and admissible cut `S`, the
    -- maximum of `(G.snapshot ·).setConductance S` over the calendar interval
    -- `[∑_{k<j} Δ_k, ∑_{k<j} Δ_k + Δ_j - 1]` is at least `φ j`.
    (hwin : ∀ j, ∀ S ∈ G.admissibleCuts,
      φ j ≤ G.maxSetConductanceOnInterval (∑ i ∈ Finset.range j, Δ i) (Δ j) S)
    -- Universal constant b ≥ 5462
    (b : ℝ) (hb_large : (5462 : ℝ) ≤ b)
    (J : ℕ)
    -- Threshold: ∑_{ℓ=0}^{J} φ_ℓ ≥ b·(Vol(s₀)/d_min + log(1+Vol(s₀))).
    -- The log term arises from the χ-component of the Lyapunov function Φ = α·ψ + χ.
    -- Because s₀ varies per fiber, the log cannot be uniformly eliminated here.
    -- The public `upper_bound` theorem absorbs it via `log_one_add_m_le_m_div_d_min`.
    (hJ : b * ((TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) / d_min
              + Real.log (1 + (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ)))
          ≤ ∑ ℓ ∈ Finset.range (J + 1), φ ℓ) :
    -- Conclusion: P(T_abs ≤ I_{J+1}^- = Δ_0 + … + Δ_J) ≥ 1/2
    (1 / 2 : ℝ) ≤ ((vm.μ : Measure Ω)
      {ω | vm.absorptionTime ω ≤ (↑(∑ j ∈ Finset.range (J + 1), Δ j) : ℕ∞)}).toReal := by
  -- Abbreviations
  set K := ∑ j ∈ Finset.range (J + 1), Δ j with hK_def
  -- ── Step 1: Measurability / stopping-time setup ──────────────────────────────
  -- S is measurable w.r.t. ℱ t at each t
  have hS_meas : ∀ t, @Measurable Ω (Finset V) (vm.ℱ t) ⊤ (vm.S t) := fun t =>
    (measurable_of_countable (fun A => VoterModel.minoritySet G.toTemporalGraph t A)).comp
      (vm.A_stronglyAdapted t).measurable
  -- The initial minority set is nonempty iff s_0 ≠ ∅; we work in two cases.
  -- For the non-empty case, we need s_0 nonempty to apply chi_down_drift_voter_unstable.
  -- ── Step 2: Reduction to the case s_0 ≠ ∅ ───────────────────────────────────
  -- If s_0 = ∅ then T_abs = 0 and absorption has already occurred, so the bound is trivial.
  by_cases hs_0_empty : s_0 = ∅
  · -- absorptionTime ≤ 0 ≤ K, so P(absorptionTime ≤ K) = 1 ≥ 1/2
    have huniv : {ω | vm.absorptionTime ω ≤ (K : ℕ∞)} = Set.univ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      -- The minority set is empty at time 0 (since `s_0 = ∅`), so absorption is by time 0 ≤ K.
      refine (vm.absorptionTime_le_coe_iff_exists ω K).mpr ⟨0, Nat.zero_le K, ?_⟩
      have hS0 : vm.S 0 ω = ∅ := by rw [hs_0 ω]; exact hs_0_empty
      exact hS0
    rw [huniv, measure_univ, ENNReal.toReal_one]
    norm_num
  -- ── Step 3: s_0 is nonempty ──────────────────────────────────────────────────
  have hs_0_ne : s_0.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs_0_empty
  -- ── Step 4: T_J ≤ K ──────────────────────────────────────────────────────────
  -- `embeddedChainTime_le_sum_early` directly
  -- gives `T_J ω ≤ ∑ k ∈ range (J+1), Δ k = K`.
  have hT_J_le_K : ∀ ω, embeddedChainTime G.toTemporalGraph vm Δ J ω ≤ K := fun ω =>
    embeddedChainTime_le_sum_early G.toTemporalGraph vm Δ hΔ_pos J ω
  -- ── Step 4.2: Absorption at S_{T_J} = ∅ implies T_abs ≤ T_J ≤ K ──────────
  have hT_abs_le_K : ∀ ω, vm.S (embeddedChainTime G.toTemporalGraph vm Δ J ω) ω = ∅ →
      vm.absorptionTime ω ≤ (K : ℕ∞) := by
    intro ω habs
    -- S_{T_J} = ∅ exhibits an empty minority time ≤ T_J, so absorptionTime ≤ T_J directly
    -- (it is the FIRST hitting time; no permanence needed).
    have hTabs_le : vm.absorptionTime ω ≤ (embeddedChainTime G.toTemporalGraph vm Δ J ω : ℕ∞) :=
      (vm.absorptionTime_le_coe_iff_exists ω (embeddedChainTime G.toTemporalGraph vm Δ J ω)).mpr
        ⟨embeddedChainTime G.toTemporalGraph vm Δ J ω, le_refl _, habs⟩
    exact le_trans hTabs_le (by exact_mod_cast hT_J_le_K ω)
  -- ── Step 5: Two-part probability argument (paper §3.3) ───────────────────────
  -- Let A = {∃ j ≤ J : vol(S_{T_j}) ≥ 8·vol(s_0)} (vol 8-folds in J steps)
  -- Let B = {∀ j ≤ J : vol(S_{T_j}) < 8·vol(s_0)} (vol never 8-folds; complement of A)
  -- Note: A and B partition the sample space, so P(A)+P(B) = 1 always.
  -- We bound: P(A) ≤ 1/8 (Part 1, Doob maximal ineq on vol supermartingale)
  --           P({S_{T_J}≠∅} ∩ B) ≤ 3/8 (Part 2 = L50, Markov on X_J)
  -- Hence {S_{T_J}≠∅} ⊆ A ∪ ({S_{T_J}≠∅}∩B), so
  --   P(S_{T_J}≠∅) ≤ P(A) + P({S_{T_J}≠∅}∩B) ≤ 1/8 + 3/8 = 1/2.
  --
  -- Part 1: vol(S_{T_j}) is a supermartingale at embedded times (from
  -- vol_minority_supermartingale + OST), so by Doob's maximal inequality:
  --   P(∃j≤J: vol(S_{T_j}) ≥ 8·vol(s_0)) ≤ E[vol(S_{T_0})] / (8·vol(s_0)) = 1/8.
  -- (Deferred: requires optional stopping for supermartingales at embedded times.)
  have h_vol8fold : ((vm.μ : Measure Ω) {ω | ∃ j ≤ J,
      8 * (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) ≤
      (TemporalGraph.volume G.toTemporalGraph 0 (vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω) : ℝ)}).toReal ≤
      1 / 8 :=
    vol8fold_bound G vm d_min hd hd_pos s_0 hs_0_ne hs_0 Δ hΔ_pos J
  -- Part 2: P(not absorbed AND vol never 8-folds in J steps) ≤ 3/8 (L50).
  have h_no8fold : ((vm.μ : Measure Ω) {ω | vm.S (embeddedChainTime G.toTemporalGraph vm Δ J ω) ω ≠ ∅ ∧
      ∀ j ≤ J,
      (TemporalGraph.volume G.toTemporalGraph 0 (vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω) : ℝ) <
      8 * (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ)}).toReal ≤ 3 / 8 :=
    combined_potential_dj_bound G vm d_min hd hd_pos s_0 hs_0_ne hs_0
      Δ hΔ_pos φ hφ_nn hφ_le1 hwin b hb_large J hJ
  -- Union bound: P(S_{T_J} = ∅) ≥ 1/2.
  -- {S_{T_J} ≠ ∅} ⊆ A ∪ ({S_{T_J}≠∅}∩B), so P(S_{T_J}≠∅) ≤ P(A)+P({S_{T_J}≠∅}∩B) ≤ 1/2.
  have h_abs_prob : (1 / 2 : ℝ) ≤
      ((vm.μ : Measure Ω) {ω | vm.S (embeddedChainTime G.toTemporalGraph vm Δ J ω) ω = ∅}).toReal := by
    haveI hprob : IsProbabilityMeasure (vm.μ : Measure Ω) := inferInstance
    set A := {ω : Ω | ∃ j ≤ J, 8 * (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) ≤
        (TemporalGraph.volume G.toTemporalGraph 0 (vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω) : ℝ)}
    set B := {ω : Ω | ∀ j ≤ J, (TemporalGraph.volume G.toTemporalGraph 0 (vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω) : ℝ) <
        8 * (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ)}
    set C := {ω : Ω | vm.S (embeddedChainTime G.toTemporalGraph vm Δ J ω) ω ≠ ∅ ∧
        ∀ j ≤ J, (TemporalGraph.volume G.toTemporalGraph 0 (vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω) : ℝ) <
        8 * (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ)}
    -- Measurability of {S_{T_J} = ∅} via stopping-time decomposition
    have h_setOf_meas : MeasurableSet {ω : Ω | vm.S (embeddedChainTime G.toTemporalGraph vm Δ J ω) ω = ∅} := by
      have hT_meas : Measurable (embeddedChainTime G.toTemporalGraph vm Δ J) := by
        intro s _
        rw [show (embeddedChainTime G.toTemporalGraph vm Δ J) ⁻¹' s = ⋃ t ∈ s, {w | embeddedChainTime G.toTemporalGraph vm Δ J w = t}
            from by ext ω; simp]
        apply MeasurableSet.biUnion (Set.to_countable s); intro t _
        rw [show {w : Ω | embeddedChainTime G.toTemporalGraph vm Δ J w = t} =
            {w | (embeddedChainTime G.toTemporalGraph vm Δ J w : ℕ∞) = ↑t} from by ext w; simp [Nat.cast_inj]]
        exact vm.ℱ.le t _ (embeddedChainTime_isStoppingTime G.toTemporalGraph vm Δ hS_meas J |>.measurableSet_eq t)
      have h_S_TJ_meas : Measurable (fun ω => vm.S (embeddedChainTime G.toTemporalGraph vm Δ J ω) ω) := by
        intro S hS
        rw [show (fun ω => vm.S (embeddedChainTime G.toTemporalGraph vm Δ J ω) ω) ⁻¹' S =
            ⋃ t : ℕ, (embeddedChainTime G.toTemporalGraph vm Δ J) ⁻¹' {t} ∩ (vm.S t) ⁻¹' S
            from by ext ω; simp [eq_comm]]
        apply MeasurableSet.iUnion; intro t
        exact (hT_meas (measurableSet_singleton _)).inter (vm.ℱ.le t _ (hS_meas t hS))
      exact h_S_TJ_meas (measurableSet_singleton _)
    -- {S_{T_J}≠∅} ⊆ A ∪ C (since B = Aᶜ and C = {S≠∅}∩B)
    have hne_sub : {ω : Ω | vm.S (embeddedChainTime G.toTemporalGraph vm Δ J ω) ω ≠ ∅} ⊆ A ∪ C := by
      intro ω hω
      by_cases hA : ∃ j ≤ J, 8 * (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) ≤
          (TemporalGraph.volume G.toTemporalGraph 0 (vm.S (embeddedChainTime G.toTemporalGraph vm Δ j ω) ω) : ℝ)
      · exact Or.inl hA
      · exact Or.inr ⟨hω, by push Not at hA; exact hA⟩
    -- P({S≠∅}) ≤ P(A) + P(C) by subset + union bound
    have h_ne_le : ((vm.μ : Measure Ω) {ω | vm.S (embeddedChainTime G.toTemporalGraph vm Δ J ω) ω ≠ ∅}) ≤ (vm.μ : Measure Ω) A + (vm.μ : Measure Ω) C :=
      (measure_mono hne_sub).trans (measure_union_le A C)
    -- P({S≠∅}).toReal ≤ 3/8
    have h_ne_le_real : ((vm.μ : Measure Ω) {ω | vm.S (embeddedChainTime G.toTemporalGraph vm Δ J ω) ω ≠ ∅}).toReal ≤ 1 / 2 :=
      calc ((vm.μ : Measure Ω) {ω | vm.S (embeddedChainTime G.toTemporalGraph vm Δ J ω) ω ≠ ∅}).toReal
          ≤ ((vm.μ : Measure Ω) A + (vm.μ : Measure Ω) C).toReal := ENNReal.toReal_mono (by finiteness) h_ne_le
        _ = ((vm.μ : Measure Ω) A).toReal + ((vm.μ : Measure Ω) C).toReal :=
            ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)
        _ ≤ 1 / 2 := by linarith
    -- P({S=∅}) + P({S≠∅}) = 1 (probability space)
    have h_compl_real : ((vm.μ : Measure Ω) {ω | vm.S (embeddedChainTime G.toTemporalGraph vm Δ J ω) ω = ∅}).toReal +
        ((vm.μ : Measure Ω) {ω | vm.S (embeddedChainTime G.toTemporalGraph vm Δ J ω) ω ≠ ∅}).toReal = 1 := by
      have h1 := congr_arg ENNReal.toReal
        (prob_add_prob_compl (μ := vm.μ)
          (s := {ω | vm.S (embeddedChainTime G.toTemporalGraph vm Δ J ω) ω = ∅}) h_setOf_meas)
      rwa [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), ENNReal.toReal_one] at h1
    linarith
  -- ── Step 6: Convert absorption event to absorptionTime ≤ K ────────────────────────
  have h_subset : {ω | vm.S (embeddedChainTime G.toTemporalGraph vm Δ J ω) ω = ∅} ⊆
      {ω | vm.absorptionTime ω ≤ (K : ℕ∞)} := fun ω hω => hT_abs_le_K ω hω
  calc (1 / 2 : ℝ)
      ≤ ((vm.μ : Measure Ω) {ω | vm.S (embeddedChainTime G.toTemporalGraph vm Δ J ω) ω = ∅}).toReal := h_abs_prob
    _ ≤ ((vm.μ : Measure Ω) {ω | vm.absorptionTime ω ≤ (K : ℕ∞)}).toReal :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono h_subset)

/-- **Conditional absorption over a single fiber.**

For each initial opinion set `σ₀ : Finset V`, the probability of absorption
by time `K = ∑ j ∈ range (J+1) Δ j`, restricted to outcomes that start in
`σ₀`, is at least `(1/2) · (vm.μ : Measure Ω) {A₀ = σ₀}`.

The proof constructs the conditional `TemporalGraph.VoterModelAbstract` on the
subtype `{ω | vm.opinionZeroSet 0 ω = σ₀}` (whose measure is the normalised restriction
of `vm.μ` to `{A₀ = σ₀}`) and applies `voter_absorb_two_opinion` (T23).
The conditional VoterModel's `markovMarginal` and `markovProperty` fields are derived
by induction from `vm.A_markovProperty`; this derivation is deferred.
-/
private theorem cond_fiber_absorption
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (G : TemporalGraphFixedDegree V)
    (vm : G.VoterModelAbstract 2 Ω)
    (d_min : ℕ) (hd : d_min = G.minDegreeAt 0) (hd_pos : 0 < d_min)
    (Δ : ℕ → ℕ) (hΔ_pos : ∀ j, 1 ≤ Δ j)
    (φ : ℕ → ℝ) (hφ_nn : ∀ j, 0 ≤ φ j) (hφ_le1 : ∀ j, φ j ≤ 1)
    -- Window-guarantee hypothesis (per-interval MAX-form, paper's
    -- `φ^{I_j}(𝒢) ≥ φ_j`).
    (hwin : ∀ j, ∀ S ∈ G.admissibleCuts,
      φ j ≤ G.maxSetConductanceOnInterval (∑ i ∈ Finset.range j, Δ i) (Δ j) S)
    (b : ℝ) (hb : 0 < b) (hb_large : (5462 : ℝ) ≤ b)
    (J : ℕ)
    -- Threshold: b·(m/d_min + log(1+m)) ≤ ∑_{ℓ=0}^{J} φ_ℓ.
    -- Here m = |E| = (G.snapshot 0).edgeFinset.card. The log term is required at this level.
    -- The public `upper_bound` passes b/2 for b here (requiring b ≥ 10924), since
    -- log(1+m) ≤ (49/50)·m/d_min implies (b/2)·(m/d_min + log(1+m)) ≤ b·(m/d_min).
    (hsum : b * ((G.snapshot 0).edgeFinset.card / (d_min : ℝ) +
        Real.log (1 + (G.snapshot 0).edgeFinset.card)) ≤ ∑ ℓ ∈ Finset.range (J + 1), φ ℓ)
    (σ₀ : Finset V) :
    -- Conclusion: (vm.μ : Measure Ω) ({A₀=σ₀} ∩ {T_abs ≤ K}) ≥ (1/2) · (vm.μ : Measure Ω) {A₀=σ₀}  (in ℝ)
    (1 / 2 : ℝ) * ((vm.μ : Measure Ω) {ω | vm.opinionZeroSet 0 ω = σ₀}).toReal ≤
      ((vm.μ : Measure Ω) ({ω | vm.opinionZeroSet 0 ω = σ₀} ∩
        {ω | vm.absorptionTime ω ≤ (↑(∑ j ∈ Finset.range (J + 1), Δ j) : ℕ∞)})).toReal :=
  by
  -- Step 1: Case split on μ{A 0 = σ₀} = 0.
  by_cases hpos : (vm.μ : Measure Ω) {ω | vm.opinionZeroSet 0 ω = σ₀} = 0
  · simp only [hpos, ENNReal.toReal_zero, mul_zero]; positivity
  -- Step 2: Abbreviate the event E = {A 0 = σ₀}.
  set E := {ω : Ω | vm.opinionZeroSet 0 ω = σ₀} with hE_def
  -- Step 3: Construct the conditional VoterModel on the subtype ↥E.
  let vm' := conditionalVoterModel G.toTemporalGraph vm σ₀ hpos
  -- Step 4: The initial minority set is deterministic:
  --   vm'.S 0 ω' = minoritySet G.toTemporalGraph 0 σ₀  for all ω'.
  set s_0 := VoterModel.minoritySet G.toTemporalGraph 0 σ₀
  have hS0 : ∀ ω' : ↥E, vm'.S 0 ω' = s_0 := by
    intro ω'
    show VoterModel.minoritySet G.toTemporalGraph 0 (vm'.opinionZeroSet 0 ω') = VoterModel.minoritySet G.toTemporalGraph 0 σ₀
    rw [show vm'.opinionZeroSet 0 ω' = vm.opinionZeroSet 0 ω'.val from conditionalVoterModel_A G.toTemporalGraph vm σ₀ hpos 0 ω']
    congr 1; exact ω'.property
  -- Step 5: Establish the volume bound vol(s_0) ≤ (G.snapshot 0).edgeFinset.card.
  -- volume G.toTemporalGraph 0 Finset.univ = ∑ v, (G.snapshot 0).degree v = 2·|edgeFinset|
  have hvol_univ : TemporalGraph.volume G.toTemporalGraph 0 Finset.univ = 2 * (G.snapshot 0).edgeFinset.card := by
    show (G.snapshot 0).volume Finset.univ = 2 * (G.snapshot 0).edgeFinset.card
    simp only [SimpleGraph.volume]
    exact (G.snapshot 0).sum_degrees_eq_twice_card_edges
  have hvol_s0_le : TemporalGraph.volume G.toTemporalGraph 0 s_0 ≤ (G.snapshot 0).edgeFinset.card := by
    -- 2·vol(s_0) ≤ vol(univ) = 2·|edgeFinset|, so vol(s_0) ≤ |edgeFinset|
    have hvol_add : TemporalGraph.volume G.toTemporalGraph 0 σ₀ +
        TemporalGraph.volume G.toTemporalGraph 0 (Finset.univ \ σ₀) = TemporalGraph.volume G.toTemporalGraph 0 Finset.univ := by
      simp only [TemporalGraph.volume, SimpleGraph.volume]
      rw [← Finset.sum_union Finset.sdiff_disjoint.symm]; congr 1; ext x; simp
    have h2le : 2 * TemporalGraph.volume G.toTemporalGraph 0 s_0 ≤ TemporalGraph.volume G.toTemporalGraph 0 Finset.univ := by
      show 2 * TemporalGraph.volume G.toTemporalGraph 0 (VoterModel.minoritySet G.toTemporalGraph 0 σ₀) ≤
          TemporalGraph.volume G.toTemporalGraph 0 Finset.univ
      unfold VoterModel.minoritySet
      split_ifs with h
      · omega
      · push Not at h; omega
    linarith [hvol_univ ▸ h2le]
  -- Step 6: The hypothesis hsum implies T23's hJ (with s_0 in place of edgeFinset.card).
  have hd_min_pos_real : (0 : ℝ) < (d_min : ℝ) := by exact_mod_cast hd_pos
  have hvol_le_real : (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) ≤ (G.snapshot 0).edgeFinset.card := by
    exact_mod_cast hvol_s0_le
  have hJ_vol : b * ((TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) / d_min +
      Real.log (1 + (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ)))
      ≤ ∑ ℓ ∈ Finset.range (J + 1), φ ℓ := by
    calc b * ((TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ) / d_min +
            Real.log (1 + (TemporalGraph.volume G.toTemporalGraph 0 s_0 : ℝ)))
        ≤ b * ((G.snapshot 0).edgeFinset.card / (d_min : ℝ) +
            Real.log (1 + (G.snapshot 0).edgeFinset.card)) := by
          apply mul_le_mul_of_nonneg_left _ hb.le
          apply add_le_add
          · exact div_le_div_of_nonneg_right hvol_le_real hd_min_pos_real.le
          · gcongr
      _ ≤ ∑ ℓ ∈ Finset.range (J + 1), φ ℓ := hsum
  -- Step 7: Apply voter_absorb_two_opinion (T23) directly with J_star := J.
  -- (The original Nat.find minimization was used only for the now-removed `hJ_min`
  -- field; with that field gone, we use J directly.)
  have h12 : (1 / 2 : ℝ) ≤ ((vm'.μ : Measure _) {ω' | vm'.absorptionTime ω' ≤
      (↑(∑ j ∈ Finset.range (J + 1), Δ j) : ℕ∞)}).toReal :=
    voter_absorb_two_opinion G vm' d_min hd hd_pos
      s_0 hS0 Δ hΔ_pos φ hφ_nn hφ_le1 hwin b hb_large J hJ_vol
  -- Step 11: Combine via conditionalVoterModel_compat.
  set K := ∑ j ∈ Finset.range (J + 1), Δ j
  have hcompat : ((vm.μ : Measure Ω) E).toReal *
      ((vm'.μ : Measure _) {ω' : ↥E | vm'.absorptionTime ω' ≤ (↑K : ℕ∞)}).toReal =
      ((vm.μ : Measure Ω) (E ∩ {ω | vm.absorptionTime ω ≤ (↑K : ℕ∞)})).toReal :=
    conditionalVoterModel_compat G.toTemporalGraph vm σ₀ hpos K
  -- Final: chain the inequalities.
  calc (1 / 2 : ℝ) * ((vm.μ : Measure Ω) E).toReal
      ≤ ((vm'.μ : Measure _) {ω' | vm'.absorptionTime ω' ≤ (↑K : ℕ∞)}).toReal *
          ((vm.μ : Measure Ω) E).toReal := by
          apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
          exact h12
    _ = ((vm.μ : Measure Ω) (E ∩ {ω | vm.absorptionTime ω ≤ (↑K : ℕ∞)})).toReal := by
          rw [mul_comm]; exact hcompat


/-- Sharp variant of `log_one_add_m_le_two_m_div_d_min`:
`log(1 + m) ≤ (49/50) · (m / d_min)`.

Proof chain: let `n = |V|`. Edge count gives `m ≤ n.choose 2 ≤ n(n−1)/2`.
The key inequality `1 + n(n−1)/2 ≤ exp((49/100)·n)` holds for all `n ≥ 1`:
Taylor partial sums (`Real.sum_le_exp_of_nonneg`) for `n ≤ 5`, then induction
using `149/100 ≤ exp(49/100)` and
`(149/100)·(1 + n(n−1)/2) ≥ 1 + (n+1)n/2` for `n ≥ 5`.
Hence `log(1+m) ≤ (49/100)·n`, and the handshake `n·d_min ≤ 2m` gives
`(49/100)·n ≤ (49/50)·(m/d_min)`. -/
lemma log_one_add_m_le_m_div_d_min
    (G : TemporalGraphFixedDegree V)
    (d_min : ℕ) (hd : d_min = G.minDegreeAt 0) (hd_pos : 0 < d_min) :
    Real.log (1 + (G.numEdges : ℝ)) ≤ 49 / 50 * ((G.numEdges : ℝ) / (d_min : ℝ)) := by
  set m : ℕ := G.numEdges
  have hm : m = (G.snapshot 0).edgeFinset.card := rfl
  set nV := Fintype.card V with hnV_def
  have hnV_pos : 0 < nV := Fintype.card_pos
  have hd_pos_real : (0 : ℝ) < (d_min : ℝ) := Nat.cast_pos.mpr hd_pos
  -- m ≤ nV.choose 2
  have hedge : m ≤ nV.choose 2 := by
    rw [hm]; exact (G.snapshot 0).card_edgeFinset_le_card_choose_two
  -- 2 * m ≤ nV * (nV - 1) in ℝ
  have hm_le : 2 * (m : ℝ) ≤ (nV : ℝ) * ((nV : ℝ) - 1) := by
    have h2 : 2 * nV.choose 2 ≤ nV * (nV - 1) := by
      rw [Nat.choose_two_right, Nat.mul_comm 2 (nV * (nV - 1) / 2)]
      exact Nat.div_mul_le_self _ 2
    have h2m : 2 * m ≤ nV * (nV - 1) := le_trans (Nat.mul_le_mul_left 2 hedge) h2
    calc 2 * (m : ℝ) = ((2 * m : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((nV * (nV - 1) : ℕ) : ℝ) := Nat.cast_le.mpr h2m
      _ = (nV : ℝ) * ((nV : ℝ) - 1) := by
          rw [Nat.cast_mul, Nat.cast_sub hnV_pos, Nat.cast_one]
  -- nV * d_min ≤ 2 * m  (handshake)
  have hhandshake : nV * d_min ≤ 2 * m := by
    have hsum := (G.snapshot 0).sum_degrees_eq_twice_card_edges
    have hle : nV * G.minDegreeAt 0 ≤ ∑ v : V, (G.snapshot 0).degree v := by
      calc nV * G.minDegreeAt 0
          = ∑ _v : V, G.minDegreeAt 0 := by
              rw [Finset.sum_const_nat (fun _ _ => rfl), Finset.card_univ, ← hnV_def]
        _ ≤ ∑ v : V, (G.snapshot 0).degree v :=
              Finset.sum_le_sum (fun v _ => G.toTemporalGraph.minDegreeAt_le_degree 0 v)
    have h : nV * G.minDegreeAt 0 ≤ 2 * (G.snapshot 0).edgeFinset.card := by rw [← hsum]; exact hle
    rw [hm, hd]; exact h
  -- Key inequality: 1 + n(n−1)/2 ≤ exp((49/100)·n) for n ≥ 1.
  have hexp49 : (149 / 100 : ℝ) ≤ Real.exp (49 / 100) := by
    have h := Real.add_one_le_exp (49 / 100 : ℝ)
    linarith
  have hkey5 : ∀ n : ℕ, 5 ≤ n →
      (1 : ℝ) + (n : ℝ) * ((n : ℝ) - 1) / 2 ≤ Real.exp (49 / 100 * (n : ℝ)) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      -- n = 5: 1 + 10 = 11 ≤ ∑_{i<8} (49/20)^i/i! ≤ exp(49/20).
      refine le_trans ?_ (Real.sum_le_exp_of_nonneg (by norm_num) 8)
      norm_num [Finset.sum_range_succ, Nat.factorial]
    | succ k hk ih =>
      have hk5 : (5 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hstep : (1 : ℝ) + ((k : ℝ) + 1) * (((k : ℝ) + 1) - 1) / 2 ≤
          (1 + (k : ℝ) * ((k : ℝ) - 1) / 2) * (149 / 100) := by
        nlinarith [sq_nonneg ((k : ℝ) - 5)]
      calc (1 : ℝ) + ((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) - 1) / 2
          = 1 + ((k : ℝ) + 1) * (((k : ℝ) + 1) - 1) / 2 := by push_cast; ring
        _ ≤ (1 + (k : ℝ) * ((k : ℝ) - 1) / 2) * (149 / 100) := hstep
        _ ≤ Real.exp (49 / 100 * (k : ℝ)) * (149 / 100) :=
            mul_le_mul_of_nonneg_right ih (by norm_num)
        _ ≤ Real.exp (49 / 100 * (k : ℝ)) * Real.exp (49 / 100) :=
            mul_le_mul_of_nonneg_left hexp49 (Real.exp_pos _).le
        _ = Real.exp (49 / 100 * ((k + 1 : ℕ) : ℝ)) := by
            rw [← Real.exp_add]; push_cast; ring_nf
  have hkey : ∀ n : ℕ, 1 ≤ n →
      (1 : ℝ) + (n : ℝ) * ((n : ℝ) - 1) / 2 ≤ Real.exp (49 / 100 * (n : ℝ)) := by
    intro n hn
    rcases Nat.lt_or_ge n 5 with h5 | h5
    · interval_cases n
      · -- n = 1: LHS = 1 ≤ ∑_{i<1} = 1 ≤ exp(49/100).
        refine le_trans ?_ (Real.sum_le_exp_of_nonneg (by norm_num) 1)
        norm_num
      · -- n = 2: LHS = 2 ≤ ∑_{i<3} (49/50)^i/i! ≈ 2.46.
        refine le_trans ?_ (Real.sum_le_exp_of_nonneg (by norm_num) 3)
        norm_num [Finset.sum_range_succ, Nat.factorial]
      · -- n = 3: LHS = 4 ≤ ∑_{i<5} (147/100)^i/i! ≈ 4.27.
        refine le_trans ?_ (Real.sum_le_exp_of_nonneg (by norm_num) 5)
        norm_num [Finset.sum_range_succ, Nat.factorial]
      · -- n = 4: LHS = 7 ≤ ∑_{i<8} (49/25)^i/i! ≈ 7.09.
        refine le_trans ?_ (Real.sum_le_exp_of_nonneg (by norm_num) 8)
        norm_num [Finset.sum_range_succ, Nat.factorial]
    · exact hkey5 n h5
  -- 1 + m ≤ exp((49/100)·nV)
  have hexp_bound : 1 + (m : ℝ) ≤ Real.exp (49 / 100 * (nV : ℝ)) := by
    have h := hkey nV hnV_pos
    linarith
  -- log(1 + m) ≤ (49/100)·nV
  have hlog_le_n : Real.log (1 + (m : ℝ)) ≤ 49 / 100 * (nV : ℝ) :=
    calc Real.log (1 + (m : ℝ))
        ≤ Real.log (Real.exp (49 / 100 * (nV : ℝ))) :=
          Real.log_le_log (by positivity) hexp_bound
      _ = 49 / 100 * (nV : ℝ) := Real.log_exp _
  -- nV ≤ 2·m/d_min  (from handshake), so (49/100)·nV ≤ (49/50)·(m/d_min).
  have hn_le : (nV : ℝ) ≤ 2 * (m : ℝ) / (d_min : ℝ) := by
    rw [le_div_iff₀ hd_pos_real]; exact_mod_cast hhandshake
  have h_scale : 49 / 100 * (nV : ℝ) ≤ 49 / 50 * ((m : ℝ) / (d_min : ℝ)) := by
    have := mul_le_mul_of_nonneg_left hn_le (by norm_num : (0 : ℝ) ≤ 49 / 100)
    calc 49 / 100 * (nV : ℝ) ≤ 49 / 100 * (2 * (m : ℝ) / (d_min : ℝ)) := this
      _ = 49 / 50 * ((m : ℝ) / (d_min : ℝ)) := by ring
  linarith

/-- Two-opinion specialization of the §3.4 upper bound (proved engine lemma; no paper
label — the paper's `thm:upper-bound-window-conductance` is the general `TemporalGraph.upper_bound_window_conductance`).

There exists a constant `b > 0` such that the following holds. Let `G` be a temporal graph
with fixed vertex degrees, `m` edges, and minimum degree `d_min`. Let `(S_t)` be the
standard two-opinion voter model on `G` with arbitrary initial state. Let
`Δ_0, Δ_1, … ≥ 1` be positive integers and `φ_0, φ_1, … ∈ [0,1]` real numbers. For
all `j ≥ 0`, let `I_j^- = Δ_0 + ⋯ + Δ_{j-1}`, `I_j^+ = I_j^- + Δ_j - 1`, and let
`I_j = [I_j^-, I_j^+]`. Suppose that `φ^{I_j}(G) ≥ φ_j` for all `j ≥ 0`. Let
`J = min{j : φ_0 + ⋯ + φ_j ≥ b·(m/d_min)}` (required to exist). Then with
probability at least `1/2`, the consensus time is at most `Δ_0 + ⋯ + Δ_J`.

The threshold `b·(m/d_min)` matches the introduction. Internally the proof uses `b/2`
when calling `cond_fiber_absorption` (which requires `b·(m/d_min + log(1+m))`),
justified by `log(1+m) ≤ (49/50)·(m/d_min)` (see `log_one_add_m_le_m_div_d_min`). -/
theorem upper_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    -- Temporal graph with fixed degrees
    (G : TemporalGraphFixedDegree V)
    -- Voter model process
    (vm : G.VoterModelAbstract 2 Ω)
    -- Minimum degree d_min = G.minDegreeAt 0
    (d_min : ℕ) (hd : d_min = G.minDegreeAt 0) (hd_pos : 0 < d_min)
    -- Interval lengths Δ_0, Δ_1, … ≥ 1
    (Δ : ℕ → ℕ) (hΔ_pos : ∀ j, 1 ≤ Δ j)
    -- Conductance lower bounds φ_0, φ_1, … ∈ [0, 1]
    (φ : ℕ → ℝ) (hφ_nn : ∀ j, 0 ≤ φ j) (hφ_le1 : ∀ j, φ j ≤ 1)
    -- Hypothesis: per-interval MAX-form window guarantee (paper's
    -- `φ^{I_j}(𝒢) ≥ φ_j`): for each `j` and admissible cut `S`, the
    -- maximum of `(G.snapshot ·).setConductance S` over the calendar interval
    -- `[∑_{k<j} Δ_k, ∑_{k<j} Δ_k + Δ_j - 1]` is at least `φ j`.
    (hwin : ∀ j, ∀ S ∈ G.admissibleCuts,
      φ j ≤ G.maxSetConductanceOnInterval (∑ i ∈ Finset.range j, Δ i) (Δ j) S)
    -- J is the index where the cumulative conductance sum first reaches b·(m/d_min).
    -- (exists by assumption; b is the universal constant, b ≥ 10924)
    (b : ℝ) (hb_large : (10924 : ℝ) ≤ b)
    (J : ℕ)
    -- φ_0 + … + φ_J ≥ b·(m/d_min). Matching the introduction.
    (hJ : b * ((G.numEdges : ℝ) / d_min) ≤ ∑ ℓ ∈ Finset.range (J + 1), φ ℓ) :
    -- Conclusion: P(T_abs ≤ Δ_0 + … + Δ_J) ≥ 1/2
    (1 / 2 : ℝ) ≤ ((vm.μ : Measure Ω)
      {ω | vm.absorptionTime ω ≤ (↑(∑ j ∈ Finset.range (J + 1), Δ j) : ℕ∞)}).toReal := by
  set m : ℕ := G.numEdges
  have hm : m = (G.snapshot 0).edgeFinset.card := rfl
  -- Abbreviations
  set K := ∑ j ∈ Finset.range (J + 1), Δ j with hK_def
  -- Step 0: derive (b/2)·(edgeFinset.card/d_min + log(1+edgeFinset.card)) ≤ ∑φ.
  -- log(1+m) ≤ (49/50)·(m/d_min) ≤ m/d_min, so m/d_min + log(1+m) ≤ 2·(m/d_min),
  -- hence (b/2)·(m/d_min + log(1+m)) ≤ b·(m/d_min) ≤ ∑φ.
  have hlog_le : Real.log (1 + (m : ℝ)) ≤ 49 / 50 * ((m : ℝ) / (d_min : ℝ)) :=
    log_one_add_m_le_m_div_d_min G d_min hd hd_pos
  have hd_pos_real : (0 : ℝ) < (d_min : ℝ) := Nat.cast_pos.mpr hd_pos
  have hb2_pos : (0 : ℝ) < b / 2 := by linarith
  have hb2_large : (5462 : ℝ) ≤ b / 2 := by linarith
  have hJ' : b / 2 * ((G.snapshot 0).edgeFinset.card / (d_min : ℝ) +
      Real.log (1 + (G.snapshot 0).edgeFinset.card)) ≤ ∑ ℓ ∈ Finset.range (J + 1), φ ℓ := by
    have heq : (m : ℝ) = (G.snapshot 0).edgeFinset.card := by exact_mod_cast hm
    have hmd_nn : (0 : ℝ) ≤ (m : ℝ) / (d_min : ℝ) :=
      div_nonneg (Nat.cast_nonneg _) hd_pos_real.le
    have hle : (m : ℝ) / d_min + Real.log (1 + (m : ℝ)) ≤ 2 * ((m : ℝ) / d_min) := by
      linarith
    calc b / 2 * ((G.snapshot 0).edgeFinset.card / (d_min : ℝ) +
            Real.log (1 + (G.snapshot 0).edgeFinset.card))
        = b / 2 * ((m : ℝ) / d_min + Real.log (1 + (m : ℝ))) := by rw [heq]
      _ ≤ b / 2 * (2 * ((m : ℝ) / d_min)) :=
            mul_le_mul_of_nonneg_left hle (by linarith)
      _ = b * ((m : ℝ) / d_min) := by ring
      _ ≤ ∑ ℓ ∈ Finset.range (J + 1), φ ℓ := hJ
  -- Step 1: Partition {T_abs ≤ K} by fibers {A 0 = σ₀}.
  have hA0_meas : ∀ σ₀ : Finset V,
      MeasurableSet {ω | vm.opinionZeroSet 0 ω = σ₀} := fun σ₀ =>
    vm.A_meas 0 _ ⟨{σ₀}, trivial, by ext; simp⟩
  have hT_meas : MeasurableSet {ω | vm.absorptionTime ω ≤ (K : ℕ∞)} :=
    vm.absorptionTime_measurable (t := {x : ℕ∞ | x ≤ (K : ℕ∞)}) MeasurableSet.of_discrete
  have hdisjoint : Pairwise (fun σ₁ σ₂ : Finset V =>
      Disjoint ({ω | vm.opinionZeroSet 0 ω = σ₁} ∩ {ω | vm.absorptionTime ω ≤ (K : ℕ∞)} : Set Ω)
               ({ω | vm.opinionZeroSet 0 ω = σ₂} ∩ {ω | vm.absorptionTime ω ≤ (K : ℕ∞)})) := by
    intro σ₁ σ₂ hne
    rw [Set.disjoint_left]
    intro ω ⟨h1, _⟩ ⟨h2, _⟩
    exact hne (h1.symm.trans h2)
  have hmeas_fiber : ∀ σ₀ : Finset V,
      MeasurableSet ({ω | vm.opinionZeroSet 0 ω = σ₀} ∩ {ω | vm.absorptionTime ω ≤ (K : ℕ∞)}) :=
    fun σ₀ => (hA0_meas σ₀).inter hT_meas
  have hunion : {ω | vm.absorptionTime ω ≤ (K : ℕ∞)} =
      ⋃ σ₀ : Finset V, ({ω | vm.opinionZeroSet 0 ω = σ₀} ∩ {ω | vm.absorptionTime ω ≤ (K : ℕ∞)}) := by
    ext ω; simp
  have hmeasure_sum : (vm.μ : Measure Ω) {ω | vm.absorptionTime ω ≤ (K : ℕ∞)} =
      ∑ σ₀ : Finset V, (vm.μ : Measure Ω) ({ω | vm.opinionZeroSet 0 ω = σ₀} ∩ {ω | vm.absorptionTime ω ≤ (K : ℕ∞)}) := by
    conv_lhs => rw [hunion]
    rw [measure_iUnion (fun i j h => hdisjoint h) hmeas_fiber, tsum_fintype]
  -- Step 2: Per-fiber bound from cond_fiber_absorption.
  have hfiber_bound : ∀ σ₀ : Finset V,
      (1 / 2 : ℝ) * ((vm.μ : Measure Ω) {ω | vm.opinionZeroSet 0 ω = σ₀}).toReal ≤
        ((vm.μ : Measure Ω) ({ω | vm.opinionZeroSet 0 ω = σ₀} ∩ {ω | vm.absorptionTime ω ≤ (K : ℕ∞)})).toReal := by
    intro σ₀
    exact cond_fiber_absorption G vm d_min hd hd_pos Δ hΔ_pos φ hφ_nn hφ_le1
      hwin (b / 2) hb2_pos hb2_large J hJ' σ₀
  -- Step 3: Convert measure sum to toReal sum.
  have htoReal_sum : ((vm.μ : Measure Ω) {ω | vm.absorptionTime ω ≤ (K : ℕ∞)}).toReal =
      ∑ σ₀ : Finset V, ((vm.μ : Measure Ω) ({ω | vm.opinionZeroSet 0 ω = σ₀} ∩ {ω | vm.absorptionTime ω ≤ (K : ℕ∞)})).toReal := by
    rw [hmeasure_sum, ENNReal.toReal_sum (fun σ₀ _ => measure_ne_top (vm.μ : Measure Ω) _)]
  -- Step 4: ∑ σ₀, vm.μ{A₀=σ₀}.toReal = 1.
  have hfibers_univ : ∑ σ₀ : Finset V, ((vm.μ : Measure Ω) {ω | vm.opinionZeroSet 0 ω = σ₀}).toReal = 1 := by
    have hpartition2 : (Set.univ : Set Ω) =
        ⋃ σ₀ : Finset V, {ω | vm.opinionZeroSet 0 ω = σ₀} := by ext ω; simp
    have hdisjoint2 : Pairwise (fun σ₁ σ₂ : Finset V =>
        Disjoint ({ω | vm.opinionZeroSet 0 ω = σ₁} : Set Ω) {ω | vm.opinionZeroSet 0 ω = σ₂}) := by
      intro σ₁ σ₂ hne
      rw [Set.disjoint_left]
      intro ω h1 h2; exact hne (h1.symm.trans h2)
    rw [show (1 : ℝ) = ((vm.μ : Measure Ω) Set.univ).toReal by rw [measure_univ]; simp]
    rw [hpartition2, measure_iUnion (fun i j h => hdisjoint2 h) (fun σ₀ => hA0_meas σ₀),
      tsum_fintype, ENNReal.toReal_sum (fun σ₀ _ => measure_ne_top (vm.μ : Measure Ω) _)]
  -- Combine: (1/2) ≤ ∑ σ₀, μ({A₀=σ₀} ∩ {T_abs ≤ K}).toReal = μ{T_abs ≤ K}.toReal
  rw [htoReal_sum]
  calc (1 / 2 : ℝ)
      = (1 / 2) * 1 := by ring
    _ = (1 / 2) * ∑ σ₀ : Finset V, ((vm.μ : Measure Ω) {ω | vm.opinionZeroSet 0 ω = σ₀}).toReal := by
          rw [hfibers_univ]
    _ = ∑ σ₀ : Finset V, (1 / 2) * ((vm.μ : Measure Ω) {ω | vm.opinionZeroSet 0 ω = σ₀}).toReal := by
          rw [Finset.mul_sum]
    _ ≤ ∑ σ₀ : Finset V,
          ((vm.μ : Measure Ω) ({ω | vm.opinionZeroSet 0 ω = σ₀} ∩ {ω | vm.absorptionTime ω ≤ (K : ℕ∞)})).toReal :=
          Finset.sum_le_sum (fun σ₀ _ => hfiber_bound σ₀)

/-- Two-opinion specialization of the §3.4 total consensus time (proved engine lemma; no
paper label — the paper's `thm:upper-bound-temporal-conductance` is the general
`TemporalGraph.upper_bound_temporal_conductance`).

There exists a constant `b' > 0` such that the following holds. Let `G` be a temporal graph
with fixed vertex degrees, `m` edges, and minimum degree `d_min`. Let `(S_t)` be the
standard two-opinion (κ=2) voter model on `G` with arbitrary initial state. If `φ̃(G) > 0`, then
with probability at least `1/2`, the consensus time is at most `b' · m / (d_min · φ̃(G))`.

The constant `b'` is `8 · b` where `b` is the constant from `upper_bound`. The factor of
`2` absorbs the bound `log(1+m) ≤ (49/50)·(m/d_min)` from `log_one_add_m_le_m_div_d_min`.

The hypothesis uses the *temporal* conductance `φ̃(G) = sup_{Δ≥1} φ^Δ(G)/Δ` (paper D7,
max-form) rather than the *graph* conductance `Φ(G) = sup_Δ {Δ⁻¹ : φ^Δ(G) ≥ 1}` (sum-form).
The two differ by `O(1/φ̃)` in general; pigeonholing the sum-form into the pointwise
window-guarantee shape required by T22 (`upper_bound`) loses a factor `Δ = Θ(1/φ̃)`.
The max-form `φ̃(G)` directly produces a `hasWindowGuarantee G.toTemporalGraph φ Δ` witness with
`φ/Δ ≥ φ̃(G)/2` via the sup property of `windowConductanceRatios`, matching the
paper's bound exactly. -/
theorem consensus_time_upper_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    -- Temporal graph with fixed degrees
    (G : TemporalGraphFixedDegree V)
    -- Voter model process
    (vm : G.VoterModelAbstract 2 Ω)
    -- Minimum degree d_min = G.minDegreeAt 0
    (d_min : ℕ) (hd : d_min = G.minDegreeAt 0) (hd_pos : 0 < d_min)
    -- Universal constant b ≥ 10924 from `upper_bound`
    (b : ℝ) (hb : 0 < b) (hb_large : (10924 : ℝ) ≤ b)
    -- Positivity of temporal conductance φ̃(G) > 0
    (hΦ_pos : 0 < G.temporalConductance) :
    -- Conclusion: P(T_abs ≤ ⌈8·b·m / (d_min · φ̃(G))⌉) ≥ 1/2
    (1 / 2 : ℝ) ≤ ((vm.μ : Measure Ω) {ω | vm.absorptionTime ω ≤
      (↑⌈8 * b * (G.numEdges : ℝ) /
        ((d_min : ℝ) * G.temporalConductance)⌉₊ : ℕ∞)}).toReal := by
  classical
  set m : ℕ := G.numEdges
  have hm : m = (G.snapshot 0).edgeFinset.card := rfl
  -- Derive 2·d_min ≤ b·m from the handshake lemma: nV·d_min ≤ 2·m (handshake),
  -- nV ≥ 1 gives d_min ≤ 2·m, so 2·d_min ≤ 4·m ≤ b·m since b ≥ 10924 ≥ 4.
  have hbm : 2 * (d_min : ℝ) ≤ b * (m : ℝ) := by
    have hnV_pos : 0 < Fintype.card V := Fintype.card_pos
    have hhandshake : Fintype.card V * d_min ≤ 2 * m := by
      have hsum := (G.snapshot 0).sum_degrees_eq_twice_card_edges
      have hle : Fintype.card V * G.minDegreeAt 0 ≤ ∑ v : V, (G.snapshot 0).degree v := by
        calc Fintype.card V * G.minDegreeAt 0
            = ∑ _v : V, G.minDegreeAt 0 := by
                rw [Finset.sum_const_nat (fun _ _ => rfl), Finset.card_univ]
          _ ≤ ∑ v : V, (G.snapshot 0).degree v :=
                Finset.sum_le_sum (fun v _ => TemporalGraph.minDegree_le_deg G.toTemporalGraph v)
      have h : Fintype.card V * G.minDegreeAt 0 ≤ 2 * (G.snapshot 0).edgeFinset.card := by
        rw [← hsum]; exact hle
      rw [hm, hd]; exact h
    have hd_le : (d_min : ℝ) ≤ 2 * (m : ℝ) := by
      have h : d_min ≤ 2 * m :=
        le_trans (Nat.le_mul_of_pos_left _ hnV_pos) hhandshake
      exact_mod_cast h
    have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    nlinarith
  -- Extract a window-guarantee witness `(φ, Δ)` from `0 < temporalConductance G.toTemporalGraph`.
  -- By the sup property of `windowConductanceRatios`, there exists a ratio
  -- `windowConductance G.toTemporalGraph Δ / Δ` strictly greater than `temporalConductance G.toTemporalGraph / 2`.
  set Φt : ℝ := TemporalGraph.temporalConductance G.toTemporalGraph with hΦt_def
  have hΦt_pos : 0 < Φt := hΦ_pos
  have hhalf_lt : Φt / 2 < Φt := by linarith
  have hne : (TemporalGraph.windowConductanceRatios G.toTemporalGraph).Nonempty :=
    ⟨TemporalGraph.windowConductance G.toTemporalGraph 1 / (1 : ℝ), 1, le_rfl, by norm_num⟩
  have hsup_eq : Φt = sSup (TemporalGraph.windowConductanceRatios G.toTemporalGraph) := rfl
  have hΦt_half_lt_sup : Φt / 2 < sSup (TemporalGraph.windowConductanceRatios G.toTemporalGraph) := by
    rw [← hsup_eq]; exact hhalf_lt
  obtain ⟨a, ha_ratio, ha_gt⟩ := exists_lt_of_lt_csSup hne hΦt_half_lt_sup
  obtain ⟨Δ, hΔ_ge1, ha_eq⟩ := ha_ratio
  -- Set `φ := windowConductance G.toTemporalGraph Δ`, so `a = φ/Δ` and `φ/Δ > Φt/2`.
  set φ : ℝ := TemporalGraph.windowConductance G.toTemporalGraph Δ with hφ_def
  have hΔ_pos_real : (0 : ℝ) < (Δ : ℝ) := by exact_mod_cast hΔ_ge1
  have hΔ_ne : (Δ : ℝ) ≠ 0 := ne_of_gt hΔ_pos_real
  have hφ_div_gt : φ / (Δ : ℝ) > Φt / 2 := by rw [ha_eq] at ha_gt; exact ha_gt
  -- φ > 0: from φ/Δ > Φt/2 > 0 and Δ > 0.
  have hφ_pos : 0 < φ := by
    have hpos : 0 < φ / (Δ : ℝ) := lt_trans (by linarith : (0 : ℝ) < Φt / 2) hφ_div_gt
    exact (div_pos_iff_of_pos_right hΔ_pos_real).mp hpos
  have hφ_nn : 0 ≤ φ := hφ_pos.le
  have hφ_le1 : φ ≤ 1 := TemporalGraph.windowConductance_le_one G.toTemporalGraph Δ
  -- Window guarantee at `(φ, Δ)` via `hasWindowGuarantee_of_le_windowConductance`.
  have hwin0 : TemporalGraph.hasWindowGuarantee G.toTemporalGraph φ Δ :=
    TemporalGraph.hasWindowGuarantee_of_le_windowConductance G.toTemporalGraph hΔ_ge1 (le_refl _)
  -- Per-interval MAX-form hypothesis required by T22: for each `j` and admissible
  -- cut `S`, `φ ≤ φ^{[j·Δ, j·Δ+Δ-1]}(S)`. Obtained from `hwin0` at start time `j·Δ`
  -- via `hasWindowGuarantee_le_maxSetConductanceOnInterval`.
  have hsum_const : ∀ j : ℕ, (∑ _i ∈ Finset.range j, Δ) = j * Δ := fun j => by
    simp [Finset.sum_const, Finset.card_range, mul_comm]
  have hwin : ∀ j : ℕ, ∀ S ∈ TemporalGraph.admissibleCuts G.toTemporalGraph,
      (fun _ : ℕ => φ) j ≤ TemporalGraph.maxSetConductanceOnInterval G.toTemporalGraph
        (∑ i ∈ Finset.range j, (fun _ : ℕ => Δ) i) ((fun _ : ℕ => Δ) j) S := by
    intro j S hS
    have hbridge :=
      TemporalGraph.hasWindowGuarantee_le_maxSetConductanceOnInterval
        G.toTemporalGraph hwin0 (j * Δ) hS
    -- hbridge : φ ≤ maxSetConductanceOnInterval G.toTemporalGraph (j*Δ) Δ S
    -- Goal:     φ ≤ maxSetConductanceOnInterval G.toTemporalGraph (∑ range j, Δ) Δ S
    show φ ≤ _
    convert hbridge using 2
    exact hsum_const j
  -- Set J := ⌈α/φ⌉₊ where α := b·(m/d_min + log(1+m)).
  set α : ℝ := b * ((m : ℝ) / d_min + Real.log (1 + (m : ℝ))) with hα_def
  set J : ℕ := ⌈α / φ⌉₊ with hJ_def
  have hd_min_pos_real : (0 : ℝ) < (d_min : ℝ) := by exact_mod_cast hd_pos
  have hlog_nn : (0 : ℝ) ≤ Real.log (1 + (m : ℝ)) :=
    Real.log_nonneg (by have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m; linarith)
  have hα_nn : (0 : ℝ) ≤ α := by
    apply mul_nonneg hb.le
    apply add_nonneg
    · exact div_nonneg (Nat.cast_nonneg _) hd_min_pos_real.le
    · exact hlog_nn
  -- α ≥ 2: b·m/d_min ≥ 2 from hbm.
  have hbm_div_ge2 : (2 : ℝ) ≤ b * (m : ℝ) / (d_min : ℝ) := by
    rw [le_div_iff₀ hd_min_pos_real]; linarith
  have hα_ge2 : (2 : ℝ) ≤ α := by
    calc (2 : ℝ) ≤ b * (m : ℝ) / (d_min : ℝ) := hbm_div_ge2
      _ ≤ b * ((m : ℝ) / (d_min : ℝ) + Real.log (1 + (m : ℝ))) := by
          have heq : b * (m : ℝ) / (d_min : ℝ) = b * ((m : ℝ) / (d_min : ℝ)) := by ring
          rw [heq]
          apply mul_le_mul_of_nonneg_left _ hb.le
          linarith
      _ = α := rfl
  -- Sum condition for T22 (paper-aligned): b·(m/d_min+log(1+m)) ≤
  -- ∑_{ℓ=0}^J φ = (J+1)·φ.
  have hsum_const : (∑ _ℓ ∈ Finset.range (J + 1), φ) = ((J + 1 : ℕ) : ℝ) * φ := by
    simp [Finset.sum_const, Finset.card_range]
  have hJ_bound : α ≤ ∑ _ℓ ∈ Finset.range (J + 1), φ := by
    rw [hsum_const]
    -- (J : ℝ) ≥ α/φ since J = ⌈α/φ⌉₊
    have hJ_ge : α / φ ≤ (J : ℝ) := Nat.le_ceil _
    have hJ_succ_ge : α / φ ≤ ((J + 1 : ℕ) : ℝ) := by push_cast; linarith
    have : α / φ * φ ≤ ((J + 1 : ℕ) : ℝ) * φ := mul_le_mul_of_nonneg_right hJ_succ_ge hφ_nn
    rwa [div_mul_cancel₀ _ (ne_of_gt hφ_pos)] at this
  -- Derive b·(m/d_min) ≤ ∑φ for the new upper_bound signature.
  -- α = b·(m/d_min + log(1+m)) ≥ b·(m/d_min) since log ≥ 0.
  have hJ_bound_simple : b * ((m : ℝ) / d_min) ≤ ∑ _ℓ ∈ Finset.range (J + 1), φ := by
    calc b * ((m : ℝ) / d_min)
        ≤ b * ((m : ℝ) / d_min + Real.log (1 + (m : ℝ))) := by
            apply mul_le_mul_of_nonneg_left _ hb.le; linarith [hlog_nn]
      _ = α := rfl
      _ ≤ ∑ _ℓ ∈ Finset.range (J + 1), φ := hJ_bound
  -- Apply upper_bound with constant Δ_j = Δ, φ_j = φ.
  have hUB := upper_bound G vm d_min hd hd_pos
    (fun _ => Δ) (fun _ => hΔ_ge1)
    (fun _ => φ) (fun _ => hφ_nn) (fun _ => hφ_le1)
    hwin b hb_large J hJ_bound_simple
  -- The sum ∑ j ∈ range (J+1), Δ = (J+1) · Δ.
  have hsum_eq : (∑ _j ∈ Finset.range (J + 1), Δ) = (J + 1) * Δ := by
    simp [Finset.sum_const, Finset.card_range, Nat.succ_mul]
  -- Key arithmetic: (J+1)·Δ ≤ ⌈4·α/Φt⌉₊.
  -- From hφ_div_gt: φ/Δ > Φt/2, i.e., Δ/φ < 2/Φt, i.e., Δ·Φt < 2·φ ≤ 2.
  -- J ≤ α/φ + 1, so (J+1)·Δ ≤ (α/φ + 2)·Δ = α·Δ/φ + 2·Δ.
  --   α·Δ/φ < α·(2/Φt) = 2α/Φt.
  --   2·Δ ≤ 2α/Φt since Δ·Φt < 2 ≤ α.
  -- Hence (J+1)·Δ < 4α/Φt.
  have hΔφ_Φt : (Δ : ℝ) * Φt < 2 * φ := by
    -- From φ/Δ > Φt/2 and Δ > 0, 2 > 0: 2·φ > Δ·Φt.
    have hlt : Φt / 2 < φ / (Δ : ℝ) := hφ_div_gt
    have h := (div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 2) hΔ_pos_real).mp hlt
    -- h : Φt * Δ < φ * 2
    linarith
  have hkey : ((J + 1) * Δ : ℕ) ≤
      ⌈4 * b * ((m : ℝ) / d_min + Real.log (1 + (m : ℝ))) / Φt⌉₊ := by
    -- Show real-valued bound, take ceilings.
    have hreal_bound : ((J + 1) * Δ : ℕ) ≤
        4 * b * ((m : ℝ) / d_min + Real.log (1 + (m : ℝ))) / Φt := by
      have hLHS_eq : (((J + 1) * Δ : ℕ) : ℝ) = ((J : ℝ) + 1) * (Δ : ℝ) := by
        push_cast; ring
      -- Step 1: J ≤ α/φ + 1 in ℝ
      have hJ_le : (J : ℝ) ≤ α / φ + 1 := by
        have hfloor : (⌊α / φ⌋₊ : ℝ) ≤ α / φ :=
          Nat.floor_le (div_nonneg hα_nn hφ_nn)
        have : (J : ℝ) ≤ ⌊α / φ⌋₊ + 1 := by
          exact_mod_cast Nat.ceil_le_floor_add_one _
        linarith
      -- Step 2: ((J+1)·Δ : ℝ) ≤ (α/φ + 2)·Δ
      have hstep1 : ((J : ℝ) + 1) * (Δ : ℝ) ≤ (α / φ + 2) * (Δ : ℝ) := by
        have : (J : ℝ) + 1 ≤ α / φ + 2 := by linarith
        exact mul_le_mul_of_nonneg_right this hΔ_pos_real.le
      -- (α/φ + 2)·Δ = α·Δ/φ + 2·Δ
      have hexpand : (α / φ + 2) * (Δ : ℝ) = α * (Δ : ℝ) / φ + 2 * (Δ : ℝ) := by
        field_simp
      -- α·Δ/φ ≤ 2·α/Φt: from Δ·Φt < 2·φ, hence Δ/φ < 2/Φt, hence α·Δ/φ ≤ 2·α/Φt.
      have hαΔφ : α * (Δ : ℝ) / φ ≤ 2 * α / Φt := by
        rw [div_le_div_iff₀ hφ_pos hΦt_pos]
        -- Goal: α·Δ·Φt ≤ 2·α·φ
        nlinarith only [hΔφ_Φt, hα_nn]
      -- 2·Δ ≤ 2·α/Φt: from Δ·Φt < 2·φ ≤ 2 ≤ α, so 2·Δ·Φt < 4 ≤ 2·α·... wait, need 2·Δ·Φt ≤ 2·α.
      -- Have Δ·Φt < 2·φ ≤ 2, hence 2·Δ·Φt < 4 = 2·2 ≤ 2·α.
      have h2Δ : (2 : ℝ) * (Δ : ℝ) ≤ 2 * α / Φt := by
        rw [le_div_iff₀ hΦt_pos]
        have hbnd : (Δ : ℝ) * Φt < 2 := by
          calc (Δ : ℝ) * Φt < 2 * φ := hΔφ_Φt
            _ ≤ 2 * 1 := by linarith
            _ = 2 := by ring
        linarith only [hbnd, hα_ge2]
      -- Combine.
      have hcombine : (α / φ + 2) * (Δ : ℝ) ≤
          4 * b * ((m : ℝ) / d_min + Real.log (1 + (m : ℝ))) / Φt := by
        rw [hexpand]
        have h_sum_le : α * (Δ : ℝ) / φ + 2 * (Δ : ℝ) ≤
            2 * α / Φt + 2 * α / Φt := by linarith
        have h_rhs : 2 * α / Φt + 2 * α / Φt =
            4 * b * ((m : ℝ) / d_min + Real.log (1 + (m : ℝ))) / Φt := by
          rw [hα_def]
          field_simp
          ring
        linarith
      rw [hLHS_eq]
      linarith
    have := Nat.ceil_le_ceil hreal_bound
    rwa [Nat.ceil_natCast] at this
  -- Show ⌈4b·(m/d+log(1+m))/Φ⌉₊ ≤ ⌈8b·m/(d·Φ)⌉₊ via the sharp log bound.
  have hkey2 : ⌈4 * b * ((m : ℝ) / d_min + Real.log (1 + (m : ℝ))) / Φt⌉₊ ≤
      ⌈8 * b * (m : ℝ) / ((d_min : ℝ) * Φt)⌉₊ := by
    apply Nat.ceil_le_ceil
    have hlog_le : Real.log (1 + (m : ℝ)) ≤ 49 / 50 * ((m : ℝ) / (d_min : ℝ)) :=
      log_one_add_m_le_m_div_d_min G d_min hd hd_pos
    have hd_pos_real : (0 : ℝ) < (d_min : ℝ) := Nat.cast_pos.mpr hd_pos
    have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    -- log(1+m) ≤ m/d, so m/d + log ≤ 2*(m/d), hence 4b*(m/d + log) ≤ 8b*(m/d).
    have hmd_nn : (0 : ℝ) ≤ (m : ℝ) / (d_min : ℝ) := div_nonneg hm_nn hd_pos_real.le
    have hlog_le' : Real.log (1 + (m : ℝ)) ≤ (m : ℝ) / (d_min : ℝ) := by linarith
    have hA_le_B : 4 * b * ((m : ℝ) / d_min + Real.log (1 + (m : ℝ))) ≤
        8 * b * ((m : ℝ) / d_min) := by
      have hlog_mul : 4 * b * Real.log (1 + (m : ℝ)) ≤ 4 * b * ((m : ℝ) / d_min) :=
        mul_le_mul_of_nonneg_left hlog_le' (by linarith)
      have hgoal_eq : 4 * b * ((m : ℝ) / d_min + Real.log (1 + (m : ℝ))) =
          4 * b * ((m : ℝ) / d_min) + 4 * b * Real.log (1 + (m : ℝ)) := by ring
      linarith [show (8 : ℝ) * b * ((m : ℝ) / d_min) =
          4 * b * ((m : ℝ) / d_min) + 4 * b * ((m : ℝ) / d_min) from by ring]
    calc 4 * b * ((m : ℝ) / d_min + Real.log (1 + (m : ℝ))) / Φt
        ≤ 8 * b * ((m : ℝ) / d_min) / Φt := by
            rw [div_le_div_iff₀ hΦt_pos hΦt_pos]
            exact mul_le_mul_of_nonneg_right hA_le_B (le_of_lt hΦt_pos)
      _ = 8 * b * (m : ℝ) / ((d_min : ℝ) * Φt) := by ring
  -- Combine: the set in `upper_bound`'s conclusion is a subset of ours.
  refine le_trans hUB ?_
  apply ENNReal.toReal_mono
  · exact measure_ne_top (vm.μ : Measure Ω) _
  · refine (vm.μ : Measure Ω).mono ?_
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    have : (∑ j ∈ Finset.range (J + 1), Δ) ≤
        ⌈8 * b * (m : ℝ) / ((d_min : ℝ) *
          TemporalGraph.temporalConductance G.toTemporalGraph)⌉₊ := by
      rw [hsum_eq]
      exact le_trans hkey hkey2
    exact le_trans hω (by exact_mod_cast this)


end VoterModel
