module

import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import UpperBound.MultiOpinion.Metaphase
public import VoterProcess.Absorption.Consensus
public import TemporalGraph.Degree
public import TemporalGraph.Conductance
public import TemporalGraph.Basic
import Mathlib.Algebra.Order.Star.Real
import UpperBound.MultiOpinion.Expectation.Metaphase
import UpperBound.MultiOpinion.Expectation.Rbeta
import UpperBound.TwoOpinion.Theorem

/-! ## §3.4 multi-opinion upper bound (Tier E): abstract-model internals

Assembles the §3.4 expectation analysis (`expected_Rbeta_succ_le_final`, bounding
`E[R_{β}]` for `β = beta κ + 1`) with the consensus characterization
(`metaphase_beta_succ_consensus`) and Markov's inequality into the general
`κ`-opinion upper bound: with probability `≥ 1/2`, the consensus time `consensusTime` is at
most `Δ_0 + … + Δ_J`.

The metaphase cap constant `B` is chosen as the power of two in `hJ`, large enough that the
Markov ratio `E[R_β]/r_max` is `≤ 1/2` while (via `hJ`) the surviving phase fits inside
`∑_{j<J+1} Δ_j`.

## Main results

- `upper_bound_window_conductance_abstract`, `upper_bound_temporal_conductance_abstract` — abstract-model
  internal lemmas; the paper-facing `upper_bound_window_conductance`, `upper_bound_temporal_conductance`
  wrappers live in `MainTheorems.lean`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Classical ENNReal NNReal

noncomputable section

namespace TemporalGraph

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
variable {κ : ℕ} [NeZero κ] {G : TemporalGraph V}
variable {Ω : Type*} [MeasurableSpace Ω]

/-- §3.4 upper bound, general `κ`-opinion form (abstract-model internal lemma). For the lazy voter
model on a fixed-degree temporal graph `G` with `m` edges and minimum degree `d_min`, given window
lengths `Δ_j ≥ 1` and conductances `φ_j ∈ [0,1]` such that on each window `[∑_{i<j} Δ_i, … + Δ_j − 1]`
every admissible cut attains conductance `≥ φ_j` (`hwin`), if `∑_{ℓ ≤ J} φ_ℓ ≥ 2^21·m/d_min`
then with probability at least `1/2` consensus is reached by time `Δ_0 + … + Δ_J`. -/
theorem upper_bound_window_conductance_abstract
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V] {κ : ℕ} [NeZero κ] {Ω : Type*} [MeasurableSpace Ω]
    (G : TemporalGraphFixedDegree V) (vm : G.VoterModelAbstract κ Ω)
    (Δ : ℕ → ℕ) (hΔ_pos : ∀ j, 1 ≤ Δ j)
    (φ : ℕ → ℝ) (hφ_nn : ∀ j, 0 ≤ φ j) (hφ_le1 : ∀ j, φ j ≤ 1)
    (hwin : ∀ j, ∀ Sc ∈ G.admissibleCuts,
      φ j ≤ G.maxSetConductanceOnInterval (∑ i ∈ Finset.range j, Δ i) (Δ j) Sc)
    (J : ℕ) (hJ : 2 ^ 21 * ((G.numEdges : ℝ) / (G.minDegreeAt 0 : ℝ))
      ≤ ∑ ℓ ∈ Finset.range (J + 1), φ ℓ) :
    0.5 ≤
      vm.μ {ω | vm.consensusTime ω ≤ (↑(∑ j ∈ Finset.range (J + 1), Δ j) : ℕ∞)} := by
  -- `vm.μ` here is the `ℝ≥0`-valued `ProbabilityMeasure`; reduce to the real `.toReal` form.
  suffices h : (1 / 2 : ℝ) ≤ ((vm.μ : Measure _)
      {ω | vm.consensusTime ω ≤ (↑(∑ j ∈ Finset.range (J + 1), Δ j) : ℕ∞)}).toReal by
    rw [← NNReal.coe_le_coe]
    rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, ENNReal.coe_toReal] at h
    push_cast at h ⊢
    linarith [h]
  classical
  set m : ℕ := G.numEdges
  have hm : m = (G.snapshot 0).edgeFinset.card := rfl
  -- Fix the universal constant `b` at the minimal value admissible for
  -- `expected_Rbeta_succ_le_final`.
  set b : ℝ := 5462 with hb_def
  have hb_large : (5462 : ℝ) ≤ b := hb_def.ge
  -- `d_min := G.minDegreeAt 0`; positivity from `FixedDegrees` (every degree is positive).
  obtain ⟨vmin, hvmin⟩ := TemporalGraph.exists_minDegreeAt_vertex G.toTemporalGraph 0
  have hd_pos : 0 < G.minDegreeAt 0 := by
    simp only [TemporalGraphFixedDegree.minDegreeAt]; rw [hvmin]; exact G.degrees_pos vmin 0
  set d_min : ℕ := G.minDegreeAt 0 with hd
  have hmono : Monotone (TemporalGraph.phaseTime Δ φ) := TemporalGraph.phaseTime_mono Δ φ
  set B : ℝ := 2 ^ 21 with hBdef
  set β : ℕ := TemporalGraph.beta κ + 1 with hβdef
  set R : Ω → ℕ := fun ω => vm.metaphase B m d_min Δ φ β ω with hRdef
  set rM : ℕ := TemporalGraph.rMax B m d_min with hrMdef
  have hb1 : (1 : ℝ) ≤ b := by linarith
  have hd1 : (1 : ℝ) ≤ (d_min : ℝ) := by exact_mod_cast hd_pos
  have hdR : (0 : ℝ) < (d_min : ℝ) := by linarith
  -- `hvol` from edge count + fixed degrees (volume = 2·edges = 2m)
  have hvol : ∀ t, (TemporalGraph.volume G.toTemporalGraph t Finset.univ : ℝ) ≤ 2 * (m : ℝ) := by
    intro t
    have hsumeq : ∑ v : V, (G.snapshot t).degree v = ∑ v : V, (G.snapshot 0).degree v :=
      Finset.sum_congr rfl (fun v _ => G.degrees_fixed v t 0)
    have h1 : (G.snapshot t).edgeFinset.card = m := by
      have h2 : 2 * (G.snapshot t).edgeFinset.card = 2 * (G.snapshot 0).edgeFinset.card := by
        rw [← (G.snapshot t).sum_degrees_eq_twice_card_edges,
          ← (G.snapshot 0).sum_degrees_eq_twice_card_edges, hsumeq]
      rw [hm]; omega
    have hve : TemporalGraph.volume G.toTemporalGraph t Finset.univ = 2 * m := by
      have h3 : TemporalGraph.volume G.toTemporalGraph t Finset.univ = ∑ v : V, (G.snapshot t).degree v := rfl
      rw [h3, (G.snapshot t).sum_degrees_eq_twice_card_edges, h1]
    rw [hve]; exact le_of_eq (by push_cast; ring)
  -- handshake `n·d_min ≤ 2m`, hence `m/d_min ≥ 1/2`
  have hhand : (Fintype.card V : ℝ) * (d_min : ℝ) ≤ 2 * (m : ℝ) :=
    TemporalGraph.card_mul_minDegree_le m d_min hd (hvol 0)
  have hnpos : (1 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast Fintype.card_pos
  have hmd_ge : (1 : ℝ) / 2 ≤ (m : ℝ) / (d_min : ℝ) := by
    rw [le_div_iff₀ hdR]; nlinarith [hhand, hnpos]
  have hm_pos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h] at hmd_ge; norm_num at hmd_ge
    · exact h
  -- bounded reachability `reachUpToRMax`, derived from the finite phase budget `hJ`
  -- (`r ≤ r_max = ⌊B·m/d_min⌋ ⟹ (r:ℝ) ≤ B·m/d_min ≤ ∑_{ℓ ≤ J} φ_ℓ`, reachable by `ℓ = J+1`)
  have hreachR : TemporalGraph.reachUpToRMax B m d_min φ := by
    intro r hr
    refine ⟨J + 1, ?_⟩
    have hBnn : (0 : ℝ) ≤ B * (m : ℝ) / (d_min : ℝ) := by
      rw [hBdef]; positivity
    have hfloor : ((TemporalGraph.rMax B m d_min : ℕ) : ℝ) ≤ B * (m : ℝ) / (d_min : ℝ) := by
      unfold TemporalGraph.rMax; exact Nat.floor_le hBnn
    calc (r : ℝ) ≤ ((TemporalGraph.rMax B m d_min : ℕ) : ℝ) := by exact_mod_cast hr
      _ ≤ B * (m : ℝ) / (d_min : ℝ) := hfloor
      _ = (2 ^ 21 : ℝ) * ((m : ℝ) / (d_min : ℝ)) := by rw [hBdef]; ring
      _ ≤ ∑ ℓ ∈ Finset.range (J + 1), φ ℓ := hJ
  -- `E[R] ≤ 186 b m / d_min`
  have hER : (vm.μ : Measure Ω)[fun ω => (R ω : ℝ)] ≤ 186 * b * (m : ℝ) / (d_min : ℝ) :=
    vm.expected_Rbeta_succ_le_final B d_min b Δ φ hmono hd hd_pos (by linarith)
      hΔ_pos hφ_nn hφ_le1 hreachR hwin hb_large hm_pos hvol
  -- `r_max ≥ 372 b m / d_min`
  have hrM_ge : (372 : ℝ) * b * (m : ℝ) / (d_min : ℝ) ≤ (rM : ℝ) := by
    have hx : (2 ^ 21 : ℝ) * ((m : ℝ) / (d_min : ℝ)) - 1 < (rM : ℝ) := by
      have hlt := Nat.lt_floor_add_one ((2 ^ 21 : ℝ) * ((m : ℝ) / (d_min : ℝ)))
      have : (rM : ℝ) = (⌊(2 ^ 21 : ℝ) * ((m : ℝ) / (d_min : ℝ))⌋₊ : ℝ) := by
        rw [hrMdef, hBdef, TemporalGraph.rMax, mul_div_assoc]
      rw [this]; linarith
    have hslack : (1 : ℝ) ≤ ((2 ^ 21 : ℝ) - 372 * b) * ((m : ℝ) / (d_min : ℝ)) := by
      rw [hb_def]; nlinarith [hmd_ge]
    have heq : (2 ^ 21 : ℝ) * ((m : ℝ) / (d_min : ℝ)) =
        372 * b * (m : ℝ) / (d_min : ℝ)
          + ((2 ^ 21 : ℝ) - 372 * b) * ((m : ℝ) / (d_min : ℝ)) := by ring
    rw [heq] at hx; linarith
  have hrM_pos : (0 : ℝ) < (rM : ℝ) := by
    have : (0 : ℝ) < 372 * b * (m : ℝ) / (d_min : ℝ) := by positivity
    linarith
  -- measurability / integrability of `R`
  have hRmeas : Measurable R := vm.metaphase_measurable B m d_min Δ φ hmono β
  have hRint : Integrable (fun ω => (R ω : ℝ)) vm.μ :=
    vm.integrable_natCast_le (TemporalGraph.rMax B m d_min) hRmeas
      (fun ω => vm.metaphase_le_rMax B m d_min Δ φ β ω)
  have hR_nn : (0 : Ω → ℝ) ≤ᵐ[(vm.μ : Measure Ω)] (fun ω => (R ω : ℝ)) :=
    ae_of_all _ (fun ω => Nat.cast_nonneg _)
  -- Markov: `μ.real {r_max ≤ R} ≤ 1/2`
  have hmarkov : ((vm.μ : Measure _) {ω | rM ≤ R ω}).toReal ≤ 1 / 2 := by
    have hge := MeasureTheory.mul_meas_ge_le_integral_of_nonneg hR_nn hRint (rM : ℝ)
    have hset : {x | (rM : ℝ) ≤ (R x : ℝ)} = {ω | rM ≤ R ω} := by
      ext ω; simp only [Set.mem_setOf_eq, Nat.cast_le]
    rw [hset] at hge
    have hER' : ∫ ω, (R ω : ℝ) ∂vm.μ ≤ (rM : ℝ) * (1 / 2) := by
      have : (186 : ℝ) * b * (m : ℝ) / (d_min : ℝ) ≤ (rM : ℝ) * (1 / 2) := by
        have hhalf : (186 : ℝ) * b * (m : ℝ) / (d_min : ℝ)
            = (372 * b * (m : ℝ) / (d_min : ℝ)) * (1 / 2) := by ring
        rw [hhalf]; exact mul_le_mul_of_nonneg_right hrM_ge (by norm_num)
      exact le_trans hER this
    exact le_of_mul_le_mul_left (le_trans hge hER') hrM_pos
  -- `{R < r_max} ⊆ {consensusTime ≤ ∑Δ}`
  have hsubset : {ω | R ω < rM} ⊆
      {ω | vm.consensusTime ω ≤ (↑(∑ j ∈ Finset.range (J + 1), Δ j) : ℕ∞)} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    have hcons : vm.consensusTime ω ≤ (↑(TemporalGraph.phaseTime Δ φ (R ω)) : ℕ∞) :=
      vm.metaphase_beta_succ_consensus B m d_min Δ φ ω hω
    have hRφ : (R ω : ℝ) ≤ ∑ ℓ ∈ Finset.range (J + 1), φ ℓ := by
      have h1 : (R ω : ℝ) < (rM : ℝ) := by exact_mod_cast hω
      have h2 : (rM : ℝ) ≤ (2 ^ 21 : ℝ) * ((m : ℝ) / (d_min : ℝ)) := by
        rw [hrMdef, hBdef, TemporalGraph.rMax, mul_div_assoc]
        exact Nat.floor_le (by positivity)
      linarith [hJ]
    have hle := TemporalGraph.phaseTime_le_sum_Delta (Δ := Δ) (φ := φ) (R ω) J hRφ
    exact le_trans hcons (Nat.cast_le.mpr hle)
  -- combine via complement
  have hAmeas : MeasurableSet
      {ω | vm.consensusTime ω ≤ (↑(∑ j ∈ Finset.range (J + 1), Δ j) : ℕ∞)} :=
    vm.consensusTime_measurable
      (t := {x : ℕ∞ | x ≤ (↑(∑ j ∈ Finset.range (J + 1), Δ j) : ℕ∞)})
      MeasurableSet.of_discrete
  have hEmeas : MeasurableSet {ω | rM ≤ R ω} := hRmeas measurableSet_Ici
  have hcompl : {ω | R ω < rM} = {ω | rM ≤ R ω}ᶜ := by
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
  have hmono_meas : ((vm.μ : Measure _) {ω | R ω < rM}).toReal
      ≤ ((vm.μ : Measure _)
        {ω | vm.consensusTime ω ≤ (↑(∑ j ∈ Finset.range (J + 1), Δ j) : ℕ∞)}).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsubset)
  have hcomplR : ((vm.μ : Measure _) {ω | R ω < rM}).toReal = 1 - ((vm.μ : Measure _) {ω | rM ≤ R ω}).toReal := by
    rw [hcompl, measure_compl hEmeas (measure_ne_top _ _), measure_univ,
      ENNReal.toReal_sub_of_le prob_le_one (by norm_num), ENNReal.toReal_one]
  linarith [hmono_meas, hcomplR, hmarkov]

/-- §3.4 upper bound in closed form (general `κ`-opinion, abstract-model internal lemma). For the
lazy voter model on a fixed-degree temporal graph `G` with `m` edges and minimum degree `d_min`,
with probability at least `1/2` the consensus time is at most `b'·m / (d_min·Φ(G))`, with explicit
constant `b' = 2^22`. Stated in `ℝ≥0∞`, so no positivity hypothesis on `Φ(G)` is needed: when
`Φ(G) ≤ 0` the denominator is `0` and, since `m ≥ 1`, the bound evaluates to `⊤`, making the event
the whole space. -/
theorem upper_bound_temporal_conductance_abstract
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V] {κ : ℕ} [NeZero κ] {Ω : Type*} [MeasurableSpace Ω]
    (G : TemporalGraphFixedDegree V) (vm : G.VoterModelAbstract κ Ω) :
    0.5 ≤ vm.μ {ω | (vm.consensusTime ω : ℝ≥0∞) ≤
      2 ^ 22 * (G.numEdges : ℝ≥0∞) /
        ((G.minDegreeAt 0 : ℝ≥0∞) * ENNReal.ofReal G.temporalConductance)} := by
  -- Split on the sign of `Φ(G)`. When `Φ(G) ≤ 0` the bound degenerates to `⊤` (numerator nonzero
  -- since `m ≥ 1`, denominator `0`), so the event is `univ` and has probability `1 ≥ 1/2`.
  rcases le_or_gt G.temporalConductance 0 with hΦ_nonpos | hΦ_pos
  · have hnum_ne : (2 ^ 22 * (G.numEdges : ℝ≥0∞)) ≠ 0 :=
      mul_ne_zero (by norm_num) (by exact_mod_cast G.numEdges_pos.ne')
    have hRHS : (2 ^ 22 * (G.numEdges : ℝ≥0∞) /
        ((G.minDegreeAt 0 : ℝ≥0∞) * ENNReal.ofReal G.temporalConductance)) = ⊤ := by
      rw [ENNReal.ofReal_eq_zero.mpr hΦ_nonpos, mul_zero, ENNReal.div_zero hnum_ne]
    have hset : {ω | (vm.consensusTime ω : ℝ≥0∞) ≤ 2 ^ 22 * (G.numEdges : ℝ≥0∞) /
        ((G.minDegreeAt 0 : ℝ≥0∞) * ENNReal.ofReal G.temporalConductance)} = Set.univ := by
      rw [hRHS]; ext ω; simp
    rw [hset]; simp; norm_num
  -- `vm.μ` here is the `ℝ≥0`-valued `ProbabilityMeasure`; reduce to the real `.toReal` form.
  suffices h : (1 / 2 : ℝ) ≤ ((vm.μ : Measure Ω) {ω | (vm.consensusTime ω : ℝ≥0∞) ≤
      2 ^ 22 * (G.numEdges : ℝ≥0∞) /
        ((G.minDegreeAt 0 : ℝ≥0∞) * ENNReal.ofReal G.toTemporalGraph.temporalConductance)}).toReal by
    rw [← NNReal.coe_le_coe]
    rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, ENNReal.coe_toReal] at h
    push_cast at h ⊢
    linarith [h]
  classical
  set m : ℕ := G.numEdges
  have hm : m = (G.snapshot 0).edgeFinset.card := rfl
  -- Fix the universal constant `b` at the minimal value admissible for
  -- `upper_bound_window_conductance_abstract`.
  set b : ℝ := 5462 with hb_def
  have hb_large : (5462 : ℝ) ≤ b := hb_def.ge
  -- `d_min := G.minDegreeAt 0`; positivity from `FixedDegrees` (every degree is positive).
  obtain ⟨vmin, hvmin⟩ := TemporalGraph.exists_minDegreeAt_vertex G.toTemporalGraph 0
  have hd_pos : 0 < G.minDegreeAt 0 := by
    simp only [TemporalGraphFixedDegree.minDegreeAt]; rw [hvmin]; exact G.degrees_pos vmin 0
  set d_min : ℕ := G.minDegreeAt 0 with hd
  have hb : 0 < b := by linarith
  -- Derive (b/2)·d_min ≤ b·m from the handshake lemma: nV·d_min ≤ 2·m (handshake),
  -- nV ≥ 1 gives d_min ≤ 2·m, so (b/2)·d_min ≤ b·m.
  have hbm : 2731 * (d_min : ℝ) ≤ b * (m : ℝ) := by
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
    nlinarith [hd_le, hm_nn, mul_nonneg (show (0 : ℝ) ≤ b - 5462 by linarith) hm_nn]
  -- Extract a window-guarantee witness `(φ, Δ)` from `0 < temporalConductance G`.
  set Φt : ℝ := TemporalGraph.temporalConductance G.toTemporalGraph with hΦt_def
  have hΦt_pos : 0 < Φt := hΦ_pos
  have hfrac_lt : 127 / 128 * Φt < Φt := by linarith
  have hne : (TemporalGraph.windowConductanceRatios G.toTemporalGraph).Nonempty :=
    ⟨TemporalGraph.windowConductance G.toTemporalGraph 1 / (1 : ℝ), 1, le_rfl, by norm_num⟩
  have hsup_eq : Φt = sSup (TemporalGraph.windowConductanceRatios G.toTemporalGraph) := rfl
  have hΦt_frac_lt_sup : 127 / 128 * Φt < sSup (TemporalGraph.windowConductanceRatios G.toTemporalGraph) := by
    rw [← hsup_eq]; exact hfrac_lt
  obtain ⟨a, ha_ratio, ha_gt⟩ := exists_lt_of_lt_csSup hne hΦt_frac_lt_sup
  obtain ⟨Δ, hΔ_ge1, ha_eq⟩ := ha_ratio
  set φ : ℝ := TemporalGraph.windowConductance G.toTemporalGraph Δ with hφ_def
  have hΔ_pos_real : (0 : ℝ) < (Δ : ℝ) := by exact_mod_cast hΔ_ge1
  have hΔ_ne : (Δ : ℝ) ≠ 0 := ne_of_gt hΔ_pos_real
  have hφ_div_gt : φ / (Δ : ℝ) > 127 / 128 * Φt := by rw [ha_eq] at ha_gt; exact ha_gt
  have hφ_pos : 0 < φ := by
    have hpos : 0 < φ / (Δ : ℝ) := lt_trans (by linarith : (0 : ℝ) < 127 / 128 * Φt) hφ_div_gt
    exact (div_pos_iff_of_pos_right hΔ_pos_real).mp hpos
  have hφ_nn : 0 ≤ φ := hφ_pos.le
  have hφ_le1 : φ ≤ 1 := TemporalGraph.windowConductance_le_one G.toTemporalGraph Δ
  have hwin0 : TemporalGraph.hasWindowGuarantee G.toTemporalGraph φ Δ :=
    TemporalGraph.hasWindowGuarantee_of_le_windowConductance G.toTemporalGraph hΔ_ge1 (le_refl _)
  have hsum_const : ∀ j : ℕ, (∑ _i ∈ Finset.range j, Δ) = j * Δ := fun j => by
    simp [Finset.sum_const, Finset.card_range, mul_comm]
  have hwin : ∀ j : ℕ, ∀ S ∈ TemporalGraph.admissibleCuts G.toTemporalGraph,
      (fun _ : ℕ => φ) j ≤ TemporalGraph.maxSetConductanceOnInterval G.toTemporalGraph
        (∑ i ∈ Finset.range j, (fun _ : ℕ => Δ) i) ((fun _ : ℕ => Δ) j) S := by
    intro j S hS
    have hbridge :=
      TemporalGraph.hasWindowGuarantee_le_maxSetConductanceOnInterval
        G.toTemporalGraph hwin0 (j * Δ) hS
    show φ ≤ _
    convert hbridge using 2
    exact hsum_const j
  -- Set J := ⌈α/φ⌉₊ where α := 2^21·(m/d_min + log(1+m)).
  set α : ℝ := (2 ^ 21 : ℝ) * ((m : ℝ) / d_min + Real.log (1 + (m : ℝ))) with hα_def
  set J : ℕ := ⌈α / φ⌉₊ with hJ_def
  have hd_min_pos_real : (0 : ℝ) < (d_min : ℝ) := by exact_mod_cast hd_pos
  have hlog_nn : (0 : ℝ) ≤ Real.log (1 + (m : ℝ)) :=
    Real.log_nonneg (by have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m; linarith)
  have hα_nn : (0 : ℝ) ≤ α :=
    mul_nonneg (by positivity)
      (add_nonneg (div_nonneg (Nat.cast_nonneg _) hd_min_pos_real.le) hlog_nn)
  have hbm_div_ge : (2731 : ℝ) ≤ b * (m : ℝ) / (d_min : ℝ) := by
    rw [le_div_iff₀ hd_min_pos_real]; linarith
  have hα_ge : (2731 : ℝ) ≤ α := by
    have hmd_nn : (0 : ℝ) ≤ (m : ℝ) / (d_min : ℝ) :=
      div_nonneg (Nat.cast_nonneg m) hd_min_pos_real.le
    have h1 : b * (m : ℝ) / (d_min : ℝ) ≤ α := by
      have hb_le : b ≤ (2 ^ 21 : ℝ) := by rw [hb_def]; norm_num
      calc b * (m : ℝ) / (d_min : ℝ) = b * ((m : ℝ) / (d_min : ℝ)) := by ring
        _ ≤ (2 ^ 21 : ℝ) * ((m : ℝ) / (d_min : ℝ)) :=
              mul_le_mul_of_nonneg_right hb_le hmd_nn
        _ ≤ (2 ^ 21 : ℝ) * ((m : ℝ) / (d_min : ℝ) + Real.log (1 + (m : ℝ))) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity); linarith [hlog_nn]
        _ = α := by rw [hα_def]
    linarith [hbm_div_ge]
  -- Sum condition: α ≤ ∑_{ℓ=0}^J φ = (J+1)·φ.
  have hsum_const2 : (∑ _ℓ ∈ Finset.range (J + 1), φ) = ((J + 1 : ℕ) : ℝ) * φ := by
    simp [Finset.sum_const, Finset.card_range]
  have hJ_bound : α ≤ ∑ _ℓ ∈ Finset.range (J + 1), φ := by
    rw [hsum_const2]
    have hJ_ge : α / φ ≤ (J : ℝ) := Nat.le_ceil _
    have hJ_succ_ge : α / φ ≤ ((J + 1 : ℕ) : ℝ) := by push_cast; linarith
    have : α / φ * φ ≤ ((J + 1 : ℕ) : ℝ) * φ := mul_le_mul_of_nonneg_right hJ_succ_ge hφ_nn
    rwa [div_mul_cancel₀ _ (ne_of_gt hφ_pos)] at this
  -- Threshold for `upper_bound_window_conductance`: 2^21·(m/d_min) ≤ ∑φ.
  have hJ_bound_general : (2 ^ 21 : ℝ) * ((m : ℝ) / d_min) ≤ ∑ _ℓ ∈ Finset.range (J + 1), φ := by
    calc (2 ^ 21 : ℝ) * ((m : ℝ) / d_min)
        ≤ (2 ^ 21 : ℝ) * ((m : ℝ) / d_min + Real.log (1 + (m : ℝ))) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity); linarith [hlog_nn]
      _ = α := by rw [hα_def]
      _ ≤ ∑ _ℓ ∈ Finset.range (J + 1), φ := hJ_bound
  -- Apply upper_bound_window_conductance with constant Δ_j = Δ, φ_j = φ.
  have hUB := upper_bound_window_conductance_abstract G vm
    (fun _ => Δ) (fun _ => hΔ_ge1)
    (fun _ => φ) (fun _ => hφ_nn) (fun _ => hφ_le1)
    hwin J hJ_bound_general
  have hsum_eq : (∑ _j ∈ Finset.range (J + 1), Δ) = (J + 1) * Δ := by
    simp [Finset.sum_const, Finset.card_range, Nat.succ_mul]
  -- From hφ_div_gt: φ/Δ > (127/128)·Φt, i.e. 127·Δ·Φt < 128·φ.
  have hΔφ_Φt : 127 * ((Δ : ℝ) * Φt) < 128 * φ := by
    have hlt : 127 / 128 * Φt < φ / (Δ : ℝ) := hφ_div_gt
    have h := (lt_div_iff₀ hΔ_pos_real).mp hlt
    linarith
  -- Key arithmetic (real, no rounding): (J+1)·Δ ≤ (128/127 + 1/512)·α/Φt.
  have hreal_bound : (((J + 1) * Δ : ℕ) : ℝ) ≤ 128 / 127 * α / Φt + 1 / 512 * α / Φt := by
      have hLHS_eq : (((J + 1) * Δ : ℕ) : ℝ) = ((J : ℝ) + 1) * (Δ : ℝ) := by push_cast; ring
      have hJ_le : (J : ℝ) ≤ α / φ + 1 := by
        have hfloor : (⌊α / φ⌋₊ : ℝ) ≤ α / φ :=
          Nat.floor_le (div_nonneg hα_nn hφ_nn)
        have : (J : ℝ) ≤ ⌊α / φ⌋₊ + 1 := by
          exact_mod_cast Nat.ceil_le_floor_add_one _
        linarith
      have hstep1 : ((J : ℝ) + 1) * (Δ : ℝ) ≤ (α / φ + 2) * (Δ : ℝ) := by
        have : (J : ℝ) + 1 ≤ α / φ + 2 := by linarith
        exact mul_le_mul_of_nonneg_right this hΔ_pos_real.le
      have hexpand : (α / φ + 2) * (Δ : ℝ) = α * (Δ : ℝ) / φ + 2 * (Δ : ℝ) := by
        field_simp
      have hαΔφ : α * (Δ : ℝ) / φ ≤ 128 / 127 * α / Φt := by
        rw [div_le_div_iff₀ hφ_pos hΦt_pos]
        nlinarith [mul_le_mul_of_nonneg_left hΔφ_Φt.le hα_nn]
      have h2Δ : (2 : ℝ) * (Δ : ℝ) ≤ 1 / 512 * α / Φt := by
        rw [le_div_iff₀ hΦt_pos]
        have hbnd : (Δ : ℝ) * Φt < 128 / 127 := by
          have hφ1 : 128 * φ ≤ 128 := by linarith
          linarith
        nlinarith [hα_ge]
      have hcombine : (α / φ + 2) * (Δ : ℝ) ≤ 128 / 127 * α / Φt + 1 / 512 * α / Φt := by
        rw [hexpand]
        linarith
      rw [hLHS_eq]
      linarith
  -- Fold the log term via `log_one_add_m_le_m_div_d_min` (`log(1+m) ≤ (49/50)·m/d_min`):
  -- (128/127 + 1/512)·(1 + 49/50)·2^21 ≤ 2^22.
  have hCbound : 128 / 127 * α / Φt + 1 / 512 * α / Φt
      ≤ (2 : ℝ) ^ 22 * (m : ℝ) / ((d_min : ℝ) * Φt) := by
    have hlog_le := _root_.VoterModel.log_one_add_m_le_m_div_d_min G d_min hd hd_pos
    have hmd_nn : (0 : ℝ) ≤ (m : ℝ) / (d_min : ℝ) :=
      div_nonneg (Nat.cast_nonneg m) hd_min_pos_real.le
    have hA_le_B : (128 / 127 + 1 / 512) * α ≤ (2 : ℝ) ^ 22 * ((m : ℝ) / d_min) := by
      rw [hα_def]
      nlinarith [hlog_le, hmd_nn]
    calc 128 / 127 * α / Φt + 1 / 512 * α / Φt
        = (128 / 127 + 1 / 512) * α / Φt := by ring
      _ ≤ (2 : ℝ) ^ 22 * ((m : ℝ) / d_min) / Φt := by
          rw [div_le_div_iff₀ hΦt_pos hΦt_pos]
          exact mul_le_mul_of_nonneg_right hA_le_B (le_of_lt hΦt_pos)
      _ = (2 : ℝ) ^ 22 * (m : ℝ) / ((d_min : ℝ) * Φt) := by ring
  -- Combine: the bound set in `upper_bound_window_conductance`'s conclusion is a subset of ours.
  have hreal_total : (((J + 1) * Δ : ℕ) : ℝ) ≤
      (2 : ℝ) ^ 22 * (m : ℝ) / ((d_min : ℝ) * Φt) := le_trans hreal_bound hCbound
  rw [show (0.5 : ℝ≥0) = 1 / 2 by norm_num] at hUB
  refine le_trans hUB ?_
  apply ENNReal.toReal_mono (measure_ne_top (vm.μ : Measure Ω) _)
  refine (vm.μ : Measure Ω).mono ?_
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  -- `hω : consensusTime ω ≤ ↑(∑Δ)` in `ℕ∞`; goal compares the `ℝ≥0∞`-cast with `ofReal C`.
  have hk : ((∑ _j ∈ Finset.range (J + 1), Δ : ℕ) : ℝ) ≤
      (2 : ℝ) ^ 22 * (m : ℝ) / ((d_min : ℝ) * Φt) := by rw [hsum_eq]; exact hreal_total
  calc (vm.consensusTime ω : ℝ≥0∞)
      ≤ ((↑(∑ _j ∈ Finset.range (J + 1), Δ) : ℕ∞) : ℝ≥0∞) := by exact_mod_cast hω
    _ = ENNReal.ofReal ((∑ _j ∈ Finset.range (J + 1), Δ : ℕ) : ℝ) := by
        rw [ENNReal.ofReal_natCast]; exact_mod_cast rfl
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ 22 * (m : ℝ) / ((d_min : ℝ) * Φt)) :=
        ENNReal.ofReal_le_ofReal hk
    -- Push `ENNReal.ofReal` through the division: naturals inject directly, only `Φt` stays real.
    _ = 2 ^ 22 * (m : ℝ≥0∞) / ((d_min : ℝ≥0∞) * ENNReal.ofReal Φt) := by
        rw [ENNReal.ofReal_div_of_pos (mul_pos hd_min_pos_real hΦt_pos),
          ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat,
          ENNReal.ofReal_mul hd_min_pos_real.le, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]

end TemporalGraph
