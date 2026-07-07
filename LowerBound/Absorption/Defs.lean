module

public import LowerBound.SubProcess
import LowerBound.ArcDecomposition
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Complex.ExponentialBounds
import LowerBound.Absorbing
public import VoterProcess.Absorption.Time
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Covering.Besicovitch

/-! ## Main results

Field-free absorption-time event inclusions, initial half-cut state
`halfCutLow`, block-count / boundary-delta definitions, and their
basic arithmetic/contiguous-arc lemmas. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

namespace TemporalGraph.VoterProcess.LowerBound

-- NeZero instance for staticCliqueGraph p.k in hstep signatures

/-! ### Absorption-time event inclusions (field-free, law-only)

These local set inclusions connect the honest ℕ∞ ceiling/floor survival events
directly via `absorptionTime`, using only ℕ∞/ℕ/ℝ threshold monotonicity. They
replace the former `T_abs`-cast bridge lemmas: a real-threshold inequality
between the two budgets yields the ℕ∞ inclusion of the survival events. -/

/-- If `Y < X` (with `0 ≤ Y`), surviving past `⌈X⌉₊` implies surviving past
`⌊Y⌋₊`, since `⌊Y⌋₊ < ⌈X⌉₊`. Field-free. -/
lemma setOf_ceil_le_subset_floor_lt {W : Type*} [Fintype W] [Nonempty W]
    [DecidableEq W] {G : TemporalGraph W} {Ω : Type*} [MeasurableSpace Ω]
    (vm : TemporalGraph.VoterModelAbstract G 2 Ω) {X Y : ℝ} (hY : 0 ≤ Y) (hYX : Y < X) :
    {ω | (⌈X⌉₊ : ℕ∞) ≤ vm.absorptionTime ω} ⊆ {ω | (⌊Y⌋₊ : ℕ∞) < vm.absorptionTime ω} := by
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  have hlt : (⌊Y⌋₊ : ℕ∞) < (⌈X⌉₊ : ℕ∞) := by
    have hr : (⌊Y⌋₊ : ℝ) < (⌈X⌉₊ : ℝ) :=
      lt_of_le_of_lt (Nat.floor_le hY) (lt_of_lt_of_le hYX (Nat.le_ceil X))
    exact_mod_cast hr
  exact lt_of_lt_of_le hlt hω

/-- If `Y₂ ≤ Y₁`, surviving past `⌊Y₁⌋₊` implies surviving past `⌊Y₂⌋₊`,
since `⌊Y₂⌋₊ ≤ ⌊Y₁⌋₊`. Field-free. -/
lemma setOf_floor_lt_mono {W : Type*} [Fintype W] [Nonempty W]
    [DecidableEq W] {G : TemporalGraph W} {Ω : Type*} [MeasurableSpace Ω]
    (vm : TemporalGraph.VoterModelAbstract G 2 Ω) {Y₁ Y₂ : ℝ} (h : Y₂ ≤ Y₁) :
    {ω | (⌊Y₁⌋₊ : ℕ∞) < vm.absorptionTime ω} ⊆ {ω | (⌊Y₂⌋₊ : ℕ∞) < vm.absorptionTime ω} := by
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  exact lt_of_le_of_lt (by exact_mod_cast Nat.floor_le_floor h) hω

/-- The initial state `s₀`: all vertices in the first `z/2` blocks.
In the paper's notation, `s₀ = V₁ ∪ … ∪ V_{z/2}` (1-indexed). -/
def halfCutLow (p : Params) : Finset (VertexSet p) :=
  Finset.univ.filter fun v => v.1.val < p.z / 2

/-- The block-count process: `W j ω = #{i | block i ⊆ A(j·T, ω)}`.

Starting from `halfCutLow`, `W 0 = z/2`. Under the coupling argument, `W` behaves
as an unbiased ±1 random walk: in each interval I_j the active K_{2k} absorbs (by
`berenbrink_step_bound_pmf` + `geometric_boundary_bound_pmf_static`), flipping exactly one block's opinion with equal
probability. The voter model has absorbed iff `W` hits `{0, z}`. -/
def blockCount (p : Params) {Ω : Type} [MeasurableSpace Ω]
    (vm : TemporalGraph.VoterModelAbstract (lowerBoundGraph p) 2 Ω) (j : ℕ) (ω : Ω) : ℕ :=
  (Finset.univ.filter fun i : Fin p.z => block p i ⊆ vm.opinionZeroSet (j * p.T) ω).card

/-- `W 0 = z/2` under the `halfCutLow` initial condition.

Block `i` is entirely in opinion 0 iff `i.val < z/2`, so the count equals
`#{i : Fin p.z | i.val < p.z / 2} = p.z / 2`. -/
theorem blockCount_initial (p : Params) {Ω : Type} [MeasurableSpace Ω]
    (vm : TemporalGraph.VoterModelAbstract (lowerBoundGraph p) 2 Ω)
    {ω : Ω} (hA₀ : vm.opinionZeroSet 0 ω = halfCutLow p) :
    blockCount p vm 0 ω = p.z / 2 := by
  show (Finset.univ.filter fun i : Fin p.z => block p i ⊆ vm.opinionZeroSet (0 * p.T) ω).card = p.z / 2
  rw [Nat.zero_mul, hA₀]
  -- Goal: #{i : Fin p.z | block p i ⊆ halfCutLow p} = p.z / 2.
  -- block p i ⊆ halfCutLow p ↔ i.val < p.z / 2 (since block i = column i).
  have hblock_iff : ∀ i : Fin p.z,
      block p i ⊆ halfCutLow p ↔ i.val < p.z / 2 := by
    intro i
    constructor
    · intro hsub
      have hmem : (i, ⟨0, p.hk_pos⟩) ∈ block p i := by
        simp [block, Finset.mem_image]
      exact (Finset.mem_filter.mp (hsub hmem)).2
    · intro hi v hv
      simp only [halfCutLow, Finset.mem_filter, Finset.mem_univ, true_and]
      exact (mem_block p i v).mp hv ▸ hi
  simp_rw [hblock_iff]
  rw [Fin.card_filter_val_lt, min_eq_right (Nat.div_le_self p.z 2)]

/-- Active-parity anchors with mixed seam in `S`.

`activeMixed p j S` is the set of anchors `a : Fin p.z` whose parity matches `j`
(i.e. `a.val % 2 = j % 2`) and whose seam `block a ∪ block (a+1)` is *mixed* in `S`,
meaning neither fully contained in `S` nor disjoint from `S`. These are exactly the
boundary anchors that contribute to the per-interval boundary increment `W̃`. -/
def activeMixed (p : Params) (j : ℕ) (S : Finset (VertexSet p)) :
    Finset (Fin p.z) :=
  Finset.univ.filter (fun a : Fin p.z => a.val % 2 = j % 2 ∧
    ¬ (block p a ∪ block p (a + 1) ⊆ S ∨ Disjoint (block p a ∪ block p (a + 1)) S))

/-- Per-interval boundary increment `Δ_j(S, S')`.

For a contiguous arc `S` and any `S'`, this is the signed count of active mixed-seam
anchors whose clique restriction in `S'` is either `univ` (contributes `+1`) or empty
(contributes `−1`). Outside the contiguous-arc regime the increment is set to `0`. -/
noncomputable def boundaryDelta (p : Params) (j : ℕ)
    (S S' : Finset (VertexSet p)) : ℝ :=
  @ite ℝ (IsContiguousArc p S) (Classical.dec _)
    (∑ a ∈ activeMixed p j S,
      ((if cliqueRestrict p a S' = Finset.univ then (1 : ℝ) else 0) -
        (if cliqueRestrict p a S' = ∅ then (1 : ℝ) else 0)))
    0

/-- Accumulated boundary-increment process `W̃_j`.

Starts at `p.z / 2` and accumulates `boundaryDelta p j` between consecutive boundary
times. Adapted to `boundaryFiltration p vm` (proved downstream). -/
noncomputable def boundaryDeltaProcess (p : Params) {Ω : Type}
    [MeasurableSpace Ω] (vm : TemporalGraph.VoterModelAbstract (lowerBoundGraph p) 2 Ω) :
    ℕ → Ω → ℝ
  | 0, _ => ((p.z / 2 : ℕ) : ℝ)
  | (j + 1), ω => boundaryDeltaProcess p vm j ω +
      boundaryDelta p j (vm.opinionZeroSet (j * p.T) ω) (vm.opinionZeroSet ((j + 1) * p.T) ω)


/-- For the lower-bound graph, the minority set is empty iff the state is `∅`
or `Finset.univ` (consensus). This is a structural fact about regular graphs:
since all vertices have the same positive degree, `vol(S) = (2k-1)·#S`. -/
theorem minoritySet_lowerBoundGraph_eq_empty_iff (p : Params) (t : ℕ)
    (S : Finset (VertexSet p)) :
    VoterModel.minoritySet (lowerBoundGraph p) t S = ∅ ↔
      S = ∅ ∨ S = Finset.univ := by
  -- volume(U) = (2k-1) · #U in the (2k-1)-regular lower-bound graph
  have hdeg : ∀ v : VertexSet p,
      ((lowerBoundGraph p).snapshot t).degree v = 2 * p.k - 1 := by
    intro v
    have h := lowerBoundGraph_degree p t v
    -- TemporalGraph.degree unfolds to SimpleGraph.degree on graph t
    show ((lowerBoundGraph p).snapshot t).degree v = 2 * p.k - 1
    exact h
  have hvol_eq : ∀ (U : Finset (VertexSet p)),
      TemporalGraph.volume (lowerBoundGraph p) t U = (2 * p.k - 1) * U.card := by
    intro U
    simp only [TemporalGraph.volume, SimpleGraph.volume]
    rw [Finset.sum_congr rfl (fun v _ => hdeg v)]
    rw [Finset.sum_const, smul_eq_mul]
    ring
  have h2k_pos : 0 < 2 * p.k - 1 := by
    have hk : 1 ≤ p.k := p.hk_pos
    omega
  unfold VoterModel.minoritySet
  rw [hvol_eq S, hvol_eq (Finset.univ \ S)]
  constructor
  · intro h
    split_ifs at h with hcase
    · left; exact h
    · right
      exact le_antisymm (Finset.subset_univ _)
        (Finset.sdiff_eq_empty_iff_subset.mp h)
  · rintro (hS | hS)
    · subst hS
      simp
    · subst hS
      -- After subst: goal is the if-then-else with S = univ.
      have hsdiff : (Finset.univ : Finset (VertexSet p)) \ Finset.univ = ∅ :=
        Finset.sdiff_self _
      have hcard_univ_pos : 0 < (Finset.univ : Finset (VertexSet p)).card := by
        rw [Finset.card_univ]
        exact Fintype.card_pos
      have hne : ¬ (2 * p.k - 1) * (Finset.univ : Finset (VertexSet p)).card ≤
          (2 * p.k - 1) * (Finset.univ \ Finset.univ : Finset (VertexSet p)).card := by
        rw [hsdiff]
        simp only [Finset.card_empty, Nat.mul_zero, not_le]
        exact Nat.mul_pos h2k_pos hcard_univ_pos
      rw [if_neg hne, hsdiff]

/-- Helper (c) – voter absorption time dominates `T · (block-count hitting time)`.

If the voter model has absorbed strictly before interval boundary `j` (i.e.
`absorptionTime ω < ⌈T·j⌉₊ = T·j`), then by a.e. permanence the minority set is
empty at `j·T`, hence `blockCount p vm j ω = 0 ∨ blockCount p vm j ω = p.z`.
Stated a.e. (over `vm.μ`) since permanence is a.e. -/
theorem absorptionTime_lt_implies_blockCount_boundary (p : Params)
    {Ω : Type} [MeasurableSpace Ω]
    (vm : TemporalGraph.VoterModelAbstract (lowerBoundGraph p) 2 Ω) (j : ℕ) :
    {ω | vm.absorptionTime ω < (⌈(p.T : ℝ) * j⌉₊ : ℕ∞)} ≤ᵐ[(vm.μ : Measure Ω)]
      {ω | ∃ i ≤ j, blockCount p vm i ω = 0 ∨ blockCount p vm i ω = p.z} := by
  have hfix := lowerBoundGraph_fixedDegrees p
  filter_upwards
    [TemporalGraph.VoterModelAbstract.ae_minoritySet_empty_of_absorptionTime_le
      (G := (lowerBoundGraph p).withFixed hfix) vm]
    with ω hperm hω
  -- After `filter_upwards`, membership is in applied form; read off the predicate.
  replace hω : vm.absorptionTime ω < (⌈(p.T : ℝ) * (j : ℝ)⌉₊ : ℕ∞) := hω
  -- `⌈(p.T:ℝ)*j⌉₊ = p.T * j` since `(p.T:ℝ)*j = ((p.T*j : ℕ):ℝ)`.
  have hceil : (⌈(p.T : ℝ) * (j : ℝ)⌉₊ : ℕ) = p.T * j := by
    rw [show (p.T : ℝ) * (j : ℝ) = ((p.T * j : ℕ) : ℝ) by push_cast; ring, Nat.ceil_natCast]
  rw [hceil] at hω
  -- `absorptionTime ω ≤ (j*p.T : ℕ∞)`, then a.e. permanence gives emptiness at `j*T`.
  have hle : vm.absorptionTime ω ≤ ((j * p.T : ℕ) : ℕ∞) := by
    have hlt' : vm.absorptionTime ω ≤ ((p.T * j : ℕ) : ℕ∞) := le_of_lt hω
    rwa [Nat.mul_comm p.T j] at hlt'
  have hperm' := hperm (j * p.T) hle
  -- hperm' : minoritySet G (j*T) (vm.opinionZeroSet (j*T) ω) = ∅
  rcases (minoritySet_lowerBoundGraph_eq_empty_iff p (j * p.T) (vm.opinionZeroSet (j * p.T) ω)).mp hperm'
    with hA_empty | hA_univ
  · -- A = ∅ ⟹ blockCount = 0
    refine ⟨j, le_refl _, Or.inl ?_⟩
    show (Finset.univ.filter fun i : Fin p.z => block p i ⊆ vm.opinionZeroSet (j * p.T) ω).card = 0
    rw [hA_empty]
    -- block p i ⊆ ∅ iff block p i = ∅, which is false (block has card k ≥ 1)
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _ hsub
    have hsub_eq : block p i = ∅ := Finset.subset_empty.mp hsub
    have : (block p i).card = 0 := by rw [hsub_eq]; rfl
    rw [card_block] at this
    exact absurd this (Nat.pos_iff_ne_zero.mp p.hk_pos)
  · -- A = univ ⟹ blockCount = p.z
    refine ⟨j, le_refl _, Or.inr ?_⟩
    show (Finset.univ.filter fun i : Fin p.z => block p i ⊆ vm.opinionZeroSet (j * p.T) ω).card = p.z
    rw [hA_univ]
    -- every block ⊆ univ
    have hall : (Finset.univ.filter fun i : Fin p.z => block p i ⊆ Finset.univ) =
        Finset.univ := by
      apply Finset.filter_eq_self.mpr
      intro i _
      exact Finset.subset_univ _
    rw [hall, Finset.card_univ, Fintype.card_fin]

/-- The threshold `α := alphaOf p` chosen so that `1 - 2⁻ᵅ ≥ 1 - 1/p.z³`.

Conceptually `α = ⌈3 log₂ p.z⌉` (the paper's Claim 2 choice). We package its
existence (along with the two properties we need) into a single existential to
keep the arithmetic side quest contained. -/
theorem exists_alpha_witness (Γ : ℕ) (p : Params)
    (hz20 : 20 ≤ p.z)
    (hTbound : (10 : ℝ) * Γ * p.k * Real.log p.z ≤ (p.T : ℝ)) :
    ∃ α : ℕ, 1 ≤ α ∧ ((1 : ℝ) / 2) ^ α ≤ 1 / (p.z : ℝ) ^ 3 ∧
      Γ * α * p.k ≤ p.T := by
  -- Take `α := ⌈3 * logb 2 z⌉`. We verify the three required properties.
  -- Useful real-analytic facts about `z`.
  have hz_pos : (0 : ℝ) < (p.z : ℝ) := by exact_mod_cast p.hz_pos
  have hz_ge20R : (20 : ℝ) ≤ (p.z : ℝ) := by exact_mod_cast hz20
  have h_logz_pos : 0 < Real.log p.z := by
    apply Real.log_pos
    have : (1 : ℝ) < 20 := by norm_num
    linarith
  have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h_log2_gt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  -- `log z ≥ 2 log 2` from `z ≥ 20 ≥ 4`.
  have h_logz_ge : 2 * Real.log 2 ≤ Real.log p.z := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      ring
    have h4lez : Real.log 4 ≤ Real.log p.z := by
      apply Real.log_le_log (by norm_num)
      linarith
    linarith
  have h_logz_ge_one : (1 : ℝ) ≤ Real.log p.z := by
    have : (1 : ℝ) ≤ 2 * Real.log 2 := by linarith
    linarith
  -- `3 * logb 2 z ≥ 0` since `z ≥ 1`.
  have h_logb_nonneg : 0 ≤ Real.logb 2 p.z := by
    apply Real.logb_nonneg (by norm_num)
    linarith
  have h_3logb_nonneg : 0 ≤ (3 : ℝ) * Real.logb 2 p.z := by positivity
  -- `3 * logb 2 z ≥ 3 * logb 2 20 ≥ 3 * 2 = 6 ≥ 1`.
  have h_3logb_ge_six : (6 : ℝ) ≤ 3 * Real.logb 2 p.z := by
    -- `logb 2 z = log z / log 2 ≥ 2 log 2 / log 2 = 2`.
    have h_logb_ge_two : (2 : ℝ) ≤ Real.logb 2 p.z := by
      unfold Real.logb
      rw [le_div_iff₀ h_log2_pos]
      linarith
    linarith
  set α : ℕ := ⌈(3 : ℝ) * Real.logb 2 p.z⌉₊ with hα_def
  refine ⟨α, ?_, ?_, ?_⟩
  -- Goal 1: `1 ≤ α`.
  · have : (1 : ℕ) ≤ ⌈(3 : ℝ) * Real.logb 2 p.z⌉₊ := by
      rw [Nat.one_le_iff_ne_zero, Ne, Nat.ceil_eq_zero, not_le]
      linarith
    exact this
  -- Goal 2: `(1/2)^α ≤ 1/z³`.
  · -- Equivalent to `z³ ≤ 2^α`, which follows from `α ≥ 3 * logb 2 z`.
    have hz_cube_pos : (0 : ℝ) < (p.z : ℝ) ^ 3 := by positivity
    have h_two_pos : (0 : ℝ) < 2 := by norm_num
    have h_two_ne_one : (2 : ℝ) ≠ 1 := by norm_num
    have h_one_lt_two : (1 : ℝ) < 2 := by norm_num
    -- `α ≥ 3 * logb 2 z`.
    have hα_ge : (3 : ℝ) * Real.logb 2 p.z ≤ (α : ℝ) := Nat.le_ceil _
    -- `(2 : ℝ)^(3 * logb 2 z) = z^3`.
    have h_rpow_eq : (2 : ℝ) ^ ((3 : ℝ) * Real.logb 2 p.z) = (p.z : ℝ) ^ 3 := by
      rw [mul_comm, Real.rpow_mul h_two_pos.le, Real.rpow_logb h_two_pos h_two_ne_one hz_pos]
      norm_num
    -- `(2 : ℝ)^(α : ℝ) ≥ z^3`.
    have h_rpow_le : (p.z : ℝ) ^ 3 ≤ (2 : ℝ) ^ ((α : ℕ) : ℝ) := by
      rw [← h_rpow_eq]
      exact Real.rpow_le_rpow_of_exponent_le h_one_lt_two.le hα_ge
    -- Convert to natural-number power.
    have h_two_pow_eq : (2 : ℝ) ^ ((α : ℕ) : ℝ) = (2 : ℝ) ^ α := by
      rw [Real.rpow_natCast]
    rw [h_two_pow_eq] at h_rpow_le
    -- Now `(1/2)^α = 1 / 2^α ≤ 1 / z^3`.
    have h_two_pow_pos : (0 : ℝ) < (2 : ℝ) ^ α := by positivity
    rw [one_div_pow, one_div, one_div]
    rw [inv_le_inv₀ h_two_pow_pos hz_cube_pos]
    exact h_rpow_le
  -- Goal 3: `Γ * α * k ≤ T`.
  · -- We show `(Γ * α * k : ℝ) ≤ (p.T : ℝ)` then cast back.
    rw [show (Γ * α * p.k : ℕ) = (Γ * α * p.k : ℕ) from rfl]
    -- Push to ℝ.
    have hgoal_real : ((Γ * α * p.k : ℕ) : ℝ) ≤ (p.T : ℝ) := by
      push_cast
      -- `α ≤ 3 * logb 2 z + 1` from `Nat.ceil_lt_add_one`.
      have hα_lt : (α : ℝ) < 3 * Real.logb 2 p.z + 1 := by
        have := Nat.ceil_lt_add_one h_3logb_nonneg
        exact_mod_cast this
      have hα_le : (α : ℝ) ≤ 3 * Real.logb 2 p.z + 1 := hα_lt.le
      -- `3 * logb 2 z + 1 ≤ 6 * log z`.
      -- `3 * logb 2 z = 3 * log z / log 2`. We need:
      --   `3 * log z / log 2 + 1 ≤ 6 * log z`
      -- ⟺ `3 * log z + log 2 ≤ 6 * log z * log 2` (multiplying by log 2 > 0)
      -- ⟺ `log 2 ≤ (6 * log 2 - 3) * log z`.
      -- Since `log z ≥ 2 * log 2 > 1.38` and `6 * log 2 - 3 > 1.15`,
      -- RHS ≥ `1.15 * 1.38 > 1.59` > `log 2 ≈ 0.69`.
      have h_α_le_6logz : (α : ℝ) ≤ 6 * Real.log p.z := by
        have h_logb : Real.logb 2 p.z = Real.log p.z / Real.log 2 := rfl
        rw [h_logb] at hα_le
        -- Multiply through by log 2.
        have h_step : (α : ℝ) * Real.log 2 ≤ 3 * Real.log p.z + Real.log 2 := by
          have := mul_le_mul_of_nonneg_right hα_le h_log2_pos.le
          calc (α : ℝ) * Real.log 2
              ≤ (3 * (Real.log p.z / Real.log 2) + 1) * Real.log 2 := this
            _ = 3 * Real.log p.z + Real.log 2 := by
                field_simp
        -- We want `α * log 2 ≤ 6 * log z * log 2`, i.e.
        -- `3 * log z + log 2 ≤ 6 * log z * log 2`.
        have h_aux : 3 * Real.log p.z + Real.log 2 ≤ 6 * Real.log p.z * Real.log 2 := by
          nlinarith [h_log2_gt, h_logz_ge, h_log2_pos, h_logz_pos]
        have h_α_log2 : (α : ℝ) * Real.log 2 ≤ 6 * Real.log p.z * Real.log 2 := by
          linarith
        -- Cancel log 2 > 0.
        have := (mul_le_mul_iff_of_pos_right h_log2_pos).mp h_α_log2
        linarith
      -- `Γ * α * k ≤ Γ * (6 * log z) * k ≤ Γ * (10 * log z) * k = 10 * Γ * k * log z ≤ T`.
      have hΓ_nn : (0 : ℝ) ≤ (Γ : ℝ) := by positivity
      have hk_nn : (0 : ℝ) ≤ (p.k : ℝ) := by positivity
      have h1 : (Γ : ℝ) * (α : ℝ) * (p.k : ℝ)
          ≤ (Γ : ℝ) * (6 * Real.log p.z) * (p.k : ℝ) := by
        have := mul_le_mul_of_nonneg_left h_α_le_6logz hΓ_nn
        nlinarith [this, hk_nn]
      have h_prod_nn : (0 : ℝ) ≤ (Γ : ℝ) * (p.k : ℝ) * Real.log p.z := by
        positivity
      have h2 : (Γ : ℝ) * (6 * Real.log p.z) * (p.k : ℝ)
          ≤ 10 * (Γ : ℝ) * (p.k : ℝ) * Real.log p.z := by
        have : (Γ : ℝ) * (6 * Real.log p.z) * (p.k : ℝ)
            = 6 * ((Γ : ℝ) * (p.k : ℝ) * Real.log p.z) := by ring
        rw [this]
        have : (10 : ℝ) * (Γ : ℝ) * (p.k : ℝ) * Real.log p.z
            = 10 * ((Γ : ℝ) * (p.k : ℝ) * Real.log p.z) := by ring
        rw [this]
        linarith [h_prod_nn]
      linarith [h1, h2, hTbound]
    exact_mod_cast hgoal_real

-- `IsContiguousArc` is defined in `Defs.lean`; `halfCutLow_isContiguousArc` proved here
-- since `halfCutLow` is defined in this file.

theorem halfCutLow_isContiguousArc (p : Params) :
    IsContiguousArc p (halfCutLow p) :=
  ⟨⟨0, p.hz_pos⟩, p.z / 2, Nat.div_le_self p.z 2, by
    ext v
    simp only [halfCutLow, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_biUnion, Finset.mem_range, mem_block]
    constructor
    · intro hv
      exact ⟨v.1.val, hv, Fin.ext (by simp [Nat.mod_eq_of_lt v.1.isLt])⟩
    · rintro ⟨i, hi, hvi⟩
      have hiz : i < p.z := Nat.lt_of_lt_of_le hi (Nat.div_le_self p.z 2)
      rw [Fin.ext_iff] at hvi
      simp only [Nat.zero_add, Nat.mod_eq_of_lt hiz] at hvi
      omega⟩

theorem blockCount_arc_zero_iff (p : Params) (S : Finset (VertexSet p))
    (h : IsContiguousArc p S) :
    (Finset.univ.filter fun i : Fin p.z => block p i ⊆ S).card = 0 ↔ S = ∅ := by
  obtain ⟨b, m, _hm, hS⟩ := h
  constructor
  · intro hcard
    by_contra hne
    have hempty : Finset.univ.filter (fun i : Fin p.z => block p i ⊆ S) = ∅ :=
      Finset.card_eq_zero.mp hcard
    have hm_pos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with rfl | hpos
      · simp [Finset.range_zero, Finset.biUnion_empty] at hS; exact absurd hS hne
      · exact hpos
    have hblock_sub : block p b ⊆ S := by
      rw [hS]; intro v hv; rw [mem_block] at hv
      exact Finset.mem_biUnion.mpr ⟨0, Finset.mem_range.mpr hm_pos, by
        rw [mem_block]; rw [hv]
        exact Fin.ext (by simp [Nat.mod_eq_of_lt b.isLt])⟩
    have hb_in : b ∈ Finset.univ.filter (fun i : Fin p.z => block p i ⊆ S) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hblock_sub⟩
    simp [hempty] at hb_in
  · rintro rfl
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _ hbi
    exact absurd (Finset.subset_empty.mp hbi)
      (Finset.nonempty_iff_ne_empty.mp ⟨(i, ⟨0, p.hk_pos⟩), (mem_block p i _).mpr rfl⟩)

theorem blockCount_z_iff (p : Params) (S : Finset (VertexSet p)) :
    (Finset.univ.filter fun i : Fin p.z => block p i ⊆ S).card = p.z ↔ S = Finset.univ := by
  constructor
  · intro hcard
    apply Finset.eq_univ_of_forall
    intro v
    have heq : Finset.univ.filter (fun i : Fin p.z => block p i ⊆ S) = Finset.univ :=
      Finset.eq_univ_of_card _ (by simp [Fintype.card_fin]; exact hcard)
    have hv1 : v.1 ∈ Finset.univ.filter (fun i : Fin p.z => block p i ⊆ S) := by
      rw [heq]; exact Finset.mem_univ _
    exact (Finset.mem_filter.mp hv1).2 ((mem_block p v.1 v).mpr rfl)
  · rintro rfl
    rw [Finset.filter_true_of_mem (fun _ _ => Finset.subset_univ _)]
    simp [Finset.card_univ, Fintype.card_fin]

/-- Helper for `contiguousArc_step_structure`, part 1: blockCount change bound.

For a contiguous arc `S` and interval `j`, every reachable `S'` (i.e., with
`opinionProcess₂ (j*T) T S S' ≠ 0`) differs in blockCount by at most 2.

Mathematically: in interval `I_j`, `lowerBoundGraph` is a disjoint union of K_{2k}
cliques `block a ∪ block (a+1)` for anchors `a` with `a.val % 2 = j % 2`. Vertices
not in any active clique are isolated, so their opinion is preserved by `stepDist₂`
(`nextOpinionDist₂_eq_pure_of_not_nonempty`). For an arc `S = ⋃ block(b+i)`, only
the (at most two) boundary cliques are mixed; interior active cliques start at
consensus (block-aligned consensus is preserved by the synchronous voter model on
the K_{2k}). Hence `block i ⊆ S` can change only for the ≤ 2 blocks per boundary
clique pair, and the blockCount changes by at most 2.

Formalising this requires:
- `stepDist₂` preservation for vertices in non-active edges (isolated case);
- `stepDist₂` preservation of block-aligned consensus on active cliques (interior case);
- inductive lift to `opinionProcess₂` over `p.T` steps.
This infrastructure is not yet in the project; deferred. -/
theorem contiguousArc_blockCount_diff_le_two (p : Params) (j : ℕ)
    (S S' : Finset (VertexSet p)) (hS : IsContiguousArc p S)
    (hop : VoterModel.opinionProcess₂ (lowerBoundGraph p) (j * p.T) p.T S S' ≠ 0) :
    |(((Finset.univ.filter (block p · ⊆ S')).card : ℤ) -
      ((Finset.univ.filter (block p · ⊆ S)).card : ℤ))| ≤ 2 := by
  -- Local helpers (private in ArcDecomposition.lean, reproduced here)
  have local_block_ne : ∀ c : Fin p.z, (block p c).Nonempty :=
    fun c => ⟨(c, ⟨0, p.hk_pos⟩), (mem_block p c _).mpr rfl⟩
  have local_arc_dichotomy : ∀ c : Fin p.z, block p c ⊆ S ∨ Disjoint (block p c) S := by
    obtain ⟨b, m, _hm, hS_eq⟩ := hS; intro c
    by_cases hex : ∃ i ∈ Finset.range m,
        c = (⟨(b.val + i) % p.z, Nat.mod_lt _ p.hz_pos⟩ : Fin p.z)
    · left; obtain ⟨i, hi, hci⟩ := hex; intro v hv; rw [mem_block] at hv; rw [hS_eq]
      exact Finset.mem_biUnion.mpr ⟨i, hi, by rw [mem_block, hv, hci]⟩
    · right; refine Finset.disjoint_left.mpr fun v hvb hvS => hex ?_
      rw [hS_eq] at hvS; obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp hvS
      exact ⟨i, hi, by rw [mem_block] at hvb hvi; rw [← hvb, hvi]⟩
  -- `⟨(a.val+1)%p.z, _⟩ = a + 1` in Fin p.z
  have succ_eq : ∀ a : Fin p.z,
      (⟨(a.val + 1) % p.z, Nat.mod_lt _ p.hz_pos⟩ : Fin p.z) = a + 1 :=
    fun a => Fin.ext (by simp [Fin.val_add])
  -- Shared: `cliqueRestrict p a S'` has nonzero probability at S' given S reachable
  have hmap_ne_S' : ∀ a : Fin p.z, a.val % 2 = j % 2 →
      VoterModel.opinionProcess₂ (staticCliqueGraph p.k) 0 p.T (cliqueRestrict p a S)
        (cliqueRestrict p a S') ≠ 0 := by
    intro a ha
    have hmarg := opinionProcess₂_clique_marginal p a j p.T (le_refl _) ha S
    have hpos : 0 < VoterModel.opinionProcess₂ (lowerBoundGraph p) (j * p.T) p.T S S' :=
      lt_of_le_of_ne zero_le (Ne.symm hop)
    have hmap_ne : (VoterModel.opinionProcess₂ (lowerBoundGraph p) (j * p.T) p.T S).map
        (cliqueRestrict p a) (cliqueRestrict p a S') ≠ 0 := by
      rw [PMF.map_apply]; apply ne_of_gt; refine lt_of_lt_of_le hpos ?_
      have hle := ENNReal.le_tsum
        (f := fun a_1 => if cliqueRestrict p a S' = cliqueRestrict p a a_1 then
            VoterModel.opinionProcess₂ (lowerBoundGraph p) (j * p.T) p.T S a_1 else 0) S'
      rw [if_pos rfl] at hle
      refine hle.trans (le_of_eq ?_); congr 1; ext; split_ifs <;> rfl
    rwa [← hmarg]
  -- Same-case: Disjoint seam S → Disjoint seam S'
  have seam_disj_preserved : ∀ a : Fin p.z, a.val % 2 = j % 2 →
      Disjoint (block p a ∪ block p (a + 1)) S →
      Disjoint (block p a ∪ block p (a + 1)) S' := by
    intro a ha hdisj
    have hempty_cr : cliqueRestrict p a S = ∅ := by
      simp only [cliqueRestrict, cliqueFinset]
      rw [Finset.image_eq_empty]
      exact Finset.disjoint_iff_inter_eq_empty.mp hdisj.symm
    have hne := hmap_ne_S' a ha
    rw [hempty_cr, opinionProcess₂_empty_eq_pure, PMF.pure_apply] at hne
    have hempty_cr' : cliqueRestrict p a S' = ∅ := by
      split_ifs at hne with h; exact h; exact absurd rfl hne
    rw [Finset.disjoint_left]
    intro v hvseam hvS'
    have hmem := (mem_cliqueRestrict_iff p a S' v (by simp [cliqueFinset, hvseam])).mpr hvS'
    simp [hempty_cr'] at hmem
  -- Same-case: seam ⊆ S → seam ⊆ S'
  have seam_sub_preserved : ∀ a : Fin p.z, a.val % 2 = j % 2 →
      block p a ∪ block p (a + 1) ⊆ S → block p a ∪ block p (a + 1) ⊆ S' := by
    intro a ha hfull
    have huniv_cr : cliqueRestrict p a S = Finset.univ := by
      simp only [cliqueRestrict, cliqueFinset]
      rw [show S ∩ (block p a ∪ block p (a + 1)) = block p a ∪ block p (a + 1) from
            Finset.inter_eq_right.mpr hfull]
      simpa [cliqueFinset] using cliqueFinset_image_eq_univ p a
    have hne := hmap_ne_S' a ha
    rw [huniv_cr, opinionProcess₂_univ_eq_pure, PMF.pure_apply] at hne
    have huniv_cr' : cliqueRestrict p a S' = Finset.univ := by
      split_ifs at hne with h; exact h; exact absurd rfl hne
    intro v hvseam
    exact (mem_cliqueRestrict_iff p a S' v (by simp [cliqueFinset, hvseam])).mp
      (huniv_cr' ▸ Finset.mem_univ _)
  -- parity boolean and block-count filter sets
  let odd : Bool := decide (j % 2 = 1)
  let fS  := Finset.univ.filter (fun c : Fin p.z => block p c ⊆ S)
  let fS' := Finset.univ.filter (fun c : Fin p.z => block p c ⊆ S')
  let gained := fS' \ fS
  let lost   := fS  \ fS'
  show |(((fS' : Finset _).card : ℤ) - (fS : Finset _).card)| ≤ 2
  suffices hbd : gained.card ≤ 2 ∧ lost.card ≤ 2 by
    have hcard_eq : (fS'.card : ℤ) - fS.card = gained.card - lost.card := by
      have h1 : gained.card + (fS' ∩ fS).card = fS'.card :=
        Finset.card_sdiff_add_card_inter fS' fS
      have h2 : lost.card + (fS' ∩ fS).card = fS.card := by
        have := Finset.card_sdiff_add_card_inter fS fS'
        rwa [Finset.inter_comm] at this
      omega
    rw [hcard_eq, abs_le]
    have hg : (gained.card : ℤ) ≤ 2 := by exact_mod_cast hbd.1
    have hl : (lost.card : ℤ) ≤ 2 := by exact_mod_cast hbd.2
    constructor <;> omega
  -- Step 1: map c ↦ activeAnchor p odd c lands in seamMixedAnchors p S
  have gained_into_mixed : ∀ c ∈ gained, activeAnchor p odd c ∈ seamMixedAnchors p S := by
    intro c hcg
    simp only [gained, fS, fS', Finset.mem_sdiff, Finset.mem_filter,
      Finset.mem_univ, true_and] at hcg
    obtain ⟨hcsub', hcnsub⟩ := hcg
    have hdisj_c : Disjoint (block p c) S := (local_arc_dichotomy c).resolve_left hcnsub
    let a := activeAnchor p odd c
    have ha_par : a.val % 2 = parityNat odd := activeAnchor_parity p odd c
    have ha_jmod : a.val % 2 = j % 2 := activeAnchor_parity_jmod2 p j c
    have hc_or : c = a ∨ c = a + 1 := (activeAnchor_eq_iff_eq_or_succ p odd a c ha_par).mp rfl
    have hc_sub : block p c ⊆ block p a ∪ block p (a + 1) :=
      hc_or.elim (· ▸ Finset.subset_union_left) (· ▸ Finset.subset_union_right)
    rw [seamMixedAnchors, Finset.mem_filter, succ_eq]
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hcons
    rcases hcons with hfull | hdisj
    · -- seam ⊆ S and Disjoint (block c) S: pick v ∈ block c ⊆ seam ⊆ S, contradiction
      obtain ⟨v, hv⟩ := local_block_ne c
      exact absurd (hc_sub.trans hfull hv) (Finset.disjoint_left.mp hdisj_c hv)
    · -- Disjoint seam S → Disjoint seam S': block c ⊆ seam, pick v ∈ block c ⊆ S', contradiction
      have hdisj_seam' := seam_disj_preserved a ha_jmod hdisj
      obtain ⟨v, hv⟩ := local_block_ne c
      exact absurd (hcsub' hv) (Finset.disjoint_left.mp hdisj_seam' (hc_sub hv))
  have lost_into_mixed : ∀ c ∈ lost, activeAnchor p odd c ∈ seamMixedAnchors p S := by
    intro c hcl
    simp only [lost, fS, fS', Finset.mem_sdiff, Finset.mem_filter,
      Finset.mem_univ, true_and] at hcl
    obtain ⟨hcsub, hcnsub'⟩ := hcl
    let a := activeAnchor p odd c
    have ha_par : a.val % 2 = parityNat odd := activeAnchor_parity p odd c
    have ha_jmod : a.val % 2 = j % 2 := activeAnchor_parity_jmod2 p j c
    have hc_or : c = a ∨ c = a + 1 := (activeAnchor_eq_iff_eq_or_succ p odd a c ha_par).mp rfl
    have hc_sub : block p c ⊆ block p a ∪ block p (a + 1) :=
      hc_or.elim (· ▸ Finset.subset_union_left) (· ▸ Finset.subset_union_right)
    rw [seamMixedAnchors, Finset.mem_filter, succ_eq]
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hcons
    rcases hcons with hfull | hdisj
    · -- seam ⊆ S → seam ⊆ S': block c ⊆ seam ⊆ S', contradicts ¬ block c ⊆ S'
      exact absurd (hc_sub.trans (seam_sub_preserved a ha_jmod hfull)) hcnsub'
    · -- Disjoint seam S: block c ⊆ seam → Disjoint (block c) S, contradicts block c ⊆ S
      obtain ⟨v, hv⟩ := local_block_ne c
      exact absurd (hcsub hv) (Finset.disjoint_left.mp hdisj (hc_sub hv))
  -- Step 2: the map is injective on gained and lost
  have gained_inj : Set.InjOn (activeAnchor p odd) (gained : Set (Fin p.z)) := by
    intro c hcg c' hcg' heq
    set a := activeAnchor p odd c with ha_def
    have ha_par : a.val % 2 = parityNat odd := activeAnchor_parity p odd c
    have hc_or  : c  = a ∨ c  = a + 1 := (activeAnchor_eq_iff_eq_or_succ p odd a c  ha_par).mp rfl
    have hc'_or : c' = a ∨ c' = a + 1 :=
      (activeAnchor_eq_iff_eq_or_succ p odd a c' ha_par).mp heq.symm
    by_contra hne
    have hcc' : (c = a ∧ c' = a + 1) ∨ (c = a + 1 ∧ c' = a) := by
      rcases hc_or with hca | hca <;> rcases hc'_or with hca' | hca'
      · exact absurd (hca.trans hca'.symm) hne
      · exact Or.inl ⟨hca, hca'⟩
      · exact Or.inr ⟨hca, hca'⟩
      · exact absurd (hca.trans hca'.symm) hne
    have hcg_mem : c ∈ gained := hcg
    have hcg'_mem : c' ∈ gained := hcg'
    simp only [gained, fS, fS', Finset.mem_sdiff, Finset.mem_filter,
      Finset.mem_univ, true_and] at hcg_mem hcg'_mem
    have hdisj_c  : Disjoint (block p c)  S := (local_arc_dichotomy c).resolve_left hcg_mem.2
    have hdisj_c' : Disjoint (block p c') S := (local_arc_dichotomy c').resolve_left hcg'_mem.2
    have hdisj_seam : Disjoint (block p a ∪ block p (a + 1)) S := by
      rcases hcc' with ⟨hca, hca'⟩ | ⟨hca, hca'⟩
      · -- c = a, c' = a + 1
        rw [show block p a ∪ block p (a + 1) = block p c ∪ block p c' from by rw [hca, hca']]
        exact Finset.disjoint_union_left.mpr ⟨hdisj_c, hdisj_c'⟩
      · -- c = a + 1, c' = a
        rw [show block p a ∪ block p (a + 1) = block p c' ∪ block p c from by rw [hca, hca']]
        exact Finset.disjoint_union_left.mpr ⟨hdisj_c', hdisj_c⟩
    have hmixed := gained_into_mixed c (Finset.mem_coe.mp hcg)
    rw [seamMixedAnchors, Finset.mem_filter, succ_eq] at hmixed
    exact absurd (Or.inr hdisj_seam) hmixed.2
  have lost_inj : Set.InjOn (activeAnchor p odd) (lost : Set (Fin p.z)) := by
    intro c hcl c' hcl' heq
    set a := activeAnchor p odd c with ha_def
    have ha_par : a.val % 2 = parityNat odd := activeAnchor_parity p odd c
    have ha_jmod : a.val % 2 = j % 2 := activeAnchor_parity_jmod2 p j c
    have hc_or  : c  = a ∨ c  = a + 1 := (activeAnchor_eq_iff_eq_or_succ p odd a c  ha_par).mp rfl
    have hc'_or : c' = a ∨ c' = a + 1 :=
      (activeAnchor_eq_iff_eq_or_succ p odd a c' ha_par).mp heq.symm
    by_contra hne
    have hcc' : (c = a ∧ c' = a + 1) ∨ (c = a + 1 ∧ c' = a) := by
      rcases hc_or with hca | hca <;> rcases hc'_or with hca' | hca'
      · exact absurd (hca.trans hca'.symm) hne
      · exact Or.inl ⟨hca, hca'⟩
      · exact Or.inr ⟨hca, hca'⟩
      · exact absurd (hca.trans hca'.symm) hne
    have hcl_mem : c ∈ lost := hcl
    have hcl'_mem : c' ∈ lost := hcl'
    simp only [lost, fS, fS', Finset.mem_sdiff, Finset.mem_filter,
      Finset.mem_univ, true_and] at hcl_mem hcl'_mem
    have hsub_c  : block p c  ⊆ S := hcl_mem.1
    have hsub_c' : block p c' ⊆ S := hcl'_mem.1
    have hseam_sub : block p a ∪ block p (a + 1) ⊆ S := by
      rcases hcc' with ⟨hca, hca'⟩ | ⟨hca, hca'⟩
      · rw [show block p a ∪ block p (a + 1) = block p c ∪ block p c' from by rw [hca, hca']]
        exact Finset.union_subset hsub_c hsub_c'
      · rw [show block p a ∪ block p (a + 1) = block p c' ∪ block p c from by rw [hca, hca']]
        exact Finset.union_subset hsub_c' hsub_c
    have hseam_sub' : block p a ∪ block p (a + 1) ⊆ S' :=
      seam_sub_preserved a ha_jmod hseam_sub
    have hc'_sub_seam : block p c' ⊆ block p a ∪ block p (a + 1) :=
      hc'_or.elim (· ▸ Finset.subset_union_left) (· ▸ Finset.subset_union_right)
    exact absurd (hc'_sub_seam.trans hseam_sub') hcl'_mem.2
  -- Conclude: injection into seamMixedAnchors p S (card ≤ 2)
  constructor
  · exact le_trans (Finset.card_le_card_of_injOn (activeAnchor p odd) gained_into_mixed gained_inj)
      (arc_anchors_card_le_two p S hS)
  · exact le_trans (Finset.card_le_card_of_injOn (activeAnchor p odd) lost_into_mixed lost_inj)
      (arc_anchors_card_le_two p S hS)


end TemporalGraph.VoterProcess.LowerBound
