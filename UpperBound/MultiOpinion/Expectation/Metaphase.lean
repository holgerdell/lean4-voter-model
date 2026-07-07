module

public import UpperBound.MultiOpinion.Metaphase
import UpperBound.MultiOpinion.Markov
import VoterProcess.Expectation
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Positivity.Finset
import UpperBound.MultiOpinion.Expectation.GeomTail

/-! ## Main results

Metaphase block-count scaffolding for §3.4: the `VoterModelAbstract.metaphaseXi`
and `metaphaseBlockCount` defs, their measurability, opinion-set monotonicity,
the D2 conditional metaphase-increment bound, and the block-tail set machinery. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Classical ENNReal

noncomputable section

namespace TemporalGraph

/-! ### Metaphase block count `N_α` (D1-instantiation scaffolding)

The §3.4 "Proof of Theorem from Claim" groups the phases of metaphase `α` into
*blocks* of length `ξ_α`. `N_α` is the number of such blocks before the metaphase
ends. Two deterministic facts feed the probabilistic argument:

* `metaphaseBlockCount_succ_le_iff` — `{N_α ≥ k+1} = {R_{α+1} > R_α + k·ξ_α}`,
  matching the event of `per_metaphase_two_thirds` at block start `r = R_α+k·ξ_α`.
* `metaphase_succ_sub_le` — `R_{α+1} − R_α ≤ N_α · ξ_α`, the domination used to
  pass from `μ[N_α | 𝒢_{R_α}] ≤ 3` to `E[R_{α+1} − R_α | 𝒢_{R_α}] ≤ 3·ξ_α`.
-/

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
variable {κ : ℕ} [NeZero κ] {G : TemporalGraphFixedDegree V}

/-- `ξ_α` evaluated at the random metaphase start `R_α`: the block length
`xiAlpha b m d_min |𝒪(t_{R_α})|` for metaphase `α`. It is `𝒢_{R_α}`-measurable
and always `≥ 1`. -/
def VoterModelAbstract.metaphaseXi {Ω : Type*} [MeasurableSpace Ω] (vm : G.VoterModelAbstract κ Ω)
    (B : ℝ) (m d_min : ℕ) (b : ℝ) (Δ : ℕ → ℕ) (φ : ℕ → ℝ) (α : ℕ) (ω : Ω) : ℕ :=
  TemporalGraph.xiAlpha b m d_min
    (vm.opinionSet (TemporalGraph.phaseTime Δ φ (vm.metaphase B m d_min Δ φ α ω)) ω).card

theorem VoterModelAbstract.one_le_metaphaseXi {Ω : Type*} [MeasurableSpace Ω] (vm : G.VoterModelAbstract κ Ω)
    (B : ℝ) (m d_min : ℕ) (b : ℝ) (Δ : ℕ → ℕ) (φ : ℕ → ℝ) (α : ℕ) (ω : Ω) :
    1 ≤ vm.metaphaseXi B m d_min b Δ φ α ω := by
  unfold VoterModelAbstract.metaphaseXi TemporalGraph.xiAlpha; omega

/-- `N_α`, the number of `ξ_α`-blocks before metaphase `α` ends: the least `k`
with `R_{α+1} ≤ R_α + k·ξ_α`. The cap `r_max` of `metaphase` keeps the set
nonempty (`k = r_max` works since `ξ_α ≥ 1`), so the `sInf` is well defined. -/
def VoterModelAbstract.metaphaseBlockCount {Ω : Type*} [MeasurableSpace Ω] (vm : G.VoterModelAbstract κ Ω)
    (B : ℝ) (m d_min : ℕ) (b : ℝ) (Δ : ℕ → ℕ) (φ : ℕ → ℝ) (α : ℕ) (ω : Ω) : ℕ :=
  sInf {k | vm.metaphase B m d_min Δ φ (α + 1) ω
            ≤ vm.metaphase B m d_min Δ φ α ω + k * vm.metaphaseXi B m d_min b Δ φ α ω}

variable {Ω : Type*} [MeasurableSpace Ω] (vm : VoterModelAbstract G.toTemporalGraph κ Ω)
  (B : ℝ) (m d_min : ℕ) (b : ℝ) (Δ : ℕ → ℕ) (φ : ℕ → ℝ)

/-- The defining set of `N_α` is nonempty: `k = r_max` lies in it, since
`R_{α+1} ≤ r_max ≤ R_α + r_max·ξ_α` (using `ξ_α ≥ 1`). -/
theorem VoterModelAbstract.metaphaseBlockCount_set_nonempty (α : ℕ) (ω : Ω) :
    {k | vm.metaphase B m d_min Δ φ (α + 1) ω
          ≤ vm.metaphase B m d_min Δ φ α ω + k * vm.metaphaseXi B m d_min b Δ φ α ω}.Nonempty := by
  refine ⟨TemporalGraph.rMax B m d_min, ?_⟩
  simp only [Set.mem_setOf_eq]
  have hξ := vm.one_le_metaphaseXi B m d_min b Δ φ α ω
  have hR := vm.metaphase_le_rMax B m d_min Δ φ (α + 1) ω
  calc vm.metaphase B m d_min Δ φ (α + 1) ω
      ≤ TemporalGraph.rMax B m d_min := hR
    _ ≤ TemporalGraph.rMax B m d_min * vm.metaphaseXi B m d_min b Δ φ α ω :=
        Nat.le_mul_of_pos_right _ (by omega)
    _ ≤ vm.metaphase B m d_min Δ φ α ω
          + TemporalGraph.rMax B m d_min * vm.metaphaseXi B m d_min b Δ φ α ω :=
        Nat.le_add_left _ _

/-- **Threshold from survival (eq `0a` source).** If phase `r'` is strictly before
the metaphase boundary `R_{α+1}`, the opinion count at `t_{r'}` still exceeds the
metaphase threshold `θ_α = max ⌈(6/7)^α κ⌉ 1`. (If it were `≤ θ_α`, then `r'` would
lie in the defining `sInf` set, forcing `R_{α+1} ≤ r'`.) -/
theorem VoterModelAbstract.metaphase_succ_lt_opinionCard_gt (α r' : ℕ) (ω : Ω)
    (h : r' < vm.metaphase B m d_min Δ φ (α + 1) ω) :
    max ⌈(6 / 7 : ℝ) ^ α * (κ : ℝ)⌉₊ 1
      < (vm.opinionSet (TemporalGraph.phaseTime Δ φ r') ω).card := by
  by_contra hcon
  rw [not_lt] at hcon
  have hmem : r' ∈ insert (TemporalGraph.rMax B m d_min)
      {r | (vm.opinionSet (TemporalGraph.phaseTime Δ φ r) ω).card
            ≤ max ⌈(6 / 7 : ℝ) ^ α * (κ : ℝ)⌉₊ 1} :=
    Set.mem_insert_of_mem _ hcon
  have hle : vm.metaphase B m d_min Δ φ (α + 1) ω ≤ r' := Nat.sInf_le hmem
  omega

/-- **Metaphase count bound (eq `00b` source).** At the boundary `R_{α+1}`, either
the cap `r_max` was reached, or the opinion count has dropped to the threshold
`θ_α = max ⌈(6/7)^α κ⌉ 1`. (The boundary is a member of its defining `sInf` set.) -/
theorem VoterModelAbstract.metaphase_succ_opinionCard_le (α : ℕ) (ω : Ω) :
    vm.metaphase B m d_min Δ φ (α + 1) ω = TemporalGraph.rMax B m d_min ∨
      (vm.opinionSet (TemporalGraph.phaseTime Δ φ
          (vm.metaphase B m d_min Δ φ (α + 1) ω)) ω).card
        ≤ max ⌈(6 / 7 : ℝ) ^ α * (κ : ℝ)⌉₊ 1 := by
  have hne : (insert (TemporalGraph.rMax B m d_min)
      {r | (vm.opinionSet (TemporalGraph.phaseTime Δ φ r) ω).card
            ≤ max ⌈(6 / 7 : ℝ) ^ α * (κ : ℝ)⌉₊ 1}).Nonempty :=
    ⟨_, Set.mem_insert _ _⟩
  have hmem := Nat.sInf_mem hne
  rcases Set.mem_insert_iff.mp hmem with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- **Increment is zero off the survival event.** If the opinion count at `t_{R_α}` is
already `≤ θ_α`, then `R_α` is a metaphase boundary, so `R_{α+1} = R_α`. -/
theorem VoterModelAbstract.metaphase_succ_eq_of_card_le (α : ℕ) (ω : Ω)
    (h : (vm.opinionSet (TemporalGraph.phaseTime Δ φ (vm.metaphase B m d_min Δ φ α ω)) ω).card
          ≤ max ⌈(6 / 7 : ℝ) ^ α * (κ : ℝ)⌉₊ 1) :
    vm.metaphase B m d_min Δ φ (α + 1) ω = vm.metaphase B m d_min Δ φ α ω := by
  have hle : vm.metaphase B m d_min Δ φ (α + 1) ω ≤ vm.metaphase B m d_min Δ φ α ω :=
    Nat.sInf_le (Set.mem_insert_of_mem _ h)
  have hge : vm.metaphase B m d_min Δ φ α ω ≤ vm.metaphase B m d_min Δ φ (α + 1) ω :=
    vm.metaphase_mono B m d_min Δ φ ω (Nat.le_succ α)
  omega

omit [NeZero κ] in
/-- **Metaphase threshold arithmetic (eq `00b`).** If `x ≤ θ_β = max⌈(6/7)^β κ⌉ 1`
and `θ_{β+1} = max⌈(6/7)^{β+1} κ⌉ 1 < y`, then `(6/7)·x < y`. (The metaphase count
`|O_α| = x ≤ θ_{α-1}` and the survival count `|𝒪(s+K)| = y > θ_α` give
`(6/7)|O_α| < |𝒪(s+K)|`, the threshold feeding `one_block_hED`.) -/
theorem opinion_threshold_arith (β x y : ℕ)
    (hx : x ≤ max ⌈(6 / 7 : ℝ) ^ β * (κ : ℝ)⌉₊ 1)
    (hy : max ⌈(6 / 7 : ℝ) ^ (β + 1) * (κ : ℝ)⌉₊ 1 < y) :
    (6 / 7 : ℝ) * (x : ℝ) < (y : ℝ) := by
  set a := (6 / 7 : ℝ) ^ β * (κ : ℝ) with ha
  have ha_nn : 0 ≤ a := by rw [ha]; positivity
  have hpow : (6 / 7 : ℝ) ^ (β + 1) * (κ : ℝ) = (6 / 7 : ℝ) * a := by rw [ha, pow_succ]; ring
  rw [hpow] at hy
  -- `max ⌈a⌉ 1 ≤ a + 1`
  have hmax_le : ((max ⌈a⌉₊ 1 : ℕ) : ℝ) ≤ a + 1 := by
    rw [Nat.cast_max]
    refine max_le ?_ (by push_cast; linarith)
    exact (Nat.ceil_lt_add_one ha_nn).le
  have hx' : (x : ℝ) ≤ a + 1 := le_trans (by exact_mod_cast hx) hmax_le
  -- `(6/7)a + 1 ≤ y`
  have hyR : (6 / 7 : ℝ) * a + 1 ≤ (y : ℝ) := by
    have h1 : (6 / 7 : ℝ) * a ≤ (⌈(6 / 7 : ℝ) * a⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈(6 / 7 : ℝ) * a⌉₊ : ℝ) ≤ ((max ⌈(6 / 7 : ℝ) * a⌉₊ 1 : ℕ) : ℝ) := by
      exact_mod_cast le_max_left _ _
    have h3 : ((max ⌈(6 / 7 : ℝ) * a⌉₊ 1 : ℕ) : ℝ) + 1 ≤ (y : ℝ) := by
      have hle : max ⌈(6 / 7 : ℝ) * a⌉₊ 1 + 1 ≤ y := hy
      exact_mod_cast hle
    linarith
  have h56 : (6 / 7 : ℝ) * (x : ℝ) ≤ (6 / 7 : ℝ) * (a + 1) :=
    mul_le_mul_of_nonneg_left hx' (by norm_num)
  linarith [h56, hyR]

/-- **Event identity (eq `0a` link).** `N_α ≥ k+1` exactly when the metaphase has
not ended by phase `R_α + k·ξ_α`, i.e. `R_{α+1} > R_α + k·ξ_α`. This matches the
conditioning event of `per_metaphase_two_thirds` at block start `r = R_α+k·ξ_α`. -/
theorem VoterModelAbstract.metaphaseBlockCount_succ_le_iff (α k : ℕ) (ω : Ω) :
    k + 1 ≤ vm.metaphaseBlockCount B m d_min b Δ φ α ω
      ↔ vm.metaphase B m d_min Δ φ α ω + k * vm.metaphaseXi B m d_min b Δ φ α ω
          < vm.metaphase B m d_min Δ φ (α + 1) ω := by
  set R := vm.metaphase B m d_min Δ φ α ω
  set R' := vm.metaphase B m d_min Δ φ (α + 1) ω
  set ξ := vm.metaphaseXi B m d_min b Δ φ α ω
  set S := {j | R' ≤ R + j * ξ} with hS
  have hne : S.Nonempty := vm.metaphaseBlockCount_set_nonempty B m d_min b Δ φ α ω
  constructor
  · intro hk
    by_contra hcon
    have hmem : k ∈ S := by simp only [hS, Set.mem_setOf_eq]; omega
    have : vm.metaphaseBlockCount B m d_min b Δ φ α ω ≤ k := Nat.sInf_le hmem
    omega
  · intro hk
    by_contra hcon
    have hle : vm.metaphaseBlockCount B m d_min b Δ φ α ω ≤ k := by omega
    have hmem : vm.metaphaseBlockCount B m d_min b Δ φ α ω ∈ S := Nat.sInf_mem hne
    simp only [hS, Set.mem_setOf_eq] at hmem
    have hmul : vm.metaphaseBlockCount B m d_min b Δ φ α ω * ξ ≤ k * ξ :=
      Nat.mul_le_mul_right _ hle
    omega

/-- **Domination (eq `R_{α+1}−R_α ≤ N_α·ξ_α`).** The number of phases in metaphase
`α` is at most `N_α · ξ_α`; in particular `R_α ≤ R_{α+1}` and the real-valued
increment is bounded by `N_α · ξ_α`. -/
theorem VoterModelAbstract.metaphase_succ_le_blockCount_mul (α : ℕ) (ω : Ω) :
    vm.metaphase B m d_min Δ φ (α + 1) ω
      ≤ vm.metaphase B m d_min Δ φ α ω
          + vm.metaphaseBlockCount B m d_min b Δ φ α ω * vm.metaphaseXi B m d_min b Δ φ α ω := by
  have hmem := Nat.sInf_mem (vm.metaphaseBlockCount_set_nonempty B m d_min b Δ φ α ω)
  simpa only [Set.mem_setOf_eq, VoterModelAbstract.metaphaseBlockCount] using hmem

/-! ### Opinion-set monotonicity in time (eq `0b`, almost sure)

Under the voter dynamics opinions only disappear, never appear: if `q` is absent
(`phiQ q = ∅`) it stays absent (`qset_persistent`). Hence `𝒪(t)` is a.s.
non-increasing in `t`, so `|𝒪(t_r)| ≤ |𝒪(t_{R_α})| = |O_α|` for `r ≥ R_α` — the
cardinality input to the `hED` inclusion of `per_metaphase_two_thirds`. -/

/-- One-step a.s. antitonicity of the opinion set. -/
theorem VoterModelAbstract.opinionSet_subset_ae_succ (s : ℕ) :
    ∀ᵐ ω ∂(vm.μ : Measure Ω), vm.opinionSet (s + 1) ω ⊆ vm.opinionSet s ω := by
  have hpers : ∀ q : Fin κ, ∀ᵐ ω ∂(vm.μ : Measure Ω),
      VoterModel.phiQ q (vm.ξ s ω) = ∅ → VoterModel.phiQ q (vm.ξ (s + 1) ω) = ∅ :=
    fun q => (TemporalGraph.qset_persistent vm q s).1
  rw [← ae_all_iff] at hpers
  filter_upwards [hpers] with ω hω q hq
  by_contra hqs
  have hempty : VoterModel.phiQ q (vm.ξ s ω) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro v hv
    exact hqs ((vm.mem_opinionSet).mpr ⟨v, by simpa [VoterModel.phiQ] using hv⟩)
  obtain ⟨v, hv⟩ := (vm.mem_opinionSet).mp hq
  have hvmem : v ∈ VoterModel.phiQ q (vm.ξ (s + 1) ω) := by simp [VoterModel.phiQ, hv]
  rw [hω q hempty] at hvmem
  exact absurd hvmem (Finset.notMem_empty v)

/-- Multi-step a.s. antitonicity: `𝒪(t) ⊆ 𝒪(s)` a.s. for `s ≤ t`. -/
theorem VoterModelAbstract.opinionSet_subset_ae {s t : ℕ} (hst : s ≤ t) :
    ∀ᵐ ω ∂(vm.μ : Measure Ω), vm.opinionSet t ω ⊆ vm.opinionSet s ω := by
  induction t, hst using Nat.le_induction with
  | base => filter_upwards with ω using subset_rfl
  | succ n hn ih =>
    filter_upwards [ih, vm.opinionSet_subset_ae_succ n] with ω h1 h2
    exact Finset.Subset.trans h2 h1

/-! ### Measurability of `R_α`, `ξ_α`, `N_α` (for the increment reduction) -/

/-- `R_α : Ω → ℕ` is `mΩ`-measurable. -/
theorem VoterModelAbstract.metaphase_measurable
    (hmono : Monotone (TemporalGraph.phaseTime Δ φ)) (α : ℕ) :
    Measurable (fun ω => vm.metaphase B m d_min Δ φ α ω) := by
  refine measurable_to_countable' (fun n => ?_)
  exact (vm.ℱ.le _) _ (vm.metaphase_eq_measurable B m d_min Δ φ hmono α n)

/-- `ξ_α : Ω → ℕ` is `mΩ`-measurable. -/
theorem VoterModelAbstract.metaphaseXi_measurable
    (hmono : Monotone (TemporalGraph.phaseTime Δ φ)) (α : ℕ) :
    Measurable (fun ω => vm.metaphaseXi B m d_min b Δ φ α ω) := by
  refine measurable_to_countable' (fun n => ?_)
  have hunion : (fun ω => vm.metaphaseXi B m d_min b Δ φ α ω) ⁻¹' {n}
      = ⋃ r, ({ω | vm.metaphase B m d_min Δ φ α ω = r} ∩
          {ω | TemporalGraph.xiAlpha b m d_min
                (vm.opinionSet (TemporalGraph.phaseTime Δ φ r) ω).card = n}) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_setOf_eq]
    constructor
    · intro h
      exact ⟨vm.metaphase B m d_min Δ φ α ω, rfl, h⟩
    · rintro ⟨r, hr, hx⟩
      unfold VoterModelAbstract.metaphaseXi
      rw [hr]; exact hx
  rw [hunion]
  refine MeasurableSet.iUnion (fun r => MeasurableSet.inter ?_ ?_)
  · exact (vm.ℱ.le _) _ (vm.metaphase_eq_measurable B m d_min Δ φ hmono α r)
  · have hop : Measurable (fun ω => vm.opinionSet (TemporalGraph.phaseTime Δ φ r) ω) :=
      (vm.opinionSet_measurable (TemporalGraph.phaseTime Δ φ r)).mono
        (vm.ℱ.le _) le_top
    exact (measurable_from_top
      (f := fun s : Finset (Fin κ) => TemporalGraph.xiAlpha b m d_min s.card)).comp hop
        (measurableSet_singleton n)

/-- `N_α : Ω → ℕ` is `mΩ`-measurable. -/
theorem VoterModelAbstract.metaphaseBlockCount_measurable
    (hmono : Monotone (TemporalGraph.phaseTime Δ φ)) (α : ℕ) :
    Measurable (fun ω => vm.metaphaseBlockCount B m d_min b Δ φ α ω) := by
  have hR := vm.metaphase_measurable B m d_min Δ φ hmono α
  have hR' := vm.metaphase_measurable B m d_min Δ φ hmono (α + 1)
  have hξ := vm.metaphaseXi_measurable B m d_min b Δ φ hmono α
  have hge : ∀ k, MeasurableSet {ω | k + 1 ≤ vm.metaphaseBlockCount B m d_min b Δ φ α ω} := by
    intro k
    have hset : {ω | k + 1 ≤ vm.metaphaseBlockCount B m d_min b Δ φ α ω}
        = {ω | vm.metaphase B m d_min Δ φ α ω + k * vm.metaphaseXi B m d_min b Δ φ α ω
              < vm.metaphase B m d_min Δ φ (α + 1) ω} := by
      ext ω; simp only [Set.mem_setOf_eq]
      exact vm.metaphaseBlockCount_succ_le_iff B m d_min b Δ φ α k ω
    rw [hset]
    exact measurableSet_lt (hR.add (measurable_const.mul hξ)) hR'
  refine measurable_to_countable' (fun n => ?_)
  cases n with
  | zero =>
    have hz : (fun ω => vm.metaphaseBlockCount B m d_min b Δ φ α ω) ⁻¹' {0}
        = {ω | 0 + 1 ≤ vm.metaphaseBlockCount B m d_min b Δ φ α ω}ᶜ := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_setOf_eq]
      omega
    rw [hz]; exact (hge 0).compl
  | succ k =>
    have hsk : (fun ω => vm.metaphaseBlockCount B m d_min b Δ φ α ω) ⁻¹' {k + 1}
        = {ω | k + 1 ≤ vm.metaphaseBlockCount B m d_min b Δ φ α ω}
          ∩ {ω | (k + 1) + 1 ≤ vm.metaphaseBlockCount B m d_min b Δ φ α ω}ᶜ := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_compl_iff,
        Set.mem_setOf_eq]
      omega
    rw [hsk]; exact (hge k).inter (hge (k + 1)).compl

/-- `N_α ≤ r_max` (the cap is a member of the defining `sInf` set). -/
theorem VoterModelAbstract.metaphaseBlockCount_le_rMax (α : ℕ) (ω : Ω) :
    vm.metaphaseBlockCount B m d_min b Δ φ α ω ≤ TemporalGraph.rMax B m d_min := by
  refine Nat.sInf_le ?_
  simp only [Set.mem_setOf_eq]
  have hξ := vm.one_le_metaphaseXi B m d_min b Δ φ α ω
  have hR := vm.metaphase_le_rMax B m d_min Δ φ (α + 1) ω
  calc vm.metaphase B m d_min Δ φ (α + 1) ω
      ≤ TemporalGraph.rMax B m d_min := hR
    _ ≤ TemporalGraph.rMax B m d_min * vm.metaphaseXi B m d_min b Δ φ α ω :=
        Nat.le_mul_of_pos_right _ (by omega)
    _ ≤ vm.metaphase B m d_min Δ φ α ω
          + TemporalGraph.rMax B m d_min * vm.metaphaseXi B m d_min b Δ φ α ω :=
        Nat.le_add_left _ _

/-- Uniform bound on `ξ_α`: since `|𝒪| ≥ 1`, the block length is at most
`1 + ⌈b·(τm/(P·d_min) + log(1+τm/P))⌉`. Needs `0 ≤ b` and `0 < d_min`. -/
theorem VoterModelAbstract.metaphaseXi_le (hb : 0 ≤ b) (hd : 0 < d_min) (α : ℕ) (ω : Ω) :
    vm.metaphaseXi B m d_min b Δ φ α ω
      ≤ 1 + ⌈b * (14 * (m : ℝ) / (3 * (d_min : ℝ)) + Real.log (1 + 14 * (m : ℝ) / 3))⌉₊ := by
  unfold VoterModelAbstract.metaphaseXi TemporalGraph.xiAlpha
  refine Nat.add_le_add_left (Nat.ceil_mono ?_) 1
  set c := (vm.opinionSet (TemporalGraph.phaseTime Δ φ (vm.metaphase B m d_min Δ φ α ω)) ω).card
    with hc
  have hc1 : 1 ≤ c := by
    rw [hc]
    refine Finset.Nonempty.card_pos ?_
    exact (Finset.univ_nonempty).image _
  have hcR : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc1
  have hdR : (0 : ℝ) < (d_min : ℝ) := by exact_mod_cast hd
  have hmR : (0 : ℝ) ≤ (m : ℝ) := by positivity
  apply mul_le_mul_of_nonneg_left _ hb
  have h1 : 14 * (m : ℝ) / (3 * ((d_min : ℝ) * (c : ℝ)))
      ≤ 14 * (m : ℝ) / (3 * (d_min : ℝ)) := by
    gcongr
    nlinarith [hcR, hdR]
  have h2 : Real.log (1 + 14 * (m : ℝ) / (3 * (c : ℝ))) ≤ Real.log (1 + 14 * (m : ℝ) / 3) := by
    apply Real.log_le_log (by positivity)
    have : 14 * (m : ℝ) / (3 * (c : ℝ)) ≤ 14 * (m : ℝ) / 3 := by
      rw [div_le_iff₀ (by positivity)]
      rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num)]
      nlinarith [hmR, hcR]
    linarith
  linarith

/-- `ξ_α` is `𝒢_{R_α}`-strongly-measurable: it is determined by the configuration
at the stopping time `R_α`. -/
theorem VoterModelAbstract.metaphaseXi_stronglyMeasurable_stopped
    (hmono : Monotone (TemporalGraph.phaseTime Δ φ)) (α : ℕ) :
    StronglyMeasurable[(vm.metaphase_isStoppingTime B m d_min Δ φ hmono α).measurableSpace]
      (fun ω => (vm.metaphaseXi B m d_min b Δ φ α ω : ℝ)) := by
  set hτ := vm.metaphase_isStoppingTime B m d_min Δ φ hmono α with hτdef
  have hmeasN : @Measurable Ω ℕ hτ.measurableSpace _
      (fun ω => vm.metaphaseXi B m d_min b Δ φ α ω) := by
    refine @measurable_to_countable' ℕ Ω _ _ hτ.measurableSpace _ (fun n => ?_)
    have hunion : (fun ω => vm.metaphaseXi B m d_min b Δ φ α ω) ⁻¹' {n}
        = ⋃ r, ({ω | TemporalGraph.xiAlpha b m d_min
                  (vm.opinionSet (TemporalGraph.phaseTime Δ φ r) ω).card = n}
                ∩ {ω | (vm.metaphase B m d_min Δ φ α ω : WithTop ℕ) = (r : WithTop ℕ)}) := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_inter_iff,
        Set.mem_setOf_eq, Nat.cast_inj]
      constructor
      · intro h; exact ⟨vm.metaphase B m d_min Δ φ α ω, h, rfl⟩
      · rintro ⟨r, hx, hr⟩; unfold VoterModelAbstract.metaphaseXi; rw [hr]; exact hx
    rw [hunion]
    refine MeasurableSet.iUnion (fun r => ?_)
    refine (hτ.measurableSet_inter_eq_iff _ r).mpr ?_
    refine MeasurableSet.inter ?_ ?_
    · have hop : @Measurable Ω (Finset (Fin κ)) (vm.ℱ (TemporalGraph.phaseTime Δ φ r)) ⊤
          (fun ω => vm.opinionSet (TemporalGraph.phaseTime Δ φ r) ω) :=
        vm.opinionSet_measurable (TemporalGraph.phaseTime Δ φ r)
      exact (measurable_from_top
        (f := fun s : Finset (Fin κ) => TemporalGraph.xiAlpha b m d_min s.card)).comp hop
          (measurableSet_singleton n)
    · exact hτ.measurableSet_eq r
  have hmeasR : @Measurable Ω ℝ hτ.measurableSpace _
      (fun ω => (vm.metaphaseXi B m d_min b Δ φ α ω : ℝ)) :=
    (measurable_from_top (f := fun k : ℕ => (k : ℝ))).comp hmeasN
  exact hmeasR.stronglyMeasurable

/-- The survival event `E_α = {|𝒪(t_{R_α})| > θ}` is `𝒢_{R_α}`-measurable (it is a
threshold on the stopped opinion count `|𝒪(phaseTime ∘ R_α)|`). -/
theorem VoterModelAbstract.metaphase_survival_measurableSet_stopped
    (hmono : Monotone (TemporalGraph.phaseTime Δ φ)) (α θ : ℕ) :
    MeasurableSet[(vm.metaphase_isStoppingTime B m d_min Δ φ hmono α).measurableSpace]
      {ω | θ < (vm.opinionSet (TemporalGraph.phaseTime Δ φ
              (vm.metaphase B m d_min Δ φ α ω)) ω).card} := by
  set hτ := vm.metaphase_isStoppingTime B m d_min Δ φ hmono α with hτdef
  have hunion : {ω | θ < (vm.opinionSet (TemporalGraph.phaseTime Δ φ
          (vm.metaphase B m d_min Δ φ α ω)) ω).card}
      = ⋃ r, ({ω | θ < (vm.opinionSet (TemporalGraph.phaseTime Δ φ r) ω).card}
              ∩ {ω | (vm.metaphase B m d_min Δ φ α ω : WithTop ℕ) = (r : WithTop ℕ)}) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, Nat.cast_inj]
    constructor
    · intro h; exact ⟨vm.metaphase B m d_min Δ φ α ω, h, rfl⟩
    · rintro ⟨r, hx, hr⟩; rw [hr]; exact hx
  rw [hunion]
  refine MeasurableSet.iUnion (fun r => ?_)
  refine (hτ.measurableSet_inter_eq_iff _ r).mpr (MeasurableSet.inter ?_ (hτ.measurableSet_eq r))
  exact ((measurable_from_top (f := fun s : Finset (Fin κ) => s.card)).comp
    (vm.opinionSet_measurable (TemporalGraph.phaseTime Δ φ r))) measurableSet_Ioi

/-- A `ℕ`-valued measurable map bounded by `C` has integrable real cast (probability
measure). -/
theorem VoterModelAbstract.integrable_natCast_le {f : Ω → ℕ} (C : ℕ)
    (hf : Measurable f) (hbd : ∀ ω, f ω ≤ C) :
    Integrable (fun ω => (f ω : ℝ)) vm.μ := by
  refine Integrable.mono' (integrable_const (C : ℝ))
    ((measurable_from_top (f := fun k : ℕ => (k : ℝ))).comp hf).aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact_mod_cast hbd ω

/-! ### D2 instantiation: the conditional metaphase-increment bound -/

/-- **Metaphase increment bound** (`E[R_{α+1} − R_α | 𝒢_{R_α}] ≤ 3·ξ_α`).
Composes the conditional geometric-tail bound `condExp_geom_tail_le_three`
(applied to the per-level tail hypothesis `htail`) with the deterministic
domination `R_{α+1} − R_α ≤ N_α·ξ_α` and the `𝒢_{R_α}`-measurability of `ξ_α`.

FORMALIZATION NOTE: the increment is the *real* difference `(R_{α+1} : ℝ) − (R_α : ℝ)`
(faithful to `R_{α+1} − R_α`, and equal to the truncated `ℕ`-difference since
`R_α ≤ R_{α+1}`). The conditioning σ-algebra `𝒢_{R_α}` is the stopping-time
σ-algebra of `R_α` for the coarse filtration `phaseFiltration`. -/
theorem VoterModelAbstract.metaphase_increment_le
    (hmono : Monotone (TemporalGraph.phaseTime Δ φ)) (hb : 0 ≤ b) (hd : 0 < d_min) (α : ℕ)
    (htail : ∀ k, (vm.μ : Measure Ω)[Set.indicator {ω | k + 1 ≤ vm.metaphaseBlockCount B m d_min b Δ φ α ω}
          (fun _ => (1 : ℝ)) |
          (vm.metaphase_isStoppingTime B m d_min Δ φ hmono α).measurableSpace]
        ≤ᵐ[(vm.μ : Measure Ω)] (fun _ => ((2 : ℝ) / 3) ^ k)) :
    (vm.μ : Measure Ω)[(fun ω => (vm.metaphase B m d_min Δ φ (α + 1) ω : ℝ)
            - (vm.metaphase B m d_min Δ φ α ω : ℝ)) |
        (vm.metaphase_isStoppingTime B m d_min Δ φ hmono α).measurableSpace]
      ≤ᵐ[(vm.μ : Measure Ω)] (fun ω => 3 * (vm.metaphaseXi B m d_min b Δ φ α ω : ℝ)) := by
  set hτ := vm.metaphase_isStoppingTime B m d_min Δ φ hmono α with hτdef
  have hm := hτ.measurableSpace_le
  -- block count N_α and its integrability
  have hNmeas : Measurable (fun ω => vm.metaphaseBlockCount B m d_min b Δ φ α ω) :=
    vm.metaphaseBlockCount_measurable B m d_min b Δ φ hmono α
  have hNint : Integrable (fun ω => (vm.metaphaseBlockCount B m d_min b Δ φ α ω : ℝ)) vm.μ :=
    vm.integrable_natCast_le (TemporalGraph.rMax B m d_min) hNmeas
      (fun ω => vm.metaphaseBlockCount_le_rMax B m d_min b Δ φ α ω)
  -- step 1: μ[N_α | 𝒢] ≤ 3
  have hN3 := condExp_geom_tail_le_three hm hNmeas hNint htail
  -- ξ_α measurability and integrability
  set Cξ := 1 + ⌈b * (14 * (m : ℝ) / (3 * (d_min : ℝ)) + Real.log (1 + 14 * (m : ℝ) / 3))⌉₊ with hCξ
  have hξmeas : Measurable (fun ω => vm.metaphaseXi B m d_min b Δ φ α ω) :=
    vm.metaphaseXi_measurable B m d_min b Δ φ hmono α
  have hξint : Integrable (fun ω => (vm.metaphaseXi B m d_min b Δ φ α ω : ℝ)) vm.μ :=
    vm.integrable_natCast_le Cξ hξmeas (fun ω => vm.metaphaseXi_le B m d_min b Δ φ hb hd α ω)
  have hc_meas : StronglyMeasurable[hτ.measurableSpace]
      (fun ω => (vm.metaphaseXi B m d_min b Δ φ α ω : ℝ)) :=
    vm.metaphaseXi_stronglyMeasurable_stopped B m d_min b Δ φ hmono α
  have hc_nn : 0 ≤ᵐ[(vm.μ : Measure Ω)] (fun ω => (vm.metaphaseXi B m d_min b Δ φ α ω : ℝ)) := by
    filter_upwards with ω
    simp only [Pi.zero_apply]
    positivity
  -- g = R_{α+1} − R_α and its integrability
  have hRint : Integrable (fun ω => (vm.metaphase B m d_min Δ φ α ω : ℝ)) vm.μ :=
    vm.integrable_natCast_le (TemporalGraph.rMax B m d_min)
      (vm.metaphase_measurable B m d_min Δ φ hmono α)
      (fun ω => vm.metaphase_le_rMax B m d_min Δ φ α ω)
  have hR'int : Integrable (fun ω => (vm.metaphase B m d_min Δ φ (α + 1) ω : ℝ)) vm.μ :=
    vm.integrable_natCast_le (TemporalGraph.rMax B m d_min)
      (vm.metaphase_measurable B m d_min Δ φ hmono (α + 1))
      (fun ω => vm.metaphase_le_rMax B m d_min Δ φ (α + 1) ω)
  have hgint : Integrable (fun ω => (vm.metaphase B m d_min Δ φ (α + 1) ω : ℝ)
      - (vm.metaphase B m d_min Δ φ α ω : ℝ)) vm.μ := hR'int.sub hRint
  -- c·N integrability via bounded multiplier
  have hcN_int : Integrable ((fun ω => (vm.metaphaseXi B m d_min b Δ φ α ω : ℝ))
      * (fun ω => (vm.metaphaseBlockCount B m d_min b Δ φ α ω : ℝ))) vm.μ := by
    refine hNint.bdd_mul
      ((measurable_from_top (f := fun k : ℕ => (k : ℝ))).comp hξmeas).aestronglyMeasurable
      (c := (Cξ : ℝ)) ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hb2 : vm.metaphaseXi B m d_min b Δ φ α ω ≤ Cξ :=
      vm.metaphaseXi_le B m d_min b Δ φ hb hd α ω
    exact_mod_cast hb2
  -- domination g ≤ ξ·N
  have hgN : (fun ω => (vm.metaphase B m d_min Δ φ (α + 1) ω : ℝ)
        - (vm.metaphase B m d_min Δ φ α ω : ℝ))
      ≤ᵐ[(vm.μ : Measure Ω)] ((fun ω => (vm.metaphaseXi B m d_min b Δ φ α ω : ℝ))
        * (fun ω => (vm.metaphaseBlockCount B m d_min b Δ φ α ω : ℝ))) := by
    filter_upwards with ω
    have h := vm.metaphase_succ_le_blockCount_mul B m d_min b Δ φ α ω
    have hcast : (vm.metaphase B m d_min Δ φ (α + 1) ω : ℝ)
        ≤ (vm.metaphase B m d_min Δ φ α ω : ℝ)
          + (vm.metaphaseBlockCount B m d_min b Δ φ α ω : ℝ)
            * (vm.metaphaseXi B m d_min b Δ φ α ω : ℝ) := by
      rw [← Nat.cast_mul, ← Nat.cast_add]; exact_mod_cast h
    simp only [Pi.mul_apply]
    nlinarith [hcast]
  -- step 2: compose
  have := condExp_le_of_le_mul_of_condExp_le_three hm hc_meas hc_nn hNint hgint hcN_int hgN hN3
  simpa only [Pi.mul_apply] using this

/-! ### From the single-block bound to `htail` (STEP 1 ⇒ STEP 2 ⇒ STEP 3)

The metaphase block-survival events are `B_α^k = {R_α + k·ξ_α < R_{α+1}}`. By
`metaphaseBlockCount_succ_le_iff`, `{k+1 ≤ N_α} = B_α^k`, and `B_α^{k+1} ⊆ B_α^k`.
The single-block bound (STEP 1, `one_block_random_index`-shaped, taken as a
hypothesis here) feeds a clean set-integral induction giving the geometric tail
`htail`, which closes the increment bound `metaphase_increment_le`. -/

/-- `B_α^k = {R_α + k·ξ_α < R_{α+1}}`, the event "metaphase `α` survives block `k`". -/
def VoterModelAbstract.blockTailSet (α k : ℕ) : Set Ω :=
  {ω | vm.metaphase B m d_min Δ φ α ω + k * vm.metaphaseXi B m d_min b Δ φ α ω
        < vm.metaphase B m d_min Δ φ (α + 1) ω}

/-- `{k+1 ≤ N_α} = B_α^k` (`metaphaseBlockCount_succ_le_iff`). -/
theorem VoterModelAbstract.blockCount_succ_le_eq_blockTailSet (α k : ℕ) :
    {ω | k + 1 ≤ vm.metaphaseBlockCount B m d_min b Δ φ α ω}
      = vm.blockTailSet B m d_min b Δ φ α k := by
  ext ω; exact vm.metaphaseBlockCount_succ_le_iff B m d_min b Δ φ α k ω

/-- `B_α^k` is `mΩ`-measurable. -/
theorem VoterModelAbstract.blockTailSet_measurable
    (hmono : Monotone (TemporalGraph.phaseTime Δ φ)) (α k : ℕ) :
    MeasurableSet (vm.blockTailSet B m d_min b Δ φ α k) :=
  measurableSet_lt
    ((vm.metaphase_measurable B m d_min Δ φ hmono α).add
      (measurable_const.mul (vm.metaphaseXi_measurable B m d_min b Δ φ hmono α)))
    (vm.metaphase_measurable B m d_min Δ φ hmono (α + 1))

/-- `B_α^{k+1} ⊆ B_α^k` (more blocks survived ⇒ fewer). -/
theorem VoterModelAbstract.blockTailSet_antitone (α k : ℕ) :
    vm.blockTailSet B m d_min b Δ φ α (k + 1) ⊆ vm.blockTailSet B m d_min b Δ φ α k := by
  intro ω hω
  simp only [VoterModelAbstract.blockTailSet, Set.mem_setOf_eq] at hω ⊢
  have hmul : k * vm.metaphaseXi B m d_min b Δ φ α ω
      ≤ (k + 1) * vm.metaphaseXi B m d_min b Δ φ α ω :=
    Nat.mul_le_mul_right _ (Nat.le_succ k)
  omega

/-- Set-integral of an indicator over a measurable set. -/
theorem VoterModelAbstract.setIntegral_indicator_one (T : Set Ω)
    (D : Set Ω) (hD : MeasurableSet D) :
    ∫ ω in T, D.indicator (fun _ => (1 : ℝ)) ω ∂vm.μ = ((vm.μ : Measure Ω) (T ∩ D)).toReal := by
  rw [MeasureTheory.setIntegral_indicator hD, setIntegral_const, smul_eq_mul, mul_one]
  rfl

end TemporalGraph
