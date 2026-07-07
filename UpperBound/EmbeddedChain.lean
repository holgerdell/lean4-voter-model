module

public import Mathlib.Probability.Process.Stopping
public import VoterProcess.Step


@[expose] public section
open Finset MeasureTheory
open scoped BigOperators Classical

noncomputable section

namespace VoterModel

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- \label{def:stopping-times}
Volume excursion time (`T_{i_{min}}`).

The first time `t ≥ t₀` (up to `tMax`) that the volume of `S_t` has changed by a factor
of at least `3/2` or `1/2` compared to its volume at time `t₀`, or `S_t = ∅`. That is,
`Vol(S_t) ∉ [Vol(S_{t₀})/2, 3·Vol(S_{t₀})/2]` or `S_t = ∅`. Returns `tMax + 1` if
the volume stays within the band throughout `[t₀, tMax]`.

Note: the condition `S_t = ∅` is implied by `2·Vol(S_t) < Vol(S_{t₀})` when `Vol(S_{t₀}) > 0`,
since `Vol(∅) = 0`. -/
def volumeExcursionTime
    (G : TemporalGraph V) (vm : TemporalGraph.VoterModelAbstract G 2 Ω)
    (t₀ tMax : ℕ) (ω : Ω) : ℕ :=
  let v₀ := TemporalGraph.volume G t₀ (vm.S t₀ ω)
  let candidates := (Finset.Icc t₀ tMax).filter fun t =>
    2 * TemporalGraph.volume G t (vm.S t ω) < v₀ ∨
    3 * v₀ < 2 * TemporalGraph.volume G t (vm.S t ω)
  if h : candidates.Nonempty then candidates.min' h else tMax + 1

/-- \label{def:stopping-times}
Stopping times `T₀ = 0, T₁, T₂, …`, defined by induction on `j`.

Let `T₀ = 0`. Given `T_j` and positive integers `Δ_0, Δ_1, …`, let
`I_j^+ = Δ_0 + ⋯ + Δ_j - 1` (the last time index of interval `j`). Then
```
T_{j+1} = min(I_j^+ + 1, T_{j_min})
```
where `T_{j_min}` is the first time `t ≥ T_j` at which the volume of `S_t` leaves
`[Vol(S_{T_j})/2, 3·Vol(S_{T_j})/2]` or `S_t = ∅`, searched within `[T_j, I_j^+]`.
Equivalently, `T_{j+1} = volumeExcursionTime G vm T_j (I_j^+)`, which automatically
returns `I_j^+ + 1` when no excursion occurs in `[T_j, I_j^+]`. -/
def embeddedChainTime
    -- Temporal graph
    (G : TemporalGraph V)
    -- Voter model process (S_t)(ω)
    (vm : TemporalGraph.VoterModelAbstract G 2 Ω)
    -- Interval lengths Δ_0, Δ_1, …  (each should be ≥ 1)
    (Δ : ℕ → ℕ) : ℕ → Ω → ℕ
  | 0, _ => 0
  | i + 1, ω =>
    let tᵢ := embeddedChainTime G vm Δ i ω
    -- I_i^+ = (Δ_0 + … + Δ_i) - 1
    let cap := (∑ j ∈ Finset.range (i + 1), Δ j) - 1
    volumeExcursionTime G vm tᵢ cap ω

/-- \label{def:embedded-voter-process}

Let `(𝒢_t)` be a temporal graph and let `(S_t)` be the minority set process of
a voter model on `(𝒢_t)`. The *embedded voter process* is `((T_j, S_{T_j}) : j ≥ 0)`,
sampling the minority set only at the stopping times `T₀, T₁, …`
from `def:stopping-times`. -/
def embeddedVoterProcess {α : Type*} (S : ℕ → Ω → α) (T : ℕ → Ω → ℕ) : ℕ → Ω → ℕ × α :=
  fun i ω => (T i ω, S (T i ω) ω)

/-- \label{stmt:are-stopping-times}

When `t₀ ≤ tMax`, the volume excursion time is strictly greater than `t₀`. -/
theorem lt_volumeExcursionTime
    (G : TemporalGraph V) (vm : TemporalGraph.VoterModelAbstract G 2 Ω)
    (t₀ tMax : ℕ) (ω : Ω) (h : t₀ ≤ tMax) :
    t₀ < volumeExcursionTime G vm t₀ tMax ω := by
  unfold volumeExcursionTime
  dsimp only
  set v₀ := TemporalGraph.volume G t₀ (vm.S t₀ ω)
  set candidates := (Finset.Icc t₀ tMax).filter fun t =>
    2 * TemporalGraph.volume G t (vm.S t ω) < v₀ ∨
    3 * v₀ < 2 * TemporalGraph.volume G t (vm.S t ω)
  split
  · rename_i hne
    have hmin_mem := Finset.min'_mem candidates hne
    have hfilt := Finset.mem_filter.mp hmin_mem
    have hge : t₀ ≤ candidates.min' hne := (Finset.mem_Icc.mp hfilt.1).1
    have hne_t₀ : candidates.min' hne ≠ t₀ := by
      intro heq
      have := hfilt.2
      rw [heq] at this
      omega
    omega
  · omega

/-- The volume excursion time is at most `tMax + 1`. -/
theorem volumeExcursionTime_le_succ
    (G : TemporalGraph V) (vm : TemporalGraph.VoterModelAbstract G 2 Ω)
    (t₀ tMax : ℕ) (ω : Ω) :
    volumeExcursionTime G vm t₀ tMax ω ≤ tMax + 1 := by
  unfold volumeExcursionTime; simp only
  split
  · rename_i hne
    have hmem := Finset.min'_mem _ hne
    have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hmem).1).2
    exact Nat.le_succ_of_le (Finset.min'_le _ _ hmem |>.trans this)
  · exact le_refl _

/-- Before the volume excursion time, the upper excursion condition does not hold:
`2 · Vol(S_j) ≤ 3 · Vol(S_{t₀})`. -/
theorem volumeExcursionTime_vol_le
    (G : TemporalGraph V) (vm : TemporalGraph.VoterModelAbstract G 2 Ω)
    (t₀ tMax j : ℕ) (ω : Ω)
    (h_lo : t₀ ≤ j) (h_hi : j < volumeExcursionTime G vm t₀ tMax ω) :
    2 * TemporalGraph.volume G j (vm.S j ω) ≤ 3 * TemporalGraph.volume G t₀ (vm.S t₀ ω) := by
  have hj_le : j ≤ tMax := by
    have := volumeExcursionTime_le_succ G vm t₀ tMax ω; omega
  by_contra h
  push Not at h
  have hmem : j ∈ (Finset.Icc t₀ tMax).filter (fun t =>
      2 * TemporalGraph.volume G t (vm.S t ω) < TemporalGraph.volume G t₀ (vm.S t₀ ω) ∨
      3 * TemporalGraph.volume G t₀ (vm.S t₀ ω) < 2 * TemporalGraph.volume G t (vm.S t ω)) :=
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h_lo, hj_le⟩, Or.inr h⟩
  have hne : ((Finset.Icc t₀ tMax).filter _).Nonempty := ⟨j, hmem⟩
  have hvET_le : volumeExcursionTime G vm t₀ tMax ω ≤ j := by
    suffices volumeExcursionTime G vm t₀ tMax ω ≤ j from this
    unfold volumeExcursionTime; simp only
    simp [hne]
    exact Finset.min'_le _ _ hmem
  omega

/-- Before the volume excursion time, the lower excursion condition does not hold:
`Vol(S_{t₀}) ≤ 2 · Vol(S_j)`. -/
theorem volumeExcursionTime_vol_ge
    (G : TemporalGraph V) (vm : TemporalGraph.VoterModelAbstract G 2 Ω)
    (t₀ tMax j : ℕ) (ω : Ω)
    (h_lo : t₀ ≤ j) (h_hi : j < volumeExcursionTime G vm t₀ tMax ω) :
    TemporalGraph.volume G t₀ (vm.S t₀ ω) ≤ 2 * TemporalGraph.volume G j (vm.S j ω) := by
  have hj_le : j ≤ tMax := by
    have := volumeExcursionTime_le_succ G vm t₀ tMax ω; omega
  by_contra h
  push Not at h
  have hmem : j ∈ (Finset.Icc t₀ tMax).filter (fun t =>
      2 * TemporalGraph.volume G t (vm.S t ω) < TemporalGraph.volume G t₀ (vm.S t₀ ω) ∨
      3 * TemporalGraph.volume G t₀ (vm.S t₀ ω) < 2 * TemporalGraph.volume G t (vm.S t ω)) :=
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h_lo, hj_le⟩, Or.inl h⟩
  have hne : ((Finset.Icc t₀ tMax).filter _).Nonempty := ⟨j, hmem⟩
  have hvET_le : volumeExcursionTime G vm t₀ tMax ω ≤ j := by
    suffices volumeExcursionTime G vm t₀ tMax ω ≤ j from this
    unfold volumeExcursionTime; simp only
    simp [hne]
    exact Finset.min'_le _ _ hmem
  omega

/-- Before the volume excursion time, the minority set is nonempty, given the initial
set is nonempty and degrees are positive. -/
theorem volumeExcursionTime_S_nonempty
    (G : TemporalGraphFixedDegree V)
    (vm : G.VoterModelAbstract 2 Ω)
    (t₀ tMax j : ℕ) (ω : Ω)
    (h_lo : t₀ ≤ j) (h_hi : j < volumeExcursionTime G.toTemporalGraph vm t₀ tMax ω)
    (h₀ : (vm.S t₀ ω).Nonempty) :
    (vm.S j ω).Nonempty := by
  have hv₀_pos : 0 < TemporalGraph.volume G.toTemporalGraph t₀ (vm.S t₀ ω) :=
    (G.snapshot t₀).volume_pos_of_nonempty h₀ (fun v => G.degrees_pos v t₀)
  have hge := volumeExcursionTime_vol_ge G.toTemporalGraph vm t₀ tMax j ω h_lo h_hi
  rcases (vm.S j ω).eq_empty_or_nonempty with he | hne
  · exfalso
    rw [he] at hge
    have hzero : TemporalGraph.volume G j (∅ : Finset V) = 0 := by
      show (G.snapshot j).volume ∅ = 0
      simp [SimpleGraph.volume]
    linarith
  · exact hne

/-- \label{stmt:are-stopping-times}

The embedded chain times are strictly increasing: `T_i(ω) < T_{i+1}(ω)`, provided
`T_i(ω) ≤ I_i^+ = (Δ_0 + … + Δ_i) - 1` (the cap for interval `i+1`). -/
theorem embeddedChainTime_strictMono
    (G : TemporalGraph V)
    (vm : TemporalGraph.VoterModelAbstract G 2 Ω)
    (Δ : ℕ → ℕ) (i : ℕ) (ω : Ω)
    -- T_i(ω) ≤ I_i^+ = (∑_{j ≤ i} Δ_j) - 1
    (hT_le : embeddedChainTime G vm Δ i ω ≤ (∑ j ∈ Finset.range (i + 1), Δ j) - 1) :
    embeddedChainTime G vm Δ i ω < embeddedChainTime G vm Δ (i + 1) ω := by
  simp only [embeddedChainTime]
  exact lt_volumeExcursionTime G vm _ _ ω hT_le

/-! ### Stopping time property

The embedded chain times `T₀, T₁, …` are stopping times w.r.t. any filtration to which
`S` is adapted (i.e., each `S t` is `ℱ t`-measurable with the discrete σ-algebra on
`Finset V`).

1. **`volumeExcursionTime`** depends on `ω` through `(S t₀ ω, …, S tMax ω)`.
   For `j ≤ tMax`, `{T_min = j}` depends on `S` at times `≤ j`, so lies in `ℱ j`.

2. **`embeddedChainTime`** is proved by induction: `T₀ = 0` is a stopping time
   by `isStoppingTime_const`, and the inductive step decomposes over `{T_i = k}`.
   The key simplification over the old proof: the cap `I_i^+` is deterministic, so
   `T_{i+1}(ω) = volumeExcursionTime G vm (T_i ω) cap ω` with deterministic `cap`. No
   further decomposition over a random upper bound is needed.
-/

-- Helper: ↑(min a b) = min ↑a ↑b in ℕ∞ (not in Mathlib for WithTop).

-- Helper: pair of ⊤-measurable functions (countable first component) is ⊤-measurable.
omit mΩ in
private lemma measurable_pair_top
    {mΩ' : MeasurableSpace Ω} {α β : Type*} [Countable α]
    {f : Ω → α} {g : Ω → β}
    (hf : @Measurable Ω α mΩ' ⊤ f) (hg : @Measurable Ω β mΩ' ⊤ g) :
    @Measurable Ω (α × β) mΩ' ⊤ (fun ω => (f ω, g ω)) := by
  intro B _
  have : (fun ω => (f ω, g ω)) ⁻¹' B =
      ⋃ a : α, (f ⁻¹' {a} ∩ g ⁻¹' {b | (a, b) ∈ B}) := by
    ext ω; simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
    exact ⟨fun h => ⟨f ω, rfl, h⟩, fun ⟨a, ha, hb⟩ => ha ▸ hb⟩
  rw [this]
  exact .iUnion fun a => (hf trivial).inter (hg trivial)

-- Helper: tuple of ⊤-measurable functions (Fintype domain/codomain) is ⊤-measurable.

-- Helper: S t is ℱ n-⊤-measurable when t ≤ n (filtration monotonicity).
omit [Nonempty V] [Fintype V] [DecidableEq V] mΩ in
private lemma adapted_le
    {mΩ' : MeasurableSpace Ω} {ℱ : MeasureTheory.Filtration ℕ mΩ'}
    {S : ℕ → Ω → Finset V}
    (hS : ∀ t, @Measurable Ω (Finset V) (ℱ t) ⊤ (S t))
    {t n : ℕ} (h : t ≤ n) : @Measurable Ω (Finset V) (ℱ n) ⊤ (S t) :=
  fun _ hA => (ℱ.mono' h) _ ((hS t) hA)

open MeasureTheory in

open MeasureTheory in
/-- \label{stmt:are-stopping-times}

For fixed `t₀` and `tMax`, `volumeExcursionTime G S t₀ tMax` depends on `ω` only through
`(S t₀ ω, …, S tMax ω)`, so it is `ℱ tMax`-measurable and hence a stopping time. -/
theorem volumeExcursionTime_isStoppingTime
    {ℱ : Filtration ℕ mΩ}
    (G : TemporalGraph V) (vm : TemporalGraph.VoterModelAbstract G 2 Ω)
    (hS : ∀ t, @Measurable Ω (Finset V) (ℱ t) ⊤ (vm.S t))
    (t₀ tMax : ℕ) :
    IsStoppingTime ℱ (fun ω => (volumeExcursionTime G vm t₀ tMax ω : ℕ∞)) := by
  by_cases htMax : tMax < t₀
  · -- Case 1: t₀ > tMax ⟹ Icc t₀ tMax = ∅ ⟹ candidates = ∅ ⟹ vET = tMax + 1 (constant)
    have hconst : (fun ω => (volumeExcursionTime G vm t₀ tMax ω : ℕ∞)) = fun _ => ↑(tMax + 1) := by
      ext ω
      simp only [volumeExcursionTime]
      have hempty : (Finset.Icc t₀ tMax).filter (fun t =>
        2 * TemporalGraph.volume G t (vm.S t ω) < TemporalGraph.volume G t₀ (vm.S t₀ ω) ∨
        3 * TemporalGraph.volume G t₀ (vm.S t₀ ω) < 2 * TemporalGraph.volume G t (vm.S t ω)) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro x hx
        have := (Finset.mem_Icc.mp hx)
        omega
      simp [hempty]
    rw [hconst]
    exact isStoppingTime_const ℱ (↑(tMax + 1))
  · -- Case 2: t₀ ≤ tMax
    push Not at htMax
    -- Direct definition: show ∀ n, {vET ≤ n} ∈ ℱ n.
    intro n
    show @MeasurableSet Ω (ℱ n) {ω | (volumeExcursionTime G vm t₀ tMax ω : ℕ∞) ≤ ↑n}
    -- Auxiliary: vET ≤ tMax + 1 always
    have hvET_le : ∀ ω, volumeExcursionTime G vm t₀ tMax ω ≤ tMax + 1 := by
      intro ω; unfold volumeExcursionTime; simp only
      split
      · rename_i hne
        have hmem := Finset.min'_mem _ hne
        have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hmem).1).2
        exact Nat.le_succ_of_le (Finset.min'_le _ _ hmem |>.trans this)
      · exact le_refl _
    -- Auxiliary: vET > t₀
    have hvET_gt : ∀ ω, t₀ < volumeExcursionTime G vm t₀ tMax ω :=
      fun ω => lt_volumeExcursionTime G vm t₀ tMax ω htMax
    by_cases hn_high : tMax < n
    · -- n > tMax ⟹ {vET ≤ n} = Ω (since vET ≤ tMax + 1 ≤ n)
      convert @MeasurableSet.univ Ω (ℱ n)
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      have : (volumeExcursionTime G vm t₀ tMax ω : ℕ∞) ≤ ↑(tMax + 1) := by
        exact_mod_cast hvET_le ω
      exact this.trans (by exact_mod_cast (by omega : tMax + 1 ≤ n))
    · push Not at hn_high -- n ≤ tMax
      by_cases hn_low : n ≤ t₀
      · -- n ≤ t₀ ⟹ {vET ≤ n} = ∅ (since vET > t₀ ≥ n)
        convert @MeasurableSet.empty Ω (ℱ n)
        ext ω; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
        have : (↑n : ℕ∞) < ↑(volumeExcursionTime G vm t₀ tMax ω) := by
          exact_mod_cast lt_of_le_of_lt hn_low (hvET_gt ω)
        exact this
      · -- t₀ < n ≤ tMax: the interesting case
        push Not at hn_low
        -- {vET ≤ n} = ⋃ t ∈ Icc t₀ n, {ω | volume excursion condition at t}
        -- Key equivalence: vET ≤ n ↔ ∃ t ∈ Icc t₀ n, excursion(t, ω)
        -- Each excursion condition at t depends on (S t₀ ω, S t ω), ℱ n-measurable
        -- Define the excursion predicate for readability
        set excursion := fun (t : ℕ) (ω : Ω) =>
          2 * TemporalGraph.volume G t (vm.S t ω) < TemporalGraph.volume G t₀ (vm.S t₀ ω) ∨
          3 * TemporalGraph.volume G t₀ (vm.S t₀ ω) < 2 * TemporalGraph.volume G t (vm.S t ω)
          with hexcursion_def
        -- Step 1: Rewrite {vET ≤ n} = ⋃ t ∈ Icc t₀ n, {ω | excursion t ω}
        have hset_eq : {ω : Ω | (volumeExcursionTime G vm t₀ tMax ω : ℕ∞) ≤ ↑n} =
            ⋃ t ∈ Finset.Icc t₀ n, {ω : Ω | excursion t ω} := by
          ext ω
          simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_Icc]
          constructor
          · -- vET ≤ n → ∃ candidate ≤ n
            intro hle
            have hle' : volumeExcursionTime G vm t₀ tMax ω ≤ n := by exact_mod_cast hle
            unfold volumeExcursionTime at hle'
            simp only at hle'
            split at hle'
            · rename_i hne
              -- min' candidates ≤ n, so min' is a candidate ≤ n ≤ tMax, hence in Icc t₀ n
              have hmin_mem := Finset.min'_mem _ hne
              have hfilt := Finset.mem_filter.mp hmin_mem
              have hIcc := Finset.mem_Icc.mp hfilt.1
              exact ⟨_, ⟨hIcc.1, hle'⟩, hfilt.2⟩
            · omega -- tMax + 1 ≤ n but n ≤ tMax, contradiction
          · -- ∃ candidate ≤ n → vET ≤ n
            rintro ⟨t, ⟨ht_lo, ht_hi⟩, hcond⟩
            suffices h : volumeExcursionTime G vm t₀ tMax ω ≤ n by exact_mod_cast h
            unfold volumeExcursionTime
            simp only
            have hmem : t ∈ (Finset.Icc t₀ tMax).filter (fun t =>
              2 * TemporalGraph.volume G t (vm.S t ω) < TemporalGraph.volume G t₀ (vm.S t₀ ω) ∨
              3 * TemporalGraph.volume G t₀ (vm.S t₀ ω) < 2 * TemporalGraph.volume G t (vm.S t ω)) := by
              rw [Finset.mem_filter, Finset.mem_Icc]
              exact ⟨⟨ht_lo, le_trans ht_hi hn_high⟩, hcond⟩
            have hne : ((Finset.Icc t₀ tMax).filter _).Nonempty := ⟨t, hmem⟩
            simp [hne]
            exact le_trans (Finset.min'_le _ _ hmem) ht_hi
        rw [hset_eq]
        -- Step 2: Each {ω | excursion t ω} is ℱ n-measurable (for t ≤ n)
        apply MeasurableSet.biUnion (Finset.Icc t₀ n).finite_toSet.countable
        intro t ht
        have ht_le_n : t ≤ n := (Finset.mem_Icc.mp ht).2
        -- excursion t ω depends on (S t₀ ω, S t ω), preimage under ℱ n-measurable pair
        have hpair_meas : @Measurable Ω (Finset V × Finset V) (ℱ n) ⊤
            (fun ω => (vm.S t₀ ω, vm.S t ω)) :=
          measurable_pair_top (adapted_le hS (by omega)) (adapted_le hS ht_le_n)
        -- {ω | excursion t ω} is a preimage under (vm.S t₀, vm.S t)
        have : {ω : Ω | excursion t ω} =
            (fun ω => (vm.S t₀ ω, vm.S t ω)) ⁻¹'
            {p : Finset V × Finset V |
              2 * TemporalGraph.volume G t p.2 < TemporalGraph.volume G t₀ p.1 ∨
              3 * TemporalGraph.volume G t₀ p.1 < 2 * TemporalGraph.volume G t p.2} := by
          ext ω; simp [hexcursion_def]
        rw [this]
        exact hpair_meas trivial

open MeasureTheory in
/-- \label{stmt:are-stopping-times}

The embedded chain times `T₀, T₁, T₂, …` are stopping times w.r.t. any filtration
to which the process `S` is adapted. No admissibility hypothesis is needed; the
deterministic cap `I_i^+` makes the inductive step direct. -/
theorem embeddedChainTime_isStoppingTime
    {ℱ : Filtration ℕ mΩ}
    (G : TemporalGraph V)
    (vm : TemporalGraph.VoterModelAbstract G 2 Ω)
    (Δ : ℕ → ℕ)
    (hS : ∀ t, @Measurable Ω (Finset V) (ℱ t) ⊤ (vm.S t))
    (i : ℕ) :
    IsStoppingTime ℱ (fun ω => (embeddedChainTime G vm Δ i ω : ℕ∞)) := by
  induction i with
  | zero =>
    -- T₀ = 0 for all ω
    exact isStoppingTime_const ℱ 0
  | succ i ih =>
    -- T_{i+1}(ω) = vET(T_i(ω), cap, ω) where cap = I_i^+ is deterministic
    intro n
    show @MeasurableSet Ω (ℱ n) {ω | (embeddedChainTime G vm Δ (i + 1) ω : ℕ∞) ≤ ↑n}
    -- cap = I_i^+ is deterministic (depends only on Δ and i, not ω)
    set cap := (∑ j ∈ Finset.range (i + 1), Δ j) - 1 with hcap_def
    -- Decompose: {T_{i+1} ≤ n}
    --   = (⋃_{k ≤ n} {T_i = k} ∩ {vET(k, cap) ≤ n})  ∪  ({T_i > cap} ∩ {cap+1 ≤ n})
    -- Key cases:
    --   k ≤ n: {T_i = k} ∈ ℱ k ⊆ ℱ n; {vET(k,cap) ≤ n} ∈ ℱ n (vET is a stopping time)
    --   n < k ≤ cap: vET(k,cap) ≥ k+1 > n (by lt_volumeExcursionTime), so {vET(k,cap) ≤ n} = ∅
    --   k > cap: vET(k,cap) = cap+1; only nonempty when cap+1 ≤ n, giving {T_i > cap} ∈ ℱ cap ⊆ ℱ n
    -- Step 1: Show {T_{i+1} ≤ n} = ⋃_{k ≤ n} {T_i = k} ∩ {vET(k,cap) ≤ n} ∪ {T_i > cap} ∩ {cap+1 ≤ n}
    have hdecomp : {ω | (embeddedChainTime G vm Δ (i + 1) ω : ℕ∞) ≤ ↑n} =
        (⋃ k ∈ Finset.range (n + 1), {ω | (embeddedChainTime G vm Δ i ω : ℕ∞) = ↑k} ∩
          {ω | (volumeExcursionTime G vm k cap ω : ℕ∞) ≤ ↑n}) ∪
        ({ω | (cap : ℕ∞) < embeddedChainTime G vm Δ i ω} ∩
          {ω | (cap + 1 : ℕ∞) ≤ ↑n}) := by
      ext ω
      simp only [embeddedChainTime, Set.mem_setOf_eq, Set.mem_union, Set.mem_iUnion,
        Finset.mem_range, Set.mem_inter_iff]
      constructor
      · intro h_le
        -- T_{i+1} = vET(T_i, cap) ≤ n
        -- Case 1: T_i ≤ n → first part
        -- Case 2: T_i > cap → vET = cap+1 ≤ n → second part
        -- Case 3: n < T_i ≤ cap → vET ≥ T_i+1 > n, contradiction
        by_cases hTi_le : embeddedChainTime G vm Δ i ω ≤ n
        · left
          exact ⟨embeddedChainTime G vm Δ i ω, by exact_mod_cast Nat.lt_succ_of_le hTi_le, rfl, h_le⟩
        · push Not at hTi_le
          by_cases hTi_cap : embeddedChainTime G vm Δ i ω ≤ cap
          · -- n < T_i ≤ cap: vET(T_i, cap) > T_i > n. Contradiction.
            exfalso
            have hvET_gt : embeddedChainTime G vm Δ i ω <
                volumeExcursionTime G vm (embeddedChainTime G vm Δ i ω) cap ω :=
              lt_volumeExcursionTime G vm _ _ ω hTi_cap
            have hvET_le : volumeExcursionTime G vm (embeddedChainTime G vm Δ i ω) cap ω ≤ n := by
              exact_mod_cast h_le
            omega
          · -- T_i > cap: vET(T_i, cap) = cap+1 ≤ n
            right
            push Not at hTi_cap
            constructor
            · exact_mod_cast hTi_cap
            · -- T_{i+1} = vET(T_i, cap) = cap+1 ≤ n
              -- Need: vET(T_i, cap) = cap+1 when T_i > cap
              have hvET_eq : volumeExcursionTime G vm (embeddedChainTime G vm Δ i ω) cap ω =
                  cap + 1 := by
                unfold volumeExcursionTime; dsimp only
                simp [Finset.Icc_eq_empty (by omega : ¬ (embeddedChainTime G vm Δ i ω ≤ cap))]
              -- T_{i+1} = vET(T_i, cap) = cap+1 ≤ n
              have hcast : (embeddedChainTime G vm Δ (i+1) ω : ℕ∞) = cap + 1 := by
                exact_mod_cast hvET_eq
              rw [← hcast]; exact h_le
      · rintro (⟨k, hk, hk_eq, hle⟩ | ⟨hcap_lt, hle⟩)
        · -- First part: T_i = k ≤ n, vET(k, cap) ≤ n
          have hk_val : embeddedChainTime G vm Δ i ω = k := WithTop.coe_injective hk_eq
          simp only [hk_val]
          exact hle
        · -- Second part: T_i > cap, cap+1 ≤ n
          have hTi_gt : cap < embeddedChainTime G vm Δ i ω := by exact_mod_cast hcap_lt
          have hvET_eq : volumeExcursionTime G vm (embeddedChainTime G vm Δ i ω) cap ω = cap + 1 := by
            unfold volumeExcursionTime; dsimp only
            simp [Finset.Icc_eq_empty (by omega : ¬ (embeddedChainTime G vm Δ i ω ≤ cap))]
          show (volumeExcursionTime G vm (embeddedChainTime G vm Δ i ω) cap ω : ℕ∞) ≤ ↑n
          rw [hvET_eq]; exact hle
    rw [hdecomp]
    apply MeasurableSet.union
    · -- ⋃_{k ≤ n} {T_i = k} ∩ {vET(k, cap) ≤ n}
      apply MeasurableSet.biUnion (Finset.range (n + 1)).countable_toSet
      intro k hk
      have hk_le : k ≤ n := by simp only [Finset.coe_range, Set.mem_Iio] at hk; omega
      apply MeasurableSet.inter
      · -- {T_i = k} ∈ ℱ k ⊆ ℱ n
        exact ℱ.mono' hk_le _ (ih.measurableSet_eq_of_countable k)
      · -- {vET(k, cap) ≤ n} ∈ ℱ n: vET with deterministic cap is a stopping time
        exact (volumeExcursionTime_isStoppingTime G vm hS k cap) n
    · -- {T_i > cap} ∩ {cap+1 ≤ n}
      by_cases hcap_n : cap < n
      · -- cap < n: both components measurable in ℱ n
        apply MeasurableSet.inter
        · -- {T_i > cap} = {T_i ≤ cap}ᶜ ∈ ℱ cap ⊆ ℱ n
          have hcap_le : cap ≤ n := le_of_lt hcap_n
          have hmeas_le : @MeasurableSet Ω (ℱ cap) {ω | (embeddedChainTime G vm Δ i ω : ℕ∞) ≤ cap} :=
            ih cap
          have hset_eq : {ω : Ω | (cap : ℕ∞) < embeddedChainTime G vm Δ i ω} =
              {ω | (embeddedChainTime G vm Δ i ω : ℕ∞) ≤ cap}ᶜ := by ext ω; simp [not_le]
          exact ℱ.mono' hcap_le _ (hset_eq ▸ hmeas_le.compl)
        · -- {cap+1 ≤ n}: constant set, measurable
          by_cases h : cap + 1 ≤ n
          · convert @MeasurableSet.univ Ω (ℱ n)
            ext ω; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
            exact_mod_cast h
          · convert @MeasurableSet.empty Ω (ℱ n)
            ext ω; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
            exact_mod_cast h
      · -- cap ≥ n: whole intersection is ∅ since {cap+1 ≤ n} = ∅
        push Not at hcap_n  -- hcap_n : n ≤ cap
        convert @MeasurableSet.empty Ω (ℱ n)
        have hlt : ¬ (cap + 1 ≤ n) := by omega
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
          not_and]
        intro _
        exact_mod_cast hlt

end VoterModel
