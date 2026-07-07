module

public import Mathlib.Probability.Process.Stopping
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import VoterProcess.OpinionCoupling

/-! ## §3.4 multi-opinion metaphase scaffolding (Tier A)

Deterministic and measurable-theoretic scaffolding for the §3.4 argument that
derives the multi-opinion absorption bound from the two-opinion bound
(`sections/3.4_multi_opinion.tex`). This file provides **only** the definitions,
their basic monotonicity, and the measurability / stopping-time facts. The actual
probability bounds (the §3.4 "Claim" and the Markov-inequality accounting) live
elsewhere (e.g. `MultiOpinionCoupling.claim_Xq_le_half`).

The objects formalized (with their paper names):

- `opinionSet`/`numOpinions` — the set `𝒪(t)` of opinions present at time `t`.
- `phaseIndex φ r` — `ℓ_r = min{ℓ : ∑_{j<ℓ} φ_j ≥ r}` (deterministic phase index).
- `phaseTime Δ φ r` — `t_r = ∑_{j<ℓ_r} Δ_j` (start time of the `r`'th phase).
- `rMax B m d_min` — `r_max = ⌊Bm/d_min⌋`.
- `beta κ` — `β = ⌈log_{1/ρ} κ⌉`, the metaphase count (base `1/ρ = 7/6`).
- `xiAlpha b m d_min |O_α|` — `ξ_α`, the per-metaphase phase budget.
- `metaphase vm B m d_min Δ φ α` — the random metaphase index `R_α`.
- `phaseFiltration vm Δ φ` — the coarse filtration `𝒢_r = ℱ_{t_r}`.
- `Xq vm q s` — the indicator `X_q` (opinion `q` neither vanished nor took over).
- `smallOpinions vm s O_α m` — the small opinions `O_{t_r}^-`.

## Main results

- `isConsensus_iff_opinionSet_card_one` — consensus ⇔ `|𝒪(t)| = 1`.
- `phaseIndex_mono`, `phaseTime_mono` — monotonicity in `r` (given reachability).
- `opinionSet_measurable`, `numOpinions_measurable`, `Xq_measurable`,
  `smallOpinions_measurable` — measurability w.r.t. `ℱ_s`.
- `metaphase_mono`, `metaphase_le_rMax` — monotone in `α`, capped by `r_max`.
- `metaphase_le_measurable`, `metaphase_eq_measurable` — `{R_α ≤ r}` / `{R_α = r}`
  are `ℱ_{t_r}`-measurable.
- `metaphase_isStoppingTime` — `R_α` is a stopping time for `𝒢_r`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Classical

noncomputable section

namespace TemporalGraph

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V] {κ : ℕ} [NeZero κ]
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {G : TemporalGraph V}

/-! ### Deterministic phase scaffolding -/

/-- `ℓ_r`, the (deterministic) index of the first prefix of the `φ`-budget that
reaches level `r`, taken as a **running maximum** of the bare
`sInf {ℓ : ∑_{j<ℓ} φ_j ≥ r'}` over all `r' ≤ r`.

The bare `sInf` collapses to `0` once `r` exceeds the total budget (`sInf ∅ = 0`),
which would break monotonicity; the running maximum keeps `phaseIndex` flat in the
unreachable region. On the reachable range the two agree
(`phaseIndex_eq_of_reachable`), so all phase-budget facts are recovered, while
`phaseIndex_mono` now holds with **no reachability hypothesis**. -/
def phaseIndex (φ : ℕ → ℝ) (r : ℕ) : ℕ :=
  (Finset.range (r + 1)).sup (fun r' => sInf {ℓ | (r' : ℝ) ≤ ∑ j ∈ Finset.range ℓ, φ j})

/-- `t_r = ∑_{j<ℓ_r} Δ_j`, the start time of the `r`'th phase. -/
def phaseTime (Δ : ℕ → ℕ) (φ : ℕ → ℝ) (r : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (phaseIndex φ r), Δ j

/-- `r_max = ⌊Bm/d_min⌋`, the cap on the number of phases. -/
def rMax (B : ℝ) (m d_min : ℕ) : ℕ := ⌊B * (m : ℝ) / (d_min : ℝ)⌋₊

/-- **Bounded reachability.** Every level `r ≤ r_max` is reached by some prefix of
the `φ`-budget. This is the faithful (paper-`J < ∞`) replacement for *global*
reachability: the metaphase counters never exceed `r_max`
(`metaphase_le_rMax`), so reachability is only ever needed up to the cap, and the
bound `r ≤ r_max ≤ ⌊∑_{j ≤ J} φ_j⌋` is exactly what the finite phase budget `hJ`
supplies. -/
def reachUpToRMax (B : ℝ) (m d_min : ℕ) (φ : ℕ → ℝ) : Prop :=
  ∀ r : ℕ, r ≤ rMax B m d_min → ∃ ℓ, (r : ℝ) ≤ ∑ j ∈ Finset.range ℓ, φ j

/-- `β = ⌈log_{1/ρ} κ⌉` with shrink factor `ρ = 6/7`; the number of metaphases
needed to drop below one opinion. -/
def beta (κ : ℕ) : ℕ := ⌈Real.logb (7 / 6) (κ : ℝ)⌉₊

/-- `ξ_α = 1 + ⌈ b·(τm/(d_min·|O_α|) + log(1 + τm/|O_α|)) ⌉` with volume-threshold
factor `τ = 14/3`, the per-metaphase phase budget from the §3.4 Claim. -/
def xiAlpha (b m d_min : ℝ) (Oα_card : ℕ) : ℕ :=
  1 + ⌈b * (14 * m / (3 * (d_min * (Oα_card : ℝ)))
        + Real.log (1 + 14 * m / (3 * (Oα_card : ℝ))))⌉₊

/-- The phase-index `ℓ_r` is monotone in `r`, **unconditionally**: it is a running
maximum over the growing index set `range (r+1)`. -/
theorem phaseIndex_mono (φ : ℕ → ℝ) : Monotone (phaseIndex φ) := by
  intro r r' hr
  have hsub : Finset.range (r + 1) ⊆ Finset.range (r' + 1) := by
    intro x hx; rw [Finset.mem_range] at hx ⊢; omega
  exact Finset.sup_mono hsub

/-- The phase start time `t_r` is monotone in `r`, **unconditionally**. -/
theorem phaseTime_mono (Δ : ℕ → ℕ) (φ : ℕ → ℝ) : Monotone (phaseTime Δ φ) := by
  intro r r' hr
  have hsub : Finset.range (phaseIndex φ r) ⊆ Finset.range (phaseIndex φ r') := by
    intro x hx; rw [Finset.mem_range] at hx ⊢
    exact lt_of_lt_of_le hx (phaseIndex_mono φ hr)
  show (∑ j ∈ Finset.range (phaseIndex φ r), Δ j)
    ≤ ∑ j ∈ Finset.range (phaseIndex φ r'), Δ j
  exact Finset.sum_le_sum_of_subset hsub

/-- On the reachable range the running-maximum `phaseIndex` agrees with the bare
`sInf`. If level `r` is reachable then every `r' ≤ r` is too (reachability is
downward closed) and the bare `sInf` is monotone there, so the running maximum is
attained at `r' = r`. -/
theorem phaseIndex_eq_of_reachable (φ : ℕ → ℝ) {r : ℕ}
    (hr : ∃ ℓ, (r : ℝ) ≤ ∑ j ∈ Finset.range ℓ, φ j) :
    phaseIndex φ r = sInf {ℓ | (r : ℝ) ≤ ∑ j ∈ Finset.range ℓ, φ j} := by
  unfold phaseIndex
  apply le_antisymm
  · apply Finset.sup_le
    intro r' hr'
    have hr'r : r' ≤ r := by rw [Finset.mem_range] at hr'; omega
    have hmem := Nat.sInf_mem hr
    apply Nat.sInf_le
    simp only [Set.mem_setOf_eq] at hmem ⊢
    exact le_trans (by exact_mod_cast hr'r) hmem
  · exact Finset.le_sup (f := fun r' : ℕ => sInf {ℓ | (r' : ℝ) ≤ ∑ j ∈ Finset.range ℓ, φ j})
      (Finset.self_mem_range_succ r)

/-- If level `r` is reachable, the prefix budget at `ℓ_r` reaches `r`. -/
theorem phaseIndex_reach_ge (φ : ℕ → ℝ) {r : ℕ}
    (hr : ∃ ℓ, (r : ℝ) ≤ ∑ j ∈ Finset.range ℓ, φ j) :
    (r : ℝ) ≤ ∑ j ∈ Finset.range (phaseIndex φ r), φ j := by
  rw [phaseIndex_eq_of_reachable φ hr]; exact Nat.sInf_mem hr

/-! ### Opinion set and consensus -/

/-- `𝒪(t) = {ξ_t(v) : v ∈ V}`, the set of opinions present at time `t`. -/
def VoterModelAbstract.opinionSet (vm : VoterModelAbstract G κ Ω) (t : ℕ) (ω : Ω) : Finset (Fin κ) :=
  Finset.univ.image (vm.ξ t ω)


/-- The number of opinions present is at most the number of vertices `n = |V|`
(the opinion set is the image of `ξ_t` on `V`). -/
theorem VoterModelAbstract.numOpinions_le_card (vm : VoterModelAbstract G κ Ω) (t : ℕ) (ω : Ω) :
    (vm.opinionSet t ω).card ≤ Fintype.card V := by
  calc (vm.opinionSet t ω).card
      = (Finset.univ.image (vm.ξ t ω)).card := rfl
    _ ≤ (Finset.univ : Finset V).card := Finset.card_image_le
    _ = Fintype.card V := Finset.card_univ

theorem VoterModelAbstract.mem_opinionSet (vm : VoterModelAbstract G κ Ω) {t : ℕ} {ω : Ω} {q : Fin κ} :
    q ∈ vm.opinionSet t ω ↔ ∃ v, vm.ξ t ω v = q := by
  simp [VoterModelAbstract.opinionSet, Finset.mem_image]

/-- Consensus is equivalent to having exactly one opinion present. -/
theorem isConsensus_iff_opinionSet_card_one (vm : VoterModelAbstract G κ Ω) (t : ℕ) (ω : Ω) :
    VoterModel.IsConsensus (vm.ξ t ω) ↔ (vm.opinionSet t ω).card = 1 := by
  obtain ⟨v0⟩ := ‹Nonempty V›
  constructor
  · intro h
    have hsing : vm.opinionSet t ω = {vm.ξ t ω v0} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨(vm.mem_opinionSet).mpr ⟨v0, rfl⟩, ?_⟩
      intro b hb
      obtain ⟨v, hv⟩ := (vm.mem_opinionSet).mp hb
      rw [← hv]; exact h v v0
    rw [hsing, Finset.card_singleton]
  · intro hcard u w
    rw [Finset.card_eq_one] at hcard
    obtain ⟨a, ha⟩ := hcard
    have hu : vm.ξ t ω u = a := by
      have : vm.ξ t ω u ∈ vm.opinionSet t ω := (vm.mem_opinionSet).mpr ⟨u, rfl⟩
      rw [ha, Finset.mem_singleton] at this; exact this
    have hw : vm.ξ t ω w = a := by
      have : vm.ξ t ω w ∈ vm.opinionSet t ω := (vm.mem_opinionSet).mpr ⟨w, rfl⟩
      rw [ha, Finset.mem_singleton] at this; exact this
    rw [hu, hw]

/-! ### Measurability scaffolding

All of the §3.4 random objects factor through the single configuration `ξ_s`, so
their events are finite Boolean combinations of the atoms `{ξ_s = g}`. -/

/-- `ξ_s` is measurable from `ℱ_s` to the discrete σ-algebra on `V → Fin κ`. -/
theorem VoterModelAbstract.xi_measurable_filtration (vm : VoterModelAbstract G κ Ω) (s : ℕ) :
    @Measurable Ω (V → Fin κ) (vm.ℱ s) ⊤ (vm.ξ s) :=
  measurable_iff_comap_le.mpr (le_iSup₂_of_le s (Finset.mem_Iic.mpr le_rfl) le_rfl)

/-- Any event of the form `{ω | P (ξ_s ω)}` is `ℱ_s`-measurable: it is the finite
union of the atoms `{ξ_s = g}` over `g` with `P g`. -/
theorem VoterModelAbstract.xi_event_filtration (vm : VoterModelAbstract G κ Ω) (s : ℕ)
    (P : (V → Fin κ) → Prop) :
    @MeasurableSet Ω (vm.ℱ s) {ω | P (vm.ξ s ω)} := by
  have heq : {ω | P (vm.ξ s ω)} = ⋃ g ∈ {g : V → Fin κ | P g}, {ω | vm.ξ s ω = g} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    exact ⟨fun h => ⟨vm.ξ s ω, h, rfl⟩, fun ⟨_, hg, hgω⟩ => hgω ▸ hg⟩
  rw [heq]
  refine MeasurableSet.biUnion (Set.toFinite _).countable (fun g _ => ?_)
  exact Measurable.of_comap_le (le_iSup₂_of_le s (Finset.mem_Iic.mpr le_rfl) le_rfl)
    (show @MeasurableSet (V → Fin κ) ⊤ {g} from trivial)

/-- `opinionSet` is `ℱ_s`-measurable into the discrete σ-algebra. -/
theorem VoterModelAbstract.opinionSet_measurable (vm : VoterModelAbstract G κ Ω) (s : ℕ) :
    @Measurable Ω (Finset (Fin κ)) (vm.ℱ s) ⊤ (fun ω => vm.opinionSet s ω) := by
  intro t _
  exact vm.xi_event_filtration s (fun g => Finset.univ.image g ∈ t)


/-- The event `{ω | |𝒪(s)| ≤ θ}` is `ℱ_s`-measurable. -/
theorem VoterModelAbstract.opinionCard_le_event_filtration (vm : VoterModelAbstract G κ Ω) (s θ : ℕ) :
    @MeasurableSet Ω (vm.ℱ s) {ω | (vm.opinionSet s ω).card ≤ θ} :=
  vm.xi_event_filtration s (fun g => (Finset.univ.image g).card ≤ θ)

/-- The §3.4 indicator `X_q`: `1` when opinion `q` is present but not the only one
(`q ∈ 𝒪(s)` and `𝒪(s) ≠ {q}`), i.e. the `q`-set is neither empty nor full. -/
def VoterModelAbstract.Xq (vm : VoterModelAbstract G κ Ω) (q : Fin κ) (s : ℕ) (ω : Ω) : ℝ :=
  if VoterModel.phiQ q (vm.ξ s ω) = ∅ ∨ VoterModel.phiQ q (vm.ξ s ω) = Finset.univ
  then 0 else 1

/-- `X_q` is `ℱ_s`-measurable. -/
theorem VoterModelAbstract.Xq_measurable (vm : VoterModelAbstract G κ Ω) (q : Fin κ) (s : ℕ) :
    @Measurable Ω ℝ (vm.ℱ s) _ (vm.Xq q s) :=
  (measurable_from_top (f := fun g : V → Fin κ =>
      if VoterModel.phiQ q g = ∅ ∨ VoterModel.phiQ q g = Finset.univ then (0 : ℝ) else 1)).comp
    (vm.xi_measurable_filtration s)

/-- `O_{t}^-`, the small opinions present at time `s`: opinions `q ∈ 𝒪(s)` whose
`q`-set has volume at most the threshold `τ·m/|O_α|` (with `τ = 14/3`). -/
def VoterModelAbstract.smallOpinions (vm : VoterModelAbstract G κ Ω) (s : ℕ) (Oα : Finset (Fin κ))
    (m : ℕ) (ω : Ω) : Finset (Fin κ) :=
  (vm.opinionSet s ω).filter
    (fun q => (TemporalGraph.volume G s (VoterModel.phiQ q (vm.ξ s ω)) : ℝ)
                ≤ 14 * (m : ℝ) / (3 * (Oα.card : ℝ)))

/-- `smallOpinions` is `ℱ_s`-measurable into the discrete σ-algebra. -/
theorem VoterModelAbstract.smallOpinions_measurable (vm : VoterModelAbstract G κ Ω) (s : ℕ)
    (Oα : Finset (Fin κ)) (m : ℕ) :
    @Measurable Ω (Finset (Fin κ)) (vm.ℱ s) ⊤ (fun ω => vm.smallOpinions s Oα m ω) := by
  intro t _
  exact vm.xi_event_filtration s
    (fun g => (Finset.univ.image g).filter
      (fun q => (TemporalGraph.volume G s (VoterModel.phiQ q g) : ℝ)
                  ≤ 14 * (m : ℝ) / (3 * (Oα.card : ℝ))) ∈ t)

/-! ### The metaphase index `R_α` -/

/-- `R_α`, the random metaphase index. `R_0 = 0`, and `R_{α+1}` is the first phase
`r` (capped at `r_max`) by which the number of opinions has dropped to
`⌈ρ^α κ⌉ ∨ 1` with shrink factor `ρ = 6/7`. The cap `r_max` keeps the defining set
nonempty, so the `sInf` is well defined. -/
def VoterModelAbstract.metaphase (vm : VoterModelAbstract G κ Ω) (B : ℝ) (m d_min : ℕ)
    (Δ : ℕ → ℕ) (φ : ℕ → ℝ) : ℕ → Ω → ℕ
  | 0, _ => 0
  | (α + 1), ω =>
    sInf (insert (TemporalGraph.rMax B m d_min)
      {r | (vm.opinionSet (TemporalGraph.phaseTime Δ φ r) ω).card
            ≤ max ⌈(6 / 7 : ℝ) ^ α * (κ : ℝ)⌉₊ 1})

/-- `R_α ≤ r_max` always (the cap is a member of the defining set). -/
theorem VoterModelAbstract.metaphase_le_rMax (vm : VoterModelAbstract G κ Ω) (B : ℝ) (m d_min : ℕ)
    (Δ : ℕ → ℕ) (φ : ℕ → ℝ) (α : ℕ) (ω : Ω) :
    vm.metaphase B m d_min Δ φ α ω ≤ TemporalGraph.rMax B m d_min := by
  cases α with
  | zero => exact Nat.zero_le _
  | succ k =>
    exact Nat.sInf_le (Set.mem_insert _ _)

/-- `R_α` is monotone in `α`. -/
theorem VoterModelAbstract.metaphase_mono (vm : VoterModelAbstract G κ Ω) (B : ℝ) (m d_min : ℕ)
    (Δ : ℕ → ℕ) (φ : ℕ → ℝ) (ω : Ω) :
    Monotone (fun α => vm.metaphase B m d_min Δ φ α ω) := by
  apply monotone_nat_of_le_succ
  intro α
  cases α with
  | zero => exact Nat.zero_le _
  | succ k =>
    -- thresholds: exponent `k` for `R_{k+1}`, exponent `k+1` for `R_{k+2}`.
    have hθ : max ⌈(6 / 7 : ℝ) ^ (k + 1) * (κ : ℝ)⌉₊ 1
        ≤ max ⌈(6 / 7 : ℝ) ^ k * (κ : ℝ)⌉₊ 1 := by
      refine max_le_max ?_ le_rfl
      apply Nat.ceil_mono
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ k)
    have hsub : insert (TemporalGraph.rMax B m d_min)
          {r | (vm.opinionSet (TemporalGraph.phaseTime Δ φ r) ω).card
                ≤ max ⌈(6 / 7 : ℝ) ^ (k + 1) * (κ : ℝ)⌉₊ 1}
        ⊆ insert (TemporalGraph.rMax B m d_min)
          {r | (vm.opinionSet (TemporalGraph.phaseTime Δ φ r) ω).card
                ≤ max ⌈(6 / 7 : ℝ) ^ k * (κ : ℝ)⌉₊ 1} := by
      intro r hr
      rcases Set.mem_insert_iff.mp hr with hr | hr
      · exact Set.mem_insert_iff.mpr (Or.inl hr)
      · exact Set.mem_insert_of_mem _ (le_trans hr hθ)
    have hne : (insert (TemporalGraph.rMax B m d_min)
        {r | (vm.opinionSet (TemporalGraph.phaseTime Δ φ r) ω).card
              ≤ max ⌈(6 / 7 : ℝ) ^ (k + 1) * (κ : ℝ)⌉₊ 1}).Nonempty :=
      ⟨_, Set.mem_insert _ _⟩
    exact Nat.sInf_le (hsub (Nat.sInf_mem hne))

/-- The event `{R_α ≤ r}` is measurable w.r.t. `ℱ_{t_r}`, given that `t = phaseTime`
is monotone (so that earlier-phase events lift to level `t_r`). -/
theorem VoterModelAbstract.metaphase_le_measurable (vm : VoterModelAbstract G κ Ω) (B : ℝ) (m d_min : ℕ)
    (Δ : ℕ → ℕ) (φ : ℕ → ℝ) (hmono : Monotone (TemporalGraph.phaseTime Δ φ)) (α r : ℕ) :
    @MeasurableSet Ω (vm.ℱ (TemporalGraph.phaseTime Δ φ r))
      {ω | vm.metaphase B m d_min Δ φ α ω ≤ r} := by
  cases α with
  | zero =>
    have h0 : {ω | vm.metaphase B m d_min Δ φ 0 ω ≤ r} = Set.univ := by
      ext ω; simp [VoterModelAbstract.metaphase]
    rw [h0]; exact MeasurableSet.univ
  | succ k =>
    set θ := max ⌈(6 / 7 : ℝ) ^ k * (κ : ℝ)⌉₊ 1 with hθdef
    have hset : {ω | vm.metaphase B m d_min Δ φ (k + 1) ω ≤ r}
        = ⋃ r' ∈ Finset.range (r + 1),
            ({ω | r' = TemporalGraph.rMax B m d_min} ∪
             {ω | (vm.opinionSet (TemporalGraph.phaseTime Δ φ r') ω).card ≤ θ}) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_range, Set.mem_union, exists_prop]
      constructor
      · intro hle
        have hne : (insert (TemporalGraph.rMax B m d_min)
            {r' | (vm.opinionSet (TemporalGraph.phaseTime Δ φ r') ω).card ≤ θ}).Nonempty :=
          ⟨_, Set.mem_insert _ _⟩
        have hmem := Nat.sInf_mem hne
        change sInf _ ≤ r at hle
        exact ⟨sInf _, Nat.lt_succ_of_le hle, Set.mem_insert_iff.mp hmem⟩
      · rintro ⟨r', hr', hor⟩
        change sInf _ ≤ r
        have hmem' : r' ∈ insert (TemporalGraph.rMax B m d_min)
            {r'' | (vm.opinionSet (TemporalGraph.phaseTime Δ φ r'') ω).card ≤ θ} := by
          rcases hor with h | h
          · exact Set.mem_insert_iff.mpr (Or.inl h)
          · exact Set.mem_insert_of_mem _ h
        exact le_trans (Nat.sInf_le hmem') (Nat.lt_succ_iff.mp hr')
    rw [hset]
    refine MeasurableSet.biUnion (Finset.range (r + 1)).countable_toSet (fun r' hr' => ?_)
    have hr'le : r' ≤ r := by
      have hr'mem : r' ∈ Finset.range (r + 1) := hr'
      exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hr'mem)
    refine MeasurableSet.union ?_ ?_
    · by_cases hc : r' = TemporalGraph.rMax B m d_min
      · have hu : {ω : Ω | r' = TemporalGraph.rMax B m d_min} = Set.univ := by
          ext ω; simp [hc]
        rw [hu]; exact @MeasurableSet.univ Ω (vm.ℱ (TemporalGraph.phaseTime Δ φ r))
      · have he : {ω : Ω | r' = TemporalGraph.rMax B m d_min} = (∅ : Set Ω) := by
          ext ω; simp [hc]
        rw [he]; exact @MeasurableSet.empty Ω (vm.ℱ (TemporalGraph.phaseTime Δ φ r))
    · exact (vm.ℱ.mono (hmono hr'le)) _
        (vm.opinionCard_le_event_filtration (TemporalGraph.phaseTime Δ φ r') θ)

/-! ### The coarse filtration `𝒢_r = ℱ_{t_r}` and the stopping time `R_α` -/

/-- `𝒢_r = ℱ_{t_r}`, the filtration along the phase times. Requires that the phase
time `t_r` is monotone in `r` (see `phaseTime_mono`). -/
def VoterModelAbstract.phaseFiltration (vm : VoterModelAbstract G κ Ω) (Δ : ℕ → ℕ) (φ : ℕ → ℝ)
    (hmono : Monotone (TemporalGraph.phaseTime Δ φ)) :
    MeasureTheory.Filtration ℕ mΩ where
  seq r := vm.ℱ (TemporalGraph.phaseTime Δ φ r)
  mono' _ _ h := vm.ℱ.mono (hmono h)
  le' r := vm.ℱ.le (TemporalGraph.phaseTime Δ φ r)

/-- `R_α` is a stopping time for the coarse filtration `𝒢_r = ℱ_{t_r}`. (In this
Mathlib, `IsStoppingTime` ranges over `WithTop ℕ`, so `R_α` is coerced.) -/
theorem VoterModelAbstract.metaphase_isStoppingTime (vm : VoterModelAbstract G κ Ω) (B : ℝ) (m d_min : ℕ)
    (Δ : ℕ → ℕ) (φ : ℕ → ℝ) (hmono : Monotone (TemporalGraph.phaseTime Δ φ)) (α : ℕ) :
    MeasureTheory.IsStoppingTime (vm.phaseFiltration Δ φ hmono)
      (fun ω => (vm.metaphase B m d_min Δ φ α ω : WithTop ℕ)) := by
  intro r
  have key := vm.metaphase_le_measurable B m d_min Δ φ hmono α r
  have hset : {ω | vm.metaphase B m d_min Δ φ α ω ≤ r}
      = {ω | (vm.metaphase B m d_min Δ φ α ω : WithTop ℕ) ≤ (r : WithTop ℕ)} := by
    ext ω; simp only [Set.mem_setOf_eq, Nat.cast_le]
  rw [hset] at key
  exact key

/-- The event `{R_α = r}` is measurable w.r.t. `ℱ_{t_r}`. -/
theorem VoterModelAbstract.metaphase_eq_measurable (vm : VoterModelAbstract G κ Ω) (B : ℝ) (m d_min : ℕ)
    (Δ : ℕ → ℕ) (φ : ℕ → ℝ) (hmono : Monotone (TemporalGraph.phaseTime Δ φ)) (α r : ℕ) :
    @MeasurableSet Ω (vm.ℱ (TemporalGraph.phaseTime Δ φ r))
      {ω | vm.metaphase B m d_min Δ φ α ω = r} := by
  have h := (vm.metaphase_isStoppingTime B m d_min Δ φ hmono α).measurableSet_eq r
  have hset : {ω | vm.metaphase B m d_min Δ φ α ω = r}
      = {ω | (vm.metaphase B m d_min Δ φ α ω : WithTop ℕ) = (r : WithTop ℕ)} := by
    ext ω; simp only [Set.mem_setOf_eq, Nat.cast_inj]
  rw [hset]
  exact h

end TemporalGraph
