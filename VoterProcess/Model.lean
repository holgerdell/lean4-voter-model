module

public import VoterProcess.Construction

/-!
# The standard voter model

The abstract voter model `TemporalGraph.VoterModelAbstract` is parameterized by an arbitrary
measurable sample space `Ω`. This file provides the concrete model
`TemporalGraph.VoterModel` whose sample space is **hard-wired** to the trajectory space
`ℕ → (V → Fin κ)`, with the opinion process being the coordinate projection `ω t`. This lets
headline theorems avoid carrying `{Ω} [MeasurableSpace Ω] [StandardBorelSpace Ω]` binders.

## Main results

- `MarkovModel` — a law `μ` on `ℕ → S` with the general, kernel-free `markovProperty`
  (memorylessness), stated purely with cylinder masses (no measurable-set hypotheses).
- `VoterModel.updateProb`, `VoterModel.transitionProb` — the per-vertex update probability and
  the one-step transition probability of the voter model (product of independent per-vertex
  updates).
- `TemporalGraph.VoterModel` — the standard voter model on `ℕ → (V → Fin κ)`:
  `extends MarkovModel (V → Fin κ)` and adds the voter `transition` law (`transitionProb`),
  opinion process `ω t`.
- `TemporalGraph.VoterModel.transition_prefix` — the full-prefix product recursion, derived from
  `markovProperty` + `transition`; the concrete drop-in for the old single-field Markov property.
- `TemporalGraph.VoterModel.ofPrefixRecursion` — build a model from any measure satisfying that
  recursion (splits it into `markovProperty` and `transition`).
- `TemporalGraph.VoterModel.toAbstract` — bridge to `VoterModelAbstract` on
  `ℕ → (V → Fin κ)`.
- `VoterModel.opinionZeroSet`, `VoterModel.consensusTime` — forwarding
  defs, definitionally equal to the abstract versions on `vm.toAbstract`.
- `TemporalGraph.VoterModel.ofDeterministic` — non-vacuity: the canonical deterministic-start
  model.
- `TemporalGraph.VoterModel.existsUnique_ofStart` — for every fixed-degree `G`
  and start state `ξ₀`
  there is exactly one voter model on `G` with `vm.μ {ω | ω 0 = ξ₀} = 1`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Classical ENNReal

noncomputable section

/-- Time-inhomogeneous Markov chains `(ξ_t : t ≥ 0)` over a set `S`. -/
structure MarkovModel (S : Type*) [MeasurableSpace S] where
  /-- The probability assigned to each possible outcome (x_t : t ≥ 0). -/
  μ : ProbabilityMeasure (ℕ → S)
  /-- The Markov property: `P(ξ_{t+1} = x' ∣ ξ_0, …, ξ_t) = P(ξ_{t+1} = x' ∣ ξ_t)`,
      cross-multiplied to avoid division. -/
  markovProperty (t : ℕ) (a : ℕ → S) (x' : S) :
      μ {ξ | (∀ j ≤ t, ξ j = a j) ∧ ξ (t + 1) = x'} * μ {ξ | ξ t = a t}
        = μ {ξ | ξ t = a t ∧ ξ (t + 1) = x'} * μ {ξ | ∀ j ≤ t, ξ j = a j}

/-- Splitting a length-`(t + 1)` prefix cylinder: pin the first `t` coordinates, then the last. -/
private theorem setOf_prefix_succ {Y : Type*} (t : ℕ) (a : ℕ → Y) :
    {ξ : ℕ → Y | ∀ j ≤ t + 1, ξ j = a j}
      = {ξ | (∀ j ≤ t, ξ j = a j) ∧ ξ (t + 1) = a (t + 1)} := by
  ext ξ
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hh
    exact ⟨fun j hj => hh j (by omega), hh (t + 1) le_rfl⟩
  · rintro ⟨h1, h2⟩ j hj
    rcases eq_or_lt_of_le hj with heq | hlt
    · rw [heq]; exact h2
    · exact h1 j (Nat.lt_succ_iff.mp hlt)

/-- Two prefix cylinders coincide when the pinned prefixes agree. -/
private theorem setOf_prefix_congr {Y : Type*} (t : ℕ) {a b : ℕ → Y}
    (h : ∀ j ≤ t, a j = b j) :
    {ξ : ℕ → Y | ∀ j ≤ t, ξ j = a j} = {ξ | ∀ j ≤ t, ξ j = b j} := by
  ext ξ
  exact forall_congr' fun j => imp_congr_right fun hj => by rw [h j hj]

/-- A coordinate-pinning cylinder `{ξ | ξ i = c}` on the trajectory space is measurable. -/
private theorem measurableSet_coord_eq {Y : Type*} [MeasurableSpace Y]
    [MeasurableSingletonClass Y] (i : ℕ) (c : Y) :
    MeasurableSet {ξ : ℕ → Y | ξ i = c} := by
  have : {ξ : ℕ → Y | ξ i = c} = (fun ξ => ξ i) ⁻¹' {c} := rfl
  rw [this]
  exact measurable_pi_apply i (MeasurableSet.singleton c)

/-- **Memorylessness + one-step transition ⟹ full-prefix recursion.** Given the cross-multiplied
memoryless identity `hMarkov` and the one-step transition law `hStep` (with kernel `w`), the
probability of a length-`(t+1)` prefix factors as `w · (probability of the length-`t` prefix)`. No
summation is needed in this direction; the current state is cancelled directly. -/
private theorem prefix_recursion_of_markov_step {Y : Type*} [MeasurableSpace Y]
    (μ : Measure (ℕ → Y)) [IsFiniteMeasure μ] (w : ℕ → Y → Y → ℝ≥0∞)
    (hMarkov : ∀ (t : ℕ) (a : ℕ → Y) (x' : Y),
      μ {ξ | (∀ j ≤ t, ξ j = a j) ∧ ξ (t + 1) = x'} * μ {ξ | ξ t = a t}
        = μ {ξ | ξ t = a t ∧ ξ (t + 1) = x'} * μ {ξ | ∀ j ≤ t, ξ j = a j})
    (hStep : ∀ (t : ℕ) (x x' : Y),
      μ {ξ | ξ t = x ∧ ξ (t + 1) = x'} = w t x x' * μ {ξ | ξ t = x})
    (t : ℕ) (a : ℕ → Y) :
    μ {ξ | ∀ j ≤ t + 1, ξ j = a j}
      = w t (a t) (a (t + 1)) * μ {ξ | ∀ j ≤ t, ξ j = a j} := by
  rw [setOf_prefix_succ]
  by_cases hzero : μ {ξ : ℕ → Y | ξ t = a t} = 0
  · have hpre_zero : μ {ξ : ℕ → Y | ∀ j ≤ t, ξ j = a j} = 0 :=
      measure_mono_null (fun ξ hξ => hξ t le_rfl) hzero
    rw [measure_mono_null (fun ξ hξ => hξ.1 t le_rfl) hzero, hpre_zero, mul_zero]
  · have hkey := hMarkov t a (a (t + 1))
    rw [hStep t (a t) (a (t + 1))] at hkey
    exact (ENNReal.mul_left_inj hzero (measure_ne_top μ _)).mp (by rw [hkey]; ring)

/-- Split form of the prefix recursion: pinning an arbitrary target `x'` at time `t + 1` onto a
prefix `a` factors through `w t (a t) x'`. Obtained from `hrec` by repinning the last coordinate. -/
private theorem split_of_prefix_recursion {Y : Type*} [MeasurableSpace Y]
    (μ : Measure (ℕ → Y)) (w : ℕ → Y → Y → ℝ≥0∞)
    (hrec : ∀ (t : ℕ) (a : ℕ → Y),
      μ {ξ | ∀ j ≤ t + 1, ξ j = a j}
        = w t (a t) (a (t + 1)) * μ {ξ | ∀ j ≤ t, ξ j = a j})
    (t : ℕ) (a : ℕ → Y) (x' : Y) :
    μ {ξ | (∀ j ≤ t, ξ j = a j) ∧ ξ (t + 1) = x'}
      = w t (a t) x' * μ {ξ | ∀ j ≤ t, ξ j = a j} := by
  set ã : ℕ → Y := fun j => if j = t + 1 then x' else a j with hã
  have hãle : ∀ j, j ≤ t → ã j = a j := fun j hj => by
    rw [hã]; simp only [if_neg (by omega : j ≠ t + 1)]
  have hãs : ã (t + 1) = x' := by rw [hã]; simp
  have h := hrec t ã
  rw [setOf_prefix_succ, hãs, hãle t le_rfl, Set.setOf_and, setOf_prefix_congr t hãle] at h
  rw [Set.setOf_and]
  exact h

/-- **Full-prefix recursion ⟹ one-step transition.** Summing the split form over the finite family
of length-`t` prefixes sharing current state `x` recovers the two-time-marginal transition law. -/
private theorem step_of_prefix_recursion {Y : Type*} [MeasurableSpace Y] [Fintype Y]
    [MeasurableSingletonClass Y]
    (μ : Measure (ℕ → Y)) (w : ℕ → Y → Y → ℝ≥0∞)
    (hrec : ∀ (t : ℕ) (a : ℕ → Y),
      μ {ξ | ∀ j ≤ t + 1, ξ j = a j}
        = w t (a t) (a (t + 1)) * μ {ξ | ∀ j ≤ t, ξ j = a j})
    (t : ℕ) (x x' : Y) :
    μ {ξ | ξ t = x ∧ ξ (t + 1) = x'} = w t x x' * μ {ξ | ξ t = x} := by
  have hsplit : ∀ (a : ℕ → Y), a t = x →
      μ {ξ | (∀ j ≤ t, ξ j = a j) ∧ ξ (t + 1) = x'}
        = w t x x' * μ {ξ | ∀ j ≤ t, ξ j = a j} := by
    intro a hat
    have h := split_of_prefix_recursion μ w hrec t a x'
    rwa [hat] at h
  set P : (ℕ → Y) → (↥(Finset.Iic t) → Y) := fun ξ j => ξ j.1 with hP
  set atom : (↥(Finset.Iic t) → Y) → Set (ℕ → Y) := fun ρ => P ⁻¹' {ρ} with hatom
  set hext : (↥(Finset.Iic t) → Y) → (ℕ → Y) :=
    fun ρ j => if hj : j ≤ t then ρ ⟨j, Finset.mem_Iic.mpr hj⟩ else x with hhext
  set TF : Finset (↥(Finset.Iic t) → Y) :=
    Finset.univ.filter (fun ρ => ρ ⟨t, by simp⟩ = x) with hTF
  have hext_t : ∀ ρ, hext ρ t = ρ ⟨t, by simp⟩ := fun ρ => by
    rw [hhext]; simp only [dif_pos le_rfl]
  have hatom_eq : ∀ ρ, atom ρ = {ξ : ℕ → Y | ∀ j ≤ t, ξ j = hext ρ j} := by
    intro ρ; ext ξ
    simp only [hatom, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq, hP]
    constructor
    · intro hξ j hj
      show ξ j = hext ρ j
      rw [hhext]; simp only [dif_pos hj]; rw [← hξ]
    · intro hξ
      funext j
      show ξ j.1 = ρ j
      have hj := Finset.mem_Iic.mp j.2
      have := hξ j.1 hj
      rw [hhext] at this; simp only [dif_pos hj] at this; rw [this]
  have hatom_meas : ∀ ρ, MeasurableSet (atom ρ) := by
    intro ρ
    have : atom ρ = ⋂ j : ↥(Finset.Iic t), {ξ : ℕ → Y | ξ j.1 = ρ j} := by
      ext ξ
      simp only [hatom, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter,
        Set.mem_setOf_eq, hP, funext_iff]
    rw [this]; exact MeasurableSet.iInter fun j => measurableSet_coord_eq j.1 (ρ j)
  have hdisj : (↑TF : Set (↥(Finset.Iic t) → Y)).PairwiseDisjoint atom := by
    intro a _ b _ hab
    simp only [Function.onFun]; rw [Set.disjoint_left]
    intro ξ ha hb
    simp only [hatom, Set.mem_preimage, Set.mem_singleton_iff] at ha hb
    exact hab (ha ▸ hb)
  have hcur_union : {ξ : ℕ → Y | ξ t = x} = ⋃ ρ ∈ TF, atom ρ := by
    ext ξ
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, hatom, Set.mem_preimage, Set.mem_singleton_iff,
      exists_prop, hTF, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hξ; exact ⟨P ξ, by show ξ t = x; exact hξ, rfl⟩
    · rintro ⟨ρ, hρ, rfl⟩; exact hρ
  have hEx'_meas : MeasurableSet {ξ : ℕ → Y | ξ (t + 1) = x'} :=
    measurableSet_coord_eq (t + 1) x'
  have hcur : μ {ξ : ℕ → Y | ξ t = x} = ∑ ρ ∈ TF, μ (atom ρ) := by
    rw [hcur_union, measure_biUnion_finset hdisj (fun ρ _ => hatom_meas ρ)]
  have hjoint : μ {ξ : ℕ → Y | ξ t = x ∧ ξ (t + 1) = x'}
      = ∑ ρ ∈ TF, w t x x' * μ (atom ρ) := by
    have hset : {ξ : ℕ → Y | ξ t = x ∧ ξ (t + 1) = x'}
        = ⋃ ρ ∈ TF, (atom ρ ∩ {ξ | ξ (t + 1) = x'}) := by
      rw [← Set.iUnion₂_inter,
        show (⋃ ρ ∈ TF, atom ρ) = {ξ : ℕ → Y | ξ t = x} from hcur_union.symm]
      ext ξ; simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    rw [hset,
      measure_biUnion_finset
        (fun a ha b hb hab => (hdisj ha hb hab).mono Set.inter_subset_left Set.inter_subset_left)
        (fun ρ _ => (hatom_meas ρ).inter hEx'_meas)]
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    have hρx : ρ ⟨t, by simp⟩ = x := by
      simpa only [hTF, Finset.mem_filter, Finset.mem_univ, true_and] using hρ
    have hstate : hext ρ t = x := by rw [hext_t]; exact hρx
    rw [hatom_eq ρ,
      show {ξ : ℕ → Y | ∀ j ≤ t, ξ j = hext ρ j} ∩ {ξ | ξ (t + 1) = x'}
          = {ξ | (∀ j ≤ t, ξ j = hext ρ j) ∧ ξ (t + 1) = x'} from by
        ext ξ; simp only [Set.mem_inter_iff, Set.mem_setOf_eq],
      hsplit (hext ρ) hstate]
  rw [hjoint, hcur, Finset.mul_sum]

/-- **Full-prefix recursion ⟹ memorylessness.** Pure algebra from the split form and the one-step
transition: both sides equal `w t (a t) x' · μ(prefix) · μ(current state)`. -/
private theorem markov_of_prefix_recursion {Y : Type*} [MeasurableSpace Y] [Fintype Y]
    [MeasurableSingletonClass Y]
    (μ : Measure (ℕ → Y)) (w : ℕ → Y → Y → ℝ≥0∞)
    (hrec : ∀ (t : ℕ) (a : ℕ → Y),
      μ {ξ | ∀ j ≤ t + 1, ξ j = a j}
        = w t (a t) (a (t + 1)) * μ {ξ | ∀ j ≤ t, ξ j = a j})
    (t : ℕ) (a : ℕ → Y) (x' : Y) :
    μ {ξ | (∀ j ≤ t, ξ j = a j) ∧ ξ (t + 1) = x'} * μ {ξ | ξ t = a t}
      = μ {ξ | ξ t = a t ∧ ξ (t + 1) = x'} * μ {ξ | ∀ j ≤ t, ξ j = a j} := by
  rw [split_of_prefix_recursion μ w hrec t a x', step_of_prefix_recursion μ w hrec t (a t) x']
  ring

/-- Probability that vertex `v`'s updated opinion is `o`: with probability `½` the vertex keeps
its opinion `ξ v`, with probability `½` it adopts the opinion of a uniformly random neighbour
(isolated vertices keep their opinion). -/
def VoterModel.updateProb {V : Type*} [Fintype V] {κ : ℕ} (G : SimpleGraph V)
    [DecidableRel G.Adj] (ξ : V → Fin κ) (v : V) (o : Fin κ) : ℝ≥0∞ :=
  let keep : ℝ≥0∞ := if o = ξ v then 1 else 0
  let adopt : ℝ≥0∞ := #{w ∈ G.neighborFinset v | ξ w = o} / (G.degree v : ℝ≥0∞)
  if G.degree v = 0 then keep else 2⁻¹ * keep + 2⁻¹ * adopt


/-- One-step transition probability of the voter model on `G`: every vertex updates
independently, so the probability of transitioning from `ξ` to `ξ'` is the product of the
per-vertex update probabilities. -/
def VoterModel.transitionProb {V : Type*} [Fintype V] {κ : ℕ} (G : SimpleGraph V)
    [DecidableRel G.Adj] (ξ ξ' : V → Fin κ) : ℝ≥0∞ :=
  ∏ v, VoterModel.updateProb G ξ v (ξ' v)

/-- On a snapshot of a temporal graph, the per-vertex update probability agrees with the
per-vertex distribution `TemporalGraph.VoterModel.nextOpinionDist`. -/
theorem VoterModel.updateProb_eq_nextOpinionDist {V : Type*} [Fintype V] [Nonempty V]
    [DecidableEq V] {κ : ℕ} (G : TemporalGraph V) (t : ℕ)
    (ξ : V → Fin κ) (v : V) (o : Fin κ) :
    VoterModel.updateProb (G.snapshot t) ξ v o
      = TemporalGraph.VoterModel.nextOpinionDist G t ξ v o := by
  show VoterModel.updateProb (G.snapshot t) ξ v o
    = TemporalGraph.VoterModel.nextOpinionMass G t ξ v o
  simp only [VoterModel.updateProb, TemporalGraph.VoterModel.nextOpinionMass]
  by_cases hN : ((G.snapshot t).neighborFinset v).Nonempty
  · have hdeg : (G.snapshot t).degree v ≠ 0 := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      exact (Finset.card_pos.mpr hN).ne'
    simp only [if_neg hdeg, if_pos hN, SimpleGraph.card_neighborFinset_eq_degree]
  · have hdeg : (G.snapshot t).degree v = 0 := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_eq_zero,
        Finset.not_nonempty_iff_eq_empty.mp hN]
    simp only [if_pos hdeg, if_neg hN]

/-- On a snapshot of a temporal graph, the transition probability is the product of the
per-vertex distributions `nextOpinionDist`. -/
theorem VoterModel.transitionProb_eq_prod_nextOpinionDist {V : Type*} [Fintype V] [Nonempty V]
    [DecidableEq V] {κ : ℕ} (G : TemporalGraph V) (t : ℕ) (x x' : V → Fin κ) :
    VoterModel.transitionProb (G.snapshot t) x x'
      = ∏ v, TemporalGraph.VoterModel.nextOpinionDist G t x v (x' v) :=
  Finset.prod_congr rfl fun v _ => VoterModel.updateProb_eq_nextOpinionDist G t x v (x' v)

namespace TemporalGraph

/-- \label{def:voter-model}

The standard voter model with `κ` opinions on a temporal graph `G`. -/
structure VoterModel {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraph V) (κ : ℕ) [NeZero κ]
    extends MarkovModel (V → Fin κ) where
  /-- Under the law `μ`, one synchronous step transitions from `x` to `x'` with probability
  `transitionProb`: `P(ξ_{t+1} = x' ∣ ξ_t = x) = transitionProb`, cross-multiplied to avoid
  division. -/
  transition (t x x') :
      μ {ξ | ξ (t + 1) = x' ∧ ξ t = x}
        = (VoterModel.transitionProb (G.snapshot t) x x') * μ {ξ | ξ t = x}

/-- The full-prefix product recursion, recovered from the general `markovProperty` together with
the voter `transition` kernel. Concrete drop-in for the old single-field Markov property. -/
theorem VoterModel.transition_prefix {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    {κ : ℕ} [NeZero κ] {G : TemporalGraph V}
    (vm : VoterModel G κ) (t : ℕ) (a : ℕ → (V → Fin κ)) :
    (vm.μ : Measure (ℕ → (V → Fin κ))) {ξ | ∀ j ≤ t + 1, ξ j = a j}
      = VoterModel.transitionProb (G.snapshot t) (a t) (a (t + 1))
        * (vm.μ : Measure (ℕ → (V → Fin κ))) {ξ | ∀ j ≤ t, ξ j = a j} := by
  have hMarkov : ∀ (s : ℕ) (b : ℕ → (V → Fin κ)) (x' : V → Fin κ),
      (vm.μ : Measure (ℕ → (V → Fin κ)))
          {ξ | (∀ j ≤ s, ξ j = b j) ∧ ξ (s + 1) = x'}
          * (vm.μ : Measure (ℕ → (V → Fin κ))) {ξ | ξ s = b s}
        = (vm.μ : Measure (ℕ → (V → Fin κ))) {ξ | ξ s = b s ∧ ξ (s + 1) = x'}
          * (vm.μ : Measure (ℕ → (V → Fin κ))) {ξ | ∀ j ≤ s, ξ j = b j} := by
    intro s b x'
    simp only [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, ← ENNReal.coe_mul]
    exact_mod_cast vm.markovProperty s b x'
  have hStep : ∀ (s : ℕ) (x x' : V → Fin κ),
      (vm.μ : Measure (ℕ → (V → Fin κ))) {ξ | ξ s = x ∧ ξ (s + 1) = x'}
        = VoterModel.transitionProb (G.snapshot s) x x'
          * (vm.μ : Measure (ℕ → (V → Fin κ))) {ξ | ξ s = x} := by
    intro s x x'
    rw [show {ξ : ℕ → V → Fin κ | ξ s = x ∧ ξ (s + 1) = x'}
          = {ξ | ξ (s + 1) = x' ∧ ξ s = x} from by ext ξ; exact and_comm,
        ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
        ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    exact vm.transition s x x'
  exact prefix_recursion_of_markov_step (vm.μ : Measure (ℕ → (V → Fin κ)))
    (fun s x x' => VoterModel.transitionProb (G.snapshot s) x x') hMarkov hStep t a

/-- Build a voter model from any probability measure on the trajectory space satisfying the
full-prefix
product recursion; the memoryless `markovProperty` and the `transition` kernel are then derived. -/
def VoterModel.ofPrefixRecursion {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    {κ : ℕ} [NeZero κ] {G : TemporalGraph V}
    (μP : Measure (ℕ → (V → Fin κ))) [IsProbabilityMeasure μP]
    (hrec : ∀ (t : ℕ) (a : ℕ → (V → Fin κ)),
      μP {ξ | ∀ j ≤ t + 1, ξ j = a j}
        = VoterModel.transitionProb (G.snapshot t) (a t) (a (t + 1))
          * μP {ξ | ∀ j ≤ t, ξ j = a j}) : VoterModel G κ where
  μ := ⟨μP, inferInstance⟩
  markovProperty t a x' := by
    rw [← ENNReal.coe_inj, ENNReal.coe_mul, ENNReal.coe_mul,
        ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
        ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
        ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
        ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    exact markov_of_prefix_recursion μP
      (fun t x x' => VoterModel.transitionProb (G.snapshot t) x x') hrec t a x'
  transition t x x' := by
    rw [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
        ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
        show {ξ : ℕ → V → Fin κ | ξ (t + 1) = x' ∧ ξ t = x}
          = {ξ | ξ t = x ∧ ξ (t + 1) = x'} from by ext ξ; exact and_comm]
    exact step_of_prefix_recursion μP
      (fun t x x' => VoterModel.transitionProb (G.snapshot t) x x') hrec t x x'

/-- Atomic ⇒ integral: recover the integral form of the conditional Markov property over an
arbitrary `ℱ_t`-measurable `B` from the atomic identity, decomposing `B` into its finite disjoint
prefix-cylinder atoms. -/
private theorem markovProperty_integral_of_atomic
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V] {κ : ℕ} [NeZero κ]
    {G : TemporalGraph V}
    (μ : Measure (ℕ → (V → Fin κ)))
    (hAtom : ∀ (t : ℕ) (ξ : ℕ → (V → Fin κ)),
      μ {ω | ∀ j ≤ t + 1, ω j = ξ j}
        = VoterModel.transitionProb (G.snapshot t) (ξ t) (ξ (t + 1))
          * μ {ω | ∀ j ≤ t, ω j = ξ j})
    (t : ℕ) (g : V → Fin κ) (B : Set (ℕ → (V → Fin κ)))
    (hB : MeasurableSet[⨆ j ∈ Finset.Iic t,
      MeasurableSpace.comap (fun ω : ℕ → (V → Fin κ) => ω j) ⊤] B) :
    μ (B ∩ {ω | ω (t + 1) = g})
      = ∫⁻ ω in B, VoterModel.transitionProb (G.snapshot t) (ω t) g ∂μ := by
  -- Split form (target `g` separate from the prefix `h`) of the merged hypothesis.
  have hAtom' : ∀ (g : V → Fin κ) (h : ℕ → (V → Fin κ)),
      μ {ω | (∀ j ≤ t, ω j = h j) ∧ ω (t + 1) = g}
        = VoterModel.transitionProb (G.snapshot t) (h t) g
          * μ {ω | ∀ j ≤ t, ω j = h j} := fun g h =>
    split_of_prefix_recursion μ
      (fun s x x' => VoterModel.transitionProb (G.snapshot s) x x') hAtom t h g
  -- Project a path onto its length-`(t+1)` prefix, valued in the finite type of prefixes.
  set P : (ℕ → (V → Fin κ)) → (↥(Finset.Iic t) → (V → Fin κ)) :=
    fun ω j => ω j.1 with hP
  -- `ℱ_t ≤ comap P ⊤`: each coordinate `j ≤ t` factors through `P`.
  have hle : (⨆ j ∈ Finset.Iic t,
      MeasurableSpace.comap (fun ω : ℕ → (V → Fin κ) => ω j) ⊤)
        ≤ MeasurableSpace.comap P ⊤ := by
    refine iSup₂_le fun j hj => ?_
    have hfac : (fun ω : ℕ → (V → Fin κ) => ω j)
        = (fun ρ : ↥(Finset.Iic t) → (V → Fin κ) => ρ ⟨j, hj⟩) ∘ P := rfl
    rw [hfac, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono le_top
  -- Hence `B = P ⁻¹' T` for a set `T` of prefixes; `T` is finite.
  obtain ⟨T, -, hTB⟩ := MeasurableSpace.measurableSet_comap.mp (hle _ hB)
  set TF : Finset (↥(Finset.Iic t) → (V → Fin κ)) := (Set.toFinite T).toFinset with hTF
  set atom : (↥(Finset.Iic t) → (V → Fin κ)) → Set (ℕ → (V → Fin κ)) :=
    fun ρ => P ⁻¹' {ρ} with hatom
  -- Any extension of a prefix `ρ` to a full path (values past `t` are irrelevant).
  set hext : (↥(Finset.Iic t) → (V → Fin κ)) → (ℕ → (V → Fin κ)) :=
    fun ρ j => if hj : j ≤ t then ρ ⟨j, Finset.mem_Iic.mpr hj⟩ else fun _ => 0 with hhext
  have hBunion : B = ⋃ ρ ∈ TF, atom ρ := by
    rw [← hTB]
    ext ω
    simp only [hatom, Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff,
      exists_prop, hTF, Set.Finite.mem_toFinset]
    constructor
    · intro hω; exact ⟨P ω, hω, rfl⟩
    · rintro ⟨ρ, hρ, rfl⟩; exact hρ
  have hdisj : (↑TF : Set (↥(Finset.Iic t) → (V → Fin κ))).PairwiseDisjoint atom := by
    intro a _ b _ hab
    simp only [Function.onFun]
    rw [Set.disjoint_left]
    intro ω ha hb
    simp only [hatom, Set.mem_preimage, Set.mem_singleton_iff] at ha hb
    exact hab (ha ▸ hb)
  have hatom_meas : ∀ ρ, MeasurableSet (atom ρ) := by
    intro ρ
    have hset : atom ρ = ⋂ j : ↥(Finset.Iic t),
        {ω : ℕ → (V → Fin κ) | ω j.1 = ρ j} := by
      ext ω
      simp only [hatom, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter,
        Set.mem_setOf_eq, hP, funext_iff]
    rw [hset]
    exact MeasurableSet.iInter fun j => measurableSet_coord_eq j.1 (ρ j)
  have hEg_meas : MeasurableSet {ω : ℕ → (V → Fin κ) | ω (t + 1) = g} :=
    measurableSet_coord_eq (t + 1) g
  -- Each atom is the prefix cylinder pinned to any extension `hext ρ` of `ρ`.
  have hatom_eq : ∀ ρ, atom ρ =
      {ω : ℕ → (V → Fin κ) | ∀ j ≤ t, ω j = hext ρ j} := by
    intro ρ
    ext ω
    simp only [hatom, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq, hP]
    constructor
    · intro hω j hj
      show ω j = hext ρ j
      rw [hhext]
      simp only [dif_pos hj]
      rw [← hω]
    · intro hω
      funext j
      show ω j.1 = ρ j
      have hj := Finset.mem_Iic.mp j.2
      have hthis := hω j.1 hj
      rw [hhext] at hthis; simp only [dif_pos hj] at hthis
      rw [hthis]
  -- LHS decomposes over the finite disjoint union.
  have hLHS : μ (B ∩ {ω | ω (t + 1) = g})
      = ∑ ρ ∈ TF, VoterModel.transitionProb (G.snapshot t) (hext ρ t) g * μ (atom ρ) := by
    rw [hBunion, Set.iUnion₂_inter,
      measure_biUnion_finset
        (fun a ha b hb hab => (hdisj ha hb hab).mono Set.inter_subset_left Set.inter_subset_left)
        (fun ρ _ => (hatom_meas ρ).inter hEg_meas)]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [hatom_eq ρ, show {ω : ℕ → (V → Fin κ) | ∀ j ≤ t, ω j = hext ρ j}
          ∩ {ω | ω (t + 1) = g}
          = {ω | (∀ j ≤ t, ω j = hext ρ j) ∧ ω (t + 1) = g} from by
        ext ω; simp only [Set.mem_inter_iff, Set.mem_setOf_eq],
      hAtom' g (hext ρ)]
  -- RHS decomposes identically: the integrand is constant on each atom.
  have hRHS : ∫⁻ ω in B, VoterModel.transitionProb (G.snapshot t) (ω t) g ∂μ
      = ∑ ρ ∈ TF, VoterModel.transitionProb (G.snapshot t) (hext ρ t) g * μ (atom ρ) := by
    rw [hBunion, lintegral_biUnion_finset hdisj (fun ρ _ => hatom_meas ρ)]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [setLIntegral_congr_fun (hatom_meas ρ)
      (g := fun _ => VoterModel.transitionProb (G.snapshot t) (hext ρ t) g)
      (fun ω hω => by
        have hωt : ω t = hext ρ t := by rw [hatom_eq ρ] at hω; exact hω t le_rfl
        simp only [hωt]),
      setLIntegral_const]
  rw [hLHS, ← hRHS]

/-- Integral ⇒ atomic: recover the atomic conditional Markov identity from the integral form by
specializing `B` to a prefix cylinder, on which the per-vertex integrand is constant. -/
private theorem atomic_of_integral
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V] {κ : ℕ} {G : TemporalGraph V}
    (μ : Measure (ℕ → (V → Fin κ)))
    (hInt : ∀ (t : ℕ) (g : V → Fin κ) (B : Set (ℕ → (V → Fin κ)))
      (_ : MeasurableSet[⨆ j ∈ Finset.Iic t,
        MeasurableSpace.comap (fun ω : ℕ → (V → Fin κ) => ω j) ⊤] B),
      μ (B ∩ {ω | ω (t + 1) = g})
        = ∫⁻ ω in B, VoterModel.transitionProb (G.snapshot t) (ω t) g ∂μ)
    (t : ℕ) (ξ : ℕ → (V → Fin κ)) :
    μ {ω | ∀ j ≤ t + 1, ω j = ξ j}
      = VoterModel.transitionProb (G.snapshot t) (ξ t) (ξ (t + 1))
        * μ {ω | ∀ j ≤ t, ω j = ξ j} := by
  set B : Set (ℕ → (V → Fin κ)) := {ω | ∀ j ≤ t, ω j = ξ j} with hB_def
  have hBeq : B = ⋂ j : ↥(Finset.Iic t), {ω : ℕ → (V → Fin κ) | ω j.1 = ξ j.1} := by
    ext ω
    simp only [hB_def, Set.mem_setOf_eq, Set.mem_iInter, Subtype.forall, Finset.mem_Iic]
  have hBfilt : MeasurableSet[⨆ j ∈ Finset.Iic t,
      MeasurableSpace.comap (fun ω : ℕ → (V → Fin κ) => ω j) ⊤] B := by
    rw [hBeq]
    refine MeasurableSet.iInter fun j => ?_
    have hcomap : MeasurableSet[MeasurableSpace.comap
        (fun ω : ℕ → (V → Fin κ) => ω j.1) ⊤]
        {ω : ℕ → (V → Fin κ) | ω j.1 = ξ j.1} :=
      ⟨{ξ j.1}, trivial, rfl⟩
    exact (le_iSup₂ (f := fun j (_ : j ∈ Finset.Iic t) =>
      MeasurableSpace.comap (fun ω : ℕ → (V → Fin κ) => ω j) ⊤) j.1 j.2) _ hcomap
  have hmeasB : MeasurableSet B := by
    rw [hBeq]
    exact MeasurableSet.iInter fun j => measurableSet_coord_eq j.1 (ξ j.1)
  have hBg := hInt t (ξ (t + 1)) B hBfilt
  have hset : B ∩ {ω : ℕ → (V → Fin κ) | ω (t + 1) = ξ (t + 1)}
      = {ω | ∀ j ≤ t + 1, ω j = ξ j} := by
    rw [setOf_prefix_succ, Set.setOf_and, hB_def]
  rw [hset] at hBg
  rw [hBg, setLIntegral_congr_fun hmeasB
    (g := fun _ => VoterModel.transitionProb (G.snapshot t) (ξ t) (ξ (t + 1)))
    (fun ω hω => by
      have hωt : ω t = ξ t := by rw [hB_def] at hω; exact hω t le_rfl
      simp only [hωt]),
    setLIntegral_const]

/-- The ambient product σ-algebra on the finite discrete space `V → Fin κ` is `⊤`. -/
private theorem measurableSpace_pi_top {V : Type*} [Fintype V] {κ : ℕ} :
    (inferInstance : MeasurableSpace (V → Fin κ)) = ⊤ :=
  le_antisymm le_top fun _ _ => MeasurableSet.of_discrete

/-- Bridge from the concrete model to `VoterModelAbstract` on
`ℕ → (V → Fin κ)`, opinion process
`ξ t ω = ω t`. The abstract integral-form Markov property is derived from the atomic field via
`markovProperty_integral_of_atomic`. -/
def VoterModel.toAbstract {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    {κ : ℕ} [NeZero κ] {G : TemporalGraph V}
    (vm : VoterModel G κ) : VoterModelAbstract G κ (ℕ → (V → Fin κ)) where
  μ := vm.μ
  ξ := fun t ω => ω t
  hξ_meas := fun t => by
    -- The structure hardcodes the codomain σ-algebra as `⊤`; bridge to the global
    -- `MeasurableSpace (V → Fin κ)` via `inferInstance = ⊤` (finite/discrete space).
    rw [← measurableSpace_pi_top]
    exact (measurable_pi_apply (δ := ℕ) (X := fun _ => V → Fin κ) t).comap_le
  markovProperty := by
    -- The atomic recursion needed by the bridge lemma is the derived `transition_prefix`.
    intro t g B hB
    rw [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    simpa only [VoterModel.transitionProb_eq_prod_nextOpinionDist] using
      markovProperty_integral_of_atomic (vm.μ : Measure _)
        vm.transition_prefix t g B hB

end TemporalGraph

/-- The opinion-0 vertex set `{v | ξ t v = 0}`. -/
def VoterModel.opinionZeroSet {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    {κ : ℕ} [NeZero κ] (t : ℕ) (ξ : ℕ → (V → Fin κ)) : Finset V :=
  {v | ξ t v = 0}

/-- First time all vertices agree, else ∞. -/
def VoterModel.consensusTime {V : Type*} {κ : ℕ} (ξ : ℕ → (V → Fin κ)) : ℕ∞ :=
  if h : ∃ t, ∀ u w, ξ t u = ξ t w then Nat.find h else ⊤

namespace TemporalGraph

/-- Non-vacuity: the canonical voter model with deterministic initial state `ξ₀`,
carrying the Ionescu–Tulcea trajectory measure. -/
def VoterModel.ofDeterministic {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    {κ : ℕ} [NeZero κ] (G : TemporalGraph V) (ξ₀ : V → Fin κ) : VoterModel G κ :=
  haveI : IsProbabilityMeasure (Measure.dirac ξ₀ : Measure (V → Fin κ)) :=
    Measure.dirac.isProbabilityMeasure
  haveI : IsProbabilityMeasure
      (_root_.VoterModel.voterTrajectoryMeasureFrom G (Measure.dirac ξ₀)) := inferInstance
  VoterModel.ofPrefixRecursion
      (_root_.VoterModel.voterTrajectoryMeasureFrom G (Measure.dirac ξ₀)) <| by
    -- The integral form of the conditional Markov property for the trajectory measure.
    have hInt : ∀ (t : ℕ) (g : V → Fin κ) (B : Set (ℕ → (V → Fin κ)))
        (_ : MeasurableSet[⨆ j ∈ Finset.Iic t,
          MeasurableSpace.comap (fun ω : ℕ → (V → Fin κ) => ω j) ⊤] B),
        (_root_.VoterModel.voterTrajectoryMeasureFrom G (Measure.dirac ξ₀))
            (B ∩ {ω | ω (t + 1) = g})
          = ∫⁻ ω in B, VoterModel.transitionProb (G.snapshot t) (ω t) g
            ∂_root_.VoterModel.voterTrajectoryMeasureFrom G (Measure.dirac ξ₀) := by
      intro t g B hB
      have htop := measurableSpace_pi_top (V := V) (κ := κ)
      -- Bridge the `⊤`-filtration hypothesis to the global-instance one.
      have hB' : @MeasurableSet (_root_.VoterModel.OpinionTrajectorySpace V κ)
          (⨆ i ∈ Finset.Iic t,
          MeasurableSpace.comap (fun ω : ℕ → (V → Fin κ) => ω i)
            (inferInstance : MeasurableSpace (V → Fin κ))) B := by
        have hfeq : (⨆ i ∈ Finset.Iic t,
            MeasurableSpace.comap (fun ω : ℕ → (V → Fin κ) => ω i)
              (inferInstance : MeasurableSpace (V → Fin κ))) =
            (⨆ i ∈ Finset.Iic t,
              MeasurableSpace.comap (fun ω : ℕ → (V → Fin κ) => ω i)
                (⊤ : MeasurableSpace (V → Fin κ))) := by
          simp only [htop]
        rw [hfeq]; exact hB
      simp_rw [VoterModel.transitionProb_eq_prod_nextOpinionDist,
        ← _root_.VoterModel.stepDist_apply]
      rw [_root_.VoterModel.voterTrajectoryMeasureFrom_markovProperty G (Measure.dirac ξ₀)
        t g B hB']
      refine setLIntegral_congr_fun ?_ (fun ω _ => ?_)
      · have hle : (⨆ i ∈ Finset.Iic t,
            MeasurableSpace.comap (fun ω : ℕ → (V → Fin κ) => ω i)
              (inferInstance : MeasurableSpace (V → Fin κ))) ≤
          (inferInstance : MeasurableSpace (ℕ → (V → Fin κ))) := by
          apply iSup₂_le
          intro i _
          exact (measurable_pi_apply i).comap_le
        exact hle _ hB'
      · exact PMF.toMeasure_apply_singleton (_root_.VoterModel.stepDist G t (ω t)) g
          (MeasurableSet.singleton g)
    -- Derive the atomic recursion by specializing `B` to a prefix cylinder.
    intro t ξ
    exact atomic_of_integral
      (_root_.VoterModel.voterTrajectoryMeasureFrom G (Measure.dirac ξ₀)) hInt t ξ

/-! ### Existence and uniqueness of the model with a given deterministic start state

The prefix cylinders `{ω | ∀ j ≤ t, ω j = ξ j}` form a π-system generating the product
σ-algebra on the trajectory space. The `markovProperty` field, together with the deterministic
start `μ {ω | ω 0 = ξ₀} = 1`, determines the measure of every prefix cylinder by induction on
`t`, so any two voter models on `G` with the same start have equal law, hence are equal. -/

/-- Prefix cylinders `{ω | ∀ j ≤ t, ω j = ξ j}` on the trajectory space `ℕ → Y`. -/
private def prefixCyls (Y : Type*) : Set (Set (ℕ → Y)) :=
  {s | ∃ (t : ℕ) (ξ : ℕ → Y), s = {ω | ∀ j ≤ t, ω j = ξ j}}

/-- Prefix cylinders form a π-system: a nonempty intersection of two prefix cylinders is the
prefix cylinder of the longer length pinned to the merged prefix. -/
private theorem isPiSystem_prefixCyls (Y : Type*) : IsPiSystem (prefixCyls Y) := by
  rintro _ ⟨ts, ξs, rfl⟩ _ ⟨tt, ξt, rfl⟩ hne
  obtain ⟨w, hws, hwt⟩ := hne
  simp only [Set.mem_setOf_eq] at hws hwt
  refine ⟨max ts tt, fun j => if j ≤ ts then ξs j else ξt j, ?_⟩
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩ j hj
    by_cases hjs : j ≤ ts
    · simp only [if_pos hjs]; exact h1 j hjs
    · simp only [if_neg hjs]
      have hjt : j ≤ tt := by
        rcases le_max_iff.mp hj with h | h
        · omega
        · exact h
      exact h2 j hjt
  · intro hh
    refine ⟨fun j hjs => ?_, fun j hjt => ?_⟩
    · have := hh j (le_max_of_le_left hjs)
      simp only [if_pos hjs] at this; exact this
    · have := hh j (le_max_of_le_right hjt)
      by_cases hjs : j ≤ ts
      · simp only [if_pos hjs] at this
        rw [this, ← hws j hjs, hwt j hjt]
      · simp only [if_neg hjs] at this; exact this

open MeasurableSpace in
/-- Prefix cylinders generate the product σ-algebra on `ℕ → Y` for a finite `Y`. -/
private theorem generateFrom_prefixCyls (Y : Type*) [MeasurableSpace Y] [Fintype Y]
    [MeasurableSingletonClass Y] :
    generateFrom (prefixCyls Y) = (inferInstance : MeasurableSpace (ℕ → Y)) := by
  apply le_antisymm
  · apply generateFrom_le
    rintro _ ⟨t, ξ, rfl⟩
    have hrw : {ω : ℕ → Y | ∀ j ≤ t, ω j = ξ j}
        = ⋂ j, ⋂ (_ : j ≤ t), (fun ω : ℕ → Y => ω j) ⁻¹' {ξ j} := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
    rw [hrw]
    refine MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => ?_
    exact measurable_pi_apply j (MeasurableSet.singleton (ξ j))
  · show (MeasurableSpace.pi : MeasurableSpace (ℕ → Y)) ≤ _
    refine iSup_le fun i => ?_
    refine measurable_iff_comap_le.mp
      (@measurable_to_countable' Y (ℕ → Y) _ _ (generateFrom (prefixCyls Y))
        (fun ω => ω i) ?_)
    intro c
    have hset : (fun ω : ℕ → Y => ω i) ⁻¹' {c}
        = ⋃ (ρ : {x // x ∈ Finset.Iic i} → Y) (_ : ρ ⟨i, by simp⟩ = c),
            {ω : ℕ → Y | ∀ j ≤ i,
              ω j =
                (fun j => if hj : j ≤ i then ρ ⟨j, Finset.mem_Iic.mpr hj⟩ else c) j} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_setOf_eq]
      constructor
      · intro hω
        refine ⟨fun j => ω j.1, hω, fun j hj => ?_⟩
        simp only [dif_pos hj]
      · rintro ⟨ρ, hρc, hρ⟩
        have := hρ i le_rfl
        simp only [dif_pos (le_refl i)] at this
        rw [this, hρc]
    rw [hset]
    refine MeasurableSet.iUnion fun ρ => MeasurableSet.iUnion fun _ => ?_
    exact measurableSet_generateFrom ⟨i, _, rfl⟩

/-- For two probability measures on the trajectory space with the same deterministic start
`κ {ω | ω 0 = ξ₀} = 1`, the measures of `{ω | ω 0 = c}` agree (both `1` if `c = ξ₀`,
else `0`). -/
private theorem coord0_eq {Y : Type*} [MeasurableSpace Y] [MeasurableSingletonClass Y] (ξ₀ : Y)
    (μ ν : Measure (ℕ → Y)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ0 : μ {ω | ω 0 = ξ₀} = 1) (hν0 : ν {ω | ω 0 = ξ₀} = 1) (c : Y) :
    μ {ω : ℕ → Y | ω 0 = c} = ν {ω : ℕ → Y | ω 0 = c} := by
  by_cases hc : c = ξ₀
  · rw [hc, hμ0, hν0]
  · have hcoord : MeasurableSet {ω : ℕ → Y | ω 0 = ξ₀} := by
      have hpre : {ω : ℕ → Y | ω 0 = ξ₀} =
          (fun ω : ℕ → Y => ω 0) ⁻¹' {ξ₀} := rfl
      rw [hpre]; exact measurable_pi_apply 0 (MeasurableSet.singleton ξ₀)
    have hnull : ∀ (κ : Measure (ℕ → Y)) [IsProbabilityMeasure κ],
        κ {ω : ℕ → Y | ω 0 = ξ₀} = 1 → κ {ω : ℕ → Y | ω 0 = c} = 0 := by
      intro κ _ h0
      refine measure_mono_null (t := {ω : ℕ → Y | ω 0 = ξ₀}ᶜ) (fun ω hω => ?_) ?_
      · simp only [Set.mem_setOf_eq] at hω
        simp only [Set.mem_compl_iff, Set.mem_setOf_eq]; rw [hω]; exact hc
      · rw [measure_compl hcoord (measure_ne_top _ _), measure_univ, h0, tsub_self]
    rw [hnull μ hμ0, hnull ν hν0]

/-- Two probability measures on the trajectory space satisfying the same one-step recursion (with
common
coefficient `w`) and the same deterministic start agree on every prefix cylinder, by induction on
the cylinder length. -/
private theorem cyl_eq {Y : Type*} [MeasurableSpace Y] [MeasurableSingletonClass Y] (ξ₀ : Y)
    (w : ℕ → Y → Y → ℝ≥0∞) (μ ν : Measure (ℕ → Y))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ0 : μ {ω | ω 0 = ξ₀} = 1) (hν0 : ν {ω | ω 0 = ξ₀} = 1)
    (hμm : ∀ (t : ℕ) (ξ : ℕ → Y), μ {ω | ∀ j ≤ t + 1, ω j = ξ j}
      = w t (ξ t) (ξ (t + 1)) * μ {ω | ∀ j ≤ t, ω j = ξ j})
    (hνm : ∀ (t : ℕ) (ξ : ℕ → Y), ν {ω | ∀ j ≤ t + 1, ω j = ξ j}
      = w t (ξ t) (ξ (t + 1)) * ν {ω | ∀ j ≤ t, ω j = ξ j}) :
    ∀ (t : ℕ) (ξ : ℕ → Y),
      μ {ω | ∀ j ≤ t, ω j = ξ j} = ν {ω | ∀ j ≤ t, ω j = ξ j} := by
  intro t
  induction t with
  | zero =>
    intro ξ
    have hset : {ω : ℕ → Y | ∀ j ≤ 0, ω j = ξ j} = {ω : ℕ → Y | ω 0 = ξ 0} := by
      ext ω; simp only [Nat.le_zero, Set.mem_setOf_eq]
      exact ⟨fun h => h 0 rfl, fun h j hj => hj ▸ h⟩
    rw [hset]; exact coord0_eq ξ₀ μ ν hμ0 hν0 (ξ 0)
  | succ n ih => intro ξ; rw [hμm n ξ, hνm n ξ, ih ξ]

/-- Existence and uniqueness of the standard voter model with a given deterministic start state:
for every fixed-degree temporal graph `G` and every initial opinion configuration `ξ₀`, there is
exactly one voter model `vm` on `G` whose initial state is deterministically `ξ₀`, i.e. with
`vm.μ {ω | ω 0 = ξ₀} = 1`. Existence is the canonical Ionescu–Tulcea model
`ofDeterministic`; uniqueness holds because the `markovProperty` recursion together with the
start condition pins the
measure of every prefix cylinder, and prefix cylinders determine the law. -/
theorem VoterModel.existsUnique_ofStart {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    {κ : ℕ} [NeZero κ] (G : TemporalGraphFixedDegree V) (ξ₀ : V → Fin κ) :
    ∃! vm : VoterModel (G : TemporalGraph V) κ,
      (vm.μ : Measure (ℕ → (V → Fin κ))) {ω | ω 0 = ξ₀} = 1 := by
  -- The canonical model `ofDeterministic` has the deterministic start.
  have hstart : ((VoterModel.ofDeterministic (G : TemporalGraph V) ξ₀).μ
      : Measure (ℕ → (V → Fin κ))) {ω | ω 0 = ξ₀} = 1 := by
    haveI : IsProbabilityMeasure (Measure.dirac ξ₀ : Measure (V → Fin κ)) :=
      Measure.dirac.isProbabilityMeasure
    show (_root_.VoterModel.voterTrajectoryMeasureFrom (G : TemporalGraph V) (Measure.dirac ξ₀))
        {ω | ω 0 = ξ₀} = 1
    rw [_root_.VoterModel.voterTrajectoryMeasureFrom_marginal_zero (G : TemporalGraph V)
      (Measure.dirac ξ₀) ξ₀]
    simp
  refine ⟨VoterModel.ofDeterministic (G : TemporalGraph V) ξ₀, hstart, ?_⟩
  -- Uniqueness.
  intro vm hvm
  have hμeq : (vm.μ : Measure (ℕ → (V → Fin κ)))
      = ((VoterModel.ofDeterministic (G : TemporalGraph V) ξ₀).μ : Measure _) := by
    refine ext_of_generate_finite (prefixCyls (V → Fin κ))
      (generateFrom_prefixCyls (V → Fin κ)).symm (isPiSystem_prefixCyls (V → Fin κ)) ?_ ?_
    · rintro _ ⟨t, ξ, rfl⟩
      exact cyl_eq ξ₀
        (fun t a b => VoterModel.transitionProb ((G : TemporalGraph V).snapshot t) a b)
        (vm.μ : Measure _)
        ((VoterModel.ofDeterministic (G : TemporalGraph V) ξ₀).μ : Measure _)
        hvm hstart vm.transition_prefix
        (VoterModel.ofDeterministic (G : TemporalGraph V) ξ₀).transition_prefix t ξ
    · rw [measure_univ, measure_univ]
  -- From equal laws to equal structures (proof irrelevance on the `markovProperty`/`transition`
  -- fields).
  obtain ⟨⟨μ1, hmark1⟩, htrans⟩ := vm
  have hμ1 : μ1 = (VoterModel.ofDeterministic (G : TemporalGraph V) ξ₀).μ :=
    ProbabilityMeasure.toMeasure_injective hμeq
  subst hμ1
  rfl

end TemporalGraph

/-- The standard voter model with `κ` opinions on a temporal graph `G`. -/
structure VoterModel {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraphFixedDegree V) (κ : ℕ) [NeZero κ]
    extends MarkovModel (V → Fin κ) where
  /-- Under the law `μ`, one synchronous step transitions from `x` to `x'` with probability
  `transitionProb`: `P(ξ_{t+1} = x' ∣ ξ_t = x) = transitionProb`, cross-multiplied to avoid
  division. -/
  transition (t x x') :
      μ {ξ | ξ (t + 1) = x' ∧ ξ t = x}
        = (VoterModel.transitionProb (G.snapshot t) x x') * μ {ξ | ξ t = x}

namespace VoterModel

/-- Reinterpret a fixed-degree voter model as one on the underlying `TemporalGraph`
(the two structures share definitionally equal fields). -/
def toBase {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V] {κ : ℕ} [NeZero κ]
    {G : TemporalGraphFixedDegree V} (vm : VoterModel G κ) :
    TemporalGraph.VoterModel G.toTemporalGraph κ :=
  ⟨vm.toMarkovModel, vm.transition⟩

/-- Build a fixed-degree voter model from one on the underlying `TemporalGraph`. -/
def ofBase {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V] {κ : ℕ} [NeZero κ]
    {G : TemporalGraphFixedDegree V} (vm : TemporalGraph.VoterModel G.toTemporalGraph κ) :
    VoterModel G κ :=
  ⟨vm.toMarkovModel, vm.transition⟩

@[simp] theorem toBase_μ {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    {κ : ℕ} [NeZero κ] {G : TemporalGraphFixedDegree V} (vm : VoterModel G κ) :
    vm.toBase.μ = vm.μ := rfl
@[simp] theorem ofBase_μ {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    {κ : ℕ} [NeZero κ]
    {G : TemporalGraphFixedDegree V} (vm : TemporalGraph.VoterModel G.toTemporalGraph κ) :
    (ofBase (G := G) vm).μ = vm.μ := rfl

/-- The full-prefix product recursion for a fixed-degree voter model: the concrete drop-in for the
old single-field Markov property, derived from the general `markovProperty` and `transition`. -/
theorem transition_prefix {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    {κ : ℕ} [NeZero κ]
    {G : TemporalGraphFixedDegree V} (vm : VoterModel G κ) (t : ℕ) (a : ℕ → (V → Fin κ)) :
    (vm.μ : Measure (ℕ → (V → Fin κ))) {ξ | ∀ j ≤ t + 1, ξ j = a j}
      = transitionProb (G.snapshot t) (a t) (a (t + 1))
        * (vm.μ : Measure (ℕ → (V → Fin κ))) {ξ | ∀ j ≤ t, ξ j = a j} :=
  vm.toBase.transition_prefix t a

/-- Bridge to the abstract voter model on the trajectory space. -/
def toAbstract {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V] {κ : ℕ} [NeZero κ]
    {G : TemporalGraphFixedDegree V} (vm : VoterModel G κ) :
    TemporalGraph.VoterModelAbstract G.toTemporalGraph κ (ℕ → (V → Fin κ)) :=
  vm.toBase.toAbstract

/-- The canonical deterministic-start voter model on a fixed-degree graph. -/
def ofDeterministic {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V] {κ : ℕ} [NeZero κ]
    (G : TemporalGraphFixedDegree V) (ξ₀ : V → Fin κ) : VoterModel G κ :=
  ofBase (TemporalGraph.VoterModel.ofDeterministic G.toTemporalGraph ξ₀)

/-- As a sanity-check that the definition of the VoterModel structure is not vacuous, we prove: For
every temporal graph with fixed and positive degrees and for every possible start state ξ₀ of
opinions, there exists exactly one VoterModel. This can be seen as an application of the
Ionescu–Tulcea theorem. -/
theorem existsUnique_ofStart {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    {κ : ℕ} [NeZero κ]
    (G : TemporalGraphFixedDegree V) (ξ₀ : V → Fin κ) :
    ∃! vm : VoterModel G κ, vm.μ {ξ | ξ 0 = ξ₀} = 1 := by
  obtain ⟨base, hbase, huniq⟩ := TemporalGraph.VoterModel.existsUnique_ofStart G ξ₀
  refine ⟨ofBase base, ?_, ?_⟩
  · simp only [ofBase_μ]
    rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at hbase
    exact_mod_cast hbase
  · intro vm hvm
    have hvm' : (vm.toBase.μ : Measure (ℕ → (V → Fin κ))) {ω | ω 0 = ξ₀} = 1 := by
      rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, toBase_μ]
      exact_mod_cast hvm
    have hbaseEq : vm.toBase = base := huniq vm.toBase hvm'
    calc vm = ofBase vm.toBase := by cases vm; rfl
      _ = ofBase base := by rw [hbaseEq]

end VoterModel
