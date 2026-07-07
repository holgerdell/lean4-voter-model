module

public import VoterProcess.Step

/-! ## Two-opinion (`κ = 2`) API for the voter model

This file realizes the paper's §1.3 reduction: for the κ=2 case of the general
`TemporalGraph.VoterModelAbstract` (`\label{def:voter-model}`), the opinion-0 set process
`A_t = {v | ξ_t v = 0} = phiZero (ξ_t)` evolves by the two-opinion kernel `stepDist₂`.
It provides the derived two-opinion API on `VoterModelAbstract G 2` (`A_meas`, `A_markovMarginal`,
`A_markovProperty`, the `phiZero`/`phiZeroInv` bijection, and the smart constructor
`ofOpinionZeroData`, `\label{def:voter-model-two-opinion}`).

The core is the **pushforward identity** `stepDist_map_phiZero`: pushing the
κ=2 joint update `stepDist` along `ξ ↦ {v | ξ v = 0}` gives exactly `stepDist₂`
on the opinion-0 set. It lifts the per-vertex correspondence
`nextOpinionDist_map_phiZero` through the independent-product fold.

## Main results

- `VoterModel.stepDist_map_phiZero` — one-step pushforward to `stepDist₂`.
- `VoterModel.opinionProcess_map_phiZero` — multi-step pushforward to `opinionProcess₂`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Classical

noncomputable section

namespace VoterModel

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]

/-- The opinion-0 vertex set of a two-opinion function: `{v | ξ v = 0}`. -/
def phiZero (ξ : V → Fin 2) : Finset V := Finset.univ.filter (fun v => ξ v = 0)

/-- Per-vertex correspondence (κ=2): pushing the per-vertex update `nextOpinionDist`
along "is the new opinion `0`?" recovers the two-opinion `nextOpinionDist₂` on the
opinion-0 set. -/
theorem nextOpinionDist_map_phiZero (G : TemporalGraph V) (t : ℕ) (ξ : V → Fin 2) (v : V) :
    (TemporalGraph.VoterModel.nextOpinionDist G t ξ v).map (fun o => decide (o = 0))
      = nextOpinionDist₂ G t (phiZero ξ) v := by
  have hmem : ∀ w : V, decide (w ∈ phiZero ξ) = decide (ξ w = 0) := by intro w; simp [phiZero]
  rw [nextOpinionDist_eq_bind]
  unfold nextOpinionDistBind nextOpinionDist₂
  split_ifs with hN
  · rw [PMF.map_bind]; congr 1; ext b; cases b
    · simp [PMF.map_comp, Function.comp, hmem]
    · simp [PMF.pure_map, hmem]
  · simp [PMF.pure_map, hmem]

/-- Fold-lift auxiliary: along the independent-product fold over a `Nodup` list
`l`, the opinion-0 set **restricted to the processed vertices** `l` matches the
two-opinion `Finset`-valued fold. -/
theorem foldK_map_phiZero (G : TemporalGraph V) (t : ℕ) (ξ : V → Fin 2)
    (l : List V) (hnd : l.Nodup) :
    (l.foldr (fun v dist => dist.bind fun f =>
        (TemporalGraph.VoterModel.nextOpinionDist G t ξ v).map fun o => Function.update f v o)
      (PMF.pure (fun _ => 0))).map
      (fun f => l.toFinset.filter (fun u => f u = 0)) =
    l.foldr (fun v dist => dist.bind fun T =>
        (nextOpinionDist₂ G t (phiZero ξ) v).map fun b => cond b (insert v T) T) (PMF.pure ∅) := by
  induction l with
  | nil => simp [PMF.pure_map]
  | cons v tail ih =>
    rw [List.nodup_cons] at hnd
    obtain ⟨hv, hnd'⟩ := hnd
    simp only [List.foldr_cons]
    rw [PMF.map_bind, ← nextOpinionDist_map_phiZero G t ξ v, ← ih hnd', PMF.bind_map]
    apply congrArg (PMF.bind _)
    funext f
    simp only [Function.comp]
    rw [PMF.map_comp, PMF.map_comp]
    congr 1
    funext o
    simp only [Function.comp, List.toFinset_cons]
    have hvtail : v ∉ tail.toFinset := by simpa using hv
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert]
    by_cases ho : o = 0
    · subst ho
      simp only [decide_true, cond_true, Finset.mem_insert, Finset.mem_filter]
      constructor
      · rintro ⟨hx, hxo⟩
        rcases hx with rfl | hx
        · left; rfl
        · right; exact ⟨hx, by rwa [Function.update_of_ne (by rintro rfl; exact hvtail hx)] at hxo⟩
      · rintro (rfl | ⟨hx, hxo⟩)
        · exact ⟨Or.inl rfl, by simp⟩
        · exact ⟨Or.inr hx, by rwa [Function.update_of_ne (by rintro rfl; exact hvtail hx)]⟩
    · simp only [ho, decide_false, cond_false, Finset.mem_filter]
      constructor
      · rintro ⟨hx, hxo⟩
        rcases hx with rfl | hx
        · exact absurd (by simpa using hxo) ho
        · exact ⟨hx, by rwa [Function.update_of_ne (by rintro rfl; exact hvtail hx)] at hxo⟩
      · rintro ⟨hx, hxo⟩
        exact ⟨Or.inr hx, by rwa [Function.update_of_ne (by rintro rfl; exact hvtail hx)]⟩

/-- **One-step pushforward (κ=2).** Pushing the joint update `stepDist` along the
opinion-0 map `phiZero` recovers the two-opinion step `stepDist₂` on the opinion-0 set. -/
theorem stepDist_map_phiZero (G : TemporalGraph V) (t : ℕ) (ξ : V → Fin 2) :
    (stepDist G t ξ).map phiZero = stepDist₂ G t (phiZero ξ) := by
  have h := foldK_map_phiZero G t ξ Finset.univ.toList (Finset.nodup_toList _)
  rw [stepDist_eq_fold]
  unfold stepDistFold stepDist₂
  rw [← h]
  congr 1
  funext f
  simp [phiZero, Finset.toList_toFinset]

/-- **Multi-step pushforward (κ=2).** Pushing the multi-step process
`opinionProcess` along `phiZero` recovers the two-opinion `opinionProcess₂`. -/
theorem opinionProcess_map_phiZero (G : TemporalGraph V) (t₀ : ℕ) (Δ : ℕ) (ξ : V → Fin 2) :
    (opinionProcess G t₀ Δ ξ).map phiZero = opinionProcess₂ G t₀ Δ (phiZero ξ) := by
  induction Δ with
  | zero => simp [opinionProcess, opinionProcess₂, PMF.pure_map]
  | succ Δ ih =>
    rw [opinionProcess, opinionProcess₂, PMF.map_bind]
    simp only [stepDist_map_phiZero]
    rw [← ih, PMF.bind_map]
    rfl

/-! ### Consensus ↔ minority-set helpers (κ=2)

A two-opinion configuration is at consensus iff its opinion-0 set is `∅` or
`univ`, and in either case the minority set is empty; conversely a non-consensus
configuration has a nonempty minority set. -/

omit [DecidableEq V] in
/-- At consensus (`κ=2`), the opinion-0 set is everything or nothing. -/
private theorem phiZero_eq_empty_or_univ {ξ : V → Fin 2} (h : IsConsensus ξ) :
    phiZero ξ = ∅ ∨ phiZero ξ = univ := by
  obtain ⟨v0⟩ := ‹Nonempty V›
  by_cases h0 : ξ v0 = 0
  · right
    rw [phiZero, Finset.filter_true_of_mem]
    exact fun v _ => (h v v0).trans h0
  · left
    rw [phiZero, Finset.filter_false_of_mem]
    exact fun v _ hv => h0 ((h v0 v).trans hv)

/-- Every vertex has a neighbour ⟹ the total volume is positive. -/
private theorem volume_univ_pos_neighbors {G : TemporalGraph V} {s : ℕ}
    (hG : ∀ v, (G.neighborFinset s v).Nonempty) :
    0 < TemporalGraph.volume G s univ := by
  apply SimpleGraph.volume_univ_pos
  intro v
  exact (hG v).card_pos

/-- At consensus (`κ=2`), the minority set is empty. -/
theorem minoritySet_phiZero_eq_empty_of_isConsensus
    {G : TemporalGraph V} {s : ℕ}
    (hG : ∀ v, (G.neighborFinset s v).Nonempty)
    {ξ : V → Fin 2} (h : IsConsensus ξ) :
    minoritySet G s (phiZero ξ) = ∅ := by
  rcases phiZero_eq_empty_or_univ h with he | hu
  · rw [he]
    unfold minoritySet
    have hvol : TemporalGraph.volume G s (∅ : Finset V)
        ≤ TemporalGraph.volume G s (univ \ ∅) := by
      have h0 : TemporalGraph.volume G s (∅ : Finset V) = 0 := by
        simp [TemporalGraph.volume, SimpleGraph.volume]
      rw [h0]; exact Nat.zero_le _
    rw [if_pos hvol]
  · rw [hu]
    unfold minoritySet
    have hvol : ¬ (TemporalGraph.volume G s (univ : Finset V)
        ≤ TemporalGraph.volume G s (univ \ univ)) := by
      rw [Finset.sdiff_self]
      have h0 : TemporalGraph.volume G s (∅ : Finset V) = 0 := by
        simp [TemporalGraph.volume, SimpleGraph.volume]
      rw [h0]
      exact Nat.not_le.mpr (volume_univ_pos_neighbors hG)
    rw [if_neg hvol, Finset.sdiff_self]

omit [Fintype V] [Nonempty V] [DecidableEq V] in
/-- Away from consensus (`κ=2`), there is both a vertex with opinion `0` and a
vertex with a nonzero opinion. -/
private theorem exists_zero_and_nonzero_of_not_isConsensus {ξ : V → Fin 2}
    (h : ¬ IsConsensus ξ) :
    (∃ a, ξ a = 0) ∧ (∃ b, ξ b ≠ 0) := by
  unfold IsConsensus at h
  push Not at h
  obtain ⟨u, w, huw⟩ := h
  have hval : ∀ x : Fin 2, x = 0 ∨ x = 1 := by decide
  by_cases h0 : ξ u = 0
  · exact ⟨⟨u, h0⟩, ⟨w, fun hw => huw (h0.trans hw.symm)⟩⟩
  · have hu1 : ξ u = 1 := (hval (ξ u)).resolve_left h0
    refine ⟨⟨w, ?_⟩, ⟨u, h0⟩⟩
    rcases hval (ξ w) with hw0 | hw1
    · exact hw0
    · exact absurd (hu1.trans hw1.symm) huw

omit [Nonempty V] [DecidableEq V] in
/-- Away from consensus, the opinion-0 set is neither empty nor everything. -/
private theorem phiZero_ne_empty_ne_univ_of_not_isConsensus {ξ : V → Fin 2}
    (h : ¬ IsConsensus ξ) :
    phiZero ξ ≠ ∅ ∧ phiZero ξ ≠ univ := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := exists_zero_and_nonzero_of_not_isConsensus h
  refine ⟨Finset.ne_empty_of_mem (a := a) (by simp [phiZero, ha]), ?_⟩
  intro hu
  have hbmem : b ∈ phiZero ξ := hu ▸ Finset.mem_univ b
  rw [phiZero, Finset.mem_filter] at hbmem
  exact hb hbmem.2

/-- Away from consensus, the minority set is nonempty. -/
theorem minoritySet_phiZero_ne_empty_of_not_isConsensus
    {G : TemporalGraph V} {s : ℕ} {ξ : V → Fin 2} (h : ¬ IsConsensus ξ) :
    minoritySet G s (phiZero ξ) ≠ ∅ := by
  obtain ⟨hne, hnu⟩ := phiZero_ne_empty_ne_univ_of_not_isConsensus h
  unfold minoritySet
  split_ifs with hc
  · exact hne
  · intro hc2
    rw [Finset.sdiff_eq_empty_iff_subset] at hc2
    exact hnu (Finset.univ_subset_iff.mp hc2)

/-- The configuration with opinion-0 set `T`: vertices in `T` hold opinion `0`,
all others hold opinion `1`. This is the inverse of `phiZero` (`κ = 2`). -/
def phiZeroInv (T : Finset V) : V → Fin 2 := fun v => if v ∈ T then 0 else 1

/-- Every `Fin 2` value is `0` or `1`. -/
theorem fin2_cases : ∀ x : Fin 2, x = 0 ∨ x = 1 := by decide

omit [Nonempty V] in
/-- `phiZero ∘ phiZeroInv = id`: the opinion-0 set of `phiZeroInv T` is `T`. -/
theorem phiZero_phiZeroInv (T : Finset V) : phiZero (phiZeroInv T) = T := by
  ext v
  simp only [phiZero, phiZeroInv, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases h : v ∈ T
  · simp [h]
  · simp [h]

omit [Nonempty V] in
/-- `phiZeroInv ∘ phiZero = id`: reconstructing a configuration from its
opinion-0 set recovers it (uses that the non-zero value of `Fin 2` is `1`). -/
theorem phiZeroInv_phiZero (f : V → Fin 2) : phiZeroInv (phiZero f) = f := by
  funext v
  simp only [phiZeroInv, phiZero, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases fin2_cases (f v) with h | h
  · simp [h]
  · rw [if_neg (by rw [h]; decide), h]

omit [Nonempty V] in
/-- For `κ = 2`, `phiZero` is injective: the opinion-0 set determines the whole
configuration. -/
theorem phiZero_injective : Function.Injective (phiZero (V := V)) := by
  intro f g h
  rw [← phiZeroInv_phiZero f, ← phiZeroInv_phiZero g, h]

omit [Nonempty V] in
/-- Pushforward of a `PMF` along the κ=2 bijection `phiZero`, evaluated at a
point in the image: `(P.map phiZero) (phiZero g) = P g`. -/
theorem map_phiZero_apply (P : PMF (V → Fin 2)) (g : V → Fin 2) :
    (P.map phiZero) (phiZero g) = P g := by
  rw [PMF.map_apply]
  refine (tsum_eq_single g (fun h hne => ?_)).trans (if_pos rfl)
  exact if_neg (fun he => hne (phiZero_injective he).symm)

end VoterModel

namespace TemporalGraph

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
variable {Ω : Type*} [MeasurableSpace Ω] {G : TemporalGraph V}

/-- The fiber of `phiZero` over `T`: opinion functions whose opinion-0 set is `T`. -/
private def fib (T : Finset V) : Finset (V → Fin 2) :=
  Finset.univ.filter (fun f => VoterModel.phiZero f = T)

omit [Nonempty V] in
private theorem mem_fib {f : V → Fin 2} {T : Finset V} :
    f ∈ fib T ↔ VoterModel.phiZero f = T := by
  simp [fib]

/-- Each fiber event `{ω | ξ_j ω = f}` is measurable. -/
private theorem xi_eq_measurable (vm : VoterModelAbstract G 2 Ω) (j : ℕ) (f : V → Fin 2) :
    MeasurableSet {ω | vm.ξ j ω = f} :=
  vm.hξ_meas j _ ⟨{f}, trivial, by ext ω; simp [Set.mem_preimage]⟩

/-- Decompose `{ω | phiZero (ξ_j ω) = T}` as the disjoint union of fiber events. -/
private theorem phiZero_event_eq (vm : VoterModelAbstract G 2 Ω) (j : ℕ) (T : Finset V) :
    {ω | VoterModel.phiZero (vm.ξ j ω) = T} = ⋃ f ∈ fib T, {ω | vm.ξ j ω = f} := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, mem_fib]
  exact ⟨fun h => ⟨vm.ξ j ω, h, rfl⟩, fun ⟨_, hf, hω⟩ => hω ▸ hf⟩

/-- The fiber events `{ω | ξ_j ω = f}` are pairwise disjoint. -/
private theorem xi_event_disjoint (vm : VoterModelAbstract G 2 Ω) (j : ℕ)
    (s : Finset (V → Fin 2)) :
    (↑s : Set (V → Fin 2)).PairwiseDisjoint (fun f => {ω | vm.ξ j ω = f}) := by
  intro f _ f' _ hff
  refine Set.disjoint_left.mpr fun ω hω hω' => hff ?_
  simp only [Set.mem_setOf_eq] at hω hω'
  exact hω ▸ hω'

omit [Nonempty V] in
/-- Summing a `PMF` over a fiber of `phiZero` equals its pushforward value. -/
private theorem fib_sum_eq_map (P : PMF (V → Fin 2)) (T : Finset V) :
    ∑ g ∈ fib T, P g = (P.map VoterModel.phiZero) T := by
  rw [PMF.map_apply, tsum_fintype]
  unfold fib
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun g _ => ?_
  by_cases h : VoterModel.phiZero g = T
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg fun he => h he.symm]

/-- `ω ↦ stepDist G t (ξ_t ω) g` is measurable. -/
private theorem stepDist_apply_measurable (vm : VoterModelAbstract G 2 Ω) (t : ℕ) (g : V → Fin 2) :
    Measurable (fun ω => VoterModel.stepDist G t (vm.ξ t ω) g) := by
  have hξ : @Measurable Ω (V → Fin 2) _ ⊤ (vm.ξ t) :=
    measurable_iff_comap_le.mpr (vm.hξ_meas t)
  exact (measurable_from_top (f := fun f => VoterModel.stepDist G t f g)).comp hξ

/-- The opinion-0 set process `A` of a general κ-opinion voter model is
measurable w.r.t. the ambient σ-algebra (derived from `hξ_meas`). -/
theorem VoterModelAbstract.A_meas {κ : ℕ} [NeZero κ] (vm : VoterModelAbstract G κ Ω) (t : ℕ) :
    MeasurableSpace.comap (vm.opinionZeroSet t) ⊤ ≤ ‹MeasurableSpace Ω› := by
  have hle : MeasurableSpace.comap (vm.opinionZeroSet t) ⊤
      ≤ MeasurableSpace.comap (vm.ξ t) ⊤ := by
    rw [show (vm.opinionZeroSet t)
          = (fun ξ : V → Fin κ => Finset.univ.filter (fun v => ξ v = 0)) ∘ vm.ξ t from rfl,
        ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono le_top
  exact le_trans hle (vm.hξ_meas t)

/-- **Marginal Markov property for the opinion-0 set process (κ=2).** The joint
probability of `A_t = T` and `A_{t+Δ} = S'` factors through the two-opinion
`opinionProcess₂`. Derived from the general `markovMarginal` by pushforward along `phiZero`. -/
theorem VoterModelAbstract.A_markovMarginal (vm : VoterModelAbstract G 2 Ω) (t Δ : ℕ) (T S' : Finset V) :
    (vm.μ : Measure Ω) ({ω | vm.opinionZeroSet t ω = T} ∩ {ω | vm.opinionZeroSet (t + Δ) ω = S'}) =
      (vm.μ : Measure Ω) {ω | vm.opinionZeroSet t ω = T} * VoterModel.opinionProcess₂ G t Δ T S' := by
  show (vm.μ : Measure _) ({ω | VoterModel.phiZero (vm.ξ t ω) = T}
        ∩ {ω | VoterModel.phiZero (vm.ξ (t + Δ) ω) = S'})
      = (vm.μ : Measure _) {ω | VoterModel.phiZero (vm.ξ t ω) = T}
        * VoterModel.opinionProcess₂ G t Δ T S'
  have hmeasF : MeasurableSet {ω | VoterModel.phiZero (vm.ξ (t + Δ) ω) = S'} := by
    rw [phiZero_event_eq vm (t + Δ) S']
    exact MeasurableSet.biUnion (fib S').countable_toSet
      (fun g _ => xi_eq_measurable vm (t + Δ) g)
  rw [phiZero_event_eq vm t T, Set.iUnion₂_inter]
  rw [measure_biUnion_finset
      (by
        intro f _ f' _ hff
        refine Set.disjoint_left.mpr fun ω hω hω' => hff ?_
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at hω hω'
        exact hω.1 ▸ hω'.1)
      (fun f _ => (xi_eq_measurable vm t f).inter hmeasF)]
  rw [measure_biUnion_finset (xi_event_disjoint vm t (fib T))
        (fun f _ => xi_eq_measurable vm t f),
      Finset.sum_mul]
  refine Finset.sum_congr rfl fun f hf => ?_
  rw [phiZero_event_eq vm (t + Δ) S', Set.inter_iUnion₂,
      measure_biUnion_finset
        (by
          intro g _ g' _ hgg
          refine Set.disjoint_left.mpr fun ω hω hω' => hgg ?_
          simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at hω hω'
          exact hω.2 ▸ hω'.2)
        (fun g _ => (xi_eq_measurable vm t f).inter (xi_eq_measurable vm (t + Δ) g))]
  rw [Finset.sum_congr rfl (fun g _ => vm.markovMarginal t Δ f g), ← Finset.mul_sum,
      fib_sum_eq_map, VoterModel.opinionProcess_map_phiZero, mem_fib.mp hf]

/-- **Conditional Markov property for the opinion-0 set process (κ=2).** For any
`B` measurable w.r.t. `σ(A_0, …, A_t)`, `μ(B ∩ {A_{t+1} = S'}) = ∫_B stepDist₂(G,t,A_t)(S')`.
Derived from the general `markovProperty` by pushforward along `phiZero`. -/
theorem VoterModelAbstract.A_markovProperty (vm : VoterModelAbstract G 2 Ω) (t : ℕ) (S' : Finset V) (B : Set Ω)
    (hB : @MeasurableSet Ω (⨆ j ∈ Finset.Iic t,
      MeasurableSpace.comap (vm.opinionZeroSet j) ⊤) B) :
    (vm.μ : Measure Ω) (B ∩ {ω | vm.opinionZeroSet (t + 1) ω = S'}) =
      ∫⁻ ω in B, (VoterModel.stepDist₂ G t (vm.opinionZeroSet t ω)) S' ∂vm.μ := by
  show (vm.μ : Measure _) (B ∩ {ω | VoterModel.phiZero (vm.ξ (t + 1) ω) = S'})
      = ∫⁻ ω in B, VoterModel.stepDist₂ G t (VoterModel.phiZero (vm.ξ t ω)) S' ∂vm.μ
  have hle : (⨆ j ∈ Finset.Iic t,
        MeasurableSpace.comap (fun ω => VoterModel.phiZero (vm.ξ j ω)) ⊤)
      ≤ ⨆ j ∈ Finset.Iic t, MeasurableSpace.comap (vm.ξ j) ⊤ := by
    apply iSup₂_mono
    intro j _
    rw [show (fun ω => VoterModel.phiZero (vm.ξ j ω))
          = VoterModel.phiZero ∘ vm.ξ j from rfl, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono le_top
  have hB' : MeasurableSet[⨆ j ∈ Finset.Iic t,
      MeasurableSpace.comap (vm.ξ j) ⊤] B := hle _ hB
  have hBmΩ : MeasurableSet B :=
    (iSup₂_le fun j _ => vm.hξ_meas j) _ hB'
  rw [phiZero_event_eq vm (t + 1) S', Set.inter_iUnion₂,
      measure_biUnion_finset
        (by
          intro g _ g' _ hgg
          refine Set.disjoint_left.mpr fun ω hω hω' => hgg ?_
          simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at hω hω'
          exact hω.2 ▸ hω'.2)
        (fun g _ => hBmΩ.inter (xi_eq_measurable vm (t + 1) g))]
  rw [Finset.sum_congr rfl (fun g _ =>
    (ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure vm.μ _).symm.trans
      (vm.markovProperty t g B hB'))]
  simp only [← VoterModel.stepDist_apply]
  rw [← lintegral_finsetSum (fib S') (fun g _ => stepDist_apply_measurable vm t g)]
  refine lintegral_congr fun ω => ?_
  rw [fib_sum_eq_map, VoterModel.stepDist_map_phiZero]

/-- For `κ = 2`, the σ-algebra generated by `ξ_j` equals the one generated by the
opinion-0 set `A_j`, because `phiZero`/`phiZeroInv` are mutually inverse. -/
theorem VoterModelAbstract.comap_xi_eq_comap_A (vm : VoterModelAbstract G 2 Ω) (j : ℕ) :
    MeasurableSpace.comap (vm.ξ j) ⊤ = MeasurableSpace.comap (vm.opinionZeroSet j) ⊤ := by
  apply le_antisymm
  · rw [show vm.ξ j = VoterModel.phiZeroInv ∘ vm.opinionZeroSet j from
          funext fun ω => (VoterModel.phiZeroInv_phiZero (vm.ξ j ω)).symm,
        ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono le_top
  · rw [show vm.opinionZeroSet j = VoterModel.phiZero ∘ vm.ξ j from rfl, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono le_top

/-- For `κ = 2`, the natural filtration `ℱ_t = σ(ξ_0, …, ξ_t)` coincides with the
opinion-0 set filtration `σ(A_0, …, A_t)`. -/
theorem VoterModelAbstract.fseq_eq_A (vm : VoterModelAbstract G 2 Ω) (t : ℕ) :
    vm.ℱ t = ⨆ j ∈ Finset.Iic t, MeasurableSpace.comap (vm.opinionZeroSet j) ⊤ := by
  show (⨆ j ∈ Finset.Iic t, MeasurableSpace.comap (vm.ξ j) ⊤)
      = ⨆ j ∈ Finset.Iic t, MeasurableSpace.comap (vm.opinionZeroSet j) ⊤
  exact iSup_congr fun j => iSup_congr fun _ => VoterModelAbstract.comap_xi_eq_comap_A vm j

/-- Bridge measurability of `B` from the natural filtration `vm.ℱ t` (= `σ(ξ)`) to
the opinion-0 set history `⨆ j ∈ Iic t, σ(A_j)` (κ=2). The two σ-algebras are equal
via `fseq_eq_A`; this is the form consumed by `A_markovProperty`. -/
theorem VoterModelAbstract.fmeas_to_Asup (vm : VoterModelAbstract G 2 Ω) {t : ℕ} {B : Set Ω}
    (hB : MeasurableSet[vm.ℱ t] B) :
    @MeasurableSet Ω (⨆ j ∈ Finset.Iic t, MeasurableSpace.comap (vm.opinionZeroSet j) ⊤) B :=
  vm.fseq_eq_A t ▸ hB

/-- The event `{ω | A_k ω = X}` is measurable w.r.t. the natural filtration `vm.ℱ t`
for any `k ≤ t` (κ general): `A_k` is `ℱ_k`-measurable and `ℱ_k ≤ ℱ_t`. -/
theorem VoterModelAbstract.measurableSet_setOf_A_eq {κ : ℕ} [NeZero κ] (vm : VoterModelAbstract G κ Ω)
    {t k : ℕ} (hk : k ≤ t) (X : Finset V) :
    @MeasurableSet Ω (vm.ℱ t) {ω | vm.opinionZeroSet k ω = X} :=
  vm.ℱ.mono hk _ ((vm.A_stronglyAdapted k).measurable (measurableSet_singleton X))

/-- For a two-opinion configuration `phiZeroInv T`, the κ=2 one-step kernel
`stepDist` at `g : V → Fin 2` equals the two-opinion `stepDist₂` at `phiZero g`. -/
theorem VoterModelAbstract.stepDist_phiZeroInv_apply (t : ℕ) (T : Finset V) (g : V → Fin 2) :
    VoterModel.stepDist G t (VoterModel.phiZeroInv T) g =
      VoterModel.stepDist₂ G t T (VoterModel.phiZero g) := by
  rw [← VoterModel.map_phiZero_apply (VoterModel.stepDist G t (VoterModel.phiZeroInv T)) g,
    VoterModel.stepDist_map_phiZero, VoterModel.phiZero_phiZeroInv]


omit [Nonempty V] [MeasurableSpace Ω] in
/-- Event rewrite: `phiZeroInv (A_t) = f` iff `A_t = phiZero f`. -/
private theorem phiZeroInv_data_event_eq {A : ℕ → Ω → Finset V} (t : ℕ) (f : V → Fin 2) :
    {ω | VoterModel.phiZeroInv (A t ω) = f} = {ω | A t ω = VoterModel.phiZero f} := by
  ext ω
  simp only [Set.mem_setOf_eq]
  exact ⟨fun h => by rw [← h, VoterModel.phiZero_phiZeroInv],
         fun h => by rw [h, VoterModel.phiZeroInv_phiZero]⟩

/-- \label{def:voter-model-two-opinion}

**Smart constructor for `VoterModelAbstract G 2` from opinion-0-set data.** Given a
probability measure `μ`, an opinion-0 set process `A : ℕ → Ω → Finset V` with its
measurability, marginal Markov (through `opinionProcess₂`), and conditional Markov
(through `stepDist₂`) properties — exactly the data of the two-opinion voter model —
build a general κ=2 `VoterModel` whose opinion process is `ξ_t = phiZeroInv (A_t)`.
Its opinion-0 set recovers `A` (see `ofOpinionZeroData_A`). This packages the
bijection transport (`phiZeroInv`/`phiZero`) so constructions never mention the
two-opinion structure. -/
def VoterModelAbstract.ofOpinionZeroData (μ : ProbabilityMeasure Ω) (A : ℕ → Ω → Finset V)
    (hA_meas : ∀ t, MeasurableSpace.comap (A t) ⊤ ≤ ‹MeasurableSpace Ω›)
    (hmarkovProperty : ∀ (t : ℕ) (S' : Finset V) (B : Set Ω),
      @MeasurableSet Ω (⨆ j ∈ Finset.Iic t, MeasurableSpace.comap (A j) ⊤) B →
      (μ : Measure Ω) (B ∩ {ω | A (t + 1) ω = S'}) =
        ∫⁻ ω in B, (VoterModel.stepDist₂ G t (A t ω)) S' ∂μ) :
    VoterModelAbstract G 2 Ω where
  μ := μ
  ξ := fun t ω => VoterModel.phiZeroInv (A t ω)
  hξ_meas := fun t => by
    have hle : MeasurableSpace.comap (fun ω => VoterModel.phiZeroInv (A t ω)) ⊤
        ≤ MeasurableSpace.comap (A t) ⊤ := by
      rw [show (fun ω => VoterModel.phiZeroInv (A t ω))
            = VoterModel.phiZeroInv ∘ A t from rfl, ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono le_top
    exact le_trans hle (hA_meas t)
  markovProperty := by
    intro t g B hB
    rw [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    simp only [← VoterModel.stepDist_apply]
    show (μ : Measure _) (B ∩ {ω | VoterModel.phiZeroInv (A (t + 1) ω) = g})
        = ∫⁻ ω in B, (VoterModel.stepDist G t (VoterModel.phiZeroInv (A t ω))) g ∂μ
    have hle : (⨆ j ∈ Finset.Iic t,
          MeasurableSpace.comap (fun ω => VoterModel.phiZeroInv (A j ω)) ⊤)
        ≤ ⨆ j ∈ Finset.Iic t, MeasurableSpace.comap (A j) ⊤ := by
      apply iSup₂_mono
      intro j _
      rw [show (fun ω => VoterModel.phiZeroInv (A j ω))
            = VoterModel.phiZeroInv ∘ A j from rfl, ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono le_top
    rw [phiZeroInv_data_event_eq (t + 1) g, hmarkovProperty t (VoterModel.phiZero g) B (hle _ hB)]
    refine lintegral_congr fun ω => ?_
    exact (VoterModelAbstract.stepDist_phiZeroInv_apply t (A t ω) g).symm



end TemporalGraph
