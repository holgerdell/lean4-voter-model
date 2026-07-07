module

public import VoterProcess.Instances
public import Mathlib.Probability.Process.Adapted
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import VoterProcess.CrossCut

/-! ## The standard κ-opinion voter model on a temporal graph

This file formalizes the paper's general voter model (`\label{def:voter-model}`):
a κ-opinion process `ξ : ℕ → Ω → (V → Fin κ)` on a temporal graph, where at
each step every vertex independently and synchronously picks a uniform random
neighbour and, with probability `1/2`, adopts that neighbour's opinion.

For the two-opinion (`κ = 2`) case, the opinion-0 set process `A` is recovered
here as a **def** `vm.opinionZeroSet t ω = {v | ξ t ω v = 0}` (not a field); the derived
two-opinion API (`A_markovMarginal`, `A_markovProperty`, `volS`, `psiS`, `cutS`, …) lives in
`Spec/VoterModelTwoOpinion.lean`.

## Main definitions

- `VoterModel.nextOpinionDist` / `VoterModel.stepDist` — per-vertex / joint one-step
  κ-opinion transition.
- `VoterModel.opinionProcess` — the multi-step κ-opinion process.
- `VoterModel.IsConsensus` — all vertices hold the same opinion.
- `TemporalGraph.VoterModelAbstract` — the standard κ-opinion voter model bundle.
- `vm.opinionZeroSet`, `vm.S`, `vm.ℱ` — opinion-0 set, minority set, natural filtration (defs).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Classical ENNReal

noncomputable section

namespace VoterModel

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V] {κ : ℕ} [NeZero κ]

/-- Monadic/`bind` formulation of the per-vertex next-opinion distribution: vertex
`v` keeps its opinion `ξ v` with probability `1/2`, otherwise adopts the opinion
`ξ w` of a uniformly random neighbour `w` (or keeps `ξ v` if isolated). Kept as an
alternative formulation, bridged to the primary `nextOpinionDist` by `nextOpinionDist_eq_bind`. -/
def nextOpinionDistBind (G : TemporalGraph V) (t : ℕ) (ξ : V → Fin κ) (v : V) : PMF (Fin κ) :=
  if hN : (G.neighborFinset t v).Nonempty then
    (PMF.uniformOfFintype Bool).bind fun b =>
      cond b (PMF.pure (ξ v)) ((PMF.uniformOfFinset (G.neighborFinset t v) hN).map fun w => ξ w)
  else PMF.pure (ξ v)

end VoterModel

namespace TemporalGraph.VoterModel

/-- Per-vertex one-step mass function of the standard voter model:
the probability that vertex `v`'s next opinion is `o` equals `½·[o = ξ v] + ½·#{w ∈ N(v) : ξ w = o}/deg(v)`. -/
def nextOpinionMass {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V] {κ : ℕ}
    (G : TemporalGraph V) (t : ℕ) (ξ : V → Fin κ) (v : V) : Fin κ → ℝ≥0∞ :=
  let N := (G.snapshot t).neighborFinset v
  fun o =>
    if N.Nonempty then
      2⁻¹ * (if o = ξ v then 1 else 0)                               -- keep ξ v  (prob 1/2)
      + 2⁻¹ * ((N.filter (fun w => ξ w = o)).card / (N.card : ℝ≥0∞)) -- copy uniform neighbour
    else
      if o = ξ v then 1 else 0

/-- The total mass equals 1. -/
theorem nextOpinionMass_sum_eq_one {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V] {κ : ℕ}
    (G : TemporalGraph V) (t : ℕ) (ξ : V → Fin κ) (v : V) :
    ∑ o : Fin κ, nextOpinionMass G t ξ v o = 1 := by
  simp only [nextOpinionMass]
  by_cases hN : (G.neighborFinset t v).Nonempty
  · simp only [if_pos hN]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have h1 : (∑ o : Fin κ, (if o = ξ v then (1:ℝ≥0∞) else 0)) = 1 := by
      rw [Finset.sum_ite_eq' Finset.univ (ξ v) (fun _ => (1:ℝ≥0∞)), if_pos (Finset.mem_univ _)]
    have hcard : (∑ o : Fin κ, ((G.neighborFinset t v).filter (fun w => ξ w = o)).card)
        = (G.neighborFinset t v).card :=
      (Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (ξ x))).symm
    have h2 : (∑ o : Fin κ, (((G.neighborFinset t v).filter (fun w => ξ w = o)).card : ℝ≥0∞)
        / ((G.neighborFinset t v).card : ℝ≥0∞)) = 1 := by
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_mul, ← Nat.cast_sum, hcard, ← div_eq_mul_inv,
        ENNReal.div_self (by exact_mod_cast (Finset.card_pos.mpr hN).ne')
          (ENNReal.natCast_ne_top _)]
    rw [h1, h2]; simp only [mul_one]; exact ENNReal.inv_two_add_inv_two
  · simp only [if_neg hN]
    rw [Finset.sum_ite_eq' Finset.univ (ξ v) (fun _ => (1:ℝ≥0∞)), if_pos (Finset.mem_univ _)]

/-- Probability mass function of one step of the standard voter model. -/
def nextOpinionDist {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V] {κ : ℕ}
    (G : TemporalGraph V) (t : ℕ) (ξ : V → Fin κ) (v : V) : PMF (Fin κ) :=
  PMF.ofFintype (nextOpinionMass G t ξ v) (nextOpinionMass_sum_eq_one G t ξ v)

end TemporalGraph.VoterModel

namespace VoterModel

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V] {κ : ℕ} [NeZero κ]

/-- Monadic/`foldr` formulation of one synchronous voter step as a joint law over
`V → Fin κ`: the alternative bridged to the primary `stepDist` by `stepDist_eq_fold`. -/
def stepDistFold (G : TemporalGraph V) (t : ℕ) (ξ : V → Fin κ) : PMF (V → Fin κ) :=
  Finset.univ.toList.foldr
    (fun v dist => dist.bind fun f =>
      (TemporalGraph.VoterModel.nextOpinionDist G t ξ v).map fun o => Function.update f v o)
    (PMF.pure (fun _ => 0))

/-- One synchronous step of the lazy voter model as a joint law over opinion functions `V → Fin κ`:
the independent product of the per-vertex updates `nextOpinionDist` across all vertices. -/
def stepDist (G : TemporalGraph V) (t : ℕ) (ξ : V → Fin κ) : PMF (V → Fin κ) :=
  PMF.ofFintype (fun g => ∏ v : V, TemporalGraph.VoterModel.nextOpinionDist G t ξ v (g v))
    (by
      have h : (∑ g : V → Fin κ, ∏ v : V, TemporalGraph.VoterModel.nextOpinionDist G t ξ v (g v))
          = ∏ v : V, ∑ x : Fin κ, TemporalGraph.VoterModel.nextOpinionDist G t ξ v x := by
        rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
      rw [h]
      refine Finset.prod_eq_one fun v _ => ?_
      have h1 := (TemporalGraph.VoterModel.nextOpinionDist G t ξ v).tsum_coe
      rwa [tsum_fintype] at h1)

/-- The κ-opinion process `(ξ_i : i ≥ t₀)`: the distribution of the opinion
function after `t` steps, starting from `ξ` at time `t₀`. -/
def opinionProcess (G : TemporalGraph V) (t₀ : ℕ) :
    ℕ → (V → Fin κ) → PMF (V → Fin κ)
  | 0, ξ => PMF.pure ξ
  | t + 1, ξ => (opinionProcess G t₀ t ξ).bind (fun ζ => stepDist G (t₀ + t) ζ)

/-- Consensus: all vertices hold the same opinion. -/
def IsConsensus {V : Type*} {κ : ℕ} (ξ : V → Fin κ) : Prop := ∀ u w : V, ξ u = ξ w

/-! ### Independent-product characterization of `stepDist`

The joint update `stepDist` is defined as a `foldr` of per-vertex `Function.update`s.
The product formula `stepDist_apply` certifies it is the independent product of the
per-vertex updates `nextOpinionDist`; this is the bridge between the explicit per-vertex
form used in the `VoterModel` structure below and the `foldr` used by callsites. -/


omit [NeZero κ] in
/-- Bridge: the primary `nextOpinionDist` (explicit mass function) coincides with the
monadic formulation `nextOpinionDistBind`. -/
theorem nextOpinionDist_eq_bind (G : TemporalGraph V) (t : ℕ) (ξ : V → Fin κ) (v : V) :
    TemporalGraph.VoterModel.nextOpinionDist G t ξ v = nextOpinionDistBind G t ξ v := by
  ext o
  show (if (G.neighborFinset t v).Nonempty then
          2⁻¹ * (if o = ξ v then 1 else 0)
            + 2⁻¹ * (((G.neighborFinset t v).filter (fun w => ξ w = o)).card
                      / ((G.neighborFinset t v).card : ℝ≥0∞))
        else (if o = ξ v then 1 else 0)) = nextOpinionDistBind G t ξ v o
  symm
  unfold nextOpinionDistBind
  by_cases hN : (G.neighborFinset t v).Nonempty
  · rw [dif_pos hN, if_pos hN, PMF.bind_apply, tsum_bool]
    simp only [PMF.uniformOfFintype_apply, Fintype.card_bool, Nat.cast_ofNat, cond_false,
      cond_true]
    have hnb : (((PMF.uniformOfFinset (G.neighborFinset t v) hN).map fun w => ξ w) o)
        = (((G.neighborFinset t v).filter (fun w => ξ w = o)).card : ℝ≥0∞)
            / ((G.neighborFinset t v).card : ℝ≥0∞) := by
      rw [PMF.map_apply, tsum_fintype]
      simp only [PMF.uniformOfFinset_apply, ← Finset.sum_filter, Finset.sum_ite_mem]
      rw [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
      congr 3
      ext a
      simp [and_comm, eq_comm]
    have hpure : (PMF.pure (ξ v)) o = if o = ξ v then (1 : ℝ≥0∞) else 0 := by
      by_cases h : o = ξ v
      · rw [if_pos h, PMF.pure_apply, if_pos h]
      · rw [if_neg h, PMF.pure_apply, if_neg h]
    rw [hnb, hpure, add_comm]
  · rw [dif_neg hN, if_neg hN]
    by_cases h : o = ξ v
    · rw [if_pos h, PMF.pure_apply, if_pos h]
    · rw [if_neg h, PMF.pure_apply, if_neg h]

omit [NeZero κ] in
/-- Evaluation of one `foldr` factor: mapping `nextOpinionDist` along the coordinate
update `f ↦ update f a o` and evaluating at `g` keeps `f` off `a` and contributes
`nextOpinionDist a (g a)`. -/
private theorem map_nextOpinion_update_apply (G : TemporalGraph V) (t : ℕ) (ξ : V → Fin κ)
    (a : V) (f g : V → Fin κ) :
    ((TemporalGraph.VoterModel.nextOpinionDist G t ξ a).map fun o => Function.update f a o) g
      = if (∀ w, w ≠ a → f w = g w)
        then (TemporalGraph.VoterModel.nextOpinionDist G t ξ a) (g a) else 0 := by
  rw [PMF.map_apply, tsum_fintype, Finset.sum_eq_single (g a)]
  · by_cases h : ∀ w, w ≠ a → f w = g w
    · rw [if_pos h, if_pos (show g = Function.update f a (g a) from ?_)]
      funext w
      by_cases hw : w = a
      · rw [hw, Function.update_self]
      · rw [Function.update_of_ne hw]; exact (h w hw).symm
    · rw [if_neg h, if_neg (show ¬ g = Function.update f a (g a) from ?_)]
      intro hg
      apply h
      intro w hw
      have hh := congrFun hg w
      rw [Function.update_of_ne hw] at hh
      exact hh.symm
  · intro o _ ho
    rw [if_neg]
    intro hg
    have h1 : g a = o := by have := congrFun hg a; rwa [Function.update_self] at this
    exact ho h1.symm
  · intro hni; exact absurd (Finset.mem_univ _) hni

omit [NeZero κ] in
/-- Closed form for the `foldr` defining `stepDist`, over an arbitrary `Nodup`
list `l` and base value `f₀`: the value at `g` is the product of the per-vertex
masses over the processed vertices `l`, provided `g` agrees with the base `f₀` on
the unprocessed coordinates. -/
private theorem foldr_nextOpinionDist_apply (G : TemporalGraph V) (t : ℕ) (ξ : V → Fin κ) :
    ∀ (l : List V), l.Nodup → ∀ (f₀ g : V → Fin κ),
      (l.foldr (fun v dist => dist.bind fun f =>
          (TemporalGraph.VoterModel.nextOpinionDist G t ξ v).map fun o => Function.update f v o)
        (PMF.pure f₀)) g
        = if (∀ w, w ∉ l → g w = f₀ w)
          then ∏ v ∈ l.toFinset, TemporalGraph.VoterModel.nextOpinionDist G t ξ v (g v) else 0
  | [], _, f₀, g => by
      rw [List.foldr_nil, PMF.pure_apply, List.toFinset_nil, Finset.prod_empty]
      by_cases h : ∀ w, w ∉ ([] : List V) → g w = f₀ w
      · rw [if_pos h, if_pos (funext fun w => h w (by simp))]
      · rw [if_neg h, if_neg (fun hg => h (fun w _ => by rw [hg]))]
  | a :: l, hnd, f₀, g => by
      obtain ⟨ha, hl⟩ := List.nodup_cons.mp hnd
      have ih := foldr_nextOpinionDist_apply G t ξ l hl
      rw [List.foldr_cons, PMF.bind_apply, tsum_fintype]
      simp_rw [map_nextOpinion_update_apply G t ξ a]
      set fs := Function.update g a (f₀ a) with hfs
      rw [Finset.sum_eq_single fs]
      · rw [ih f₀ fs]
        have hsec : (∀ w, w ≠ a → fs w = g w) := by
          intro w hw; rw [hfs, Function.update_of_ne hw]
        rw [if_pos hsec]
        have hcond_iff : (∀ w, w ∉ l → fs w = f₀ w) ↔ (∀ w, w ∉ (a :: l) → g w = f₀ w) := by
          constructor
          · intro h w hw
            rw [List.mem_cons, not_or] at hw
            obtain ⟨hwa, hwl⟩ := hw
            have := h w hwl
            rwa [hfs, Function.update_of_ne hwa] at this
          · intro h w hwl
            by_cases hwa : w = a
            · rw [hwa, hfs, Function.update_self]
            · rw [hfs, Function.update_of_ne hwa]
              exact h w (by rw [List.mem_cons, not_or]; exact ⟨hwa, hwl⟩)
        by_cases hcond : (∀ w, w ∉ l → fs w = f₀ w)
        · rw [if_pos hcond, if_pos (hcond_iff.mp hcond)]
          have hprod_eq : ∏ v ∈ l.toFinset, TemporalGraph.VoterModel.nextOpinionDist G t ξ v (fs v)
              = ∏ v ∈ l.toFinset, TemporalGraph.VoterModel.nextOpinionDist G t ξ v (g v) := by
            refine Finset.prod_congr rfl fun v hv => ?_
            have hva : v ≠ a := by rintro rfl; exact ha (List.mem_toFinset.mp hv)
            rw [hfs, Function.update_of_ne hva]
          rw [hprod_eq, List.toFinset_cons, Finset.prod_insert (by simpa using ha)]
          exact mul_comm _ _
        · rw [if_neg hcond, if_neg (fun h => hcond (hcond_iff.mpr h)), zero_mul]
      · intro b _ hb
        by_cases hc : ∀ w, w ≠ a → b w = g w
        · rw [ih f₀ b, if_neg, zero_mul]
          intro hcond
          apply hb
          funext w
          by_cases hw : w = a
          · rw [hw, hfs, Function.update_self]; exact hcond a ha
          · rw [hfs, Function.update_of_ne hw]; exact hc w hw
        · rw [if_neg hc, mul_zero]
      · intro hni; exact absurd (Finset.mem_univ _) hni

omit [NeZero κ] in
/-- **Product formula for `stepDist`.** The one-step joint update factors as the
independent product of the per-vertex updates:
`stepDist G t ξ g = ∏ v, nextOpinionDist G t ξ v (g v)`. This is the bridge between the
explicit per-vertex form (used in `VoterModel.markovProperty`) and the `foldr`. -/
theorem stepDist_apply (G : TemporalGraph V) (t : ℕ) (ξ g : V → Fin κ) :
    stepDist G t ξ g = ∏ v : V, TemporalGraph.VoterModel.nextOpinionDist G t ξ v (g v) := by
  rw [stepDist, PMF.ofFintype_apply]

/-- Bridge: the primary `stepDist` (explicit independent product) coincides with the
monadic/`foldr` formulation `stepDistFold`. -/
theorem stepDist_eq_fold (G : TemporalGraph V) (t : ℕ) (ξ : V → Fin κ) :
    stepDist G t ξ = stepDistFold G t ξ := by
  ext g
  rw [stepDist_apply]
  have h := foldr_nextOpinionDist_apply G t ξ Finset.univ.toList (Finset.nodup_toList _) (fun _ => 0) g
  rw [if_pos (fun w hw => absurd (Finset.mem_toList.mpr (Finset.mem_univ w)) hw),
    Finset.toList_toFinset] at h
  unfold stepDistFold; exact h.symm


end VoterModel

namespace TemporalGraph

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]

/-- The abstract `κ`-opinion voter model on a temporal graph `G` over an arbitrary sample space
`Ω`: a probability space `(Ω, μ)` carrying
the opinion process `ξ`, where `ξ t ω v ∈ Fin κ` is vertex `v`'s opinion at time `t` in outcome `ω`.
The dynamics are the lazy synchronous update (field `markovProperty`): at each step every vertex
independently copies a uniformly random neighbour's opinion with probability `1/2`, else keeps its
own. The opinion-0 set process is the derived def `vm.opinionZeroSet`. -/
structure VoterModelAbstract (G : TemporalGraph V) (κ : ℕ) [NeZero κ] (Ω : Type*)
    [mΩ : MeasurableSpace Ω] where
  /-- The underlying probability measure on `Ω`. -/
  μ : ProbabilityMeasure Ω
  /-- The opinion process: `ξ t ω v` is vertex `v`'s opinion at time `t`. -/
  ξ : ℕ → Ω → (V → Fin κ)
  /-- Each `ξ t` is measurable into `V → Fin κ` (carrying the discrete σ-algebra). -/
  hξ_meas : ∀ t, MeasurableSpace.comap (ξ t) ⊤ ≤ mΩ
  /-- **Conditional Markov property.** For every set `B` in the natural filtration
  `ℱ_t = σ(ξ_0, …, ξ_t)` and every target state `g`, the probability that the next
  configuration is `g`, conditioned on the history up to time `t`, factors as the
  **independent product of the per-vertex updates**:
  `μ(B ∩ {ξ_{t+1} = g}) = ∫⁻ ω in B, ∏ v, nextOpinionDist(G, t, ξ_t(ω), v)(g v) dμ`. -/
  markovProperty (t : ℕ) (g : V → Fin κ) (B : Set Ω)
      (hB : MeasurableSet[⨆ j ∈ Finset.Iic t, MeasurableSpace.comap (ξ j) ⊤] B) :
      μ (B ∩ {ω | ξ (t + 1) ω = g})
        = ∫⁻ ω in B, ∏ v : V, VoterModel.nextOpinionDist G t (ξ t ω) v (g v) ∂μ

/-- The abstract `κ`-opinion voter model on the underlying graph of a fixed-degree temporal graph. -/
abbrev _root_.TemporalGraphFixedDegree.VoterModelAbstract {V : Type*} [Fintype V] [Nonempty V]
    [DecidableEq V] (G : TemporalGraphFixedDegree V) (κ : ℕ) [NeZero κ] (Ω : Type*)
    [MeasurableSpace Ω] :=
  TemporalGraph.VoterModelAbstract G.toTemporalGraph κ Ω

variable {κ : ℕ} [NeZero κ] {Ω : Type*} [MeasurableSpace Ω] {G : TemporalGraph V}

/-- Fiber decomposition of a set-integral of a function of `ξ_s`: since `ξ_s`
takes finitely many values, `∫_B F(ξ_s ω) dμ = ∑_h F h · μ(B ∩ {ξ_s = h})`. -/
private theorem lintegral_xi_fiber_sum (vm : VoterModelAbstract G κ Ω) (s : ℕ) (B : Set Ω)
    (F : (V → Fin κ) → ℝ≥0∞) :
    ∫⁻ ω in B, F (vm.ξ s ω) ∂(vm.μ : Measure Ω)
      = ∑ h : V → Fin κ, F h * (vm.μ : Measure Ω) (B ∩ {ω | vm.ξ s ω = h}) := by
  classical
  have hmeas : ∀ h : V → Fin κ, MeasurableSet {ω | vm.ξ s ω = h} := fun h =>
    vm.hξ_meas s _ ⟨{h}, trivial, by ext ω; simp [Set.mem_preimage]⟩
  have hpt : (fun ω => F (vm.ξ s ω))
      = fun ω => ∑ h : V → Fin κ, ({ω | vm.ξ s ω = h}).indicator (fun _ => F h) ω := by
    funext ω
    rw [Finset.sum_eq_single (vm.ξ s ω)]
    · exact (Set.indicator_of_mem (by rfl) _).symm
    · intro h _ hne
      exact Set.indicator_of_notMem (fun heq => hne heq.symm) _
    · intro hni; exact absurd (Finset.mem_univ _) hni
  rw [hpt, lintegral_finsetSum _ fun h _ => measurable_const.indicator (hmeas h)]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [lintegral_indicator (hmeas h), setLIntegral_const, Measure.restrict_apply (hmeas h),
    Set.inter_comm]

/-- Marginal Markov property: the joint probability of `ξ t = f` and
`ξ (t + Δ) = g` factors as `μ{ξ t = f} · opinionProcess G t Δ f g`. Derived from
the one-step conditional Markov property `markovProperty` by induction on `Δ`. -/
theorem VoterModelAbstract.markovMarginal (vm : VoterModelAbstract G κ Ω) (t Δ : ℕ) (f g : V → Fin κ) :
    (vm.μ : Measure Ω) ({ω | vm.ξ t ω = f} ∩ {ω | vm.ξ (t + Δ) ω = g})
      = (vm.μ : Measure Ω) {ω | vm.ξ t ω = f} * VoterModel.opinionProcess G t Δ f g := by
  classical
  induction Δ generalizing g with
  | zero =>
    show (vm.μ : Measure Ω) ({ω | vm.ξ t ω = f} ∩ {ω | vm.ξ t ω = g})
        = (vm.μ : Measure Ω) {ω | vm.ξ t ω = f} * (PMF.pure f) g
    by_cases hfg : g = f
    · subst hfg
      rw [Set.inter_self, PMF.pure_apply, if_pos rfl, mul_one]
    · have hempty : {ω | vm.ξ t ω = f} ∩ {ω | vm.ξ t ω = g} = (∅ : Set Ω) := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro ω ⟨h1, h2⟩
        exact hfg (h1.symm.trans h2).symm
      rw [hempty, measure_empty, PMF.pure_apply, if_neg hfg, mul_zero]
  | succ Δ ih =>
    have hBfilt : @MeasurableSet Ω (⨆ j ∈ Finset.Iic (t + Δ),
        MeasurableSpace.comap (vm.ξ j) ⊤) {ω | vm.ξ t ω = f} := by
      have hle : MeasurableSpace.comap (vm.ξ t) ⊤
          ≤ ⨆ j ∈ Finset.Iic (t + Δ), MeasurableSpace.comap (vm.ξ j) ⊤ :=
        le_iSup₂_of_le t (Finset.mem_Iic.mpr (Nat.le_add_right t Δ)) le_rfl
      apply hle
      exact ⟨{f}, trivial, by ext ω; simp [Set.mem_preimage]⟩
    have hstep := vm.markovProperty (t + Δ) g {ω | vm.ξ t ω = f} hBfilt
    rw [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at hstep
    rw [show {ω | vm.ξ (t + (Δ + 1)) ω = g} = {ω | vm.ξ (t + Δ + 1) ω = g} from rfl, hstep]
    simp only [← VoterModel.stepDist_apply]
    rw [lintegral_xi_fiber_sum vm (t + Δ) {ω | vm.ξ t ω = f}
          (fun h => (VoterModel.stepDist G (t + Δ) h) g),
        show VoterModel.opinionProcess G t (Δ + 1) f
            = (VoterModel.opinionProcess G t Δ f).bind
                (fun ζ => VoterModel.stepDist G (t + Δ) ζ) from rfl,
        PMF.bind_apply, tsum_fintype, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [ih h]; ring

/-- The opinion-0 vertex set `A t ω = {v | ξ t ω v = 0}` (a def, not a structure field). -/
def VoterModelAbstract.opinionZeroSet {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V] {κ : ℕ}
    [NeZero κ] {Ω : Type*} [MeasurableSpace Ω] {G : TemporalGraph V}
    (vm : VoterModelAbstract G κ Ω) (t : ℕ) (ω : Ω) : Finset V :=
  Finset.univ.filter (fun v => vm.ξ t ω v = 0)

/-- The minority set at time `t`: `S t ω = minoritySet G t (A t ω)`. -/
def VoterModelAbstract.S (vm : VoterModelAbstract G κ Ω) (t : ℕ) (ω : Ω) : Finset V :=
  VoterModel.minoritySet G t (vm.opinionZeroSet t ω)

/-- The volume of the minority set at time `t`. -/
def VoterModelAbstract.volS (vm : VoterModelAbstract G κ Ω) (t : ℕ) (ω : Ω) : ℝ :=
  (volume G t (vm.S t ω) : ℝ)

/-- The potential of the minority set at time `t`: `ψ(S_t) = √Vol(S_t)`. -/
def VoterModelAbstract.psiS (vm : VoterModelAbstract G κ Ω) (t : ℕ) (ω : Ω) : ℝ :=
  potential G t (vm.S t ω)

/-- The edge cut of the minority set at time `t`: `e_t(S_t, S̄_t)`. -/
def VoterModelAbstract.cutS (vm : VoterModelAbstract G κ Ω) (t : ℕ) (ω : Ω) : ℕ :=
  edgesBetween G t (vm.S t ω) (univ \ vm.S t ω)

/-- The edge cut of the minority set equals the edge cut of the opinion-0 set,
because `minoritySet` is either `A` or `univ \ A`. -/
theorem VoterModelAbstract.edgesBetween_minoritySet (G : TemporalGraph V) (t k : ℕ) (A : Finset V) :
    edgesBetween G t (VoterModel.minoritySet G k A) (univ \ VoterModel.minoritySet G k A) =
      edgesBetween G t A (univ \ A) := by
  simp only [VoterModel.minoritySet]
  split_ifs with h
  · rfl
  · rw [Finset.sdiff_sdiff_eq_self (Finset.subset_univ _)]
    exact edgesBetween_comm' G t (univ \ A) A

/-- `cutS j ω = edgesBetween G j (vm.opinionZeroSet j ω) (univ \ vm.opinionZeroSet j ω)`:
the edge cut of the minority set equals the edge cut of the opinion-0 set. -/
theorem VoterModelAbstract.cutS_eq_edgesBetween_A (vm : VoterModelAbstract G κ Ω) (j : ℕ) (ω : Ω) :
    vm.cutS j ω = edgesBetween G j (vm.opinionZeroSet j ω) (univ \ vm.opinionZeroSet j ω) :=
  VoterModelAbstract.edgesBetween_minoritySet G j j (vm.opinionZeroSet j ω)

/-- \label{def:filtration}

The standard filtration of a κ-opinion voter model: `ℱ_t = σ(ξ_0, …, ξ_t)`,
the natural filtration of the opinion process `ξ`, using the discrete
σ-algebra on `V → Fin κ`. -/
def VoterModelAbstract.ℱ (vm : VoterModelAbstract G κ Ω) : Filtration ℕ (‹MeasurableSpace Ω›) where
  seq t := ⨆ j ∈ Finset.Iic t, MeasurableSpace.comap (vm.ξ j) ⊤
  mono' s t hst := by
    apply iSup₂_mono'
    intro j hj
    exact ⟨j, Finset.mem_Iic.mpr (le_trans (Finset.mem_Iic.mp hj) hst), le_rfl⟩
  le' t := by
    apply iSup₂_le
    intro j _
    exact vm.hξ_meas j

/-- The opinion-0 set process `A` is strongly adapted to the natural filtration `ℱ`.
Since `ℱ_t = σ(ξ_0, …, ξ_t)` measures `ξ_t`, and `A_t = {v | ξ_t v = 0}` factors
through `ξ_t`, the process `A` is `ℱ`-measurable. The codomain `Finset V` has the
discrete σ-algebra, so every measurable function into it is strongly measurable. -/
theorem VoterModelAbstract.A_stronglyAdapted (vm : VoterModelAbstract G κ Ω) :
    StronglyAdapted vm.ℱ vm.opinionZeroSet := by
  intro t
  have hle : MeasurableSpace.comap (vm.opinionZeroSet t) ⊤ ≤ vm.ℱ t := by
    rw [show (vm.opinionZeroSet t)
          = (fun ξ : V → Fin κ => Finset.univ.filter (fun v => ξ v = 0)) ∘ vm.ξ t from rfl,
        ← MeasurableSpace.comap_comp]
    exact le_trans (MeasurableSpace.comap_mono le_top)
      (le_iSup₂_of_le t (Finset.mem_Iic.mpr le_rfl) le_rfl)
  exact (Measurable.of_comap_le hle).stronglyMeasurable

end TemporalGraph
