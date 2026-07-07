module

import UpperBound.MultiOpinion.Coupling
public import UpperBound.MultiOpinion.Metaphase
import UpperBound.MultiOpinion.Markov
public import TemporalGraph.Degree
public import TemporalGraph.Conductance

/-! ## §3.4 multi-opinion: from the atom-form claim to a conditional expectation

This file lifts the per-history small-opinion bound
`TemporalGraph.claim_Xq_le_half` (which controls
`(μ[· | ξ_r = h])` for a single pinned configuration `h`) to a
conditional-expectation inequality with respect to the full filtration
`ℱ_r = σ(ξ_0, …, ξ_r)`.

The §3.4 indicator is `VoterModelAbstract.Xq vm q s = 1` exactly when the `q`-set
`phiQ q (ξ_s)` is neither empty nor full.  Writing
`K = ∑_{j < J+1} Δ_j`, the main result `condExp_Xq_le_half` shows

  `μ[ Xq vm q (r + K) | ℱ_r ] ≤ 1/2`   a.e. on the event `E_r`

where `E_r` is the `ℱ_r`-measurable "`q` present and small at time `r`"
event obtained by transporting the §3.4 threshold `hJ` of
`claim_Xq_le_half` to the original graph `G` (via `volume_shift`,
`minDegree_shift`, `maxSetConductanceOnInterval_shift`, `admissibleCuts_shift`).

The proof:

* **Markov form of the conditional expectation.** By the multistep Markov
  property `multistep_markov_phiQ`, the function
  `g ω = 1 − P_∅(ω) − P_univ(ω)`, where
  `P_T(ω) = opinionProcess₂ G r K (phiQ q (ξ_r ω)) T`, satisfies
  `∫_B g = ∫_B Xq` for every `B ∈ ℱ_r`.  Since `g` is `ℱ_r`-measurable, the
  uniqueness lemma `ae_eq_condExp_of_forall_setIntegral_eq` gives
  `g =ᵐ μ[Xq | ℱ_r]`.
* **Per-atom value.** On each positive-measure atom `{ξ_r = h}`, `g` is the
  constant `(μ[Xqᵉᵛᵉⁿᵗ | ξ_r = h])` value, which `claim_Xq_le_half` bounds
  by `1/2`.  Atoms of measure zero are negligible.

## Main results
- `condExp_Xq_le_half`: `μ[ Xq vm q (r + K) | ℱ_r ] ≤ᵐ 1/2` on the small-`q`
  event `E_r`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Classical ENNReal

noncomputable section

namespace TemporalGraph

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
variable {κ : ℕ} [NeZero κ] {Ω : Type*} [mΩ : MeasurableSpace Ω] {G : TemporalGraphFixedDegree V}

/-- At time index `0`, the minority set is unchanged by shifting (fixed degrees):
both branches of `minoritySet` compare the same volumes. -/
private lemma minoritySet_shift_zero (G : TemporalGraphFixedDegree V) (r : ℕ)
    (X : Finset V) :
    VoterModel.minoritySet (shift G r) 0 X = VoterModel.minoritySet G 0 X := by
  unfold VoterModel.minoritySet
  rw [volume_shift G r 0 X, volume_shift G r 0 (Finset.univ \ X)]

/-- \label{lem:condexp-Xq-le-half}

**§3.4 conditional-expectation small-opinion bound (Tier B).**

For a κ-opinion voter model `vm` on a fixed-degree temporal graph `G`,
opinion `q`, restart time `r`, and §3.4 interval/threshold data
(`d_min, Δ, φ, b, J`) stated for the *original* graph `G` at the shifted
indices, the conditional expectation of the §3.4 indicator
`Xq vm q (r + K)` with `K = ∑_{j < J+1} Δ_j`, given the filtration `ℱ_r`,
is at most `1/2` almost everywhere on the `ℱ_r`-measurable event

  `E_r = { ω | b · (Vol(minoritySet(phiQ q (ξ_r ω)))/d_min
                    + log(1 + Vol(minoritySet(phiQ q (ξ_r ω))))) ≤ ∑_{ℓ ≤ J} φ_ℓ }`,

i.e. the event that opinion `q` is "small enough at time `r`" for the
absorption threshold to fire.  Here `Vol = volume G 0`.

**FORMALIZATION NOTE (Lean-specific).** The conditioning event `E_r` is the
exact translation of the per-history threshold hypothesis `hJ` of
`claim_Xq_le_half`; making it the conditioning set is what renders the
bound `ℱ_r`-measurable and hence usable downstream.  Measure-zero atoms of
`ξ_r` (where the elementary conditional probability is undefined) are
absorbed into the a.e. quantifier. -/
theorem condExp_Xq_le_half
    (vm : VoterModelAbstract G κ Ω)
    (q : Fin κ) (r : ℕ)
    -- §3.4 threshold data, stated for `G` at shifted indices
    (d_min : ℕ) (hd : d_min = G.minDegreeAt 0) (hd_pos : 0 < d_min)
    (Δ : ℕ → ℕ) (hΔ_pos : ∀ j, 1 ≤ Δ j)
    (φ : ℕ → ℝ) (hφ_nn : ∀ j, 0 ≤ φ j) (hφ_le1 : ∀ j, φ j ≤ 1)
    (hwin : ∀ j, ∀ S ∈ TemporalGraph.admissibleCuts G.toTemporalGraph,
      φ j ≤ TemporalGraph.maxSetConductanceOnInterval G.toTemporalGraph
        ((∑ i ∈ Finset.range j, Δ i) + r) (Δ j) S)
    (b : ℝ) (hb_large : (5462 : ℝ) ≤ b) (J : ℕ) :
    (vm.μ : Measure Ω)[vm.Xq q (r + ∑ j ∈ Finset.range (J + 1), Δ j) | (vm.ℱ r : MeasurableSpace Ω)]
      ≤ᵐ[(vm.μ : Measure Ω).restrict
          {ω | b * ((TemporalGraph.volume G.toTemporalGraph 0
                  (VoterModel.minoritySet G.toTemporalGraph 0 (VoterModel.phiQ q (vm.ξ r ω))) : ℝ) / d_min
                + Real.log (1 + (TemporalGraph.volume G.toTemporalGraph 0
                  (VoterModel.minoritySet G.toTemporalGraph 0 (VoterModel.phiQ q (vm.ξ r ω))) : ℝ)))
              ≤ ∑ ℓ ∈ Finset.range (J + 1), φ ℓ}]
        (fun _ => (1 / 2 : ℝ)) := by
  set K := ∑ j ∈ Finset.range (J + 1), Δ j with hK
  set E_r : Set Ω :=
    {ω | b * ((TemporalGraph.volume G.toTemporalGraph 0
            (VoterModel.minoritySet G.toTemporalGraph 0 (VoterModel.phiQ q (vm.ξ r ω))) : ℝ) / d_min
          + Real.log (1 + (TemporalGraph.volume G.toTemporalGraph 0
            (VoterModel.minoritySet G.toTemporalGraph 0 (VoterModel.phiQ q (vm.ξ r ω))) : ℝ)))
        ≤ ∑ ℓ ∈ Finset.range (J + 1), φ ℓ} with hE_def
  -- Measurability of the opinion-process weights `P_T(ω) = opinionProcess₂ G r K (phiQ q ξ_r) T`.
  have hξr_m : @Measurable Ω (V → Fin κ) mΩ ⊤ (vm.ξ r) :=
    (vm.xi_measurable_filtration r).mono (vm.ℱ.le r) le_rfl
  have hPm : ∀ T : Finset V,
      Measurable (fun ω => (VoterModel.opinionProcess₂ G.toTemporalGraph r K (VoterModel.phiQ q (vm.ξ r ω))) T) :=
    fun T => (measurable_from_top (f := fun f : V → Fin κ =>
      (VoterModel.opinionProcess₂ G.toTemporalGraph r K (VoterModel.phiQ q f)) T)).comp hξr_m
  have hPF : ∀ T : Finset V,
      @Measurable Ω ℝ≥0∞ (vm.ℱ r) _
        (fun ω => (VoterModel.opinionProcess₂ G.toTemporalGraph r K (VoterModel.phiQ q (vm.ξ r ω))) T) :=
    fun T => (measurable_from_top (f := fun f : V → Fin κ =>
      (VoterModel.opinionProcess₂ G.toTemporalGraph r K (VoterModel.phiQ q f)) T)).comp
        (vm.xi_measurable_filtration r)
  have hbnd : ∀ (T : Finset V) (ω : Ω),
      (VoterModel.opinionProcess₂ G.toTemporalGraph r K (VoterModel.phiQ q (vm.ξ r ω))) T ≤ 1 :=
    fun T ω => PMF.coe_le_one _ _
  have hIaux : ∀ T : Finset V,
      Integrable (fun ω => ((VoterModel.opinionProcess₂ G.toTemporalGraph r K
        (VoterModel.phiQ q (vm.ξ r ω))) T).toReal) vm.μ := by
    intro T
    refine Integrable.mono' (integrable_const (1 : ℝ))
      (hPm T).ennreal_toReal.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    calc ((VoterModel.opinionProcess₂ G.toTemporalGraph r K (VoterModel.phiQ q (vm.ξ r ω))) T).toReal
        ≤ (1 : ℝ≥0∞).toReal := ENNReal.toReal_mono ENNReal.one_ne_top (hbnd T ω)
      _ = 1 := ENNReal.toReal_one
  -- The Markov form of the conditional expectation.
  set g : Ω → ℝ := fun ω =>
    1 - ((VoterModel.opinionProcess₂ G.toTemporalGraph r K (VoterModel.phiQ q (vm.ξ r ω))) ∅).toReal
      - ((VoterModel.opinionProcess₂ G.toTemporalGraph r K (VoterModel.phiQ q (vm.ξ r ω))) Finset.univ).toReal
    with hg_def
  have hg_int : Integrable g vm.μ := by
    rw [hg_def]
    exact ((integrable_const (1 : ℝ)).sub (hIaux ∅)).sub (hIaux Finset.univ)
  have hg_Fr : @Measurable Ω ℝ (vm.ℱ r) _ g := by
    rw [hg_def]
    exact (measurable_const.sub (hPF ∅).ennreal_toReal).sub (hPF Finset.univ).ennreal_toReal
  -- Markov identity: `∫_B (P_T)ᵗᵒᴿᵉᵃˡ = (μ (B ∩ {phiQ_{r+K} = T}))ᵗᵒᴿᵉᵃˡ`.
  have markovToReal : ∀ (T : Finset V) (B : Set Ω), @MeasurableSet Ω (vm.ℱ r) B →
      ∫ ω in B, ((VoterModel.opinionProcess₂ G.toTemporalGraph r K (VoterModel.phiQ q (vm.ξ r ω))) T).toReal ∂vm.μ
        = ((vm.μ : Measure _) (B ∩ {ω | VoterModel.phiQ q (vm.ξ (r + K) ω) = T})).toReal := by
    intro T B hB
    rw [integral_toReal (hPm T).aemeasurable
        (ae_of_all _ fun ω => lt_of_le_of_lt (hbnd T ω) ENNReal.one_lt_top),
      ← multistep_markov_phiQ G.toTemporalGraph vm r K q T B hB]
  -- The §3.4 indicator and its two complementary boundary events.
  have hW0m : MeasurableSet {ω | VoterModel.phiQ q (vm.ξ (r + K) ω) = (∅ : Finset V)} :=
    xiK_eq_measurable_phiQ vm (r + K) q ∅
  have hWum : MeasurableSet {ω | VoterModel.phiQ q (vm.ξ (r + K) ω) = Finset.univ} :=
    xiK_eq_measurable_phiQ vm (r + K) q Finset.univ
  have hXq_two : ∀ ω, vm.Xq q (r + K) ω
      = 1 - ({ω | VoterModel.phiQ q (vm.ξ (r + K) ω) = (∅ : Finset V)}.indicator
              (fun _ => (1 : ℝ))) ω
          - ({ω | VoterModel.phiQ q (vm.ξ (r + K) ω) = Finset.univ}.indicator
              (fun _ => (1 : ℝ))) ω := by
    intro ω
    simp only [VoterModelAbstract.Xq, Set.indicator_apply, Set.mem_setOf_eq]
    by_cases h0 : VoterModel.phiQ q (vm.ξ (r + K) ω) = (∅ : Finset V)
    · have hu : VoterModel.phiQ q (vm.ξ (r + K) ω) ≠ Finset.univ := by
        rw [h0]; exact fun h => Finset.univ_nonempty.ne_empty h.symm
      rw [if_pos (Or.inl h0), if_pos h0, if_neg hu]; ring
    · by_cases hu : VoterModel.phiQ q (vm.ξ (r + K) ω) = Finset.univ
      · rw [if_pos (Or.inr hu), if_neg h0, if_pos hu]; ring
      · rw [if_neg (not_or.mpr ⟨h0, hu⟩), if_neg h0, if_neg hu]; ring
  have hXq_int : Integrable (vm.Xq q (r + K)) vm.μ := by
    refine Integrable.mono' (integrable_const (1 : ℝ))
      ((vm.Xq_measurable q (r + K)).mono (vm.ℱ.le (r + K)) le_rfl).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    rw [VoterModelAbstract.Xq]; split_ifs <;> simp
  -- `∫_B g = ∫_B Xq` for every `B ∈ ℱ_r`.
  have hLeq : ∀ B, @MeasurableSet Ω (vm.ℱ r) B →
      ∫ ω in B, g ω ∂vm.μ = ∫ ω in B, vm.Xq q (r + K) ω ∂vm.μ := by
    intro B hBF
    have hgval : ∫ ω in B, g ω ∂vm.μ
        = ((vm.μ : Measure _) B).toReal
          - ((vm.μ : Measure _) (B ∩ {ω | VoterModel.phiQ q (vm.ξ (r + K) ω) = (∅ : Finset V)})).toReal
          - ((vm.μ : Measure _) (B ∩ {ω | VoterModel.phiQ q (vm.ξ (r + K) ω) = Finset.univ})).toReal := by
      have hI1 : Integrable (fun ω => (1 : ℝ)
          - ((VoterModel.opinionProcess₂ G.toTemporalGraph r K (VoterModel.phiQ q (vm.ξ r ω))) ∅).toReal) vm.μ :=
        (integrable_const 1).sub (hIaux ∅)
      simp only [hg_def]
      rw [integral_sub hI1.integrableOn ((hIaux Finset.univ).integrableOn),
          integral_sub ((integrable_const (1 : ℝ)).integrableOn) ((hIaux ∅).integrableOn),
          markovToReal ∅ B hBF, markovToReal Finset.univ B hBF]
      simp only [setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
    have hXqval : ∫ ω in B, vm.Xq q (r + K) ω ∂vm.μ
        = ((vm.μ : Measure _) B).toReal
          - ((vm.μ : Measure _) (B ∩ {ω | VoterModel.phiQ q (vm.ξ (r + K) ω) = (∅ : Finset V)})).toReal
          - ((vm.μ : Measure _) (B ∩ {ω | VoterModel.phiQ q (vm.ξ (r + K) ω) = Finset.univ})).toReal := by
      have hJ1 : Integrable (fun ω => (1 : ℝ)
          - {ω | VoterModel.phiQ q (vm.ξ (r + K) ω) = (∅ : Finset V)}.indicator
              (fun _ => (1 : ℝ)) ω) vm.μ :=
        (integrable_const 1).sub ((integrable_const 1).indicator hW0m)
      simp only [hXq_two]
      rw [integral_sub hJ1.integrableOn (((integrable_const (1 : ℝ)).indicator hWum).integrableOn),
          integral_sub ((integrable_const (1 : ℝ)).integrableOn)
            (((integrable_const (1 : ℝ)).indicator hW0m).integrableOn),
          setIntegral_indicator hW0m, setIntegral_indicator hWum]
      simp only [setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
    rw [hgval, hXqval]
  -- Conditional-expectation identification.
  have hcond_eq : g =ᵐ[(vm.μ : Measure Ω)]
      (vm.μ : Measure Ω)[vm.Xq q (r + K) | (vm.ℱ r : MeasurableSpace Ω)] :=
    ae_eq_condExp_of_forall_setIntegral_eq (vm.ℱ.le r) hXq_int
      (fun s _ _ => hg_int.integrableOn) (fun s hs _ => hLeq s hs)
      hg_Fr.stronglyMeasurable.aestronglyMeasurable
  -- Transport `hwin` to the shifted graph (uniform over the conditioning).
  have hwin_shift : ∀ j, ∀ S ∈ TemporalGraph.admissibleCuts (shift G.toTemporalGraph r),
      φ j ≤ TemporalGraph.maxSetConductanceOnInterval (shift G.toTemporalGraph r)
        (∑ i ∈ Finset.range j, Δ i) (Δ j) S := by
    intro j S hS
    rw [admissibleCuts_shift G r] at hS
    rw [maxSetConductanceOnInterval_shift G r (∑ i ∈ Finset.range j, Δ i) (Δ j) S]
    exact hwin j S hS
  -- The indicator-of-`Eset` form (for the per-atom value).
  have hEsetm : MeasurableSet
      {ω | ¬ (VoterModel.phiQ q (vm.ξ (r + K) ω) = (∅ : Finset V) ∨
              VoterModel.phiQ q (vm.ξ (r + K) ω) = Finset.univ)} := by
    have hEq : {ω | ¬ (VoterModel.phiQ q (vm.ξ (r + K) ω) = (∅ : Finset V) ∨
              VoterModel.phiQ q (vm.ξ (r + K) ω) = Finset.univ)}
        = ({ω | VoterModel.phiQ q (vm.ξ (r + K) ω) = (∅ : Finset V)} ∪
            {ω | VoterModel.phiQ q (vm.ξ (r + K) ω) = Finset.univ})ᶜ := by
      ext ω; simp [Set.mem_compl_iff, not_or]
    rw [hEq]; exact (hW0m.union hWum).compl
  have hXq_ind : ∀ ω, vm.Xq q (r + K) ω
      = Set.indicator
          {ω | ¬ (VoterModel.phiQ q (vm.ξ (r + K) ω) = (∅ : Finset V) ∨
                  VoterModel.phiQ q (vm.ξ (r + K) ω) = Finset.univ)}
          (fun _ => (1 : ℝ)) ω := by
    intro ω
    simp only [VoterModelAbstract.Xq, Set.indicator_apply, Set.mem_setOf_eq]
    by_cases h : VoterModel.phiQ q (vm.ξ (r + K) ω) = (∅ : Finset V) ∨
        VoterModel.phiQ q (vm.ξ (r + K) ω) = Finset.univ
    · rw [if_pos h, if_neg (not_not.mpr h)]
    · rw [if_neg h, if_pos h]
  -- `E_r`-measurability.
  have hErm : MeasurableSet E_r :=
    vm.ℱ.le r _ (vm.xi_event_filtration r
      (fun f => b * ((TemporalGraph.volume G.toTemporalGraph 0
            (VoterModel.minoritySet G.toTemporalGraph 0 (VoterModel.phiQ q f)) : ℝ) / d_min
          + Real.log (1 + (TemporalGraph.volume G.toTemporalGraph 0
            (VoterModel.minoritySet G.toTemporalGraph 0 (VoterModel.phiQ q f)) : ℝ)))
        ≤ ∑ ℓ ∈ Finset.range (J + 1), φ ℓ))
  -- The bound `g ≤ 1/2` a.e. on `E_r`.
  have hbound : g ≤ᵐ[(vm.μ : Measure Ω).restrict E_r] (fun _ => (1 / 2 : ℝ)) := by
    refine (ae_restrict_iff' hErm).mpr ?_
    -- a.e. the atom `{ξ_r = ξ_r ω}` has positive measure
    have hNc : ∀ᵐ ω ∂(vm.μ : Measure Ω), (vm.μ : Measure _) (historySet vm r (vm.ξ r ω)) ≠ 0 := by
      rw [ae_iff]
      have hset : {ω | ¬ (vm.μ : Measure _) (historySet vm r (vm.ξ r ω)) ≠ 0}
          = ⋃ h ∈ {h : V → Fin κ | (vm.μ : Measure _) (historySet vm r h) = 0}, historySet vm r h := by
        ext ω
        simp only [not_not, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop, historySet]
        exact ⟨fun hω => ⟨vm.ξ r ω, hω, rfl⟩,
          fun ⟨h, hh, hωh⟩ => by rw [show vm.ξ r ω = h from hωh]; exact hh⟩
      rw [hset]
      exact (measure_biUnion_null_iff (Set.to_countable _)).mpr (fun h hh => hh)
    filter_upwards [hNc] with ω hωpos
    intro hωEr
    -- Extract the threshold from `E_r`-membership.
    rw [hE_def, Set.mem_setOf_eq] at hωEr
    -- Apply the atom-form claim at `h = ξ_r ω`.
    have hμB0 : (vm.μ : Measure _) (historySet vm r (vm.ξ r ω)) ≠ 0 := hωpos
    have hμBtop : (vm.μ : Measure _) (historySet vm r (vm.ξ r ω)) ≠ ⊤ := measure_ne_top _ _
    have hvol_eq : TemporalGraph.volume (shift G.toTemporalGraph r) 0
          (VoterModel.minoritySet (shift G.toTemporalGraph r) 0 (VoterModel.phiQ q (vm.ξ r ω)))
        = TemporalGraph.volume G.toTemporalGraph 0
          (VoterModel.minoritySet G.toTemporalGraph 0 (VoterModel.phiQ q (vm.ξ r ω))) := by
      rw [minoritySet_shift_zero G r (VoterModel.phiQ q (vm.ξ r ω)),
        volume_shift G r 0 _]
    have hJ_shift : b * ((TemporalGraph.volume (shift G.toTemporalGraph r) 0
              (VoterModel.minoritySet (shift G.toTemporalGraph r) 0
                (VoterModel.phiQ q (vm.ξ r ω))) : ℝ) / d_min
            + Real.log (1 + (TemporalGraph.volume (shift G.toTemporalGraph r) 0
              (VoterModel.minoritySet (shift G.toTemporalGraph r) 0
                (VoterModel.phiQ q (vm.ξ r ω))) : ℝ)))
          ≤ ∑ ℓ ∈ Finset.range (J + 1), φ ℓ := by
      rw [hvol_eq]; exact hωEr
    have hclaim := claim_Xq_le_half G vm q r (vm.ξ r ω) hμB0 d_min
      (by rw [minDegree_shift G r]; exact hd) hd_pos Δ hΔ_pos φ hφ_nn hφ_le1
      hwin_shift b hb_large J hJ_shift
    rw [← hK] at hclaim
    -- Identify `g ω` with the elementary conditional probability of `Eset`.
    have hBF : @MeasurableSet Ω (vm.ℱ r) (historySet vm r (vm.ξ r ω)) :=
      vm.xi_event_filtration r (fun f => f = vm.ξ r ω)
    have hBμ : MeasurableSet (historySet vm r (vm.ξ r ω)) := historySet_meas vm r (vm.ξ r ω)
    have hg_const : Set.EqOn g (fun _ => g ω) (historySet vm r (vm.ξ r ω)) := by
      intro ω' hω'
      have hξ : vm.ξ r ω' = vm.ξ r ω := hω'
      show g ω' = g ω
      simp only [hg_def]; rw [hξ]
    have hgB : ∫ ω' in historySet vm r (vm.ξ r ω), g ω' ∂vm.μ
        = ((vm.μ : Measure _) (historySet vm r (vm.ξ r ω))).toReal * g ω := by
      rw [setIntegral_congr_fun hBμ hg_const, setIntegral_const, measureReal_def, smul_eq_mul]
    have hXqB : ∫ ω' in historySet vm r (vm.ξ r ω), vm.Xq q (r + K) ω' ∂vm.μ
        = ((vm.μ : Measure _) (historySet vm r (vm.ξ r ω) ∩
            {ω | ¬ (VoterModel.phiQ q (vm.ξ (r + K) ω) = (∅ : Finset V) ∨
                    VoterModel.phiQ q (vm.ξ (r + K) ω) = Finset.univ)})).toReal := by
      simp only [hXq_ind]
      rw [setIntegral_indicator hEsetm, setIntegral_const, measureReal_def, smul_eq_mul, mul_one]
    have hcombine : ((vm.μ : Measure _) (historySet vm r (vm.ξ r ω))).toReal * g ω
        = ((vm.μ : Measure _) (historySet vm r (vm.ξ r ω) ∩
            {ω | ¬ (VoterModel.phiQ q (vm.ξ (r + K) ω) = (∅ : Finset V) ∨
                    VoterModel.phiQ q (vm.ξ (r + K) ω) = Finset.univ)})).toReal := by
      rw [← hgB, ← hXqB]; exact hLeq _ hBF
    have hμBne : ((vm.μ : Measure _) (historySet vm r (vm.ξ r ω))).toReal ≠ 0 :=
      ENNReal.toReal_ne_zero.mpr ⟨hμB0, hμBtop⟩
    have hcondReal : (ProbabilityTheory.cond vm.μ (historySet vm r (vm.ξ r ω))
          {ω | ¬ (VoterModel.phiQ q (vm.ξ (r + K) ω) = (∅ : Finset V) ∨
                  VoterModel.phiQ q (vm.ξ (r + K) ω) = Finset.univ)}).toReal = g ω := by
      rw [ProbabilityTheory.cond_apply hBμ, ENNReal.toReal_mul, ENNReal.toReal_inv,
        ← hcombine, ← mul_assoc, inv_mul_cancel₀ hμBne, one_mul]
    -- Conclude via the claim.
    rw [show g ω = (ProbabilityTheory.cond vm.μ (historySet vm r (vm.ξ r ω))
          {ω | ¬ (VoterModel.phiQ q (vm.ξ (r + K) ω) = (∅ : Finset V) ∨
                  VoterModel.phiQ q (vm.ξ (r + K) ω) = Finset.univ)}).toReal from hcondReal.symm]
    calc (ProbabilityTheory.cond vm.μ (historySet vm r (vm.ξ r ω))
            {ω | ¬ (VoterModel.phiQ q (vm.ξ (r + K) ω) = (∅ : Finset V) ∨
                    VoterModel.phiQ q (vm.ξ (r + K) ω) = Finset.univ)}).toReal
        ≤ ((1 : ℝ≥0∞) / 2).toReal := ENNReal.toReal_mono (by simp) hclaim
      _ = (1 / 2 : ℝ) := by rw [ENNReal.toReal_div]; simp
  -- Combine: `condExp =ᵐ g ≤ᵐ 1/2` on `E_r`.
  have hrestr : (vm.μ : Measure Ω)[vm.Xq q (r + K) | (vm.ℱ r : MeasurableSpace Ω)]
      =ᵐ[(vm.μ : Measure Ω).restrict E_r] g :=
    ae_restrict_of_ae hcond_eq.symm
  exact hrestr.le.trans hbound

end TemporalGraph
