module

import UpperBound.MultiOpinion.Markov
public import VoterProcess.Shift
public import VoterProcess.TwoOpinion
public import VoterProcess.OpinionCoupling
public import VoterProcess.Absorption.Time
import UpperBound.TwoOpinion.Theorem

/-! ## §3.4 multi-opinion reduction: the per-opinion two-opinion coupling

This file builds the two-opinion voter model obtained from the κ-opinion model
`vm : TemporalGraph.VoterModelAbstract G κ Ω` by:

1. restarting at a time `r` and conditioning on a pinned history-configuration
   `vm.ξ r = h`;
2. projecting onto a single opinion `q` via `phiQ q`.

The resulting object `coupledTwoOpinion` is a
`TemporalGraph.VoterModelAbstract (shift G r) ↥P`, where `P ⊆ Ω` is the
permanence-restricted subtype

  `P = {ω | vm.ξ r ω = h} ∩ {ω | (q-set permanence from r)}`.

**FORMALIZATION NOTE (Lean-specific).** The paper's §3.4 coupling is stated on the
event `{ξ_r = h}`. The Lean `VoterModel` structure carries a *pointwise*
field `hT_abs_permanent : ∀ ω t, T_abs ω ≤ t → minoritySet … = ∅`. For the
`q`-projection `A s ω = phiQ q (ξ_{r+s} ω)`, pointwise permanence of the `q`-set is
NOT derivable from an abstract κ-`VoterModel` (only `qset_persistent`, an a.s.
one-step statement, is available). We therefore intersect the conditioning event
with the a.s.-full permanence event, obtaining a subtype `P` of full
`cond`-measure. Because `P` is `cond`-full, `measure_comap_subtype_of_full`
recovers the conditional probabilities, so the final `claim_Xq_le_half` is stated
directly on `vm.μ[| {ξ_r = h}]` exactly as in the paper.

## Main results

- `coupledTwoOpinion` — the two-opinion model on `shift G r` over the subtype `P`.
- `coupledTwoOpinion_S0` — its initial minority set is deterministic.
- `q_absorb_half` — `voter_absorb_two_opinion` applied to `coupledTwoOpinion`.
- `claim_Xq_le_half` — the §3.4 small-opinion claim: conditioned on `ξ_r = h`,
  opinion `q` neither vanishes nor takes over within the deadline with prob `≤ 1/2`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Classical

noncomputable section

namespace TemporalGraph

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]

/-! ### Foundational helpers -/

/-- `minoritySet G t S = ∅ ↔ S = ∅ ∨ S = univ`, given fixed (positive) degrees so
that `Vol(univ) > 0`. Re-proved here (the original is `private` in
`CanonicalConstruction`). -/
theorem minoritySet_eq_empty_iff
    (G : TemporalGraphFixedDegree V)
    (t : ℕ) (S : Finset V) :
    VoterModel.minoritySet G.toTemporalGraph t S = ∅ ↔ S = ∅ ∨ S = Finset.univ := by
  unfold VoterModel.minoritySet
  have hVuniv_pos : 0 < TemporalGraph.volume G.toTemporalGraph t Finset.univ := by
    obtain ⟨v⟩ := ‹Nonempty V›
    have hdeg_pos : 0 < TemporalGraph.degree G.toTemporalGraph t v := G.degrees_pos v t
    have hdeg_le : TemporalGraph.degree G.toTemporalGraph t v ≤
        TemporalGraph.volume G.toTemporalGraph t Finset.univ := by
      simp only [TemporalGraph.volume, SimpleGraph.volume, TemporalGraph.degree]
      exact Finset.single_le_sum (f := fun u => (G.snapshot t).degree u)
        (fun u _ => Nat.zero_le _) (Finset.mem_univ v)
    exact lt_of_lt_of_le hdeg_pos hdeg_le
  constructor
  · intro h
    split_ifs at h with hvol
    · left; exact h
    · right
      have : ∀ x, x ∈ S := by
        intro x
        by_contra hxS
        have hx_mem : x ∈ Finset.univ \ S := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxS⟩
        rw [h] at hx_mem
        exact Finset.notMem_empty _ hx_mem
      exact Finset.eq_univ_of_forall this
  · rintro (rfl | rfl)
    · have hcond_true :
          TemporalGraph.volume G.toTemporalGraph t (∅ : Finset V) ≤
          TemporalGraph.volume G.toTemporalGraph t (Finset.univ \ ∅) := by
        simp [TemporalGraph.volume, SimpleGraph.volume]
      simp only [hcond_true, ite_true]
    · have h_emp_zero : TemporalGraph.volume G.toTemporalGraph t (∅ : Finset V) = 0 := by
        simp [TemporalGraph.volume, SimpleGraph.volume]
      rw [Finset.sdiff_self, h_emp_zero, if_neg (not_le.mpr hVuniv_pos)]

/-- Bridge lemma: for a full-measure subtype, the comap-measure of a preimage
equals the original measure of the set. (Re-proved; original is `private`.) -/
theorem measure_comap_subtype_of_full
    {α : Type*} [MeasurableSpace α] {s : Set α} (hs : MeasurableSet s)
    (μ : Measure α) (hfull : μ sᶜ = 0)
    (E : Set α) (hE : MeasurableSet E) :
    Measure.comap (Subtype.val : s → α) μ (Subtype.val ⁻¹' E) = μ E := by
  rw [comap_subtype_coe_apply hs]
  simp only [Subtype.image_preimage_coe]
  have hzeromeas : μ (sᶜ ∩ E) = 0 := by
    have hle : μ (sᶜ ∩ E) ≤ μ sᶜ := measure_mono Set.inter_subset_left
    rw [hfull] at hle
    exact le_antisymm hle zero_le
  have hdecomp : E = (s ∩ E) ∪ (sᶜ ∩ E) := by
    rw [← Set.union_inter_distrib_right, Set.union_compl_self, Set.univ_inter]
  conv_rhs => rw [hdecomp]
  rw [measure_union]
  · rw [hzeromeas, add_zero]
  · exact Set.disjoint_iff_inter_eq_empty.mpr (by ext x; simp; tauto)
  · exact hs.compl.inter hE


variable {κ : ℕ} [NeZero κ] {Ω : Type*} [mΩ : MeasurableSpace Ω] {G : TemporalGraph V}

/-! ### `q`-set absorption and permanence -/

/-- A.s. one-step permanence of the `q`-set's boundary states, shifted by `r`. -/
theorem phiQ_oneStepPerm_ae (G : TemporalGraph V) (vm : VoterModelAbstract G κ Ω) (q : Fin κ) (r : ℕ) :
    ∀ᵐ ω ∂(vm.μ : Measure Ω), ∀ s,
      (VoterModel.phiQ q (vm.ξ (r + s) ω) = ∅ →
        VoterModel.phiQ q (vm.ξ (r + (s + 1)) ω) = ∅) ∧
      (VoterModel.phiQ q (vm.ξ (r + s) ω) = univ →
        VoterModel.phiQ q (vm.ξ (r + (s + 1)) ω) = univ) := by
  rw [ae_all_iff]
  intro s
  exact (qset_persistent vm q (r + s)).1.and (qset_persistent vm q (r + s)).2

/-- One-step permanence implies full permanence: once absorbed, the `q`-set stays
absorbed at every later time. -/
theorem phiQ_perm_of_oneStep (G : TemporalGraph V) (vm : VoterModelAbstract G κ Ω) (q : Fin κ) (r : ℕ)
    {ω : Ω}
    (hone : ∀ s,
      (VoterModel.phiQ q (vm.ξ (r + s) ω) = ∅ →
        VoterModel.phiQ q (vm.ξ (r + (s + 1)) ω) = ∅) ∧
      (VoterModel.phiQ q (vm.ξ (r + s) ω) = univ →
        VoterModel.phiQ q (vm.ξ (r + (s + 1)) ω) = univ))
    {s t : ℕ} (hst : s ≤ t)
    (habs : VoterModel.phiQ q (vm.ξ (r + s) ω) = ∅ ∨
            VoterModel.phiQ q (vm.ξ (r + s) ω) = univ) :
    VoterModel.phiQ q (vm.ξ (r + t) ω) = ∅ ∨
    VoterModel.phiQ q (vm.ξ (r + t) ω) = univ := by
  induction t, hst using Nat.le_induction with
  | base => exact habs
  | succ t _ ih =>
    rcases ih with h0 | h1
    · exact Or.inl ((hone t).1 h0)
    · exact Or.inr ((hone t).2 h1)

/-! ### The conditioning event, permanence event, and coupled subtype `P` -/

/-- The conditioning event `{ω | ξ_r ω = h}`. -/
def historySet (vm : VoterModelAbstract G κ Ω) (r : ℕ) (h : V → Fin κ) : Set Ω :=
  {ω | vm.ξ r ω = h}

/-- The (a.s.-full) `q`-set one-step permanence event, shifted by `r`. -/
def permSet (vm : VoterModelAbstract G κ Ω) (q : Fin κ) (r : ℕ) : Set Ω :=
  {ω | ∀ s,
    (VoterModel.phiQ q (vm.ξ (r + s) ω) = ∅ →
      VoterModel.phiQ q (vm.ξ (r + (s + 1)) ω) = ∅) ∧
    (VoterModel.phiQ q (vm.ξ (r + s) ω) = univ →
      VoterModel.phiQ q (vm.ξ (r + (s + 1)) ω) = univ)}

/-- The coupled subtype `P = {ξ_r = h} ∩ (q-permanence)`. -/
def coupledSubtype (vm : VoterModelAbstract G κ Ω) (q : Fin κ) (r : ℕ) (h : V → Fin κ) : Set Ω :=
  historySet vm r h ∩ permSet vm q r

theorem historySet_meas (vm : VoterModelAbstract G κ Ω) (r : ℕ) (h : V → Fin κ) :
    MeasurableSet (historySet vm r h) :=
  xiK_eq_measurable vm r h

theorem permSet_meas (vm : VoterModelAbstract G κ Ω) (q : Fin κ) (r : ℕ) :
    MeasurableSet (permSet vm q r) := by
  have hmeas : ∀ (j : ℕ) (T : Finset V),
      MeasurableSet {ω : Ω | VoterModel.phiQ q (vm.ξ j ω) = T} :=
    fun j T => xiK_eq_measurable_phiQ vm j q T
  have hrw : permSet vm q r = ⋂ s : ℕ,
      (({ω | VoterModel.phiQ q (vm.ξ (r + s) ω) = ∅}ᶜ ∪
        {ω | VoterModel.phiQ q (vm.ξ (r + (s + 1)) ω) = ∅}) ∩
       ({ω | VoterModel.phiQ q (vm.ξ (r + s) ω) = univ}ᶜ ∪
        {ω | VoterModel.phiQ q (vm.ξ (r + (s + 1)) ω) = univ})) := by
    ext ω
    simp only [permSet, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff, Set.mem_union,
      Set.mem_compl_iff, imp_iff_not_or]
  rw [hrw]
  exact MeasurableSet.iInter fun s =>
    ((hmeas (r + s) ∅).compl.union (hmeas (r + (s + 1)) ∅)).inter
      ((hmeas (r + s) univ).compl.union (hmeas (r + (s + 1)) univ))

theorem coupledSubtype_meas (vm : VoterModelAbstract G κ Ω) (q : Fin κ) (r : ℕ) (h : V → Fin κ) :
    MeasurableSet (coupledSubtype vm q r h) :=
  (historySet_meas vm r h).inter (permSet_meas vm q r)

/-- The coupled subtype has full `cond`-measure: `cond Pᶜ = 0`. -/
theorem cond_coupledSubtype_compl_zero (vm : VoterModelAbstract G κ Ω) (q : Fin κ) (r : ℕ)
    (h : V → Fin κ) :
    (ProbabilityTheory.cond vm.μ (historySet vm r h)) (coupledSubtype vm q r h)ᶜ = 0 := by
  have hE_meas : MeasurableSet (historySet vm r h) := historySet_meas vm r h
  have hperm0 : (vm.μ : Measure Ω) (permSet vm q r)ᶜ = 0 :=
    ae_iff.mp (phiQ_oneStepPerm_ae G vm q r)
  have hcondE : (ProbabilityTheory.cond vm.μ (historySet vm r h)) (historySet vm r h)ᶜ = 0 := by
    rw [ProbabilityTheory.cond_apply hE_meas, Set.inter_compl_self, measure_empty, mul_zero]
  have hcondP : (ProbabilityTheory.cond vm.μ (historySet vm r h)) (permSet vm q r)ᶜ = 0 := by
    rw [ProbabilityTheory.cond_apply hE_meas]
    have hz : (vm.μ : Measure Ω) (historySet vm r h ∩ (permSet vm q r)ᶜ) = 0 :=
      le_antisymm (le_trans (measure_mono Set.inter_subset_right) (le_of_eq hperm0)) bot_le
    rw [hz, mul_zero]
  show (ProbabilityTheory.cond vm.μ (historySet vm r h))
      (historySet vm r h ∩ permSet vm q r)ᶜ = 0
  rw [Set.compl_inter]
  refine le_antisymm (le_trans (measure_union_le _ _) ?_) bot_le
  rw [hcondE, hcondP, add_zero]

/-! ### The subtype filtration is coarser than the shifted ambient filtration -/

theorem coupled_filtration_le (vm : VoterModelAbstract G κ Ω) (q : Fin κ) (r : ℕ) (h : V → Fin κ)
    (t : ℕ) :
    (⨆ j ∈ Finset.Iic t, MeasurableSpace.comap
        (fun ω' : ↥(coupledSubtype vm q r h) => VoterModel.phiQ q (vm.ξ (r + j) ω'.val)) ⊤)
      ≤ MeasurableSpace.comap (Subtype.val : ↥(coupledSubtype vm q r h) → Ω) (vm.ℱ (r + t)) := by
  apply iSup₂_le
  intro j hj
  rw [show (fun ω' : ↥(coupledSubtype vm q r h) => VoterModel.phiQ q (vm.ξ (r + j) ω'.val))
        = (VoterModel.phiQ q ∘ vm.ξ (r + j)) ∘ Subtype.val from rfl,
      ← MeasurableSpace.comap_comp]
  refine MeasurableSpace.comap_mono ?_
  rw [← MeasurableSpace.comap_comp]
  refine le_trans (MeasurableSpace.comap_mono le_top) ?_
  have hj' : r + j ≤ r + t := by have := Finset.mem_Iic.mp hj; omega
  exact le_iSup₂_of_le (r + j) (Finset.mem_Iic.mpr hj') le_rfl

/-! ### The conditional Markov property of the coupled model -/

theorem coupled_markovProperty (vm : VoterModelAbstract G κ Ω) (q : Fin κ) (r : ℕ) (h : V → Fin κ)
    (t : ℕ) (S' : Finset V) (B' : Set ↥(coupledSubtype vm q r h))
    (hB' : @MeasurableSet ↥(coupledSubtype vm q r h)
      (⨆ j ∈ Finset.Iic t, MeasurableSpace.comap
        (fun ω' : ↥(coupledSubtype vm q r h) =>
          VoterModel.phiQ q (vm.ξ (r + j) ω'.val)) ⊤) B') :
    (Measure.comap Subtype.val (ProbabilityTheory.cond vm.μ (historySet vm r h)))
      (B' ∩ {ω' | VoterModel.phiQ q (vm.ξ (r + (t + 1)) ω'.val) = S'}) =
    ∫⁻ ω' in B', (VoterModel.stepDist₂ (shift G r) t
        (VoterModel.phiQ q (vm.ξ (r + t) ω'.val))) S'
      ∂(Measure.comap Subtype.val (ProbabilityTheory.cond vm.μ (historySet vm r h))) := by
  have hP : MeasurableSet (coupledSubtype vm q r h) := coupledSubtype_meas vm q r h
  have hE : MeasurableSet (historySet vm r h) := historySet_meas vm r h
  have hfull := cond_coupledSubtype_compl_zero vm q r h
  have hperm0 : (vm.μ : Measure Ω) (permSet vm q r)ᶜ = 0 := ae_iff.mp (phiQ_oneStepPerm_ae G vm q r)
  -- extract the ambient generator `u` of `B'`
  have hB'' : @MeasurableSet _ (MeasurableSpace.comap Subtype.val (vm.ℱ (r + t))) B' :=
    coupled_filtration_le vm q r h t _ hB'
  rw [MeasurableSpace.measurableSet_comap] at hB''
  obtain ⟨u, hu_meas, hu_eq⟩ := hB''
  have hu_mΩ : MeasurableSet u := vm.ℱ.le (r + t) u hu_meas
  set U_S1 : Set Ω := {ω | VoterModel.phiQ q (vm.ξ (r + (t + 1)) ω) = S'} with hUS1
  have hU_S1_meas : MeasurableSet U_S1 := xiK_eq_measurable_phiQ vm (r + (t + 1)) q S'
  -- `E`-measurability inside the filtration `ℱ_{r+t}`
  have hE_filt : @MeasurableSet Ω (vm.ℱ (r + t)) (historySet vm r h) := by
    have hsub_le : MeasurableSpace.comap (vm.ξ r) ⊤ ≤ (vm.ℱ (r + t) : MeasurableSpace Ω) :=
      le_iSup₂_of_le r (Finset.mem_Iic.mpr (by omega)) le_rfl
    exact hsub_le _ ⟨{h}, trivial, by ext ω; simp [historySet, Set.mem_preimage]⟩
  -- LHS rewritten as preimage and pushed through the full subtype
  have hLset : (B' ∩ {ω' | VoterModel.phiQ q (vm.ξ (r + (t + 1)) ω'.val) = S'})
      = Subtype.val ⁻¹' (u ∩ U_S1) := by
    rw [← hu_eq]; ext ω'
    simp only [Set.mem_inter_iff, Set.mem_preimage, hUS1, Set.mem_setOf_eq]
  -- push LHS through the full subtype, expand `cond`
  rw [hLset, measure_comap_subtype_of_full hP _ hfull _ (hu_mΩ.inter hU_S1_meas),
      ProbabilityTheory.cond_apply hE]
  rw [setLIntegral_subtype hP B'
      (fun ω => (VoterModel.stepDist₂ (shift G r) t (VoterModel.phiQ q (vm.ξ (r + t) ω))) S')]
  have hImg : Subtype.val '' B' = u ∩ coupledSubtype vm q r h := by
    rw [← hu_eq]
    ext ω
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨hx, x.property⟩
    · rintro ⟨hu, hPmem⟩; exact ⟨⟨ω, hPmem⟩, hu, rfl⟩
  rw [hImg, ProbabilityTheory.cond, setLIntegral_smul_measure, smul_eq_mul]
  congr 1
  -- reduce both sides over `μ`, dropping the restriction to `E`
  have hUP_meas : MeasurableSet (u ∩ coupledSubtype vm q r h) := hu_mΩ.inter hP
  have hUP_subE : u ∩ coupledSubtype vm q r h ⊆ historySet vm r h := by
    intro x hx
    have hx2 : x ∈ historySet vm r h ∧ x ∈ permSet vm q r := hx.2
    exact hx2.1
  rw [Measure.restrict_restrict hUP_meas, Set.inter_eq_left.mpr hUP_subE]
  -- remove the (full-measure) permanence factor from the integration region
  have hsub1 : u ∩ coupledSubtype vm q r h ⊆ u ∩ historySet vm r h := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    have hx2 : x ∈ historySet vm r h ∧ x ∈ permSet vm q r := hx.2
    exact hx2.1
  have hae : ((u ∩ coupledSubtype vm q r h : Set Ω)) =ᵐ[(vm.μ : Measure Ω)]
      ((u ∩ historySet vm r h : Set Ω)) := by
    rw [MeasureTheory.ae_eq_set]
    refine ⟨?_, ?_⟩
    · rw [Set.sdiff_eq_empty.mpr hsub1, measure_empty]
    · refine measure_mono_null (fun x hx => ?_) hperm0
      obtain ⟨⟨hxu, hxE⟩, hxnP⟩ := hx
      simp only [Set.mem_compl_iff]
      intro hxperm
      exact hxnP ⟨hxu, (⟨hxE, hxperm⟩ : x ∈ historySet vm r h ∧ x ∈ permSet vm q r)⟩
  rw [setLIntegral_congr hae]
  -- `opinionProcess₂ _ 1 = stepDist₂`, and the integrand transports across the shift
  have hop1 : ∀ X : Finset V,
      VoterModel.opinionProcess₂ G (r + t) 1 X = VoterModel.stepDist₂ G (r + t) X := by
    intro X
    show (VoterModel.opinionProcess₂ G (r + t) 0 X).bind
        (fun S => VoterModel.stepDist₂ G ((r + t) + 0) S) = _
    rw [show VoterModel.opinionProcess₂ G (r + t) 0 X = PMF.pure X from rfl,
        PMF.pure_bind, Nat.add_zero]
  have hf : ∀ X : Finset V,
      (VoterModel.stepDist₂ (shift G r) t X) S' = (VoterModel.opinionProcess₂ G (r + t) 1 X) S' := by
    intro X
    rw [hop1 X, VoterModel.stepDist₂_shift, show t + r = r + t from by omega]
  rw [setLIntegral_congr_fun (hu_mΩ.inter hE)
      (fun x _ => hf (VoterModel.phiQ q (vm.ξ (r + t) x)))]
  -- apply the one-step phiQ-Markov property and identify sets
  rw [← multistep_markov_phiQ G vm (r + t) 1 q S'
        (u ∩ historySet vm r h) (hu_meas.inter hE_filt)]
  congr 1
  ext ω
  constructor
  · rintro ⟨hxE, hxu, hxS⟩; exact ⟨⟨hxu, hxE⟩, hxS⟩
  · rintro ⟨⟨hxu, hxE⟩, hxS⟩; exact ⟨hxE, hxu, hxS⟩

/-! ### The coupled two-opinion model -/

/-- **The §3.4 coupling.** From the κ-opinion model `vm`, opinion `q`, restart time
`r`, and pinned history-configuration `h` (with `μ{ξ_r = h} ≠ 0`), build the standard
two-opinion voter model on the shifted graph `shift G r`, over the permanence-restricted
subtype `P = {ξ_r = h} ∩ (q-permanence)`, tracking the `q`-set `phiQ q (ξ_{r+·})`. -/
def coupledTwoOpinion (vm : VoterModelAbstract G κ Ω)
    (q : Fin κ) (r : ℕ) (h : V → Fin κ) (hpos : (vm.μ : Measure Ω) (historySet vm r h) ≠ 0) :
    VoterModelAbstract (shift G r) 2 ↥(coupledSubtype vm q r h) :=
  VoterModelAbstract.ofOpinionZeroData (G := shift G r)
    ⟨Measure.comap Subtype.val (ProbabilityTheory.cond vm.μ (historySet vm r h)), by
      have hP := coupledSubtype_meas vm q r h
      have hfull := cond_coupledSubtype_compl_zero vm q r h
      have hE := historySet_meas vm r h
      constructor
      show Measure.comap Subtype.val (ProbabilityTheory.cond vm.μ (historySet vm r h)) Set.univ = 1
      rw [show (Set.univ : Set ↥(coupledSubtype vm q r h)) = Subtype.val ⁻¹' Set.univ from rfl,
          measure_comap_subtype_of_full hP _ hfull Set.univ MeasurableSet.univ,
          ProbabilityTheory.cond_apply hE, Set.inter_univ]
      exact ENNReal.inv_mul_cancel hpos (measure_ne_top _ _)⟩
    (fun s ω' => VoterModel.phiQ q (vm.ξ (r + s) ω'.val))
    (fun s => by
      show MeasurableSpace.comap ((VoterModel.phiQ q ∘ vm.ξ (r + s)) ∘ Subtype.val) ⊤
          ≤ MeasurableSpace.comap Subtype.val mΩ
      rw [← MeasurableSpace.comap_comp]
      refine MeasurableSpace.comap_mono ?_
      rw [← MeasurableSpace.comap_comp]
      exact le_trans (MeasurableSpace.comap_mono le_top) (vm.hξ_meas (r + s)))
    (coupled_markovProperty vm q r h)

/-- The opinion-0 set of the coupled model is the tracked `q`-set. -/
@[simp] theorem coupledTwoOpinion_A (vm : VoterModelAbstract G κ Ω)
    (q : Fin κ) (r : ℕ) (h : V → Fin κ) (hpos : (vm.μ : Measure Ω) (historySet vm r h) ≠ 0)
    (s : ℕ) (ω' : ↥(coupledSubtype vm q r h)) :
    (coupledTwoOpinion vm q r h hpos).opinionZeroSet s ω' = VoterModel.phiQ q (vm.ξ (r + s) ω'.val) :=
  VoterModel.phiZero_phiZeroInv _

/-- The initial minority set of the coupled model is deterministic:
`S_0 ω = minoritySet (shift G r) 0 (phiQ q h)` for every `ω`. -/
theorem coupledTwoOpinion_S0 (vm : VoterModelAbstract G κ Ω)
    (q : Fin κ) (r : ℕ) (h : V → Fin κ) (hpos : (vm.μ : Measure Ω) (historySet vm r h) ≠ 0)
    (ω' : ↥(coupledSubtype vm q r h)) :
    (coupledTwoOpinion vm q r h hpos).S 0 ω' =
      VoterModel.minoritySet (shift G r) 0 (VoterModel.phiQ q h) := by
  have hh : vm.ξ r ω'.val = h := ω'.property.1
  show VoterModel.minoritySet (shift G r) 0 ((coupledTwoOpinion vm q r h hpos).opinionZeroSet 0 ω') = _
  rw [coupledTwoOpinion_A, Nat.add_zero, hh]

/-! ### Two-opinion absorption for the coupled model -/

/-- **Absorption of the coupled model.** Applying `voter_absorb_two_opinion` to
`coupledTwoOpinion`: under the §3.4 interval/threshold data for the shifted graph
(with deterministic initial minority set `s₀ = minoritySet (shift G r) 0 (phiQ q h)`),
with probability `≥ 1/2` the `q`-set is absorbed within the deadline. -/
theorem q_absorb_half (G : TemporalGraphFixedDegree V) (vm : G.VoterModelAbstract κ Ω)
    (q : Fin κ) (r : ℕ) (h : V → Fin κ) (hpos : (vm.μ : Measure Ω) (historySet vm r h) ≠ 0)
    (d_min : ℕ) (hd : d_min = (shift G.toTemporalGraph r).minDegreeAt 0) (hd_pos : 0 < d_min)
    (Δ : ℕ → ℕ) (hΔ_pos : ∀ j, 1 ≤ Δ j)
    (φ : ℕ → ℝ) (hφ_nn : ∀ j, 0 ≤ φ j) (hφ_le1 : ∀ j, φ j ≤ 1)
    (hwin : ∀ j, ∀ S ∈ TemporalGraph.admissibleCuts (shift G.toTemporalGraph r),
      φ j ≤ TemporalGraph.maxSetConductanceOnInterval (shift G.toTemporalGraph r)
        (∑ i ∈ Finset.range j, Δ i) (Δ j) S)
    (b : ℝ) (hb_large : (5462 : ℝ) ≤ b) (J : ℕ)
    (hJ : b * ((TemporalGraph.volume (shift G.toTemporalGraph r) 0
              (VoterModel.minoritySet (shift G.toTemporalGraph r) 0 (VoterModel.phiQ q h)) : ℝ) / d_min
            + Real.log (1 + (TemporalGraph.volume (shift G.toTemporalGraph r) 0
              (VoterModel.minoritySet (shift G.toTemporalGraph r) 0 (VoterModel.phiQ q h)) : ℝ)))
          ≤ ∑ ℓ ∈ Finset.range (J + 1), φ ℓ) :
    (1 / 2 : ℝ) ≤ (((coupledTwoOpinion vm q r h hpos).μ : Measure _)
        {ω' | (coupledTwoOpinion vm q r h hpos).absorptionTime ω' ≤
          (↑(∑ j ∈ Finset.range (J + 1), Δ j) : ℕ∞)}).toReal :=
  VoterModel.voter_absorb_two_opinion
    ((shift G.toTemporalGraph r).withFixed (FixedDegrees_shift G r))
    (coupledTwoOpinion vm q r h hpos) d_min hd hd_pos
    (VoterModel.minoritySet (shift G.toTemporalGraph r) 0 (VoterModel.phiQ q h))
    (coupledTwoOpinion_S0 vm q r h hpos)
    Δ hΔ_pos φ hφ_nn hφ_le1 hwin b hb_large J hJ

/-! ### The §3.4 small-opinion claim -/

/-- **`claim_Xq_le_half` (§3.4).** Conditioned on the history `ξ_r = h`, the
probability that opinion `q` neither vanishes nor takes over within the deadline
`K = Δ_0 + … + Δ_J` (i.e. `phiQ q (ξ_{r+K}) ∉ {∅, univ}`) is at most `1/2`.

This is the per-opinion bound `Pr(X_q = 1 ∣ ℋ_{t_r}) ≤ 1/2` of §3.4, obtained by
coupling to the two-opinion model `coupledTwoOpinion` and applying
`voter_absorb_two_opinion` (via `q_absorb_half`), then translating the absorption
event back through the conditioning and the permanence-restricted subtype. -/
theorem claim_Xq_le_half (G : TemporalGraphFixedDegree V) (vm : G.VoterModelAbstract κ Ω)
    (q : Fin κ) (r : ℕ) (h : V → Fin κ) (hpos : (vm.μ : Measure Ω) (historySet vm r h) ≠ 0)
    (d_min : ℕ) (hd : d_min = (shift G.toTemporalGraph r).minDegreeAt 0) (hd_pos : 0 < d_min)
    (Δ : ℕ → ℕ) (hΔ_pos : ∀ j, 1 ≤ Δ j)
    (φ : ℕ → ℝ) (hφ_nn : ∀ j, 0 ≤ φ j) (hφ_le1 : ∀ j, φ j ≤ 1)
    (hwin : ∀ j, ∀ S ∈ TemporalGraph.admissibleCuts (shift G.toTemporalGraph r),
      φ j ≤ TemporalGraph.maxSetConductanceOnInterval (shift G.toTemporalGraph r)
        (∑ i ∈ Finset.range j, Δ i) (Δ j) S)
    (b : ℝ) (hb_large : (5462 : ℝ) ≤ b) (J : ℕ)
    (hJ : b * ((TemporalGraph.volume (shift G.toTemporalGraph r) 0
              (VoterModel.minoritySet (shift G.toTemporalGraph r) 0 (VoterModel.phiQ q h)) : ℝ) / d_min
            + Real.log (1 + (TemporalGraph.volume (shift G.toTemporalGraph r) 0
              (VoterModel.minoritySet (shift G.toTemporalGraph r) 0 (VoterModel.phiQ q h)) : ℝ)))
          ≤ ∑ ℓ ∈ Finset.range (J + 1), φ ℓ) :
    (ProbabilityTheory.cond vm.μ (historySet vm r h))
        {ω | ¬ (VoterModel.phiQ q (vm.ξ (r + ∑ j ∈ Finset.range (J + 1), Δ j) ω) = ∅ ∨
                VoterModel.phiQ q (vm.ξ (r + ∑ j ∈ Finset.range (J + 1), Δ j) ω) = univ)}
      ≤ 1 / 2 := by
  set K := ∑ j ∈ Finset.range (J + 1), Δ j with hK
  set Wabs : Set Ω :=
    {ω | VoterModel.phiQ q (vm.ξ (r + K) ω) = ∅ ∨ VoterModel.phiQ q (vm.ξ (r + K) ω) = univ}
    with hWabs
  have hWabs_meas : MeasurableSet Wabs :=
    (xiK_eq_measurable_phiQ vm (r + K) q ∅).union (xiK_eq_measurable_phiQ vm (r + K) q univ)
  have hP := coupledSubtype_meas vm q r h
  have hfull := cond_coupledSubtype_compl_zero vm q r h
  haveI : IsProbabilityMeasure (ProbabilityTheory.cond vm.μ (historySet vm r h)) :=
    ProbabilityTheory.cond_isProbabilityMeasure hpos
  -- absorption event corresponds to the `q`-set boundary event
  have hset : {ω' : ↥(coupledSubtype vm q r h) |
        (coupledTwoOpinion vm q r h hpos).absorptionTime ω' ≤ (↑K : ℕ∞)}
      = Subtype.val ⁻¹' Wabs := by
    ext ω'
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hWabs]
    rw [(coupledTwoOpinion vm q r h hpos).absorptionTime_le_coe_iff_exists ω' K]
    simp only [coupledTwoOpinion_A]
    constructor
    · rintro ⟨t, htK, ht⟩
      rw [minoritySet_eq_empty_iff
        ((shift G.toTemporalGraph r).withFixed (FixedDegrees_shift G r))] at ht
      exact phiQ_perm_of_oneStep G.toTemporalGraph vm q r ω'.property.2 htK ht
    · intro hmem
      exact ⟨K, le_refl K,
        (minoritySet_eq_empty_iff
          ((shift G.toTemporalGraph r).withFixed (FixedDegrees_shift G r)) _ _).mpr hmem⟩
  have hμ'eq : (((coupledTwoOpinion vm q r h hpos).μ : Measure _)
        {ω' | (coupledTwoOpinion vm q r h hpos).absorptionTime ω' ≤ (↑K : ℕ∞)}).toReal
      = (ProbabilityTheory.cond vm.μ (historySet vm r h) Wabs).toReal := by
    congr 1
    show Measure.comap Subtype.val (ProbabilityTheory.cond vm.μ (historySet vm r h))
        {ω' | (coupledTwoOpinion vm q r h hpos).absorptionTime ω' ≤ (↑K : ℕ∞)} = _
    rw [hset, measure_comap_subtype_of_full hP _ hfull Wabs hWabs_meas]
  have hbound := q_absorb_half G vm q r h hpos d_min hd hd_pos Δ hΔ_pos φ hφ_nn hφ_le1
    hwin b hb_large J hJ
  rw [hμ'eq] at hbound
  -- (1/2 : ENNReal) ≤ cond Wabs
  have hne : ProbabilityTheory.cond vm.μ (historySet vm r h) Wabs ≠ ⊤ := measure_ne_top _ _
  have hof : ENNReal.ofReal (1 / 2) = (1 / 2 : ENNReal) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one]
    simp
  have hge : (1 / 2 : ENNReal) ≤ ProbabilityTheory.cond vm.μ (historySet vm r h) Wabs := by
    rw [← hof]
    exact (ENNReal.ofReal_le_iff_le_toReal hne).mpr hbound
  -- complement
  have hcompl : {ω | ¬ (VoterModel.phiQ q (vm.ξ (r + K) ω) = ∅ ∨
      VoterModel.phiQ q (vm.ξ (r + K) ω) = univ)} = Wabsᶜ := by
    ext ω; simp only [hWabs, Set.mem_compl_iff, Set.mem_setOf_eq]
  rw [hcompl, measure_compl hWabs_meas hne, measure_univ]
  calc (1 : ENNReal) - ProbabilityTheory.cond vm.μ (historySet vm r h) Wabs
      ≤ 1 - 1 / 2 := tsub_le_tsub_left hge 1
    _ = 1 / 2 := ENNReal.sub_eq_of_eq_add (by simp) (ENNReal.add_halves 1).symm

end TemporalGraph
