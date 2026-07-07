module

import LowerBound.CliqueIndependence
import LowerBound.ArcDecomposition
import VoterProcess.DeterministicFiber
import Probability.Preliminaries
import VoterProcess.TwoOpinion
import LowerBound.Absorbing
import VoterProcess.Expectation
import Mathlib.Algebra.Order.Star.Real

public import LowerBound.Absorption.Defs
import LowerBound.Absorption.SeamCases

/-! ## Main results

The boundary filtration, `boundaryDelta` conditional-expectation and
martingale structure of `boundaryDeltaProcess`, the Azuma exponential
bound, and `blockCount_good_azuma_bound` / `blockCount_absorbed_ub`. -/

public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

namespace TemporalGraph.VoterProcess.LowerBound

/-- First interval index at which the arc invariant fails; `⊤` if arc holds forever.
Equal to `inf {j : WithTop ℕ | j ≠ ⊤ ∧ ¬IsContiguousArc at j·T ω}`. -/
noncomputable def arcFailTime (p : Params) {Ω : Type} [MeasurableSpace Ω]
    (vm : TemporalGraph.VoterModelAbstract (lowerBoundGraph p) 2 Ω) (ω : Ω) : WithTop ℕ :=
  sInf {j : WithTop ℕ | j ≠ ⊤ ∧ ¬IsContiguousArc p (vm.opinionZeroSet (j.getD 0 * p.T) ω)}

/-- Filtration at boundary times `j·T`, pulled back from `vm.ℱ`. -/
noncomputable def boundaryFiltration (p : Params) {Ω : Type} [MeasurableSpace Ω]
    (vm : TemporalGraph.VoterModelAbstract (lowerBoundGraph p) 2 Ω) :
    MeasureTheory.Filtration ℕ (inferInstance : MeasurableSpace Ω) where
  seq j := vm.ℱ (j * p.T)
  mono' {_ _} hij := vm.ℱ.mono (Nat.mul_le_mul_right p.T hij)
  le' j := vm.ℱ.le (j * p.T)


/-- Strong consensus preservation: if `seam(a) ⊆ S` then `seam(a) ⊆ S'`. -/
private theorem opinionProcess₂_seam_subset_preserved (p : Params) (a : Fin p.z)
    (j : ℕ) (ha : a.val % 2 = j % 2) (S S' : Finset (VertexSet p))
    (hsub : block p a ∪ block p (a + 1) ⊆ S)
    (hop : VoterModel.opinionProcess₂ (lowerBoundGraph p) (j * p.T) p.T S S' ≠ 0) :
    block p a ∪ block p (a + 1) ⊆ S' := by
  -- Use opinionProcess₂_clique_marginal: cliqueRestrict a S = univ → cliqueRestrict a S' = univ.
  have hres_S : cliqueRestrict p a S = (Finset.univ : Finset (CliqueVertex p.k)) := by
    have h_iff := (cliqueFinset_consensus_iff p a S).mp (Or.inl hsub)
    rcases h_iff with huniv | hempty
    · exact huniv
    · exfalso
      have hblock_a_nonempty : (block p a).Nonempty := by
        have := card_block p a
        exact Finset.card_pos.mp (this ▸ p.hk_pos)
      obtain ⟨w, hw⟩ := hblock_a_nonempty
      have hw_seam : w ∈ block p a ∪ block p (a + 1) := Finset.mem_union_left _ hw
      have hw_S : w ∈ S := hsub hw_seam
      have hw_in : toCliqueVtx p a w ∈ cliqueRestrict p a S :=
        (mem_cliqueRestrict_iff p a S w hw_seam).mpr hw_S
      rw [hempty] at hw_in
      exact (Finset.notMem_empty _) hw_in
  have hmarg := opinionProcess₂_clique_marginal p a j p.T (le_refl _) ha S
  have hmap_ne : (VoterModel.opinionProcess₂ (lowerBoundGraph p) (j * p.T) p.T S).map
      (cliqueRestrict p a) (cliqueRestrict p a S') ≠ 0 := by
    rw [PMF.map_apply]
    apply ne_of_gt
    have hpos : 0 < VoterModel.opinionProcess₂ (lowerBoundGraph p) (j * p.T) p.T S S' :=
      lt_of_le_of_ne zero_le (Ne.symm hop)
    refine lt_of_lt_of_le hpos ?_
    have hle := ENNReal.le_tsum
      (f := fun a_1 => if cliqueRestrict p a S' = cliqueRestrict p a a_1 then
          VoterModel.opinionProcess₂ (lowerBoundGraph p) (j * p.T) p.T S a_1 else 0) S'
    simp only [if_true] at hle; refine hle.trans (le_of_eq ?_); congr 1; ext; split_ifs <;> rfl
  rw [hmarg, hres_S, opinionProcess₂_univ_eq_pure, PMF.pure_apply] at hmap_ne
  split_ifs at hmap_ne with hcr
  · -- cliqueRestrict a S' = univ. So all of cliqueFinset a ⊆ S'.
    -- hcr : Finset.univ = cliqueRestrict p a S' (from pure_apply if-then-else).
    intro v hv
    have hcr' : cliqueRestrict p a S' = Finset.univ := hcr
    rcases (cliqueFinset_consensus_iff p a S').mpr (Or.inl hcr') with huniv | hempty
    · exact huniv hv
    · -- disjoint(seam, S'), contradicts seam ⊆ S' (need block a non-empty).
      exfalso
      have hblock_a_nonempty : (block p a).Nonempty := by
        have := card_block p a
        exact Finset.card_pos.mp (this ▸ p.hk_pos)
      obtain ⟨w, hw⟩ := hblock_a_nonempty
      have hw_seam : w ∈ block p a ∪ block p (a + 1) := Finset.mem_union_left _ hw
      have hw_S' : w ∈ S' := by
        have hin : toCliqueVtx p a w ∈ cliqueRestrict p a S' := by
          rw [hcr']; exact Finset.mem_univ _
        exact (mem_cliqueRestrict_iff p a S' w hw_seam).mp hin
      exact Finset.disjoint_left.mp hempty hw_seam hw_S'
  · exact absurd rfl hmap_ne

/-- Strong consensus preservation: if `seam(a)` disjoint from `S` then `seam(a)` disjoint from `S'`. -/
private theorem opinionProcess₂_seam_disjoint_preserved (p : Params) (a : Fin p.z)
    (j : ℕ) (ha : a.val % 2 = j % 2) (S S' : Finset (VertexSet p))
    (hdisj : Disjoint (block p a ∪ block p (a + 1)) S)
    (hop : VoterModel.opinionProcess₂ (lowerBoundGraph p) (j * p.T) p.T S S' ≠ 0) :
    Disjoint (block p a ∪ block p (a + 1)) S' := by
  have hres_S : cliqueRestrict p a S = (∅ : Finset (CliqueVertex p.k)) := by
    have h_iff := (cliqueFinset_consensus_iff p a S).mp (Or.inr hdisj)
    rcases h_iff with huniv | hempty
    · exfalso
      have hblock_a_nonempty : (block p a).Nonempty := by
        have := card_block p a
        exact Finset.card_pos.mp (this ▸ p.hk_pos)
      obtain ⟨w, hw⟩ := hblock_a_nonempty
      have hw_seam : w ∈ block p a ∪ block p (a + 1) := Finset.mem_union_left _ hw
      have hw_nS : w ∉ S := fun hw_S => Finset.disjoint_left.mp hdisj hw_seam hw_S
      have hw_in_univ : toCliqueVtx p a w ∈ cliqueRestrict p a S := by
        rw [huniv]; exact Finset.mem_univ _
      have hw_S : w ∈ S := (mem_cliqueRestrict_iff p a S w hw_seam).mp hw_in_univ
      exact hw_nS hw_S
    · exact hempty
  have hmarg := opinionProcess₂_clique_marginal p a j p.T (le_refl _) ha S
  have hmap_ne : (VoterModel.opinionProcess₂ (lowerBoundGraph p) (j * p.T) p.T S).map
      (cliqueRestrict p a) (cliqueRestrict p a S') ≠ 0 := by
    rw [PMF.map_apply]
    apply ne_of_gt
    have hpos : 0 < VoterModel.opinionProcess₂ (lowerBoundGraph p) (j * p.T) p.T S S' :=
      lt_of_le_of_ne zero_le (Ne.symm hop)
    refine lt_of_lt_of_le hpos ?_
    have hle := ENNReal.le_tsum
      (f := fun a_1 => if cliqueRestrict p a S' = cliqueRestrict p a a_1 then
          VoterModel.opinionProcess₂ (lowerBoundGraph p) (j * p.T) p.T S a_1 else 0) S'
    simp only [if_true] at hle; refine hle.trans (le_of_eq ?_); congr 1; ext; split_ifs <;> rfl
  rw [hmarg, hres_S, opinionProcess₂_empty_eq_pure, PMF.pure_apply] at hmap_ne
  split_ifs at hmap_ne with hcr
  · -- cliqueRestrict a S' = ∅. So all of cliqueFinset a is disjoint from S'.
    have hcr' : cliqueRestrict p a S' = ∅ := hcr
    rcases (cliqueFinset_consensus_iff p a S').mpr (Or.inr hcr') with huniv | hempty
    · -- seam ⊆ S', then cliqueRestrict ≠ ∅.
      exfalso
      have hblock_a_nonempty : (block p a).Nonempty := by
        have := card_block p a
        exact Finset.card_pos.mp (this ▸ p.hk_pos)
      obtain ⟨w, hw⟩ := hblock_a_nonempty
      have hw_seam : w ∈ block p a ∪ block p (a + 1) := Finset.mem_union_left _ hw
      have hw_S' : w ∈ S' := huniv hw_seam
      have hw_in : toCliqueVtx p a w ∈ cliqueRestrict p a S' :=
        (mem_cliqueRestrict_iff p a S' w hw_seam).mpr hw_S'
      rw [hcr'] at hw_in
      exact (Finset.notMem_empty _) hw_in
    · exact hempty
  · exact absurd rfl hmap_ne


/-- Auxiliary iff: `block p a ⊆ S' ∧ block p (a+1) ⊆ S' ↔ cliqueRestrict p a S' = univ`.

Holds for any `S'` (no contiguity assumption needed). Follows from
`cliqueFinset_consensus_iff` together with the fact that `cliqueRestrict = univ`
forces every clique vertex into `S'`. -/
private theorem block_pair_subset_iff_cliqueRestrict_univ (p : Params) (a : Fin p.z)
    (S' : Finset (VertexSet p)) :
    (block p a ⊆ S' ∧ block p (a + 1) ⊆ S') ↔
      cliqueRestrict p a S' = (Finset.univ : Finset (CliqueVertex p.k)) := by
  constructor
  · rintro ⟨hba, hba1⟩
    have hsub : block p a ∪ block p (a + 1) ⊆ S' := Finset.union_subset hba hba1
    have h_iff := (cliqueFinset_consensus_iff p a S').mp (Or.inl hsub)
    rcases h_iff with huniv | hempty
    · exact huniv
    · exfalso
      have hblock_a_nonempty : (block p a).Nonempty := by
        have := card_block p a
        exact Finset.card_pos.mp (this ▸ p.hk_pos)
      obtain ⟨w, hw⟩ := hblock_a_nonempty
      have hw_seam : w ∈ block p a ∪ block p (a + 1) := Finset.mem_union_left _ hw
      have hw_S' : w ∈ S' := hba hw
      have hw_in : toCliqueVtx p a w ∈ cliqueRestrict p a S' :=
        (mem_cliqueRestrict_iff p a S' w hw_seam).mpr hw_S'
      rw [hempty] at hw_in
      exact (Finset.notMem_empty _) hw_in
  · intro huniv
    -- cliqueRestrict = univ ⟹ every v ∈ cliqueFinset p a lies in S'.
    have hall : ∀ v ∈ cliqueFinset p a, v ∈ S' := by
      intro v hv
      have : toCliqueVtx p a v ∈ cliqueRestrict p a S' := by
        rw [huniv]; exact Finset.mem_univ _
      exact (mem_cliqueRestrict_iff p a S' v hv).mp this
    refine ⟨?_, ?_⟩
    · intro v hv
      exact hall v (Finset.mem_union_left _ hv)
    · intro v hv
      exact hall v (Finset.mem_union_right _ hv)

/-- Auxiliary iff, contiguous case: for `S'` a contiguous arc,
`¬ block p a ⊆ S' ∧ ¬ block p (a+1) ⊆ S' ↔ cliqueRestrict p a S' = ∅`.

Crucially uses `IsContiguousArc p S'` to convert "block c ⊄ S'" to
"block c disjoint from S'" via block-alignment. -/
private theorem not_block_pair_subset_iff_cliqueRestrict_empty_of_contig
    (p : Params) (a : Fin p.z) (S' : Finset (VertexSet p))
    (hS' : IsContiguousArc p S') :
    (¬ block p a ⊆ S' ∧ ¬ block p (a + 1) ⊆ S') ↔
      cliqueRestrict p a S' = (∅ : Finset (CliqueVertex p.k)) := by
  -- Block-aligned dichotomy for contig S': each block is ⊆ S' or disjoint.
  have hblock_align : ∀ c : Fin p.z, block p c ⊆ S' ∨ Disjoint (block p c) S' := by
    intro c
    obtain ⟨b, m, hm_le, hS'_eq⟩ := hS'
    rw [hS'_eq]
    classical
    by_cases hc_in : ∃ i ∈ Finset.range m,
        c = ⟨(b.val + i) % p.z, Nat.mod_lt _ p.hz_pos⟩
    · left
      obtain ⟨i, hi_range, hc_eq⟩ := hc_in
      intro v hv
      rw [Finset.mem_biUnion]
      exact ⟨i, hi_range, hc_eq ▸ hv⟩
    · right
      rw [Finset.disjoint_right]
      intro v hv hv_blockc
      rw [Finset.mem_biUnion] at hv
      obtain ⟨i, hi_range, hv_block⟩ := hv
      apply hc_in
      refine ⟨i, hi_range, ?_⟩
      rw [mem_block] at hv_blockc hv_block
      rw [← hv_blockc, hv_block]
  have hk_pos : 0 < p.k := p.hk_pos
  have h_block_nonempty : ∀ c : Fin p.z, (block p c).Nonempty := fun c =>
    Finset.card_pos.mp ((card_block p c).symm ▸ hk_pos)
  have h_nsub_iff_disj : ∀ c : Fin p.z, ¬ block p c ⊆ S' ↔ Disjoint (block p c) S' := by
    intro c
    constructor
    · intro hns
      rcases hblock_align c with hin | hdisj
      · exact absurd hin hns
      · exact hdisj
    · intro hdisj hsub
      obtain ⟨v, hv⟩ := h_block_nonempty c
      exact (Finset.disjoint_left.mp hdisj hv) (hsub hv)
  constructor
  · rintro ⟨hna, hna1⟩
    have hda := (h_nsub_iff_disj a).mp hna
    have hda1 := (h_nsub_iff_disj (a + 1)).mp hna1
    have hdisj_union : Disjoint (block p a ∪ block p (a + 1)) S' := by
      rw [Finset.disjoint_union_left]; exact ⟨hda, hda1⟩
    rcases (cliqueFinset_consensus_iff p a S').mp (Or.inr hdisj_union) with huniv | hempty
    · -- cliqueRestrict = univ ⟹ some clique vertex in S' — contradiction with disjoint.
      exfalso
      obtain ⟨w, hw⟩ := h_block_nonempty a
      have hw_seam : w ∈ cliqueFinset p a := Finset.mem_union_left _ hw
      have : toCliqueVtx p a w ∈ cliqueRestrict p a S' := by
        rw [huniv]; exact Finset.mem_univ _
      have hwS' : w ∈ S' := (mem_cliqueRestrict_iff p a S' w hw_seam).mp this
      exact (Finset.disjoint_left.mp hda hw) hwS'
    · exact hempty
  · intro hempty
    -- cliqueRestrict = ∅ ⟹ no v ∈ cliqueFinset a lies in S'.
    have hnone : ∀ v ∈ cliqueFinset p a, v ∉ S' := by
      intro v hv hvS'
      have : toCliqueVtx p a v ∈ cliqueRestrict p a S' :=
        (mem_cliqueRestrict_iff p a S' v hv).mpr hvS'
      rw [hempty] at this
      exact (Finset.notMem_empty _) this
    refine ⟨?_, ?_⟩
    · intro hsub
      obtain ⟨v, hv⟩ := h_block_nonempty a
      exact hnone v (Finset.mem_union_left _ hv) (hsub hv)
    · intro hsub
      obtain ⟨v, hv⟩ := h_block_nonempty (a + 1)
      exact hnone v (Finset.mem_union_right _ hv) (hsub hv)



/-- Clique-restriction cardinality at a mixed seam on a contiguous arc.

For a contiguous arc `S` and an active anchor `a` (parity `j % 2`) whose seam
`block a ∪ block (a+1)` is mixed in `S` (neither fully in `S` nor disjoint from `S`),
the clique restriction `cliqueRestrict p a S` has size `p.k`.

**Proof**: `IsContiguousArc p S` is block-aligned, so each `block c` either lies in `S`
or is disjoint from it. The mixed-seam hypothesis rules out both blocks being in `S`
(would give `block a ∪ block (a+1) ⊆ S`) and both being disjoint (would give
`Disjoint (block a ∪ block (a+1)) S`). Hence exactly one of `block a`, `block (a+1)`
is in `S`; its image under `toCliqueVtx p a` has size `p.k` by `card_block` and
`toCliqueVtx_injOn`.

The `j`-parity hypothesis is unused in the conclusion but kept for API consistency
with the neighbouring `blockCount_balanced_absorption_symmetry`. -/
private theorem cliqueRestrict_card_eq_k_of_mixed_on_contig
    (p : Params) (S : Finset (VertexSet p)) (hS : IsContiguousArc p S)
    (a : Fin p.z)
    (h_mixed : ¬ (block p a ∪ block p (a + 1) ⊆ S ∨
        Disjoint (block p a ∪ block p (a + 1)) S)) :
    (cliqueRestrict p a S).card = p.k := by
  classical
  -- We argue by cases on whether block a ⊆ S.
  have hblock_align : ∀ c : Fin p.z, block p c ⊆ S ∨ Disjoint (block p c) S := by
    intro c
    obtain ⟨b, m, hm_le, hS_eq⟩ := hS
    rw [hS_eq]
    classical
    -- block c is either one of the arc blocks (⊆) or disjoint.
    by_cases hc_in : ∃ i ∈ Finset.range m,
        c = ⟨(b.val + i) % p.z, Nat.mod_lt _ p.hz_pos⟩
    · left
      obtain ⟨i, hi_range, hc_eq⟩ := hc_in
      intro v hv
      rw [Finset.mem_biUnion]
      exact ⟨i, hi_range, hc_eq ▸ hv⟩
    · right
      rw [Finset.disjoint_right]
      intro v hv
      rw [Finset.mem_biUnion] at hv
      obtain ⟨i, hi_range, hv_block⟩ := hv
      intro hv_blockc
      apply hc_in
      refine ⟨i, hi_range, ?_⟩
      rw [mem_block] at hv_blockc hv_block
      rw [← hv_blockc, hv_block]
  have ha_in_or_disj := hblock_align a
  have ha1_in_or_disj := hblock_align (a + 1)
  -- h_mixed rules out (both in) and (both disjoint).
  have hcase : (block p a ⊆ S ∧ Disjoint (block p (a + 1)) S) ∨
               (Disjoint (block p a) S ∧ block p (a + 1) ⊆ S) := by
    rcases ha_in_or_disj with ha_in | ha_disj
    · rcases ha1_in_or_disj with ha1_in | ha1_disj
      · -- both in: contradicts h_mixed (block a ∪ block (a+1) ⊆ S).
        exact absurd (Or.inl (Finset.union_subset ha_in ha1_in)) h_mixed
      · exact Or.inl ⟨ha_in, ha1_disj⟩
    · rcases ha1_in_or_disj with ha1_in | ha1_disj
      · exact Or.inr ⟨ha_disj, ha1_in⟩
      · -- both disjoint: contradicts h_mixed.
        have hdisj_union : Disjoint (block p a ∪ block p (a + 1)) S := by
          rw [Finset.disjoint_union_left]; exact ⟨ha_disj, ha1_disj⟩
        exact absurd (Or.inr hdisj_union) h_mixed
  -- cliqueRestrict a S = image (toCliqueVtx a) (S ∩ cliqueFinset a).
  -- In each case, this image equals image of block a or image of block (a+1) (size k).
  rcases hcase with ⟨ha_in, ha1_disj⟩ | ⟨ha_disj, ha1_in⟩
  · -- block a ⊆ S, block (a+1) disjoint from S.
    have hint : S ∩ cliqueFinset p a = block p a := by
      rw [cliqueFinset]
      ext v
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hvS, hv | hv⟩
        · exact hv
        · exact absurd hv ((Finset.disjoint_left.mp (disjoint_comm.mp ha1_disj)) hvS)
      · intro hv
        exact ⟨ha_in hv, Or.inl hv⟩
    show ((S ∩ cliqueFinset p a).image (toCliqueVtx p a)).card = p.k
    rw [hint, Finset.card_image_of_injOn]
    · exact card_block p a
    · intro v hv w hw heq
      have hv' : v ∈ cliqueFinset p a := Finset.mem_union_left _ hv
      have hw' : w ∈ cliqueFinset p a := Finset.mem_union_left _ hw
      exact toCliqueVtx_injOn p a hv' hw' heq
  · -- block (a+1) ⊆ S, block a disjoint from S.
    have hint : S ∩ cliqueFinset p a = block p (a + 1) := by
      rw [cliqueFinset]
      ext v
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hvS, hv | hv⟩
        · exact absurd hv ((Finset.disjoint_left.mp (disjoint_comm.mp ha_disj)) hvS)
        · exact hv
      · intro hv
        exact ⟨ha1_in hv, Or.inr hv⟩
    show ((S ∩ cliqueFinset p a).image (toCliqueVtx p a)).card = p.k
    rw [hint, Finset.card_image_of_injOn]
    · exact card_block p (a + 1)
    · intro v hv w hw heq
      have hv' : v ∈ cliqueFinset p a := Finset.mem_union_right _ hv
      have hw' : w ∈ cliqueFinset p a := Finset.mem_union_right _ hw
      exact toCliqueVtx_injOn p a hv' hw' heq

/-- \label{lem:opinion-process-clique-marginal-balanced-univ-eq-empty}

Full marginal symmetry: for a contiguous arc `S` with mixed seam at active anchor `a`
(parity `j % 2`), the full sum of `[cliqueRestrict a S' = univ] · opP_lbg(S, S').toReal`
equals the full sum with `univ` replaced by `∅`.

No `IsContiguousArc p S'` restriction is imposed on the sum; this is the *full*
marginal identity (no leak step).

**Proof.** Each side equals the `.toReal` of the marginal PMF
`(opP_lbg(S, ·)).map (cliqueRestrict p a)` evaluated at `univ` and `∅` respectively.
By `opinionProcess₂_clique_marginal`, this marginal equals
`opP_static(cliqueRestrict p a S, ·)`. By `cliqueRestrict_card_eq_k_of_mixed_on_contig`
(L99), `|cliqueRestrict p a S| = p.k`, so
`opinionProcess₂_staticClique_balanced_absorption_symmetric` (L69) gives equality at
`univ` and `∅`. -/
theorem opinionProcess₂_clique_marginal_balanced_univ_eq_empty
    (p : Params) (j : ℕ) (S : Finset (VertexSet p)) (hS : IsContiguousArc p S)
    (a : Fin p.z) (ha_par : a.val % 2 = j % 2)
    (h_mixed : ¬ (block p a ∪ block p (a + 1) ⊆ S ∨
        Disjoint (block p a ∪ block p (a + 1) ) S)) :
    ∑ S' : Finset (VertexSet p),
        ((@ite ℝ (cliqueRestrict p a S' = (Finset.univ : Finset (CliqueVertex p.k)))
              (Classical.dec _) 1 0) *
          (VoterModel.opinionProcess₂ (lowerBoundGraph p) (j * p.T) p.T S S').toReal) =
      ∑ S' : Finset (VertexSet p),
        ((@ite ℝ (cliqueRestrict p a S' = (∅ : Finset (CliqueVertex p.k)))
              (Classical.dec _) 1 0) *
          (VoterModel.opinionProcess₂ (lowerBoundGraph p) (j * p.T) p.T S S').toReal) := by
  classical
  -- Abbreviation for the per-S' weight.
  set opP : Finset (VertexSet p) → ℝ := fun S' =>
    (VoterModel.opinionProcess₂ (lowerBoundGraph p) (j * p.T) p.T S S').toReal with hopP_def
  set Aunivℝ : Finset (VertexSet p) → ℝ := fun S' =>
    (@ite ℝ (cliqueRestrict p a S' = (Finset.univ : Finset (CliqueVertex p.k)))
      (Classical.dec _) 1 0) * opP S' with hAuniv_def
  set Aempℝ : Finset (VertexSet p) → ℝ := fun S' =>
    (@ite ℝ (cliqueRestrict p a S' = (∅ : Finset (CliqueVertex p.k)))
      (Classical.dec _) 1 0) * opP S' with hAemp_def
  -- L99: |cliqueRestrict p a S| = p.k at a mixed seam on a contig arc.
  have hcard : (cliqueRestrict p a S).card = p.k :=
    cliqueRestrict_card_eq_k_of_mixed_on_contig p S hS a h_mixed
  -- L69: static-clique balanced absorption is symmetric at any T₀ with card = k.
  have h_static :
      VoterModel.opinionProcess₂ (staticCliqueGraph p.k) 0 p.T
        (cliqueRestrict p a S) Finset.univ =
      VoterModel.opinionProcess₂ (staticCliqueGraph p.k) 0 p.T
        (cliqueRestrict p a S) ∅ :=
    opinionProcess₂_staticClique_balanced_absorption_symmetric p.k p.hk_pos 0 p.T
      (cliqueRestrict p a S) hcard
  -- Marginal identity: (opP_lbg S).map(cliqueRestrict a) = opP_static(cliqueRestrict S).
  have hmarg := opinionProcess₂_clique_marginal p a j p.T (le_refl _) ha_par S
  -- Sum of Aunivℝ = (full marginal at univ).toReal.
  have hAuniv_sum : (∑ S' : Finset (VertexSet p), Aunivℝ S') =
      (VoterModel.opinionProcess₂ (staticCliqueGraph p.k) 0 p.T
        (cliqueRestrict p a S) Finset.univ).toReal := by
    have hmap_apply : ((VoterModel.opinionProcess₂ (lowerBoundGraph p) (j * p.T) p.T S).map
          (cliqueRestrict p a)) Finset.univ =
        ∑' S' : Finset (VertexSet p),
          (@ite ENNReal (Finset.univ = cliqueRestrict p a S') (Classical.dec _)
            ((VoterModel.opinionProcess₂ (lowerBoundGraph p) (j * p.T) p.T S) S') 0) := by
      rw [PMF.map_apply]
    rw [hmarg] at hmap_apply
    have h_tsum_eq : ∑' S' : Finset (VertexSet p),
          (@ite ENNReal (Finset.univ = cliqueRestrict p a S') (Classical.dec _)
            ((VoterModel.opinionProcess₂ (lowerBoundGraph p) (j * p.T) p.T S) S') 0) =
        ∑ S' : Finset (VertexSet p),
          (@ite ENNReal (Finset.univ = cliqueRestrict p a S') (Classical.dec _)
            ((VoterModel.opinionProcess₂ (lowerBoundGraph p) (j * p.T) p.T S) S') 0) :=
      tsum_eq_sum (fun b hb => absurd (Finset.mem_univ _) hb)
    rw [h_tsum_eq] at hmap_apply
    have hlt_each : ∀ S' : Finset (VertexSet p),
        (@ite ENNReal (Finset.univ = cliqueRestrict p a S') (Classical.dec _)
          ((VoterModel.opinionProcess₂ (lowerBoundGraph p) (j * p.T) p.T S) S') 0) ≠ ⊤ := by
      intro S'
      by_cases h : (Finset.univ : Finset (CliqueVertex p.k)) = cliqueRestrict p a S'
      · simp [h, PMF.apply_ne_top]
      · simp [h]
    have hsum_real_eq :
        (∑ S' : Finset (VertexSet p),
          (@ite ENNReal (Finset.univ = cliqueRestrict p a S') (Classical.dec _)
            ((VoterModel.opinionProcess₂ (lowerBoundGraph p) (j * p.T) p.T S) S') 0)).toReal =
        ∑ S' : Finset (VertexSet p), Aunivℝ S' := by
      rw [ENNReal.toReal_sum (fun S' _ => hlt_each S')]
      apply Finset.sum_congr rfl
      intro S' _
      rw [hAuniv_def]
      dsimp only
      by_cases h : (Finset.univ : Finset (CliqueVertex p.k)) = cliqueRestrict p a S'
      · have h' : cliqueRestrict p a S' = Finset.univ := h.symm
        rw [if_pos h, if_pos h', one_mul]
      · have h' : cliqueRestrict p a S' ≠ Finset.univ := fun heq => h heq.symm
        rw [if_neg h, if_neg h', zero_mul]
        rfl
    rw [← hsum_real_eq, ← hmap_apply]
  have hAemp_sum : (∑ S' : Finset (VertexSet p), Aempℝ S') =
      (VoterModel.opinionProcess₂ (staticCliqueGraph p.k) 0 p.T
        (cliqueRestrict p a S) ∅).toReal := by
    have hmap_apply : ((VoterModel.opinionProcess₂ (lowerBoundGraph p) (j * p.T) p.T S).map
          (cliqueRestrict p a)) ∅ =
        ∑' S' : Finset (VertexSet p),
          (@ite ENNReal (∅ = cliqueRestrict p a S') (Classical.dec _)
            ((VoterModel.opinionProcess₂ (lowerBoundGraph p) (j * p.T) p.T S) S') 0) := by
      rw [PMF.map_apply]
    rw [hmarg] at hmap_apply
    have h_tsum_eq : ∑' S' : Finset (VertexSet p),
          (@ite ENNReal (∅ = cliqueRestrict p a S') (Classical.dec _)
            ((VoterModel.opinionProcess₂ (lowerBoundGraph p) (j * p.T) p.T S) S') 0) =
        ∑ S' : Finset (VertexSet p),
          (@ite ENNReal (∅ = cliqueRestrict p a S') (Classical.dec _)
            ((VoterModel.opinionProcess₂ (lowerBoundGraph p) (j * p.T) p.T S) S') 0) :=
      tsum_eq_sum (fun b hb => absurd (Finset.mem_univ _) hb)
    rw [h_tsum_eq] at hmap_apply
    have hlt_each : ∀ S' : Finset (VertexSet p),
        (@ite ENNReal (∅ = cliqueRestrict p a S') (Classical.dec _)
          ((VoterModel.opinionProcess₂ (lowerBoundGraph p) (j * p.T) p.T S) S') 0) ≠ ⊤ := by
      intro S'
      by_cases h : (∅ : Finset (CliqueVertex p.k)) = cliqueRestrict p a S'
      · simp [h, PMF.apply_ne_top]
      · simp [h]
    have hsum_real_eq :
        (∑ S' : Finset (VertexSet p),
          (@ite ENNReal (∅ = cliqueRestrict p a S') (Classical.dec _)
            ((VoterModel.opinionProcess₂ (lowerBoundGraph p) (j * p.T) p.T S) S') 0)).toReal =
        ∑ S' : Finset (VertexSet p), Aempℝ S' := by
      rw [ENNReal.toReal_sum (fun S' _ => hlt_each S')]
      apply Finset.sum_congr rfl
      intro S' _
      rw [hAemp_def]
      dsimp only
      by_cases h : (∅ : Finset (CliqueVertex p.k)) = cliqueRestrict p a S'
      · have h' : cliqueRestrict p a S' = ∅ := h.symm
        rw [if_pos h, if_pos h', one_mul]
      · have h' : cliqueRestrict p a S' ≠ ∅ := fun heq => h heq.symm
        rw [if_neg h, if_neg h', zero_mul]
        rfl
    rw [← hsum_real_eq, ← hmap_apply]
  rw [hAuniv_sum, hAemp_sum, h_static]

/-- \label{lem:boundary-delta-cond-exp-zero}

`E[Δ_j(A_{jT}, A_{(j+1)T}) | ℱ_{jT}] = 0` a.s.

For the voter model `vm` on `lowerBoundGraph p` and parity `j : ℕ`, the
conditional expectation of `boundaryDelta p j (A_{jT}, A_{(j+1)T})` given
`ℱ_{jT}` equals 0 almost surely.

**Proof.** Apply uniqueness of the conditional expectation
(`ae_eq_condExp_of_forall_setIntegral_eq`). For each ℱ_{jT}-measurable
`s` decompose `s = ⋃_S (s ∩ {A(jT) = S})`. On non-contiguous atoms the
integrand vanishes by `boundaryDelta`'s `ite` guard. On contiguous atoms
expand `boundaryDelta` over `activeMixed p j S` and use
`multistep_markov_filtration₂` to rewrite each measure
`vm.μ(atomS ∩ {A((j+1)T) = S'})` as `opP·vm.μ(atomS)`. The remaining sum
factors via `Finset.sum_comm` into `∑_{a ∈ activeMixed} (univ-side − ∅-side)`,
which is zero by `opinionProcess₂_clique_marginal_balanced_univ_eq_empty`
(L100). -/
theorem boundaryDelta_condExp_zero
    (p : Params) {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (vm : TemporalGraph.VoterModelAbstract (lowerBoundGraph p) 2 Ω)
    (j : ℕ) :
    (vm.μ : Measure _)[(fun ω => boundaryDelta p j (vm.opinionZeroSet (j * p.T) ω) (vm.opinionZeroSet ((j + 1) * p.T) ω)) |
        vm.ℱ (j * p.T)] =ᵐ[(vm.μ : Measure _)] (0 : Ω → ℝ) := by
  classical
  haveI : IsProbabilityMeasure (vm.μ : Measure Ω) := inferInstance
  -- σ-algebra at time j*T.
  have hfilt_le : vm.ℱ (j * p.T) ≤ (inferInstance : MeasurableSpace Ω) := vm.ℱ.le _
  haveI : SigmaFinite ((vm.μ : Measure _).trim hfilt_le) := inferInstance
  -- The integrand `f`.
  set f : Ω → ℝ := fun ω =>
    boundaryDelta p j (vm.opinionZeroSet (j * p.T) ω) (vm.opinionZeroSet ((j + 1) * p.T) ω) with hf_def
  -- Pointwise bound on `f`: `|boundaryDelta| ≤ |activeMixed| ≤ p.z`.
  have hf_bound : ∀ ω, |f ω| ≤ (p.z : ℝ) := by
    intro ω
    simp only [hf_def, boundaryDelta]
    split_ifs with hcont
    · -- |∑| ≤ ∑|·| ≤ ∑ 1 ≤ |activeMixed| ≤ p.z.
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hterm_le : ∀ a ∈ activeMixed p j (vm.opinionZeroSet (j * p.T) ω),
          |(if cliqueRestrict p a (vm.opinionZeroSet ((j + 1) * p.T) ω) = Finset.univ then (1 : ℝ) else 0) -
            (if cliqueRestrict p a (vm.opinionZeroSet ((j + 1) * p.T) ω) = ∅ then (1 : ℝ) else 0)| ≤ 1 := by
        intro a _
        rcases (em (cliqueRestrict p a (vm.opinionZeroSet ((j + 1) * p.T) ω) = Finset.univ)) with h1 | h1
        · rw [if_pos h1]
          rcases (em (cliqueRestrict p a (vm.opinionZeroSet ((j + 1) * p.T) ω) = ∅)) with h2 | h2
          · rw [if_pos h2]; norm_num
          · rw [if_neg h2]; norm_num
        · rw [if_neg h1]
          rcases (em (cliqueRestrict p a (vm.opinionZeroSet ((j + 1) * p.T) ω) = ∅)) with h2 | h2
          · rw [if_pos h2]; norm_num
          · rw [if_neg h2]; norm_num
      calc ∑ a ∈ activeMixed p j (vm.opinionZeroSet (j * p.T) ω),
              |(if cliqueRestrict p a (vm.opinionZeroSet ((j + 1) * p.T) ω) = Finset.univ then (1 : ℝ) else 0) -
                (if cliqueRestrict p a (vm.opinionZeroSet ((j + 1) * p.T) ω) = ∅ then (1 : ℝ) else 0)|
            ≤ ∑ _a ∈ activeMixed p j (vm.opinionZeroSet (j * p.T) ω), (1 : ℝ) := by
              exact Finset.sum_le_sum hterm_le
          _ = ((activeMixed p j (vm.opinionZeroSet (j * p.T) ω)).card : ℝ) := by
              rw [Finset.sum_const, nsmul_eq_mul, mul_one]
          _ ≤ ((Finset.univ : Finset (Fin p.z)).card : ℝ) := by
              exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
          _ = (p.z : ℝ) := by rw [Finset.card_univ, Fintype.card_fin]
    · simp [abs_zero, Nat.cast_nonneg]
  -- Strong measurability of `f` factoring through `(A(jT), A((j+1)T))`.
  have hAjm : Measurable (vm.opinionZeroSet (j * p.T)) :=
    (VoterModelAbstract.A_stronglyAdapted vm (j * p.T)).measurable.mono (vm.ℱ.le _) le_rfl
  have hAj1m : Measurable (vm.opinionZeroSet ((j + 1) * p.T)) :=
    (VoterModelAbstract.A_stronglyAdapted vm ((j + 1) * p.T)).measurable.mono (vm.ℱ.le _) le_rfl
  have hf_sm : StronglyMeasurable f := by
    have hprodm : Measurable
        (fun ω => (vm.opinionZeroSet (j * p.T) ω, vm.opinionZeroSet ((j + 1) * p.T) ω)) :=
      hAjm.prodMk hAj1m
    have hcomp : Measurable f := by
      have : f = (fun (st : Finset (VertexSet p) × Finset (VertexSet p)) =>
          boundaryDelta p j st.1 st.2) ∘
          (fun ω => (vm.opinionZeroSet (j * p.T) ω, vm.opinionZeroSet ((j + 1) * p.T) ω)) := by
        funext ω; rfl
      rw [this]
      exact Measurable.of_discrete.comp hprodm
    exact hcomp.stronglyMeasurable
  -- Integrability of `f`.
  have hf_int : Integrable f vm.μ :=
    MeasureTheory.Integrable.of_bound hf_sm.aestronglyMeasurable (p.z : ℝ)
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hf_bound ω)
  -- Apply uniqueness of conditional expectation.
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hfilt_le hf_int
  · intro s _ _; exact (integrable_zero _ _ _).integrableOn
  · intro s hs _
    -- ∫_s 0 = 0; need ∫_s f = 0.
    simp only [Pi.zero_apply, MeasureTheory.integral_zero]
    symm
    -- Atom-decompose s by `vm.opinionZeroSet (j*T)`.
    set atomS : Finset (VertexSet p) → Set Ω :=
      fun S => s ∩ {ω : Ω | vm.opinionZeroSet (j * p.T) ω = S} with hatomS_def
    have hAj_meas_F : ∀ S : Finset (VertexSet p),
        @MeasurableSet Ω (vm.ℱ (j * p.T)) {ω : Ω | vm.opinionZeroSet (j * p.T) ω = S} := by
      intro S
      have hAm : Measurable[vm.ℱ (j * p.T)] (vm.opinionZeroSet (j * p.T)) :=
        (VoterModelAbstract.A_stronglyAdapted vm (j * p.T)).measurable
      exact hAm (measurableSet_singleton S)
    have hatomS_filt : ∀ S, @MeasurableSet Ω (vm.ℱ (j * p.T)) (atomS S) := fun S =>
      hs.inter (hAj_meas_F S)
    have hatomS_meas : ∀ S, MeasurableSet (atomS S) := fun S =>
      hfilt_le _ (hatomS_filt S)
    have hpart_S : s = ⋃ S : Finset (VertexSet p), atomS S := by
      ext ω; simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq, atomS]
      refine ⟨fun h => ⟨vm.opinionZeroSet (j * p.T) ω, h, rfl⟩, fun ⟨_, ⟨h, _⟩⟩ => h⟩
    have hdisj_S : Pairwise (Function.onFun Disjoint atomS) := by
      intro S₁ S₂ hne
      apply Set.disjoint_left.mpr
      intro ω h1 h2
      exact hne (h1.2.symm.trans h2.2)
    rw [hpart_S,
      MeasureTheory.integral_iUnion_fintype hatomS_meas hdisj_S
        (fun S => hf_int.integrableOn)]
    -- It suffices to show each atom-integral is 0.
    apply Finset.sum_eq_zero
    intro S _
    -- On atomS S, f = boundaryDelta p j S (A((j+1)T) ω).
    have hf_on_atom : ∀ ω ∈ atomS S,
        f ω = boundaryDelta p j S (vm.opinionZeroSet ((j + 1) * p.T) ω) := by
      intro ω hω
      simp only [hf_def]
      rw [hω.2]
    by_cases hcontS : IsContiguousArc p S
    · -- Contiguous case: expand boundaryDelta and apply L100.
      -- Step 1: pointwise rewrite of `f` on atomS S to the per-S' indicator sum.
      have hf_atom_sum : ∀ ω ∈ atomS S,
          f ω = ∑ S' : Finset (VertexSet p),
            boundaryDelta p j S S' *
              (if vm.opinionZeroSet ((j + 1) * p.T) ω = S' then (1 : ℝ) else 0) := by
        intro ω hω
        rw [hf_on_atom ω hω]
        rw [Finset.sum_eq_single (vm.opinionZeroSet ((j + 1) * p.T) ω)]
        · simp
        · intro S' _ hne; rw [if_neg (Ne.symm hne), mul_zero]
        · intro h; exact absurd (Finset.mem_univ _) h
      -- Step 2: integrate the sum over atomS S.
      have hint_sum :
          ∫ x in atomS S, f x ∂vm.μ =
            ∑ S' : Finset (VertexSet p),
              boundaryDelta p j S S' *
                ((vm.μ : Measure _) (atomS S ∩ {ω | vm.opinionZeroSet ((j + 1) * p.T) ω = S'})).toReal := by
        have hAset_meas : ∀ S' : Finset (VertexSet p),
            MeasurableSet {ω : Ω | vm.opinionZeroSet ((j + 1) * p.T) ω = S'} :=
          fun S' => hAj1m (measurableSet_singleton S')
        conv_lhs => rw [setIntegral_congr_fun (hatomS_meas S) (fun ω hω => hf_atom_sum ω hω)]
        rw [MeasureTheory.integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro S' _
          rw [MeasureTheory.integral_const_mul]
          congr 1
          rw [show (fun x : Ω => (if vm.opinionZeroSet ((j + 1) * p.T) x = S' then (1 : ℝ) else 0)) =
                Set.indicator {ω | vm.opinionZeroSet ((j + 1) * p.T) ω = S'} (fun _ => (1 : ℝ)) from by
            funext ω; simp [Set.indicator_apply]]
          rw [MeasureTheory.integral_indicator (hAset_meas S')]
          rw [MeasureTheory.setIntegral_const]
          simp [Measure.real, Measure.restrict_apply (hAset_meas S'), Set.inter_comm]
        · intro S' _
          have hsm : StronglyMeasurable
              (fun x : Ω => boundaryDelta p j S S' *
                (if vm.opinionZeroSet ((j + 1) * p.T) x = S' then (1 : ℝ) else 0)) := by
            apply StronglyMeasurable.mul
            · exact stronglyMeasurable_const
            · exact StronglyMeasurable.ite (hAset_meas S')
                stronglyMeasurable_const stronglyMeasurable_const
          refine MeasureTheory.Integrable.of_bound hsm.aestronglyMeasurable
            ((p.z : ℝ) + 1) (Filter.Eventually.of_forall fun ω => ?_)
          rw [Real.norm_eq_abs, abs_mul]
          have hbd_le : |boundaryDelta p j S S'| ≤ (p.z : ℝ) := by
            simp only [boundaryDelta, if_pos hcontS]
            have habs := Finset.abs_sum_le_sum_abs
              (fun a : Fin p.z =>
                (if cliqueRestrict p a S' = Finset.univ then (1 : ℝ) else 0) -
                  (if cliqueRestrict p a S' = ∅ then (1 : ℝ) else 0))
              (activeMixed p j S)
            refine habs.trans ?_
            have hterm_le : ∀ a ∈ activeMixed p j S,
                |(if cliqueRestrict p a S' = Finset.univ then (1 : ℝ) else 0) -
                  (if cliqueRestrict p a S' = ∅ then (1 : ℝ) else 0)| ≤ 1 := by
              intro a _
              rcases em (cliqueRestrict p a S' = Finset.univ) with h1 | h1
              · rw [if_pos h1]
                rcases em (cliqueRestrict p a S' = ∅) with h2 | h2
                · rw [if_pos h2]; norm_num
                · rw [if_neg h2]; norm_num
              · rw [if_neg h1]
                rcases em (cliqueRestrict p a S' = ∅) with h2 | h2
                · rw [if_pos h2]; norm_num
                · rw [if_neg h2]; norm_num
            calc ∑ a ∈ activeMixed p j S,
                    |(if cliqueRestrict p a S' = Finset.univ then (1 : ℝ) else 0) -
                      (if cliqueRestrict p a S' = ∅ then (1 : ℝ) else 0)|
                  ≤ ∑ _a ∈ activeMixed p j S, (1 : ℝ) := Finset.sum_le_sum hterm_le
                _ = ((activeMixed p j S).card : ℝ) := by
                    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
                _ ≤ ((Finset.univ : Finset (Fin p.z)).card : ℝ) := by
                    exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
                _ = (p.z : ℝ) := by rw [Finset.card_univ, Fintype.card_fin]
          have hind : |(if vm.opinionZeroSet ((j + 1) * p.T) ω = S' then (1 : ℝ) else 0)| ≤ 1 := by
            split_ifs <;> norm_num
          calc |boundaryDelta p j S S'| *
                |(if vm.opinionZeroSet ((j + 1) * p.T) ω = S' then (1 : ℝ) else 0)|
              ≤ (p.z : ℝ) * 1 :=
                mul_le_mul hbd_le hind (by positivity) (by positivity)
            _ ≤ (p.z : ℝ) + 1 := by linarith
      -- Step 3: rewrite each atom-measure via `multistep_markov_filtration₂`.
      have hatom_meas : ∀ S' : Finset (VertexSet p),
          ((vm.μ : Measure _) (atomS S ∩ {ω | vm.opinionZeroSet ((j + 1) * p.T) ω = S'})).toReal =
            (VoterModel.opinionProcess₂ (lowerBoundGraph p) (j * p.T) p.T S S').toReal *
              ((vm.μ : Measure _) (atomS S)).toReal := by
        intro S'
        have hmk := VoterModel.multistep_markov_filtration₂
          (lowerBoundGraph p) vm (j * p.T) p.T S' (atomS S) (hatomS_filt S)
        have htimes : (j + 1) * p.T = j * p.T + p.T := by ring
        rw [htimes]
        have hconstS : ∀ ω ∈ atomS S,
            (VoterModel.opinionProcess₂ (lowerBoundGraph p) (j * p.T) p.T
              (vm.opinionZeroSet (j * p.T) ω)) S' =
            (VoterModel.opinionProcess₂ (lowerBoundGraph p) (j * p.T) p.T S) S' := by
          intro ω hω; rw [hω.2]
        rw [hmk, setLIntegral_congr_fun (hatomS_meas S) hconstS]
        rw [setLIntegral_const, ENNReal.toReal_mul, mul_comm]
      -- Step 4: combine + apply L100 inside `boundaryDelta`'s sum.
      rw [hint_sum]
      have h_factor :
          ∑ S' : Finset (VertexSet p),
              boundaryDelta p j S S' *
                ((vm.μ : Measure _) (atomS S ∩ {ω | vm.opinionZeroSet ((j + 1) * p.T) ω = S'})).toReal =
            ((vm.μ : Measure _) (atomS S)).toReal *
              ∑ S' : Finset (VertexSet p),
                boundaryDelta p j S S' *
                  (VoterModel.opinionProcess₂ (lowerBoundGraph p)
                    (j * p.T) p.T S S').toReal := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro S' _
        rw [hatom_meas S']; ring
      rw [h_factor]
      -- The inner sum is 0 by L100 applied to each anchor in `activeMixed p j S`.
      have h_inner :
          ∑ S' : Finset (VertexSet p),
              boundaryDelta p j S S' *
                (VoterModel.opinionProcess₂ (lowerBoundGraph p)
                  (j * p.T) p.T S S').toReal = 0 := by
        -- Unfold boundaryDelta on contiguous S.
        have hbd_eq : ∀ S' : Finset (VertexSet p),
            boundaryDelta p j S S' =
              ∑ a ∈ activeMixed p j S,
                ((if cliqueRestrict p a S' = Finset.univ then (1 : ℝ) else 0) -
                  (if cliqueRestrict p a S' = ∅ then (1 : ℝ) else 0)) := by
          intro S'
          simp only [boundaryDelta]
          rw [if_pos hcontS]
        -- Distribute multiplication, then swap sums.
        have hexpand : ∀ S' : Finset (VertexSet p),
            boundaryDelta p j S S' *
              (VoterModel.opinionProcess₂ (lowerBoundGraph p) (j * p.T) p.T S S').toReal =
            ∑ a ∈ activeMixed p j S,
              ((if cliqueRestrict p a S' = Finset.univ then (1 : ℝ) else 0) -
                (if cliqueRestrict p a S' = ∅ then (1 : ℝ) else 0)) *
              (VoterModel.opinionProcess₂ (lowerBoundGraph p)
                (j * p.T) p.T S S').toReal := by
          intro S'
          rw [hbd_eq S', Finset.sum_mul]
        simp_rw [hexpand]
        rw [Finset.sum_comm]
        -- For each a ∈ activeMixed p j S, the inner sum over S' vanishes by L100.
        apply Finset.sum_eq_zero
        intro a ha
        -- Extract the parity + mixed-seam witnesses from activeMixed.
        simp only [activeMixed, Finset.mem_filter, Finset.mem_univ, true_and] at ha
        obtain ⟨ha_par, h_mixed⟩ := ha
        have hL100 := opinionProcess₂_clique_marginal_balanced_univ_eq_empty
          p j S hcontS a ha_par h_mixed
        -- Goal: ∑_{S'} (1[univ] - 1[∅]) * opP = 0; split as `univ`-sum minus `∅`-sum.
        have hsplit :
            ∑ S' : Finset (VertexSet p),
                ((if cliqueRestrict p a S' = Finset.univ then (1 : ℝ) else 0) -
                  (if cliqueRestrict p a S' = ∅ then (1 : ℝ) else 0)) *
                  (VoterModel.opinionProcess₂ (lowerBoundGraph p)
                    (j * p.T) p.T S S').toReal =
            (∑ S' : Finset (VertexSet p),
                ((@ite ℝ (cliqueRestrict p a S' = (Finset.univ : Finset (CliqueVertex p.k)))
                    (Classical.dec _) 1 0) *
                  (VoterModel.opinionProcess₂ (lowerBoundGraph p)
                    (j * p.T) p.T S S').toReal)) -
              ∑ S' : Finset (VertexSet p),
                ((@ite ℝ (cliqueRestrict p a S' = (∅ : Finset (CliqueVertex p.k)))
                    (Classical.dec _) 1 0) *
                  (VoterModel.opinionProcess₂ (lowerBoundGraph p)
                    (j * p.T) p.T S S').toReal) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro S' _
          ring_nf
        rw [hsplit, hL100, sub_self]
      rw [h_inner, mul_zero]
    · -- Non-contiguous case: integrand is 0 pointwise on atomS S.
      have hf_zero : ∀ ω ∈ atomS S, f ω = 0 := by
        intro ω hω
        rw [hf_on_atom ω hω]
        simp only [boundaryDelta]
        rw [if_neg hcontS]
      rw [setIntegral_congr_fun (hatomS_meas S) hf_zero]
      exact MeasureTheory.integral_zero _ _
  · -- AE strong measurability of (0 : Ω → ℝ) w.r.t. vm.ℱ (j*T).
    exact (stronglyMeasurable_const : StronglyMeasurable[vm.ℱ (j * p.T)]
      (fun _ : Ω => (0 : ℝ))).aestronglyMeasurable

/-- \label{lem:boundary-delta-process-eq-block-count-on-live}

Bridge lemma. On the *live event* `{arcFailTime > j}`, the accumulated boundary-increment
process `boundaryDeltaProcess p vm j` (a.k.a. `W̃_j`) coincides with the block-count
process `blockCount p vm j` (cast to `ℝ`), almost surely.

The pointwise version is unprovable from `arcFailTime > j` alone: the inductive step
needs `opinionProcess₂(jT, T, A_jT(ω), A_(j+1)T(ω)) ≠ 0` to apply the seam-preservation
lemmas, but for measure-zero outliers the joint can be off-support. The a.e. signature
suffices for downstream Azuma applications, and matches paper semantics.

**Proof.** Induction on `j`.
- *Base:* `boundaryDeltaProcess 0 = z/2` by definition; `blockCount 0 = z/2` by
  `blockCount_initial`. Pointwise equal.
- *Step:* assume IH (a.e.). For each `k ≤ j`, let `badStep k` be the (measure-zero) set
  of outcomes where `opP(kT, T, A_kT, A_(k+1)T) = 0`. On the complement of `badUpTo (j+1)`,
  intersected with `{arcFailTime > j+1}`: both `A_jT` and `A_(j+1)T` are contiguous arcs
  (by definition of `arcFailTime`), and `opP ≠ 0` at step `j`. Decompose
  `blockCount(j+1) - blockCount(j)` as `∑_c ([block c ⊆ A_(j+1)T] - [block c ⊆ A_jT])`;
  interior cliques (whose active seam is at consensus in `A_jT`) contribute 0 by
  `opinionProcess₂_seam_subset_preserved`/`_disjoint_preserved`; boundary cliques
  (`c ∈ {a, a+1}` with `a ∈ activeMixed`) give `[cR_a = univ] - [cR_a = ∅]` via the
  block-pair iff lemmas, matching `boundaryDelta`. -/
theorem boundaryDeltaProcess_eq_blockCount_on_live
    (p : Params) {Ω : Type} [MeasurableSpace Ω]
    (vm : TemporalGraph.VoterModelAbstract (lowerBoundGraph p) 2 Ω)
    (hA₀ : ∀ᵐ ω ∂(vm.μ : Measure Ω), vm.opinionZeroSet 0 ω = halfCutLow p) (j : ℕ) :
    ∀ᵐ ω ∂(vm.μ : Measure _), (j : WithTop ℕ) < arcFailTime p vm ω →
      boundaryDeltaProcess p vm j ω = (blockCount p vm j ω : ℝ) := by
  classical
  -- Auxiliary: arc holds at all times strictly before `arcFailTime`.
  have h_arc_before :
      ∀ (ω : Ω) (n : ℕ), (↑n : WithTop ℕ) < arcFailTime p vm ω →
        IsContiguousArc p (vm.opinionZeroSet (n * p.T) ω) := by
    intro ω n hlt
    by_contra hbad
    have hmem : (↑n : WithTop ℕ) ∈
        {j : WithTop ℕ | j ≠ ⊤ ∧ ¬IsContiguousArc p (vm.opinionZeroSet (j.getD 0 * p.T) ω)} := by
      refine ⟨WithTop.coe_ne_top, ?_⟩
      show ¬IsContiguousArc p (vm.opinionZeroSet (((↑n : WithTop ℕ).getD 0) * p.T) ω)
      have hgetd : ((↑n : WithTop ℕ).getD 0) = n := rfl
      rw [hgetd]
      exact hbad
    have hsInf_le : arcFailTime p vm ω ≤ (↑n : WithTop ℕ) := sInf_le hmem
    exact absurd hsInf_le (not_le.mpr hlt)
  -- Auxiliary: `arcFailTime > j+1 ⟹ arcFailTime > j`.
  have h_live_mono : ∀ (ω : Ω) (k : ℕ),
      ((k + 1 : ℕ) : WithTop ℕ) < arcFailTime p vm ω →
        (k : WithTop ℕ) < arcFailTime p vm ω := by
    intro ω k hlt
    have hle : (k : WithTop ℕ) ≤ ((k + 1 : ℕ) : WithTop ℕ) := by
      exact_mod_cast Nat.le_succ k
    exact lt_of_le_of_lt hle hlt
  -- Bad step at index `k`: outcomes where the one-step PMF assigns 0 mass to the realized
  -- successor.  By `vm.A_markovMarginal`, each such "fiber" has measure 0.  Define `badStep k` as
  -- the union over all (S, S') with opP = 0 of `{A_kT = S} ∩ {A_(k+1)T = S'}`.
  set badStep : ℕ → Set Ω := fun k =>
    ⋃ q ∈ ((Finset.univ : Finset (Finset (VertexSet p) × Finset (VertexSet p))).filter
        (fun q =>
          VoterModel.opinionProcess₂ (lowerBoundGraph p) (k * p.T) p.T q.1 q.2 = 0)),
      ({ω : Ω | vm.opinionZeroSet (k * p.T) ω = q.1} ∩ {ω | vm.opinionZeroSet ((k + 1) * p.T) ω = q.2})
    with hbadStep_def
  have hbadStep_zero : ∀ k, (vm.μ : Measure _) (badStep k) = 0 := by
    intro k
    set goodPairs : Finset (Finset (VertexSet p) × Finset (VertexSet p)) :=
      (Finset.univ.filter (fun q =>
        VoterModel.opinionProcess₂ (lowerBoundGraph p) (k * p.T) p.T q.1 q.2 = 0))
      with hgoodPairs_def
    have h_fiber_zero : ∀ q ∈ goodPairs,
        (vm.μ : Measure _) ({ω : Ω | vm.opinionZeroSet (k * p.T) ω = q.1} ∩
              {ω | vm.opinionZeroSet ((k + 1) * p.T) ω = q.2}) = 0 := by
      intro q hq
      simp only [goodPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hq
      have hMk := vm.A_markovMarginal (k * p.T) p.T q.1 q.2
      have hidx : k * p.T + p.T = (k + 1) * p.T := by ring
      rw [hidx] at hMk
      rw [hMk, hq, mul_zero]
    have h_sum_zero :
        (∑ q ∈ goodPairs, (vm.μ : Measure _) ({ω : Ω | vm.opinionZeroSet (k * p.T) ω = q.1} ∩
              {ω | vm.opinionZeroSet ((k + 1) * p.T) ω = q.2})) = 0 :=
      Finset.sum_eq_zero h_fiber_zero
    have h_le :
        (vm.μ : Measure _) (badStep k) ≤ ∑ q ∈ goodPairs,
          (vm.μ : Measure _) ({ω : Ω | vm.opinionZeroSet (k * p.T) ω = q.1} ∩
              {ω | vm.opinionZeroSet ((k + 1) * p.T) ω = q.2}) := by
      simp only [hbadStep_def, goodPairs]
      exact measure_biUnion_finset_le _ _
    exact le_antisymm (h_sum_zero ▸ h_le) bot_le
  -- Off `badStep k`: `opP(kT, T, A_kT ω, A_(k+1)T ω) ≠ 0`.
  have h_opP_ne_off_badStep : ∀ k ω, ω ∉ badStep k →
      VoterModel.opinionProcess₂ (lowerBoundGraph p) (k * p.T) p.T
          (vm.opinionZeroSet (k * p.T) ω) (vm.opinionZeroSet ((k + 1) * p.T) ω) ≠ 0 := by
    intro k ω hω h0
    apply hω
    simp only [hbadStep_def, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq, Prod.exists]
    exact ⟨vm.opinionZeroSet (k * p.T) ω, vm.opinionZeroSet ((k + 1) * p.T) ω, h0, rfl, rfl⟩
  -- The set-level key identity: for contig S, S' with `opP(kT, T, S, S') ≠ 0`, the
  -- per-step `boundaryDelta` equals `blockCountSet S' - blockCountSet S`.
  set blockCountSet : Finset (VertexSet p) → ℕ :=
    fun S => (Finset.univ.filter fun i : Fin p.z => block p i ⊆ S).card
    with hblockCountSet_def
  have hbc_to_set : ∀ (k : ℕ) (ω : Ω),
      blockCount p vm k ω = blockCountSet (vm.opinionZeroSet (k * p.T) ω) := by
    intro k ω; rfl
  have hkey : ∀ (k : ℕ) (S S' : Finset (VertexSet p)),
      IsContiguousArc p S → IsContiguousArc p S' →
      VoterModel.opinionProcess₂ (lowerBoundGraph p) (k * p.T) p.T S S' ≠ 0 →
      boundaryDelta p k S S' =
        ((blockCountSet S' : ℝ) - (blockCountSet S : ℝ)) := by
    intro k S S' hcS hcS' hop
    -- Unfold boundaryDelta on contiguous S.
    simp only [boundaryDelta]
    rw [if_pos hcS]
    -- For each c : Fin p.z, set a(c) = activeAnchor (decide (k%2=1)) c.
    -- Define per-c indicator δ(c) := [block c ⊆ S'] - [block c ⊆ S] ∈ {-1, 0, +1}.
    -- Then ∑_c δ(c) = (blockCountSet S' - blockCountSet S).
    have hdiff_eq :
        ((blockCountSet S' : ℝ) - (blockCountSet S : ℝ)) =
        ∑ c : Fin p.z,
          ((if block p c ⊆ S' then (1 : ℝ) else 0) -
            (if block p c ⊆ S then (1 : ℝ) else 0)) := by
      have heq1 : (blockCountSet S' : ℝ) =
          ∑ c : Fin p.z, (if block p c ⊆ S' then (1 : ℝ) else 0) := by
        simp only [hblockCountSet_def]
        rw [Finset.card_filter]
        push_cast
        rfl
      have heq2 : (blockCountSet S : ℝ) =
          ∑ c : Fin p.z, (if block p c ⊆ S then (1 : ℝ) else 0) := by
        simp only [hblockCountSet_def]
        rw [Finset.card_filter]
        push_cast
        rfl
      rw [heq1, heq2, ← Finset.sum_sub_distrib]
    rw [hdiff_eq]
    -- Partition Fin p.z by activeAnchor: c is interior (its anchor's seam is at consensus
    -- in S) ⟹ δ(c) = 0; boundary (anchor in activeMixed) ⟹ δ(c) = (per-anchor summand).
    -- Define `act c := activeAnchor (decide (k % 2 = 1)) c : Fin p.z`.
    set odd : Bool := decide (k % 2 = 1) with hodd_def
    set act : Fin p.z → Fin p.z := fun c => activeAnchor p odd c with hact_def
    have hact_par : ∀ c : Fin p.z, (act c).val % 2 = k % 2 := by
      intro c; exact activeAnchor_parity_jmod2 p k c
    -- Block c ⊆ block (act c) ∪ block (act c + 1).
    have hblockc_sub : ∀ c : Fin p.z,
        block p c ⊆ block p (act c) ∪ block p (act c + 1) := by
      intro c
      have hc_eq : c = act c ∨ c = act c + 1 := by
        have h_iff := activeAnchor_eq_iff_eq_or_succ p odd (act c) c
        have hact_par' : (act c).val % 2 = parityNat odd := by
          simp only [parityNat, hodd_def]
          rcases Nat.mod_two_eq_zero_or_one k with hj | hj
          · simp [hj, hact_par c]
          · simp [hj, hact_par c]
        exact (h_iff hact_par').mp rfl
      rcases hc_eq with hca | hca
      · conv_lhs => rw [hca]
        exact Finset.subset_union_left
      · conv_lhs => rw [hca]
        exact Finset.subset_union_right
    -- block c is nonempty.
    have hblockc_ne : ∀ c : Fin p.z, (block p c).Nonempty := by
      intro c
      have := card_block p c
      exact Finset.card_pos.mp (this ▸ p.hk_pos)
    -- Per-c partition into "consensus seam at act(c) in S" vs. "mixed".
    -- If seam at act(c) is at consensus in S, then by preservation (S → S' via opP ≠ 0),
    -- it's at consensus in S', and δ(c) = 0.
    -- If seam at act(c) is mixed in S, then act(c) ∈ activeMixed p k S, and we'll later
    -- recover the per-anchor summand.
    -- Define per-c indicator δ_c.
    -- Strategy: split the sum over c into:
    --   ∑_{c : act(c) seam at consensus} δ(c) = 0
    --   ∑_{c : act(c) ∈ activeMixed} δ(c) = ∑_{a ∈ activeMixed} (δ at a + δ at a+1)
    -- and show the second equals ∑_{a ∈ activeMixed} ((cR_a S' = univ) - (cR_a S' = ∅)).
    -- Define the predicate "act c seam mixed in S" and split.
    set isMixed : Fin p.z → Prop :=
      fun c => ¬ (block p (act c) ∪ block p (act c + 1) ⊆ S ∨
                  Disjoint (block p (act c) ∪ block p (act c + 1)) S)
      with hisMixed_def
    -- Per-c per-side identity for "interior" c (act c seam at consensus in S).
    have h_interior_zero : ∀ c : Fin p.z, ¬ isMixed c →
        ((if block p c ⊆ S' then (1 : ℝ) else 0) -
          (if block p c ⊆ S then (1 : ℝ) else 0)) = 0 := by
      intro c hnotmixed
      simp only [isMixed, not_not] at hnotmixed
      -- act c seam ⊆ S or disjoint from S.
      rcases hnotmixed with hsub_S | hdisj_S
      · -- Seam ⊆ S, hence (by preservation) seam ⊆ S'.
        have hsub_S' : block p (act c) ∪ block p (act c + 1) ⊆ S' :=
          opinionProcess₂_seam_subset_preserved p (act c) k (hact_par c) S S' hsub_S hop
        have hc_S : block p c ⊆ S := (hblockc_sub c).trans hsub_S
        have hc_S' : block p c ⊆ S' := (hblockc_sub c).trans hsub_S'
        rw [if_pos hc_S, if_pos hc_S', sub_self]
      · -- Seam disjoint from S, hence (by preservation) seam disjoint from S'.
        have hdisj_S' : Disjoint (block p (act c) ∪ block p (act c + 1)) S' :=
          opinionProcess₂_seam_disjoint_preserved p (act c) k (hact_par c) S S' hdisj_S hop
        obtain ⟨v, hv⟩ := hblockc_ne c
        have hv_seam : v ∈ block p (act c) ∪ block p (act c + 1) := hblockc_sub c hv
        have hc_nS : ¬ block p c ⊆ S := fun hc =>
          Finset.disjoint_left.mp hdisj_S hv_seam (hc hv)
        have hc_nS' : ¬ block p c ⊆ S' := fun hc =>
          Finset.disjoint_left.mp hdisj_S' hv_seam (hc hv)
        rw [if_neg hc_nS, if_neg hc_nS', sub_self]
    -- Restrict the sum over c to those with mixed-seam anchor.
    -- Split the sum: ∑_c = ∑_{isMixed c} + ∑_{¬ isMixed c}.
    have hsum_split :
        ∑ c : Fin p.z,
            ((if block p c ⊆ S' then (1 : ℝ) else 0) -
              (if block p c ⊆ S then (1 : ℝ) else 0)) =
        ∑ c ∈ (Finset.univ.filter (fun c => isMixed c)),
            ((if block p c ⊆ S' then (1 : ℝ) else 0) -
              (if block p c ⊆ S then (1 : ℝ) else 0)) := by
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin p.z))
          (fun c => isMixed c)]
      have hzero :
          (∑ c ∈ (Finset.univ.filter (fun c => ¬ isMixed c)),
              ((if block p c ⊆ S' then (1 : ℝ) else 0) -
                (if block p c ⊆ S then (1 : ℝ) else 0))) = 0 := by
        apply Finset.sum_eq_zero
        intro c hc
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
        exact h_interior_zero c hc
      rw [hzero, add_zero]
    rw [hsum_split]
    -- The remaining sum runs over c with `act c` an active mixed anchor.
    -- Auxiliary: `parityNat odd = k % 2`.
    have hparity_odd_eq_kmod2 : parityNat odd = k % 2 := by
      simp only [parityNat, hodd_def]
      rcases Nat.mod_two_eq_zero_or_one k with hj | hj
      · simp [hj]
      · simp [hj]
    -- act a = a when a has parity `k % 2`.
    have hact_self : ∀ a : Fin p.z, a.val % 2 = k % 2 → act a = a := by
      intro a ha_par
      simp only [hact_def, activeAnchor]
      have hpar_a : a.val % 2 = parityNat odd := by rw [hparity_odd_eq_kmod2]; exact ha_par
      simp [hpar_a]
    -- act (a+1) = a when a has parity `k % 2` (since (a+1) has opposite parity).
    have hact_succ : ∀ a : Fin p.z, a.val % 2 = k % 2 → act (a + 1) = a := by
      intro a ha_par
      simp only [hact_def, activeAnchor]
      have hpar_a : a.val % 2 = parityNat odd := by rw [hparity_odd_eq_kmod2]; exact ha_par
      have hpar_a1 : (a + 1).val % 2 ≠ parityNat odd :=
        (parity_add_one_ne_parity_iff p odd a).mpr hpar_a
      simp [hpar_a1]
    -- `c ∈ filter isMixed ↔ act c ∈ activeMixed p k S`.
    have h_isMixed_iff : ∀ c : Fin p.z,
        isMixed c ↔ act c ∈ activeMixed p k S := by
      intro c
      constructor
      · intro hmix
        simp only [activeMixed, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hact_par c, hmix⟩
      · intro ha
        simp only [activeMixed, Finset.mem_filter, Finset.mem_univ, true_and] at ha
        exact ha.2
    -- `MapsTo` for sum_fiberwise.
    have h_mapsTo : ∀ c ∈ (Finset.univ.filter (fun c => isMixed c)), act c ∈ activeMixed p k S := by
      intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
      exact (h_isMixed_iff c).mp hc
    -- For each a ∈ activeMixed p k S, the fiber `(filter isMixed univ).filter (act · = a)`
    -- equals `{a, a+1}` (as a Finset). Indeed:
    -- • `act a = a` (parity match) and `isMixed a` (since act a = a, the seam is mixed by ha).
    -- • `act (a+1) = a` and `isMixed (a+1)` (since act (a+1) = a, same seam check).
    -- • For any other c with `act c = a`, the iff `activeAnchor_eq_iff_eq_or_succ` forces
    --   c ∈ {a, a+1}.
    have h_fiber_eq : ∀ a ∈ activeMixed p k S,
        ((Finset.univ : Finset (Fin p.z)).filter (fun c => isMixed c)).filter
          (fun c => act c = a) = ({a, a + 1} : Finset (Fin p.z)) := by
      intro a ha
      have ha_par : a.val % 2 = k % 2 := by
        simp only [activeMixed, Finset.mem_filter, Finset.mem_univ, true_and] at ha
        exact ha.1
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
                 Finset.mem_singleton]
      constructor
      · rintro ⟨_hmix, hca⟩
        -- act c = a, so by activeAnchor_eq_iff_eq_or_succ: c = a or c = a+1.
        have ha_par' : a.val % 2 = parityNat odd := by
          rw [hparity_odd_eq_kmod2]; exact ha_par
        have h_iff := activeAnchor_eq_iff_eq_or_succ p odd a c
        exact (h_iff ha_par').mp hca
      · rintro (hca_eq | hca_eq)
        · -- c = a.  Need isMixed c (after rewrite) and act c = a.
          rw [hca_eq]
          have hacta : act a = a := hact_self a ha_par
          refine ⟨?_, hacta⟩
          have h_iff := h_isMixed_iff a
          have : act a ∈ activeMixed p k S := by rw [hacta]; exact ha
          exact h_iff.mpr this
        · -- c = a+1.
          rw [hca_eq]
          have hacta1 : act (a + 1) = a := hact_succ a ha_par
          refine ⟨?_, hacta1⟩
          have h_iff := h_isMixed_iff (a + 1)
          have : act (a + 1) ∈ activeMixed p k S := by rw [hacta1]; exact ha
          exact h_iff.mpr this
    -- Apply Finset.sum_fiberwise_of_maps_to.
    have h_fiberwise :
        ∑ c ∈ ((Finset.univ : Finset (Fin p.z)).filter (fun c => isMixed c)),
            ((if block p c ⊆ S' then (1 : ℝ) else 0) -
              (if block p c ⊆ S then (1 : ℝ) else 0)) =
        ∑ a ∈ activeMixed p k S,
          ∑ c ∈ (((Finset.univ : Finset (Fin p.z)).filter (fun c => isMixed c)).filter
            (fun c => act c = a)),
            ((if block p c ⊆ S' then (1 : ℝ) else 0) -
              (if block p c ⊆ S then (1 : ℝ) else 0)) := by
      rw [← Finset.sum_fiberwise_of_maps_to h_mapsTo
        (fun c : Fin p.z =>
          ((if block p c ⊆ S' then (1 : ℝ) else 0) -
            (if block p c ⊆ S then (1 : ℝ) else 0)))]
    rw [h_fiberwise]
    -- Now compute the per-anchor inner sum.
    apply Finset.sum_congr rfl
    intro a ha
    rw [h_fiber_eq a ha]
    -- The fiber {a, a+1} (Finset): a and a+1 are distinct (parity).
    have ha_par : a.val % 2 = k % 2 := by
      simp only [activeMixed, Finset.mem_filter, Finset.mem_univ, true_and] at ha
      exact ha.1
    have h_a_ne_a1 : a ≠ a + 1 := by
      intro he
      have hpar_eq : a.val % 2 = (a + 1).val % 2 := by rw [← he]
      have hpar_ne : (a + 1).val % 2 ≠ a.val % 2 := by
        have hpar_odd : a.val % 2 = parityNat odd := by
          rw [hparity_odd_eq_kmod2]; exact ha_par
        have hpar_a1_ne : (a + 1).val % 2 ≠ parityNat odd :=
          (parity_add_one_ne_parity_iff p odd a).mpr hpar_odd
        rw [hpar_odd]; exact hpar_a1_ne
      exact hpar_ne hpar_eq.symm
    rw [Finset.sum_pair h_a_ne_a1]
    -- Inner sum: δ(a) + δ(a+1).
    -- A_(k+1)T = S' is contig (hcS').  Use block_pair_subset_iff_cliqueRestrict_univ /
    -- not_block_pair_subset_iff_cliqueRestrict_empty_of_contig on S'.
    -- Cases on (block a ⊆ S', block (a+1) ⊆ S').
    -- block_pair_subset_iff_cliqueRestrict_univ p a S' : (ba ∧ ba1) ↔ cR_a = univ.
    -- not_block_pair_subset_iff_cliqueRestrict_empty_of_contig p a S' hcS' :
    --   (¬ba ∧ ¬ba1) ↔ cR_a = ∅.
    -- Need: ([block a ⊆ S'] + [block (a+1) ⊆ S']) - ([block a ⊆ S] + [block (a+1) ⊆ S])
    --     = [cR_a S' = univ] - [cR_a S' = ∅].
    -- On S (which has mixed seam at a): exactly one of (block a ⊆ S, block (a+1) ⊆ S) holds.
    -- This follows from `mixed_active_seam_eq_boundary` indirectly, or directly: S is contig,
    -- so block-aligned, so each block is ⊆ S or disjoint.  By mixed seam, neither both
    -- ⊆ S nor both disjoint.  So exactly one is ⊆ S (the other is disjoint, hence not ⊆).
    -- Hence [block a ⊆ S] + [block (a+1) ⊆ S] = 1.
    have h_mixed_a : ¬ (block p a ∪ block p (a + 1) ⊆ S ∨
                       Disjoint (block p a ∪ block p (a + 1)) S) := by
      simp only [activeMixed, Finset.mem_filter, Finset.mem_univ, true_and] at ha
      exact ha.2
    -- Block-aligned dichotomy for contig S.
    have h_block_dichS : ∀ c : Fin p.z, block p c ⊆ S ∨ Disjoint (block p c) S := by
      intro c
      obtain ⟨b, m, _hm_le, hS_eq⟩ := hcS
      classical
      by_cases hc_in : ∃ i ∈ Finset.range m,
          c = ⟨(b.val + i) % p.z, Nat.mod_lt _ p.hz_pos⟩
      · left
        obtain ⟨i, hi_range, hc_eq⟩ := hc_in
        intro v hv
        rw [hS_eq, Finset.mem_biUnion]
        exact ⟨i, hi_range, hc_eq ▸ hv⟩
      · right
        rw [hS_eq, Finset.disjoint_right]
        intro v hv hv_blockc
        rw [Finset.mem_biUnion] at hv
        obtain ⟨i, hi_range, hv_block⟩ := hv
        apply hc_in
        refine ⟨i, hi_range, ?_⟩
        rw [mem_block] at hv_blockc hv_block
        rw [← hv_blockc, hv_block]
    -- Block-aligned dichotomy: block c ⊆ S' ∨ disjoint, since S' is contig.
    have h_block_dichS' : ∀ c : Fin p.z, block p c ⊆ S' ∨ Disjoint (block p c) S' := by
      intro c
      obtain ⟨b, m, _hm_le, hS'_eq⟩ := hcS'
      classical
      by_cases hc_in : ∃ i ∈ Finset.range m,
          c = ⟨(b.val + i) % p.z, Nat.mod_lt _ p.hz_pos⟩
      · left
        obtain ⟨i, hi_range, hc_eq⟩ := hc_in
        intro v hv
        rw [hS'_eq, Finset.mem_biUnion]
        exact ⟨i, hi_range, hc_eq ▸ hv⟩
      · right
        rw [hS'_eq, Finset.disjoint_right]
        intro v hv hv_blockc
        rw [Finset.mem_biUnion] at hv
        obtain ⟨i, hi_range, hv_block⟩ := hv
        apply hc_in
        refine ⟨i, hi_range, ?_⟩
        rw [mem_block] at hv_blockc hv_block
        rw [← hv_blockc, hv_block]
    -- Mixed seam at a in S: neither both ⊆ S nor both disjoint from S; combined with the
    -- per-block dichotomy, exactly one of (block a ⊆ S, block (a+1) ⊆ S) holds.
    have hblock_a_ne : (block p a).Nonempty := by
      have := card_block p a
      exact Finset.card_pos.mp (this ▸ p.hk_pos)
    have hblock_a1_ne : (block p (a + 1)).Nonempty := by
      have := card_block p (a + 1)
      exact Finset.card_pos.mp (this ▸ p.hk_pos)
    -- For each side, derive a tight characterization of which case obtains on S.
    have h_nsub_iff_disj_S : ∀ c : Fin p.z,
        ¬ block p c ⊆ S ↔ Disjoint (block p c) S := by
      intro c
      constructor
      · intro hns
        rcases h_block_dichS c with hin | hdisj
        · exact absurd hin hns
        · exact hdisj
      · intro hdisj hsub
        have hbc : (block p c).Nonempty := by
          have := card_block p c
          exact Finset.card_pos.mp (this ▸ p.hk_pos)
        obtain ⟨v, hv⟩ := hbc
        exact (Finset.disjoint_left.mp hdisj hv) (hsub hv)
    have h_nsub_iff_disj_S' : ∀ c : Fin p.z,
        ¬ block p c ⊆ S' ↔ Disjoint (block p c) S' := by
      intro c
      constructor
      · intro hns
        rcases h_block_dichS' c with hin | hdisj
        · exact absurd hin hns
        · exact hdisj
      · intro hdisj hsub
        have hbc : (block p c).Nonempty := by
          have := card_block p c
          exact Finset.card_pos.mp (this ▸ p.hk_pos)
        obtain ⟨v, hv⟩ := hbc
        exact (Finset.disjoint_left.mp hdisj hv) (hsub hv)
    -- On S: exactly one of (block a ⊆ S, block (a+1) ⊆ S) holds.
    -- Case A: ba ⊆ S, ba1 ⊆ S ⟹ union ⊆ S, contradicts mixed.
    -- Case B: ba ⊄ S, ba1 ⊄ S ⟹ both disjoint ⟹ union disjoint, contradicts mixed.
    -- So exactly one ⊆.
    have h_eq_S : (block p a ⊆ S) ∨ (block p (a + 1) ⊆ S) := by
      by_contra hno
      push Not at hno
      obtain ⟨h_nba, h_nba1⟩ := hno
      apply h_mixed_a
      right
      have hda : Disjoint (block p a) S := (h_nsub_iff_disj_S a).mp h_nba
      have hda1 : Disjoint (block p (a + 1)) S := (h_nsub_iff_disj_S (a + 1)).mp h_nba1
      rw [Finset.disjoint_union_left]
      exact ⟨hda, hda1⟩
    have h_not_both_S : ¬ (block p a ⊆ S ∧ block p (a + 1) ⊆ S) := by
      rintro ⟨h1, h2⟩
      apply h_mixed_a
      left
      exact Finset.union_subset h1 h2
    -- Sum on S: exactly one of [block a ⊆ S], [block (a+1) ⊆ S] is 1, so sum = 1.
    have hsum_S :
        (if block p a ⊆ S then (1 : ℝ) else 0) +
        (if block p (a + 1) ⊆ S then (1 : ℝ) else 0) = 1 := by
      rcases h_eq_S with h1 | h2
      · -- block a ⊆ S
        have h2_n : ¬ block p (a + 1) ⊆ S := fun h => h_not_both_S ⟨h1, h⟩
        rw [if_pos h1, if_neg h2_n]; ring
      · have h1_n : ¬ block p a ⊆ S := fun h => h_not_both_S ⟨h, h2⟩
        rw [if_neg h1_n, if_pos h2]; ring
    -- Now case on (block a ⊆ S', block (a+1) ⊆ S').  Four cases:
    --   (T, T) ⟹ cR_a S' = univ  (and ≠ ∅ since blocks are nonempty)
    --   (F, F) ⟹ cR_a S' = ∅  (via not_block_pair_subset_iff_cliqueRestrict_empty_of_contig)
    --   (T, F) or (F, T) ⟹ cR_a S' ∉ {univ, ∅}
    have h_univ_ne_empty : (Finset.univ : Finset (CliqueVertex p.k)) ≠ ∅ := by
      have h2k_pos : 0 < 2 * p.k := by have := p.hk_pos; omega
      have hnonempty : (Finset.univ : Finset (CliqueVertex p.k)).Nonempty :=
        ⟨⟨0, h2k_pos⟩, Finset.mem_univ _⟩
      exact (Finset.nonempty_iff_ne_empty.mp hnonempty)
    -- Goal: [cR_a S' = univ] - [cR_a S' = ∅] = δ a + δ (a + 1).
    symm
    -- Rearrange to extract the "+1 on S" piece.
    have hgoal_eq :
        ((if block p a ⊆ S' then (1 : ℝ) else 0) -
            (if block p a ⊆ S then (1 : ℝ) else 0)) +
         ((if block p (a + 1) ⊆ S' then (1 : ℝ) else 0) -
            (if block p (a + 1) ⊆ S then (1 : ℝ) else 0)) =
        ((if block p a ⊆ S' then (1 : ℝ) else 0) +
         (if block p (a + 1) ⊆ S' then (1 : ℝ) else 0)) -
        ((if block p a ⊆ S then (1 : ℝ) else 0) +
         (if block p (a + 1) ⊆ S then (1 : ℝ) else 0)) := by ring
    rw [hgoal_eq, hsum_S]
    -- Case on (block a ⊆ S', block (a+1) ⊆ S').
    by_cases hba_S' : block p a ⊆ S'
    · by_cases hba1_S' : block p (a + 1) ⊆ S'
      · -- Both ⊆ S': cR_a S' = univ; and ≠ ∅.
        have h_univ : cliqueRestrict p a S' = Finset.univ :=
          (block_pair_subset_iff_cliqueRestrict_univ p a S').mp ⟨hba_S', hba1_S'⟩
        have h_ne_empty : cliqueRestrict p a S' ≠ ∅ := by
          rw [h_univ]; exact h_univ_ne_empty
        rw [if_pos hba_S', if_pos hba1_S', if_pos h_univ, if_neg h_ne_empty]
        ring
      · -- (T, F): cR_a S' ∉ {univ, ∅}.
        have h_ne_univ : cliqueRestrict p a S' ≠ Finset.univ := by
          intro heq
          have hpair : block p a ⊆ S' ∧ block p (a + 1) ⊆ S' :=
            (block_pair_subset_iff_cliqueRestrict_univ p a S').mpr heq
          exact hba1_S' hpair.2
        have h_ne_empty : cliqueRestrict p a S' ≠ ∅ := by
          intro heq
          have hboth : ¬ block p a ⊆ S' ∧ ¬ block p (a + 1) ⊆ S' :=
            (not_block_pair_subset_iff_cliqueRestrict_empty_of_contig p a S' hcS').mpr heq
          exact hboth.1 hba_S'
        rw [if_pos hba_S', if_neg hba1_S', if_neg h_ne_univ, if_neg h_ne_empty]
        ring
    · by_cases hba1_S' : block p (a + 1) ⊆ S'
      · -- (F, T): cR_a S' ∉ {univ, ∅}.
        have h_ne_univ : cliqueRestrict p a S' ≠ Finset.univ := by
          intro heq
          have hpair : block p a ⊆ S' ∧ block p (a + 1) ⊆ S' :=
            (block_pair_subset_iff_cliqueRestrict_univ p a S').mpr heq
          exact hba_S' hpair.1
        have h_ne_empty : cliqueRestrict p a S' ≠ ∅ := by
          intro heq
          have hboth : ¬ block p a ⊆ S' ∧ ¬ block p (a + 1) ⊆ S' :=
            (not_block_pair_subset_iff_cliqueRestrict_empty_of_contig p a S' hcS').mpr heq
          exact hboth.2 hba1_S'
        rw [if_neg hba_S', if_pos hba1_S', if_neg h_ne_univ, if_neg h_ne_empty]
        ring
      · -- Both ⊄ S': cR_a S' = ∅.
        have h_empty : cliqueRestrict p a S' = ∅ :=
          (not_block_pair_subset_iff_cliqueRestrict_empty_of_contig p a S' hcS').mp
            ⟨hba_S', hba1_S'⟩
        have h_ne_univ : cliqueRestrict p a S' ≠ Finset.univ := by
          rw [h_empty]; exact (Ne.symm h_univ_ne_empty)
        rw [if_neg hba_S', if_neg hba1_S', if_neg h_ne_univ, if_pos h_empty]
        ring
  -- ---- INDUCTION ----
  induction j with
  | zero =>
    filter_upwards [hA₀] with ω hω0 _hlive
    show boundaryDeltaProcess p vm 0 ω = (blockCount p vm 0 ω : ℝ)
    -- LHS: ((p.z / 2 : ℕ) : ℝ) by def.
    -- RHS: ((p.z / 2 : ℕ) : ℝ) by blockCount_initial (a.e. initial condition).
    have hbc0 : blockCount p vm 0 ω = p.z / 2 := blockCount_initial p vm hω0
    show ((p.z / 2 : ℕ) : ℝ) = (blockCount p vm 0 ω : ℝ)
    rw [hbc0]
  | succ j ih =>
    -- IH (a.e.): on `{arcFailTime > j}`, `W̃_j = blockCount j`.
    -- New null set: `badStep j` (μ = 0).
    have hbad_zero : (vm.μ : Measure _) (badStep j) = 0 := hbadStep_zero j
    -- Combine IH with `badStep j` ∈ null.
    filter_upwards [ih, (MeasureTheory.ae_iff (μ := (vm.μ : Measure Ω))
      (p := fun ω => ω ∉ badStep j)).mpr (by
        rw [show {ω | ¬ ω ∉ badStep j} = badStep j from by ext; simp]; exact hbad_zero)]
      with ω ih_ω hnbad hlive
    -- hlive : (j + 1 : WithTop ℕ) < arcFailTime p vm ω
    have hlive_j : (j : WithTop ℕ) < arcFailTime p vm ω := by
      have hcast : ((j + 1 : ℕ) : WithTop ℕ) = ((j : ℕ) + 1 : WithTop ℕ) := by
        push_cast; rfl
      have : ((j + 1 : ℕ) : WithTop ℕ) < arcFailTime p vm ω := hlive
      exact h_live_mono ω j this
    -- A_jT and A_(j+1)T both contig.
    have h_arc_j : IsContiguousArc p (vm.opinionZeroSet (j * p.T) ω) := h_arc_before ω j hlive_j
    have h_arc_j1 : IsContiguousArc p (vm.opinionZeroSet ((j + 1) * p.T) ω) := by
      have : ((j + 1 : ℕ) : WithTop ℕ) < arcFailTime p vm ω := hlive
      exact h_arc_before ω (j + 1) this
    -- opP ≠ 0 at step j (since ω ∉ badStep j).
    have hopP_ne : VoterModel.opinionProcess₂ (lowerBoundGraph p) (j * p.T) p.T
        (vm.opinionZeroSet (j * p.T) ω) (vm.opinionZeroSet ((j + 1) * p.T) ω) ≠ 0 := h_opP_ne_off_badStep j ω hnbad
    -- IH: W̃_j ω = blockCount j ω.
    have ihW : boundaryDeltaProcess p vm j ω = (blockCount p vm j ω : ℝ) := ih_ω hlive_j
    -- Apply hkey at S = A_jT ω, S' = A_(j+1)T ω.
    have hkey_inst := hkey j (vm.opinionZeroSet (j * p.T) ω) (vm.opinionZeroSet ((j + 1) * p.T) ω) h_arc_j h_arc_j1 hopP_ne
    -- Unfold boundaryDeltaProcess at j+1.
    show boundaryDeltaProcess p vm (j + 1) ω = (blockCount p vm (j + 1) ω : ℝ)
    show boundaryDeltaProcess p vm j ω +
        boundaryDelta p j (vm.opinionZeroSet (j * p.T) ω) (vm.opinionZeroSet ((j + 1) * p.T) ω) =
      (blockCount p vm (j + 1) ω : ℝ)
    rw [ihW, hkey_inst, hbc_to_set j ω, hbc_to_set (j + 1) ω]
    ring

/-! ### W̃-process infrastructure

The following six lemmas establish that `boundaryDeltaProcess` (a.k.a. `W̃`) is a
martingale w.r.t. `boundaryFiltration`, with pointwise bounded increments `|ΔW̃| ≤ 2`.
The structure mirrors `stoppedBlockCount_*` but is dramatically simpler: there is no
`arcFailTime` freezing, since `boundaryDelta` is defined to vanish off contiguous arcs. -/

/-- `boundaryDeltaProcess 0 = z/2`: holds by definition (no cases needed). -/
private theorem boundaryDeltaProcess_zero (p : Params) {Ω : Type} [MeasurableSpace Ω]
    (vm : TemporalGraph.VoterModelAbstract (lowerBoundGraph p) 2 Ω) (ω : Ω) :
    boundaryDeltaProcess p vm 0 ω = ((p.z / 2 : ℕ) : ℝ) := by
  rfl

/-- Adaptedness of `boundaryDeltaProcess` to `boundaryFiltration`.

For each `j`, `boundaryDeltaProcess p vm j` is `(boundaryFiltration p vm).seq j`-strongly
measurable. Proof: induction on `j`; at step `j+1`, the process equals
`W̃_j + boundaryDelta p j (A_{jT}, A_{(j+1)T})`. Both summands are strongly measurable
w.r.t. `vm.ℱ ((j+1) * p.T)`: the first by widening from `j*p.T`, the second since both
`A_{jT}` and `A_{(j+1)T}` are measurable at time `(j+1)*p.T`. -/
private theorem boundaryDeltaProcess_adapted (p : Params) {Ω : Type} [MeasurableSpace Ω]
    (vm : TemporalGraph.VoterModelAbstract (lowerBoundGraph p) 2 Ω) :
    MeasureTheory.StronglyAdapted (boundaryFiltration p vm) (boundaryDeltaProcess p vm) := by
  classical
  intro j
  show StronglyMeasurable[vm.ℱ (j * p.T)] (boundaryDeltaProcess p vm j)
  induction j with
  | zero =>
    -- boundaryDeltaProcess 0 = const ((p.z / 2 : ℕ) : ℝ)
    have h0 : boundaryDeltaProcess p vm 0 = fun _ : Ω => ((p.z / 2 : ℕ) : ℝ) := by
      funext ω; rfl
    rw [h0]
    exact stronglyMeasurable_const
  | succ j ih =>
    -- boundaryDeltaProcess (j+1) ω = boundaryDeltaProcess j ω + boundaryDelta j (A_jT ω) (A_(j+1)T ω)
    have hexpand : boundaryDeltaProcess p vm (j + 1) =
        fun ω => boundaryDeltaProcess p vm j ω +
          boundaryDelta p j (vm.opinionZeroSet (j * p.T) ω) (vm.opinionZeroSet ((j + 1) * p.T) ω) := by
      funext ω; rfl
    rw [hexpand]
    have hWj : StronglyMeasurable[vm.ℱ ((j + 1) * p.T)] (boundaryDeltaProcess p vm j) :=
      ih.mono (vm.ℱ.mono (Nat.mul_le_mul_right p.T (Nat.le_succ j)))
    -- The boundaryDelta term is measurable from (A_jT, A_(j+1)T), both measurable at (j+1)*T.
    have hAjm : Measurable[vm.ℱ ((j + 1) * p.T)] (vm.opinionZeroSet (j * p.T)) :=
      ((VoterModelAbstract.A_stronglyAdapted vm (j * p.T)).measurable).mono
        (vm.ℱ.mono (Nat.mul_le_mul_right p.T (Nat.le_succ j))) le_rfl
    have hAj1m : Measurable[vm.ℱ ((j + 1) * p.T)] (vm.opinionZeroSet ((j + 1) * p.T)) :=
      (VoterModelAbstract.A_stronglyAdapted vm ((j + 1) * p.T)).measurable
    have hprodm : Measurable[vm.ℱ ((j + 1) * p.T)]
        (fun ω => (vm.opinionZeroSet (j * p.T) ω, vm.opinionZeroSet ((j + 1) * p.T) ω)) :=
      hAjm.prodMk hAj1m
    have hΔm : Measurable[vm.ℱ ((j + 1) * p.T)]
        (fun ω => boundaryDelta p j (vm.opinionZeroSet (j * p.T) ω) (vm.opinionZeroSet ((j + 1) * p.T) ω)) := by
      have : (fun ω => boundaryDelta p j (vm.opinionZeroSet (j * p.T) ω) (vm.opinionZeroSet ((j + 1) * p.T) ω)) =
          (fun st : Finset (VertexSet p) × Finset (VertexSet p) => boundaryDelta p j st.1 st.2) ∘
            (fun ω => (vm.opinionZeroSet (j * p.T) ω, vm.opinionZeroSet ((j + 1) * p.T) ω)) := by
        funext ω; rfl
      rw [this]
      exact Measurable.of_discrete.comp hprodm
    exact hWj.add hΔm.stronglyMeasurable

/-- A pointwise bound: `|boundaryDeltaProcess p vm j ω| ≤ (p.z / 2 : ℕ) + j * p.z`.

Used to derive integrability. By induction on `j`: at the step, `|W̃_{j+1}| ≤ |W̃_j| +
|boundaryDelta| ≤ (z/2 + j·z) + z`, and `(z/2 + j·z) + z ≤ z/2 + (j+1)·z`. -/
private theorem boundaryDeltaProcess_abs_le (p : Params) {Ω : Type} [MeasurableSpace Ω]
    (vm : TemporalGraph.VoterModelAbstract (lowerBoundGraph p) 2 Ω) (j : ℕ) (ω : Ω) :
    |boundaryDeltaProcess p vm j ω| ≤ ((p.z / 2 : ℕ) : ℝ) + (j : ℝ) * (p.z : ℝ) := by
  classical
  induction j with
  | zero =>
    show |boundaryDeltaProcess p vm 0 ω| ≤ ((p.z / 2 : ℕ) : ℝ) + ((0 : ℕ) : ℝ) * (p.z : ℝ)
    have h0 : boundaryDeltaProcess p vm 0 ω = ((p.z / 2 : ℕ) : ℝ) := rfl
    rw [h0, Nat.cast_zero, zero_mul, add_zero, abs_of_nonneg (by positivity)]
  | succ j ih =>
    have hexp : boundaryDeltaProcess p vm (j + 1) ω =
        boundaryDeltaProcess p vm j ω +
          boundaryDelta p j (vm.opinionZeroSet (j * p.T) ω) (vm.opinionZeroSet ((j + 1) * p.T) ω) := rfl
    rw [hexp]
    -- |boundaryDelta| ≤ p.z (same bound as in L101).
    have hΔ_le : |boundaryDelta p j (vm.opinionZeroSet (j * p.T) ω) (vm.opinionZeroSet ((j + 1) * p.T) ω)| ≤
        (p.z : ℝ) := by
      simp only [boundaryDelta]
      split_ifs with hcont
      · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        have hterm_le : ∀ a ∈ activeMixed p j (vm.opinionZeroSet (j * p.T) ω),
            |(if cliqueRestrict p a (vm.opinionZeroSet ((j + 1) * p.T) ω) = Finset.univ then (1 : ℝ) else 0) -
              (if cliqueRestrict p a (vm.opinionZeroSet ((j + 1) * p.T) ω) = ∅ then (1 : ℝ) else 0)| ≤ 1 := by
          intro a _
          rcases em (cliqueRestrict p a (vm.opinionZeroSet ((j + 1) * p.T) ω) = Finset.univ) with h1 | h1
          · rw [if_pos h1]
            rcases em (cliqueRestrict p a (vm.opinionZeroSet ((j + 1) * p.T) ω) = ∅) with h2 | h2
            · rw [if_pos h2]; norm_num
            · rw [if_neg h2]; norm_num
          · rw [if_neg h1]
            rcases em (cliqueRestrict p a (vm.opinionZeroSet ((j + 1) * p.T) ω) = ∅) with h2 | h2
            · rw [if_pos h2]; norm_num
            · rw [if_neg h2]; norm_num
        calc ∑ a ∈ activeMixed p j (vm.opinionZeroSet (j * p.T) ω),
                |(if cliqueRestrict p a (vm.opinionZeroSet ((j + 1) * p.T) ω) = Finset.univ then (1 : ℝ) else 0) -
                  (if cliqueRestrict p a (vm.opinionZeroSet ((j + 1) * p.T) ω) = ∅ then (1 : ℝ) else 0)|
              ≤ ∑ _a ∈ activeMixed p j (vm.opinionZeroSet (j * p.T) ω), (1 : ℝ) :=
                Finset.sum_le_sum hterm_le
            _ = ((activeMixed p j (vm.opinionZeroSet (j * p.T) ω)).card : ℝ) := by
                rw [Finset.sum_const, nsmul_eq_mul, mul_one]
            _ ≤ ((Finset.univ : Finset (Fin p.z)).card : ℝ) := by
                exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
            _ = (p.z : ℝ) := by rw [Finset.card_univ, Fintype.card_fin]
      · simp [abs_zero, Nat.cast_nonneg]
    calc |boundaryDeltaProcess p vm j ω +
            boundaryDelta p j (vm.opinionZeroSet (j * p.T) ω) (vm.opinionZeroSet ((j + 1) * p.T) ω)|
        ≤ |boundaryDeltaProcess p vm j ω| +
            |boundaryDelta p j (vm.opinionZeroSet (j * p.T) ω) (vm.opinionZeroSet ((j + 1) * p.T) ω)| := abs_add_le _ _
      _ ≤ (((p.z / 2 : ℕ) : ℝ) + (j : ℝ) * (p.z : ℝ)) + (p.z : ℝ) := add_le_add ih hΔ_le
      _ = ((p.z / 2 : ℕ) : ℝ) + ((j + 1 : ℕ) : ℝ) * (p.z : ℝ) := by push_cast; ring

/-- Integrability of `boundaryDeltaProcess j`.

`W̃_j` is strongly measurable (by `_adapted`) and pointwise bounded by `z/2 + j·z`
(by `_abs_le`), hence integrable. -/
private theorem boundaryDeltaProcess_integrable (p : Params) {Ω : Type} [MeasurableSpace Ω]
    (vm : TemporalGraph.VoterModelAbstract (lowerBoundGraph p) 2 Ω) (j : ℕ) :
    MeasureTheory.Integrable (boundaryDeltaProcess p vm j) vm.μ :=
  MeasureTheory.Integrable.of_bound
    (boundaryDeltaProcess_adapted p vm).stronglyMeasurable.aestronglyMeasurable
    (((p.z / 2 : ℕ) : ℝ) + (j : ℝ) * (p.z : ℝ))
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]
      exact boundaryDeltaProcess_abs_le p vm j ω)

/-- Conditional expectation step for `boundaryDeltaProcess`.

`E[W̃_{j+1} | ℱ_{jT}] =ᵐ W̃_j`. Proof: `W̃_{j+1} = W̃_j + boundaryDelta j (A_{jT}, A_{(j+1)T})`;
condExp distributes over sums; the W̃_j term passes through `condExp_of_stronglyMeasurable`
(it is adapted and integrable); the boundaryDelta term is 0 a.e. by L101
(`boundaryDelta_condExp_zero`). -/
private theorem boundaryDeltaProcess_condExp (p : Params)
    {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (vm : TemporalGraph.VoterModelAbstract (lowerBoundGraph p) 2 Ω) (j : ℕ) :
    boundaryDeltaProcess p vm j =ᵐ[(vm.μ : Measure _)]
      (vm.μ : Measure _)[boundaryDeltaProcess p vm (j + 1) | (boundaryFiltration p vm).seq j] := by
  classical
  haveI : IsProbabilityMeasure (vm.μ : Measure Ω) := inferInstance
  -- σ-algebra at time j*T (defeq to (boundaryFiltration p vm).seq j).
  have hfilt_le : (boundaryFiltration p vm).seq j ≤ (inferInstance : MeasurableSpace Ω) :=
    (boundaryFiltration p vm).le j
  -- W̃_j adapted and integrable.
  have hW_sm : StronglyMeasurable[(boundaryFiltration p vm).seq j] (boundaryDeltaProcess p vm j) :=
    boundaryDeltaProcess_adapted p vm j
  have hW_int : Integrable (boundaryDeltaProcess p vm j) vm.μ :=
    boundaryDeltaProcess_integrable p vm j
  -- The boundaryDelta increment is integrable (bounded by p.z, same as in L101).
  set f : Ω → ℝ := fun ω =>
    boundaryDelta p j (vm.opinionZeroSet (j * p.T) ω) (vm.opinionZeroSet ((j + 1) * p.T) ω) with hf_def
  have hAjm : Measurable (vm.opinionZeroSet (j * p.T)) :=
    (VoterModelAbstract.A_stronglyAdapted vm (j * p.T)).measurable.mono (vm.ℱ.le _) le_rfl
  have hAj1m : Measurable (vm.opinionZeroSet ((j + 1) * p.T)) :=
    (VoterModelAbstract.A_stronglyAdapted vm ((j + 1) * p.T)).measurable.mono (vm.ℱ.le _) le_rfl
  have hf_sm : StronglyMeasurable f := by
    have hprodm : Measurable
        (fun ω => (vm.opinionZeroSet (j * p.T) ω, vm.opinionZeroSet ((j + 1) * p.T) ω)) :=
      hAjm.prodMk hAj1m
    have hcomp : Measurable f := by
      have heq : f = (fun st : Finset (VertexSet p) × Finset (VertexSet p) =>
          boundaryDelta p j st.1 st.2) ∘
          (fun ω => (vm.opinionZeroSet (j * p.T) ω, vm.opinionZeroSet ((j + 1) * p.T) ω)) := by
        funext ω; rfl
      rw [heq]
      exact Measurable.of_discrete.comp hprodm
    exact hcomp.stronglyMeasurable
  have hf_bound : ∀ ω, |f ω| ≤ (p.z : ℝ) := by
    intro ω
    simp only [hf_def, boundaryDelta]
    split_ifs with hcont
    · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hterm_le : ∀ a ∈ activeMixed p j (vm.opinionZeroSet (j * p.T) ω),
          |(if cliqueRestrict p a (vm.opinionZeroSet ((j + 1) * p.T) ω) = Finset.univ then (1 : ℝ) else 0) -
            (if cliqueRestrict p a (vm.opinionZeroSet ((j + 1) * p.T) ω) = ∅ then (1 : ℝ) else 0)| ≤ 1 := by
        intro a _
        rcases em (cliqueRestrict p a (vm.opinionZeroSet ((j + 1) * p.T) ω) = Finset.univ) with h1 | h1
        · rw [if_pos h1]
          rcases em (cliqueRestrict p a (vm.opinionZeroSet ((j + 1) * p.T) ω) = ∅) with h2 | h2
          · rw [if_pos h2]; norm_num
          · rw [if_neg h2]; norm_num
        · rw [if_neg h1]
          rcases em (cliqueRestrict p a (vm.opinionZeroSet ((j + 1) * p.T) ω) = ∅) with h2 | h2
          · rw [if_pos h2]; norm_num
          · rw [if_neg h2]; norm_num
      calc ∑ a ∈ activeMixed p j (vm.opinionZeroSet (j * p.T) ω),
              |(if cliqueRestrict p a (vm.opinionZeroSet ((j + 1) * p.T) ω) = Finset.univ then (1 : ℝ) else 0) -
                (if cliqueRestrict p a (vm.opinionZeroSet ((j + 1) * p.T) ω) = ∅ then (1 : ℝ) else 0)|
            ≤ ∑ _a ∈ activeMixed p j (vm.opinionZeroSet (j * p.T) ω), (1 : ℝ) :=
              Finset.sum_le_sum hterm_le
          _ = ((activeMixed p j (vm.opinionZeroSet (j * p.T) ω)).card : ℝ) := by
              rw [Finset.sum_const, nsmul_eq_mul, mul_one]
          _ ≤ ((Finset.univ : Finset (Fin p.z)).card : ℝ) := by
              exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
          _ = (p.z : ℝ) := by rw [Finset.card_univ, Fintype.card_fin]
    · simp [abs_zero, Nat.cast_nonneg]
  have hf_int : Integrable f vm.μ :=
    MeasureTheory.Integrable.of_bound hf_sm.aestronglyMeasurable (p.z : ℝ)
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hf_bound ω)
  -- The definitional expansion: W̃_{j+1} = W̃_j + f.
  have hexpand : boundaryDeltaProcess p vm (j + 1) = boundaryDeltaProcess p vm j + f := by
    funext ω; rfl
  -- condExp distributes over the sum.
  have hadd :
      (vm.μ : Measure _)[boundaryDeltaProcess p vm (j + 1) | (boundaryFiltration p vm).seq j] =ᵐ[(vm.μ : Measure _)]
        (vm.μ : Measure _)[boundaryDeltaProcess p vm j | (boundaryFiltration p vm).seq j] +
        (vm.μ : Measure _)[f | (boundaryFiltration p vm).seq j] := by
    rw [hexpand]
    exact condExp_add hW_int hf_int _
  -- W̃_j is adapted: condExp returns itself.
  have hWcond :
      (vm.μ : Measure _)[boundaryDeltaProcess p vm j | (boundaryFiltration p vm).seq j] =
        boundaryDeltaProcess p vm j :=
    condExp_of_stronglyMeasurable hfilt_le hW_sm hW_int
  -- L101: condExp of boundaryDelta is 0 a.e. (w.r.t. vm.ℱ (j*p.T), defeq to seq j).
  have hΔcond :
      (vm.μ : Measure _)[f | (boundaryFiltration p vm).seq j] =ᵐ[(vm.μ : Measure _)] (0 : Ω → ℝ) := by
    have hL101 := boundaryDelta_condExp_zero p vm j
    -- Goal differs only by the σ-algebra spelling (defeq).
    show (vm.μ : Measure _)[f | vm.ℱ (j * p.T)] =ᵐ[(vm.μ : Measure _)] (0 : Ω → ℝ)
    exact hL101
  -- Combine.
  filter_upwards [hadd, hΔcond] with ω hadd_ω hΔcond_ω
  rw [hadd_ω, Pi.add_apply, hWcond, hΔcond_ω]
  simp

/-- `W̃` is a martingale w.r.t. `boundaryFiltration`. Combines _adapted, _integrable,
and _condExp via `martingale_nat`. -/
private theorem boundaryDeltaProcess_isMartingale (p : Params)
    {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (vm : TemporalGraph.VoterModelAbstract (lowerBoundGraph p) 2 Ω) :
    MeasureTheory.Martingale (boundaryDeltaProcess p vm) (boundaryFiltration p vm) vm.μ :=
  martingale_nat (boundaryDeltaProcess_adapted p vm) (boundaryDeltaProcess_integrable p vm)
    (boundaryDeltaProcess_condExp p vm)

/-- Pointwise bounded differences `|W̃_i − W̃_{i-1}| ≤ 2`.

By definition `W̃_i = W̃_{i-1} + boundaryDelta (i-1) (A_{(i-1)T}, A_{iT})`, so the difference
equals `boundaryDelta`. On contiguous `S`, the sum is over `activeMixed p (i-1) S ⊆
seamMixedAnchors p S`, which has cardinality `≤ 2` by `arc_anchors_card_le_two`. Each
summand lies in `{-1, 0, 1}`. On non-contiguous `S`, the `boundaryDelta` is 0. -/
private theorem boundaryDeltaProcess_diff_bd (p : Params)
    {Ω : Type} [MeasurableSpace Ω]
    (vm : TemporalGraph.VoterModelAbstract (lowerBoundGraph p) 2 Ω) (i : ℕ) (hi1 : 1 ≤ i) (ω : Ω) :
    |boundaryDeltaProcess p vm i ω - boundaryDeltaProcess p vm (i - 1) ω| ≤ 2 := by
  classical
  -- Rewrite i = (i-1) + 1 and unfold W̃_i.
  have hsucc : (i - 1) + 1 = i := Nat.succ_pred_eq_of_pos hi1
  -- The difference equals boundaryDelta at index (i-1).
  have hdiff_eq : boundaryDeltaProcess p vm i ω - boundaryDeltaProcess p vm (i - 1) ω =
      boundaryDelta p (i - 1) (vm.opinionZeroSet ((i - 1) * p.T) ω) (vm.opinionZeroSet (((i - 1) + 1) * p.T) ω) := by
    have heq : boundaryDeltaProcess p vm i ω =
        boundaryDeltaProcess p vm ((i - 1) + 1) ω := by rw [hsucc]
    rw [heq]
    show boundaryDeltaProcess p vm (i - 1) ω +
        boundaryDelta p (i - 1) (vm.opinionZeroSet ((i - 1) * p.T) ω) (vm.opinionZeroSet (((i - 1) + 1) * p.T) ω) -
        boundaryDeltaProcess p vm (i - 1) ω =
      boundaryDelta p (i - 1) (vm.opinionZeroSet ((i - 1) * p.T) ω) (vm.opinionZeroSet (((i - 1) + 1) * p.T) ω)
    ring
  rw [hdiff_eq]
  -- Bound boundaryDelta: split on IsContiguousArc.
  set S := vm.opinionZeroSet ((i - 1) * p.T) ω with hS_def
  set S' := vm.opinionZeroSet (((i - 1) + 1) * p.T) ω with hS'_def
  simp only [boundaryDelta]
  split_ifs with hcont
  · -- Contiguous S: ∑ over activeMixed, each summand ∈ [-1, 1], |activeMixed| ≤ 2.
    -- Bridge: activeMixed p (i-1) S ⊆ seamMixedAnchors p S.
    have hsub : activeMixed p (i - 1) S ⊆ seamMixedAnchors p S := by
      intro a ha
      simp only [activeMixed, Finset.mem_filter, Finset.mem_univ, true_and] at ha
      obtain ⟨_, h_mixed⟩ := ha
      simp only [seamMixedAnchors, Finset.mem_filter, Finset.mem_univ, true_and]
      -- Convert (a + 1 : Fin p.z) to ⟨(a.val + 1) % p.z, _⟩.
      have hsucc_eq : (a + 1 : Fin p.z) =
          (⟨(a.val + 1) % p.z, Nat.mod_lt _ p.hz_pos⟩ : Fin p.z) := by
        apply Fin.ext
        show (a + 1 : Fin p.z).val = (a.val + 1) % p.z
        rw [Fin.val_add]
        simp
      rw [← hsucc_eq]
      exact h_mixed
    have hcard_le : (activeMixed p (i - 1) S).card ≤ 2 :=
      (Finset.card_le_card hsub).trans (arc_anchors_card_le_two p S hcont)
    -- |∑ ...| ≤ ∑ |...| ≤ ∑ 1 = card ≤ 2.
    have hterm_le : ∀ a ∈ activeMixed p (i - 1) S,
        |(if cliqueRestrict p a S' = Finset.univ then (1 : ℝ) else 0) -
          (if cliqueRestrict p a S' = ∅ then (1 : ℝ) else 0)| ≤ 1 := by
      intro a _
      rcases em (cliqueRestrict p a S' = Finset.univ) with h1 | h1
      · rw [if_pos h1]
        rcases em (cliqueRestrict p a S' = ∅) with h2 | h2
        · rw [if_pos h2]; norm_num
        · rw [if_neg h2]; norm_num
      · rw [if_neg h1]
        rcases em (cliqueRestrict p a S' = ∅) with h2 | h2
        · rw [if_pos h2]; norm_num
        · rw [if_neg h2]; norm_num
    calc |∑ a ∈ activeMixed p (i - 1) S,
            ((if cliqueRestrict p a S' = Finset.univ then (1 : ℝ) else 0) -
              (if cliqueRestrict p a S' = ∅ then (1 : ℝ) else 0))|
        ≤ ∑ a ∈ activeMixed p (i - 1) S,
            |(if cliqueRestrict p a S' = Finset.univ then (1 : ℝ) else 0) -
              (if cliqueRestrict p a S' = ∅ then (1 : ℝ) else 0)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a ∈ activeMixed p (i - 1) S, (1 : ℝ) := Finset.sum_le_sum hterm_le
      _ = ((activeMixed p (i - 1) S).card : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ (2 : ℝ) := by exact_mod_cast hcard_le
  · -- Non-contiguous S: boundaryDelta = 0.
    show |(0 : ℝ)| ≤ 2
    norm_num

/-- A.e. variant of `goodArc_blockCount_deviation_sub` for `boundaryDeltaProcess`.

On `{∀ j ≤ N, IsContiguousArc at j·T}`, we have `(N : WithTop ℕ) < arcFailTime`
pointwise, so by `boundaryDeltaProcess_eq_blockCount_on_live` at index `N` (which is
an a.e. statement), `boundaryDeltaProcess N ω = blockCount N ω` a.e. Combined with
`boundaryDeltaProcess_zero` and `blockCount N ∈ {0, z}`, the deviation
`|W̃_N − W̃_0| ≥ z/2` holds a.e. on `goodArc ∩ {bc_N ∈ {0, z}}`.

Stated as `μ((goodArc ∩ {bc_N ∈ {0, z}}) \ {|W̃_N − W̃_0| ≥ z/2}) = 0`. -/
private theorem goodArc_boundaryDeltaProcess_deviation_sub_ae (p : Params)
    {Ω : Type} [MeasurableSpace Ω]
    (vm : TemporalGraph.VoterModelAbstract (lowerBoundGraph p) 2 Ω)
    (hA₀ : ∀ᵐ ω ∂(vm.μ : Measure Ω), vm.opinionZeroSet 0 ω = halfCutLow p) (N : ℕ) :
    (vm.μ : Measure _) (({ω | ∀ j ≤ N, IsContiguousArc p (vm.opinionZeroSet (j * p.T) ω)} ∩
            {ω | blockCount p vm N ω = 0 ∨ blockCount p vm N ω = p.z}) \
          {ω | |boundaryDeltaProcess p vm N ω -
                boundaryDeltaProcess p vm 0 ω| ≥ ((p.z / 2 : ℕ) : ℝ)}) = 0 := by
  classical
  -- The L102 null set: {ω | (↑N : WithTop ℕ) < arcFailTime ω ∧ W̃_N ω ≠ blockCount N ω}.
  set L102_bad : Set Ω :=
    {ω : Ω | (↑N : WithTop ℕ) < arcFailTime p vm ω ∧
              boundaryDeltaProcess p vm N ω ≠ (blockCount p vm N ω : ℝ)} with hL102_bad_def
  have hL102_bad_zero : (vm.μ : Measure _) L102_bad = 0 := by
    have hae := boundaryDeltaProcess_eq_blockCount_on_live p vm hA₀ N
    -- Convert ∀ᵐ to measure-of-negation = 0.
    rw [MeasureTheory.ae_iff] at hae
    -- {ω | ¬((↑N : WithTop ℕ) < arcFailTime → W̃_N = bc_N)} = L102_bad.
    have hset_eq : {ω | ¬((↑N : WithTop ℕ) < arcFailTime p vm ω →
        boundaryDeltaProcess p vm N ω = (blockCount p vm N ω : ℝ))} = L102_bad := by
      ext ω
      simp only [hL102_bad_def, Set.mem_setOf_eq, Classical.not_imp]
    rw [hset_eq] at hae
    exact hae
  -- Show: bad set ⊆ L102_bad.
  apply measure_mono_null _ hL102_bad_zero
  intro ω hω
  obtain ⟨⟨hgood, hbc⟩, hndev⟩ := hω
  simp only [Set.mem_setOf_eq] at hgood hbc hndev
  -- From goodArc: derive (↑(N+1) : WithTop ℕ) ≤ arcFailTime (copy of h_lb).
  have h_lb : (↑(N + 1) : WithTop ℕ) ≤ arcFailTime p vm ω := by
    unfold arcFailTime
    apply le_sInf
    intro a ha
    simp only [Set.mem_setOf_eq] at ha
    obtain ⟨ha_ne, ha_fail⟩ := ha
    cases a with
    | top => exact le_top
    | coe n =>
      have hn_gt : N < n := by
        by_contra h
        push Not at h
        exact ha_fail (hgood n h)
      exact Nat.cast_le.mpr (by omega)
  -- Lift to (↑N : WithTop ℕ) < arcFailTime via N < N+1.
  have h_live_N : (↑N : WithTop ℕ) < arcFailTime p vm ω := by
    have h_lt : (↑N : WithTop ℕ) < (↑(N + 1) : WithTop ℕ) := by
      exact_mod_cast Nat.lt_succ_self N
    exact lt_of_lt_of_le h_lt h_lb
  -- Show ω ∈ L102_bad: i.e. the implication fails because W̃_N ω ≠ blockCount N ω.
  refine ⟨h_live_N, ?_⟩
  -- Suppose W̃_N ω = blockCount N ω. Combined with W̃_0 = z/2 and bc_N ∈ {0, z},
  -- derive |W̃_N - W̃_0| ≥ z/2, contradicting hndev.
  intro heq
  apply hndev
  rw [heq, boundaryDeltaProcess_zero p vm ω]
  rcases hbc with h0 | hpz
  · have h0r : (blockCount p vm N ω : ℝ) = 0 := by exact_mod_cast h0
    rw [h0r, zero_sub, abs_neg]
    exact le_abs_self _
  · have hpzr : (blockCount p vm N ω : ℝ) = (p.z : ℝ) := by exact_mod_cast hpz
    rw [hpzr]
    have hdiv : ((p.z / 2 : ℕ) : ℝ) * 2 = (p.z : ℝ) := by
      exact_mod_cast Nat.div_mul_cancel p.hz_even
    rw [show (p.z : ℝ) - ((p.z / 2 : ℕ) : ℝ) = ((p.z / 2 : ℕ) : ℝ) from by linarith]
    exact le_abs_self _

/-- W̃-based variant of `blockCount_martingale_bd`. Drops the static-clique-step hypotheses
(`Γ α hα hαz2 hαT hstep`) — `boundaryDeltaProcess_isMartingale` requires none. The
conclusion uses **a.e.** inclusion (μ of the set-difference is 0). -/
private theorem blockCount_martingale_bd_boundaryDelta (p : Params)
    {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (vm : TemporalGraph.VoterModelAbstract (lowerBoundGraph p) 2 Ω)
    (hA₀ : ∀ᵐ ω ∂(vm.μ : Measure Ω), vm.opinionZeroSet 0 ω = halfCutLow p) (N : ℕ) :
    ∃ (ℱ : MeasureTheory.Filtration ℕ (inferInstance : MeasurableSpace Ω))
      (W : ℕ → Ω → ℝ),
      MeasureTheory.Martingale W ℱ vm.μ ∧
      (∀ i, 1 ≤ i → i ≤ N → ∀ᵐ ω ∂(vm.μ : Measure _), |W i ω - W (i - 1) ω| ≤ 2) ∧
      (∀ ω, W 0 ω = (p.z / 2 : ℕ)) ∧
      (vm.μ : Measure _) (({ω | ∀ j ≤ N, IsContiguousArc p (vm.opinionZeroSet (j * p.T) ω)} ∩
              {ω | blockCount p vm N ω = 0 ∨ blockCount p vm N ω = p.z}) \
            {ω | |W N ω - W 0 ω| ≥ ((p.z / 2 : ℕ) : ℝ)}) = 0 :=
  ⟨boundaryFiltration p vm, boundaryDeltaProcess p vm,
    boundaryDeltaProcess_isMartingale p vm,
    fun i hi1 _ => Filter.Eventually.of_forall fun ω =>
      boundaryDeltaProcess_diff_bd p vm i hi1 ω,
    fun ω => boundaryDeltaProcess_zero p vm ω,
    goodArc_boundaryDeltaProcess_deviation_sub_ae p vm hA₀ N⟩

/-- Numerical bound: `2 · exp(−(z/2)² / (2 · ∑ 4)) ≤ 0.4902` whenever `1 ≤ N`,
`N < z²/45`, and `z ≥ 20`. The sum simplifies to `8 · N`, so the exponent is
`−(z/2)² / (8 N) = −z²/(32 N)`, and `z²/(32 N) > 45/32`, with
`2 · exp(−45/32) ≤ 2/4.08 < 0.4902`. -/
private theorem azuma_exp_bound (p : Params) (N : ℕ) (hN1 : 1 ≤ N)
    (hN : (N : ℝ) < (p.z : ℝ) ^ 2 / 45) :
    2 * Real.exp (-(p.z / 2 : ℕ) ^ 2 / (2 * ∑ _ ∈ Finset.Icc 1 N, (2 : ℝ) ^ 2)) ≤ 0.4902 := by
  have hcard : (Finset.Icc 1 N).card = N := by rw [Nat.card_Icc]; omega
  have hsum : ∑ _ ∈ Finset.Icc 1 N, (2 : ℝ) ^ 2 = 4 * ↑N := by
    simp only [Finset.sum_const, hcard]; ring
  rw [hsum, show (2 : ℝ) * (4 * ↑N) = 8 * ↑N from by ring]
  have hdiv : (p.z / 2 : ℕ) * 2 = p.z := Nat.div_mul_cancel p.hz_even
  have hcast : (↑(p.z / 2 : ℕ) : ℝ) * 2 = ↑p.z := by exact_mod_cast hdiv
  have h_4sq : (4 : ℝ) * ↑(p.z / 2 : ℕ) ^ 2 = ↑p.z ^ 2 := by
    nlinarith [sq_nonneg ((↑(p.z / 2 : ℕ) : ℝ) * 2 - ↑p.z)]
  have h8N : (0 : ℝ) < 8 * ↑N := by positivity
  have h20 : 45 / 32 * (8 * ↑N) ≤ (↑(p.z / 2 : ℕ) : ℝ) ^ 2 := by linarith [h_4sq, hN]
  have h_arg : -(↑(p.z / 2 : ℕ) : ℝ) ^ 2 / (8 * ↑N) ≤ -(45 / 32 : ℝ) := by
    rw [div_le_iff₀ h8N]; linarith
  have h_mono : Real.exp (-(↑(p.z / 2 : ℕ) : ℝ) ^ 2 / (8 * ↑N)) ≤ Real.exp (-(45 / 32 : ℝ)) :=
    Real.exp_le_exp.mpr h_arg
  -- Taylor with 9 terms at `45/32`: `∑_{i<9} (45/32)^i/i! ≈ 4.08056 ≥ 4.08`.
  have h_lower : (4.08 : ℝ) ≤ Real.exp (45 / 32) :=
    le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
             (Real.sum_le_exp_of_nonneg (by norm_num) 9)
  have h_ub : Real.exp (-(45 / 32 : ℝ)) ≤ 0.2451 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num : (0 : ℝ) < 0.2451)]
    norm_num; linarith [h_lower]
  linarith [h_mono, h_ub]

/-- Azuma absorption bound: on the good-arc event, P(blockCount_N ∈ {0,z}) ≤ 0.4902.

Stopped blockCount is a martingale w.r.t. boundary filtration (|ΔW| ≤ 2, W_0 = z/2)
by K_{2k} complement symmetry. Two-sided Azuma (c_i = 2, threshold = z/2):
P(|W_N − z/2| ≥ z/2) ≤ 2 · exp(−z²/(32N)) ≤ 2 · exp(−45/32) ≤ 0.4902. -/
private theorem blockCount_good_azuma_bound (p : Params)
    (hz20 : 20 ≤ p.z)
    {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (vm : TemporalGraph.VoterModelAbstract (lowerBoundGraph p) 2 Ω)
    (hA₀ : ∀ᵐ ω ∂(vm.μ : Measure Ω), vm.opinionZeroSet 0 ω = halfCutLow p) (N : ℕ)
    (hN : (N : ℝ) < (p.z : ℝ) ^ 2 / 45) :
    ((vm.μ : Measure _) ({ω | ∀ j ≤ N, IsContiguousArc p (vm.opinionZeroSet (j * p.T) ω)} ∩
            {ω | blockCount p vm N ω = 0 ∨ blockCount p vm N ω = p.z})).toReal ≤ 0.4902 := by
  -- N = 0: the event is empty since blockCount 0 = z/2 ∉ {0, z}.
  rcases Nat.eq_zero_or_pos N with rfl | hN1
  · -- For N=0, blockCount 0 ω = p.z/2 a.e., and z/2 ∉ {0, z} since 4 ≤ z, so the event is null.
    have hz2_ne_zero : p.z / 2 ≠ 0 := by omega
    have hz2_ne_z : p.z / 2 ≠ p.z := by omega
    have hbc0_ae : (vm.μ : Measure _) {ω | blockCount p vm 0 ω ≠ p.z / 2} = 0 := by
      rw [← MeasureTheory.ae_iff]
      filter_upwards [hA₀] with ω hω0
      exact blockCount_initial p vm hω0
    have hnull :
        (vm.μ : Measure _) ({ω : Ω | ∀ j ≤ 0, IsContiguousArc p (vm.opinionZeroSet (j * p.T) ω)} ∩
          {ω | blockCount p vm 0 ω = 0 ∨ blockCount p vm 0 ω = p.z}) = 0 := by
      apply measure_mono_null _ hbc0_ae
      rintro ω ⟨_, hbc⟩
      simp only [Set.mem_setOf_eq]
      rcases hbc with h | h <;> omega
    rw [hnull, ENNReal.toReal_zero]; norm_num
  · -- N ≥ 1: apply Azuma + numerical bound.
    -- Use the W̃-based martingale witness (a.e. inclusion of the deviation event).
    obtain ⟨ℱ, W, hmart, hbd, hW0, hsub⟩ :=
      blockCount_martingale_bd_boundaryDelta p vm hA₀ N
    -- Threshold T = (p.z / 2 : ℕ : ℝ).
    set Tthr : ℝ := ((p.z / 2 : ℕ) : ℝ) with hTthr_def
    have hTthr_nn : 0 ≤ Tthr := Nat.cast_nonneg _
    -- One-sided Azuma on W with c_i = 2.
    have h_azuma_pos :
        ((vm.μ : Measure _) {ω | W N ω - W 0 ω ≥ Tthr}).toReal ≤
          Real.exp (- Tthr ^ 2 / (2 * ∑ i ∈ Finset.Icc 1 N, (2 : ℝ) ^ 2)) :=
      azuma_inequality (Y := W) (μ := (vm.μ : Measure Ω)) (ℱ := ℱ) hmart
        (c := fun _ => 2) (n := N) (T := Tthr)
        (fun i hi1 hiN => hbd i hi1 hiN) hTthr_nn
    -- Apply Azuma to (-W): a martingale with the same bounded differences.
    have hmart_neg : MeasureTheory.Martingale (-W) ℱ vm.μ := hmart.neg
    have hbd_neg : ∀ i, 1 ≤ i → i ≤ N →
        ∀ᵐ ω ∂(vm.μ : Measure _), |(-W) i ω - (-W) (i - 1) ω| ≤ 2 := by
      intro i hi1 hiN
      filter_upwards [hbd i hi1 hiN] with ω hω
      have heq : (-W) i ω - (-W) (i - 1) ω = -(W i ω - W (i - 1) ω) := by
        simp [Pi.neg_apply]; ring
      rw [heq, abs_neg]; exact hω
    have h_azuma_neg :
        ((vm.μ : Measure _) {ω | (-W) N ω - (-W) 0 ω ≥ Tthr}).toReal ≤
          Real.exp (- Tthr ^ 2 / (2 * ∑ i ∈ Finset.Icc 1 N, (2 : ℝ) ^ 2)) :=
      azuma_inequality (Y := -W) (μ := (vm.μ : Measure Ω)) (ℱ := ℱ) hmart_neg
        (c := fun _ => 2) (n := N) (T := Tthr)
        (fun i hi1 hiN => hbd_neg i hi1 hiN) hTthr_nn
    -- Two-sided event: {|W N - W 0| ≥ Tthr} ⊆ {W N - W 0 ≥ Tthr} ∪ {-(W N - W 0) ≥ Tthr}.
    have h_two_sub :
        {ω : Ω | |W N ω - W 0 ω| ≥ Tthr} ⊆
          {ω | W N ω - W 0 ω ≥ Tthr} ∪ {ω | (-W) N ω - (-W) 0 ω ≥ Tthr} := by
      intro ω hω
      simp only [Set.mem_setOf_eq, Set.mem_union, Pi.neg_apply] at hω ⊢
      rcases le_or_gt 0 (W N ω - W 0 ω) with hge | hlt
      · left; rw [abs_of_nonneg hge] at hω; exact hω
      · right; rw [abs_of_neg hlt] at hω
        have hrew : -W N ω - -W 0 ω = -(W N ω - W 0 ω) := by ring
        rw [hrew]; exact hω
    -- Combine: μ{|W_N - W_0| ≥ Tthr} ≤ 2 · exp(...).
    have h_two_bound :
        ((vm.μ : Measure _) {ω | |W N ω - W 0 ω| ≥ Tthr}).toReal ≤
          2 * Real.exp (- Tthr ^ 2 / (2 * ∑ i ∈ Finset.Icc 1 N, (2 : ℝ) ^ 2)) := by
      calc ((vm.μ : Measure _) {ω | |W N ω - W 0 ω| ≥ Tthr}).toReal
          ≤ ((vm.μ : Measure _) ({ω | W N ω - W 0 ω ≥ Tthr} ∪
                    {ω | (-W) N ω - (-W) 0 ω ≥ Tthr})).toReal :=
            ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono h_two_sub)
        _ ≤ (((vm.μ : Measure _) {ω | W N ω - W 0 ω ≥ Tthr}) +
              ((vm.μ : Measure _) {ω | (-W) N ω - (-W) 0 ω ≥ Tthr})).toReal :=
            ENNReal.toReal_mono
              (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩)
              (measure_union_le _ _)
        _ = ((vm.μ : Measure _) {ω | W N ω - W 0 ω ≥ Tthr}).toReal +
              ((vm.μ : Measure _) {ω | (-W) N ω - (-W) 0 ω ≥ Tthr}).toReal :=
            ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)
        _ ≤ Real.exp (- Tthr ^ 2 / (2 * ∑ i ∈ Finset.Icc 1 N, (2 : ℝ) ^ 2)) +
              Real.exp (- Tthr ^ 2 / (2 * ∑ i ∈ Finset.Icc 1 N, (2 : ℝ) ^ 2)) :=
            add_le_add h_azuma_pos h_azuma_neg
        _ = 2 * Real.exp (- Tthr ^ 2 / (2 * ∑ i ∈ Finset.Icc 1 N, (2 : ℝ) ^ 2)) := by ring
    -- Goal: μ(goodArc ∩ blockCount-bdy) ≤ 0.4902. The witness `hsub` is now a
    -- *measure-zero* set-difference (a.e. inclusion); convert via `ae_le_set` +
    -- `measure_mono_ae`.
    have h_ae_le :
        (({ω : Ω | ∀ j ≤ N, IsContiguousArc p (vm.opinionZeroSet (j * p.T) ω)} ∩
          {ω : Ω | blockCount p vm N ω = 0 ∨ blockCount p vm N ω = p.z}) :
            Set Ω) ≤ᵐ[(vm.μ : Measure _)]
        ({ω : Ω | |W N ω - W 0 ω| ≥ Tthr} : Set Ω) := by
      rw [MeasureTheory.ae_le_set]
      exact hsub
    have h_meas_le :
        (vm.μ : Measure _) (({ω : Ω | ∀ j ≤ N, IsContiguousArc p (vm.opinionZeroSet (j * p.T) ω)} ∩
              {ω : Ω | blockCount p vm N ω = 0 ∨ blockCount p vm N ω = p.z}) :
                Set Ω) ≤
            (vm.μ : Measure _) ({ω : Ω | |W N ω - W 0 ω| ≥ Tthr} : Set Ω) :=
      MeasureTheory.measure_mono_ae h_ae_le
    calc ((vm.μ : Measure _) ({ω | ∀ j ≤ N, IsContiguousArc p (vm.opinionZeroSet (j * p.T) ω)} ∩
                  {ω | blockCount p vm N ω = 0 ∨ blockCount p vm N ω = p.z})).toReal
        ≤ ((vm.μ : Measure _) {ω | |W N ω - W 0 ω| ≥ Tthr}).toReal :=
          ENNReal.toReal_mono (measure_ne_top _ _) h_meas_le
      _ ≤ 2 * Real.exp (- Tthr ^ 2 / (2 * ∑ i ∈ Finset.Icc 1 N, (2 : ℝ) ^ 2)) := h_two_bound
      _ ≤ 0.4902 := by
            have hexp_eq : - Tthr ^ 2 = -((p.z / 2 : ℕ) : ℝ) ^ 2 := by
              rw [hTthr_def]
            rw [hexp_eq]
            exact azuma_exp_bound p N hN1 hN

/-- Helper (b') — combined Azuma + τ-stopping absorption bound (deferred).

`P(∃ i ≤ N, blockCount i ∈ {0,z}) ≤ 1 − 0.5075` for any `N < z²/45`.

**Proof sketch (deferred):**
- **Contiguous-block invariant**: `A_0 = halfCutLow` is a contiguous arc of `z/2` whole
  blocks. Define `τ` as the first interval `j` where `A_{jT}` is NOT a contiguous arc of
  whole blocks. On `{τ > j}`, at most 2 active K_{2k} cliques in `I_{j+1}` are mixed
  (one seam clique at each arc boundary); all others are homogeneous and trivially absorbed.
- **τ bound**: By `perInterval_absorption_prob` (each mixed clique fails with prob ≤ 2^{-α})
  and union bound over ≤ 2 mixed cliques per interval:
  `P(τ ≤ N) ≤ 2N · 2^{-α} ≤ 2(z²/45)/z³ = 2/(45z) ≤ 1/450`
  (using `(1/2)^α ≤ 1/z³` from `exists_alpha_witness`).
- **Martingale W**: On `{τ > j}`, the stopped block-count `W_j = blockCount j` changes
  by at most ±2 per step (at most 2 seam cliques absorb per interval, each contributing
  ±1). Each seam clique goes ±1 with equal probability by `K_{2k}` symmetry, so W is an
  `(ℱ_{j·T})`-martingale with `W 0 = z/2` and `|ΔW| ≤ 2`.
- **Azuma** (two-sided, c_i = 2, n = N, threshold z/2):
  `P(W_N ∈ {0,z}) ≤ 2 · exp(−(z/2)²/(2·4N)) = 2·exp(−z²/(32N)) ≤ 2·exp(−45/32) ≤ 0.4902`.
- **Combine**: `1/450 + 0.4902 ≤ 0.4925 = 1 − 0.5075`. ✓ -/
theorem blockCount_absorbed_ub (Γ : ℕ) (p : Params)
    (hz20 : 20 ≤ p.z)
    (hTbound : (10 : ℝ) * Γ * p.k * Real.log p.z ≤ (p.T : ℝ))
    (hstep : ∀ (t : ℕ) (T : Finset (CliqueVertex p.k)),
        (1 / 2 : ENNReal) ≤
          VoterModel.opinionProcess₂ (staticCliqueGraph p.k) t (Γ * p.k) T Finset.univ +
          VoterModel.opinionProcess₂ (staticCliqueGraph p.k) t (Γ * p.k) T ∅)
    {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (vm : TemporalGraph.VoterModelAbstract (lowerBoundGraph p) 2 Ω)
    (hA₀ : ∀ᵐ ω ∂(vm.μ : Measure Ω), vm.opinionZeroSet 0 ω = halfCutLow p) (N : ℕ)
    (hN : (N : ℝ) < (p.z : ℝ) ^ 2 / 45) :
    ((vm.μ : Measure _) {ω | ∃ i ≤ N, blockCount p vm i ω = 0 ∨ blockCount p vm i ω = p.z}).toReal ≤
      1 - 0.5075 := by
  obtain ⟨α, hα, hαz2, hαT⟩ := exists_alpha_witness Γ p hz20 hTbound
  -- Events: goodArc = arc invariant holds for all j ≤ N; arcFails = complement.
  set goodArc : Set Ω := {ω | ∀ j ≤ N, IsContiguousArc p (vm.opinionZeroSet (j * p.T) ω)}
  set arcFails : Set Ω := {ω | ∃ j ≤ N, ¬IsContiguousArc p (vm.opinionZeroSet (j * p.T) ω)}
  -- GoodE: goodArc ∩ terminal blockCount hits {0,z}.
  set GoodE : Set Ω := goodArc ∩ {ω | blockCount p vm N ω = 0 ∨ blockCount p vm N ω = p.z}
  -- bad event ⊆ᵐ arcFails ∪ GoodE.  On goodArc, {0,z} is absorbing: if bc_i ∈ {0,z}
  -- for some i ≤ N then the process absorbed by i·T, so by a.e. permanence the
  -- minority set is empty at N·T, giving bc_N ∈ {0,z}.
  have hfix := lowerBoundGraph_fixedDegrees p
  have h_decomp : {ω | ∃ i ≤ N, blockCount p vm i ω = 0 ∨ blockCount p vm i ω = p.z}
      ≤ᵐ[(vm.μ : Measure Ω)] (arcFails ∪ GoodE : Set Ω) := by
    filter_upwards
      [TemporalGraph.VoterModelAbstract.ae_minoritySet_empty_of_absorptionTime_le
        (G := (lowerBoundGraph p).withFixed hfix) vm]
      with ω hperm hω
    -- Membership is in applied form; read off the predicate.
    replace hω : ∃ i ≤ N, blockCount p vm i ω = 0 ∨ blockCount p vm i ω = p.z := hω
    by_cases h : ∀ j ≤ N, IsContiguousArc p (vm.opinionZeroSet (j * p.T) ω)
    · have hg : ω ∈ goodArc := h
      refine Set.mem_union_right _ (Set.mem_inter hg ?_)
      show blockCount p vm N ω = 0 ∨ blockCount p vm N ω = p.z
      obtain ⟨i, hi, hbc⟩ := hω
      -- bc_i ∈ {0,z} → A(i*T) = ∅ or univ (using arc invariant for bc_i=0).
      have hAi : vm.opinionZeroSet (i * p.T) ω = ∅ ∨ vm.opinionZeroSet (i * p.T) ω = Finset.univ := by
        rcases hbc with hbc0 | hbcz
        · exact Or.inl ((blockCount_arc_zero_iff p (vm.opinionZeroSet (i * p.T) ω) (h i hi)).mp hbc0)
        · exact Or.inr ((blockCount_z_iff p (vm.opinionZeroSet (i * p.T) ω)).mp hbcz)
      -- A = ∅ or univ → minoritySet = ∅ → absorptionTime ω ≤ i*T.
      have hmin_i : VoterModel.minoritySet (lowerBoundGraph p) (i * p.T) (vm.opinionZeroSet (i * p.T) ω) = ∅ :=
        (minoritySet_lowerBoundGraph_eq_empty_iff p (i * p.T) (vm.opinionZeroSet (i * p.T) ω)).mpr hAi
      have habs_le_i : vm.absorptionTime ω ≤ ((i * p.T : ℕ) : ℕ∞) :=
        (TemporalGraph.VoterModelAbstract.absorptionTime_le_coe_iff_exists
          vm ω (i * p.T)).mpr ⟨i * p.T, le_refl _, hmin_i⟩
      -- absorptionTime ω ≤ N*T by transitivity, then a.e. permanence gives minority(N*T) = ∅.
      have hmin_N : VoterModel.minoritySet (lowerBoundGraph p) (N * p.T) (vm.opinionZeroSet (N * p.T) ω) = ∅ :=
        hperm (N * p.T)
          (le_trans habs_le_i (by exact_mod_cast Nat.mul_le_mul_right p.T hi))
      -- minority(N*T) = ∅ → A(N*T) = ∅ or univ → bc_N ∈ {0, z}.
      rcases (minoritySet_lowerBoundGraph_eq_empty_iff p (N * p.T) (vm.opinionZeroSet (N * p.T) ω)).mp hmin_N
          with hAN | hAN
      · left
        show (Finset.univ.filter fun i : Fin p.z => block p i ⊆ vm.opinionZeroSet (N * p.T) ω).card = 0
        rw [hAN, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro i' _ hsub
        exact absurd (Finset.subset_empty.mp hsub)
          (Finset.nonempty_iff_ne_empty.mp ⟨(i', ⟨0, p.hk_pos⟩), (mem_block p i' _).mpr rfl⟩)
      · right; exact (blockCount_z_iff p (vm.opinionZeroSet (N * p.T) ω)).mpr hAN
    · refine Set.mem_union_left _ ?_
      show ∃ j ≤ N, ¬IsContiguousArc p (vm.opinionZeroSet (j * p.T) ω)
      push Not at h; exact h
  have h_tau : ((vm.μ : Measure _) arcFails).toReal ≤ 1 / 450 :=
    arc_fail_event_le Γ p hz20 α hα hαz2 hαT hstep vm hA₀ N hN
  have h_azuma : ((vm.μ : Measure _) GoodE).toReal ≤ 0.4902 :=
    blockCount_good_azuma_bound p hz20 vm hA₀ N hN
  -- Combine: μ(E) ≤ μ(arcFails) + μ(GoodE) ≤ 1/450 + 0.4902 ≤ 0.4925 = 1 - 0.5075.
  calc ((vm.μ : Measure _) {ω | ∃ i ≤ N, blockCount p vm i ω = 0 ∨ blockCount p vm i ω = p.z}).toReal
      ≤ ((vm.μ : Measure _) (arcFails ∪ GoodE)).toReal :=
          ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae h_decomp)
    _ ≤ (((vm.μ : Measure _) arcFails) + ((vm.μ : Measure _) GoodE)).toReal :=
          ENNReal.toReal_mono
            (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩)
            (measure_union_le _ _)
    _ = ((vm.μ : Measure _) arcFails).toReal + ((vm.μ : Measure _) GoodE).toReal :=
          ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)
    _ ≤ 1 / 450 + 0.4902 := add_le_add h_tau h_azuma
    _ ≤ 1 - 0.5075 := by norm_num


end TemporalGraph.VoterProcess.LowerBound
