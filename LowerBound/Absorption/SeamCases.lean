module

import VoterProcess.TwoOpinion
import LowerBound.Absorbing
import Mathlib.Algebra.Order.Star.Real

public import LowerBound.Absorption.Defs
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Covering.Besicovitch

/-! ## Main results

The nine-row seam-witness table (`row4_witness` … `row9_witness`) and the
per-step arc-failure analysis: `contiguousArc_step_structure`,
`arc_fail_has_two_seam_events`, `arc_fail_per_step`, `arc_fail_event_le`. -/

public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

namespace TemporalGraph.VoterProcess.LowerBound

/-- Row 4 of the 9-row witness table in `contiguousArc_break_seam_mixed`:
    inactive/active parity, both seams `sub` ⇒ witness `(b - 1, m + 2)` (or `(0, p.z)` if `m + 2 > p.z`). -/
private theorem row4_witness {p : Params} {S S' : Finset (VertexSet p)}
    (b aL aR bm1 : Fin p.z) (m : ℕ) (hm_ge2 : 1 < m) (hm_lt : m < p.z)
    (arcVtx : ℕ → Fin p.z)
    (arcVtx_def : ∀ i, arcVtx i = ⟨(b.val + i) % p.z, Nat.mod_lt _ p.hz_pos⟩)
    (arcVtx_inj : ∀ {i k : ℕ}, i < p.z → k < p.z → arcVtx i = arcVtx k → i = k)
    (arcVtx_succ : ∀ i, arcVtx (i + 1) = arcVtx i + 1)
    (arcVtx_zero : arcVtx 0 = b)
    (arcVtx_pred_succ : arcVtx m.pred + 1 = arcVtx m)
    (arcIdx : Finset (Fin p.z))
    (arcVtx_mem_arcIdx : ∀ i, i < m → arcVtx i ∈ arcIdx)
    (harcIdx : ∀ c : Fin p.z, c ∈ arcIdx ↔ block p c ⊆ S)
    (harc_mem_iff : ∀ c : Fin p.z, c ∈ arcIdx ↔ ∃ i ∈ Finset.range m, c = arcVtx i)
    (succ_eq : ∀ a : Fin p.z, (⟨(a.val + 1) % p.z, Nat.mod_lt _ p.hz_pos⟩ : Fin p.z) = a + 1)
    (block_dichotomy_S' : ∀ c : Fin p.z, block p c ⊆ S' ∨ Disjoint (block p c) S')
    (interior_block_iff_S' : ∀ c : Fin p.z,
      c ≠ aL → c ≠ aL + 1 → c ≠ aR → c ≠ aR + 1 → (block p c ⊆ S' ↔ block p c ⊆ S))
    (build_arc_witness : ∀ (b' : Fin p.z) (m' : ℕ), m' ≤ p.z →
      (∀ c : Fin p.z, block p c ⊆ S' ↔
        ∃ i ∈ Finset.range m', c = ⟨(b'.val + i) % p.z, Nat.mod_lt _ p.hz_pos⟩) →
      IsContiguousArc p S')
    (haL_succ : aL + 1 = b) (haR_bm1 : aR = bm1)
    (bm1_eq_arcVtx : bm1 = arcVtx m.pred)
    (haL_sub : block p aL ∪ block p (aL + 1) ⊆ S')
    (haR_sub : block p aR ∪ block p (aR + 1) ⊆ S') :
    IsContiguousArc p S' := by
  have hm_pos : 0 < m := by omega
  have hm_le : m ≤ p.z := le_of_lt hm_lt
  have h1_mod : (1 : ℕ) % p.z = 1 := Nat.mod_eq_of_lt (by omega)
  have h_aL_sub_S' : block p aL ⊆ S' :=
    fun v hv => haL_sub (Finset.mem_union_left _ hv)
  have h_aL1_sub_S' : block p (aL + 1) ⊆ S' :=
    fun v hv => haL_sub (Finset.mem_union_right _ hv)
  have h_aR_sub_S' : block p aR ⊆ S' :=
    fun v hv => haR_sub (Finset.mem_union_left _ hv)
  have h_aR1_sub_S' : block p (aR + 1) ⊆ S' :=
    fun v hv => haR_sub (Finset.mem_union_right _ hv)
  -- arcVtx2 i := ⟨(aL.val + i) % p.z, _⟩
  let arcVtx2 : ℕ → Fin p.z := fun i => ⟨(aL.val + i) % p.z, Nat.mod_lt _ p.hz_pos⟩
  have arcVtx2_zero : arcVtx2 0 = aL := Fin.ext (by simp [arcVtx2, Nat.mod_eq_of_lt aL.isLt])
  have arcVtx2_one : arcVtx2 1 = aL + 1 := succ_eq aL
  have arcVtx2_succ : ∀ i, arcVtx2 (i + 1) = arcVtx2 i + 1 := by
    intro i
    rw [← succ_eq (arcVtx2 i)]
    apply Fin.ext
    show (aL.val + (i + 1)) % p.z = ((aL.val + i) % p.z + 1) % p.z
    have h1 : aL.val + (i + 1) = (aL.val + i) + 1 := by ring
    rw [h1, Nat.add_mod (aL.val + i) 1 p.z, h1_mod]
  have arcVtx2_shift : ∀ i, arcVtx2 (i + 1) = arcVtx i := by
    intro i
    induction i with
    | zero => rw [arcVtx2_one, haL_succ, ← arcVtx_zero]
    | succ k ih => rw [arcVtx2_succ (k + 1), ih, ← arcVtx_succ]
  by_cases hm_edge : m + 2 ≤ p.z
  · -- Standard case: witness (aL, m + 2)
    refine build_arc_witness aL (m + 2) hm_edge ?_
    intro c
    show block p c ⊆ S' ↔ ∃ i ∈ Finset.range (m + 2), c = arcVtx2 i
    refine ⟨?_, ?_⟩
    · intro hc_sub
      by_cases hcaL : c = aL
      · exact ⟨0, Finset.mem_range.mpr (by omega), by rw [hcaL]; exact arcVtx2_zero.symm⟩
      by_cases hcaL1 : c = aL + 1
      · exact ⟨1, Finset.mem_range.mpr (by omega), by rw [hcaL1]; exact arcVtx2_one.symm⟩
      by_cases hcaR : c = aR
      · refine ⟨m, Finset.mem_range.mpr (by omega), ?_⟩
        have hmp : m.pred + 1 = m := Nat.succ_pred_eq_of_pos hm_pos
        rw [hcaR, haR_bm1, bm1_eq_arcVtx, ← arcVtx2_shift m.pred, hmp]
      by_cases hcaR1 : c = aR + 1
      · refine ⟨m + 1, Finset.mem_range.mpr (by omega), ?_⟩
        rw [hcaR1, haR_bm1, bm1_eq_arcVtx, arcVtx_pred_succ, ← arcVtx2_shift m]
      have hc_S : block p c ⊆ S :=
        (interior_block_iff_S' c hcaL hcaL1 hcaR hcaR1).mp hc_sub
      have hc_arc : c ∈ arcIdx := (harcIdx c).mpr hc_S
      obtain ⟨i, hi, rfl⟩ := (harc_mem_iff c).mp hc_arc
      rw [Finset.mem_range] at hi
      refine ⟨i + 1, Finset.mem_range.mpr (by omega), ?_⟩
      exact (arcVtx2_shift i).symm
    · rintro ⟨i, hi, rfl⟩
      rw [Finset.mem_range] at hi
      by_cases h0 : i = 0
      · subst h0; rw [arcVtx2_zero]; exact h_aL_sub_S'
      by_cases h1 : i = 1
      · subst h1; rw [arcVtx2_one]; exact h_aL1_sub_S'
      by_cases h_m1 : i = m + 1
      · -- arcVtx2 (m+1) = arcVtx m = aR + 1
        subst h_m1
        rw [arcVtx2_shift, ← arcVtx_pred_succ, ← bm1_eq_arcVtx, ← haR_bm1]
        exact h_aR1_sub_S'
      have hi_pos : 1 ≤ i := by omega
      have hi_pred : i - 1 < m := by omega
      have hi_rw : i = (i - 1) + 1 := by omega
      rw [hi_rw, arcVtx2_shift]
      by_cases hci_R : arcVtx (i - 1) = aR
      · rw [hci_R]; exact h_aR_sub_S'
      have hci_arc : arcVtx (i - 1) ∈ arcIdx := arcVtx_mem_arcIdx (i - 1) hi_pred
      have hci_S : block p (arcVtx (i - 1)) ⊆ S := (harcIdx _).mp hci_arc
      have hizpz : i - 1 < p.z := Nat.lt_of_lt_of_le hi_pred hm_le
      have hci_L : arcVtx (i - 1) ≠ aL := by
        intro heq
        have h_succ : arcVtx (i - 1) + 1 = arcVtx 0 := by
          rw [arcVtx_zero, ← haL_succ, heq]
        have h_arc_i : arcVtx i = arcVtx (i - 1) + 1 := by
          have hi_rw : i = (i - 1) + 1 := by omega
          conv_lhs => rw [hi_rw]
          exact arcVtx_succ (i - 1)
        rw [← h_arc_i] at h_succ
        have hizpz' : i < p.z := Nat.lt_of_lt_of_le hi (by omega : m + 2 ≤ p.z)
        have : i = 0 := arcVtx_inj hizpz' p.hz_pos h_succ
        exact h0 this
      have hci_L1 : arcVtx (i - 1) ≠ aL + 1 := by
        intro heq
        rw [haL_succ] at heq
        have : arcVtx (i - 1) = arcVtx 0 := by rw [heq, arcVtx_zero]
        have h0_eq : i - 1 = 0 := arcVtx_inj hizpz p.hz_pos this
        exact h1 (by omega)
      have hci_R1 : arcVtx (i - 1) ≠ aR + 1 := by
        rw [haR_bm1, bm1_eq_arcVtx, arcVtx_pred_succ]; intro heq
        have : i - 1 = m := arcVtx_inj hizpz hm_lt heq
        omega
      exact (interior_block_iff_S' (arcVtx (i - 1)) hci_L hci_L1 hci_R hci_R1).mpr hci_S
  · -- Edge case: m + 2 > p.z, so m = p.z - 1. Show S' = Finset.univ.
    push Not at hm_edge
    have hm_eq : m = p.z - 1 := by omega
    -- Every block ⊆ S':
    -- arcVtx 0..arcVtx(m-1) are in S (via arcIdx) and seam aL covers block_(b-1)=aL and block_b=aL+1=arcVtx 0.
    -- Seam aR covers block_aR=arcVtx(m-1)=bm1 and block_(aR+1)=arcVtx m.
    -- arcVtx m = arcVtx (p.z - 1). Cyclically this is the "block before b" = aL!
    -- So {aL, aL+1, ..., aR+1} cyclically covers everything.
    -- We argue every block is in S' via the four boundary statuses + interior_block_iff_S'.
    have h_all_subS' : ∀ c : Fin p.z, block p c ⊆ S' := by
      intro c
      by_cases hcaL : c = aL
      · rw [hcaL]; exact h_aL_sub_S'
      by_cases hcaL1 : c = aL + 1
      · rw [hcaL1]; exact h_aL1_sub_S'
      by_cases hcaR : c = aR
      · rw [hcaR]; exact h_aR_sub_S'
      by_cases hcaR1 : c = aR + 1
      · rw [hcaR1]; exact h_aR1_sub_S'
      -- Interior: block c ⊆ S iff block c ⊆ S'. Need block c ⊆ S.
      -- c ∉ {aL, aL+1, aR, aR+1} ⊆ {aL, b, bm1, arcVtx m}.
      -- We argue c ∈ arcIdx. Since m = p.z - 1, arcIdx = {arcVtx 0, ..., arcVtx (p.z-2)},
      -- missing exactly one element: arcVtx (p.z-1).
      -- We need to show arcVtx (p.z-1) = aL (i.e., the missing block is aL = b-1).
      -- aL + 1 = b = arcVtx 0, so aL = arcVtx 0 - 1 cyclically. In Fin: aL = arcVtx (p.z - 1).
      have haL_arcVtx_z1 : aL = arcVtx (p.z - 1) := by
        -- aL + 1 = b and arcVtx (p.z - 1) + 1 = b cyclically.
        have h1 : aL + 1 = arcVtx (p.z - 1) + 1 := by
          rw [haL_succ]
          apply Fin.ext
          show b.val = (arcVtx (p.z - 1) + 1).val
          rw [← succ_eq (arcVtx (p.z - 1))]
          show b.val = ((arcVtx (p.z - 1)).val + 1) % p.z
          rw [arcVtx_def]
          show b.val = ((b.val + (p.z - 1)) % p.z + 1) % p.z
          have hbz : b.val < p.z := b.isLt
          -- (b + (p.z - 1)) % p.z is either b.val - 1 (if b ≥ 1) or p.z - 1 (if b = 0).
          -- Case 1: b.val ≥ 1. Then b + p.z - 1 ≥ p.z, so (b + p.z - 1) % p.z = b - 1.
          -- (b - 1 + 1) % p.z = b % p.z = b. ✓
          -- Case 2: b.val = 0. Then b + p.z - 1 = p.z - 1 < p.z, so (b + p.z - 1) % p.z = p.z - 1.
          -- (p.z - 1 + 1) % p.z = p.z % p.z = 0 = b. ✓
          by_cases hbpos : b.val ≥ 1
          · have h_inner : (b.val + (p.z - 1)) % p.z = b.val - 1 := by
              have h1 : b.val + (p.z - 1) = (b.val - 1) + p.z := by omega
              rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            rw [h_inner]
            have h_outer : (b.val - 1 + 1) % p.z = b.val := by
              have : b.val - 1 + 1 = b.val := by omega
              rw [this, Nat.mod_eq_of_lt hbz]
            exact h_outer.symm
          · push Not at hbpos
            have hb0 : b.val = 0 := by omega
            have h_inner : (b.val + (p.z - 1)) % p.z = p.z - 1 := by
              rw [hb0, Nat.zero_add]; exact Nat.mod_eq_of_lt (by omega)
            rw [h_inner]
            have h_outer : (p.z - 1 + 1) % p.z = 0 := by
              have : p.z - 1 + 1 = p.z := by omega
              rw [this, Nat.mod_self]
            rw [h_outer, hb0]
        have heq : aL + 1 + (-1 : Fin p.z) = arcVtx (p.z - 1) + 1 + (-1 : Fin p.z) :=
          congrArg (· + (-1 : Fin p.z)) h1
        simpa [add_assoc] using heq
      -- So c ∈ {arcVtx 0, ..., arcVtx (p.z-1)} \ {aL} = arcIdx (since arcIdx misses only aL).
      -- Now c ≠ aL, so c = arcVtx i for some i < p.z - 1 = m, i.e., c ∈ arcIdx.
      have hc_S : block p c ⊆ S := by
        -- Use block_dichotomy_S': either block c ⊆ S' (then use interior_block_iff_S') or disjoint.
        -- Actually for our argument: block c ⊆ S iff c ∈ arcIdx. We show c ∈ arcIdx by exhaustion.
        rcases block_dichotomy_S' c with h | h
        · -- We want to show block c ⊆ S. Use interior_block_iff_S' since c is interior.
          exact (interior_block_iff_S' c hcaL hcaL1 hcaR hcaR1).mp h
        · -- block c disjoint S'. But we need block c ⊆ S' below. Need to derive contradiction.
          -- Argument: c ∉ {aL, aL+1, aR, aR+1}. Cyclically these four points and arcIdx cover everything when m = p.z - 1.
          -- Concretely: arcIdx = {arcVtx 0, ..., arcVtx (p.z-2)} (all except aL).
          -- {aL, aL+1, aR, aR+1} = {aL, arcVtx 0, arcVtx (m-1), arcVtx m}.
          -- Since m = p.z - 1, arcVtx m = arcVtx (p.z - 1) = aL.
          -- So {aL, aL+1, aR, aR+1} = {aL, arcVtx 0, arcVtx (p.z - 2), aL} = {aL, b, arcVtx (p.z - 2)}.
          -- arcIdx covers {arcVtx 0, ..., arcVtx (p.z - 2)}.
          -- Combined: every c is either aL or in arcIdx.
          -- If c ≠ aL, then c ∈ arcIdx, so block c ⊆ S.
          -- (Independent of haR_disj; ignore the false hypothesis.)
          exfalso
          have hc_arcIdx : c ∈ arcIdx := by
            -- Show c ∈ arcIdx for all c ≠ aL.
            -- Strategy: use that c = arcVtx j for some j < p.z, and j ≠ p.z - 1 (else c = aL).
            -- Then j < p.z - 1 = m, so c ∈ arcIdx.
            obtain ⟨j, hj_lt, hj_eq⟩ : ∃ j, j < p.z ∧ c = arcVtx j := by
              refine ⟨(c.val + p.z - b.val) % p.z, Nat.mod_lt _ p.hz_pos, ?_⟩
              apply Fin.ext
              rw [arcVtx_def]
              show c.val = (b.val + (c.val + p.z - b.val) % p.z) % p.z
              have hb : b.val < p.z := b.isLt
              have hcc : c.val < p.z := c.isLt
              rw [Nat.add_mod b.val _ p.z, Nat.mod_mod, ← Nat.add_mod]
              have heq2 : b.val + (c.val + p.z - b.val) = c.val + p.z := by omega
              rw [heq2, Nat.add_mod_right, Nat.mod_eq_of_lt hcc]
            rw [hj_eq] at hcaL
            have hj_ne : j ≠ p.z - 1 := by
              intro h
              apply hcaL
              rw [haL_arcVtx_z1, h]
            rw [hj_eq]
            refine (harc_mem_iff (arcVtx j)).mpr ⟨j, Finset.mem_range.mpr ?_, rfl⟩
            omega
          have hc_S : block p c ⊆ S := (harcIdx c).mp hc_arcIdx
          -- Now block c ⊆ S. Combined with c ≠ aL, aL+1, aR, aR+1, interior_block_iff_S' gives block c ⊆ S'.
          -- But h : Disjoint (block c) S'. Contradiction.
          have hcS' := (interior_block_iff_S' c hcaL hcaL1 hcaR hcaR1).mpr hc_S
          obtain ⟨v, hv⟩ := (⟨_, (mem_block p c (c, ⟨0, p.hk_pos⟩)).mpr rfl⟩ :
            (block p c).Nonempty)
          exact (Finset.disjoint_left.mp h) hv (hcS' hv)
      exact (interior_block_iff_S' c hcaL hcaL1 hcaR hcaR1).mpr hc_S
    -- Witness: (⟨0, _⟩, p.z) with S' = univ.
    refine ⟨⟨0, p.hz_pos⟩, p.z, le_refl _, ?_⟩
    have hS'_univ : S' = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro v
      exact h_all_subS' v.1 ((mem_block p v.1 v).mpr rfl)
    rw [hS'_univ]; symm
    apply Finset.eq_univ_of_forall; intro v
    refine Finset.mem_biUnion.mpr ⟨v.1.val, Finset.mem_range.mpr v.1.isLt, ?_⟩
    rw [mem_block]; apply Fin.ext
    show v.1.val = (0 + v.1.val) % p.z
    rw [Nat.zero_add, Nat.mod_eq_of_lt v.1.isLt]

/-- Row 7 of the 9-row witness table in `contiguousArc_break_seam_mixed`:
    inactive/active parity, both seams `disj` ⇒ witness `(b + 1, m - 2)`. -/
private theorem row7_witness {p : Params} {S S' : Finset (VertexSet p)}
    (b aL aR bm1 : Fin p.z) (m : ℕ) (hm_ge2 : 1 < m) (hm_lt : m < p.z)
    (arcVtx : ℕ → Fin p.z)
    (arcVtx_def : ∀ i, arcVtx i = ⟨(b.val + i) % p.z, Nat.mod_lt _ p.hz_pos⟩)
    (arcVtx_inj : ∀ {i k : ℕ}, i < p.z → k < p.z → arcVtx i = arcVtx k → i = k)
    (arcVtx_succ : ∀ i, arcVtx (i + 1) = arcVtx i + 1)
    (arcVtx_zero : arcVtx 0 = b)
    (arcVtx_pred_succ : arcVtx m.pred + 1 = arcVtx m)
    (arcIdx : Finset (Fin p.z))
    (arcVtx_mem_arcIdx : ∀ i, i < m → arcVtx i ∈ arcIdx)
    (harcIdx : ∀ c : Fin p.z, c ∈ arcIdx ↔ block p c ⊆ S)
    (harc_mem_iff : ∀ c : Fin p.z, c ∈ arcIdx ↔ ∃ i ∈ Finset.range m, c = arcVtx i)
    (interior_block_iff_S' : ∀ c : Fin p.z,
      c ≠ aL → c ≠ aL + 1 → c ≠ aR → c ≠ aR + 1 → (block p c ⊆ S' ↔ block p c ⊆ S))
    (build_arc_witness : ∀ (b' : Fin p.z) (m' : ℕ), m' ≤ p.z →
      (∀ c : Fin p.z, block p c ⊆ S' ↔
        ∃ i ∈ Finset.range m', c = ⟨(b'.val + i) % p.z, Nat.mod_lt _ p.hz_pos⟩) →
      IsContiguousArc p S')
    (haL_succ : aL + 1 = b) (haR_bm1 : aR = bm1)
    (bm1_eq_arcVtx : bm1 = arcVtx m.pred)
    (haL_disj : Disjoint (block p aL ∪ block p (aL + 1)) S')
    (haR_disj : Disjoint (block p aR ∪ block p (aR + 1)) S') :
    IsContiguousArc p S' := by
  have hm_pos : 0 < m := by omega
  have hm_le : m ≤ p.z := le_of_lt hm_lt
  have h1_mod : (1 : ℕ) % p.z = 1 := Nat.mod_eq_of_lt (by omega)
  have h_aL_ndj_S' : ¬ block p aL ⊆ S' := by
    intro hsub
    obtain ⟨v, hv⟩ := (⟨_, (mem_block p aL (aL, ⟨0, p.hk_pos⟩)).mpr rfl⟩ :
      (block p aL).Nonempty)
    exact (Finset.disjoint_left.mp haL_disj) (Finset.mem_union_left _ hv) (hsub hv)
  have h_aL1_ndj_S' : ¬ block p (aL + 1) ⊆ S' := by
    intro hsub
    obtain ⟨v, hv⟩ := (⟨_, (mem_block p (aL+1) (aL+1, ⟨0, p.hk_pos⟩)).mpr rfl⟩ :
      (block p (aL+1)).Nonempty)
    exact (Finset.disjoint_left.mp haL_disj) (Finset.mem_union_right _ hv) (hsub hv)
  have h_aR_ndj_S' : ¬ block p aR ⊆ S' := by
    intro hsub
    obtain ⟨v, hv⟩ := (⟨_, (mem_block p aR (aR, ⟨0, p.hk_pos⟩)).mpr rfl⟩ :
      (block p aR).Nonempty)
    exact (Finset.disjoint_left.mp haR_disj) (Finset.mem_union_left _ hv) (hsub hv)
  have h_aR1_ndj_S' : ¬ block p (aR + 1) ⊆ S' := by
    intro hsub
    obtain ⟨v, hv⟩ := (⟨_, (mem_block p (aR+1) (aR+1, ⟨0, p.hk_pos⟩)).mpr rfl⟩ :
      (block p (aR+1)).Nonempty)
    exact (Finset.disjoint_left.mp haR_disj) (Finset.mem_union_right _ hv) (hsub hv)
  refine build_arc_witness (b + 1) (m - 2) (by omega) ?_
  intro c
  have b1_eq_arcVtx : ∀ i, (⟨((b + 1).val + i) % p.z, Nat.mod_lt _ p.hz_pos⟩ : Fin p.z) =
      arcVtx (i + 1) := by
    intro i
    have h_b1_val : (b + 1 : Fin p.z).val = (b.val + 1) % p.z := by simp [Fin.val_add]
    apply Fin.ext
    show ((b + 1).val + i) % p.z = (arcVtx (i + 1)).val
    rw [arcVtx_def, h_b1_val, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    ring_nf
  show block p c ⊆ S' ↔ ∃ i ∈ Finset.range (m - 2), c =
      (⟨((b + 1).val + i) % p.z, Nat.mod_lt _ p.hz_pos⟩ : Fin p.z)
  refine ⟨?_, ?_⟩
  · intro hc_sub
    by_cases hcaL : c = aL
    · exfalso; rw [hcaL] at hc_sub; exact h_aL_ndj_S' hc_sub
    by_cases hcaL1 : c = aL + 1
    · exfalso; rw [hcaL1] at hc_sub; exact h_aL1_ndj_S' hc_sub
    by_cases hcaR : c = aR
    · exfalso; rw [hcaR] at hc_sub; exact h_aR_ndj_S' hc_sub
    by_cases hcaR1 : c = aR + 1
    · exfalso; rw [hcaR1] at hc_sub; exact h_aR1_ndj_S' hc_sub
    -- Interior
    have hc_S : block p c ⊆ S :=
      (interior_block_iff_S' c hcaL hcaL1 hcaR hcaR1).mp hc_sub
    have hc_arc : c ∈ arcIdx := (harcIdx c).mpr hc_S
    obtain ⟨i, hi, rfl⟩ := (harc_mem_iff c).mp hc_arc
    rw [Finset.mem_range] at hi
    have hi_pos : 0 < i := by
      by_contra h0
      push Not at h0
      apply hcaL1
      rw [haL_succ, ← arcVtx_zero]
      have : i = 0 := by omega
      rw [this]
    have hi_ne_pred : i ≠ m.pred := by
      intro h
      apply hcaR
      rw [haR_bm1, bm1_eq_arcVtx, h]
    have hmp : m.pred = m - 1 := Nat.pred_eq_sub_one
    refine ⟨i - 1, Finset.mem_range.mpr (by omega), ?_⟩
    rw [b1_eq_arcVtx]
    congr 1
    omega
  · rintro ⟨i, hi, rfl⟩
    rw [Finset.mem_range] at hi
    rw [b1_eq_arcVtx]
    have hi_succ : i + 1 < m := by omega
    have hci_arc : arcVtx (i + 1) ∈ arcIdx := arcVtx_mem_arcIdx (i + 1) hi_succ
    have hci_S : block p (arcVtx (i + 1)) ⊆ S := (harcIdx _).mp hci_arc
    have hizpz : i + 1 < p.z := Nat.lt_of_lt_of_le hi_succ hm_le
    have h_L : arcVtx (i + 1) ≠ aL := by
      intro heq
      have hi2 : i + 2 < p.z := by omega
      have h_succ_arc : arcVtx (i + 1) + 1 = arcVtx 0 := by
        rw [arcVtx_zero, ← haL_succ, heq]
      have h_eq : arcVtx (i + 2) = arcVtx 0 := by
        rw [← arcVtx_succ (i + 1)] at h_succ_arc; exact h_succ_arc
      have : i + 2 = 0 := arcVtx_inj hi2 p.hz_pos h_eq
      omega
    have h_L1 : arcVtx (i + 1) ≠ aL + 1 := by
      intro heq
      rw [haL_succ] at heq
      have : arcVtx (i + 1) = arcVtx 0 := by rw [heq, arcVtx_zero]
      have : i + 1 = 0 := arcVtx_inj hizpz p.hz_pos this
      omega
    have h_R : arcVtx (i + 1) ≠ aR := by
      rw [haR_bm1, bm1_eq_arcVtx]; intro heq
      have hmpredz : m.pred < p.z := Nat.lt_of_le_of_lt (Nat.pred_le _) hm_lt
      have : i + 1 = m.pred := arcVtx_inj hizpz hmpredz heq
      have hmp : m.pred = m - 1 := Nat.pred_eq_sub_one
      omega
    have h_R1 : arcVtx (i + 1) ≠ aR + 1 := by
      rw [haR_bm1, bm1_eq_arcVtx, arcVtx_pred_succ]; intro heq
      have : i + 1 = m := arcVtx_inj hizpz hm_lt heq
      omega
    exact (interior_block_iff_S' (arcVtx (i + 1)) h_L h_L1 h_R h_R1).mpr hci_S

/-- Row 5 of the 9-row witness table in `contiguousArc_break_seam_mixed`:
    inactive/active parity, `haL=sub`, `haR=disj` ⇒ witness `(b - 1, m)`. -/
private theorem row5_witness {p : Params} {S S' : Finset (VertexSet p)}
    (b aL aR bm1 : Fin p.z) (m : ℕ) (hm_ge2 : 1 < m) (hm_lt : m < p.z)
    (arcVtx : ℕ → Fin p.z)
    (arcVtx_inj : ∀ {i k : ℕ}, i < p.z → k < p.z → arcVtx i = arcVtx k → i = k)
    (arcVtx_succ : ∀ i, arcVtx (i + 1) = arcVtx i + 1)
    (arcVtx_zero : arcVtx 0 = b)
    (arcVtx_pred_succ : arcVtx m.pred + 1 = arcVtx m)
    (arcIdx : Finset (Fin p.z))
    (arcVtx_mem_arcIdx : ∀ i, i < m → arcVtx i ∈ arcIdx)
    (harcIdx : ∀ c : Fin p.z, c ∈ arcIdx ↔ block p c ⊆ S)
    (harc_mem_iff : ∀ c : Fin p.z, c ∈ arcIdx ↔ ∃ i ∈ Finset.range m, c = arcVtx i)
    (succ_eq : ∀ a : Fin p.z, (⟨(a.val + 1) % p.z, Nat.mod_lt _ p.hz_pos⟩ : Fin p.z) = a + 1)
    (interior_block_iff_S' : ∀ c : Fin p.z,
      c ≠ aL → c ≠ aL + 1 → c ≠ aR → c ≠ aR + 1 → (block p c ⊆ S' ↔ block p c ⊆ S))
    (build_arc_witness : ∀ (b' : Fin p.z) (m' : ℕ), m' ≤ p.z →
      (∀ c : Fin p.z, block p c ⊆ S' ↔
        ∃ i ∈ Finset.range m', c = ⟨(b'.val + i) % p.z, Nat.mod_lt _ p.hz_pos⟩) →
      IsContiguousArc p S')
    (haL_succ : aL + 1 = b) (haR_bm1 : aR = bm1)
    (bm1_eq_arcVtx : bm1 = arcVtx m.pred)
    (haL_sub : block p aL ∪ block p (aL + 1) ⊆ S')
    (haR_disj : Disjoint (block p aR ∪ block p (aR + 1)) S') :
    IsContiguousArc p S' := by
  have hm_pos : 0 < m := by omega
  have hm_le : m ≤ p.z := le_of_lt hm_lt
  have h1_mod : (1 : ℕ) % p.z = 1 := Nat.mod_eq_of_lt (by omega)
  have h_aL_sub_S' : block p aL ⊆ S' :=
    fun v hv => haL_sub (Finset.mem_union_left _ hv)
  have h_aL1_sub_S' : block p (aL + 1) ⊆ S' :=
    fun v hv => haL_sub (Finset.mem_union_right _ hv)
  have h_aR_ndj_S' : ¬ block p aR ⊆ S' := by
    intro hsub
    obtain ⟨v, hv⟩ := (⟨_, (mem_block p aR (aR, ⟨0, p.hk_pos⟩)).mpr rfl⟩ :
      (block p aR).Nonempty)
    exact (Finset.disjoint_left.mp haR_disj) (Finset.mem_union_left _ hv) (hsub hv)
  have h_aR1_ndj_S' : ¬ block p (aR + 1) ⊆ S' := by
    intro hsub
    obtain ⟨v, hv⟩ := (⟨_, (mem_block p (aR+1) (aR+1, ⟨0, p.hk_pos⟩)).mpr rfl⟩ :
      (block p (aR+1)).Nonempty)
    exact (Finset.disjoint_left.mp haR_disj) (Finset.mem_union_right _ hv) (hsub hv)
  -- arcVtx2 i := ⟨(aL.val + i) % p.z, _⟩
  let arcVtx2 : ℕ → Fin p.z := fun i => ⟨(aL.val + i) % p.z, Nat.mod_lt _ p.hz_pos⟩
  have arcVtx2_zero : arcVtx2 0 = aL := Fin.ext (by simp [arcVtx2, Nat.mod_eq_of_lt aL.isLt])
  have arcVtx2_one : arcVtx2 1 = aL + 1 := succ_eq aL
  have arcVtx2_succ : ∀ i, arcVtx2 (i + 1) = arcVtx2 i + 1 := by
    intro i
    rw [← succ_eq (arcVtx2 i)]
    apply Fin.ext
    show (aL.val + (i + 1)) % p.z = ((aL.val + i) % p.z + 1) % p.z
    have h1 : aL.val + (i + 1) = (aL.val + i) + 1 := by ring
    rw [h1, Nat.add_mod (aL.val + i) 1 p.z, h1_mod]
  have arcVtx2_shift : ∀ i, arcVtx2 (i + 1) = arcVtx i := by
    intro i
    induction i with
    | zero => rw [arcVtx2_one, haL_succ, ← arcVtx_zero]
    | succ k ih => rw [arcVtx2_succ (k + 1), ih, ← arcVtx_succ]
  refine build_arc_witness aL m hm_le ?_
  intro c
  show block p c ⊆ S' ↔ ∃ i ∈ Finset.range m, c = arcVtx2 i
  refine ⟨?_, ?_⟩
  · intro hc_sub
    by_cases hcaR : c = aR
    · exfalso; rw [hcaR] at hc_sub; exact h_aR_ndj_S' hc_sub
    by_cases hcaR1 : c = aR + 1
    · exfalso; rw [hcaR1] at hc_sub; exact h_aR1_ndj_S' hc_sub
    by_cases hcaL : c = aL
    · exact ⟨0, Finset.mem_range.mpr hm_pos, by rw [hcaL]; exact arcVtx2_zero.symm⟩
    by_cases hcaL1 : c = aL + 1
    · exact ⟨1, Finset.mem_range.mpr (by omega), by rw [hcaL1]; exact arcVtx2_one.symm⟩
    have hc_S : block p c ⊆ S :=
      (interior_block_iff_S' c hcaL hcaL1 hcaR hcaR1).mp hc_sub
    have hc_arc : c ∈ arcIdx := (harcIdx c).mpr hc_S
    obtain ⟨i, hi, rfl⟩ := (harc_mem_iff c).mp hc_arc
    rw [Finset.mem_range] at hi
    -- arcVtx i ≠ aR means i ≠ m.pred, so i ≤ m - 2, so i + 1 ≤ m - 1 < m
    have hi_ne_pred : i ≠ m.pred := by
      intro h
      apply hcaR
      rw [haR_bm1, bm1_eq_arcVtx, h]
    have hmp : m.pred = m - 1 := Nat.pred_eq_sub_one
    refine ⟨i + 1, Finset.mem_range.mpr (by omega), ?_⟩
    exact (arcVtx2_shift i).symm
  · rintro ⟨i, hi, rfl⟩
    rw [Finset.mem_range] at hi
    by_cases h0 : i = 0
    · subst h0; rw [arcVtx2_zero]; exact h_aL_sub_S'
    by_cases h1 : i = 1
    · subst h1; rw [arcVtx2_one]; exact h_aL1_sub_S'
    have hi_pos : 1 ≤ i := by omega
    have hi_pred : i - 1 < m - 1 := by omega
    have hi_pred' : i - 1 < m := by omega
    have hi_rw : i = (i - 1) + 1 := by omega
    rw [hi_rw, arcVtx2_shift]
    have hci_arc : arcVtx (i - 1) ∈ arcIdx := arcVtx_mem_arcIdx (i - 1) hi_pred'
    have hci_S : block p (arcVtx (i - 1)) ⊆ S := (harcIdx _).mp hci_arc
    have hizpz : i - 1 < p.z := Nat.lt_of_lt_of_le hi_pred' hm_le
    have hci_L : arcVtx (i - 1) ≠ aL := by
      intro heq
      have h_succ : arcVtx (i - 1) + 1 = arcVtx 0 := by
        rw [arcVtx_zero, ← haL_succ, heq]
      have h_arc_i : arcVtx i = arcVtx (i - 1) + 1 := by
        have hi_rw : i = (i - 1) + 1 := by omega
        conv_lhs => rw [hi_rw]
        exact arcVtx_succ (i - 1)
      rw [← h_arc_i] at h_succ
      have hizpz' : i < p.z := Nat.lt_of_lt_of_le hi hm_le
      have : i = 0 := arcVtx_inj hizpz' p.hz_pos h_succ
      exact h0 this
    have hci_L1 : arcVtx (i - 1) ≠ aL + 1 := by
      intro heq
      rw [haL_succ] at heq
      have : arcVtx (i - 1) = arcVtx 0 := by rw [heq, arcVtx_zero]
      have h0_eq : i - 1 = 0 := arcVtx_inj hizpz p.hz_pos this
      exact h1 (by omega)
    have hci_R : arcVtx (i - 1) ≠ aR := by
      rw [haR_bm1, bm1_eq_arcVtx]; intro heq
      have hmpredz : m.pred < p.z := Nat.lt_of_le_of_lt (Nat.pred_le _) hm_lt
      have : i - 1 = m.pred := arcVtx_inj hizpz hmpredz heq
      have hmp : m.pred = m - 1 := Nat.pred_eq_sub_one
      omega
    have hci_R1 : arcVtx (i - 1) ≠ aR + 1 := by
      rw [haR_bm1, bm1_eq_arcVtx, arcVtx_pred_succ]; intro heq
      have : i - 1 = m := arcVtx_inj hizpz hm_lt heq
      omega
    exact (interior_block_iff_S' (arcVtx (i - 1)) hci_L hci_L1 hci_R hci_R1).mpr hci_S

/-- Row 6 of the 9-row witness table in `contiguousArc_break_seam_mixed`:
    inactive/active parity, `haL=disj`, `haR=sub` ⇒ witness `(b + 1, m)`. -/
private theorem row6_witness {p : Params} {S S' : Finset (VertexSet p)}
    (b aL aR bm1 : Fin p.z) (m : ℕ) (hm_ge2 : 1 < m) (hm_lt : m < p.z)
    (arcVtx : ℕ → Fin p.z)
    (arcVtx_def : ∀ i, arcVtx i = ⟨(b.val + i) % p.z, Nat.mod_lt _ p.hz_pos⟩)
    (arcVtx_inj : ∀ {i k : ℕ}, i < p.z → k < p.z → arcVtx i = arcVtx k → i = k)
    (arcVtx_succ : ∀ i, arcVtx (i + 1) = arcVtx i + 1)
    (arcVtx_zero : arcVtx 0 = b)
    (arcVtx_pred_succ : arcVtx m.pred + 1 = arcVtx m)
    (arcIdx : Finset (Fin p.z))
    (arcVtx_mem_arcIdx : ∀ i, i < m → arcVtx i ∈ arcIdx)
    (harcIdx : ∀ c : Fin p.z, c ∈ arcIdx ↔ block p c ⊆ S)
    (harc_mem_iff : ∀ c : Fin p.z, c ∈ arcIdx ↔ ∃ i ∈ Finset.range m, c = arcVtx i)
    (interior_block_iff_S' : ∀ c : Fin p.z,
      c ≠ aL → c ≠ aL + 1 → c ≠ aR → c ≠ aR + 1 → (block p c ⊆ S' ↔ block p c ⊆ S))
    (build_arc_witness : ∀ (b' : Fin p.z) (m' : ℕ), m' ≤ p.z →
      (∀ c : Fin p.z, block p c ⊆ S' ↔
        ∃ i ∈ Finset.range m', c = ⟨(b'.val + i) % p.z, Nat.mod_lt _ p.hz_pos⟩) →
      IsContiguousArc p S')
    (haL_succ : aL + 1 = b) (haR_bm1 : aR = bm1)
    (bm1_eq_arcVtx : bm1 = arcVtx m.pred)
    (haL_disj : Disjoint (block p aL ∪ block p (aL + 1)) S')
    (haR_sub : block p aR ∪ block p (aR + 1) ⊆ S') :
    IsContiguousArc p S' := by
  have hm_pos : 0 < m := by omega
  have hm_le : m ≤ p.z := le_of_lt hm_lt
  have h1_mod : (1 : ℕ) % p.z = 1 := Nat.mod_eq_of_lt (by omega)
  have h_aL_ndj_S' : ¬ block p aL ⊆ S' := by
    intro hsub
    obtain ⟨v, hv⟩ := (⟨_, (mem_block p aL (aL, ⟨0, p.hk_pos⟩)).mpr rfl⟩ :
      (block p aL).Nonempty)
    exact (Finset.disjoint_left.mp haL_disj) (Finset.mem_union_left _ hv) (hsub hv)
  have h_aL1_ndj_S' : ¬ block p (aL + 1) ⊆ S' := by
    intro hsub
    obtain ⟨v, hv⟩ := (⟨_, (mem_block p (aL+1) (aL+1, ⟨0, p.hk_pos⟩)).mpr rfl⟩ :
      (block p (aL+1)).Nonempty)
    exact (Finset.disjoint_left.mp haL_disj) (Finset.mem_union_right _ hv) (hsub hv)
  have h_aR_sub_S' : block p aR ⊆ S' :=
    fun v hv => haR_sub (Finset.mem_union_left _ hv)
  have h_aR1_sub_S' : block p (aR + 1) ⊆ S' :=
    fun v hv => haR_sub (Finset.mem_union_right _ hv)
  refine build_arc_witness (b + 1) m hm_le ?_
  intro c
  have b1_eq_arcVtx : ∀ i, (⟨((b + 1).val + i) % p.z, Nat.mod_lt _ p.hz_pos⟩ : Fin p.z) =
      arcVtx (i + 1) := by
    intro i
    have h_b1_val : (b + 1 : Fin p.z).val = (b.val + 1) % p.z := by simp [Fin.val_add]
    apply Fin.ext
    show ((b + 1).val + i) % p.z = (arcVtx (i + 1)).val
    rw [arcVtx_def, h_b1_val, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    ring_nf
  show block p c ⊆ S' ↔ ∃ i ∈ Finset.range m, c =
      (⟨((b + 1).val + i) % p.z, Nat.mod_lt _ p.hz_pos⟩ : Fin p.z)
  refine ⟨?_, ?_⟩
  · intro hc_sub
    by_cases hcaL : c = aL
    · exfalso; rw [hcaL] at hc_sub; exact h_aL_ndj_S' hc_sub
    by_cases hcaL1 : c = aL + 1
    · exfalso; rw [hcaL1] at hc_sub; exact h_aL1_ndj_S' hc_sub
    by_cases hcaR : c = aR
    · -- c = aR = bm1 = arcVtx (m-1). b1 index: i = m - 2.
      refine ⟨m - 2, Finset.mem_range.mpr (by omega), ?_⟩
      rw [hcaR, haR_bm1, bm1_eq_arcVtx, b1_eq_arcVtx]
      have hmp : m.pred = m - 2 + 1 := by
        have : m.pred = m - 1 := Nat.pred_eq_sub_one
        omega
      rw [hmp]
    by_cases hcaR1 : c = aR + 1
    · -- c = aR + 1 = arcVtx m. b1 index: i = m - 1.
      refine ⟨m - 1, Finset.mem_range.mpr (by omega), ?_⟩
      -- Goal: c = ⟨((b+1).val + (m-1))%p.z, _⟩
      -- We have c = aR + 1 = bm1 + 1 = arcVtx m.pred + 1 = arcVtx m
      -- And b1 m-1 = arcVtx ((m-1) + 1) = arcVtx m. ✓
      rw [hcaR1, haR_bm1, bm1_eq_arcVtx, arcVtx_pred_succ]
      rw [b1_eq_arcVtx]
      have hmp : m = m - 1 + 1 := by omega
      conv_lhs => rw [hmp]
    -- Interior
    have hc_S : block p c ⊆ S :=
      (interior_block_iff_S' c hcaL hcaL1 hcaR hcaR1).mp hc_sub
    have hc_arc : c ∈ arcIdx := (harcIdx c).mpr hc_S
    obtain ⟨i, hi, rfl⟩ := (harc_mem_iff c).mp hc_arc
    rw [Finset.mem_range] at hi
    have hi_pos : 0 < i := by
      by_contra h0
      push Not at h0
      apply hcaL1
      rw [haL_succ, ← arcVtx_zero]
      have : i = 0 := by omega
      rw [this]
    refine ⟨i - 1, Finset.mem_range.mpr (by omega), ?_⟩
    rw [b1_eq_arcVtx]
    congr 1
    omega
  · rintro ⟨i, hi, rfl⟩
    rw [Finset.mem_range] at hi
    rw [b1_eq_arcVtx]
    have hi_succ : i + 1 < m + 1 := by omega
    by_cases h_R : arcVtx (i + 1) = aR
    · rw [h_R]; exact h_aR_sub_S'
    by_cases h_R1 : arcVtx (i + 1) = aR + 1
    · rw [h_R1]; exact h_aR1_sub_S'
    -- arcVtx (i+1) ∈ arcIdx iff i+1 < m
    have hi_succ_lt_m : i + 1 < m := by
      by_contra hge
      push Not at hge
      -- i + 1 = m. Then arcVtx (i+1) = arcVtx m = aR + 1.
      have hi_eq : i + 1 = m := by omega
      apply h_R1
      rw [haR_bm1, bm1_eq_arcVtx, arcVtx_pred_succ]
      rw [hi_eq]
    have hci_arc : arcVtx (i + 1) ∈ arcIdx := arcVtx_mem_arcIdx (i + 1) hi_succ_lt_m
    have hci_S : block p (arcVtx (i + 1)) ⊆ S := (harcIdx _).mp hci_arc
    have hizpz : i + 1 < p.z := Nat.lt_of_lt_of_le hi_succ_lt_m hm_le
    have h_L : arcVtx (i + 1) ≠ aL := by
      intro heq
      have hi2 : i + 2 < p.z := by omega
      have h_succ_arc : arcVtx (i + 1) + 1 = arcVtx 0 := by
        rw [arcVtx_zero, ← haL_succ, heq]
      have h_eq : arcVtx (i + 2) = arcVtx 0 := by
        rw [← arcVtx_succ (i + 1)] at h_succ_arc
        exact h_succ_arc
      have : i + 2 = 0 := arcVtx_inj hi2 p.hz_pos h_eq
      omega
    have h_L1 : arcVtx (i + 1) ≠ aL + 1 := by
      intro heq
      rw [haL_succ] at heq
      have : arcVtx (i + 1) = arcVtx 0 := by rw [heq, arcVtx_zero]
      have : i + 1 = 0 := arcVtx_inj hizpz p.hz_pos this
      omega
    exact (interior_block_iff_S' (arcVtx (i + 1)) h_L h_L1 h_R h_R1).mpr hci_S

/-- Row 9 of the 9-row witness table in `contiguousArc_break_seam_mixed`:
    inactive/inactive parity, `haL=disj`, `haR=sub` ⇒ witness `(b + 1, m - 1)`. -/
private theorem row9_witness {p : Params} {S S' : Finset (VertexSet p)}
    (b aL aR bm1 : Fin p.z) (m : ℕ) (hm_ge2 : 1 < m) (hm_lt : m < p.z)
    (arcVtx : ℕ → Fin p.z)
    (arcVtx_def : ∀ i, arcVtx i = ⟨(b.val + i) % p.z, Nat.mod_lt _ p.hz_pos⟩)
    (arcVtx_inj : ∀ {i k : ℕ}, i < p.z → k < p.z → arcVtx i = arcVtx k → i = k)
    (arcVtx_succ : ∀ i, arcVtx (i + 1) = arcVtx i + 1)
    (arcVtx_zero : arcVtx 0 = b)
    (arcVtx_predpred_succ : arcVtx (m.pred - 1) + 1 = arcVtx m.pred)
    (arcIdx : Finset (Fin p.z))
    (arcVtx_mem_arcIdx : ∀ i, i < m → arcVtx i ∈ arcIdx)
    (harcIdx : ∀ c : Fin p.z, c ∈ arcIdx ↔ block p c ⊆ S)
    (harc_mem_iff : ∀ c : Fin p.z, c ∈ arcIdx ↔ ∃ i ∈ Finset.range m, c = arcVtx i)
    (interior_block_iff_S' : ∀ c : Fin p.z,
      c ≠ aL → c ≠ aL + 1 → c ≠ aR → c ≠ aR + 1 → (block p c ⊆ S' ↔ block p c ⊆ S))
    (build_arc_witness : ∀ (b' : Fin p.z) (m' : ℕ), m' ≤ p.z →
      (∀ c : Fin p.z, block p c ⊆ S' ↔
        ∃ i ∈ Finset.range m', c = ⟨(b'.val + i) % p.z, Nat.mod_lt _ p.hz_pos⟩) →
      IsContiguousArc p S')
    (haL_succ : aL + 1 = b) (haR_succ : aR + 1 = bm1)
    (bm1_eq_arcVtx : bm1 = arcVtx m.pred)
    (haL_disj : Disjoint (block p aL ∪ block p (aL + 1)) S')
    (haR_sub : block p aR ∪ block p (aR + 1) ⊆ S') :
    IsContiguousArc p S' := by
  have hm_pos : 0 < m := by omega
  have hm_le : m ≤ p.z := le_of_lt hm_lt
  have h1_mod : (1 : ℕ) % p.z = 1 := Nat.mod_eq_of_lt (by omega)
  have h_aL_ndj_S' : ¬ block p aL ⊆ S' := by
    intro hsub
    obtain ⟨v, hv⟩ := (⟨_, (mem_block p aL (aL, ⟨0, p.hk_pos⟩)).mpr rfl⟩ :
      (block p aL).Nonempty)
    exact (Finset.disjoint_left.mp haL_disj) (Finset.mem_union_left _ hv) (hsub hv)
  have h_aL1_ndj_S' : ¬ block p (aL + 1) ⊆ S' := by
    intro hsub
    obtain ⟨v, hv⟩ := (⟨_, (mem_block p (aL+1) (aL+1, ⟨0, p.hk_pos⟩)).mpr rfl⟩ :
      (block p (aL+1)).Nonempty)
    exact (Finset.disjoint_left.mp haL_disj) (Finset.mem_union_right _ hv) (hsub hv)
  have h_aR_sub_S' : block p aR ⊆ S' :=
    fun v hv => haR_sub (Finset.mem_union_left _ hv)
  have h_aR1_sub_S' : block p (aR + 1) ⊆ S' :=
    fun v hv => haR_sub (Finset.mem_union_right _ hv)
  -- aR = arcVtx (m.pred - 1)
  have haR_arcVtx : aR = arcVtx (m.pred - 1) := by
    have h1 : aR + 1 = arcVtx (m.pred - 1) + 1 := by
      rw [haR_succ, bm1_eq_arcVtx, arcVtx_predpred_succ]
    have heq : aR + 1 + (-1 : Fin p.z) = arcVtx (m.pred - 1) + 1 + (-1 : Fin p.z) :=
      congrArg (· + (-1 : Fin p.z)) h1
    simpa [add_assoc] using heq
  -- arcVtx_b1 i := ⟨((aL+1).val + i)%p.z, _⟩ (i.e., starting at b = aL+1)
  -- Show arcVtx_b1 i = arcVtx (i+1).
  -- m = 2 corner case: aR = arcVtx 0 = b = aL + 1, so block_aR ⊆ S' from haR_sub
  -- contradicts block_(aL+1) disj S' from haL_disj.
  -- For m ≥ 3, the construction proceeds normally.
  -- First, eliminate the m = 2 corner via direct contradiction:
  by_cases hm2 : m = 2
  · exfalso
    -- haR_arcVtx : aR = arcVtx (m.pred - 1) = arcVtx 0 = b.
    -- haL_succ : aL + 1 = b. So aR = aL + 1.
    have haR_eq_aL1 : aR = aL + 1 := by
      rw [haR_arcVtx]
      have hmp : m.pred - 1 = 0 := by
        have : m.pred = m - 1 := Nat.pred_eq_sub_one
        omega
      rw [hmp, arcVtx_zero, ← haL_succ]
    -- block_aR ⊆ S' but block_(aL+1) disj S'.
    have h_aL1_S' : block p (aL + 1) ⊆ S' := haR_eq_aL1 ▸ h_aR_sub_S'
    exact h_aL1_ndj_S' h_aL1_S'
  have hm_ge3 : 3 ≤ m := by omega
  refine build_arc_witness (b + 1) (m - 1) (by omega) ?_
  intro c
  -- Re-index: ⟨((b+1).val + i)%p.z, _⟩ = arcVtx (i + 1).
  have b1_eq_arcVtx : ∀ i, (⟨((b + 1).val + i) % p.z, Nat.mod_lt _ p.hz_pos⟩ : Fin p.z) =
      arcVtx (i + 1) := by
    intro i
    have h_b1_val : (b + 1 : Fin p.z).val = (b.val + 1) % p.z := by simp [Fin.val_add]
    apply Fin.ext
    show ((b + 1).val + i) % p.z = (arcVtx (i + 1)).val
    have arcVtx_succ_val : (arcVtx (i + 1)).val = (b.val + (i + 1)) % p.z := by
      rw [arcVtx_def]
    rw [arcVtx_succ_val, h_b1_val, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    ring_nf
  show block p c ⊆ S' ↔ ∃ i ∈ Finset.range (m - 1), c =
      (⟨((b + 1).val + i) % p.z, Nat.mod_lt _ p.hz_pos⟩ : Fin p.z)
  refine ⟨?_, ?_⟩
  · intro hc_sub
    by_cases hcaL : c = aL
    · exfalso; rw [hcaL] at hc_sub; exact h_aL_ndj_S' hc_sub
    by_cases hcaL1 : c = aL + 1
    · exfalso; rw [hcaL1] at hc_sub; exact h_aL1_ndj_S' hc_sub
    by_cases hcaR : c = aR
    · -- c = aR = arcVtx (m.pred - 1) = arcVtx (m-2). b1 index: i s.t. arcVtx (i+1) = arcVtx (m-2),
      -- so i + 1 = m - 2, i.e., i = m - 3.
      refine ⟨m - 3, Finset.mem_range.mpr (by omega), ?_⟩
      rw [hcaR, haR_arcVtx, b1_eq_arcVtx]
      have hmp : m.pred - 1 = m - 3 + 1 := by
        have : m.pred = m - 1 := Nat.pred_eq_sub_one
        omega
      rw [hmp]
    by_cases hcaR1 : c = aR + 1
    · -- c = aR + 1 = bm1 = arcVtx (m-1). b1 index: i = m - 2.
      refine ⟨m - 2, Finset.mem_range.mpr (by omega), ?_⟩
      rw [hcaR1, haR_succ, bm1_eq_arcVtx, b1_eq_arcVtx]
      have hmp : m.pred = m - 2 + 1 := by
        have : m.pred = m - 1 := Nat.pred_eq_sub_one
        omega
      rw [hmp]
    -- Interior
    have hc_S : block p c ⊆ S :=
      (interior_block_iff_S' c hcaL hcaL1 hcaR hcaR1).mp hc_sub
    have hc_arc : c ∈ arcIdx := (harcIdx c).mpr hc_S
    obtain ⟨i, hi, rfl⟩ := (harc_mem_iff c).mp hc_arc
    rw [Finset.mem_range] at hi
    -- arcVtx i. We need to express c = arcVtx i = arcVtx_b1 (i - 1) = arcVtx_b1 j with j < m - 1.
    -- i ≠ 0 since c ≠ aL+1 = b = arcVtx 0.
    have hi_pos : 0 < i := by
      by_contra h0
      push Not at h0
      apply hcaL1
      rw [haL_succ, ← arcVtx_zero]
      have : i = 0 := by omega
      rw [this]
    refine ⟨i - 1, Finset.mem_range.mpr ?_, ?_⟩
    · -- i ≠ m - 1 (since c ≠ aR + 1 = bm1 = arcVtx (m-1))
      have hi_ne : i ≠ m - 1 := by
        intro h
        apply hcaR1
        rw [haR_succ, bm1_eq_arcVtx]
        have hmp : m.pred = m - 1 := Nat.pred_eq_sub_one
        rw [hmp, ← h]
      omega
    rw [b1_eq_arcVtx]
    congr 1
    omega
  · rintro ⟨i, hi, rfl⟩
    rw [Finset.mem_range] at hi
    rw [b1_eq_arcVtx]
    -- arcVtx (i+1), with i+1 ∈ [1, m-1]
    have hi_succ : i + 1 < m := by omega
    by_cases h_R : arcVtx (i + 1) = aR
    · rw [h_R]; exact h_aR_sub_S'
    by_cases h_R1 : arcVtx (i + 1) = aR + 1
    · rw [h_R1]; exact h_aR1_sub_S'
    have hci_arc : arcVtx (i + 1) ∈ arcIdx := arcVtx_mem_arcIdx (i + 1) hi_succ
    have hci_S : block p (arcVtx (i + 1)) ⊆ S := (harcIdx _).mp hci_arc
    have hizpz : i + 1 < p.z := Nat.lt_of_lt_of_le hi_succ hm_le
    have h_L : arcVtx (i + 1) ≠ aL := by
      intro heq
      -- aL = b - 1, but arcVtx (i+1) is at index i+1 ≥ 1. aL would correspond to arcVtx (p.z - 1).
      -- Argue: arcVtx (i+1) = aL = b + (-1). Then arcVtx (i+1) + 1 = b = arcVtx 0.
      -- arcVtx (i+1) + 1 = arcVtx (i+2). So arcVtx (i+2) = arcVtx 0 → i + 2 ≡ 0 (mod p.z).
      -- Since 0 ≤ i + 2 < p.z (i + 1 < p.z, but i + 2 might equal p.z), we need bound.
      -- Actually i + 2 ≤ m < p.z (since i + 1 ≤ m - 1 < m ≤ p.z - 1).
      have hi2 : i + 2 < p.z := by omega
      have h_succ_arc : arcVtx (i + 1) + 1 = arcVtx 0 := by
        rw [arcVtx_zero, ← haL_succ, heq]
      have h_eq : arcVtx (i + 2) = arcVtx 0 := by
        rw [← arcVtx_succ (i + 1)] at h_succ_arc
        exact h_succ_arc
      have : i + 2 = 0 := arcVtx_inj hi2 p.hz_pos h_eq
      omega
    have h_L1 : arcVtx (i + 1) ≠ aL + 1 := by
      intro heq
      rw [haL_succ] at heq
      have : arcVtx (i + 1) = arcVtx 0 := by rw [heq, arcVtx_zero]
      have : i + 1 = 0 := arcVtx_inj hizpz p.hz_pos this
      omega
    exact (interior_block_iff_S' (arcVtx (i + 1)) h_L h_L1 h_R h_R1).mpr hci_S

/-- Row 8 of the 9-row witness table in `contiguousArc_break_seam_mixed`:
    inactive/inactive parity, both seams `sub` ⇒ witness `(b - 1, m + 1)`.

All abstract data is passed as explicit parameters to escape the parent proof's
heartbeats budget. -/
private theorem row8_witness {p : Params} {S S' : Finset (VertexSet p)}
    (b aL aR bm1 : Fin p.z) (m : ℕ) (hm_ge2 : 1 < m) (hm_lt : m < p.z)
    (arcVtx : ℕ → Fin p.z)
    (arcVtx_inj : ∀ {i k : ℕ}, i < p.z → k < p.z → arcVtx i = arcVtx k → i = k)
    (arcVtx_succ : ∀ i, arcVtx (i + 1) = arcVtx i + 1)
    (arcVtx_zero : arcVtx 0 = b)
    (arcVtx_predpred_succ : arcVtx (m.pred - 1) + 1 = arcVtx m.pred)
    (arcIdx : Finset (Fin p.z))
    (arcVtx_mem_arcIdx : ∀ i, i < m → arcVtx i ∈ arcIdx)
    (harcIdx : ∀ c : Fin p.z, c ∈ arcIdx ↔ block p c ⊆ S)
    (harc_mem_iff : ∀ c : Fin p.z, c ∈ arcIdx ↔ ∃ i ∈ Finset.range m, c = arcVtx i)
    (succ_eq : ∀ a : Fin p.z, (⟨(a.val + 1) % p.z, Nat.mod_lt _ p.hz_pos⟩ : Fin p.z) = a + 1)
    (interior_block_iff_S' : ∀ c : Fin p.z,
      c ≠ aL → c ≠ aL + 1 → c ≠ aR → c ≠ aR + 1 → (block p c ⊆ S' ↔ block p c ⊆ S))
    (build_arc_witness : ∀ (b' : Fin p.z) (m' : ℕ), m' ≤ p.z →
      (∀ c : Fin p.z, block p c ⊆ S' ↔
        ∃ i ∈ Finset.range m', c = ⟨(b'.val + i) % p.z, Nat.mod_lt _ p.hz_pos⟩) →
      IsContiguousArc p S')
    (haL_succ : aL + 1 = b) (haR_succ : aR + 1 = bm1)
    (bm1_eq_arcVtx : bm1 = arcVtx m.pred)
    (haL_sub : block p aL ∪ block p (aL + 1) ⊆ S')
    (haR_sub : block p aR ∪ block p (aR + 1) ⊆ S') :
    IsContiguousArc p S' := by
  have hm_pos : 0 < m := by omega
  have hm_le : m ≤ p.z := le_of_lt hm_lt
  have h1_mod : (1 : ℕ) % p.z = 1 := Nat.mod_eq_of_lt (by omega)
  have h_aL_sub_S' : block p aL ⊆ S' :=
    fun v hv => haL_sub (Finset.mem_union_left _ hv)
  have h_aL1_sub_S' : block p (aL + 1) ⊆ S' :=
    fun v hv => haL_sub (Finset.mem_union_right _ hv)
  have h_aR_sub_S' : block p aR ⊆ S' :=
    fun v hv => haR_sub (Finset.mem_union_left _ hv)
  have h_aR1_sub_S' : block p (aR + 1) ⊆ S' :=
    fun v hv => haR_sub (Finset.mem_union_right _ hv)
  have haR_arcVtx : aR = arcVtx (m.pred - 1) := by
    have h1 : aR + 1 = arcVtx (m.pred - 1) + 1 := by
      rw [haR_succ, bm1_eq_arcVtx, arcVtx_predpred_succ]
    have heq : aR + 1 + (-1 : Fin p.z) = arcVtx (m.pred - 1) + 1 + (-1 : Fin p.z) :=
      congrArg (· + (-1 : Fin p.z)) h1
    simpa [add_assoc] using heq
  let arcVtx2 : ℕ → Fin p.z := fun i => ⟨(aL.val + i) % p.z, Nat.mod_lt _ p.hz_pos⟩
  have arcVtx2_zero : arcVtx2 0 = aL := Fin.ext (by simp [arcVtx2, Nat.mod_eq_of_lt aL.isLt])
  have arcVtx2_one : arcVtx2 1 = aL + 1 := succ_eq aL
  have arcVtx2_succ : ∀ i, arcVtx2 (i + 1) = arcVtx2 i + 1 := by
    intro i
    rw [← succ_eq (arcVtx2 i)]
    apply Fin.ext
    show (aL.val + (i + 1)) % p.z = ((aL.val + i) % p.z + 1) % p.z
    have h1 : aL.val + (i + 1) = (aL.val + i) + 1 := by ring
    rw [h1, Nat.add_mod (aL.val + i) 1 p.z, h1_mod]
  have arcVtx2_shift : ∀ i, arcVtx2 (i + 1) = arcVtx i := by
    intro i
    induction i with
    | zero => rw [arcVtx2_one, haL_succ, ← arcVtx_zero]
    | succ k ih => rw [arcVtx2_succ (k + 1), ih, ← arcVtx_succ]
  refine build_arc_witness aL (m + 1) (by omega) ?_
  intro c
  show block p c ⊆ S' ↔ ∃ i ∈ Finset.range (m + 1), c = arcVtx2 i
  refine ⟨?_, ?_⟩
  · intro hc_sub
    by_cases hcaL : c = aL
    · exact ⟨0, Finset.mem_range.mpr (by omega), by rw [hcaL]; exact arcVtx2_zero.symm⟩
    by_cases hcaL1 : c = aL + 1
    · exact ⟨1, Finset.mem_range.mpr (by omega), by rw [hcaL1]; exact arcVtx2_one.symm⟩
    by_cases hcaR : c = aR
    · refine ⟨m.pred, Finset.mem_range.mpr (by have := Nat.pred_le m; omega), ?_⟩
      have hmp : m.pred - 1 + 1 = m.pred := by
        have hp : m.pred = m - 1 := Nat.pred_eq_sub_one
        omega
      rw [hcaR, haR_arcVtx, ← arcVtx2_shift (m.pred - 1), hmp]
    by_cases hcaR1 : c = aR + 1
    · refine ⟨m, Finset.mem_range.mpr (by omega), ?_⟩
      have hmp : m.pred + 1 = m := Nat.succ_pred_eq_of_pos hm_pos
      rw [hcaR1, haR_succ, bm1_eq_arcVtx, ← arcVtx2_shift m.pred, hmp]
    have hc_S : block p c ⊆ S :=
      (interior_block_iff_S' c hcaL hcaL1 hcaR hcaR1).mp hc_sub
    have hc_arc : c ∈ arcIdx := (harcIdx c).mpr hc_S
    obtain ⟨i, hi, rfl⟩ := (harc_mem_iff c).mp hc_arc
    rw [Finset.mem_range] at hi
    refine ⟨i + 1, Finset.mem_range.mpr (by omega), ?_⟩
    exact (arcVtx2_shift i).symm
  · rintro ⟨i, hi, rfl⟩
    rw [Finset.mem_range] at hi
    by_cases h0 : i = 0
    · subst h0; rw [arcVtx2_zero]; exact h_aL_sub_S'
    by_cases h1 : i = 1
    · subst h1; rw [arcVtx2_one]; exact h_aL1_sub_S'
    have hi_pos : 1 ≤ i := by omega
    have hi_pred : i - 1 < m := by omega
    have hi_rw : i = (i - 1) + 1 := by omega
    rw [hi_rw, arcVtx2_shift]
    by_cases hci_R : arcVtx (i - 1) = aR
    · rw [hci_R]; exact h_aR_sub_S'
    by_cases hci_R1 : arcVtx (i - 1) = aR + 1
    · rw [hci_R1]; exact h_aR1_sub_S'
    have hci_arc : arcVtx (i - 1) ∈ arcIdx := arcVtx_mem_arcIdx (i - 1) hi_pred
    have hci_S : block p (arcVtx (i - 1)) ⊆ S := (harcIdx _).mp hci_arc
    have hizpz : i - 1 < p.z := Nat.lt_of_lt_of_le hi_pred hm_le
    have hci_L : arcVtx (i - 1) ≠ aL := by
      intro heq
      have h_succ : arcVtx (i - 1) + 1 = arcVtx 0 := by
        rw [arcVtx_zero, ← haL_succ, heq]
      have h_arc_i : arcVtx i = arcVtx (i - 1) + 1 := by
        have hi_rw : i = (i - 1) + 1 := by omega
        conv_lhs => rw [hi_rw]
        exact arcVtx_succ (i - 1)
      rw [← h_arc_i] at h_succ
      have hizpz' : i < p.z := Nat.lt_of_lt_of_le hi (by omega : m + 1 ≤ p.z)
      have : i = 0 := arcVtx_inj hizpz' p.hz_pos h_succ
      exact h0 this
    have hci_L1 : arcVtx (i - 1) ≠ aL + 1 := by
      intro heq
      rw [haL_succ] at heq
      have : arcVtx (i - 1) = arcVtx 0 := by rw [heq, arcVtx_zero]
      have h0_eq : i - 1 = 0 := arcVtx_inj hizpz p.hz_pos this
      exact h1 (by omega)
    exact (interior_block_iff_S' (arcVtx (i - 1)) hci_L hci_L1 hci_R hci_R1).mpr hci_S

private theorem zero_lt_sub_one_of_two_le {m : ℕ} (h : 2 ≤ m) : 0 < m - 1 := by omega

private theorem eq_two_of_le_and_sub_le {m : ℕ} (h1 : 2 ≤ m) (h2 : m - 1 ≤ 1) : m = 2 := by omega

private theorem pred_lt_of_pos {m : ℕ} (h : 0 < m) : m.pred < m := by
  have : m.pred = m - 1 := Nat.pred_eq_sub_one
  omega

private theorem pred_sub_one_lt_of_pos {m : ℕ} (h : 0 < m) : m.pred - 1 < m := by
  have : m.pred = m - 1 := Nat.pred_eq_sub_one
  omega

/-- Helper for `contiguousArc_step_structure`, part 2: arc-breakage localisation.

If a one-interval reachable `S'` is not a contiguous arc, then at least one of the
two boundary seam K_{2k}-cliques (anchors `aL`, `aR` of parity `j % 2`) is *mixed*
in `S'` — i.e., neither fully contained in `S'` nor disjoint from `S'`.

Mathematically: interior seam cliques start at consensus (all in `S` or all out)
and consensus is absorbing (`voterModel_empty/univ_absorbing` analog at the
clique level), so they remain at consensus in `S'`. Together with isolated-vertex
preservation, this means all blocks except possibly those in the boundary cliques
have the same fully-in / fully-out status as in `S`. If `S'` is not an arc, at
least one boundary clique must have lost the consensus that `S` has on it (or the
mixed arc-end blocks would have to align block-coherently, contradicting the
hypothesis that `S'` is not an arc).

Formalising this requires the same infrastructure as
`contiguousArc_blockCount_diff_le_two`, plus a structural argument that
"arc + ≤ 2 boundary clique deviations preserved as consensus ⇒ arc". Deferred. -/
private theorem contiguousArc_break_seam_mixed (p : Params) (j : ℕ)
    (S S' : Finset (VertexSet p)) (hS : IsContiguousArc p S)
    (_hop : VoterModel.opinionProcess₂ (lowerBoundGraph p) (j * p.T) p.T S S' ≠ 0)
    (_hS'_break : ¬IsContiguousArc p S') :
    let odd : Bool := decide (j % 2 = 1)
    let b := hS.choose
    let m := hS.choose_spec.choose
    let aL : Fin p.z := activeAnchor p odd b
    let aR : Fin p.z := activeAnchor p odd ⟨(b.val + m.pred) % p.z, Nat.mod_lt _ p.hz_pos⟩
    ¬(block p aL ∪ block p (aL + 1) ⊆ S' ∨
        Disjoint (block p aL ∪ block p (aL + 1) : Finset _) S') ∨
    ¬(block p aR ∪ block p (aR + 1) ⊆ S' ∨
        Disjoint (block p aR ∪ block p (aR + 1) : Finset _) S') := by
  -- By contradiction: assume both boundary seams at consensus in S'.
  -- All active interior seams are preserved at consensus by opinionProcess₂_consensus_preserved.
  -- Then every block has a definite status in S' (from its active seam).
  -- These blocks form a contiguous arc, contradicting _hS'_break.
  intro odd b m aL aR
  by_contra h
  push Not at h
  obtain ⟨haL_cons, haR_cons⟩ := h
  -- b and m are let-bound to hS.choose and hS.choose_spec.choose.
  -- Extract the witnesses: b = hS.choose, m = hS.choose_spec.choose
  obtain ⟨hm_le, hS_eq⟩ := hS.choose_spec.choose_spec
  -- Handle m = 0 (S = ∅): opinionProcess₂ ∅ T fixes at ∅, which is an arc.
  rcases Nat.eq_zero_or_pos m with hm0 | hm_pos
  · -- m is let-bound; use rfl to equate m with its definition, then rewrite
    have hS_empty : S = ∅ := by
      have hm_rfl : m = hS.choose_spec.choose := rfl
      rw [hS_eq, ← hm_rfl, hm0]; simp
    rw [hS_empty, opinionProcess₂_empty_eq_pure, PMF.pure_apply] at _hop
    split_ifs at _hop with h
    · exact _hS'_break ⟨⟨0, p.hz_pos⟩, 0, Nat.zero_le _, by simp [← h]⟩
    · exact absurd rfl _hop
  -- Local helpers (same as contiguousArc_blockCount_diff_le_two)
  have local_block_ne : ∀ c : Fin p.z, (block p c).Nonempty :=
    fun c => ⟨(c, ⟨0, p.hk_pos⟩), (mem_block p c _).mpr rfl⟩
  have local_arc_dichotomy : ∀ c : Fin p.z, block p c ⊆ S ∨ Disjoint (block p c) S := by
    intro c
    by_cases hex : ∃ i ∈ Finset.range m,
        c = (⟨(b.val + i) % p.z, Nat.mod_lt _ p.hz_pos⟩ : Fin p.z)
    · left; obtain ⟨i, hi, hci⟩ := hex; intro v hv; rw [mem_block] at hv; rw [hS_eq]
      exact Finset.mem_biUnion.mpr ⟨i, hi, by rw [mem_block, hv, hci]⟩
    · right; refine Finset.disjoint_left.mpr fun v hvb hvS => hex ?_
      rw [hS_eq] at hvS; obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp hvS
      exact ⟨i, hi, by rw [mem_block] at hvb hvi; rw [← hvb, hvi]⟩
  have succ_eq : ∀ a : Fin p.z,
      (⟨(a.val + 1) % p.z, Nat.mod_lt _ p.hz_pos⟩ : Fin p.z) = a + 1 :=
    fun a => Fin.ext (by simp [Fin.val_add])
  have hmap_ne_S' : ∀ a : Fin p.z, a.val % 2 = j % 2 →
      VoterModel.opinionProcess₂ (staticCliqueGraph p.k) 0 p.T (cliqueRestrict p a S)
        (cliqueRestrict p a S') ≠ 0 := by
    intro a ha
    have hmarg := opinionProcess₂_clique_marginal p a j p.T (le_refl _) ha S
    have hpos : 0 < VoterModel.opinionProcess₂ (lowerBoundGraph p) (j * p.T) p.T S S' :=
      lt_of_le_of_ne zero_le (Ne.symm _hop)
    have hmap_ne : (VoterModel.opinionProcess₂ (lowerBoundGraph p) (j * p.T) p.T S).map
        (cliqueRestrict p a) (cliqueRestrict p a S') ≠ 0 := by
      rw [PMF.map_apply]; apply ne_of_gt; refine lt_of_lt_of_le hpos ?_
      have hle := ENNReal.le_tsum
        (f := fun a_1 => if cliqueRestrict p a S' = cliqueRestrict p a a_1 then
            VoterModel.opinionProcess₂ (lowerBoundGraph p) (j * p.T) p.T S a_1 else 0) S'
      rw [if_pos rfl] at hle
      refine hle.trans (le_of_eq ?_); congr 1; ext; split_ifs <;> rfl
    rwa [← hmarg]
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
  -- Parity setup
  -- odd, aL, aR are already let-bound from the `intro` at the top
  -- (odd = decide (j%2=1), aL = activeAnchor p odd b, aR = activeAnchor p odd ...)
  -- haL_cons and haR_cons already use `a + 1` notation (not Fin.mk form)
  -- Step 3: all active seams at consensus in S'
  -- For interior active seams (≠ aL, aR): they are at consensus in S (arc),
  -- hence preserved by opinionProcess₂_consensus_preserved.
  -- For boundary active seams aL, aR: assumed by hypothesis.
  have all_active_cons : ∀ a : Fin p.z, a.val % 2 = j % 2 →
      block p a ∪ block p (a + 1) ⊆ S' ∨ Disjoint (block p a ∪ block p (a + 1) : Finset _) S' := by
    intro a ha
    by_cases haL_eq : a = aL
    · subst haL_eq; exact haL_cons
    by_cases haR_eq : a = aR
    · subst haR_eq; exact haR_cons
    -- Interior active seam a (≠ aL, aR): must be at consensus in S (arc structure).
    -- The interior seams lie entirely inside or outside the arc, hence at consensus.
    -- (Interior seams lie entirely inside or outside the arc.)
    have hcons_S : block p a ∪ block p (a + 1) ⊆ S ∨
        Disjoint (block p a ∪ block p (a + 1) : Finset _) S := by
      rcases local_arc_dichotomy a with ha_sub | ha_disj
      · rcases local_arc_dichotomy (a + 1) with ha1_sub | ha1_disj
        · -- Both in S: union ⊆ S
          exact Or.inl (Finset.union_subset ha_sub ha1_sub)
        · -- a ⊆ S, a+1 disjoint S: a is the last block of the arc → aR = a
          exfalso
          -- Extract arc index i such that a = ⟨(b+i)%p.z, _⟩
          obtain ⟨v, hv_a⟩ := local_block_ne a
          have hv_S : v ∈ S := ha_sub hv_a
          rw [hS_eq] at hv_S
          obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp hv_S
          rw [mem_block] at hvi hv_a
          -- v.1 = a (from hv_a) and v.1 = ⟨(b+i)%p.z,_⟩ (from hvi)
          have ha_eq : a = (⟨(b.val + i) % p.z, Nat.mod_lt _ p.hz_pos⟩ : Fin p.z) :=
            hv_a.symm.trans hvi
          have him : i < m := Finset.mem_range.mp hi
          -- Show i = m.pred: if i+1 < m, block (a+1) ⊆ S, contradicting ha1_disj
          have hi_pred : i = m.pred := by
            by_contra hi_ne
            have hmpred : m.pred + 1 = m := Nat.succ_pred_eq_of_pos hm_pos
            have hi1 : i + 1 < m := by omega
            -- a+1 = ⟨(b+(i+1))%p.z, _⟩
            have ha1_eq : (a + 1 : Fin p.z) =
                (⟨(b.val + (i + 1)) % p.z, Nat.mod_lt _ p.hz_pos⟩ : Fin p.z) := by
              apply Fin.ext
              have hav : a.val = (b.val + i) % p.z := congr_arg Fin.val ha_eq
              have hsucc : (a + 1 : Fin p.z).val = (a.val + 1) % p.z := by
                simp [Fin.val_add]
              rw [hsucc, hav]
              show ((b.val + i) % p.z + 1) % p.z = (b.val + (i + 1)) % p.z
              rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]; ring_nf
            have ha1_sub' : block p (a + 1) ⊆ S := by
              intro w hw; rw [mem_block] at hw; rw [hS_eq]
              exact Finset.mem_biUnion.mpr ⟨i + 1, Finset.mem_range.mpr hi1,
                by rw [mem_block, hw, ha1_eq]⟩
            obtain ⟨w, hw⟩ := local_block_ne (a + 1)
            exact absurd (ha1_sub' hw) (Finset.disjoint_left.mp ha1_disj hw)
          -- aR = activeAnchor p odd a (since a = ⟨(b+m.pred)%p.z,_⟩ = the aR input)
          have ha_par : a.val % 2 = parityNat odd := by
            unfold parityNat odd
            rcases Nat.mod_two_eq_zero_or_one j with hj | hj
            · simp only [hj]; norm_num; omega
            · simp only [hj]; norm_num; omega
          have haR_eq_a : aR = a := by
            show activeAnchor p odd ⟨(b.val + m.pred) % p.z, _⟩ = a
            have heq : (⟨(b.val + m.pred) % p.z, Nat.mod_lt _ p.hz_pos⟩ : Fin p.z) = a :=
              Fin.ext (by rw [ha_eq, hi_pred])
            rw [heq]; simp only [activeAnchor, ha_par, ite_true]
          exact haR_eq haR_eq_a.symm
      · rcases local_arc_dichotomy (a + 1) with ha1_sub | ha1_disj
        · -- a disjoint S, a+1 ⊆ S: a+1 is the first block of the arc → aL = a
          exfalso
          -- Extract arc index i such that a+1 = ⟨(b+i)%p.z, _⟩
          obtain ⟨v, hv_a1⟩ := local_block_ne (a + 1)
          have hv_S : v ∈ S := ha1_sub hv_a1
          rw [hS_eq] at hv_S
          obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp hv_S
          rw [mem_block] at hvi hv_a1
          have ha1_eq : (a + 1 : Fin p.z) =
              (⟨(b.val + i) % p.z, Nat.mod_lt _ p.hz_pos⟩ : Fin p.z) :=
            hv_a1.symm.trans hvi
          have him : i < m := Finset.mem_range.mp hi
          -- Show i = 0: if i > 0, block a ⊆ S contradicting ha_disj
          have hi0 : i = 0 := by
            by_contra hi_ne
            have hi1 : 0 < i := by omega
            -- a = ⟨(b+(i-1))%p.z, _⟩
            have ha_eq' : a = (⟨(b.val + (i - 1)) % p.z, Nat.mod_lt _ p.hz_pos⟩ : Fin p.z) := by
              apply Fin.ext
              have ha1v : (a + 1 : Fin p.z).val = (b.val + i) % p.z :=
                congr_arg Fin.val ha1_eq
              have hsucc : (a + 1 : Fin p.z).val = (a.val + 1) % p.z := by
                simp [Fin.val_add]
              -- (a.val+1) ≡ (b.val+i) mod p.z
              have heqmod : a.val + 1 ≡ b.val + i [MOD p.z] := by
                exact hsucc.symm.trans ha1v
              -- So a ≡ b+i-1 mod p.z (subtract 1 from both sides)
              have hpred : a.val ≡ b.val + i - 1 [MOD p.z] :=
                Nat.ModEq.sub (Nat.le_add_left 1 a.val) (by omega) heqmod (Nat.ModEq.refl 1)
              -- Since a < p.z, a % p.z = a, so a = (b+i-1) % p.z
              have haz : a.val < p.z := a.isLt
              have hbili : b.val + (i - 1) = b.val + i - 1 := by omega
              rw [hbili]
              unfold Nat.ModEq at hpred
              rw [Nat.mod_eq_of_lt haz] at hpred
              exact hpred
            have ha_sub' : block p a ⊆ S := by
              intro w hw; rw [mem_block] at hw; rw [hS_eq]
              exact Finset.mem_biUnion.mpr ⟨i - 1, Finset.mem_range.mpr (by omega),
                by rw [mem_block, hw, ha_eq']⟩
            obtain ⟨w, hw⟩ := local_block_ne a
            exact absurd (ha_sub' hw) (Finset.disjoint_left.mp ha_disj hw)
          -- aL = activeAnchor p odd b = a
          have ha_par : a.val % 2 = parityNat odd := by
            unfold parityNat odd
            rcases Nat.mod_two_eq_zero_or_one j with hj | hj
            · simp only [hj]; norm_num; omega
            · simp only [hj]; norm_num; omega
          have haL_eq_a : aL = a := by
            -- b = a+1 since a+1 = ⟨(b+0)%p.z,_⟩ = b
            have hb_eq : b = (a + 1 : Fin p.z) := by
              have h0 : (⟨(b.val + 0) % p.z, Nat.mod_lt _ p.hz_pos⟩ : Fin p.z) = b :=
                Fin.ext (by simp [Nat.mod_eq_of_lt b.isLt])
              rw [hi0] at ha1_eq; exact (h0 ▸ ha1_eq).symm
            show activeAnchor p odd b = a
            rw [hb_eq]; simp only [activeAnchor]
            have ha1_par : (a + 1).val % 2 ≠ parityNat odd :=
              (parity_add_one_ne_parity_iff p odd a).mpr ha_par
            simp only [ha1_par, ite_false]
            abel
          exact haL_eq haL_eq_a.symm
        · -- Both disjoint S
          exact Or.inr (Finset.disjoint_union_left.mpr ⟨ha_disj, ha1_disj⟩)
    exact opinionProcess₂_consensus_preserved p a j ha S S' hcons_S _hop
  -- Step 4: every block has a definite status in S' (from its active seam).
  have block_dichotomy_S' : ∀ c : Fin p.z, block p c ⊆ S' ∨ Disjoint (block p c) S' := by
    intro c
    let a := activeAnchor p odd c
    have ha_par : a.val % 2 = j % 2 := activeAnchor_parity_jmod2 p j c
    have ha_parity : a.val % 2 = parityNat odd := by
      show (activeAnchor p odd c).val % 2 = parityNat odd
      unfold activeAnchor
      by_cases hi : c.val % 2 = parityNat odd
      · simp [hi]
      · have hsub : (c + (-1) + 1 : Fin p.z) = c := by simp [add_assoc]
        have hneq : ((c + (-1) + 1).val % 2 ≠ parityNat odd) := by simpa [hsub] using hi
        have hpred : (c + (-1)).val % 2 = parityNat odd :=
          (parity_add_one_ne_parity_iff p odd (c + (-1))).1 hneq
        simp [hi, hpred]
    have hc_or : c = a ∨ c = a + 1 :=
      (activeAnchor_eq_iff_eq_or_succ p odd a c ha_parity).mp rfl
    rcases all_active_cons a ha_par with hsub | hdisj
    · rcases hc_or with hca | hca1
      · left; rw [hca]; exact fun v hv => hsub (Finset.mem_union_left _ hv)
      · left; rw [hca1]; exact fun v hv => hsub (Finset.mem_union_right _ hv)
    · rcases hc_or with hca | hca1
      · right; rw [hca]; exact Finset.disjoint_left.mpr fun v hv =>
          (Finset.disjoint_left.mp hdisj) (Finset.mem_union_left _ hv)
      · right; rw [hca1]; exact Finset.disjoint_left.mpr fun v hv =>
          (Finset.disjoint_left.mp hdisj) (Finset.mem_union_right _ hv)
  -- Step 5: construct an IsContiguousArc witness for S'.
  -- The in-blocks of S' form a consecutive arc: active seams give pairs {a, a+1}.
  -- If seam a ⊆ S', both blocks a and a+1 are in; if disjoint, both out.
  -- The pairs are consecutive (even-spaced), so the in-blocks form a run of blocks.
  -- We construct the witness directly using b' = first in-block and m' = count.
  apply _hS'_break
  -- Define the set of in-block indices
  let inB := (Finset.univ : Finset (Fin p.z)).filter (fun c => block p c ⊆ S')
  -- S' = biUnion of blocks in inB
  have hS'_eq : S' = inB.biUnion (block p) := by
    ext v
    simp only [inB, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hv
      rcases block_dichotomy_S' v.1 with hsub | hdisj
      · exact ⟨v.1, hsub, (mem_block p v.1 v).mpr rfl⟩
      · exact absurd hv (Finset.disjoint_left.mp hdisj ((mem_block p v.1 v).mpr rfl))
    · rintro ⟨c, hcsub, hvc⟩
      exact hcsub hvc
  -- Step 5a: pair-closure of inB:
  -- for any active anchor a (parity j%2), a ∈ inB ↔ a+1 ∈ inB.
  have pair_closed : ∀ a : Fin p.z, a.val % 2 = j % 2 →
      (a ∈ inB ↔ (a + 1) ∈ inB) := by
    intro a ha
    simp only [inB, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases all_active_cons a ha with hsub | hdisj
    · constructor
      · intro _; exact fun v hv => hsub (Finset.mem_union_right _ hv)
      · intro _; exact fun v hv => hsub (Finset.mem_union_left _ hv)
    · constructor
      · intro ha_sub
        exfalso
        obtain ⟨v, hv⟩ := local_block_ne a
        exact (Finset.disjoint_left.mp hdisj) (Finset.mem_union_left _ hv) (ha_sub hv)
      · intro ha1_sub
        exfalso
        obtain ⟨v, hv⟩ := local_block_ne (a + 1)
        exact (Finset.disjoint_left.mp hdisj) (Finset.mem_union_right _ hv) (ha1_sub hv)
  -- Step 5b: parity flip: if c has parity ≠ j%2, then c+1 has parity = j%2.
  have parity_flip : ∀ c : Fin p.z, ¬(c.val % 2 = j % 2) → (c + 1).val % 2 = j % 2 := by
    intro c hpar
    have hsucc : (c + 1 : Fin p.z).val % 2 = (c.val + 1) % 2 := by
      have : (c + 1 : Fin p.z).val = (c.val + 1) % p.z := by simp [Fin.val_add]
      rw [this, Nat.mod_mod_of_dvd _ p.hz_even]
    rcases Nat.mod_two_eq_zero_or_one c.val with hcv | hcv <;>
      rcases Nat.mod_two_eq_zero_or_one j with hj | hj <;> omega
  -- Step 5c: no-holes: if c ∈ inB and c+2 ∈ inB, then c+1 ∈ inB.
  -- (Stated as: c+1+1 so Lean unifies the "+2" in Fin operations.)
  have no_holes : ∀ c : Fin p.z, c ∈ inB → (c + 1 + 1) ∈ inB → (c + 1) ∈ inB := by
    intro c hc hc2
    by_cases hpar : c.val % 2 = j % 2
    · exact (pair_closed c hpar).mp hc
    · exact (pair_closed (c + 1) (parity_flip c hpar)).mpr hc2
  -- Step 5d: show inB is a consecutive cyclic interval using the arc structure of S.
  -- For interior active seams (a ≠ aL, a ≠ aR), the pair is at consensus in S,
  -- so seam_sub/disj_preserved gives: a ∈ inB ↔ block p a ⊆ S.
  -- The arc structure makes inB consecutive; we exhibit a witness directly.
  --
  -- arcIdx: the set of block indices in S (= arcIdx from the biUnion definition of S).
  let arcIdx : Finset (Fin p.z) :=
    (Finset.range m).image fun i => (⟨(b.val + i) % p.z, Nat.mod_lt _ p.hz_pos⟩ : Fin p.z)
  have harcIdx : ∀ c : Fin p.z, c ∈ arcIdx ↔ block p c ⊆ S := by
    intro c
    simp only [arcIdx, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨i, hi, hci⟩ v hv
      rw [mem_block] at hv; rw [hS_eq]
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr hi, by rw [mem_block, hv, hci]⟩
    · intro hcsub
      obtain ⟨v, hv⟩ := local_block_ne c
      have hvS : v ∈ S := hcsub hv
      rw [hS_eq] at hvS
      obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp hvS
      rw [mem_block] at hv hvi
      exact ⟨i, Finset.mem_range.mp hi, by rw [← hv]; exact hvi.symm⟩
  -- For interior active anchor a (a ≠ aL, a ≠ aR): a ∈ inB ↔ a ∈ arcIdx.
  have interior_eq : ∀ a : Fin p.z, a.val % 2 = j % 2 → a ≠ aL → a ≠ aR →
      (a ∈ inB ↔ a ∈ arcIdx) := by
    intro a ha haL_ne haR_ne
    simp only [inB, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [harcIdx]
    constructor
    · -- block a ⊆ S' → block a ⊆ S
      intro ha_sub'
      -- From local_arc_dichotomy: block a ⊆ S ∨ Disjoint (block a) S.
      -- If disjoint: need to derive contradiction.
      rcases local_arc_dichotomy a with ha_sub | ha_disj
      · exact ha_sub
      · -- block a disjoint S.
        -- Subcase: block (a+1) ⊆ S → a = aL (would contradict haL_ne).
        rcases local_arc_dichotomy (a + 1) with ha1_sub | ha1_disj
        · -- a disjoint S, a+1 ⊆ S → (same arg as in all_active_cons) a = aL
          exfalso
          obtain ⟨v, hv_a1⟩ := local_block_ne (a + 1)
          have hv_S : v ∈ S := ha1_sub hv_a1
          rw [hS_eq] at hv_S
          obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp hv_S
          rw [mem_block] at hvi hv_a1
          have ha1_eq : (a + 1 : Fin p.z) =
              (⟨(b.val + i) % p.z, Nat.mod_lt _ p.hz_pos⟩ : Fin p.z) := hv_a1.symm.trans hvi
          have him : i < m := Finset.mem_range.mp hi
          have hi0 : i = 0 := by
            by_contra hi_ne
            have hi1 : 0 < i := Nat.pos_of_ne_zero hi_ne
            have ha_eq' : a = (⟨(b.val + (i - 1)) % p.z, Nat.mod_lt _ p.hz_pos⟩ : Fin p.z) := by
              apply Fin.ext
              have ha1v : (a + 1 : Fin p.z).val = (b.val + i) % p.z :=
                congr_arg Fin.val ha1_eq
              have hsucc : (a + 1 : Fin p.z).val = (a.val + 1) % p.z := by simp [Fin.val_add]
              have heqmod : a.val + 1 ≡ b.val + i [MOD p.z] := by
                exact hsucc.symm.trans ha1v
              have hpred : a.val ≡ b.val + i - 1 [MOD p.z] :=
                Nat.ModEq.sub (Nat.le_add_left 1 a.val) (by omega) heqmod (Nat.ModEq.refl 1)
              have haz : a.val < p.z := a.isLt
              have hbili : b.val + (i - 1) = b.val + i - 1 := by omega
              rw [hbili]; unfold Nat.ModEq at hpred
              rw [Nat.mod_eq_of_lt haz] at hpred; exact hpred
            have ha_sub' : block p a ⊆ S := by
              intro w hw; rw [mem_block] at hw; rw [hS_eq]
              exact Finset.mem_biUnion.mpr ⟨i - 1, Finset.mem_range.mpr (by omega),
                by rw [mem_block, hw, ha_eq']⟩
            obtain ⟨w, hw⟩ := local_block_ne a
            exact absurd (ha_sub' hw) (Finset.disjoint_left.mp ha_disj hw)
          -- i = 0, so a+1 = b. Then aL = activeAnchor p odd b = activeAnchor p odd (a+1).
          have ha_par : a.val % 2 = parityNat odd := by
            unfold parityNat odd
            rcases Nat.mod_two_eq_zero_or_one j with hj | hj <;>
              simp only [hj] <;> norm_num <;> omega
          have haL_eq_a : aL = a := by
            have hb_eq : b = (a + 1 : Fin p.z) := by
              have h0 : (⟨(b.val + 0) % p.z, Nat.mod_lt _ p.hz_pos⟩ : Fin p.z) = b :=
                Fin.ext (by simp [Nat.mod_eq_of_lt b.isLt])
              rw [hi0] at ha1_eq; exact (h0 ▸ ha1_eq).symm
            show activeAnchor p odd b = a
            rw [hb_eq]; simp only [activeAnchor]
            have ha1_par : (a + 1).val % 2 ≠ parityNat odd :=
              (parity_add_one_ne_parity_iff p odd a).mpr ha_par
            simp only [ha1_par, ite_false]; abel
          exact haL_ne haL_eq_a.symm
        · -- both a and a+1 disjoint S → pair disjoint S → seam_disj_preserved → pair disj S'
          have hdisj_S : Disjoint (block p a ∪ block p (a + 1)) S :=
            Finset.disjoint_union_left.mpr ⟨ha_disj, ha1_disj⟩
          have hdisj_S' := seam_disj_preserved a ha hdisj_S
          exfalso
          obtain ⟨v, hv⟩ := local_block_ne a
          exact (Finset.disjoint_left.mp hdisj_S') (Finset.mem_union_left _ hv) (ha_sub' hv)
    · -- block a ⊆ S → block a ⊆ S'
      intro ha_sub
      -- For interior a (a ≠ aR): block (a+1) ⊆ S too (else a = aR).
      have ha1_sub : block p (a + 1) ⊆ S := by
        rcases local_arc_dichotomy (a + 1) with h | h
        · exact h
        · exfalso
          obtain ⟨v, hv_a⟩ := local_block_ne a
          have hv_S : v ∈ S := ha_sub hv_a
          rw [hS_eq] at hv_S
          obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp hv_S
          rw [mem_block] at hvi hv_a
          have ha_eq : a = (⟨(b.val + i) % p.z, Nat.mod_lt _ p.hz_pos⟩ : Fin p.z) :=
            hv_a.symm.trans hvi
          have him : i < m := Finset.mem_range.mp hi
          have hi_pred : i = m.pred := by
            by_contra hi_ne
            have hmpred : m.pred + 1 = m := Nat.succ_pred_eq_of_pos hm_pos
            have hi1 : i + 1 < m := by omega
            have ha1_eq : (a + 1 : Fin p.z) =
                (⟨(b.val + (i + 1)) % p.z, Nat.mod_lt _ p.hz_pos⟩ : Fin p.z) := by
              apply Fin.ext
              have hav : a.val = (b.val + i) % p.z := congr_arg Fin.val ha_eq
              have hsucc : (a + 1 : Fin p.z).val = (a.val + 1) % p.z := by simp [Fin.val_add]
              rw [hsucc, hav]
              show ((b.val + i) % p.z + 1) % p.z = (b.val + (i + 1)) % p.z
              rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]; ring_nf
            have ha1_sub' : block p (a + 1) ⊆ S := by
              intro w hw; rw [mem_block] at hw; rw [hS_eq]
              exact Finset.mem_biUnion.mpr ⟨i + 1, Finset.mem_range.mpr hi1,
                by rw [mem_block, hw, ha1_eq]⟩
            obtain ⟨w, hw⟩ := local_block_ne (a + 1)
            exact absurd (ha1_sub' hw) (Finset.disjoint_left.mp h hw)
          -- a = b + m.pred → aR = a.
          have ha_par : a.val % 2 = parityNat odd := by
            unfold parityNat odd
            rcases Nat.mod_two_eq_zero_or_one j with hj | hj <;>
              simp only [hj] <;> norm_num <;> omega
          have haR_eq_a : aR = a := by
            show activeAnchor p odd ⟨(b.val + m.pred) % p.z, _⟩ = a
            have heq : (⟨(b.val + m.pred) % p.z, Nat.mod_lt _ p.hz_pos⟩ : Fin p.z) = a :=
              Fin.ext (by rw [ha_eq, hi_pred])
            rw [heq]; simp only [activeAnchor, ha_par, ite_true]
          exact haR_ne haR_eq_a.symm
      -- pair ⊆ S → seam_sub_preserved → pair ⊆ S'
      have hpair_sub : block p a ∪ block p (a + 1) ⊆ S :=
        Finset.union_subset ha_sub ha1_sub
      have hpair_sub' := seam_sub_preserved a ha hpair_sub
      exact fun v hv => hpair_sub' (Finset.mem_union_left _ hv)
  -- Step 5e: handle m = p.z (S = univ → S' = univ, an arc).
  by_cases hm_full : m = p.z
  · -- S = univ
    have hS_univ : S = Finset.univ := by
      apply Finset.eq_univ_of_forall; intro v; rw [hS_eq]
      let i := (v.1.val + p.z - b.val) % p.z
      refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr ?_, ?_⟩
      · show i < m; rw [hm_full]; exact Nat.mod_lt _ p.hz_pos
      · rw [mem_block]; apply Fin.ext
        show v.1.val = (b.val + i) % p.z
        simp only [i]
        have hbz : b.val < p.z := b.isLt
        have hvz : v.1.val < p.z := v.1.isLt
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        have heq : b.val + (v.1.val + p.z - b.val) = v.1.val + p.z := by omega
        rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt hvz]
    -- All blocks in S → all active seams ⊆ S → seam_sub_preserved → all blocks in S'.
    -- So S' = univ.
    have hS'_univ : S' = Finset.univ := by
      apply Finset.eq_univ_of_forall; intro v
      have hv_S : v ∈ S := hS_univ ▸ Finset.mem_univ _
      let a := activeAnchor p odd v.1
      have ha_par : a.val % 2 = j % 2 := activeAnchor_parity_jmod2 p j v.1
      have ha_parity : a.val % 2 = parityNat odd := by
        show (activeAnchor p odd v.1).val % 2 = parityNat odd
        exact activeAnchor_parity p odd v.1
      have hc_or : v.1 = a ∨ v.1 = a + 1 :=
        (activeAnchor_eq_iff_eq_or_succ p odd a v.1 ha_parity).mp rfl
      have hpair_sub : block p a ∪ block p (a + 1) ⊆ S :=
        fun w _ => hS_univ ▸ Finset.mem_univ _
      have hpair_sub' := seam_sub_preserved a ha_par hpair_sub
      rcases hc_or with h | h
      · exact hpair_sub' (Finset.mem_union_left _ ((mem_block p a v).mpr h))
      · exact hpair_sub' (Finset.mem_union_right _ ((mem_block p (a + 1) v).mpr h))
    exact ⟨⟨0, p.hz_pos⟩, p.z, le_refl _, by
      rw [hS'_univ]; symm
      apply Finset.eq_univ_of_forall; intro v
      refine Finset.mem_biUnion.mpr ⟨v.1.val, Finset.mem_range.mpr v.1.isLt, ?_⟩
      rw [mem_block]; apply Fin.ext
      show v.1.val = (0 + v.1.val) % p.z
      rw [Nat.zero_add, Nat.mod_eq_of_lt v.1.isLt]⟩
  -- Main case: 1 ≤ m < p.z. We construct an explicit `(b', m')` witness per case row.
  have hm_lt : m < p.z := lt_of_le_of_ne hm_le hm_full
  have hpz_two_le : 2 ≤ p.z := p.hz_two_le
  have h1_mod : (1 : ℕ) % p.z = 1 := Nat.mod_eq_of_lt (by omega)
  -- arcVtx: i-th cyclic block index starting at b. arcVtx 0 = b; arcVtx_succ; arcVtx_inj.
  let arcVtx : ℕ → Fin p.z := fun i => ⟨(b.val + i) % p.z, Nat.mod_lt _ p.hz_pos⟩
  have arcVtx_zero : arcVtx 0 = b :=
    Fin.ext (by simp [arcVtx, Nat.mod_eq_of_lt b.isLt])
  have hb_idx0 : (⟨(b.val + 0) % p.z, Nat.mod_lt _ p.hz_pos⟩ : Fin p.z) = b := arcVtx_zero
  -- Step (b): characterize `block p c ⊆ S'` for c outside the boundary set {aL, aL+1, aR, aR+1}.
  have interior_block_iff_S' : ∀ c : Fin p.z,
      c ≠ aL → c ≠ aL + 1 → c ≠ aR → c ≠ aR + 1 →
      (block p c ⊆ S' ↔ block p c ⊆ S) := by
    intro c hcL hcL1 hcR hcR1
    by_cases hc_par : c.val % 2 = j % 2
    · have hiff : c ∈ inB ↔ c ∈ arcIdx := interior_eq c hc_par hcL hcR
      simp only [inB, Finset.mem_filter, Finset.mem_univ, true_and] at hiff
      rw [harcIdx] at hiff; exact hiff
    · set a : Fin p.z := c + (-1 : Fin p.z) with ha_def
      have ha_succ : a + 1 = c := by simp [ha_def, add_assoc]
      have ha_par : a.val % 2 = j % 2 := by
        by_contra hne
        have : (a + 1).val % 2 = j % 2 := parity_flip a hne
        rw [ha_succ] at this; exact hc_par this
      have ha_ne_aL : a ≠ aL := fun h => hcL1 (by rw [← ha_succ, h])
      have ha_ne_aR : a ≠ aR := fun h => hcR1 (by rw [← ha_succ, h])
      have hpair_S' : (block p a ⊆ S') ↔ (block p c ⊆ S') := by
        have hpc := pair_closed a ha_par
        simp only [inB, Finset.mem_filter, Finset.mem_univ, true_and] at hpc
        rw [← ha_succ]; exact hpc
      have h_a_iff : (block p a ⊆ S') ↔ (block p a ⊆ S) := by
        have hint := interior_eq a ha_par ha_ne_aL ha_ne_aR
        simp only [inB, Finset.mem_filter, Finset.mem_univ, true_and] at hint
        rw [harcIdx] at hint; exact hint
      -- S-side consensus at the active interior pair {a, a+1}: derive from `local_arc_dichotomy`
      -- and exclusion of aL/aR (the active "boundary" anchors).
      have hpair_S : (block p a ⊆ S) ↔ (block p (a + 1) ⊆ S) := by
        rcases local_arc_dichotomy a with ha_subS | ha_disjS
        · rcases local_arc_dichotomy (a + 1) with ha1_subS | ha1_disjS
          · exact ⟨fun _ => ha1_subS, fun _ => ha_subS⟩
          · -- block a ⊆ S, block (a+1) disjoint S: would force aR = a, contradiction.
            exfalso
            obtain ⟨v, hv_a⟩ := local_block_ne a
            have hv_S : v ∈ S := ha_subS hv_a
            rw [hS_eq] at hv_S
            obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp hv_S
            rw [mem_block] at hvi hv_a
            have ha_eq : a = (⟨(b.val + i) % p.z, Nat.mod_lt _ p.hz_pos⟩ : Fin p.z) :=
              hv_a.symm.trans hvi
            have him : i < m := Finset.mem_range.mp hi
            have hi_pred : i = m.pred := by
              by_contra hi_ne
              have hmpred : m.pred + 1 = m := Nat.succ_pred_eq_of_pos hm_pos
              have hi1 : i + 1 < m := by omega
              have ha1_eq : (a + 1 : Fin p.z) =
                  (⟨(b.val + (i + 1)) % p.z, Nat.mod_lt _ p.hz_pos⟩ : Fin p.z) := by
                apply Fin.ext
                have hav : a.val = (b.val + i) % p.z := congr_arg Fin.val ha_eq
                have hsucc' : (a + 1 : Fin p.z).val = (a.val + 1) % p.z := by simp [Fin.val_add]
                rw [hsucc', hav]
                show ((b.val + i) % p.z + 1) % p.z = (b.val + (i + 1)) % p.z
                rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]; ring_nf
              have ha1_subS' : block p (a + 1) ⊆ S := by
                intro w hw; rw [mem_block] at hw; rw [hS_eq]
                exact Finset.mem_biUnion.mpr ⟨i + 1, Finset.mem_range.mpr hi1,
                  by rw [mem_block, hw, ha1_eq]⟩
              obtain ⟨w, hw⟩ := local_block_ne (a + 1)
              exact absurd (ha1_subS' hw) (Finset.disjoint_left.mp ha1_disjS hw)
            have ha_p : a.val % 2 = parityNat odd := by
              unfold parityNat odd
              rcases Nat.mod_two_eq_zero_or_one j with hj | hj <;>
                simp only [hj] <;> norm_num <;> omega
            have haR_eq_a : aR = a := by
              show activeAnchor p odd ⟨(b.val + m.pred) % p.z, _⟩ = a
              have heq : (⟨(b.val + m.pred) % p.z, Nat.mod_lt _ p.hz_pos⟩ : Fin p.z) = a :=
                Fin.ext (by rw [ha_eq, hi_pred])
              rw [heq]; simp only [activeAnchor, ha_p, ite_true]
            exact ha_ne_aR haR_eq_a.symm
        · rcases local_arc_dichotomy (a + 1) with ha1_subS | ha1_disjS
          · -- block a disjoint S, block (a+1) ⊆ S: would force aL = a, contradiction.
            exfalso
            obtain ⟨v, hv_a1⟩ := local_block_ne (a + 1)
            have hv_S : v ∈ S := ha1_subS hv_a1
            rw [hS_eq] at hv_S
            obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp hv_S
            rw [mem_block] at hvi hv_a1
            have ha1_eq : (a + 1 : Fin p.z) =
                (⟨(b.val + i) % p.z, Nat.mod_lt _ p.hz_pos⟩ : Fin p.z) :=
              hv_a1.symm.trans hvi
            have him : i < m := Finset.mem_range.mp hi
            have hi0 : i = 0 := by
              by_contra hi_ne
              have hi1 : 0 < i := Nat.pos_of_ne_zero hi_ne
              have ha_eq' : a = (⟨(b.val + (i - 1)) % p.z, Nat.mod_lt _ p.hz_pos⟩ : Fin p.z) := by
                apply Fin.ext
                have ha1v : (a + 1 : Fin p.z).val = (b.val + i) % p.z :=
                  congr_arg Fin.val ha1_eq
                have hsucc' : (a + 1 : Fin p.z).val = (a.val + 1) % p.z := by simp [Fin.val_add]
                have heqmod : a.val + 1 ≡ b.val + i [MOD p.z] := by
                  exact hsucc'.symm.trans ha1v
                have hpred : a.val ≡ b.val + i - 1 [MOD p.z] :=
                  Nat.ModEq.sub (Nat.le_add_left 1 a.val) (by omega) heqmod (Nat.ModEq.refl 1)
                have haz : a.val < p.z := a.isLt
                have hbili : b.val + (i - 1) = b.val + i - 1 := by omega
                rw [hbili]; unfold Nat.ModEq at hpred
                rw [Nat.mod_eq_of_lt haz] at hpred; exact hpred
              have ha_subS' : block p a ⊆ S := by
                intro w hw; rw [mem_block] at hw; rw [hS_eq]
                exact Finset.mem_biUnion.mpr ⟨i - 1, Finset.mem_range.mpr (by omega),
                  by rw [mem_block, hw, ha_eq']⟩
              obtain ⟨w, hw⟩ := local_block_ne a
              exact absurd (ha_subS' hw) (Finset.disjoint_left.mp ha_disjS hw)
            have ha_p : a.val % 2 = parityNat odd := by
              unfold parityNat odd
              rcases Nat.mod_two_eq_zero_or_one j with hj | hj <;>
                simp only [hj] <;> norm_num <;> omega
            have haL_eq_a : aL = a := by
              have hb_eq : b = (a + 1 : Fin p.z) := by
                have h0 : (⟨(b.val + 0) % p.z, Nat.mod_lt _ p.hz_pos⟩ : Fin p.z) = b :=
                  Fin.ext (by simp [Nat.mod_eq_of_lt b.isLt])
                rw [hi0] at ha1_eq; exact (h0 ▸ ha1_eq).symm
              show activeAnchor p odd b = a
              rw [hb_eq]; simp only [activeAnchor]
              have ha1_p : (a + 1).val % 2 ≠ parityNat odd :=
                (parity_add_one_ne_parity_iff p odd a).mpr ha_p
              simp only [ha1_p, ite_false]; abel
            exact ha_ne_aL haL_eq_a.symm
          · -- both disjoint
            refine ⟨fun h => ?_, fun h => ?_⟩
            · exfalso
              obtain ⟨v, hv⟩ := local_block_ne a
              exact (Finset.disjoint_left.mp ha_disjS) hv (h hv)
            · exfalso
              obtain ⟨v, hv⟩ := local_block_ne (a + 1)
              exact (Finset.disjoint_left.mp ha1_disjS) hv (h hv)
      rw [← hpair_S', h_a_iff, hpair_S, ha_succ]
  -- Step (c): arc-witness assembler. Given a characterization of which c satisfy
  -- `block p c ⊆ S'` as a range image starting from `b'`, derive `IsContiguousArc p S'`.
  have build_arc_witness : ∀ (b' : Fin p.z) (m' : ℕ), m' ≤ p.z →
      (∀ c : Fin p.z, (block p c ⊆ S') ↔
          ∃ i ∈ Finset.range m',
            c = (⟨(b'.val + i) % p.z, Nat.mod_lt _ p.hz_pos⟩ : Fin p.z)) →
      IsContiguousArc p S' := by
    intro b' m' hm'_le hchar
    refine ⟨b', m', hm'_le, ?_⟩
    ext v
    simp only [Finset.mem_biUnion, Finset.mem_range]
    constructor
    · intro hv
      rcases block_dichotomy_S' v.1 with hsub | hdisj
      · obtain ⟨i, hi, hci⟩ := (hchar v.1).mp hsub
        refine ⟨i, Finset.mem_range.mp hi, ?_⟩
        rw [mem_block, hci]
      · exact absurd hv (Finset.disjoint_left.mp hdisj ((mem_block p v.1 v).mpr rfl))
    · rintro ⟨i, hi, hvi⟩
      rw [mem_block] at hvi
      have hcsub : block p ⟨(b'.val + i) % p.z, Nat.mod_lt _ p.hz_pos⟩ ⊆ S' :=
        (hchar _).mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩
      exact hcsub ((mem_block p _ v).mpr hvi)
  -- Helper: arcIdx singleton when m = 1.
  have harc_mem_iff : ∀ c : Fin p.z, c ∈ arcIdx ↔
      ∃ i ∈ Finset.range m, c = (⟨(b.val + i) % p.z, Nat.mod_lt _ p.hz_pos⟩ : Fin p.z) := by
    intro c; simp [arcIdx, Finset.mem_image, Finset.mem_range, eq_comm]
  -- Step (d): m = 1 case. aL = aR. Two subcases on haL_cons.
  rcases Nat.eq_or_lt_of_le hm_pos with hm1 | hm_ge2
  · have hm_one : m = 1 := hm1.symm
    have harcIdx_singleton : arcIdx = {b} := by
      ext c
      simp only [harc_mem_iff, hm_one, Finset.mem_range, Nat.lt_one_iff,
        Finset.mem_singleton]
      refine ⟨?_, ?_⟩
      · rintro ⟨i, hi, hci⟩; rw [hi] at hci; rw [hci, hb_idx0]
      · rintro rfl; exact ⟨0, rfl, hb_idx0.symm⟩
    have haR_eq_aL : aR = aL := by
      show activeAnchor p odd ⟨(b.val + m.pred) % p.z, Nat.mod_lt _ p.hz_pos⟩ =
          activeAnchor p odd b
      congr 1; apply Fin.ext
      simp [hm_one, Nat.mod_eq_of_lt b.isLt]
    -- aL ∈ {b, b+1} structurally; either way `haL_cons` gives sub/disj for the same pair.
    rcases haL_cons with haL_sub | haL_disj
    · -- haL_sub: seam_aL ⊆ S'. Witness (aL, 2).
      refine build_arc_witness aL 2 (by omega) ?_
      intro c
      refine ⟨?_, ?_⟩
      · intro hc_sub
        by_cases hcaL : c = aL
        · exact ⟨0, Finset.mem_range.mpr (by omega), by
            rw [hcaL]; apply Fin.ext; simp [Nat.mod_eq_of_lt aL.isLt]⟩
        by_cases hcaL1 : c = aL + 1
        · refine ⟨1, Finset.mem_range.mpr (by omega), ?_⟩
          rw [hcaL1, ← succ_eq]
        exfalso
        have hc_ne_aR : c ≠ aR := haR_eq_aL ▸ hcaL
        have hc_ne_aR1 : c ≠ aR + 1 := haR_eq_aL ▸ hcaL1
        have hc_S : block p c ⊆ S :=
          (interior_block_iff_S' c hcaL hcaL1 hc_ne_aR hc_ne_aR1).mp hc_sub
        have hc_arc : c ∈ arcIdx := (harcIdx c).mpr hc_S
        rw [harcIdx_singleton, Finset.mem_singleton] at hc_arc
        -- c = b. Note aL = b ∨ aL = b + (-1) (i.e. b = aL + 1).
        -- Cases: if aL = b, then c = aL, contradicting hcaL.
        --        if aL = b + (-1), then b = aL + 1, so c = aL + 1, contradicting hcaL1.
        by_cases hbp : b.val % 2 = parityNat odd
        · have haL_b : aL = b := by show (if _ then b else _) = b; simp [hbp]
          exact hcaL (hc_arc ▸ haL_b.symm)
        · have haL_pred : aL = b + (-1 : Fin p.z) := by
            show (if _ then b else _) = b + (-1); simp [hbp]
          have hb_eq_aL1 : b = aL + 1 := by rw [haL_pred]; simp [add_assoc]
          exact hcaL1 (hc_arc ▸ hb_eq_aL1)
      · rintro ⟨i, hi, rfl⟩
        rw [Finset.mem_range] at hi
        interval_cases i
        · -- i = 0: c = aL.
          have : (⟨(aL.val + 0) % p.z, Nat.mod_lt _ p.hz_pos⟩ : Fin p.z) = aL :=
            Fin.ext (by simp [Nat.mod_eq_of_lt aL.isLt])
          rw [this]
          exact fun v hv => haL_sub (Finset.mem_union_left _ hv)
        · -- i = 1: c = aL + 1.
          have : (⟨(aL.val + 1) % p.z, Nat.mod_lt _ p.hz_pos⟩ : Fin p.z) = aL + 1 := succ_eq aL
          rw [this]
          exact fun v hv => haL_sub (Finset.mem_union_right _ hv)
    · -- haL_disj: seam_aL disjoint S'. S' has no blocks: witness (⟨0, _⟩, 0).
      refine build_arc_witness ⟨0, p.hz_pos⟩ 0 (Nat.zero_le _) ?_
      intro c
      refine ⟨?_, ?_⟩
      · intro hc_sub
        by_cases hcaL : c = aL
        · exfalso
          obtain ⟨v, hv⟩ := local_block_ne c
          exact (Finset.disjoint_left.mp haL_disj)
            (Finset.mem_union_left _ (hcaL ▸ hv)) (hc_sub hv)
        by_cases hcaL1 : c = aL + 1
        · exfalso
          obtain ⟨v, hv⟩ := local_block_ne c
          exact (Finset.disjoint_left.mp haL_disj)
            (Finset.mem_union_right _ (hcaL1 ▸ hv)) (hc_sub hv)
        exfalso
        have hc_ne_aR : c ≠ aR := haR_eq_aL ▸ hcaL
        have hc_ne_aR1 : c ≠ aR + 1 := haR_eq_aL ▸ hcaL1
        have hc_S : block p c ⊆ S :=
          (interior_block_iff_S' c hcaL hcaL1 hc_ne_aR hc_ne_aR1).mp hc_sub
        have hc_arc : c ∈ arcIdx := (harcIdx c).mpr hc_S
        rw [harcIdx_singleton, Finset.mem_singleton] at hc_arc
        by_cases hbp : b.val % 2 = parityNat odd
        · have haL_b : aL = b := by show (if _ then b else _) = b; simp [hbp]
          exact hcaL (hc_arc ▸ haL_b.symm)
        · have haL_pred : aL = b + (-1 : Fin p.z) := by
            show (if _ then b else _) = b + (-1); simp [hbp]
          have hb_eq_aL1 : b = aL + 1 := by rw [haL_pred]; simp [add_assoc]
          exact hcaL1 (hc_arc ▸ hb_eq_aL1)
      · rintro ⟨i, hi, _⟩
        simp at hi
  -- Main case: 2 ≤ m < p.z. The 9-case witness table.
  -- For each (b parity, b+m-1 parity, haL status, haR status), exhibit a witness (b', m'):
  -- - act/act/sub/sub  → (b, m+1)         act/act/sub/disj → (b, m-1)
  -- - act/inact/sub/sub → (b, m)          (act/inact/sub/disj is impossible by forcing rule)
  -- - inact/act/sub/sub → (b-1, m+2)      inact/act/sub/disj → (b-1, m)
  -- - inact/act/disj/sub → (b+1, m)       inact/act/disj/disj → (b+1, m-2)
  -- - inact/inact/sub/sub → (b-1, m+1)    inact/inact/disj/sub → (b+1, m-1)
  -- (Forcing rules: b active ⇒ aL = b ⇒ haL = sub. b+m-1 inactive ⇒ aR = b+m-2 ⇒ haR = sub.)
  -- ---------- Phase 1: concrete forms for aL, aR ----------
  have hm_ge2' : 2 ≤ m := hm_ge2
  have parity_eq : parityNat odd = j % 2 := by
    unfold parityNat odd
    rcases Nat.mod_two_eq_zero_or_one j with hj | hj <;> simp [hj]
  -- The "last block" anchor base: bm1 = ⟨(b+m.pred)%p.z,_⟩ = arcVtx (m-1)
  let bm1 : Fin p.z := ⟨(b.val + m.pred) % p.z, Nat.mod_lt _ p.hz_pos⟩
  have bm1_def : bm1 = arcVtx m.pred := rfl
  have hmpred_eq : m.pred = m - 1 := Nat.pred_eq_sub_one
  -- aL/aR are activeAnchor applied to b and bm1 respectively
  have haL_def_eq : aL = activeAnchor p odd b := rfl
  have haR_def_eq : aR = activeAnchor p odd bm1 := rfl
  -- Concrete forms by parity case-split
  have haL_act : b.val % 2 = j % 2 → aL = b := by
    intro hb
    rw [haL_def_eq]; unfold activeAnchor
    rw [parity_eq]; simp [hb]
  have haL_inact : ¬(b.val % 2 = j % 2) → aL = b + (-1 : Fin p.z) := by
    intro hb
    rw [haL_def_eq]; unfold activeAnchor
    rw [parity_eq]; simp [hb]
  have haR_act : bm1.val % 2 = j % 2 → aR = bm1 := by
    intro h
    rw [haR_def_eq]; unfold activeAnchor
    rw [parity_eq]; simp [h]
  have haR_inact : ¬(bm1.val % 2 = j % 2) → aR = bm1 + (-1 : Fin p.z) := by
    intro h
    rw [haR_def_eq]; unfold activeAnchor
    rw [parity_eq]; simp [h]
  -- Easy: when aL = c for some c, also aL + 1 = c + 1 (trivial)
  -- For "aL = b + (-1)": aL + 1 = b
  have haL_inact_succ : ¬(b.val % 2 = j % 2) → aL + 1 = b := by
    intro h; rw [haL_inact h]; simp [add_assoc]
  -- For "aR = bm1 + (-1)": aR + 1 = bm1
  have haR_inact_succ : ¬(bm1.val % 2 = j % 2) → aR + 1 = bm1 := by
    intro h; rw [haR_inact h]; simp [add_assoc]
  -- ---------- Phase 2: forcing-rule helpers ----------
  -- arcVtx i ∈ arcIdx for i < m
  have arcVtx_mem_arcIdx : ∀ i, i < m → arcVtx i ∈ arcIdx := by
    intro i hi
    simp only [arcIdx, Finset.mem_image, Finset.mem_range]
    exact ⟨i, hi, rfl⟩
  -- block (arcVtx i) ⊆ S for i < m
  have arcVtx_sub_S : ∀ i, i < m → block p (arcVtx i) ⊆ S := by
    intro i hi
    exact (harcIdx _).mp (arcVtx_mem_arcIdx i hi)
  -- arcVtx 1 = b + 1 (using succ_eq)
  have arcVtx_one_eq : arcVtx 1 = b + 1 := by
    show (⟨(b.val + 1) % p.z, _⟩ : Fin p.z) = b + 1
    exact succ_eq b
  -- arcVtx m.pred + 1 = arcVtx m (when m ≥ 1, the successor of last is the m-th arcVtx)
  have arcVtx_pred_succ : arcVtx m.pred + 1 = arcVtx m := by
    rw [← succ_eq (arcVtx m.pred)]
    apply Fin.ext
    show ((b.val + m.pred) % p.z + 1) % p.z = (b.val + m) % p.z
    have hm_eq : m.pred + 1 = m := Nat.succ_pred_eq_of_pos hm_pos
    have h1 : (b.val + m.pred) + 1 = b.val + m := by omega
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, h1]
  -- arcVtx (m.pred - 1) + 1 = arcVtx m.pred  (when m ≥ 2)
  have arcVtx_predpred_succ : arcVtx (m.pred - 1) + 1 = arcVtx m.pred := by
    rw [← succ_eq (arcVtx (m.pred - 1))]
    apply Fin.ext
    show ((b.val + (m.pred - 1)) % p.z + 1) % p.z = (b.val + m.pred) % p.z
    have h1 : (b.val + (m.pred - 1)) + 1 = b.val + m.pred := by omega
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, h1]
  -- bm1 = arcVtx m.pred (defeq)
  have bm1_eq_arcVtx : bm1 = arcVtx m.pred := rfl
  -- bm1 ≥ arcVtx 1 when m ≥ 2 (used to show block_b + block_{b+1} ⊆ S in the act case)
  -- Forcing rule 1: b active ⇒ aL = b ⇒ seam(b) ⊆ S' ⇒ haL_cons resolves to sub.
  have force_haL_sub : b.val % 2 = j % 2 →
      block p aL ∪ block p (aL + 1) ⊆ S' := by
    intro hb_par
    have haL_b : aL = b := haL_act hb_par
    -- block p b ⊆ S and block p (b+1) ⊆ S (both in arcIdx since m ≥ 2)
    have hb_sub_S : block p b ⊆ S := by
      have := arcVtx_sub_S 0 (by omega)
      rwa [show arcVtx 0 = b from arcVtx_zero] at this
    have hb1_sub_S : block p (b + 1) ⊆ S := by
      have := arcVtx_sub_S 1 (by omega)
      rwa [arcVtx_one_eq] at this
    have hpair_S : block p b ∪ block p (b + 1) ⊆ S := Finset.union_subset hb_sub_S hb1_sub_S
    have hpair_S' := seam_sub_preserved b hb_par hpair_S
    rw [haL_b]
    -- aL + 1 = b + 1 after rewriting aL = b
    exact hpair_S'
  -- Forcing rule 2: b+m-1 inactive ⇒ aR = b+m-2 ⇒ seam(aR) ⊆ S' ⇒ haR_cons resolves to sub.
  have force_haR_sub : ¬(bm1.val % 2 = j % 2) →
      block p aR ∪ block p (aR + 1) ⊆ S' := by
    intro hbm1_par
    -- aR = bm1 + (-1) = arcVtx (m.pred - 1) in Fin terms
    have haR_eq : aR = bm1 + (-1 : Fin p.z) := haR_inact hbm1_par
    have haR_succ_bm1 : aR + 1 = bm1 := haR_inact_succ hbm1_par
    -- aR is the "block before bm1" in the cyclic ordering. We need aR's parity.
    -- (aR + 1).val % 2 = bm1.val % 2 ≠ j % 2, so aR.val % 2 = j % 2 by parity_flip.
    have haR_par : aR.val % 2 = j % 2 := by
      -- aR + 1 = bm1 so aR has flipped parity
      by_contra hne
      have hflip : (aR + 1).val % 2 = j % 2 := parity_flip aR hne
      rw [haR_succ_bm1] at hflip
      exact hbm1_par hflip
    -- block p (arcVtx (m.pred - 1)) ⊆ S since (m.pred - 1) < m
    have h_pred_pred : m.pred - 1 < m := pred_sub_one_lt_of_pos hm_pos
    have h_pred : m.pred < m := pred_lt_of_pos hm_pos
    -- Identify aR with arcVtx (m.pred - 1) via aR + 1 = arcVtx m.pred (which equals bm1)
    have haR_arcVtx : aR = arcVtx (m.pred - 1) := by
      -- aR + 1 = bm1 = arcVtx m.pred, and arcVtx (m.pred - 1) + 1 = arcVtx m.pred
      -- So aR + 1 = arcVtx (m.pred - 1) + 1, hence aR = arcVtx (m.pred - 1)
      have h1 : aR + 1 = arcVtx (m.pred - 1) + 1 := by
        rw [haR_succ_bm1, bm1_eq_arcVtx, arcVtx_predpred_succ]
      -- add_right_cancel in Fin
      have := h1
      have heq : aR + 1 + (-1 : Fin p.z) = arcVtx (m.pred - 1) + 1 + (-1 : Fin p.z) :=
        congrArg (· + (-1 : Fin p.z)) this
      simpa [add_assoc] using heq
    have h_aR_sub_S : block p aR ⊆ S := by
      rw [haR_arcVtx]; exact arcVtx_sub_S (m.pred - 1) h_pred_pred
    have h_aR1_sub_S : block p (aR + 1) ⊆ S := by
      rw [haR_succ_bm1, bm1_eq_arcVtx]
      exact arcVtx_sub_S m.pred h_pred
    have hpair_S : block p aR ∪ block p (aR + 1) ⊆ S :=
      Finset.union_subset h_aR_sub_S h_aR1_sub_S
    exact seam_sub_preserved aR haR_par hpair_S
  -- Helpers to apply forcing rules to haL_cons / haR_cons
  -- (Given block p aL ∪ block p (aL+1) is nonempty, sub and disj are mutually exclusive.)
  have haL_seam_ne : (block p aL ∪ block p (aL + 1)).Nonempty := by
    obtain ⟨v, hv⟩ := local_block_ne aL
    exact ⟨v, Finset.mem_union_left _ hv⟩
  have haR_seam_ne : (block p aR ∪ block p (aR + 1)).Nonempty := by
    obtain ⟨v, hv⟩ := local_block_ne aR
    exact ⟨v, Finset.mem_union_left _ hv⟩
  -- arcVtx i = arcVtx k for 0 ≤ i,k < p.z iff i = k.
  have arcVtx_inj : ∀ {i k : ℕ}, i < p.z → k < p.z → arcVtx i = arcVtx k → i = k := by
    intro i k hik hkz heq
    have hval : (b.val + i) % p.z = (b.val + k) % p.z := congr_arg Fin.val heq
    have hmod : i ≡ k [MOD p.z] := (Nat.ModEq.refl b.val).add_left_cancel hval
    exact Nat.ModEq.eq_of_lt_of_lt hmod hik hkz
  -- arcVtx (i + 1) = arcVtx i + 1
  have arcVtx_succ : ∀ i, arcVtx (i + 1) = arcVtx i + 1 := by
    intro i
    rw [← succ_eq (arcVtx i)]
    apply Fin.ext
    show (b.val + (i + 1)) % p.z = ((b.val + i) % p.z + 1) % p.z
    have h1 : b.val + (i + 1) = (b.val + i) + 1 := by ring
    rw [h1, Nat.add_mod (b.val + i) 1 p.z, h1_mod]
  -- Disjoint-with-nonempty implies not subset and vice versa.
  -- If seam is sub and disjoint, that's a contradiction.
  have haL_resolve : (block p aL ∪ block p (aL + 1) ⊆ S') ∨
      Disjoint (block p aL ∪ block p (aL + 1) : Finset _) S' := haL_cons
  have haR_resolve : (block p aR ∪ block p (aR + 1) ⊆ S') ∨
      Disjoint (block p aR ∪ block p (aR + 1) : Finset _) S' := haR_cons
  -- ---------- Phase 3: 4-way parity case split and forced specialization ----------
  by_cases hb_par : b.val % 2 = j % 2
  · -- b active: aL = b, force haL sub.
    have haL_b : aL = b := haL_act hb_par
    have haL_sub : block p aL ∪ block p (aL + 1) ⊆ S' := force_haL_sub hb_par
    by_cases hbm1_par : bm1.val % 2 = j % 2
    · -- b active, bm1 active: aR = bm1. haR_cons can be sub or disj.
      have haR_bm1 : aR = bm1 := haR_act hbm1_par
      -- Row 1: sub/sub → (b, m+1)
      -- Row 2: sub/disj → (b, m-1)
      rcases haR_cons with haR_sub | haR_disj
      · -- Row 1: act/act/sub/sub → (b, m+1)
        -- aL = b = arcVtx 0, aL+1 = arcVtx 1; aR = bm1 = arcVtx m.pred, aR+1 = arcVtx m.
        -- Witness: (b, m+1) extending arcIdx by one block on the right (arcVtx m).
        have h_aL_sub_S' : block p aL ⊆ S' :=
          fun v hv => haL_sub (Finset.mem_union_left _ hv)
        have h_aL1_sub_S' : block p (aL + 1) ⊆ S' :=
          fun v hv => haL_sub (Finset.mem_union_right _ hv)
        have h_aR_sub_S' : block p aR ⊆ S' :=
          fun v hv => haR_sub (Finset.mem_union_left _ hv)
        have h_aR1_sub_S' : block p (aR + 1) ⊆ S' :=
          fun v hv => haR_sub (Finset.mem_union_right _ hv)
        refine build_arc_witness b (m + 1) hm_lt ?_
        intro c
        show block p c ⊆ S' ↔ ∃ i ∈ Finset.range (m + 1), c = arcVtx i
        refine ⟨?_, ?_⟩
        · intro hc_sub
          by_cases hcaL : c = aL
          · refine ⟨0, Finset.mem_range.mpr (Nat.succ_pos m), ?_⟩
            rw [hcaL, haL_b, arcVtx_zero]
          by_cases hcaL1 : c = aL + 1
          · refine ⟨1, Finset.mem_range.mpr (by omega), ?_⟩
            rw [hcaL1, haL_b]; exact arcVtx_one_eq.symm
          by_cases hcaR : c = aR
          · refine ⟨m.pred, Finset.mem_range.mpr (by have := Nat.pred_le m; omega), ?_⟩
            rw [hcaR, haR_bm1, bm1_eq_arcVtx]
          by_cases hcaR1 : c = aR + 1
          · refine ⟨m, Finset.mem_range.mpr (by omega), ?_⟩
            rw [hcaR1, haR_bm1, bm1_eq_arcVtx, arcVtx_pred_succ]
          -- Interior
          have hc_S : block p c ⊆ S :=
            (interior_block_iff_S' c hcaL hcaL1 hcaR hcaR1).mp hc_sub
          have hc_arc : c ∈ arcIdx := (harcIdx c).mpr hc_S
          obtain ⟨i, hi, rfl⟩ := (harc_mem_iff c).mp hc_arc
          rw [Finset.mem_range] at hi
          exact ⟨i, Finset.mem_range.mpr (by omega), rfl⟩
        · rintro ⟨i, hi, rfl⟩
          rw [Finset.mem_range] at hi
          by_cases h0 : i = 0
          · subst h0; rw [arcVtx_zero, ← haL_b]; exact h_aL_sub_S'
          by_cases h1 : i = 1
          · subst h1; rw [arcVtx_one_eq, ← haL_b]; exact h_aL1_sub_S'
          by_cases hmpred : i = m.pred
          · subst hmpred; rw [← bm1_eq_arcVtx, ← haR_bm1]; exact h_aR_sub_S'
          by_cases hm_idx : i = m
          · subst hm_idx; rw [← arcVtx_pred_succ, ← bm1_eq_arcVtx, ← haR_bm1]
            exact h_aR1_sub_S'
          -- Interior i: 2 ≤ i ≤ m-2
          have hi_arc : i < m := by
            rcases Nat.lt_or_ge i m with h | h
            · exact h
            · omega
          have hci_arc : arcVtx i ∈ arcIdx := arcVtx_mem_arcIdx i hi_arc
          have hci_S : block p (arcVtx i) ⊆ S := (harcIdx _).mp hci_arc
          have hizpz : i < p.z := Nat.lt_of_lt_of_le hi_arc hm_le
          have hci_L : arcVtx i ≠ aL := by
            rw [haL_b]; intro heq
            have : arcVtx i = arcVtx 0 := by rw [heq, arcVtx_zero]
            exact h0 (arcVtx_inj hizpz p.hz_pos this)
          have hci_L1 : arcVtx i ≠ aL + 1 := by
            rw [haL_b]; intro heq
            have : arcVtx i = arcVtx 1 := by rw [heq, arcVtx_one_eq]
            exact h1 (arcVtx_inj hizpz (by omega) this)
          have hci_R : arcVtx i ≠ aR := by
            rw [haR_bm1, bm1_eq_arcVtx]; intro heq
            have hmpredz : m.pred < p.z := Nat.lt_of_le_of_lt (Nat.pred_le _) hm_lt
            exact hmpred (arcVtx_inj hizpz hmpredz heq)
          have hci_R1 : arcVtx i ≠ aR + 1 := by
            rw [haR_bm1, bm1_eq_arcVtx, arcVtx_pred_succ]; intro heq
            exact hm_idx (arcVtx_inj hizpz hm_lt heq)
          exact (interior_block_iff_S' (arcVtx i) hci_L hci_L1 hci_R hci_R1).mpr hci_S
      · -- Row 2: act/act/sub/disj → (b, m-1)
        -- aL = b, aR = bm1 = arcVtx m.pred. haR_disj: block_aR ∪ block_(aR+1) disj S'.
        -- Witness (b, m-1): arcVtx 0..arcVtx (m-2). Drop arcVtx (m-1) = bm1.
        have h_aL_sub_S' : block p aL ⊆ S' :=
          fun v hv => haL_sub (Finset.mem_union_left _ hv)
        have h_aL1_sub_S' : block p (aL + 1) ⊆ S' :=
          fun v hv => haL_sub (Finset.mem_union_right _ hv)
        have h_aR_ndj_S' : ¬ block p aR ⊆ S' := by
          intro hsub
          obtain ⟨v, hv⟩ := local_block_ne aR
          exact (Finset.disjoint_left.mp haR_disj) (Finset.mem_union_left _ hv) (hsub hv)
        have h_aR1_ndj_S' : ¬ block p (aR + 1) ⊆ S' := by
          intro hsub
          obtain ⟨v, hv⟩ := local_block_ne (aR + 1)
          exact (Finset.disjoint_left.mp haR_disj) (Finset.mem_union_right _ hv) (hsub hv)
        refine build_arc_witness b (m - 1) ((Nat.sub_le m 1).trans hm_lt.le) ?_
        intro c
        show block p c ⊆ S' ↔ ∃ i ∈ Finset.range (m - 1), c = arcVtx i
        refine ⟨?_, ?_⟩
        · intro hc_sub
          by_cases hcaR : c = aR
          · exfalso; apply h_aR_ndj_S'; rw [← hcaR]; exact hc_sub
          by_cases hcaR1 : c = aR + 1
          · exfalso; apply h_aR1_ndj_S'; rw [← hcaR1]; exact hc_sub
          by_cases hcaL : c = aL
          · refine ⟨0, Finset.mem_range.mpr (zero_lt_sub_one_of_two_le hm_ge2'), ?_⟩
            rw [hcaL, haL_b, arcVtx_zero]
          by_cases hcaL1 : c = aL + 1
          · -- c = aL+1 = arcVtx 1. Need 1 ∈ range (m-1), i.e., m ≥ 3. If m=2, then aL+1 = aR (contradiction with hcaR).
            refine ⟨1, Finset.mem_range.mpr ?_, ?_⟩
            · -- Need 1 < m - 1, i.e., m ≥ 3. Suppose m = 2. Then m.pred = 1, so aR = arcVtx 1 = b + 1 = aL+1.
              by_contra hge
              push Not at hge
              have hm2 : m = 2 := eq_two_of_le_and_sub_le hm_ge2' hge
              -- aL+1 = arcVtx 1 and aR = bm1 = arcVtx m.pred = arcVtx 1 = aL+1
              have hmpred1 : m.pred = 1 := by rw [hm2]; rfl
              have : aR = aL + 1 := by
                rw [haR_bm1, bm1_eq_arcVtx, hmpred1, haL_b]
                exact arcVtx_one_eq
              exact hcaR (hcaL1.trans this.symm)
            · rw [hcaL1, haL_b]; exact arcVtx_one_eq.symm
          -- Interior
          have hc_S : block p c ⊆ S :=
            (interior_block_iff_S' c hcaL hcaL1 hcaR hcaR1).mp hc_sub
          have hc_arc : c ∈ arcIdx := (harcIdx c).mpr hc_S
          obtain ⟨i, hi, rfl⟩ := (harc_mem_iff c).mp hc_arc
          rw [Finset.mem_range] at hi
          -- Need i ≠ m.pred. If i = m.pred, then arcVtx i = bm1 = aR, contradicting hcaR.
          have hi_ne_pred : i ≠ m.pred := by
            intro h_eq
            apply hcaR
            -- arcVtx i = arcVtx m.pred = bm1 = aR
            show arcVtx i = aR
            rw [h_eq, ← bm1_eq_arcVtx, ← haR_bm1]
          refine ⟨i, Finset.mem_range.mpr ?_, rfl⟩
          -- i < m and i ≠ m.pred = m - 1, so i ≤ m - 2 < m - 1.
          have hmp : m.pred = m - 1 := Nat.pred_eq_sub_one
          rw [hmp] at hi_ne_pred
          -- Now: hi : i < m, hi_ne_pred : i ≠ m - 1. Need: i < m - 1.
          have : i ≤ m - 1 := Nat.le_pred_of_lt hi
          have : i < m - 1 ∨ i = m - 1 := lt_or_eq_of_le this
          rcases this with h | h
          · exact h
          · exact absurd h hi_ne_pred
        · rintro ⟨i, hi, rfl⟩
          rw [Finset.mem_range] at hi
          have hi_arc : i < m := by have := Nat.pred_le m; omega
          by_cases h0 : i = 0
          · subst h0; rw [arcVtx_zero, ← haL_b]; exact h_aL_sub_S'
          by_cases h1 : i = 1
          · subst h1; rw [arcVtx_one_eq, ← haL_b]; exact h_aL1_sub_S'
          -- Interior i: 2 ≤ i ≤ m-2, so arcVtx i ≠ aR (since i ≠ m-1) and ≠ aR+1.
          have hi_lt_pred : i < m.pred := by
            have hmp : m.pred = m - 1 := Nat.pred_eq_sub_one
            omega
          have hci_arc : arcVtx i ∈ arcIdx := arcVtx_mem_arcIdx i hi_arc
          have hci_S : block p (arcVtx i) ⊆ S := (harcIdx _).mp hci_arc
          have hizpz : i < p.z := Nat.lt_of_lt_of_le hi_arc hm_le
          have hci_L : arcVtx i ≠ aL := by
            rw [haL_b]; intro heq
            have : arcVtx i = arcVtx 0 := by rw [heq, arcVtx_zero]
            exact h0 (arcVtx_inj hizpz p.hz_pos this)
          have hci_L1 : arcVtx i ≠ aL + 1 := by
            rw [haL_b]; intro heq
            have : arcVtx i = arcVtx 1 := by rw [heq, arcVtx_one_eq]
            exact h1 (arcVtx_inj hizpz (by omega) this)
          have hci_R : arcVtx i ≠ aR := by
            rw [haR_bm1, bm1_eq_arcVtx]; intro heq
            have hmpredz : m.pred < p.z := Nat.lt_of_le_of_lt (Nat.pred_le _) hm_lt
            have : i = m.pred := arcVtx_inj hizpz hmpredz heq
            omega
          have hci_R1 : arcVtx i ≠ aR + 1 := by
            rw [haR_bm1, bm1_eq_arcVtx, arcVtx_pred_succ]; intro heq
            have : i = m := arcVtx_inj hizpz hm_lt heq
            omega
          exact (interior_block_iff_S' (arcVtx i) hci_L hci_L1 hci_R hci_R1).mpr hci_S
    · -- b active, bm1 inactive: aR = bm1 + (-1). Force haR sub.
      have haR_pred : aR = bm1 + (-1 : Fin p.z) := haR_inact hbm1_par
      have haR_succ : aR + 1 = bm1 := haR_inact_succ hbm1_par
      have haR_sub : block p aR ∪ block p (aR + 1) ⊆ S' := force_haR_sub hbm1_par
      -- Row 3: act/inact/sub/sub → (b, m)
      -- aL = b, aL+1 = b+1, aR = arcVtx (m-2), aR+1 = bm1 = arcVtx (m-1)
      -- Witness: (b, m). New arc = arcIdx exactly.
      have haR_arcVtx : aR = arcVtx (m.pred - 1) := by
        -- Same proof as in force_haR_sub
        have h1 : aR + 1 = arcVtx (m.pred - 1) + 1 := by
          rw [haR_succ, bm1_eq_arcVtx, arcVtx_predpred_succ]
        have heq : aR + 1 + (-1 : Fin p.z) = arcVtx (m.pred - 1) + 1 + (-1 : Fin p.z) :=
          congrArg (· + (-1 : Fin p.z)) h1
        simpa [add_assoc] using heq
      -- block_aR ⊆ S' (left half of haR_sub) and block_(aR+1) ⊆ S' (right half)
      have h_aR_sub_S' : block p aR ⊆ S' :=
        fun v hv => haR_sub (Finset.mem_union_left _ hv)
      have h_aR1_sub_S' : block p (aR + 1) ⊆ S' :=
        fun v hv => haR_sub (Finset.mem_union_right _ hv)
      have h_aL_sub_S' : block p aL ⊆ S' :=
        fun v hv => haL_sub (Finset.mem_union_left _ hv)
      have h_aL1_sub_S' : block p (aL + 1) ⊆ S' :=
        fun v hv => haL_sub (Finset.mem_union_right _ hv)
      refine build_arc_witness b m hm_le ?_
      intro c
      refine ⟨?_, ?_⟩
      · -- Forward: block p c ⊆ S' → ∃ i ∈ range m, c = arcVtx i
        intro hc_sub
        by_cases hcaL : c = aL
        · -- c = aL = b = arcVtx 0
          refine ⟨0, Finset.mem_range.mpr hm_pos, ?_⟩
          rw [hcaL, haL_b]; exact hb_idx0.symm
        by_cases hcaL1 : c = aL + 1
        · -- c = aL + 1 = b + 1 = arcVtx 1
          refine ⟨1, Finset.mem_range.mpr hm_ge2, ?_⟩
          rw [hcaL1, haL_b]; exact (succ_eq b).symm
        by_cases hcaR : c = aR
        · -- c = aR = arcVtx (m-2) = arcVtx (m.pred - 1)
          refine ⟨m.pred - 1, Finset.mem_range.mpr ?_, ?_⟩
          · have hmp : m.pred = m - 1 := Nat.pred_eq_sub_one
            calc m.pred - 1 ≤ m.pred := Nat.sub_le _ _
              _ < m := Nat.pred_lt (Nat.pos_iff_ne_zero.mp hm_pos)
          · rw [hcaR, haR_arcVtx]
        by_cases hcaR1 : c = aR + 1
        · -- c = aR + 1 = bm1 = arcVtx (m-1) = arcVtx m.pred
          refine ⟨m.pred, Finset.mem_range.mpr (Nat.pred_lt (Nat.pos_iff_ne_zero.mp hm_pos)), ?_⟩
          rw [hcaR1, haR_succ]
        -- Interior: use interior_block_iff_S'
        have hc_S : block p c ⊆ S :=
          (interior_block_iff_S' c hcaL hcaL1 hcaR hcaR1).mp hc_sub
        have hc_arc : c ∈ arcIdx := (harcIdx c).mpr hc_S
        exact (harc_mem_iff c).mp hc_arc
      · -- Reverse: ∃ i ∈ range m, c = arcVtx i → block p c ⊆ S'
        rintro ⟨i, hi, rfl⟩
        rw [Finset.mem_range] at hi
        -- arcVtx i: case-split on whether it hits a boundary anchor.
        have harcVtx_def : (⟨(b.val + i) % p.z, Nat.mod_lt _ p.hz_pos⟩ : Fin p.z) = arcVtx i := rfl
        rw [harcVtx_def]
        by_cases h0 : i = 0
        · subst h0
          rw [arcVtx_zero, ← haL_b]; exact h_aL_sub_S'
        by_cases h1 : i = 1
        · subst h1
          rw [arcVtx_one_eq, ← haL_b]
          exact h_aL1_sub_S'
        by_cases hmpred : i = m.pred
        · subst hmpred
          rw [← bm1_eq_arcVtx, ← haR_succ]
          exact h_aR1_sub_S'
        by_cases hmpredm1 : i = m.pred - 1
        · subst hmpredm1
          rw [← haR_arcVtx]
          exact h_aR_sub_S'
        -- Interior i: 2 ≤ i ≤ m-3
        have harcVtx_i_arc : arcVtx i ∈ arcIdx := arcVtx_mem_arcIdx i hi
        have hc_S : block p (arcVtx i) ⊆ S := (harcIdx _).mp harcVtx_i_arc
        have hiz : i < p.z := lt_of_lt_of_le hi hm_le
        -- Show arcVtx i ≠ aL, aL+1, aR, aR+1.
        have hne_aL : arcVtx i ≠ aL := by
          rw [haL_b]; intro heq
          have h_arc : arcVtx i = arcVtx 0 := by rw [heq, arcVtx_zero]
          exact h0 (arcVtx_inj hiz p.hz_pos h_arc)
        have hne_aL1 : arcVtx i ≠ aL + 1 := by
          rw [haL_b]; intro heq
          have h_arc : arcVtx i = arcVtx 1 := by rw [heq, arcVtx_one_eq]
          exact h1 (arcVtx_inj hiz (Nat.lt_of_lt_of_le Nat.one_lt_two hpz_two_le) h_arc)
        have hne_aR : arcVtx i ≠ aR := by
          rw [haR_arcVtx]; intro heq
          have hmpredm1z : m.pred - 1 < p.z :=
            Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_of_le_of_lt (Nat.pred_le _) hm_lt)
          exact hmpredm1 (arcVtx_inj hiz hmpredm1z heq)
        have hne_aR1 : arcVtx i ≠ aR + 1 := by
          rw [haR_succ, bm1_eq_arcVtx]; intro heq
          have hmpredz : m.pred < p.z := Nat.lt_of_le_of_lt (Nat.pred_le _) hm_lt
          exact hmpred (arcVtx_inj hiz hmpredz heq)
        exact (interior_block_iff_S' (arcVtx i) hne_aL hne_aL1 hne_aR hne_aR1).mpr hc_S
  · -- b inactive: aL = b + (-1). haL_cons can be sub or disj.
    have haL_pred : aL = b + (-1 : Fin p.z) := haL_inact hb_par
    have haL_succ : aL + 1 = b := haL_inact_succ hb_par
    by_cases hbm1_par : bm1.val % 2 = j % 2
    · -- b inactive, bm1 active: aR = bm1. 4 subcases.
      have haR_bm1 : aR = bm1 := haR_act hbm1_par
      rcases haL_cons with haL_sub | haL_disj
      · rcases haR_cons with haR_sub | haR_disj
        · -- Row 4: inact/act/sub/sub → (b-1, m+2)
          have arcVtx_def : ∀ i, arcVtx i = ⟨(b.val + i) % p.z, Nat.mod_lt _ p.hz_pos⟩ :=
            fun _ => rfl
          exact row4_witness b aL aR bm1 m hm_ge2 hm_lt arcVtx arcVtx_def arcVtx_inj
            arcVtx_succ arcVtx_zero arcVtx_pred_succ arcIdx arcVtx_mem_arcIdx harcIdx
            harc_mem_iff succ_eq block_dichotomy_S' interior_block_iff_S' build_arc_witness
            haL_succ haR_bm1 bm1_eq_arcVtx haL_sub haR_sub
        · -- Row 5: inact/act/sub/disj → (b-1, m)
          exact row5_witness b aL aR bm1 m hm_ge2 hm_lt arcVtx arcVtx_inj arcVtx_succ
            arcVtx_zero arcVtx_pred_succ arcIdx arcVtx_mem_arcIdx harcIdx harc_mem_iff
            succ_eq interior_block_iff_S' build_arc_witness haL_succ haR_bm1
            bm1_eq_arcVtx haL_sub haR_disj
      · rcases haR_cons with haR_sub | haR_disj
        · -- Row 6: inact/act/disj/sub → (b+1, m)
          have arcVtx_def : ∀ i, arcVtx i = ⟨(b.val + i) % p.z, Nat.mod_lt _ p.hz_pos⟩ :=
            fun _ => rfl
          exact row6_witness b aL aR bm1 m hm_ge2 hm_lt arcVtx arcVtx_def arcVtx_inj
            arcVtx_succ arcVtx_zero arcVtx_pred_succ arcIdx arcVtx_mem_arcIdx harcIdx
            harc_mem_iff interior_block_iff_S' build_arc_witness haL_succ haR_bm1
            bm1_eq_arcVtx haL_disj haR_sub
        · -- Row 7: inact/act/disj/disj → (b+1, m-2)
          have arcVtx_def : ∀ i, arcVtx i = ⟨(b.val + i) % p.z, Nat.mod_lt _ p.hz_pos⟩ :=
            fun _ => rfl
          exact row7_witness b aL aR bm1 m hm_ge2 hm_lt arcVtx arcVtx_def arcVtx_inj
            arcVtx_succ arcVtx_zero arcVtx_pred_succ arcIdx arcVtx_mem_arcIdx harcIdx
            harc_mem_iff interior_block_iff_S' build_arc_witness haL_succ haR_bm1
            bm1_eq_arcVtx haL_disj haR_disj
    · -- b inactive, bm1 inactive: aR = bm1 + (-1). Force haR sub.
      have haR_pred : aR = bm1 + (-1 : Fin p.z) := haR_inact hbm1_par
      have haR_succ : aR + 1 = bm1 := haR_inact_succ hbm1_par
      have haR_sub : block p aR ∪ block p (aR + 1) ⊆ S' := force_haR_sub hbm1_par
      rcases haL_cons with haL_sub | haL_disj
      · -- Row 8: inact/inact/sub/sub → (b-1, m+1)
        exact row8_witness b aL aR bm1 m hm_ge2 hm_lt arcVtx arcVtx_inj arcVtx_succ
          arcVtx_zero arcVtx_predpred_succ arcIdx arcVtx_mem_arcIdx harcIdx harc_mem_iff
          succ_eq interior_block_iff_S' build_arc_witness haL_succ haR_succ bm1_eq_arcVtx
          haL_sub haR_sub
      · -- Row 9: inact/inact/disj/sub → (b+1, m-1)
        have arcVtx_def : ∀ i, arcVtx i = ⟨(b.val + i) % p.z, Nat.mod_lt _ p.hz_pos⟩ :=
          fun _ => rfl
        exact row9_witness b aL aR bm1 m hm_ge2 hm_lt arcVtx arcVtx_def arcVtx_inj
          arcVtx_succ arcVtx_zero arcVtx_predpred_succ arcIdx
          arcVtx_mem_arcIdx harcIdx harc_mem_iff interior_block_iff_S'
          build_arc_witness haL_succ haR_succ bm1_eq_arcVtx haL_disj haR_sub

/-- Structural lemma: for a contiguous arc `S` and interval `j`, there exist two seam
K_{2k}-clique anchors `aL` and `aR` (both of parity `j % 2`, possibly equal) such that for
every one-interval reachable state `S'` (i.e., `opinionProcess₂ S S' ≠ 0`):
1. The blockCount changes by at most 2.
2. If `S'` breaks the arc invariant, then seam `aL` or seam `aR` is mixed in `S'`.
These are the (at most two) boundary seam cliques of `S` with parity `j % 2`. -/
private theorem contiguousArc_step_structure (p : Params) (j : ℕ)
    (S : Finset (VertexSet p)) (hS : IsContiguousArc p S) :
    ∃ (aL aR : Fin p.z), aL.val % 2 = j % 2 ∧ aR.val % 2 = j % 2 ∧
      ∀ S' : Finset (VertexSet p),
          VoterModel.opinionProcess₂ (lowerBoundGraph p) (j * p.T) p.T S S' ≠ 0 →
          |(((Finset.univ.filter (block p · ⊆ S')).card : ℤ) -
            ((Finset.univ.filter (block p · ⊆ S)).card : ℤ))| ≤ 2 ∧
          (¬IsContiguousArc p S' →
            ¬(block p aL ∪ block p (aL + 1) ⊆ S' ∨
              Disjoint (block p aL ∪ block p (aL + 1) : Finset _) S') ∨
            ¬(block p aR ∪ block p (aR + 1) ⊆ S' ∨
              Disjoint (block p aR ∪ block p (aR + 1) : Finset _) S')) := by
  set b : Fin p.z := hS.choose with hb_def
  set m : ℕ := hS.choose_spec.choose with hm_def
  -- Parity boolean for interval j: active seam cliques have anchor parity j % 2
  set odd : Bool := decide (j % 2 = 1) with hodd_def
  -- Left boundary anchor: K_{2k} clique containing block b (leftmost block of S)
  set aL : Fin p.z := activeAnchor p odd b with haL_def
  -- Right boundary anchor: K_{2k} clique containing block (b + m - 1) % z (rightmost block)
  -- Use m.pred to avoid ℕ underflow at m = 0; when m = 0, S = ∅ (absorbing), so
  -- the conclusion is vacuous regardless of which anchor we pick.
  set aR : Fin p.z := activeAnchor p odd ⟨(b.val + m.pred) % p.z, Nat.mod_lt _ p.hz_pos⟩
    with haR_def
  -- Parity conditions: `activeAnchor_parity_jmod2` (public, Defs.lean).
  have haL_par : aL.val % 2 = j % 2 := activeAnchor_parity_jmod2 p j b
  have haR_par : aR.val % 2 = j % 2 :=
    activeAnchor_parity_jmod2 p j ⟨(b.val + m.pred) % p.z, Nat.mod_lt _ p.hz_pos⟩
  refine ⟨aL, aR, haL_par, haR_par, ?_⟩
  intro S' hop
  refine ⟨?_, ?_⟩
  · -- |blockCount(S') - blockCount(S)| ≤ 2: only the ≤ 2 boundary seam K_{2k}-cliques
    -- aL and aR (parity j % 2) interact with the arc boundary; interior cliques start
    -- at consensus and are preserved.
    exact contiguousArc_blockCount_diff_le_two p j S S' hS hop
  · -- Arc breakage → boundary seam mixed: if S' is not a contiguous arc, the breakage
    -- must occur at one of the boundary seams aL or aR.
    intro hS'_break
    have := contiguousArc_break_seam_mixed p j S S' hS hop hS'_break
    -- The helper's let-bindings unfold to our `aL` / `aR`.
    simpa [haL_def, haR_def, hodd_def, hb_def, hm_def] using this

/-- The first-failure event {arc ok at all i < j} ∩ {arc fails at j} is covered by two sets
F₁ and F₂, each with measure ≤ (1/2)^α.

When the arc holds at step (j−1)·T but breaks at j·T, the two seam K_{2k}-cliques at the
arc boundaries are the only active cliques (parity `a.val % 2 = (j−1) % 2`). Each seam
clique fails to absorb with conditional probability ≤ (1/2)^α via `perInterval_prob_lower`
and the voter model Markov property. This lemma packages the event containment and the two
per-clique probability bounds. -/
private theorem arc_fail_has_two_seam_events (Γ : ℕ) (p : Params)
    (α : ℕ) (hα : 1 ≤ α)
    (hαT : Γ * α * p.k ≤ p.T)
    (hstep : ∀ (t : ℕ) (T : Finset (CliqueVertex p.k)),
        (1 / 2 : ENNReal) ≤
          VoterModel.opinionProcess₂ (staticCliqueGraph p.k) t (Γ * p.k) T Finset.univ +
          VoterModel.opinionProcess₂ (staticCliqueGraph p.k) t (Γ * p.k) T ∅)
    {Ω : Type} [MeasurableSpace Ω]
    (vm : TemporalGraph.VoterModelAbstract (lowerBoundGraph p) 2 Ω)
    (j : ℕ) (hj : 1 ≤ j) :
    ∃ (F₁ F₂ : Set Ω),
      ({ω | ∀ i < j, IsContiguousArc p (vm.opinionZeroSet (i * p.T) ω)} ∩
       {ω | ¬IsContiguousArc p (vm.opinionZeroSet (j * p.T) ω)}) ⊆ F₁ ∪ F₂ ∧
      ((vm.μ : Measure _) F₁).toReal ≤ (1 / 2 : ℝ) ^ α ∧
      ((vm.μ : Measure _) F₂).toReal ≤ (1 / 2 : ℝ) ^ α := by
  classical
  -- Choose seam anchors aL, aR for each arc S using contiguousArc_step_structure.
  -- We use j' = j - 1 as the interval index.
  set jm1 : ℕ := j - 1 with hjm1_def
  have hjm1_succ : jm1 + 1 = j := by rw [hjm1_def]; omega
  have hidx : jm1 * p.T + p.T = j * p.T := by
    have : jm1 + 1 = j := hjm1_succ
    calc jm1 * p.T + p.T = (jm1 + 1) * p.T := by ring
      _ = j * p.T := by rw [this]
  -- Helper: extract aL, aR per arc using Classical.choose (existence is given by
  -- contiguousArc_step_structure).
  let aL : (S : Finset (VertexSet p)) → IsContiguousArc p S → Fin p.z :=
    fun S hS => (contiguousArc_step_structure p jm1 S hS).choose
  let aR : (S : Finset (VertexSet p)) → IsContiguousArc p S → Fin p.z :=
    fun S hS => (contiguousArc_step_structure p jm1 S hS).choose_spec.choose
  -- Properties of aL, aR.
  have aL_prop : ∀ (S : Finset (VertexSet p)) (hS : IsContiguousArc p S),
      (aL S hS).val % 2 = jm1 % 2 ∧
      ∀ S' : Finset (VertexSet p),
          VoterModel.opinionProcess₂ (lowerBoundGraph p) (jm1 * p.T) p.T S S' ≠ 0 →
          |(((Finset.univ.filter (block p · ⊆ S')).card : ℤ) -
            ((Finset.univ.filter (block p · ⊆ S)).card : ℤ))| ≤ 2 ∧
          (¬IsContiguousArc p S' →
            ¬(block p (aL S hS) ∪ block p (aL S hS + 1) ⊆ S' ∨
              Disjoint (block p (aL S hS) ∪ block p (aL S hS + 1) : Finset _) S') ∨
            ¬(block p (aR S hS) ∪ block p (aR S hS + 1) ⊆ S' ∨
              Disjoint (block p (aR S hS) ∪ block p (aR S hS + 1) : Finset _) S')) := by
    intro S hS
    have hcs := (contiguousArc_step_structure p jm1 S hS).choose_spec.choose_spec
    refine ⟨hcs.1, ?_⟩
    intro S' hop
    exact hcs.2.2 S' hop
  have aR_prop : ∀ (S : Finset (VertexSet p)) (hS : IsContiguousArc p S),
      (aR S hS).val % 2 = jm1 % 2 := by
    intro S hS
    exact (contiguousArc_step_structure p jm1 S hS).choose_spec.choose_spec.2.1
  -- Define F₂_main(S, hS) and F₁_main(S, hS): seam not absorbed events.
  let F₂_main : (S : Finset (VertexSet p)) → IsContiguousArc p S → Set Ω :=
    fun S hS =>
      {ω | vm.opinionZeroSet (jm1 * p.T) ω = S} ∩
      {ω | ¬(block p (aR S hS) ∪ block p (aR S hS + 1) ⊆ vm.opinionZeroSet (j * p.T) ω ∨
            Disjoint (block p (aR S hS) ∪ block p (aR S hS + 1) : Finset _)
              (vm.opinionZeroSet (j * p.T) ω))}
  let F₁_main : (S : Finset (VertexSet p)) → IsContiguousArc p S → Set Ω :=
    fun S hS =>
      {ω | vm.opinionZeroSet (jm1 * p.T) ω = S} ∩
      {ω | ¬(block p (aL S hS) ∪ block p (aL S hS + 1) ⊆ vm.opinionZeroSet (j * p.T) ω ∨
            Disjoint (block p (aL S hS) ∪ block p (aL S hS + 1) : Finset _)
              (vm.opinionZeroSet (j * p.T) ω))}
  -- Failure event.
  set FE : Set Ω :=
    {ω | ∀ i < j, IsContiguousArc p (vm.opinionZeroSet (i * p.T) ω)} ∩
    {ω | ¬IsContiguousArc p (vm.opinionZeroSet (j * p.T) ω)} with hFE_def
  -- F₂ := union of F₂_main over arcs S.
  set F₂ : Set Ω := ⋃ (S : Finset (VertexSet p)) (hS : IsContiguousArc p S), F₂_main S hS
    with hF₂_def
  -- F₁ := FE \ F₂. Then F₁ ∪ F₂ ⊇ FE trivially.
  set F₁ : Set Ω := FE \ F₂ with hF₁_def
  refine ⟨F₁, F₂, ?_, ?_, ?_⟩
  · -- Cover: FE ⊆ F₁ ∪ F₂.
    intro ω hω
    by_cases hω₂ : ω ∈ F₂
    · exact Or.inr hω₂
    · exact Or.inl ⟨hω, hω₂⟩
  · -- μ(F₁) ≤ (1/2)^α.
    -- F₁ ⊆ F₁_main_union ∪ NullPocket.
    -- F₁_main_union := ⋃ S arc, F₁_main(S, hS).
    -- NullPocket := FE ∩ ⋃ S arc, S' not arc, opp(S, S') = 0, {A=S, A'=S'} -- has measure 0.
    set F₁_main_union : Set Ω := ⋃ (S : Finset (VertexSet p)) (hS : IsContiguousArc p S),
        F₁_main S hS with hF₁_main_union_def
    -- NullPart := union over (S arc, S' not arc, opp = 0) of {A=S, A'=S'}.
    set NullPocket : Set Ω :=
      ⋃ (S : Finset (VertexSet p)) (_ : IsContiguousArc p S)
          (S' : Finset (VertexSet p)) (_ : ¬IsContiguousArc p S')
          (_ : VoterModel.opinionProcess₂ (lowerBoundGraph p) (jm1 * p.T) p.T S S' = 0),
        {ω | vm.opinionZeroSet (jm1 * p.T) ω = S} ∩ {ω | vm.opinionZeroSet (j * p.T) ω = S'} with hNullPocket_def
    have hF₁_sub : F₁ ⊆ F₁_main_union ∪ NullPocket := by
      intro ω hω
      obtain ⟨hω_FE, hω_notF₂⟩ := hω
      -- ω is in failure event and not in F₂.
      simp only [hFE_def, Set.mem_inter_iff, Set.mem_setOf_eq] at hω_FE
      obtain ⟨h_arc_all, h_not_arc_j⟩ := hω_FE
      -- S = A(jm1*T) ω is an arc (jm1 < j).
      have hjm1_lt_j : jm1 < j := by rw [hjm1_def]; omega
      have hS_arc : IsContiguousArc p (vm.opinionZeroSet (jm1 * p.T) ω) := h_arc_all jm1 hjm1_lt_j
      set S := vm.opinionZeroSet (jm1 * p.T) ω with hS_def
      set S' := vm.opinionZeroSet (j * p.T) ω with hS'_def
      have hS'_notarc : ¬IsContiguousArc p S' := h_not_arc_j
      -- ω ∉ F₂ means: ω ∉ F₂_main(S, hS_arc), i.e., seam aR(S) is absorbed in S'.
      have hω_notF₂_main : ω ∉ F₂_main S hS_arc := by
        intro h
        apply hω_notF₂
        exact Set.mem_iUnion₂.mpr ⟨S, hS_arc, h⟩
      have hseam_aR : block p (aR S hS_arc) ∪ block p (aR S hS_arc + 1) ⊆ S' ∨
          Disjoint (block p (aR S hS_arc) ∪ block p (aR S hS_arc + 1) : Finset _) S' := by
        by_contra hbad
        apply hω_notF₂_main
        exact ⟨rfl, hbad⟩
      -- Now: case on whether opinionProcess₂(jm1*T, T, S, S') = 0 or not.
      by_cases hop : VoterModel.opinionProcess₂ (lowerBoundGraph p) (jm1 * p.T) p.T S S' = 0
      · -- ω ∈ NullPocket.
        right
        refine Set.mem_iUnion₂.mpr ⟨S, hS_arc, ?_⟩
        refine Set.mem_iUnion₂.mpr ⟨S', hS'_notarc, ?_⟩
        refine Set.mem_iUnion.mpr ⟨hop, ?_⟩
        exact ⟨rfl, rfl⟩
      · -- opp ≠ 0, apply hreach: seam aL or seam aR fails.
        have hreach_S' := (aL_prop S hS_arc).2 S' hop
        rcases hreach_S'.2 hS'_notarc with h_aL_fail | h_aR_fail
        · -- aL fails. ω ∈ F₁_main(S, hS_arc).
          left
          exact Set.mem_iUnion₂.mpr ⟨S, hS_arc, ⟨rfl, h_aL_fail⟩⟩
        · -- aR fails. But hseam_aR says aR is absorbed. Contradiction.
          exact absurd hseam_aR h_aR_fail
    -- μ(F₁_main_union) ≤ (1/2)^α and μ(NullPocket) = 0.
    -- Step 1: μ(NullPocket) = 0.
    have h_nullPocket_zero : (vm.μ : Measure _) NullPocket = 0 := by
      rw [hNullPocket_def]
      rw [measure_iUnion_null_iff]
      intro S
      rw [measure_iUnion_null_iff]
      intro _hS
      rw [measure_iUnion_null_iff]
      intro S'
      rw [measure_iUnion_null_iff]
      intro _hS'
      rw [measure_iUnion_null_iff]
      intro hop
      have hMk := vm.A_markovMarginal (jm1 * p.T) p.T S S'
      rw [hidx] at hMk
      rw [hMk, hop, mul_zero]
    -- Step 2: μ(F₁_main_union) ≤ (1/2)^α.
    -- F₁_main_union ⊆ ⋃_S {A=S} ∩ {seam aL(S) NOT absorbed}.
    -- Each fiber has measure ≤ μ{A=S} * (1/2)^α via complement of perInterval_prob_lower.
    have h_F₁_main_bound : ((vm.μ : Measure _) F₁_main_union).toReal ≤ (1 / 2 : ℝ) ^ α := by
      classical
      -- arcs : Finset of contiguous arcs.
      set arcs : Finset (Finset (VertexSet p)) :=
        Finset.univ.filter (IsContiguousArc p) with harcs_def
      -- F₁_main_union as a finite union over arcs S.
      have hUnion_finset :
          F₁_main_union = ⋃ S ∈ arcs, ⋃ (hS : IsContiguousArc p S), F₁_main S hS := by
        ext ω
        simp only [F₁_main_union, arcs, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ,
                   true_and]
        constructor
        · rintro ⟨S, hS, hω⟩; exact ⟨S, hS, hS, hω⟩
        · rintro ⟨S, hS, hS', hω⟩; exact ⟨S, hS', hω⟩
      -- Bound: μ(F₁_main_union) ≤ Σ_{S ∈ arcs} μ(F₁_main S hS).
      have h_meas_le : (vm.μ : Measure _) F₁_main_union ≤
          ∑ S ∈ arcs, (vm.μ : Measure _) (⋃ (hS : IsContiguousArc p S), F₁_main S hS) := by
        rw [hUnion_finset]
        exact measure_biUnion_finset_le _ _
      -- For each arc S, with hS : IsContiguousArc p S:
      -- μ(F₁_main S hS) ≤ μ{A=S} * (1/2)^α.
      -- The "absorbed" event for seam aL has measure ≥ μ{A=S} * (1 - (1/2)^α).
      -- Use perInterval_prob_lower with anchor aL.
      have h_arc_bound : ∀ S ∈ arcs,
          (vm.μ : Measure _) (⋃ (hS : IsContiguousArc p S), F₁_main S hS) ≤
            ENNReal.ofReal ((1 / 2 : ℝ) ^ α) * (vm.μ : Measure _) {ω | vm.opinionZeroSet (jm1 * p.T) ω = S} := by
        intro S hS_mem
        have hS : IsContiguousArc p S := (Finset.mem_filter.mp hS_mem).2
        -- Single fiber.
        have hUnion_single :
            (⋃ (hS' : IsContiguousArc p S), F₁_main S hS') = F₁_main S hS := by
          ext ω; simp only [Set.mem_iUnion]; exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hS, h⟩⟩
        rw [hUnion_single]
        -- F₁_main S hS = {A=S} ∩ {seam aL not absorbed}.
        have haL_par : (aL S hS).val % 2 = jm1 % 2 := (aL_prop S hS).1
        -- The "absorbed" event = ⋃_{S' ∈ consF} {A(j * p.T) = S'}.
        set consF : Finset (Finset (VertexSet p)) :=
          Finset.univ.filter (fun S' : Finset (VertexSet p) =>
            block p (aL S hS) ∪ block p (aL S hS + 1) ⊆ S' ∨
            Disjoint (block p (aL S hS) ∪ block p (aL S hS + 1)) S') with hconsF_def
        set Absorbed : Set Ω :=
          {ω | block p (aL S hS) ∪ block p (aL S hS + 1) ⊆ vm.opinionZeroSet (j * p.T) ω ∨
              Disjoint (block p (aL S hS) ∪ block p (aL S hS + 1)) (vm.opinionZeroSet (j * p.T) ω)}
          with hAbsorbed_def
        have hAbsorbed_eq :
            Absorbed = ⋃ S' ∈ consF, {ω : Ω | vm.opinionZeroSet (j * p.T) ω = S'} := by
          ext ω
          simp only [Absorbed, consF, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ,
                     true_and, Set.mem_setOf_eq, exists_prop]
          constructor
          · intro h; exact ⟨vm.opinionZeroSet (j * p.T) ω, h, rfl⟩
          · rintro ⟨S', h1, h2⟩; rw [h2]; exact h1
        -- Inclusion-style: F₁_main S hS ⊆ {A=S} \ ({A=S} ∩ Absorbed).
        -- Actually: F₁_main S hS = {A=S} ∩ Absorbedᶜ.
        have hF₁_eq : F₁_main S hS = {ω | vm.opinionZeroSet (jm1 * p.T) ω = S} ∩ Absorbedᶜ := by
          rfl
        rw [hF₁_eq]
        -- μ({A=S} ∩ Absᶜ) = μ{A=S} - μ({A=S} ∩ Abs)
        -- Use measure_diff_le_iff or rewrite to inter complement.
        -- Plan: μ({A=S} ∩ Absᶜ) + μ({A=S} ∩ Abs) = μ{A=S}.
        -- By markovMarginal chained: μ({A=S} ∩ Abs) = μ{A=S} * (∑_{S' ∈ consF} opinionProcess₂ S S').
        -- ∑ ≥ ofReal(1 - (1/2)^α) (perInterval_prob_lower).
        have markovMarginal_sum :
            (vm.μ : Measure _) ({ω | vm.opinionZeroSet (jm1 * p.T) ω = S} ∩ Absorbed) =
              (vm.μ : Measure _) {ω | vm.opinionZeroSet (jm1 * p.T) ω = S} *
                ∑ S' ∈ consF,
                  VoterModel.opinionProcess₂ (lowerBoundGraph p) (jm1 * p.T) p.T S S' := by
          rw [hAbsorbed_eq]
          rw [show ({ω : Ω | vm.opinionZeroSet (jm1 * p.T) ω = S} ∩
              ⋃ S' ∈ consF, {ω : Ω | vm.opinionZeroSet (j * p.T) ω = S'}) =
              ⋃ S' ∈ consF, ({ω : Ω | vm.opinionZeroSet (jm1 * p.T) ω = S} ∩
                {ω : Ω | vm.opinionZeroSet (j * p.T) ω = S'}) from by
            rw [Set.inter_iUnion]; ext ω; simp [Set.mem_iUnion]]
          rw [measure_biUnion_finset]
          · simp_rw [show ∀ S' : Finset (VertexSet p),
              ({ω : Ω | vm.opinionZeroSet (jm1 * p.T) ω = S} ∩ {ω : Ω | vm.opinionZeroSet (j * p.T) ω = S'}) =
              ({ω | vm.opinionZeroSet (jm1 * p.T) ω = S} ∩ {ω | vm.opinionZeroSet (jm1 * p.T + p.T) ω = S'}) from by
              intro S'
              rw [hidx]]
            simp_rw [vm.A_markovMarginal (jm1 * p.T) p.T S]
            rw [Finset.mul_sum]
          · -- pairwise disjoint
            intro S₁ _ S₂ _ hne
            apply Set.disjoint_left.mpr
            rintro ω ⟨_, hω₁⟩ ⟨_, hω₂⟩
            exact hne ((Set.mem_setOf.mp hω₁).symm.trans (Set.mem_setOf.mp hω₂))
          · -- measurable
            intro S' _
            apply MeasurableSet.inter
            · exact vm.A_meas (jm1 * p.T) _ ⟨{S}, trivial, by ext; simp⟩
            · exact vm.A_meas (j * p.T) _ ⟨{S'}, trivial, by ext; simp⟩
        -- perInterval_prob_lower.
        have h_sum_lb := perInterval_prob_lower p (aL S hS) jm1 haL_par Γ α hα hαT hstep S
        -- Rewrite ofReal(1 - (1/2)^α) as 1 - ofReal((1/2)^α) in ENNReal.
        have hpow_nn : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ α := by positivity
        have hpow_le_one : (1 / 2 : ℝ) ^ α ≤ 1 :=
          pow_le_one₀ (by norm_num) (by norm_num)
        have h_sub_eq : ENNReal.ofReal (1 - (1 / 2 : ℝ) ^ α) =
            1 - ENNReal.ofReal ((1 / 2 : ℝ) ^ α) := by
          rw [ENNReal.ofReal_sub _ hpow_nn]
          simp
        rw [h_sub_eq] at h_sum_lb
        -- μ({A=S} ∩ Absᶜ) = μ{A=S} - μ({A=S} ∩ Abs).
        have h_inter_le : (vm.μ : Measure _) ({ω | vm.opinionZeroSet (jm1 * p.T) ω = S} ∩ Absorbed) ≤
            (vm.μ : Measure _) {ω | vm.opinionZeroSet (jm1 * p.T) ω = S} := measure_mono Set.inter_subset_left
        have h_meas_S_ne_top : (vm.μ : Measure _) {ω | vm.opinionZeroSet (jm1 * p.T) ω = S} ≠ ⊤ := measure_ne_top _ _
        have h_compl_eq :
            (vm.μ : Measure _) ({ω | vm.opinionZeroSet (jm1 * p.T) ω = S} ∩ Absorbedᶜ) =
              (vm.μ : Measure _) {ω | vm.opinionZeroSet (jm1 * p.T) ω = S} -
                (vm.μ : Measure _) ({ω | vm.opinionZeroSet (jm1 * p.T) ω = S} ∩ Absorbed) := by
          have hsplit : ({ω | vm.opinionZeroSet (jm1 * p.T) ω = S} ∩ Absorbed) ∪
              ({ω | vm.opinionZeroSet (jm1 * p.T) ω = S} ∩ Absorbedᶜ) =
              {ω | vm.opinionZeroSet (jm1 * p.T) ω = S} := by
            rw [← Set.inter_union_distrib_left, Set.union_compl_self, Set.inter_univ]
          have hdisj : Disjoint ({ω | vm.opinionZeroSet (jm1 * p.T) ω = S} ∩ Absorbed)
              ({ω | vm.opinionZeroSet (jm1 * p.T) ω = S} ∩ Absorbedᶜ) := by
            rw [Set.disjoint_left]
            rintro ω ⟨_, hω₁⟩ ⟨_, hω₂⟩
            exact hω₂ hω₁
          have hAbs_meas : MeasurableSet Absorbed := by
            rw [hAbsorbed_eq]
            refine MeasurableSet.biUnion consF.countable_toSet (fun S' _ => ?_)
            exact vm.A_meas (j * p.T) _ ⟨{S'}, trivial, by ext; simp⟩
          have h_meas_inter_abs_c : MeasurableSet
              ({ω : Ω | vm.opinionZeroSet (jm1 * p.T) ω = S} ∩ Absorbedᶜ) := by
            apply MeasurableSet.inter _ hAbs_meas.compl
            exact vm.A_meas (jm1 * p.T) _ ⟨{S}, trivial, by ext; simp⟩
          have h_union_meas : (vm.μ : Measure _) {ω | vm.opinionZeroSet (jm1 * p.T) ω = S} =
              (vm.μ : Measure _) ({ω | vm.opinionZeroSet (jm1 * p.T) ω = S} ∩ Absorbed) +
                (vm.μ : Measure _) ({ω | vm.opinionZeroSet (jm1 * p.T) ω = S} ∩ Absorbedᶜ) := by
            rw [← measure_union hdisj h_meas_inter_abs_c, hsplit]
          rw [h_union_meas, ENNReal.add_sub_cancel_left (measure_ne_top _ _)]
        rw [h_compl_eq, markovMarginal_sum]
        have hofR_le_one : ENNReal.ofReal ((1 / 2 : ℝ) ^ α) ≤ 1 := by
          rw [show (1 : ENNReal) = ENNReal.ofReal 1 from by simp]
          exact ENNReal.ofReal_le_ofReal hpow_le_one
        calc (vm.μ : Measure _) {ω | vm.opinionZeroSet (jm1 * p.T) ω = S} -
              (vm.μ : Measure _) {ω | vm.opinionZeroSet (jm1 * p.T) ω = S} *
                ∑ S' ∈ consF,
                  VoterModel.opinionProcess₂ (lowerBoundGraph p) (jm1 * p.T) p.T S S'
            ≤ (vm.μ : Measure _) {ω | vm.opinionZeroSet (jm1 * p.T) ω = S} -
              (vm.μ : Measure _) {ω | vm.opinionZeroSet (jm1 * p.T) ω = S} *
                (1 - ENNReal.ofReal ((1 / 2 : ℝ) ^ α)) := by
              apply tsub_le_tsub_left
              exact mul_le_mul_right h_sum_lb _
          _ = (vm.μ : Measure _) {ω | vm.opinionZeroSet (jm1 * p.T) ω = S} *
              ENNReal.ofReal ((1 / 2 : ℝ) ^ α) := by
              rw [ENNReal.mul_sub (fun _ _ => h_meas_S_ne_top), mul_one]
              rw [ENNReal.sub_sub_cancel h_meas_S_ne_top
                (mul_le_of_le_one_right' hofR_le_one)]
          _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ α) *
              (vm.μ : Measure _) {ω | vm.opinionZeroSet (jm1 * p.T) ω = S} := mul_comm _ _
      -- Sum the per-arc bounds.
      have h_sum_bound : ∑ S ∈ arcs,
          (vm.μ : Measure _) (⋃ (hS : IsContiguousArc p S), F₁_main S hS) ≤
            ENNReal.ofReal ((1 / 2 : ℝ) ^ α) * 1 := by
        calc ∑ S ∈ arcs, (vm.μ : Measure _) (⋃ (hS : IsContiguousArc p S), F₁_main S hS)
            ≤ ∑ S ∈ arcs, ENNReal.ofReal ((1 / 2 : ℝ) ^ α) *
                (vm.μ : Measure _) {ω | vm.opinionZeroSet (jm1 * p.T) ω = S} := Finset.sum_le_sum h_arc_bound
          _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ α) *
                ∑ S ∈ arcs, (vm.μ : Measure _) {ω | vm.opinionZeroSet (jm1 * p.T) ω = S} := by rw [Finset.mul_sum]
          _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ α) * 1 := by
              apply mul_le_mul_right
              -- ∑ over arcs ≤ ∑ over univ = 1.
              calc ∑ S ∈ arcs, (vm.μ : Measure _) {ω | vm.opinionZeroSet (jm1 * p.T) ω = S}
                  ≤ ∑ S : Finset (VertexSet p), (vm.μ : Measure _) {ω | vm.opinionZeroSet (jm1 * p.T) ω = S} := by
                    apply Finset.sum_le_sum_of_subset
                    intro S _; exact Finset.mem_univ _
                _ = 1 := by
                  -- total mass.
                  have hdisj : Pairwise (fun T₁ T₂ => Disjoint
                      ({ω : Ω | vm.opinionZeroSet (jm1 * p.T) ω = T₁}) ({ω : Ω | vm.opinionZeroSet (jm1 * p.T) ω = T₂})) := by
                    intro T₁ T₂ hne; rw [Set.disjoint_left]
                    exact fun ω h1 h2 =>
                      hne ((Set.mem_setOf_eq.mp h1).symm.trans (Set.mem_setOf_eq.mp h2))
                  have hmeasT : ∀ T : Finset (VertexSet p),
                      MeasurableSet {ω : Ω | vm.opinionZeroSet (jm1 * p.T) ω = T} :=
                    fun T => vm.A_meas (jm1 * p.T) _ ⟨{T}, trivial, by ext; simp⟩
                  have huniv : (⋃ T : Finset (VertexSet p),
                      {ω : Ω | vm.opinionZeroSet (jm1 * p.T) ω = T}) = Set.univ := by
                    ext ω; simp
                  rw [← measure_univ (μ := (vm.μ : Measure Ω)), ← huniv,
                      measure_iUnion hdisj hmeasT, tsum_fintype]
      -- Combine.
      have h_F₁_main_meas_le :
          (vm.μ : Measure _) F₁_main_union ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ α) := by
        calc (vm.μ : Measure _) F₁_main_union
            ≤ ∑ S ∈ arcs, (vm.μ : Measure _) (⋃ (hS : IsContiguousArc p S), F₁_main S hS) := h_meas_le
          _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ α) * 1 := h_sum_bound
          _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ α) := mul_one _
      have hpow_nn : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ α := by positivity
      have h_toReal :
          ((vm.μ : Measure _) F₁_main_union).toReal ≤ (1 / 2 : ℝ) ^ α := by
        rw [show ((1 / 2 : ℝ) ^ α) = (ENNReal.ofReal ((1 / 2 : ℝ) ^ α)).toReal from
            (ENNReal.toReal_ofReal hpow_nn).symm]
        exact ENNReal.toReal_mono ENNReal.ofReal_ne_top h_F₁_main_meas_le
      exact h_toReal
    -- Combine: F₁ ⊆ F₁_main_union ∪ NullPocket; μ(F₁) ≤ μ(F₁_main) + μ(NullPocket).
    have hF₁_meas_le :
        (vm.μ : Measure _) F₁ ≤ (vm.μ : Measure _) F₁_main_union + (vm.μ : Measure _) NullPocket := by
      calc (vm.μ : Measure _) F₁ ≤ (vm.μ : Measure _) (F₁_main_union ∪ NullPocket) := measure_mono hF₁_sub
        _ ≤ (vm.μ : Measure _) F₁_main_union + (vm.μ : Measure _) NullPocket := measure_union_le _ _
    have hF₁_meas_le' :
        (vm.μ : Measure _) F₁ ≤ (vm.μ : Measure _) F₁_main_union := by
      rw [h_nullPocket_zero, add_zero] at hF₁_meas_le
      exact hF₁_meas_le
    have hF1_ne : (vm.μ : Measure _) F₁ ≠ ⊤ := measure_ne_top _ _
    have hF1main_ne : (vm.μ : Measure _) F₁_main_union ≠ ⊤ := measure_ne_top _ _
    have :=
      ENNReal.toReal_mono hF1main_ne hF₁_meas_le'
    linarith [this, h_F₁_main_bound]
  · -- μ(F₂) ≤ (1/2)^α: same proof structure, using aR.
    classical
    set arcs : Finset (Finset (VertexSet p)) :=
      Finset.univ.filter (IsContiguousArc p) with harcs_def
    have hUnion_finset :
        F₂ = ⋃ S ∈ arcs, ⋃ (hS : IsContiguousArc p S), F₂_main S hS := by
      ext ω
      simp only [F₂, arcs, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ,
                 true_and]
      constructor
      · rintro ⟨S, hS, hω⟩; exact ⟨S, hS, hS, hω⟩
      · rintro ⟨S, hS, hS', hω⟩; exact ⟨S, hS', hω⟩
    have h_meas_le : (vm.μ : Measure _) F₂ ≤
        ∑ S ∈ arcs, (vm.μ : Measure _) (⋃ (hS : IsContiguousArc p S), F₂_main S hS) := by
      rw [hUnion_finset]
      exact measure_biUnion_finset_le _ _
    have h_arc_bound : ∀ S ∈ arcs,
        (vm.μ : Measure _) (⋃ (hS : IsContiguousArc p S), F₂_main S hS) ≤
          ENNReal.ofReal ((1 / 2 : ℝ) ^ α) * (vm.μ : Measure _) {ω | vm.opinionZeroSet (jm1 * p.T) ω = S} := by
      intro S hS_mem
      have hS : IsContiguousArc p S := (Finset.mem_filter.mp hS_mem).2
      have hUnion_single :
          (⋃ (hS' : IsContiguousArc p S), F₂_main S hS') = F₂_main S hS := by
        ext ω; simp only [Set.mem_iUnion]; exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hS, h⟩⟩
      rw [hUnion_single]
      have haR_par : (aR S hS).val % 2 = jm1 % 2 := aR_prop S hS
      set consF : Finset (Finset (VertexSet p)) :=
        Finset.univ.filter (fun S' : Finset (VertexSet p) =>
          block p (aR S hS) ∪ block p (aR S hS + 1) ⊆ S' ∨
          Disjoint (block p (aR S hS) ∪ block p (aR S hS + 1)) S') with hconsF_def
      set Absorbed : Set Ω :=
        {ω | block p (aR S hS) ∪ block p (aR S hS + 1) ⊆ vm.opinionZeroSet (j * p.T) ω ∨
            Disjoint (block p (aR S hS) ∪ block p (aR S hS + 1)) (vm.opinionZeroSet (j * p.T) ω)}
        with hAbsorbed_def
      have hAbsorbed_eq :
          Absorbed = ⋃ S' ∈ consF, {ω : Ω | vm.opinionZeroSet (j * p.T) ω = S'} := by
        ext ω
        simp only [Absorbed, consF, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ,
                   true_and, Set.mem_setOf_eq, exists_prop]
        constructor
        · intro h; exact ⟨vm.opinionZeroSet (j * p.T) ω, h, rfl⟩
        · rintro ⟨S', h1, h2⟩; rw [h2]; exact h1
      have hF₂_eq : F₂_main S hS = {ω | vm.opinionZeroSet (jm1 * p.T) ω = S} ∩ Absorbedᶜ := by
        rfl
      rw [hF₂_eq]
      have markovMarginal_sum :
          (vm.μ : Measure _) ({ω | vm.opinionZeroSet (jm1 * p.T) ω = S} ∩ Absorbed) =
            (vm.μ : Measure _) {ω | vm.opinionZeroSet (jm1 * p.T) ω = S} *
              ∑ S' ∈ consF,
                VoterModel.opinionProcess₂ (lowerBoundGraph p) (jm1 * p.T) p.T S S' := by
        rw [hAbsorbed_eq]
        rw [show ({ω : Ω | vm.opinionZeroSet (jm1 * p.T) ω = S} ∩
            ⋃ S' ∈ consF, {ω : Ω | vm.opinionZeroSet (j * p.T) ω = S'}) =
            ⋃ S' ∈ consF, ({ω : Ω | vm.opinionZeroSet (jm1 * p.T) ω = S} ∩
              {ω : Ω | vm.opinionZeroSet (j * p.T) ω = S'}) from by
          rw [Set.inter_iUnion]; ext ω; simp [Set.mem_iUnion]]
        rw [measure_biUnion_finset]
        · simp_rw [show ∀ S' : Finset (VertexSet p),
            ({ω : Ω | vm.opinionZeroSet (jm1 * p.T) ω = S} ∩ {ω : Ω | vm.opinionZeroSet (j * p.T) ω = S'}) =
            ({ω | vm.opinionZeroSet (jm1 * p.T) ω = S} ∩ {ω | vm.opinionZeroSet (jm1 * p.T + p.T) ω = S'}) from by
            intro S'; rw [hidx]]
          simp_rw [vm.A_markovMarginal (jm1 * p.T) p.T S]
          rw [Finset.mul_sum]
        · intro S₁ _ S₂ _ hne
          apply Set.disjoint_left.mpr
          rintro ω ⟨_, hω₁⟩ ⟨_, hω₂⟩
          exact hne ((Set.mem_setOf.mp hω₁).symm.trans (Set.mem_setOf.mp hω₂))
        · intro S' _
          apply MeasurableSet.inter
          · exact vm.A_meas (jm1 * p.T) _ ⟨{S}, trivial, by ext; simp⟩
          · exact vm.A_meas (j * p.T) _ ⟨{S'}, trivial, by ext; simp⟩
      have h_sum_lb := perInterval_prob_lower p (aR S hS) jm1 haR_par Γ α hα hαT hstep S
      have hpow_nn : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ α := by positivity
      have hpow_le_one : (1 / 2 : ℝ) ^ α ≤ 1 :=
        pow_le_one₀ (by norm_num) (by norm_num)
      have h_sub_eq : ENNReal.ofReal (1 - (1 / 2 : ℝ) ^ α) =
          1 - ENNReal.ofReal ((1 / 2 : ℝ) ^ α) := by
        rw [ENNReal.ofReal_sub _ hpow_nn]; simp
      rw [h_sub_eq] at h_sum_lb
      have h_meas_S_ne_top : (vm.μ : Measure _) {ω | vm.opinionZeroSet (jm1 * p.T) ω = S} ≠ ⊤ := measure_ne_top _ _
      have h_compl_eq :
          (vm.μ : Measure _) ({ω | vm.opinionZeroSet (jm1 * p.T) ω = S} ∩ Absorbedᶜ) =
            (vm.μ : Measure _) {ω | vm.opinionZeroSet (jm1 * p.T) ω = S} -
              (vm.μ : Measure _) ({ω | vm.opinionZeroSet (jm1 * p.T) ω = S} ∩ Absorbed) := by
        have hsplit : ({ω | vm.opinionZeroSet (jm1 * p.T) ω = S} ∩ Absorbed) ∪
            ({ω | vm.opinionZeroSet (jm1 * p.T) ω = S} ∩ Absorbedᶜ) =
            {ω | vm.opinionZeroSet (jm1 * p.T) ω = S} := by
          rw [← Set.inter_union_distrib_left, Set.union_compl_self, Set.inter_univ]
        have hdisj : Disjoint ({ω | vm.opinionZeroSet (jm1 * p.T) ω = S} ∩ Absorbed)
            ({ω | vm.opinionZeroSet (jm1 * p.T) ω = S} ∩ Absorbedᶜ) := by
          rw [Set.disjoint_left]
          rintro ω ⟨_, hω₁⟩ ⟨_, hω₂⟩
          exact hω₂ hω₁
        have hAbs_meas : MeasurableSet Absorbed := by
          rw [hAbsorbed_eq]
          refine MeasurableSet.biUnion consF.countable_toSet (fun S' _ => ?_)
          exact vm.A_meas (j * p.T) _ ⟨{S'}, trivial, by ext; simp⟩
        have h_meas_inter_abs_c : MeasurableSet
            ({ω : Ω | vm.opinionZeroSet (jm1 * p.T) ω = S} ∩ Absorbedᶜ) := by
          apply MeasurableSet.inter _ hAbs_meas.compl
          exact vm.A_meas (jm1 * p.T) _ ⟨{S}, trivial, by ext; simp⟩
        have h_union_meas : (vm.μ : Measure _) {ω | vm.opinionZeroSet (jm1 * p.T) ω = S} =
            (vm.μ : Measure _) ({ω | vm.opinionZeroSet (jm1 * p.T) ω = S} ∩ Absorbed) +
              (vm.μ : Measure _) ({ω | vm.opinionZeroSet (jm1 * p.T) ω = S} ∩ Absorbedᶜ) := by
          rw [← measure_union hdisj h_meas_inter_abs_c, hsplit]
        rw [h_union_meas, ENNReal.add_sub_cancel_left (measure_ne_top _ _)]
      rw [h_compl_eq, markovMarginal_sum]
      have hofR_le_one : ENNReal.ofReal ((1 / 2 : ℝ) ^ α) ≤ 1 := by
        rw [show (1 : ENNReal) = ENNReal.ofReal 1 from by simp]
        exact ENNReal.ofReal_le_ofReal hpow_le_one
      calc (vm.μ : Measure _) {ω | vm.opinionZeroSet (jm1 * p.T) ω = S} -
            (vm.μ : Measure _) {ω | vm.opinionZeroSet (jm1 * p.T) ω = S} *
              ∑ S' ∈ consF,
                VoterModel.opinionProcess₂ (lowerBoundGraph p) (jm1 * p.T) p.T S S'
          ≤ (vm.μ : Measure _) {ω | vm.opinionZeroSet (jm1 * p.T) ω = S} -
            (vm.μ : Measure _) {ω | vm.opinionZeroSet (jm1 * p.T) ω = S} *
              (1 - ENNReal.ofReal ((1 / 2 : ℝ) ^ α)) := by
            apply tsub_le_tsub_left
            exact mul_le_mul_right h_sum_lb _
        _ = (vm.μ : Measure _) {ω | vm.opinionZeroSet (jm1 * p.T) ω = S} *
            ENNReal.ofReal ((1 / 2 : ℝ) ^ α) := by
            rw [ENNReal.mul_sub (fun _ _ => h_meas_S_ne_top), mul_one]
            rw [ENNReal.sub_sub_cancel h_meas_S_ne_top
              (mul_le_of_le_one_right' hofR_le_one)]
        _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ α) *
            (vm.μ : Measure _) {ω | vm.opinionZeroSet (jm1 * p.T) ω = S} := mul_comm _ _
    have h_sum_bound : ∑ S ∈ arcs,
        (vm.μ : Measure _) (⋃ (hS : IsContiguousArc p S), F₂_main S hS) ≤
          ENNReal.ofReal ((1 / 2 : ℝ) ^ α) * 1 := by
      calc ∑ S ∈ arcs, (vm.μ : Measure _) (⋃ (hS : IsContiguousArc p S), F₂_main S hS)
          ≤ ∑ S ∈ arcs, ENNReal.ofReal ((1 / 2 : ℝ) ^ α) *
              (vm.μ : Measure _) {ω | vm.opinionZeroSet (jm1 * p.T) ω = S} := Finset.sum_le_sum h_arc_bound
        _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ α) *
              ∑ S ∈ arcs, (vm.μ : Measure _) {ω | vm.opinionZeroSet (jm1 * p.T) ω = S} := by rw [Finset.mul_sum]
        _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ α) * 1 := by
            apply mul_le_mul_right
            calc ∑ S ∈ arcs, (vm.μ : Measure _) {ω | vm.opinionZeroSet (jm1 * p.T) ω = S}
                ≤ ∑ S : Finset (VertexSet p), (vm.μ : Measure _) {ω | vm.opinionZeroSet (jm1 * p.T) ω = S} := by
                  apply Finset.sum_le_sum_of_subset
                  intro S _; exact Finset.mem_univ _
              _ = 1 := by
                have hdisj : Pairwise (fun T₁ T₂ => Disjoint
                    ({ω : Ω | vm.opinionZeroSet (jm1 * p.T) ω = T₁}) ({ω : Ω | vm.opinionZeroSet (jm1 * p.T) ω = T₂})) := by
                  intro T₁ T₂ hne; rw [Set.disjoint_left]
                  exact fun ω h1 h2 =>
                    hne ((Set.mem_setOf_eq.mp h1).symm.trans (Set.mem_setOf_eq.mp h2))
                have hmeasT : ∀ T : Finset (VertexSet p),
                    MeasurableSet {ω : Ω | vm.opinionZeroSet (jm1 * p.T) ω = T} :=
                  fun T => vm.A_meas (jm1 * p.T) _ ⟨{T}, trivial, by ext; simp⟩
                have huniv : (⋃ T : Finset (VertexSet p),
                    {ω : Ω | vm.opinionZeroSet (jm1 * p.T) ω = T}) = Set.univ := by
                  ext ω; simp
                rw [← measure_univ (μ := (vm.μ : Measure Ω)), ← huniv,
                    measure_iUnion hdisj hmeasT, tsum_fintype]
    have h_F₂_meas_le :
        (vm.μ : Measure _) F₂ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ α) := by
      calc (vm.μ : Measure _) F₂
          ≤ ∑ S ∈ arcs, (vm.μ : Measure _) (⋃ (hS : IsContiguousArc p S), F₂_main S hS) := h_meas_le
        _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ α) * 1 := h_sum_bound
        _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ α) := mul_one _
    have hpow_nn : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ α := by positivity
    rw [show ((1 / 2 : ℝ) ^ α) = (ENNReal.ofReal ((1 / 2 : ℝ) ^ α)).toReal from
        (ENNReal.toReal_ofReal hpow_nn).symm]
    exact ENNReal.toReal_mono ENNReal.ofReal_ne_top h_F₂_meas_le

/-- Per-step arc-failure bound.

If the arc invariant holds at all steps `0, …, j-1` but fails at step `j`
(i.e., the state is NOT a contiguous arc of whole blocks at time `j·T`), then
some seam K_{2k}-clique in interval `I_j` failed to absorb. There are at most
two such seam cliques, each failing with probability `≤ (1/2)^α` by
`arc_fail_has_two_seam_events`. Hence this first-failure event has measure
`≤ 2 · (1/2)^α`. -/
private theorem arc_fail_per_step (Γ : ℕ) (p : Params)
    (α : ℕ) (hα : 1 ≤ α)
    (hαT : Γ * α * p.k ≤ p.T)
    (hstep : ∀ (t : ℕ) (T : Finset (CliqueVertex p.k)),
        (1 / 2 : ENNReal) ≤
          VoterModel.opinionProcess₂ (staticCliqueGraph p.k) t (Γ * p.k) T Finset.univ +
          VoterModel.opinionProcess₂ (staticCliqueGraph p.k) t (Γ * p.k) T ∅)
    {Ω : Type} [MeasurableSpace Ω]
    (vm : TemporalGraph.VoterModelAbstract (lowerBoundGraph p) 2 Ω)
    (j : ℕ) (hj : 1 ≤ j) :
    ((vm.μ : Measure _) ({ω | ∀ i < j, IsContiguousArc p (vm.opinionZeroSet (i * p.T) ω)} ∩
           {ω | ¬IsContiguousArc p (vm.opinionZeroSet (j * p.T) ω)})).toReal
    ≤ 2 * (1 / 2 : ℝ) ^ α := by
  obtain ⟨F₁, F₂, hcover, hF₁, hF₂⟩ :=
    arc_fail_has_two_seam_events Γ p α hα hαT hstep vm j hj
  have hF1ne : (vm.μ : Measure _) F₁ ≠ ⊤ := measure_ne_top _ _
  have hF2ne : (vm.μ : Measure _) F₂ ≠ ⊤ := measure_ne_top _ _
  have hF12ne : (vm.μ : Measure _) F₁ + (vm.μ : Measure _) F₂ ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hF1ne, hF2ne⟩
  calc ((vm.μ : Measure _) ({ω | ∀ i < j, IsContiguousArc p (vm.opinionZeroSet (i * p.T) ω)} ∩
               {ω | ¬IsContiguousArc p (vm.opinionZeroSet (j * p.T) ω)})).toReal
      ≤ ((vm.μ : Measure _) (F₁ ∪ F₂)).toReal :=
          ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hcover)
    _ ≤ ((vm.μ : Measure _) F₁ + (vm.μ : Measure _) F₂).toReal :=
          ENNReal.toReal_mono hF12ne (measure_union_le _ _)
    _ = ((vm.μ : Measure _) F₁).toReal + ((vm.μ : Measure _) F₂).toReal :=
          ENNReal.toReal_add hF1ne hF2ne
    _ ≤ (1 / 2 : ℝ) ^ α + (1 / 2 : ℝ) ^ α := add_le_add hF₁ hF₂
    _ = 2 * (1 / 2 : ℝ) ^ α := by ring

/-- Step-failure bound: P(∃ j ≤ N, arc invariant fails at j·T) ≤ 1/450.

At most 2 seam cliques are mixed per interval; each fails consensus with
probability ≤ (1/2)^α (by `perInterval_prob_lower`). Union bound over N
intervals: P(arcFails) ≤ N · 2 · (1/2)^α ≤ (z²/45) · (2/z³) = 2/(45z) ≤ 1/450. -/
theorem arc_fail_event_le (Γ : ℕ) (p : Params)
    (hz20 : 20 ≤ p.z)
    (α : ℕ) (hα : 1 ≤ α) (hαz2 : (1 / 2 : ℝ) ^ α ≤ 1 / (p.z : ℝ) ^ 3)
    (hαT : Γ * α * p.k ≤ p.T)
    (hstep : ∀ (t : ℕ) (T : Finset (CliqueVertex p.k)),
        (1 / 2 : ENNReal) ≤
          VoterModel.opinionProcess₂ (staticCliqueGraph p.k) t (Γ * p.k) T Finset.univ +
          VoterModel.opinionProcess₂ (staticCliqueGraph p.k) t (Γ * p.k) T ∅)
    {Ω : Type} [MeasurableSpace Ω]
    (vm : TemporalGraph.VoterModelAbstract (lowerBoundGraph p) 2 Ω)
    (hA₀ : ∀ᵐ ω ∂(vm.μ : Measure Ω), vm.opinionZeroSet 0 ω = halfCutLow p) (N : ℕ)
    (hN : (N : ℝ) < (p.z : ℝ) ^ 2 / 45) :
    ((vm.μ : Measure _) {ω | ∃ j ≤ N, ¬IsContiguousArc p (vm.opinionZeroSet (j * p.T) ω)}).toReal ≤ 1 / 450 := by
  classical
  -- First-failure decomposition. Define
  --   FF j = {arc holds at all i < j} ∩ {arc fails at j}.
  -- Then {∃ j ≤ N, ¬arc(j)} ⊆ ⋃ j ∈ Icc 1 N, FF j, because arc(0) is true
  -- (from `hA₀` + `halfCutLow_isContiguousArc`), so the minimal failing index
  -- is ≥ 1 and ≤ N.
  set FF : ℕ → Set Ω :=
    fun j => {ω | ∀ i < j, IsContiguousArc p (vm.opinionZeroSet (i * p.T) ω)} ∩
             {ω | ¬IsContiguousArc p (vm.opinionZeroSet (j * p.T) ω)}
  -- The initial arc holds only a.e.; its complement is a null set `Bad0`.
  set Bad0 : Set Ω := {ω | ¬IsContiguousArc p (vm.opinionZeroSet 0 ω)} with hBad0_def
  have hBad0_zero : (vm.μ : Measure _) Bad0 = 0 := by
    rw [hBad0_def, ← MeasureTheory.ae_iff]
    filter_upwards [hA₀] with ω hω
    rw [hω]; exact halfCutLow_isContiguousArc p
  -- On the good event (arc holds at 0), a first arc failure occurs at some `1 ≤ j ≤ N`;
  -- outcomes violating this land in the null set `Bad0`.
  have h_sub : {ω : Ω | ∃ j ≤ N, ¬IsContiguousArc p (vm.opinionZeroSet (j * p.T) ω)} ⊆
      (⋃ j ∈ Finset.Icc 1 N, FF j) ∪ Bad0 := by
    intro ω hω
    by_cases harc0ω : IsContiguousArc p (vm.opinionZeroSet 0 ω)
    · refine Set.mem_union_left _ ?_
      -- Predicate `Q j ↔ j ≤ N ∧ ¬arc(j)`.
      obtain ⟨j₀, hj₀N, hj₀⟩ := hω
      let Q : ℕ → Prop := fun j => j ≤ N ∧ ¬IsContiguousArc p (vm.opinionZeroSet (j * p.T) ω)
      have hQj₀ : Q j₀ := ⟨hj₀N, hj₀⟩
      let j_star := Nat.find ⟨j₀, hQj₀⟩
      have hQjs : Q j_star := Nat.find_spec ⟨j₀, hQj₀⟩
      have hjs_min : ∀ i, i < j_star → ¬ Q i := fun i hi => Nat.find_min _ hi
      have hjs_le : j_star ≤ N := hQjs.1
      have hjs_fail : ¬IsContiguousArc p (vm.opinionZeroSet (j_star * p.T) ω) := hQjs.2
      have hjs_pos : 1 ≤ j_star := by
        by_contra hlt
        push Not at hlt
        interval_cases j_star
        have : IsContiguousArc p (vm.opinionZeroSet (0 * p.T) ω) := by
          rw [Nat.zero_mul]; exact harc0ω
        exact hjs_fail this
      refine Set.mem_iUnion₂.mpr ⟨j_star, ?_, ?_, hjs_fail⟩
      · exact Finset.mem_Icc.mpr ⟨hjs_pos, hjs_le⟩
      · intro i hi
        have hQi : ¬ Q i := hjs_min i hi
        by_contra hne
        exact hQi ⟨Nat.le_trans (Nat.le_of_lt hi) hjs_le, hne⟩
    · exact Set.mem_union_right _ harc0ω
  -- Sub-additivity: μ(⋃ FF j) ≤ ∑ μ(FF j).
  have hpow_nn : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ α := by positivity
  have h2pow_nn : (0 : ℝ) ≤ 2 * (1 / 2 : ℝ) ^ α := by positivity
  have h_per : ∀ j ∈ Finset.Icc 1 N, ((vm.μ : Measure _) (FF j)).toReal ≤ 2 * (1 / 2 : ℝ) ^ α := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    exact arc_fail_per_step Γ p α hα hαT hstep vm j hj1
  -- Step 1: μ(bad) ≤ μ(⋃ FF) ≤ ∑ μ(FF).
  have h_meas_le :
      (vm.μ : Measure _) {ω : Ω | ∃ j ≤ N, ¬IsContiguousArc p (vm.opinionZeroSet (j * p.T) ω)} ≤
        ∑ j ∈ Finset.Icc 1 N, (vm.μ : Measure _) (FF j) := by
    calc (vm.μ : Measure _) {ω : Ω | ∃ j ≤ N, ¬IsContiguousArc p (vm.opinionZeroSet (j * p.T) ω)}
        ≤ (vm.μ : Measure _) ((⋃ j ∈ Finset.Icc 1 N, FF j) ∪ Bad0) := measure_mono h_sub
      _ ≤ (vm.μ : Measure _) (⋃ j ∈ Finset.Icc 1 N, FF j) + (vm.μ : Measure _) Bad0 :=
            measure_union_le _ _
      _ = (vm.μ : Measure _) (⋃ j ∈ Finset.Icc 1 N, FF j) := by rw [hBad0_zero, add_zero]
      _ ≤ ∑ j ∈ Finset.Icc 1 N, (vm.μ : Measure _) (FF j) := measure_biUnion_finset_le _ _
  -- Step 2: convert to ℝ via toReal monotonicity, then bound the sum.
  have h_sum_ne_top : ∀ j ∈ Finset.Icc 1 N, (vm.μ : Measure _) (FF j) ≠ ⊤ :=
    fun j _ => measure_ne_top _ _
  have h_sum_total_ne_top : (∑ j ∈ Finset.Icc 1 N, (vm.μ : Measure _) (FF j)) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr h_sum_ne_top
  have h_real_le :
      ((vm.μ : Measure _) {ω : Ω | ∃ j ≤ N, ¬IsContiguousArc p (vm.opinionZeroSet (j * p.T) ω)}).toReal ≤
        ∑ j ∈ Finset.Icc 1 N, ((vm.μ : Measure _) (FF j)).toReal := by
    have h1 : ((vm.μ : Measure _) {ω : Ω | ∃ j ≤ N, ¬IsContiguousArc p (vm.opinionZeroSet (j * p.T) ω)}).toReal ≤
        (∑ j ∈ Finset.Icc 1 N, (vm.μ : Measure _) (FF j)).toReal :=
      ENNReal.toReal_mono h_sum_total_ne_top h_meas_le
    have h2 : (∑ j ∈ Finset.Icc 1 N, (vm.μ : Measure _) (FF j)).toReal =
        ∑ j ∈ Finset.Icc 1 N, ((vm.μ : Measure _) (FF j)).toReal :=
      ENNReal.toReal_sum h_sum_ne_top
    linarith [h2 ▸ h1]
  have h_sum_le :
      ∑ j ∈ Finset.Icc 1 N, ((vm.μ : Measure _) (FF j)).toReal ≤
        ∑ _j ∈ Finset.Icc 1 N, 2 * (1 / 2 : ℝ) ^ α :=
    Finset.sum_le_sum h_per
  have h_sum_const :
      ∑ _j ∈ Finset.Icc 1 N, (2 * (1 / 2 : ℝ) ^ α) =
        (N : ℝ) * (2 * (1 / 2 : ℝ) ^ α) := by
    rw [Finset.sum_const, Nat.card_Icc]
    have hNN : (N + 1 - 1 : ℕ) = N := by omega
    rw [hNN, nsmul_eq_mul]
  -- Step 3: arithmetic. N · 2 · (1/2)^α ≤ (z²/45) · 2 · (1/z³) = 2/(45z) ≤ 1/450.
  have hzR_pos : (0 : ℝ) < (p.z : ℝ) := by
    have : (1 : ℕ) ≤ p.z := p.hz_pos
    exact_mod_cast Nat.lt_of_lt_of_le Nat.one_pos this
  have hz20R : (20 : ℝ) ≤ (p.z : ℝ) := by exact_mod_cast hz20
  have hN_nn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  -- N · 2 · (1/2)^α ≤ N · 2 · (1/z³)
  have h_step1 : (N : ℝ) * (2 * (1 / 2 : ℝ) ^ α) ≤
      (N : ℝ) * (2 * (1 / (p.z : ℝ) ^ 3)) := by
    have : (2 : ℝ) * (1 / 2 : ℝ) ^ α ≤ 2 * (1 / (p.z : ℝ) ^ 3) := by
      have h2nn : (0 : ℝ) ≤ 2 := by norm_num
      linarith [hαz2]
    nlinarith [hN_nn, this]
  -- N · 2 · (1/z³) ≤ (z²/45) · 2 · (1/z³) = 2/(45z) ≤ 1/450
  have h_step2 : (N : ℝ) * (2 * (1 / (p.z : ℝ) ^ 3)) ≤ 1 / 450 := by
    have h_inv_nn : (0 : ℝ) ≤ 2 * (1 / (p.z : ℝ) ^ 3) := by positivity
    -- N · (2/z³) ≤ (z²/45) · (2/z³)
    have hmul : (N : ℝ) * (2 * (1 / (p.z : ℝ) ^ 3)) ≤
        ((p.z : ℝ) ^ 2 / 45) * (2 * (1 / (p.z : ℝ) ^ 3)) := by
      exact mul_le_mul_of_nonneg_right hN.le h_inv_nn
    have hz_ne : ((p.z : ℝ)) ≠ 0 := ne_of_gt hzR_pos
    have hsimpl : ((p.z : ℝ) ^ 2 / 45) * (2 * (1 / (p.z : ℝ) ^ 3)) = 2 / (45 * (p.z : ℝ)) := by
      field_simp
    have hfin : 2 / (45 * (p.z : ℝ)) ≤ 1 / 450 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 450)]
      linarith [hz20R]
    linarith [hmul, hsimpl.le, hsimpl.ge, hfin]
  -- Chain everything.
  calc ((vm.μ : Measure _) {ω : Ω | ∃ j ≤ N, ¬IsContiguousArc p (vm.opinionZeroSet (j * p.T) ω)}).toReal
      ≤ ∑ j ∈ Finset.Icc 1 N, ((vm.μ : Measure _) (FF j)).toReal := h_real_le
    _ ≤ ∑ _j ∈ Finset.Icc 1 N, (2 * (1 / 2 : ℝ) ^ α) := h_sum_le
    _ = (N : ℝ) * (2 * (1 / 2 : ℝ) ^ α) := h_sum_const
    _ ≤ (N : ℝ) * (2 * (1 / (p.z : ℝ) ^ 3)) := h_step1
    _ ≤ 1 / 450 := h_step2


end TemporalGraph.VoterProcess.LowerBound
