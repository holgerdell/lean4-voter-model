module

public import LowerBound.Construction
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! ## Arc decomposition via seam-clique anchors

Characterizes `IsContiguousArc` via per-clique consensus and boundary anchors.

For an arc `S = block b ∪ … ∪ block (b+m-1)`, the *seam cliques* are pairs
`block a ∪ block (a+1)`. Interior seam cliques of `S` start in consensus (all-in or all-out),
while the two *boundary anchors* `aL = b-1` and `aR = b+m-1` are the only seam cliques
that can be in mixed state.

## Main results
- `arc_anchors_card_le_two` — at most 2 seam cliques per arc can be mixed.
- `arcExtensionConsensus` — the two consensus values that preserve the arc at each boundary.
- `arc_consensus_classify` — if an arc transitions, the result is still an arc or shrinks.
-/

@[expose] public section

noncomputable section

namespace TemporalGraph.VoterProcess.LowerBound

open MeasureTheory Finset
open scoped BigOperators

/-- The seam clique anchors of arc `S`: the (at most 2) block indices `a` such that
`block a ∪ block (a+1)` is NOT in consensus w.r.t. `S` (i.e., neither `⊆ S` nor `Disjoint S`).
For an arc `S = ⋃_{i<m} block(b+i)`, only `a = b-1` (left boundary) and `a = b+m-1`
(right boundary) are mixed. -/
def seamMixedAnchors (p : Params) (S : Finset (VertexSet p)) : Finset (Fin p.z) :=
  Finset.univ.filter fun a =>
    ¬ ((block p a ∪ block p ⟨(a.val + 1) % p.z, Nat.mod_lt _ p.hz_pos⟩) ⊆ S ∨
       Disjoint (block p a ∪ block p ⟨(a.val + 1) % p.z, Nat.mod_lt _ p.hz_pos⟩ : Finset _) S)

/-- Auxiliary: for an arc `S`, every block is either fully in `S` or disjoint from `S`. -/
private theorem arc_block_dichotomy (p : Params) (S : Finset (VertexSet p))
    (h : IsContiguousArc p S) (c : Fin p.z) :
    block p c ⊆ S ∨ Disjoint (block p c) S := by
  obtain ⟨b, m, _hm, hS⟩ := h
  by_cases hex : ∃ i ∈ Finset.range m,
      c = (⟨(b.val + i) % p.z, Nat.mod_lt _ p.hz_pos⟩ : Fin p.z)
  · left
    obtain ⟨i, hi, hci⟩ := hex
    intro v hv
    rw [mem_block] at hv
    rw [hS]
    refine Finset.mem_biUnion.mpr ⟨i, hi, ?_⟩
    rw [mem_block, hv, hci]
  · right
    refine Finset.disjoint_left.mpr ?_
    intro v hvb hvS
    apply hex
    rw [hS] at hvS
    obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp hvS
    refine ⟨i, hi, ?_⟩
    rw [mem_block] at hvb hvi
    rw [← hvb, hvi]

/-- Auxiliary: blocks are nonempty (since `p.k > 0`). -/
private theorem block_nonempty (p : Params) (c : Fin p.z) : (block p c).Nonempty :=
  ⟨(c, ⟨0, p.hk_pos⟩), (mem_block p c _).mpr rfl⟩

/-- Auxiliary: for an arc, `block c ⊆ S` and `Disjoint (block c) S` are mutually exclusive. -/
private theorem arc_block_subset_iff_not_disjoint (p : Params) (S : Finset (VertexSet p))
    (h : IsContiguousArc p S) (c : Fin p.z) :
    block p c ⊆ S ↔ ¬ Disjoint (block p c) S := by
  constructor
  · intro hsub hdisj
    obtain ⟨v, hv⟩ := block_nonempty p c
    exact (Finset.disjoint_left.mp hdisj) hv (hsub hv)
  · intro hndisj
    rcases arc_block_dichotomy p S h c with hsub | hdisj
    · exact hsub
    · exact (hndisj hdisj).elim

/-- For a contiguous arc, at most 2 seam cliques are mixed: the two boundary anchors. -/
theorem arc_anchors_card_le_two (p : Params) (S : Finset (VertexSet p))
    (h : IsContiguousArc p S) :
    (seamMixedAnchors p S).card ≤ 2 := by
  -- An arc is a union of consecutive blocks. Interior seam cliques have both blocks inside
  -- (→ ⊆ S) or both outside (→ Disjoint). Only the left and right boundary cliques
  -- straddle the arc boundary, contributing one mixed anchor each.
  -- Strategy: define inArc(c) := block c ⊆ S, then a seam at anchor a is mixed iff
  -- inArc(a) ≠ inArc(a+1). Show seamMixedAnchors ⊆ {aL, aR} for explicit aL, aR.
  obtain ⟨b, m, hm_le, hS⟩ := h
  -- Define inArc: a block index is "in the arc" iff its block ⊆ S.
  let inArc : Fin p.z → Prop := fun c => block p c ⊆ S
  -- Equivalent characterization for arcs:
  have hinArc_iff : ∀ c : Fin p.z, inArc c ↔
      ∃ i ∈ Finset.range m, c = (⟨(b.val + i) % p.z, Nat.mod_lt _ p.hz_pos⟩ : Fin p.z) := by
    intro c
    constructor
    · intro hsub
      obtain ⟨v, hv⟩ := block_nonempty p c
      have hvS : v ∈ S := hsub hv
      rw [hS] at hvS
      obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp hvS
      rw [mem_block] at hv hvi
      exact ⟨i, hi, hv ▸ hvi⟩
    · rintro ⟨i, hi, hci⟩
      intro v hv
      rw [mem_block] at hv
      rw [hS]
      refine Finset.mem_biUnion.mpr ⟨i, hi, ?_⟩
      rw [mem_block, hv, hci]
  -- The successor in Fin p.z.
  let succ : Fin p.z → Fin p.z := fun a => ⟨(a.val + 1) % p.z, Nat.mod_lt _ p.hz_pos⟩
  -- A seam at anchor a is mixed iff inArc a ≠ inArc (succ a).
  have hmixed_iff : ∀ a : Fin p.z, a ∈ seamMixedAnchors p S ↔ (inArc a ↔ ¬ inArc (succ a)) := by
    intro a
    classical
    have hdich_a := arc_block_dichotomy p S ⟨b, m, hm_le, hS⟩ a
    have hdich_s := arc_block_dichotomy p S ⟨b, m, hm_le, hS⟩ (succ a)
    have hexcl_a := arc_block_subset_iff_not_disjoint p S ⟨b, m, hm_le, hS⟩ a
    have hexcl_s := arc_block_subset_iff_not_disjoint p S ⟨b, m, hm_le, hS⟩ (succ a)
    simp only [seamMixedAnchors, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hnconsensus
      -- hnconsensus: ¬ (block a ∪ block (succ a) ⊆ S ∨ Disjoint (block a ∪ block (succ a)) S)
      push Not at hnconsensus
      obtain ⟨hnsub, hndisj⟩ := hnconsensus
      -- Mixed: not both subset and not fully disjoint
      have hnboth_sub : ¬ (inArc a ∧ inArc (succ a)) := by
        intro ⟨ha, hs⟩; exact hnsub (Finset.union_subset ha hs)
      have hnboth_disj : ¬ (Disjoint (block p a) S ∧ Disjoint (block p (succ a)) S) := by
        intro ⟨ha, hs⟩
        exact hndisj (Finset.disjoint_union_left.mpr ⟨ha, hs⟩)
      -- inArc a XOR inArc (succ a)
      rcases hdich_a with hain | hadisj
      · rcases hdich_s with hsin | hsdisj
        · exact (hnboth_sub ⟨hain, hsin⟩).elim
        · -- inArc a holds, ¬ inArc (succ a) by disjointness
          have hns : ¬ inArc (succ a) := fun hin => (hexcl_s.mp hin) hsdisj
          exact ⟨fun _ => hns, fun _ => hain⟩
      · rcases hdich_s with hsin | hsdisj
        · -- ¬ inArc a (by disjoint), inArc (succ a) — both directions vacuous
          have hna : ¬ inArc a := fun hin => (hexcl_a.mp hin) hadisj
          exact ⟨fun ha => absurd ha hna, fun hns => absurd hsin hns⟩
        · exact (hnboth_disj ⟨hadisj, hsdisj⟩).elim
    · intro hxor
      -- Goal: ¬ (subset ∨ Disjoint)
      push Not
      refine ⟨?_, ?_⟩
      · intro hsub
        have ha : inArc a := fun v hv => hsub (Finset.mem_union_left _ hv)
        have hs : inArc (succ a) := fun v hv => hsub (Finset.mem_union_right _ hv)
        exact (hxor.mp ha) hs
      · intro hdisj
        rcases hdich_a with hain | hadisj
        · rcases hdich_s with hsin | hsdisj
          · exact (hxor.mp hain) hsin
          · obtain ⟨v, hv⟩ := block_nonempty p a
            have hvU : v ∈ block p a ∪ block p (succ a) := Finset.mem_union_left _ hv
            exact (Finset.disjoint_left.mp hdisj) hvU (hain hv)
        · rcases hdich_s with hsin | hsdisj
          · obtain ⟨v, hv⟩ := block_nonempty p (succ a)
            have hvU : v ∈ block p a ∪ block p (succ a) := Finset.mem_union_right _ hv
            exact (Finset.disjoint_left.mp hdisj) hvU (hsin hv)
          · -- both blocks disjoint from S, so neither is in arc
            have hna : ¬ inArc a := fun hin => (hexcl_a.mp hin) hadisj
            have hns : ¬ inArc (succ a) := fun hin => (hexcl_s.mp hin) hsdisj
            -- xor says inArc a ↔ ¬ inArc (succ a). Given ¬ inArc (succ a), get inArc a, contradicting hna.
            exact hna (hxor.mpr hns)
  -- The set of indices in the arc: image of range m under (b + ·) mod z.
  let arcIdx : Finset (Fin p.z) := (Finset.range m).image
    (fun i => (⟨(b.val + i) % p.z, Nat.mod_lt _ p.hz_pos⟩ : Fin p.z))
  -- inArc c ↔ c ∈ arcIdx
  have hinArc_iff' : ∀ c : Fin p.z, inArc c ↔ c ∈ arcIdx := by
    intro c
    rw [hinArc_iff c]
    simp only [arcIdx, Finset.mem_image, Finset.mem_range]
    exact ⟨fun ⟨i, hi, hci⟩ => ⟨i, hi, hci.symm⟩, fun ⟨i, hi, hci⟩ => ⟨i, hi, hci.symm⟩⟩
  -- Now bound. Cases on m = 0, m = p.z, or 0 < m < p.z.
  rcases Nat.eq_zero_or_pos m with hm0 | hm_pos
  · -- m = 0: arc is empty, no mixed anchors.
    have : seamMixedAnchors p S = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro a hamem
      rw [hmixed_iff a] at hamem
      have hna : ¬ inArc a := by
        rw [hinArc_iff a]; rintro ⟨i, hi, _⟩
        rw [hm0, Finset.range_zero] at hi; exact (Finset.notMem_empty _) hi
      have hns : ¬ inArc (succ a) := by
        rw [hinArc_iff (succ a)]; rintro ⟨i, hi, _⟩
        rw [hm0, Finset.range_zero] at hi; exact (Finset.notMem_empty _) hi
      exact hna (hamem.mpr hns)
    rw [this]; simp
  · -- m ≥ 1.
    by_cases hm_full : m = p.z
    · -- m = p.z: arcIdx = univ, every block is in arc, no mixed anchors.
      have harc_univ : arcIdx = Finset.univ := by
        apply Finset.eq_univ_of_forall
        intro c
        -- c.val < p.z, find i = (c.val - b.val + p.z) % p.z < m = p.z
        let i : ℕ := (c.val + p.z - b.val) % p.z
        have hi_lt : i < p.z := Nat.mod_lt _ p.hz_pos
        have hi_lt_m : i < m := hm_full ▸ hi_lt
        refine Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi_lt_m, ?_⟩
        apply Fin.ext
        show (b.val + i) % p.z = c.val
        have h1 : (b.val + (c.val + p.z - b.val) % p.z) % p.z = c.val := by
          have hbz : b.val < p.z := b.isLt
          have hcz : c.val < p.z := c.isLt
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
          have : b.val + (c.val + p.z - b.val) = c.val + p.z := by omega
          rw [this, Nat.add_mod_right]
          exact Nat.mod_eq_of_lt hcz
        exact h1
      have : seamMixedAnchors p S = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro a hamem
        rw [hmixed_iff a] at hamem
        have ha : inArc a := (hinArc_iff' a).mpr (harc_univ ▸ Finset.mem_univ _)
        have hs : inArc (succ a) := (hinArc_iff' (succ a)).mpr (harc_univ ▸ Finset.mem_univ _)
        exact (hamem.mp ha) hs
      rw [this]; simp
    · -- 0 < m < p.z: define explicit aL and aR boundaries.
      have hm_lt : m < p.z := lt_of_le_of_ne hm_le hm_full
      -- aL: predecessor of b, the "left boundary" anchor.
      let aL : Fin p.z := ⟨(b.val + p.z - 1) % p.z, Nat.mod_lt _ p.hz_pos⟩
      -- aR: b + m - 1, the "right boundary" anchor.
      let aR : Fin p.z := ⟨(b.val + m - 1) % p.z, Nat.mod_lt _ p.hz_pos⟩
      -- Show seamMixedAnchors p S ⊆ {aL, aR}.
      have hsub : seamMixedAnchors p S ⊆ {aL, aR} := by
        intro a ha
        rw [hmixed_iff a] at ha
        rw [hinArc_iff' a, hinArc_iff' (succ a)] at ha
        -- ha : a ∈ arcIdx ↔ ¬ (succ a ∈ arcIdx)
        -- I.e., exactly one of a, succ a is in arcIdx.
        -- Case 1: a ∈ arcIdx, succ a ∉ arcIdx → a = aR.
        -- Case 2: a ∉ arcIdx, succ a ∈ arcIdx → a = aL.
        rw [Finset.mem_insert, Finset.mem_singleton]
        by_cases ha_in : a ∈ arcIdx
        · right
          have hs_out : succ a ∉ arcIdx := ha.mp ha_in
          -- a ∈ arcIdx: a = b + i for some i < m. succ a = b + i + 1.
          -- succ a ∉ arcIdx: i + 1 ≥ m. So i = m - 1 and a = b + m - 1 = aR.
          obtain ⟨i, hi, ha_eq⟩ := Finset.mem_image.mp ha_in
          rw [Finset.mem_range] at hi
          have hi_eq_pred : i = m - 1 := by
            by_contra hne
            have hi_lt_pred : i < m - 1 := Nat.lt_of_le_of_ne (Nat.le_pred_of_lt hi) hne
            have hi1_lt : i + 1 < m := by omega
            apply hs_out
            refine Finset.mem_image.mpr ⟨i + 1, Finset.mem_range.mpr hi1_lt, ?_⟩
            apply Fin.ext
            show (b.val + (i + 1)) % p.z = (a.val + 1) % p.z
            rw [← ha_eq]
            show (b.val + (i + 1)) % p.z = ((b.val + i) % p.z + 1) % p.z
            conv_rhs => rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
            ring_nf
          -- so a.val = (b.val + (m - 1)) % p.z
          show a = aR
          apply Fin.ext
          rw [← ha_eq]
          show (b.val + i) % p.z = (b.val + m - 1) % p.z
          rw [hi_eq_pred]
          congr 1
          omega
        · left
          have hs_in : succ a ∈ arcIdx := by
            by_contra hs_out
            have ha_in' : a ∈ arcIdx := ha.mpr hs_out
            exact ha_in ha_in'
          -- succ a ∈ arcIdx: succ a = b + i for some i < m.
          -- a ∉ arcIdx: a = succ a - 1 = b + i - 1, which is not in arcIdx.
          -- So i = 0, succ a = b, a = b - 1 = aL.
          obtain ⟨i, hi, hs_eq⟩ := Finset.mem_image.mp hs_in
          rw [Finset.mem_range] at hi
          have hi_eq_zero : i = 0 := by
            by_contra hne
            have hi_pos : 0 < i := Nat.pos_of_ne_zero hne
            apply ha_in
            refine Finset.mem_image.mpr ⟨i - 1, Finset.mem_range.mpr (by omega), ?_⟩
            apply Fin.ext
            -- a.val = (succ a).val - 1 ... but in modular arithmetic.
            -- We have (succ a).val = (a.val + 1) % p.z.
            -- And (succ a).val = (b.val + i) % p.z.
            -- We want a.val = (b.val + (i - 1)) % p.z.
            have h_sa_val : (succ a).val = (b.val + i) % p.z := by
              rw [Fin.ext_iff] at hs_eq; exact hs_eq.symm
            -- (a.val + 1) % p.z = (b.val + i) % p.z
            have h_aval_succ : (a.val + 1) % p.z = (b.val + i) % p.z := h_sa_val
            -- We want (b.val + (i - 1)) % p.z = a.val.
            show (b.val + (i - 1)) % p.z = a.val
            -- Approach: use the relation (a.val + 1) % p.z = (b.val + i) % p.z
            -- Subtracting 1: a.val = (b.val + i - 1) % p.z = (b.val + (i-1)) % p.z.
            have ha_lt : a.val < p.z := a.isLt
            have hbz : b.val < p.z := b.isLt
            have hiz : i < p.z := lt_of_lt_of_le hi hm_le
            -- (a.val + 1) is either < p.z or = p.z.
            by_cases h_aval_p : a.val + 1 < p.z
            · rw [Nat.mod_eq_of_lt h_aval_p] at h_aval_succ
              -- h_aval_succ : a.val + 1 = (b.val + i) % p.z
              -- We use: b.val + i = (b.val + i) % p.z + p.z * ((b.val + i) / p.z).
              have hbi_eq : b.val + i = (b.val + i) % p.z + p.z * ((b.val + i) / p.z) := by
                have := Nat.div_add_mod (b.val + i) p.z; omega
              rw [← h_aval_succ] at hbi_eq
              set q := (b.val + i) / p.z
              -- b.val + (i-1) = a.val + p.z * q (using i ≥ 1).
              have hbi_pred : b.val + (i - 1) = a.val + p.z * q := by omega
              rw [hbi_pred, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha_lt]
            · -- a.val + 1 = p.z, so (a.val + 1) % p.z = 0 = (b.val + i) % p.z.
              have h_aval_eq : a.val + 1 = p.z := by omega
              have h_zero : (a.val + 1) % p.z = 0 := by rw [h_aval_eq, Nat.mod_self]
              rw [h_zero] at h_aval_succ
              have ha_eq : a.val = p.z - 1 := by omega
              -- b.val + i = p.z * q (since (b.val+i) % p.z = 0).
              have hbi_eq : b.val + i = (b.val + i) % p.z + p.z * ((b.val + i) / p.z) := by
                have := Nat.div_add_mod (b.val + i) p.z; omega
              rw [← h_aval_succ, Nat.zero_add] at hbi_eq
              set q := (b.val + i) / p.z
              have hq_pos : 0 < q := by
                have hbi_pos : 0 < b.val + i := by omega
                rw [hbi_eq] at hbi_pos
                rcases Nat.eq_zero_or_pos q with hz | hz
                · simp [hz] at hbi_pos
                · exact hz
              -- b.val + (i-1) = p.z * q - 1 = a.val + p.z * (q-1) (using a.val = p.z - 1).
              have hbi_pred : b.val + (i - 1) = a.val + p.z * (q - 1) := by
                have hq_eq : p.z * q = p.z * (q - 1) + p.z := by
                  have := hq_pos; have hz := p.hz_pos
                  rcases Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hq_pos)
                    with ⟨q', hq'⟩
                  rw [hq']; simp [Nat.mul_succ]
                omega
              rw [hbi_pred, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha_lt]
          show a = aL
          apply Fin.ext
          show a.val = (b.val + p.z - 1) % p.z
          -- We know succ a ∈ arcIdx with i = 0, so (succ a).val = b.val.
          -- And (succ a).val = (a.val + 1) % p.z, so (a.val + 1) % p.z = b.val.
          have h_sa_eq_b : (succ a).val = b.val := by
            rw [Fin.ext_iff] at hs_eq
            rw [hs_eq.symm]
            show (b.val + i) % p.z = b.val
            rw [hi_eq_zero, Nat.add_zero, Nat.mod_eq_of_lt b.isLt]
          have h_aval_succ : (a.val + 1) % p.z = b.val := h_sa_eq_b
          have ha_lt : a.val < p.z := a.isLt
          have hbz : b.val < p.z := b.isLt
          by_cases hb_pos : 0 < b.val
          · -- a.val + 1 = b.val < p.z, so a.val = b.val - 1.
            have : a.val + 1 = b.val := by
              by_cases h_p : a.val + 1 < p.z
              · rw [Nat.mod_eq_of_lt h_p] at h_aval_succ; exact h_aval_succ
              · -- a.val + 1 = p.z, so mod = 0 = b.val? But b.val > 0. Contradiction.
                have : a.val + 1 = p.z := by omega
                rw [this, Nat.mod_self] at h_aval_succ; omega
            have : a.val = b.val - 1 := by omega
            rw [this]
            -- Goal: b.val - 1 = (b.val + p.z - 1) % p.z
            have : b.val + p.z - 1 = p.z + (b.val - 1) := by omega
            rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt]
            omega
          · -- b.val = 0, so (a.val + 1) % p.z = 0, so a.val + 1 = p.z (or a.val + 1 = 0 impossible).
            have hb0 : b.val = 0 := Nat.eq_zero_of_not_pos hb_pos
            have h0 : (a.val + 1) % p.z = 0 := hb0 ▸ h_aval_succ
            have h_aval : a.val + 1 = p.z := by
              have h1 := a.isLt
              -- a.val + 1 ≤ p.z, and (a.val + 1) % p.z = 0
              by_cases h_eq : a.val + 1 = p.z
              · exact h_eq
              · have h_lt : a.val + 1 < p.z := by omega
                rw [Nat.mod_eq_of_lt h_lt] at h0
                omega
            -- aL.val = (0 + p.z - 1) % p.z = (p.z - 1) % p.z = p.z - 1.
            show a.val = (b.val + p.z - 1) % p.z
            rw [hb0, Nat.zero_add, Nat.mod_eq_of_lt (by have := p.hz_pos; omega : p.z - 1 < p.z)]
            omega
      calc (seamMixedAnchors p S).card
          ≤ ({aL, aR} : Finset (Fin p.z)).card := Finset.card_le_card hsub
        _ ≤ 2 := by
            apply le_trans (Finset.card_insert_le _ _)
            simp




end TemporalGraph.VoterProcess.LowerBound
