module

public import LowerBound.Construction
public import LowerBound.StaticClique
import VoterProcess.Expectation
import LowerBound.Absorbing

/-! ## Clique sub-process factorization for the lower-bound graph

PMF-level infrastructure for `perInterval_absorption_prob` (§4 lower bound).

The lower-bound graph `lowerBoundGraph p` alternates between two snapshot graphs each
of length `p.T`. In interval `I_{j+1}` (steps `j·T` to `(j+1)·T − 1`), the graph
equals `snapshot0 p` or `snapshot1 p` depending on the parity of `j`. The active
K_{2k} cliques for that interval are `block p a ∪ block p (a+1)` for each anchor
`a` with `a.val % 2 = j % 2`.

## Key results

- `cliqueFinset p a`, `toCliqueVtx p a`, `cliqueRestrict p a` — bijection between
  the K_{2k} clique and `CliqueVertex p.k = Fin (2*p.k)`.
- `opinionProcess₂_clique_marginal` — PMF-level factorization: the marginal of
  `opinionProcess₂ (lowerBoundGraph p) (j·T) n S` restricted to the clique equals
  `opinionProcess₂ (staticCliqueGraph p.k) 0 (cliqueRestrict p a S) n` for `n ≤ p.T`.
- `perInterval_prob_lower` — per-interval consensus probability ≥ `1 − 2⁻ᵅ`;
  used in `LemmaAbsorption.lean` to fill `perInterval_absorption_prob`.
-/

@[expose] public section

noncomputable section

namespace TemporalGraph.VoterProcess.LowerBound

open MeasureTheory Finset
open scoped BigOperators

-- NeZero instance needed for staticCliqueGraph p.k
instance (p : Params) : NeZero p.k := ⟨p.hk_pos.ne'⟩

/-! ### Chapman–Kolmogorov (PMF level) -/

private theorem opinionProcess₂_compose
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraph V) (t n1 n2 : ℕ) (S : Finset V) :
    VoterModel.opinionProcess₂ G t (n1 + n2) S =
      (VoterModel.opinionProcess₂ G t n1 S).bind
        (fun T => VoterModel.opinionProcess₂ G (t + n1) n2 T) := by
  induction n2 with
  | zero =>
    simp only [add_zero]
    ext T
    simp [VoterModel.opinionProcess₂]
  | succ n2 ih =>
    show VoterModel.opinionProcess₂ G t (n1 + (n2 + 1)) S =
      (VoterModel.opinionProcess₂ G t n1 S).bind
        (fun T => VoterModel.opinionProcess₂ G (t + n1) (n2 + 1) T)
    have hlhs : VoterModel.opinionProcess₂ G t (n1 + (n2 + 1)) S =
        (VoterModel.opinionProcess₂ G t (n1 + n2) S).bind
          (VoterModel.stepDist₂ G (t + (n1 + n2))) := by
      rw [show n1 + (n2 + 1) = (n1 + n2) + 1 from by omega]; rfl
    rw [hlhs, ih, PMF.bind_bind]
    have : t + (n1 + n2) = (t + n1) + n2 := by omega
    simp_rw [this]
    rfl

/-! ### Clique vertex bijection -/

/-- The active K_{2k} clique for anchor `a`: union of blocks `a` and `a+1`. -/
def cliqueFinset (p : Params) (a : Fin p.z) : Finset (VertexSet p) :=
  block p a ∪ block p (a + 1)

/-- Map from `VertexSet p` to `CliqueVertex p.k`.
    Vertices in `block p a` map to indices `0..k-1`;
    vertices in `block p (a+1)` map to indices `k..2k-1`.
    The else-branch (non-clique vertices) is arbitrary; only use on `cliqueFinset p a`. -/
def toCliqueVtx (p : Params) (a : Fin p.z) (v : VertexSet p) : CliqueVertex p.k :=
  if v.1 = a then
    ⟨v.2.val, by have := v.2.isLt; omega⟩
  else
    -- arbitrary on non-clique; correct for v ∈ block p (a+1) since p.k + v.2.val < 2*p.k
    ⟨p.k + v.2.val, by have := v.2.isLt; omega⟩

/-- Restriction of state `S` to the clique `cliqueFinset p a`, transported to `CliqueVertex p.k`. -/
def cliqueRestrict (p : Params) (a : Fin p.z) (S : Finset (VertexSet p)) :
    Finset (CliqueVertex p.k) :=
  (S ∩ cliqueFinset p a).image (toCliqueVtx p a)

/-! ### Basic lemmas about `cliqueRestrict` -/

theorem toCliqueVtx_injOn (p : Params) (a : Fin p.z) :
    Set.InjOn (toCliqueVtx p a) (cliqueFinset p a) := by
  have hpz2 : 2 ≤ p.z := by obtain ⟨m, hm⟩ := p.hz_even; have := p.hz_pos; omega
  have ha1_ne_a : (a + 1 : Fin p.z) ≠ a := by
    intro h; have h1 := congr_arg Fin.val h; rw [Fin.val_add] at h1
    have halt := a.isLt
    have h1val : (1 : Fin p.z).val = 1 := by show 1 % p.z = 1; exact Nat.mod_eq_of_lt (by omega)
    rw [h1val] at h1
    by_cases hlt : a.val + 1 < p.z
    · rw [Nat.mod_eq_of_lt hlt] at h1; omega
    · rw [show a.val + 1 = p.z from by omega, Nat.mod_self] at h1; omega
  intro v₁ hv₁ v₂ hv₂ heq
  simp only [cliqueFinset, Finset.coe_union, Set.mem_union, Finset.mem_coe, mem_block] at hv₁ hv₂
  rcases hv₁ with h1a | h1b <;> rcases hv₂ with h2a | h2b
  · -- both in block a: toCliqueVtx = ⟨v.2.val, _⟩
    have e1 : toCliqueVtx p a v₁ = ⟨v₁.2.val, by have := v₁.2.isLt; omega⟩ := by
      simp [toCliqueVtx, h1a]
    have e2 : toCliqueVtx p a v₂ = ⟨v₂.2.val, by have := v₂.2.isLt; omega⟩ := by
      simp [toCliqueVtx, h2a]
    rw [e1, e2] at heq; simp only [Fin.ext_iff] at heq
    exact Prod.ext (h1a.trans h2a.symm) (Fin.val_injective heq)
  · -- v₁ in block a, v₂ in block (a+1): arithmetic contradiction
    have hne2 : v₂.1 ≠ a := by rw [h2b]; exact ha1_ne_a
    have e1 : toCliqueVtx p a v₁ = ⟨v₁.2.val, by have := v₁.2.isLt; omega⟩ := by
      simp [toCliqueVtx, h1a]
    have e2 : toCliqueVtx p a v₂ = ⟨p.k + v₂.2.val, by have := v₂.2.isLt; omega⟩ := by
      simp [toCliqueVtx, if_neg hne2]
    rw [e1, e2] at heq; simp only [Fin.ext_iff] at heq
    exact absurd heq (by have := v₁.2.isLt; omega)
  · -- v₁ in block (a+1), v₂ in block a: arithmetic contradiction
    have hne1 : v₁.1 ≠ a := by rw [h1b]; exact ha1_ne_a
    have e1 : toCliqueVtx p a v₁ = ⟨p.k + v₁.2.val, by have := v₁.2.isLt; omega⟩ := by
      simp [toCliqueVtx, if_neg hne1]
    have e2 : toCliqueVtx p a v₂ = ⟨v₂.2.val, by have := v₂.2.isLt; omega⟩ := by
      simp [toCliqueVtx, h2a]
    rw [e1, e2] at heq; simp only [Fin.ext_iff] at heq
    exact absurd heq (by have := v₂.2.isLt; omega)
  · -- both in block (a+1): toCliqueVtx = ⟨p.k + v.2.val, _⟩
    have hne1 : v₁.1 ≠ a := by rw [h1b]; exact ha1_ne_a
    have hne2 : v₂.1 ≠ a := by rw [h2b]; exact ha1_ne_a
    have e1 : toCliqueVtx p a v₁ = ⟨p.k + v₁.2.val, by have := v₁.2.isLt; omega⟩ := by
      simp [toCliqueVtx, if_neg hne1]
    have e2 : toCliqueVtx p a v₂ = ⟨p.k + v₂.2.val, by have := v₂.2.isLt; omega⟩ := by
      simp [toCliqueVtx, if_neg hne2]
    rw [e1, e2] at heq; simp only [Fin.ext_iff] at heq
    exact Prod.ext (h1b.trans h2b.symm) (Fin.val_injective (by omega))

theorem mem_cliqueRestrict_iff (p : Params) (a : Fin p.z)
    (S : Finset (VertexSet p)) (v : VertexSet p) (hv : v ∈ cliqueFinset p a) :
    toCliqueVtx p a v ∈ cliqueRestrict p a S ↔ v ∈ S := by
  simp only [cliqueRestrict, Finset.mem_image]
  constructor
  · rintro ⟨w, hw, heq⟩
    have hwC := (Finset.mem_inter.mp hw).2
    have hwS := (Finset.mem_inter.mp hw).1
    exact (toCliqueVtx_injOn p a hwC hv heq) ▸ hwS
  · intro hS
    exact ⟨v, Finset.mem_inter.mpr ⟨hS, hv⟩, rfl⟩

theorem cliqueRestrict_insert_mem (p : Params) (a : Fin p.z)
    (v : VertexSet p) (hv : v ∈ cliqueFinset p a) (S : Finset (VertexSet p)) :
    cliqueRestrict p a (insert v S) = insert (toCliqueVtx p a v) (cliqueRestrict p a S) := by
  simp only [cliqueRestrict, Finset.insert_inter_of_mem hv, Finset.image_insert]

theorem cliqueRestrict_insert_nmem (p : Params) (a : Fin p.z)
    (v : VertexSet p) (hv : v ∉ cliqueFinset p a) (S : Finset (VertexSet p)) :
    cliqueRestrict p a (insert v S) = cliqueRestrict p a S := by
  simp only [cliqueRestrict]; congr 1; ext w
  simp only [Finset.mem_inter, Finset.mem_insert]
  constructor
  · rintro ⟨h | h, hc⟩
    · exact absurd (h ▸ hc) hv
    · exact ⟨h, hc⟩
  · rintro ⟨h, hc⟩; exact ⟨Or.inr h, hc⟩

theorem cliqueRestrict_empty (p : Params) (a : Fin p.z) :
    cliqueRestrict p a ∅ = ∅ := by
  simp [cliqueRestrict]

theorem ha1_ne_aux (p : Params) (a : Fin p.z) : (a + 1 : Fin p.z) ≠ a := by
  have hpz2 : 2 ≤ p.z := by obtain ⟨m, hm⟩ := p.hz_even; have := p.hz_pos; omega
  intro h; have h1 := congr_arg Fin.val h; rw [Fin.val_add] at h1; have halt := a.isLt
  have h1val : (1 : Fin p.z).val = 1 := by show 1 % p.z = 1; exact Nat.mod_eq_of_lt (by omega)
  rw [h1val] at h1; by_cases hlt : a.val + 1 < p.z
  · rw [Nat.mod_eq_of_lt hlt] at h1; omega
  · rw [show a.val + 1 = p.z from by omega, Nat.mod_self] at h1; omega

theorem cliqueFinset_image_eq_univ (p : Params) (a : Fin p.z) :
    (cliqueFinset p a).image (toCliqueVtx p a) = Finset.univ := by
  have ha1_ne_a := ha1_ne_aux p a
  ext w; simp only [Finset.mem_image, Finset.mem_univ, iff_true, cliqueFinset]
  by_cases hw : w.val < p.k
  · exact ⟨(a, ⟨w.val, hw⟩), Finset.mem_union_left _ ((mem_block p a _).mpr rfl),
      by simp [toCliqueVtx]⟩
  · have hw2 : w.val - p.k < p.k := by have := w.isLt; omega
    exact ⟨(a + 1, ⟨w.val - p.k, hw2⟩),
      Finset.mem_union_right _ ((mem_block p (a + 1) _).mpr rfl),
      by simp only [toCliqueVtx, if_neg ha1_ne_a]; ext; simp; omega⟩

/-- The clique of `S` is `Finset.univ` iff the K_{2k} block is fully inside `S`,
    and `∅` iff the block is disjoint from `S`. -/
theorem cliqueFinset_consensus_iff (p : Params) (a : Fin p.z)
    (S : Finset (VertexSet p)) :
    (block p a ∪ block p (a + 1) ⊆ S ∨ Disjoint (block p a ∪ block p (a + 1)) S) ↔
    (cliqueRestrict p a S = Finset.univ ∨ cliqueRestrict p a S = ∅) := by
  constructor
  · intro h; rcases h with hfull | hempty
    · left
      show (S ∩ cliqueFinset p a).image (toCliqueVtx p a) = Finset.univ
      rw [show S ∩ cliqueFinset p a = cliqueFinset p a from Finset.inter_eq_right.mpr hfull]
      exact cliqueFinset_image_eq_univ p a
    · right
      show (S ∩ cliqueFinset p a).image (toCliqueVtx p a) = ∅
      rw [Finset.image_eq_empty]
      show S ∩ cliqueFinset p a = ∅
      rw [cliqueFinset, Finset.inter_comm]
      exact Finset.disjoint_iff_inter_eq_empty.mp hempty
  · intro h; rcases h with huniv | hempty
    · left
      intro v hv
      rw [← mem_cliqueRestrict_iff p a S v (by simp [cliqueFinset, hv]), huniv]
      exact Finset.mem_univ _
    · right
      rw [Finset.disjoint_left]; intro v hv hvS
      have hmem : toCliqueVtx p a v ∈ cliqueRestrict p a S :=
        (mem_cliqueRestrict_iff p a S v (by simp [cliqueFinset, hv])).mpr hvS
      simp [hempty] at hmem

/-- The sum over all `S' : Finset (VertexSet p)` satisfying the consensus condition
    equals the sum over `{∅, Finset.univ}` for the restricted PMF. -/
private theorem sum_consensus_eq_pmf_map_sum (p : Params) (a : Fin p.z)
    (μ : PMF (Finset (VertexSet p))) :
    ∑ S' ∈ Finset.univ.filter (fun S' : Finset (VertexSet p) =>
        block p a ∪ block p (a + 1) ⊆ S' ∨ Disjoint (block p a ∪ block p (a + 1)) S'),
      μ S' =
    (μ.map (cliqueRestrict p a)) Finset.univ + (μ.map (cliqueRestrict p a)) ∅ := by
  haveI : Nonempty (CliqueVertex p.k) := ⟨⟨0, by have := p.hk_pos; omega⟩⟩
  have hne : (Finset.univ : Finset (CliqueVertex p.k)) ≠ ∅ := Finset.univ_nonempty.ne_empty
  simp only [PMF.map_apply, tsum_fintype, ← Finset.sum_add_distrib, Finset.sum_filter]
  apply Finset.sum_congr rfl; intro S' _
  simp only [cliqueFinset_consensus_iff p a S', eq_comm (a := Finset.univ),
    eq_comm (a := (∅ : Finset (CliqueVertex p.k)))]
  by_cases h1 : cliqueRestrict p a S' = Finset.univ <;> by_cases h2 : cliqueRestrict p a S' = ∅ <;>
    [exact absurd (h1.symm.trans h2) hne; simp [h1, if_neg hne];
     simp [h2, if_neg (Ne.symm hne)]; simp [h1, h2]]

/-! ### Neighbor matching -/

/-- When `t` lies in interval `I_{j+1}` (i.e., `j·T ≤ t < (j+1)·T`) and
    `a.val % 2 = j % 2`, the neighbors of any `v ∈ cliqueFinset p a` in
    `lowerBoundGraph p` are exactly `cliqueFinset p a \ {v}`. -/
private theorem lowerBoundGraph_clique_neighborFinset (p : Params) (a : Fin p.z)
    (j t : ℕ) (ht_lo : j * p.T ≤ t) (ht_hi : t < (j + 1) * p.T)
    (ha : a.val % 2 = j % 2)
    (v : VertexSet p) (hv : v ∈ cliqueFinset p a) :
    TemporalGraph.neighborFinset (lowerBoundGraph p) t v = cliqueFinset p a \ {v} := by
  show TemporalGraph.neighborFinset (lowerBoundGraph p) t v =
    (block p a ∪ block p (a + 1)) \ {v}
  rw [← Finset.erase_eq]
  exact lowerBoundGraph_neighborFinset_clique p a j t ht_lo ht_hi ha v hv

/-! ### Distribution equality -/

/-- For a clique vertex `v` in interval `I_{j+1}`, the one-step opinion distribution in
    `lowerBoundGraph p` equals that in `staticCliqueGraph p.k` after applying `cliqueRestrict`. -/
theorem nextOpinionDist₂_clique_eq (p : Params) (a : Fin p.z)
    (j t : ℕ) (ht_lo : j * p.T ≤ t) (ht_hi : t < (j + 1) * p.T)
    (ha : a.val % 2 = j % 2)
    (S : Finset (VertexSet p)) (v : VertexSet p) (hv : v ∈ cliqueFinset p a) :
    VoterModel.nextOpinionDist₂ (lowerBoundGraph p) t S v =
    VoterModel.nextOpinionDist₂ (staticCliqueGraph p.k) 0
      (cliqueRestrict p a S) (toCliqueVtx p a v) := by
  -- The lower-bound graph's neighborFinset of v is cliqueFinset p a \ {v}.
  set N_lbg := TemporalGraph.neighborFinset (lowerBoundGraph p) t v with hN_lbg_def
  set N_clq := TemporalGraph.neighborFinset (staticCliqueGraph p.k) 0 (toCliqueVtx p a v)
    with hN_clq_def
  have hN_lbg_eq : N_lbg = cliqueFinset p a \ {v} :=
    lowerBoundGraph_clique_neighborFinset p a j t ht_lo ht_hi ha v hv
  have hN_clq_eq : N_clq = Finset.univ.erase (toCliqueVtx p a v) := by
    ext w
    simp [hN_clq_def, TemporalGraph.neighborFinset, staticCliqueGraph,
      SimpleGraph.top_adj, Finset.mem_erase]
    tauto
  -- Cardinalities
  have hcard_lbg : (cliqueFinset p a \ {v}).card = 2 * p.k - 1 := by
    rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hv]
    have hdisj : Disjoint (block p a) (block p (a + 1)) :=
      block_disjoint p (Ne.symm (ha1_ne_aux p a))
    rw [show cliqueFinset p a = block p a ∪ block p (a + 1) from rfl,
        Finset.card_union_of_disjoint hdisj, card_block, card_block]
    have hk := p.hk_pos
    omega
  have hcard_clq : (Finset.univ.erase (toCliqueVtx p a v)).card = 2 * p.k - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _)]
    simp [Fintype.card_fin]
  -- Nonemptiness
  have hk_pos := p.hk_pos
  have hN_lbg_ne : N_lbg.Nonempty := by
    rw [hN_lbg_eq]
    rw [← Finset.card_pos]; rw [hcard_lbg]; omega
  have hN_clq_ne : N_clq.Nonempty := by
    rw [hN_clq_eq]
    rw [← Finset.card_pos]; rw [hcard_clq]; omega
  -- Expand both sides
  rw [VoterModel.nextOpinionDist₂_eq_bind_of_nonempty (lowerBoundGraph p) t S v hN_lbg_ne]
  rw [VoterModel.nextOpinionDist₂_eq_bind_of_nonempty (staticCliqueGraph p.k) 0
      (cliqueRestrict p a S) (toCliqueVtx p a v) hN_clq_ne]
  congr 1
  funext b
  cases b
  · -- b = false: copy branch
    show (PMF.uniformOfFinset N_lbg hN_lbg_ne).map (fun w => decide (w ∈ S)) =
         (PMF.uniformOfFinset N_clq hN_clq_ne).map
          (fun w => decide (w ∈ cliqueRestrict p a S))
    classical
    -- Show the two map PMFs are equal
    apply PMF.ext
    intro b'
    rw [PMF.map_apply, PMF.map_apply]
    rw [tsum_fintype, tsum_fintype]
    -- Restrict each universal sum to the support of the uniform PMF
    have hLHS_sum :
        ∑ w : VertexSet p, (if b' = decide (w ∈ S)
          then (PMF.uniformOfFinset N_lbg hN_lbg_ne) w else 0) =
        ∑ w ∈ N_lbg, (if b' = decide (w ∈ S)
          then ((N_lbg.card : ENNReal))⁻¹ else 0) := by
      symm
      apply Finset.sum_subset_zero_on_sdiff (Finset.subset_univ _)
      · intro w hw
        rw [Finset.mem_sdiff] at hw
        split_ifs with hb
        · simp [PMF.uniformOfFinset_apply, hw.2]
        · rfl
      · intro w hw
        congr 1
        rw [PMF.uniformOfFinset_apply]
        simp [hw]
    have hRHS_sum :
        ∑ w : CliqueVertex p.k, (if b' = decide (w ∈ cliqueRestrict p a S)
          then (PMF.uniformOfFinset N_clq hN_clq_ne) w else 0) =
        ∑ w ∈ N_clq, (if b' = decide (w ∈ cliqueRestrict p a S)
          then ((N_clq.card : ENNReal))⁻¹ else 0) := by
      symm
      apply Finset.sum_subset_zero_on_sdiff (Finset.subset_univ _)
      · intro w hw
        rw [Finset.mem_sdiff] at hw
        split_ifs with hb
        · simp [PMF.uniformOfFinset_apply, hw.2]
        · rfl
      · intro w hw
        congr 1
        rw [PMF.uniformOfFinset_apply]
        simp [hw]
    -- Decidability instances differ between hLHS_sum and the goal.
    -- We bridge using convert with sufficient depth.
    convert hLHS_sum.trans (Eq.trans ?_ hRHS_sum.symm) using 5
    rw [show N_lbg.card = 2 * p.k - 1 from by rw [hN_lbg_eq]; exact hcard_lbg,
        show N_clq.card = 2 * p.k - 1 from by rw [hN_clq_eq]; exact hcard_clq]
    rw [hN_lbg_eq, hN_clq_eq]
    -- Now bijection via toCliqueVtx p a
    apply Finset.sum_bij (fun w _ => toCliqueVtx p a w)
    · -- maps_to
      intro w hw
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hw
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      intro heq
      exact hw.2 (toCliqueVtx_injOn p a hw.1 hv heq)
    · -- inj_on
      intros w₁ hw₁ w₂ hw₂ heq
      rw [Finset.mem_sdiff] at hw₁ hw₂
      exact toCliqueVtx_injOn p a hw₁.1 hw₂.1 heq
    · -- surj_on
      intro w' hw'
      rw [Finset.mem_erase] at hw'
      have himg : w' ∈ (cliqueFinset p a).image (toCliqueVtx p a) := by
        rw [cliqueFinset_image_eq_univ]; exact Finset.mem_univ _
      rw [Finset.mem_image] at himg
      obtain ⟨w, hw_mem, hw_eq⟩ := himg
      refine ⟨w, ?_, hw_eq⟩
      rw [Finset.mem_sdiff, Finset.mem_singleton]
      refine ⟨hw_mem, ?_⟩
      intro hwv
      subst hwv
      exact hw'.1 hw_eq.symm
    · -- value_eq
      intro w hw
      rw [Finset.mem_sdiff] at hw
      have : (w ∈ S) ↔ (toCliqueVtx p a w ∈ cliqueRestrict p a S) :=
        (mem_cliqueRestrict_iff p a S w hw.1).symm
      simp [this]
  · -- b = true: pure branch
    simp only [cond_true]
    congr 1
    -- decide (v ∈ S) = decide (toCliqueVtx p a v ∈ cliqueRestrict p a S)
    have := mem_cliqueRestrict_iff p a S v hv
    by_cases hvS : v ∈ S
    · simp [hvS, this.mpr hvS]
    · have hnot : toCliqueVtx p a v ∉ cliqueRestrict p a S := fun h => hvS (this.mp h)
      simp [hvS, hnot]

/-! ### PMF-level factorization -/

/-- `stepDist₂Aux` is invariant under list permutation.
    The swap case follows from PMF bind commutativity (independent samples). -/
private theorem stepDist₂Aux_perm
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraph V) (t : ℕ) (S : Finset V)
    {l₁ l₂ : List V} (h : List.Perm l₁ l₂) :
    VoterModel.stepDist₂Aux G t S l₁ = VoterModel.stepDist₂Aux G t S l₂ := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [VoterModel.stepDist₂Aux, ih]
  | swap u w l =>
    -- Two-step swap of independent updates: bind commutativity for PMF.
    simp only [VoterModel.stepDist₂Aux]
    rw [PMF.bind_bind, PMF.bind_bind]
    apply congr_arg ((VoterModel.stepDist₂Aux G t S l).bind)
    funext T
    -- Goal: ((next w).map cond_w_T).bind fun T1 => (next u).map cond_u_T1 =
    --       ((next u).map cond_u_T).bind fun T1 => (next w).map cond_w_T1
    rw [PMF.bind_map, PMF.bind_map]
    -- Both sides are bind-of-map; rewrite further to bind-of-bind:
    apply PMF.ext
    intro T'
    -- Compute LHS: ∑_b_w (next w b_w) * (∑_b_u (next u b_u) * indicator)
    -- Compute RHS: ∑_b_u (next u b_u) * (∑_b_w (next w b_w) * indicator')
    -- where indicator computes whether final T' matches the result
    have hLHS_form :
        ((VoterModel.nextOpinionDist₂ G t S w).bind
          (fun b_w : Bool =>
            (PMF.map (fun isZero : Bool => bif isZero then insert u (bif b_w then insert w T else T)
                                          else (bif b_w then insert w T else T))
              (VoterModel.nextOpinionDist₂ G t S u)))) T' =
        ∑ b_w : Bool, ∑ b_u : Bool,
          (VoterModel.nextOpinionDist₂ G t S w) b_w *
            (VoterModel.nextOpinionDist₂ G t S u) b_u *
            (if T' = (bif b_u then insert u (bif b_w then insert w T else T)
                              else (bif b_w then insert w T else T)) then 1 else 0) := by
      rw [PMF.bind_apply, tsum_fintype]
      apply Finset.sum_congr rfl; intro b_w _
      rw [PMF.map_apply, tsum_fintype]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro b_u _
      split_ifs with hT
      · simp
      · simp
    have hRHS_form :
        ((VoterModel.nextOpinionDist₂ G t S u).bind
          (fun b_u : Bool =>
            (PMF.map (fun isZero : Bool => bif isZero then insert w (bif b_u then insert u T else T)
                                          else (bif b_u then insert u T else T))
              (VoterModel.nextOpinionDist₂ G t S w)))) T' =
        ∑ b_u : Bool, ∑ b_w : Bool,
          (VoterModel.nextOpinionDist₂ G t S u) b_u *
            (VoterModel.nextOpinionDist₂ G t S w) b_w *
            (if T' = (bif b_w then insert w (bif b_u then insert u T else T)
                              else (bif b_u then insert u T else T)) then 1 else 0) := by
      rw [PMF.bind_apply, tsum_fintype]
      apply Finset.sum_congr rfl; intro b_u _
      rw [PMF.map_apply, tsum_fintype]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro b_w _
      split_ifs with hT
      · simp
      · simp
    simp only [Function.comp_def]
    -- The goal LHS is bind (next u) (insert w ...); the goal RHS is bind (next w) (insert u ...).
    -- hLHS_form expands bind (next w) (insert u ...), hRHS_form expands bind (next u) (insert w ...).
    -- So apply hRHS_form to goal's LHS, hLHS_form to goal's RHS.
    rw [hRHS_form, hLHS_form]
    -- After expansion, both sides are ∑_{b1, b2} ... with binders (b_u, b_w) and (b_w, b_u).
    -- swap one of them
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro b_w _
    apply Finset.sum_congr rfl; intro b_u _
    have hinsert_eq :
        (bif b_u then insert u (bif b_w then insert w T else T)
          else (bif b_w then insert w T else T)) =
        (bif b_w then insert w (bif b_u then insert u T else T)
          else (bif b_u then insert u T else T)) := by
      cases b_u <;> cases b_w <;> simp [Finset.insert_comm]
    rw [hinsert_eq]
    ring
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂


/-- Key auxiliary lemma: `stepDist₂Aux` factorization.
    For a list `vs` containing exactly the clique vertices (in some order) and possibly
    other (non-clique) vertices, the marginal `(stepDist₂Aux (lbg) t S vs).map cliqueRestrict`
    equals `stepDist₂Aux (clq) 0 (cliqueRestrict S) vs_clique_image`
    where `vs_clique_image = (vs.filter (·∈cliqueFinset)).map (toCliqueVtx)`.

    Strategy: induction on `vs`. For each prefix, the clique vertices contribute
    via a one-step bind through `nextOpinionDist₂_clique_eq`, while non-clique vertices
    leave `cliqueRestrict` unchanged.
-/
private theorem stepDist₂Aux_clique_marginal (p : Params) (a : Fin p.z)
    (j t : ℕ) (ht_lo : j * p.T ≤ t) (ht_hi : t < (j + 1) * p.T)
    (ha : a.val % 2 = j % 2)
    (S : Finset (VertexSet p)) (vs : List (VertexSet p)) :
    (VoterModel.stepDist₂Aux (lowerBoundGraph p) t S vs).map (cliqueRestrict p a) =
    VoterModel.stepDist₂Aux (staticCliqueGraph p.k) 0 (cliqueRestrict p a S)
      ((vs.filter (· ∈ cliqueFinset p a)).map (toCliqueVtx p a)) := by
  induction vs with
  | nil =>
    show PMF.map (cliqueRestrict p a) (PMF.pure ∅) = PMF.pure ∅
    rw [PMF.pure_map, cliqueRestrict_empty]
  | cons w ws ih =>
    by_cases hw : w ∈ cliqueFinset p a
    · -- w in clique
      have hfilter : ((w :: ws).filter (· ∈ cliqueFinset p a)) =
          w :: (ws.filter (· ∈ cliqueFinset p a)) := by
        simp [List.filter, hw]
      rw [hfilter]
      simp only [List.map_cons, VoterModel.stepDist₂Aux]
      -- LHS: ((stepDist₂Aux ws).bind fun T => (nextOpinionDist₂ w).map (cond b)).map cliqueRestrict
      -- = (stepDist₂Aux ws).bind fun T => ((nextOpinionDist₂ w).map (cond b)).map cliqueRestrict
      -- = (stepDist₂Aux ws).bind fun T => (nextOpinionDist₂ w).map (cliqueRestrict ∘ cond b)
      rw [PMF.map_bind]
      -- Goal: (stepDist₂Aux ws).bind (fun T => map cliqueRestrict (map (cond) (nextOpinionDist₂))) = ...
      simp only [PMF.map_comp]
      -- Now the RHS bind has cliqueRestrict ∘ cond
      -- Use ih to rewrite (stepDist₂Aux ws) in LHS via bind shape
      -- We want LHS to become: (stepDist₂Aux_static).bind (fun T' => map cliqueRestrict ...)
      -- Achieved by: rewriting (stepDist₂Aux ws).bind via PMF.bind_map combined with ih.
      rw [show (VoterModel.stepDist₂Aux (lowerBoundGraph p) t S ws).bind
            (fun T : Finset (VertexSet p) =>
              PMF.map ((cliqueRestrict p a) ∘ fun isZero : Bool => bif isZero then insert w T else T)
                (VoterModel.nextOpinionDist₂ (lowerBoundGraph p) t S w))
          = ((VoterModel.stepDist₂Aux (lowerBoundGraph p) t S ws).map (cliqueRestrict p a)).bind
            (fun T' : Finset (CliqueVertex p.k) =>
              PMF.map (fun isZero : Bool => bif isZero then insert (toCliqueVtx p a w) T' else T')
                (VoterModel.nextOpinionDist₂ (staticCliqueGraph p.k) 0 (cliqueRestrict p a S)
                  (toCliqueVtx p a w))) from ?_]
      · rw [ih]
      -- Subgoal: (∀ T) the integrand expressed via cliqueRestrict equals the static-clique form
      rw [PMF.bind_map]
      apply congr_arg ((VoterModel.stepDist₂Aux (lowerBoundGraph p) t S ws).bind)
      ext T
      simp only [Function.comp_def]
      -- Bridge via nextOpinionDist₂_clique_eq
      rw [nextOpinionDist₂_clique_eq p a j t ht_lo ht_hi ha S w hw]
      -- Both sides are (nextOpinionDist₂ (clq) ...).map (...)
      have hfun : (fun x : Bool => cliqueRestrict p a (bif x then insert w T else T)) =
          (fun isZero : Bool => bif isZero then insert (toCliqueVtx p a w) (cliqueRestrict p a T)
            else cliqueRestrict p a T) := by
        funext b
        cases b
        · rfl
        · show cliqueRestrict p a (insert w T) =
            insert (toCliqueVtx p a w) (cliqueRestrict p a T)
          exact cliqueRestrict_insert_mem p a w hw T
      rw [hfun]
    · -- w ∉ clique
      have hfilter : ((w :: ws).filter (· ∈ cliqueFinset p a)) =
          ws.filter (· ∈ cliqueFinset p a) := by
        simp [List.filter, hw]
      rw [hfilter]
      simp only [VoterModel.stepDist₂Aux]
      rw [PMF.map_bind]
      -- LHS: (stepDist₂Aux ws).bind (fun T => ((nextOpinionDist₂ w).map (cond)).map cliqueRestrict)
      -- The inner map of map: (cliqueRestrict ∘ cond) which on cond b T (insert w T) gives
      -- cliqueRestrict T or cliqueRestrict (insert w T) = cliqueRestrict T (since w ∉ clique)
      -- So inner = (nextOpinionDist₂ w).map (fun _ => cliqueRestrict T) = pure (cliqueRestrict T)
      simp only [PMF.map_comp]
      have hbind_const : ∀ T : Finset (VertexSet p),
          PMF.map ((cliqueRestrict p a) ∘ fun isZero : Bool => bif isZero then insert w T else T)
            (VoterModel.nextOpinionDist₂ (lowerBoundGraph p) t S w) =
          PMF.pure (cliqueRestrict p a T) := by
        intro T
        have hconst : (cliqueRestrict p a) ∘
            (fun isZero : Bool => bif isZero then insert w T else T) =
            fun _ : Bool => cliqueRestrict p a T := by
          funext b
          cases b
          · rfl
          · simp only [Function.comp_def, cond_true]
            exact cliqueRestrict_insert_nmem p a w hw T
        rw [hconst]
        exact PMF.map_const _ _
      simp_rw [hbind_const]
      -- LHS: (stepDist₂Aux ws).bind (fun T => pure (cliqueRestrict T))
      -- = (stepDist₂Aux ws).map cliqueRestrict
      -- = stepDist₂Aux (clq) 0 (cliqueRestrict S) ((ws.filter ...).map toCliqueVtx)  by ih
      show (VoterModel.stepDist₂Aux (lowerBoundGraph p) t S ws).bind
          (fun T => PMF.pure (cliqueRestrict p a T)) = _
      rw [show (VoterModel.stepDist₂Aux (lowerBoundGraph p) t S ws).bind
              (fun T => PMF.pure (cliqueRestrict p a T)) =
            (VoterModel.stepDist₂Aux (lowerBoundGraph p) t S ws).map (cliqueRestrict p a) from rfl]
      exact ih

/-- One-step factorization: `stepDist₂` of the lower-bound graph, marginalised to the clique,
    equals `stepDist₂` of the static clique applied to the restricted state. -/
theorem stepDist₂_clique_marginal (p : Params) (a : Fin p.z)
    (j t : ℕ) (ht_lo : j * p.T ≤ t) (ht_hi : t < (j + 1) * p.T)
    (ha : a.val % 2 = j % 2)
    (S : Finset (VertexSet p)) :
    (VoterModel.stepDist₂ (lowerBoundGraph p) t S).map (cliqueRestrict p a) =
    VoterModel.stepDist₂ (staticCliqueGraph p.k) 0 (cliqueRestrict p a S) := by
  rw [← VoterModel.stepDist₂Aux_eq_stepDist₂ (lowerBoundGraph p) t S,
      ← VoterModel.stepDist₂Aux_eq_stepDist₂ (staticCliqueGraph p.k) 0 (cliqueRestrict p a S)]
  rw [stepDist₂Aux_clique_marginal p a j t ht_lo ht_hi ha S Finset.univ.toList]
  -- The two lists ((univ.toList.filter ...).map toCliqueVtx) and univ.toList are both Nodup
  -- and have toFinset = univ. Use stepDist₂Aux_perm to conclude.
  apply stepDist₂Aux_perm
  have hfilter_nd : (Finset.univ.toList.filter (· ∈ cliqueFinset p a)).Nodup :=
    (Finset.univ.nodup_toList).filter _
  have hmap_nd : ((Finset.univ.toList.filter (· ∈ cliqueFinset p a)).map (toCliqueVtx p a)).Nodup := by
    apply List.Nodup.map_on _ hfilter_nd
    intro v hv w hw heq
    have hv' : v ∈ cliqueFinset p a := by
      have := List.of_mem_filter hv; simpa using this
    have hw' : w ∈ cliqueFinset p a := by
      have := List.of_mem_filter hw; simpa using this
    exact toCliqueVtx_injOn p a hv' hw' heq
  apply List.perm_of_nodup_nodup_toFinset_eq hmap_nd Finset.univ.nodup_toList
  -- toFinset equality: both equal univ over CliqueVertex p.k
  ext w; constructor
  · intro _; exact List.mem_toFinset.mpr (Finset.mem_toList.mpr (Finset.mem_univ _))
  · intro _
    rw [List.mem_toFinset, List.mem_map]
    have himg : w ∈ (cliqueFinset p a).image (toCliqueVtx p a) := by
      rw [cliqueFinset_image_eq_univ]; exact Finset.mem_univ _
    rw [Finset.mem_image] at himg
    obtain ⟨v, hv_mem, hv_eq⟩ := himg
    exact ⟨v, List.mem_filter.mpr ⟨List.mem_toFinset.mp (by simp), by simpa using hv_mem⟩, hv_eq⟩

/-- Multi-step factorization: for `n ≤ p.T` steps starting from `j·T`, the marginal of
    `opinionProcess₂ (lowerBoundGraph p)` on the clique equals
    `opinionProcess₂ (staticCliqueGraph p.k)` applied to the restricted initial state. -/
theorem opinionProcess₂_clique_marginal (p : Params) (a : Fin p.z)
    (j n : ℕ) (hn : n ≤ p.T) (ha : a.val % 2 = j % 2)
    (S : Finset (VertexSet p)) :
    (VoterModel.opinionProcess₂ (lowerBoundGraph p) (j * p.T) n S).map (cliqueRestrict p a) =
    VoterModel.opinionProcess₂ (staticCliqueGraph p.k) 0 n (cliqueRestrict p a S) := by
  induction n with
  | zero =>
    show PMF.map (cliqueRestrict p a) (PMF.pure S) = PMF.pure (cliqueRestrict p a S)
    rw [PMF.pure_map]
  | succ n ih =>
    have hn_lt : n < p.T := by omega
    have ih' := ih (by omega)
    show (VoterModel.opinionProcess₂ (lowerBoundGraph p) (j * p.T) (n + 1) S).map
            (cliqueRestrict p a) =
         VoterModel.opinionProcess₂ (staticCliqueGraph p.k) 0 (n + 1) (cliqueRestrict p a S)
    show ((VoterModel.opinionProcess₂ (lowerBoundGraph p) (j * p.T) n S).bind
            (VoterModel.stepDist₂ (lowerBoundGraph p) (j * p.T + n))).map (cliqueRestrict p a) =
         (VoterModel.opinionProcess₂ (staticCliqueGraph p.k) 0 n (cliqueRestrict p a S)).bind
            (VoterModel.stepDist₂ (staticCliqueGraph p.k) (0 + n))
    rw [PMF.map_bind, ← ih']
    rw [PMF.bind_map]
    apply congr_arg ((VoterModel.opinionProcess₂ (lowerBoundGraph p) (j * p.T) n S).bind)
    funext T
    simp only [Function.comp_def, zero_add]
    -- Need: stepDist₂_clique_marginal applied at time t = j*p.T + n
    have ht_lo : j * p.T ≤ j * p.T + n := Nat.le_add_right _ _
    have ht_hi : j * p.T + n < (j + 1) * p.T := by
      rw [Nat.succ_mul]; omega
    exact stepDist₂_clique_marginal p a j (j * p.T + n) ht_lo ht_hi ha T

/-- If the clique of anchor `a` is in consensus in `S` and `S'` is reachable from `S`
    in one interval under `lowerBoundGraph`, then the clique is in consensus in `S'`. -/
theorem opinionProcess₂_consensus_preserved (p : Params) (a : Fin p.z)
    (j : ℕ) (ha : a.val % 2 = j % 2)
    (S S' : Finset (VertexSet p))
    (hcons : block p a ∪ block p (a + 1) ⊆ S ∨ Disjoint (block p a ∪ block p (a + 1)) S)
    (hop : VoterModel.opinionProcess₂ (lowerBoundGraph p) (j * p.T) p.T S S' ≠ 0) :
    block p a ∪ block p (a + 1) ⊆ S' ∨ Disjoint (block p a ∪ block p (a + 1)) S' := by
  rw [cliqueFinset_consensus_iff] at hcons ⊢
  have hmarg := opinionProcess₂_clique_marginal p a j p.T (le_refl _) ha S
  -- S' reachable → its clique restriction has nonzero weight under the marginal map
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
    simp only at hle
    simp only [if_true] at hle; exact_mod_cast hle
  rw [hmarg] at hmap_ne
  rcases hcons with huniv | hempty
  · -- absorbing univ: after the interval the restriction is still univ
    rw [huniv, opinionProcess₂_univ_eq_pure, PMF.pure_apply] at hmap_ne
    left
    split_ifs at hmap_ne with h
    · exact h
    · exact absurd rfl hmap_ne
  · -- absorbing ∅: after the interval the restriction is still ∅
    rw [hempty, opinionProcess₂_empty_eq_pure, PMF.pure_apply] at hmap_ne
    right
    split_ifs at hmap_ne with h
    · exact h
    · exact absurd rfl hmap_ne

/-! ### PMF geometric bound for the static clique -/

/-- \label{lem:static-clique-voter}

Amplification part of `lem:static-clique-voter`: given the per-round `1/2` bound for
`Γ' * k` steps (`berenbrink_step_bound_pmf` supplies `Γ'` and this hypothesis), after
`α * Γ' * k` steps the static clique reaches consensus with probability at least
`1 − (1/2)^α`. -/
theorem geometric_boundary_bound_pmf_static
    (k : ℕ) [NeZero k] (Γ' : ℕ)
    (hstep : ∀ (t : ℕ) (T : Finset (CliqueVertex k)),
        (1 / 2 : ENNReal) ≤
          VoterModel.opinionProcess₂ (staticCliqueGraph k) t (Γ' * k) T Finset.univ +
          VoterModel.opinionProcess₂ (staticCliqueGraph k) t (Γ' * k) T ∅)
    (α : ℕ) (hα : 1 ≤ α) (T₀ : Finset (CliqueVertex k)) :
    ENNReal.ofReal (1 - (1 / 2 : ℝ) ^ α) ≤
      VoterModel.opinionProcess₂ (staticCliqueGraph k) 0 (α * Γ' * k) T₀ Finset.univ +
      VoterModel.opinionProcess₂ (staticCliqueGraph k) 0 (α * Γ' * k) T₀ ∅ := by
  set op := VoterModel.opinionProcess₂ (staticCliqueGraph k) with hopdef
  induction α with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n = 0
    · -- Base case: n = 0, so n + 1 = 1
      subst hn0
      simp only [zero_add, one_mul, pow_one]
      have h12 : ENNReal.ofReal (1 - 1 / 2 : ℝ) = 1 / 2 := by
        simp only [show (1:ℝ) - 1/2 = 2⁻¹ from by norm_num,
          ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 2)]
        norm_num
      rw [h12]
      exact hstep 0 T₀
    · have hn1 : 1 ≤ n := Nat.one_le_of_lt (Nat.pos_of_ne_zero hn0)
      have ih' := ih hn1
      -- Weights: p T = op 0 (n*Γ'*k) T₀ T
      let p : Finset (CliqueVertex k) → ENNReal := fun T => op 0 (n * Γ' * k) T₀ T
      let f : Finset (CliqueVertex k) → ENNReal :=
        fun T => op (n * Γ' * k) (Γ' * k) T Finset.univ + op (n * Γ' * k) (Γ' * k) T ∅
      have hf_half : ∀ T, (1 / 2 : ENNReal) ≤ f T := fun T => hstep (n * Γ' * k) T
      have hf_empty : f ∅ = 1 := by
        show op (n * Γ' * k) (Γ' * k) ∅ Finset.univ +
             op (n * Γ' * k) (Γ' * k) ∅ ∅ = 1
        show VoterModel.opinionProcess₂ (staticCliqueGraph k) (n * Γ' * k) (Γ' * k) ∅ Finset.univ +
             VoterModel.opinionProcess₂ (staticCliqueGraph k) (n * Γ' * k) (Γ' * k) ∅ ∅ = 1
        rw [opinionProcess₂_empty_eq_pure (staticCliqueGraph k) (n * Γ' * k) (Γ' * k)]
        simp [PMF.pure_apply, Finset.univ_nonempty.ne_empty]
      have hf_univ : f Finset.univ = 1 := by
        show op (n * Γ' * k) (Γ' * k) Finset.univ Finset.univ +
             op (n * Γ' * k) (Γ' * k) Finset.univ ∅ = 1
        show VoterModel.opinionProcess₂ (staticCliqueGraph k) (n * Γ' * k) (Γ' * k) Finset.univ
                Finset.univ +
             VoterModel.opinionProcess₂ (staticCliqueGraph k) (n * Γ' * k) (Γ' * k) Finset.univ ∅ = 1
        rw [opinionProcess₂_univ_eq_pure (staticCliqueGraph k) (n * Γ' * k) (Γ' * k)]
        simp [PMF.pure_apply, Finset.univ_nonempty.ne_empty.symm]
      -- Chapman-Kolmogorov via opinionProcess₂_compose
      have hCK : ∀ S', op 0 ((n + 1) * Γ' * k) T₀ S' =
          ∑ T, p T * op (n * Γ' * k) (Γ' * k) T S' := by
        intro S'
        show VoterModel.opinionProcess₂ (staticCliqueGraph k) 0 ((n + 1) * Γ' * k) T₀ S' =
          ∑ T, VoterModel.opinionProcess₂ (staticCliqueGraph k) 0 (n * Γ' * k) T₀ T *
            VoterModel.opinionProcess₂ (staticCliqueGraph k) (n * Γ' * k) (Γ' * k) T S'
        rw [show (n + 1) * Γ' * k = n * Γ' * k + Γ' * k from by ring]
        rw [opinionProcess₂_compose (staticCliqueGraph k) 0 (n * Γ' * k) (Γ' * k) T₀]
        simp [PMF.bind_apply, tsum_fintype, zero_add]
      have hQ_sum :
          op 0 ((n + 1) * Γ' * k) T₀ Finset.univ +
            op 0 ((n + 1) * Γ' * k) T₀ ∅ =
          ∑ T, p T * f T := by
        rw [hCK, hCK, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro T _
        rw [← mul_add]
      -- ∑ p T = 1: total mass of opinionProcess₂
      have hsum_p : ∑ T : Finset (CliqueVertex k), p T = 1 := by
        change ∑ T : Finset (CliqueVertex k),
          op 0 (n * Γ' * k) T₀ T = 1
        have := (op 0 (n * Γ' * k) T₀).tsum_coe
        rw [tsum_fintype] at this
        exact this
      have hf_split : ∀ T, f T = 1 / 2 + (f T - 1 / 2) :=
        fun T => (add_tsub_cancel_of_le (hf_half T)).symm
      have hsum_split :
          ∑ T, p T * f T = 1 / 2 + ∑ T, p T * (f T - 1 / 2) := by
        have hsplit : ∀ T ∈ Finset.univ, p T * f T =
            p T * (1 / 2) + p T * (f T - 1 / 2) := by
          intro T _; rw [← mul_add, ← hf_split T]
        rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
        congr 1
        simp_rw [mul_comm (p _) (1 / 2 : ENNReal)]
        rw [← Finset.mul_sum, hsum_p, mul_one]
      have hone_sub_half : (1 : ENNReal) - 1 / 2 = 1 / 2 :=
        (ENNReal.eq_sub_of_add_eq (by norm_num : (1/2 : ENNReal) ≠ ⊤)
          (ENNReal.add_halves 1)).symm
      have hf_empty_sub : f ∅ - 1 / 2 = 1 / 2 := by rw [hf_empty]; exact hone_sub_half
      have hf_univ_sub : f Finset.univ - 1 / 2 = 1 / 2 := by
        rw [hf_univ]; exact hone_sub_half
      have hne : (∅ : Finset (CliqueVertex k)) ≠ Finset.univ :=
        Finset.univ_nonempty.ne_empty.symm
      have hsum_lower :
          p ∅ * (1 / 2) + p Finset.univ * (1 / 2) ≤ ∑ T, p T * (f T - 1 / 2) := by
        calc p ∅ * (1 / 2) + p Finset.univ * (1 / 2)
            = p ∅ * (f ∅ - 1 / 2) + p Finset.univ * (f Finset.univ - 1 / 2) := by
                rw [hf_empty_sub, hf_univ_sub]
          _ = ∑ T ∈ ({∅, Finset.univ} : Finset (Finset (CliqueVertex k))),
                p T * (f T - 1 / 2) :=
                  (Finset.sum_pair (f := fun T => p T * (f T - 1 / 2)) hne).symm
          _ ≤ ∑ T, p T * (f T - 1 / 2) :=
                Finset.sum_le_univ_sum_of_nonneg (fun _ => zero_le)
      have hQn1_lower :
          1 / 2 + 1 / 2 * (p ∅ + p Finset.univ) ≤ ∑ T, p T * f T := by
        rw [hsum_split, mul_add, mul_comm (1 / 2 : ENNReal) (p ∅),
            mul_comm (1 / 2 : ENNReal) (p Finset.univ)]
        gcongr
      have h_half_pos : (0 : ℝ) ≤ 1 / 2 := by norm_num
      have h_tail_pos : (0 : ℝ) ≤ 1 / 2 * (1 - (1 / 2) ^ n) := by
        have h : (1/2:ℝ)^n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num); linarith
      have h12 : ENNReal.ofReal (1 / 2 : ℝ) = 1 / 2 := by
        simp only [show (1/2:ℝ) = 2⁻¹ from by norm_num,
          ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 2)]
        norm_num
      calc ENNReal.ofReal (1 - (1 / 2 : ℝ) ^ (n + 1))
          = ENNReal.ofReal (1 / 2 + 1 / 2 * (1 - (1 / 2 : ℝ) ^ n)) := by
              congr 1; ring
        _ = ENNReal.ofReal (1 / 2) +
              ENNReal.ofReal (1 / 2 * (1 - (1 / 2 : ℝ) ^ n)) :=
              ENNReal.ofReal_add h_half_pos h_tail_pos
        _ = ENNReal.ofReal (1 / 2) +
              ENNReal.ofReal (1 / 2) * ENNReal.ofReal (1 - (1 / 2 : ℝ) ^ n) := by
              rw [ENNReal.ofReal_mul h_half_pos]
        _ = 1 / 2 + 1 / 2 * ENNReal.ofReal (1 - (1 / 2 : ℝ) ^ n) := by rw [h12]
        _ ≤ 1 / 2 + 1 / 2 * (p ∅ + p Finset.univ) := by
              gcongr
              calc ENNReal.ofReal (1 - (1 / 2 : ℝ) ^ n)
                  ≤ p Finset.univ + p ∅ := ih'
                _ = p ∅ + p Finset.univ := add_comm _ _
        _ ≤ ∑ T, p T * f T := hQn1_lower
        _ = op 0 ((n + 1) * Γ' * k) T₀ Finset.univ +
              op 0 ((n + 1) * Γ' * k) T₀ ∅ := hQ_sum.symm

/-- Monotonicity: consensus probability for the static clique is non-decreasing in steps. -/
private theorem opinionProcess₂_consensus_sum_mono
    (k : ℕ) [NeZero k]
    (m n : ℕ) (hmn : m ≤ n) (T₀ : Finset (CliqueVertex k)) :
    VoterModel.opinionProcess₂ (staticCliqueGraph k) 0 m T₀ Finset.univ +
    VoterModel.opinionProcess₂ (staticCliqueGraph k) 0 m T₀ ∅ ≤
    VoterModel.opinionProcess₂ (staticCliqueGraph k) 0 n T₀ Finset.univ +
    VoterModel.opinionProcess₂ (staticCliqueGraph k) 0 n T₀ ∅ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  -- We need: op 0 m T₀ univ + op 0 m T₀ ∅ ≤ op 0 (m+d) T₀ univ + op 0 (m+d) T₀ ∅.
  -- Use opinionProcess₂_compose to expand the RHS:
  --   op 0 (m+d) T₀ X = ∑_T (op 0 m T₀ T) * (op m d T X).
  -- For X ∈ {univ, ∅}, the T = univ and T = ∅ contributions are exactly
  --   op 0 m T₀ univ * 1[X=univ] + op 0 m T₀ ∅ * 1[X=∅]
  -- (by opinionProcess₂_univ_eq_pure / opinionProcess₂_empty_eq_pure).
  -- Summing X over {univ, ∅} gives exactly LHS plus nonneg remainder.
  set op := VoterModel.opinionProcess₂ (staticCliqueGraph k) with hopdef
  have hCK : ∀ X, op 0 (m + d) T₀ X =
      ∑ T, op 0 m T₀ T * op m d T X := by
    intro X
    show VoterModel.opinionProcess₂ (staticCliqueGraph k) 0 (m + d) T₀ X =
      ∑ T, VoterModel.opinionProcess₂ (staticCliqueGraph k) 0 m T₀ T *
        VoterModel.opinionProcess₂ (staticCliqueGraph k) m d T X
    rw [opinionProcess₂_compose (staticCliqueGraph k) 0 m d T₀]
    simp [PMF.bind_apply, tsum_fintype, zero_add]
  -- Decompose the sum by separating T = univ and T = ∅
  have hne : (∅ : Finset (CliqueVertex k)) ≠ Finset.univ :=
    Finset.univ_nonempty.ne_empty.symm
  have hsubset : ({∅, Finset.univ} : Finset (Finset (CliqueVertex k))) ⊆ Finset.univ := by
    intro x _; exact Finset.mem_univ _
  -- For T = univ: op m d univ = pure univ, so op m d univ X = 1[X=univ]
  have hpure_univ : ∀ X, op m d Finset.univ X = if X = Finset.univ then 1 else 0 := by
    intro X
    show VoterModel.opinionProcess₂ (staticCliqueGraph k) m d Finset.univ X =
      if X = Finset.univ then 1 else 0
    rw [opinionProcess₂_univ_eq_pure (staticCliqueGraph k) m d, PMF.pure_apply]
    split_ifs with hX <;> simp
  have hpure_empty : ∀ X, op m d ∅ X = if X = ∅ then 1 else 0 := by
    intro X
    show VoterModel.opinionProcess₂ (staticCliqueGraph k) m d ∅ X =
      if X = ∅ then 1 else 0
    rw [opinionProcess₂_empty_eq_pure (staticCliqueGraph k) m d, PMF.pure_apply]
    split_ifs with hX <;> simp
  -- Now compute the lower bound
  have hsum_univ : ∑ T, op 0 m T₀ T * op m d T Finset.univ ≥
      op 0 m T₀ Finset.univ := by
    calc op 0 m T₀ Finset.univ
        = op 0 m T₀ Finset.univ * 1 := (mul_one _).symm
      _ = op 0 m T₀ Finset.univ * op m d Finset.univ Finset.univ := by
            rw [hpure_univ]; simp
      _ = ∑ T ∈ ({Finset.univ} : Finset (Finset (CliqueVertex k))),
            op 0 m T₀ T * op m d T Finset.univ := by
            rw [Finset.sum_singleton]
      _ ≤ ∑ T, op 0 m T₀ T * op m d T Finset.univ :=
          Finset.sum_le_univ_sum_of_nonneg (fun _ => zero_le)
  have hsum_empty : ∑ T, op 0 m T₀ T * op m d T ∅ ≥
      op 0 m T₀ ∅ := by
    calc op 0 m T₀ ∅
        = op 0 m T₀ ∅ * 1 := (mul_one _).symm
      _ = op 0 m T₀ ∅ * op m d ∅ ∅ := by
            rw [hpure_empty]; simp
      _ = ∑ T ∈ ({∅} : Finset (Finset (CliqueVertex k))),
            op 0 m T₀ T * op m d T ∅ := by
            rw [Finset.sum_singleton]
      _ ≤ ∑ T, op 0 m T₀ T * op m d T ∅ :=
          Finset.sum_le_univ_sum_of_nonneg (fun _ => zero_le)
  -- Combine
  show op 0 m T₀ Finset.univ + op 0 m T₀ ∅ ≤
       op 0 (m + d) T₀ Finset.univ + op 0 (m + d) T₀ ∅
  rw [hCK Finset.univ, hCK ∅]
  exact add_le_add hsum_univ hsum_empty

/-! ### Per-interval lower bound -/

/-- For any initial state `S` and anchor `a` with `a.val % 2 = j % 2`, the probability
    that the K_{2k} clique `block p a ∪ block p (a+1)` reaches consensus within the
    full interval `[j·T, (j+1)·T]` is at least `1 − (1/2)^α`. -/
theorem perInterval_prob_lower (p : Params) (a : Fin p.z) (j : ℕ)
    (ha : a.val % 2 = j % 2)
    (Γ : ℕ) (α : ℕ) (hα : 1 ≤ α) (hΓαT : Γ * α * p.k ≤ p.T)
    (hstep : ∀ (t : ℕ) (T : Finset (CliqueVertex p.k)),
        (1 / 2 : ENNReal) ≤
          VoterModel.opinionProcess₂ (staticCliqueGraph p.k) t (Γ * p.k) T Finset.univ +
          VoterModel.opinionProcess₂ (staticCliqueGraph p.k) t (Γ * p.k) T ∅)
    (S : Finset (VertexSet p)) :
    ENNReal.ofReal (1 - (1 / 2 : ℝ) ^ α) ≤
      ∑ S' ∈ Finset.univ.filter (fun S' : Finset (VertexSet p) =>
          block p a ∪ block p (a + 1) ⊆ S' ∨
          Disjoint (block p a ∪ block p (a + 1)) S'),
        VoterModel.opinionProcess₂ (lowerBoundGraph p) (j * p.T) p.T S S' := by
  -- Step 1: convert filter sum to PMF.map sum
  rw [sum_consensus_eq_pmf_map_sum p a (VoterModel.opinionProcess₂ (lowerBoundGraph p)
        (j * p.T) p.T S)]
  -- Step 2: rewrite PMF map at p.T via clique marginal (need n = p.T ≤ p.T)
  rw [opinionProcess₂_clique_marginal p a j p.T (le_refl _) ha S]
  -- Step 3: bound p.T by α * Γ * p.k via mono (consensus prob increases over time)
  have hk_pos : 1 ≤ p.k := p.hk_pos
  have hαΓk_le : α * Γ * p.k ≤ p.T := by rw [show α * Γ = Γ * α from Nat.mul_comm _ _]; exact hΓαT
  have hmono := opinionProcess₂_consensus_sum_mono p.k (α * Γ * p.k) p.T hαΓk_le
    (cliqueRestrict p a S)
  -- Step 4: apply geometric bound at α * Γ * p.k
  have hgeo := geometric_boundary_bound_pmf_static p.k Γ hstep α hα
    (cliqueRestrict p a S)
  -- Combine
  exact hgeo.trans hmono

end TemporalGraph.VoterProcess.LowerBound
