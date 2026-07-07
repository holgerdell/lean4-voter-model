module

public import LowerBound.Construction
import TemporalGraph.Regular
import TemporalGraph.Basic
import Mathlib.Algebra.Order.Star.Real
public import SimpleGraph.Conductance

/-! ## Lower bound on cumulative conductance for the clique construction

Formalizes {lem:clique-lower-bound-conductance} from §4.

## Main results

- `clique_lower_bound_conductance`: for any subset `S` with `|S| ≤ n/2`,
  the cumulative conductance over a window of length `3T` is at least `T/(4z)`.
-/

@[expose] public section

open Finset
open scoped BigOperators

noncomputable section

namespace TemporalGraph.VoterProcess.LowerBound

/-! ### Case 1: every block has at most k/2 vertices in S -/

/-- The two consecutive blocks `block p a` and `block p (a+1)` are distinct.
This re-derives the cyclic argument from `snapshot_degree` for a public name. -/
private lemma block_succ_ne_aux (p : Params) (a : Fin p.z) : a ≠ a + 1 := by
  intro h
  have hz2 : 2 ≤ p.z := p.hz_two_le
  have hval : ((a.val + 1) % p.z) = a.val := by
    simpa [Fin.val_add] using congrArg Fin.val h.symm
  by_cases hlt : a.val + 1 < p.z
  · have : a.val + 1 = a.val := by
      simp [Nat.mod_eq_of_lt hlt] at hval
    omega
  · have hz_eq : a.val + 1 = p.z := by omega
    have hzero : (a.val + 1) % p.z = 0 := by simp [hz_eq]
    have ha0 : a.val = 0 := by
      rw [hzero] at hval
      exact hval.symm
    omega

/-- Forward direction of `activeAnchor_eq_iff_eq_or_succ`, but stated without
relying on the private parity hypothesis: if `activeAnchor p odd i = a` then
either `i = a` or `i = a + 1` (in `Fin p.z`).

Re-derived locally because the original lemma is private to `Defs.lean`. -/
private lemma activeAnchor_imp_eq_or_succ
    (p : Params) (odd : Bool) (i a : Fin p.z)
    (h : activeAnchor p odd i = a) :
    i = a ∨ i = a + 1 := by
  unfold activeAnchor at h
  by_cases hi : i.val % 2 = (cond odd 1 0 : ℕ)
  · -- `parityNat odd = cond odd 1 0`; `activeAnchor` returns `i`, so `i = a`.
    left
    cases odd
    · -- odd = false
      simp at hi
      simpa [hi, parityNat] using h
    · -- odd = true
      simp at hi
      simpa [hi, parityNat] using h
  · right
    cases odd
    · -- odd = false
      simp at hi
      have h' : i + (-1) = a := by simpa [hi, parityNat] using h
      rw [← h']; simp [add_assoc]
    · -- odd = true
      simp at hi
      have h' : i + (-1) = a := by simpa [hi, parityNat] using h
      rw [← h']; simp [add_assoc]

/-- Generic snapshot bound: for each vertex `u ∈ S`, the number of `S`-neighbours
of `u` in a snapshot with parity `odd` is at most `p.k - 1`. The conclusion is
stated using `Classical.decPred` to be independent of the snapshot's particular
`DecidableRel`.

We state it as a bound on the cardinality of `{w ∈ S : ActiveAnchor agreement
between u and w}` because that is what we actually use. -/
private lemma snapshot_filter_card_le
    (p : Params) (odd : Bool)
    (S : Finset (VertexSet p))
    (hcase1 : ∀ x : Fin p.z, 2 * (S.filter (fun v => v.1 = x)).card ≤ p.k)
    {u : VertexSet p} (huS : u ∈ S) :
    (S.filter (fun w =>
        u ≠ w ∧ activeAnchor p odd u.1 = activeAnchor p odd w.1)).card ≤
      p.k - 1 := by
  classical
  let a : Fin p.z := activeAnchor p odd u.1
  have ha_ne : a ≠ a + 1 := block_succ_ne_aux p a
  -- `activeAnchor p odd u.1 = a` is reflexive (definitional).
  have hu_self : activeAnchor p odd u.1 = a := rfl
  -- Step 1: `S.filter (...) ⊆ (S ∩ (block p a ∪ block p (a+1))).erase u`
  have hsubset :
      S.filter (fun w =>
          u ≠ w ∧ activeAnchor p odd u.1 = activeAnchor p odd w.1) ⊆
        (S ∩ (block p a ∪ block p (a + 1))).erase u := by
    intro w hw
    rcases Finset.mem_filter.mp hw with ⟨hwS, h1, h2⟩
    have hwa : activeAnchor p odd w.1 = a := h2.symm
    have hw_or : w.1 = a ∨ w.1 = a + 1 :=
      activeAnchor_imp_eq_or_succ p odd w.1 a hwa
    refine Finset.mem_erase.mpr ⟨h1.symm, Finset.mem_inter.mpr ⟨hwS, ?_⟩⟩
    rw [Finset.mem_union, mem_block, mem_block]
    exact hw_or
  -- Step 2: bound the cardinality of `S ∩ (block p a ∪ block p (a+1))`
  have hdisj : Disjoint (S ∩ block p a) (S ∩ block p (a + 1)) := by
    apply Finset.disjoint_left.mpr
    intro w hw1 hw2
    have hwa : w.1 = a := (mem_block p a w).mp (Finset.mem_inter.mp hw1).2
    have hwa1 : w.1 = a + 1 := (mem_block p (a + 1) w).mp (Finset.mem_inter.mp hw2).2
    exact ha_ne (hwa.symm.trans hwa1)
  have hSa_eq : S ∩ block p a = S.filter (fun v => v.1 = a) := by
    ext w; simp [Finset.mem_inter, mem_block, Finset.mem_filter]
  have hSa1_eq : S ∩ block p (a + 1) = S.filter (fun v => v.1 = a + 1) := by
    ext w; simp [Finset.mem_inter, mem_block, Finset.mem_filter]
  have hSa_card : 2 * (S ∩ block p a).card ≤ p.k := by
    rw [hSa_eq]; exact hcase1 a
  have hSa1_card : 2 * (S ∩ block p (a + 1)).card ≤ p.k := by
    rw [hSa1_eq]; exact hcase1 (a + 1)
  have hcard_inter :
      (S ∩ (block p a ∪ block p (a + 1))).card =
        (S ∩ block p a).card + (S ∩ block p (a + 1)).card := by
    rw [Finset.inter_union_distrib_left, Finset.card_union_of_disjoint hdisj]
  have hcard_le : (S ∩ (block p a ∪ block p (a + 1))).card ≤ p.k := by
    rw [hcard_inter]; omega
  -- Step 3: `u ∈ S ∩ (block p a ∪ block p (a+1))`
  have hu_pair : u.1 = a ∨ u.1 = a + 1 :=
    activeAnchor_imp_eq_or_succ p odd u.1 a hu_self
  have hu_mem_union : u ∈ block p a ∪ block p (a + 1) := by
    rw [Finset.mem_union, mem_block, mem_block]; exact hu_pair
  have hu_mem_inter : u ∈ S ∩ (block p a ∪ block p (a + 1)) :=
    Finset.mem_inter.mpr ⟨huS, hu_mem_union⟩
  -- Step 4: combine
  have hcard_filter_le :
      (S.filter (fun w =>
          u ≠ w ∧ activeAnchor p odd u.1 = activeAnchor p odd w.1)).card ≤
        ((S ∩ (block p a ∪ block p (a + 1))).erase u).card :=
    Finset.card_le_card hsubset
  rw [Finset.card_erase_of_mem hu_mem_inter] at hcard_filter_le
  have hpos : 1 ≤ (S ∩ (block p a ∪ block p (a + 1))).card :=
    Finset.card_pos.mpr ⟨u, hu_mem_inter⟩
  omega

/-- In Case 1, when every block has `|S ∩ V_x| ≤ k/2`, each snapshot partitions `V`
into `z/2` cliques of size `2k`, each with `|S ∩ clique| ≤ k`.
By `static_clique_conductance`, every clique contributes conductance `≥ 1/2`,
so the overall conductance at any time `t` is `≥ 1/2`. -/
lemma case1_conductance_ge_half
    (p : Params) (hk : 1 ≤ p.k) (t : ℕ)
    (S : Finset (VertexSet p))
    (hS_nonempty : S.Nonempty)
    (hcase1 : ∀ x : Fin p.z, 2 * (S.filter (fun v => v.1 = x)).card ≤ p.k) :
    (1 / 2 : ℝ) ≤ ((lowerBoundGraph p).snapshot t).setConductance S := by
  classical
  -- Step A: volume of `S` is `|S| * (2k - 1)`.
  have hvol_nat :
      TemporalGraph.volume (lowerBoundGraph p) t S = S.card * (2 * p.k - 1) := by
    have hreg :
        ∀ u v : VertexSet p,
          TemporalGraph.deg (lowerBoundGraph p) u =
            TemporalGraph.deg (lowerBoundGraph p) v := by
      intro u v
      simp [TemporalGraph.deg, lowerBoundGraph_degree]
    have hne : Nonempty (VertexSet p) := inferInstance
    calc TemporalGraph.volume (lowerBoundGraph p) t S
        = TemporalGraph.volume (lowerBoundGraph p) 0 S :=
            TemporalGraph.volume_fixed (lowerBoundGraph p)
              (lowerBoundGraph_fixedDegrees p) S t 0
      _ = S.card * TemporalGraph.deg (lowerBoundGraph p)
            (Classical.choice hne) :=
            TemporalGraph.volume_eq_card_mul_deg_of_regular
              (lowerBoundGraph p) hreg S
      _ = S.card * (2 * p.k - 1) := by
            congr 1
            simp [TemporalGraph.deg, lowerBoundGraph_degree]
  -- Auxiliary: characterize the adjacency at time `t` in terms of `activeAnchor` for some `odd`.
  obtain ⟨odd, hAdj⟩ : ∃ odd : Bool, ∀ u w : VertexSet p,
      ((lowerBoundGraph p).snapshot t).Adj u w ↔
        u ≠ w ∧ activeAnchor p odd u.1 = activeAnchor p odd w.1 := by
    by_cases hpar : intervalIndex p t % 2 = 0
    · refine ⟨true, ?_⟩
      intro u w
      have hg : (lowerBoundGraph p).snapshot t = snapshot0 p := by
        simp [lowerBoundGraph, hpar]
      rw [hg]
      rfl
    · refine ⟨false, ?_⟩
      intro u w
      have hg : (lowerBoundGraph p).snapshot t = snapshot1 p := by
        simp [lowerBoundGraph, hpar]
      rw [hg]
      rfl
  -- Step B: per-vertex `degreeIn (univ \ S)` lower bound by `p.k`.
  -- Express `degreeIn u N` of `lowerBoundGraph` via classical decidability so we can
  -- rewrite using `hAdj`.
  classical
  have hdegIn_classical :
      ∀ (N : Finset (VertexSet p)) (u : VertexSet p),
        TemporalGraph.degreeIn (lowerBoundGraph p) t u N =
          (N.filter
            (fun w => u ≠ w ∧ activeAnchor p odd u.1 = activeAnchor p odd w.1)).card := by
    intro N u
    -- Both sides equal `(N.filter (((lowerBoundGraph p).snapshot t).Adj u)).card` and
    -- the filter on RHS is just a re-expression of that under `hAdj`.
    show ((N).filter (fun w => ((lowerBoundGraph p).snapshot t).Adj u w)).card = _
    -- Use `Finset.card_congr` via filter equality (with classical decidability).
    have hfilter_eq :
        (N.filter (fun w => ((lowerBoundGraph p).snapshot t).Adj u w) : Finset _) =
          N.filter
            (fun w => u ≠ w ∧ activeAnchor p odd u.1 = activeAnchor p odd w.1) := by
      apply Finset.filter_congr
      intro w _
      exact hAdj u w
    rw [hfilter_eq]
  have hper_vertex :
      ∀ u ∈ S,
        p.k ≤ TemporalGraph.degreeIn (lowerBoundGraph p) t u (Finset.univ \ S) := by
    intro u huS
    have hdeg : TemporalGraph.degree (lowerBoundGraph p) t u = 2 * p.k - 1 :=
      lowerBoundGraph_degree p t u
    have hdisj : Disjoint S (Finset.univ \ S) := Finset.disjoint_sdiff
    -- Express `degree u = (Finset.univ.filter ...)` in classical form.
    have hdeg_classical :
        TemporalGraph.degree (lowerBoundGraph p) t u =
          (Finset.univ.filter
            (fun w => u ≠ w ∧ activeAnchor p odd u.1 = activeAnchor p odd w.1)).card := by
      have h1 : TemporalGraph.degree (lowerBoundGraph p) t u =
                  (Finset.univ.filter
                    (fun w => ((lowerBoundGraph p).snapshot t).Adj u w)).card := by
        show ((lowerBoundGraph p).snapshot t).degree u = _
        rw [SimpleGraph.degree]
        congr 1
        ext w
        simp [SimpleGraph.mem_neighborFinset]
      rw [h1]
      congr 1
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hAdj u w
    -- Now split `Finset.univ = S ∪ (univ \ S)` via cardinality.
    have hcard_univ_split :
        (Finset.univ.filter
          (fun w => u ≠ w ∧ activeAnchor p odd u.1 = activeAnchor p odd w.1)).card =
          (S.filter
            (fun w => u ≠ w ∧ activeAnchor p odd u.1 = activeAnchor p odd w.1)).card +
          ((Finset.univ \ S).filter
            (fun w => u ≠ w ∧ activeAnchor p odd u.1 = activeAnchor p odd w.1)).card := by
      have hfilter_union :
          Finset.univ.filter
              (fun w => u ≠ w ∧ activeAnchor p odd u.1 = activeAnchor p odd w.1) =
            S.filter
                (fun w => u ≠ w ∧ activeAnchor p odd u.1 = activeAnchor p odd w.1) ∪
              (Finset.univ \ S).filter
                (fun w => u ≠ w ∧ activeAnchor p odd u.1 = activeAnchor p odd w.1) := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, Finset.mem_sdiff,
          true_and]
        constructor
        · intro ⟨hne, heq⟩
          by_cases hwS : w ∈ S
          · exact Or.inl ⟨hwS, hne, heq⟩
          · exact Or.inr ⟨hwS, hne, heq⟩
        · rintro (⟨_, hne, heq⟩ | ⟨_, hne, heq⟩)
          · exact ⟨hne, heq⟩
          · exact ⟨hne, heq⟩
      rw [hfilter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj)]
    have hin_le :
        (S.filter (fun w =>
          u ≠ w ∧ activeAnchor p odd u.1 = activeAnchor p odd w.1)).card ≤ p.k - 1 :=
      snapshot_filter_card_le p odd S hcase1 huS
    rw [hdegIn_classical (Finset.univ \ S) u]
    have htotal : 2 * p.k - 1 =
        (S.filter (fun w =>
          u ≠ w ∧ activeAnchor p odd u.1 = activeAnchor p odd w.1)).card +
        ((Finset.univ \ S).filter (fun w =>
          u ≠ w ∧ activeAnchor p odd u.1 = activeAnchor p odd w.1)).card := by
      rw [← hdeg, hdeg_classical, hcard_univ_split]
    omega
  -- Step C: edgesBetween decomposes as a sum of degreeIn over `S`.
  have hcut_sum :
      TemporalGraph.edgesBetween (lowerBoundGraph p) t S (Finset.univ \ S) =
        ∑ u ∈ S, TemporalGraph.degreeIn (lowerBoundGraph p) t u (Finset.univ \ S) := by
    show ((S ×ˢ (Finset.univ \ S)).filter
            (fun p' => ((lowerBoundGraph p).snapshot t).Adj p'.1 p'.2)).card =
          ∑ u ∈ S, ((Finset.univ \ S).filter
            (fun w => ((lowerBoundGraph p).snapshot t).Adj u w)).card
    simp only [Finset.card_filter]
    exact Finset.sum_product' S (Finset.univ \ S)
      (fun u v => if ((lowerBoundGraph p).snapshot t).Adj u v then 1 else 0)
  -- Step D: edgesBetween ≥ |S| * p.k.
  have hcut_ge : S.card * p.k ≤
      TemporalGraph.edgesBetween (lowerBoundGraph p) t S (Finset.univ \ S) := by
    rw [hcut_sum]
    calc S.card * p.k = ∑ _u ∈ S, p.k := by
            rw [Finset.sum_const]; ring
      _ ≤ ∑ u ∈ S, TemporalGraph.degreeIn (lowerBoundGraph p) t u (Finset.univ \ S) :=
            Finset.sum_le_sum hper_vertex
  -- Step E: assemble the final ratio.
  unfold SimpleGraph.setConductance
  rw [show ((lowerBoundGraph p).snapshot t).volume S = S.card * (2 * p.k - 1) from hvol_nat]
  have hScard_pos : 0 < S.card := Finset.card_pos.mpr hS_nonempty
  have h2k1_pos : 0 < 2 * p.k - 1 := by omega
  have hden_pos_nat : 0 < S.card * (2 * p.k - 1) := Nat.mul_pos hScard_pos h2k1_pos
  have hden_pos : (0 : ℝ) < ((S.card * (2 * p.k - 1) : ℕ) : ℝ) := by
    exact_mod_cast hden_pos_nat
  refine (le_div_iff₀ hden_pos).2 ?_
  -- We need: (S.card * (2 * p.k - 1)) * (1 / 2) ≤ edgesBetween
  -- It suffices to show: S.card * (2 * p.k - 1) ≤ 2 * edgesBetween.
  have hineq_nat :
      S.card * (2 * p.k - 1) ≤ 2 * (S.card * p.k) := by
    have hle : 2 * p.k - 1 ≤ 2 * p.k := by omega
    calc S.card * (2 * p.k - 1) ≤ S.card * (2 * p.k) := Nat.mul_le_mul_left _ hle
      _ = 2 * (S.card * p.k) := by ring
  have h1 : ((S.card * (2 * p.k - 1) : ℕ) : ℝ) ≤
            ((2 * (S.card * p.k) : ℕ) : ℝ) := by exact_mod_cast hineq_nat
  have h2 : ((S.card * p.k : ℕ) : ℝ) ≤
            ((TemporalGraph.edgesBetween (lowerBoundGraph p) t S (Finset.univ \ S) : ℕ) : ℝ) := by
    exact_mod_cast hcut_ge
  have hpush : ((2 * (S.card * p.k) : ℕ) : ℝ) = 2 * ((S.card * p.k : ℕ) : ℝ) := by
    push_cast; ring
  rw [hpush] at h1
  linarith

/-! ### Case 2: some block has more than k/2 vertices in S -/

/-- Partition identity: `S.card = ∑ i : Fin p.z, |S.filter (·.1 = i)|`.
The fibers of `Prod.fst` over a vertex set partition `S`. -/
private lemma sum_filter_fst_card_eq_card
    (p : Params) (S : Finset (VertexSet p)) :
    ∑ i : Fin p.z, (S.filter (fun v => v.1 = i)).card = S.card := by
  classical
  exact (Finset.card_eq_sum_card_fiberwise
      (f := fun v : VertexSet p => v.1) (s := S) (t := Finset.univ)
      (fun a _ => Finset.mem_univ _)).symm

/-- Pigeonhole + cyclic IVT: in Case 2, there exists ℓ : Fin p.z with
`2 * |S ∩ V_ℓ| ≤ p.k < 2 * |S ∩ V_{ℓ+1}|`. -/
lemma case2_pigeonhole
    (p : Params) (S : Finset (VertexSet p))
    (hS_card_le : 2 * S.card ≤ Fintype.card (VertexSet p))
    (hcase2 : ∃ x : Fin p.z, p.k < 2 * (S.filter (fun v => v.1 = x)).card) :
    ∃ ℓ : Fin p.z,
      2 * (S.filter (fun v => v.1 = ℓ)).card ≤ p.k ∧
      p.k < 2 * (S.filter (fun v => v.1 = ℓ + 1)).card := by
  classical
  -- Step 1: find a "light" block y₀ with 2 * |S ∩ V_{y₀}| ≤ p.k.
  have hcard_eq : ∑ i : Fin p.z, (S.filter (fun v => v.1 = i)).card = S.card :=
    sum_filter_fst_card_eq_card p S
  have hSV : Fintype.card (VertexSet p) = p.k * p.z := card_vertexSet p
  have hexists_light :
      ∃ y : Fin p.z, 2 * (S.filter (fun v => v.1 = y)).card ≤ p.k := by
    by_contra hall
    push Not at hall
    -- All blocks heavy: ∀ i, p.k < 2 * |S ∩ V_i|, so ∀ i, p.k + 1 ≤ 2 * |S ∩ V_i|.
    have hallk : ∀ i : Fin p.z, p.k + 1 ≤ 2 * (S.filter (fun v => v.1 = i)).card :=
      fun i => Nat.succ_le_of_lt (hall i)
    have hsum_lower :
        ∑ i : Fin p.z, (p.k + 1) ≤
          ∑ i : Fin p.z, 2 * (S.filter (fun v => v.1 = i)).card :=
      Finset.sum_le_sum (fun i _ => hallk i)
    have hsum_left : ∑ _i : Fin p.z, (p.k + 1) = (p.k + 1) * p.z := by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, mul_comm]
    have hsum_right :
        ∑ i : Fin p.z, 2 * (S.filter (fun v => v.1 = i)).card =
          2 * S.card := by
      rw [← Finset.mul_sum, hcard_eq]
    rw [hsum_left, hsum_right] at hsum_lower
    -- (p.k + 1) * p.z ≤ 2 * S.card ≤ p.k * p.z, contradiction.
    have : (p.k + 1) * p.z ≤ p.k * p.z := by
      calc (p.k + 1) * p.z ≤ 2 * S.card := hsum_lower
        _ ≤ Fintype.card (VertexSet p) := hS_card_le
        _ = p.k * p.z := hSV
    have hz_pos : 0 < p.z := p.hz_pos
    nlinarith
  obtain ⟨y₀, hy₀⟩ := hexists_light
  obtain ⟨x₀, hx₀⟩ := hcase2
  -- Step 2: cyclic IVT.
  -- Define T_light : Finset (Fin p.z) and orbit-induct.
  let T_light : Finset (Fin p.z) :=
    Finset.univ.filter (fun i => 2 * (S.filter (fun v => v.1 = i)).card ≤ p.k)
  -- We need: ∃ ℓ ∈ T_light with (ℓ + 1) ∉ T_light.
  by_contra hno
  push Not at hno
  -- hno : ∀ ℓ, 2 * |S ∩ V_ℓ| ≤ p.k → ¬ (p.k < 2 * |S ∩ V_{ℓ+1}|)
  -- i.e., ∀ ℓ ∈ T_light, ℓ + 1 ∈ T_light.
  have hclosed : ∀ ℓ : Fin p.z,
      2 * (S.filter (fun v => v.1 = ℓ)).card ≤ p.k →
      2 * (S.filter (fun v => v.1 = ℓ + 1)).card ≤ p.k := by
    intro ℓ hℓ
    have := hno ℓ hℓ
    omega
  -- Orbit: define iteration via `Fin.ofNat p.z n`. T_light is closed under step,
  -- so iterating from y₀ gives all of Fin p.z, contradicting x₀ ∉ T_light.
  have horbit : ∀ n : ℕ,
      2 * (S.filter (fun v => v.1 = y₀ + Fin.ofNat p.z n)).card ≤ p.k := by
    intro n
    induction n with
    | zero =>
      have h0 : (Fin.ofNat p.z 0) = (0 : Fin p.z) := rfl
      rw [h0, add_zero]
      exact hy₀
    | succ n ih =>
      have hstep := hclosed (y₀ + Fin.ofNat p.z n) ih
      have hcast : (Fin.ofNat p.z (n + 1) : Fin p.z) = Fin.ofNat p.z n + 1 := by
        apply Fin.ext
        simp only [Fin.ofNat, Fin.val_add, Fin.val_one']
        rw [Nat.add_mod]
      rw [hcast, ← add_assoc]
      exact hstep
  -- Specialize at n = (x₀ - y₀).val to derive contradiction.
  have hcast_eq : Fin.ofNat p.z (x₀ - y₀).val = x₀ - y₀ := by
    apply Fin.ext
    simp only [Fin.ofNat]
    exact Nat.mod_eq_of_lt (x₀ - y₀).isLt
  have hx0_orbit : y₀ + Fin.ofNat p.z (x₀ - y₀).val = x₀ := by
    rw [hcast_eq]
    -- y₀ + (x₀ - y₀) = x₀ in Fin p.z (additive group)
    have : y₀ + (x₀ - y₀) = x₀ := by
      rw [add_comm]; exact sub_add_cancel x₀ y₀
    exact this
  have hxlight : 2 * (S.filter (fun v => v.1 = x₀)).card ≤ p.k := by
    have h := horbit (x₀ - y₀).val
    rw [hx0_orbit] at h
    exact h
  omega

/-- For `t` in the sub-interval `Icc ((m-1)*p.T) (m*p.T - 1)` (with `m ≥ 1`),
the interval index equals `m`. -/
private lemma intervalIndex_of_mem
    (p : Params) (m t : ℕ) (hm : 1 ≤ m)
    (h₁ : (m - 1) * p.T ≤ t) (h₂ : t ≤ m * p.T - 1) :
    intervalIndex p t = m := by
  unfold intervalIndex
  have hT_pos : 0 < p.T := p.hT_pos
  have hlt : t < m * p.T := by
    have hm1 : 1 ≤ m * p.T := Nat.one_le_iff_ne_zero.mpr (by
      intro h
      have hm0 : m = 0 ∨ p.T = 0 := by
        rcases Nat.mul_eq_zero.mp h with h | h
        · exact Or.inl h
        · exact Or.inr h
      rcases hm0 with h | h
      · omega
      · omega)
    omega
  have hge : (m - 1) * p.T ≤ t := h₁
  have hdiv : t / p.T = m - 1 := by
    apply Nat.div_eq_of_lt_le
    · -- (m - 1) * p.T ≤ t
      exact hge
    · -- t < (m - 1 + 1) * p.T = m * p.T
      have : (m - 1 + 1) * p.T = m * p.T := by
        congr 1; omega
      rw [this]
      exact hlt
  rw [hdiv]
  omega

/-- The main per-step bound for Case 2: at any time `t` in the chosen sub-interval
`Icc ((m-1)*p.T) (m*p.T - 1)` with `m % 2 ≠ ℓ.val % 2` and the cyclic boundary at ℓ,
the conductance is at least `1 / (4 * p.z)`. -/
lemma case2_per_step_bound
    (p : Params) (hk : 1 ≤ p.k) (m : ℕ) (hm : 1 ≤ m)
    (S : Finset (VertexSet p))
    (hS_card_le : 2 * S.card ≤ Fintype.card (VertexSet p))
    (ℓ : Fin p.z)
    (hℓ_light : 2 * (S.filter (fun v => v.1 = ℓ)).card ≤ p.k)
    (hℓ_heavy : p.k < 2 * (S.filter (fun v => v.1 = ℓ + 1)).card)
    (hpar : m % 2 ≠ ℓ.val % 2)
    (t : ℕ) (h₁ : (m - 1) * p.T ≤ t) (h₂ : t ≤ m * p.T - 1) :
    (1 : ℝ) / (4 * p.z) ≤ ((lowerBoundGraph p).snapshot t).setConductance S := by
  classical
  -- Derive interval index.
  have hidx : intervalIndex p t = m := intervalIndex_of_mem p m t hm h₁ h₂
  -- Compute parity of (ℓ + 1).val: we have ((ℓ + 1).val % 2 = (ℓ.val + 1) % 2),
  -- using p.z even.
  have hsucc_parity : ((ℓ + 1).val % 2) = ((ℓ.val + 1) % 2) := by
    calc ((ℓ + 1).val % 2)
        = (((ℓ.val + 1) % p.z) % 2) := by simp [Fin.val_add]
      _ = ((ℓ.val + 1) % 2) := by rw [Nat.mod_mod_of_dvd _ p.hz_even]
  -- Choose `odd : Bool` so adjacency is `snapshotAdj p odd`, and prove anchor
  -- equalities directly from the case.
  obtain ⟨odd, hAdj, ha_ℓ, ha_ℓ1⟩ : ∃ odd : Bool,
      (∀ u w : VertexSet p,
        ((lowerBoundGraph p).snapshot t).Adj u w ↔
          u ≠ w ∧ activeAnchor p odd u.1 = activeAnchor p odd w.1) ∧
      activeAnchor p odd ℓ = ℓ ∧ activeAnchor p odd (ℓ + 1) = ℓ := by
    by_cases hm2 : m % 2 = 0
    · -- m even: graph = snapshot0 (odd anchors); odd = true.
      -- m % 2 = 0 ≠ ℓ.val % 2 means ℓ.val % 2 = 1.
      have hℓ1 : ℓ.val % 2 = 1 := by
        rcases Nat.mod_two_eq_zero_or_one ℓ.val with h0 | h1
        · exfalso; apply hpar; rw [hm2, h0]
        · exact h1
      have hℓ1_succ : (ℓ + 1).val % 2 = 0 := by
        rw [hsucc_parity]; omega
      refine ⟨true, ?_, ?_, ?_⟩
      · intro u w
        have hpar' : intervalIndex p t % 2 = 0 := by rw [hidx]; exact hm2
        have hg : (lowerBoundGraph p).snapshot t = snapshot0 p := by
          simp [lowerBoundGraph, hpar']
        rw [hg]; rfl
      · -- activeAnchor p true ℓ = ℓ via `imp_eq_or_succ` reverse plus parity.
        -- Use that `activeAnchor` returns ℓ iff `ℓ.val % 2 = 1` (which we have).
        -- Compute via reduction: activeAnchor unfolds to if-then-else.
        have : activeAnchor p true ℓ = if ℓ.val % 2 = 1 then ℓ else ℓ + (-1) := rfl
        rw [this, if_pos hℓ1]
      · -- activeAnchor p true (ℓ + 1) = ℓ via similar computation.
        have : activeAnchor p true (ℓ + 1) =
            if (ℓ + 1).val % 2 = 1 then (ℓ + 1) else (ℓ + 1) + (-1) := rfl
        rw [this]
        have hne_one : (0 : ℕ) ≠ 1 := by decide
        rw [if_neg (by rw [hℓ1_succ]; exact hne_one)]
        -- Goal: (ℓ + 1) + (-1) = ℓ
        rw [add_assoc, add_neg_cancel, add_zero]
    · -- m odd: graph = snapshot1 (even anchors); odd = false.
      -- m % 2 = 1 ≠ ℓ.val % 2 means ℓ.val % 2 = 0.
      have hm1 : m % 2 = 1 := by omega
      have hℓ0 : ℓ.val % 2 = 0 := by
        rcases Nat.mod_two_eq_zero_or_one ℓ.val with h0 | h1
        · exact h0
        · exfalso; apply hpar; rw [hm1, h1]
      have hℓ0_succ : (ℓ + 1).val % 2 = 1 := by
        rw [hsucc_parity]; omega
      refine ⟨false, ?_, ?_, ?_⟩
      · intro u w
        have hpar' : intervalIndex p t % 2 ≠ 0 := by rw [hidx]; exact hm2
        have hg : (lowerBoundGraph p).snapshot t = snapshot1 p := by
          simp [lowerBoundGraph, hpar']
        rw [hg]; rfl
      · -- activeAnchor p false ℓ = ℓ.
        have : activeAnchor p false ℓ = if ℓ.val % 2 = 0 then ℓ else ℓ + (-1) := rfl
        rw [this, if_pos hℓ0]
      · -- activeAnchor p false (ℓ + 1) = ℓ.
        have : activeAnchor p false (ℓ + 1) =
            if (ℓ + 1).val % 2 = 0 then (ℓ + 1) else (ℓ + 1) + (-1) := rfl
        rw [this]
        have hne_zero : (1 : ℕ) ≠ 0 := by decide
        rw [if_neg (by rw [hℓ0_succ]; exact hne_zero)]
        rw [add_assoc, add_neg_cancel, add_zero]
  -- Define C = block p ℓ ∪ block p (ℓ+1); |C| = 2 * p.k.
  set C : Finset (VertexSet p) := block p ℓ ∪ block p (ℓ + 1) with hC_def
  have hCdisj : Disjoint (block p ℓ) (block p (ℓ + 1)) :=
    block_disjoint p (block_succ_ne_aux p ℓ)
  have hCcard : C.card = 2 * p.k := by
    rw [hC_def, Finset.card_union_of_disjoint hCdisj, card_block, card_block, two_mul]
  -- Clique fact: any two distinct vertices of C are adjacent at time t.
  have hclique : ∀ u ∈ C, ∀ w ∈ C, u ≠ w → ((lowerBoundGraph p).snapshot t).Adj u w := by
    intro u hu w hw hne
    rw [hAdj]
    refine ⟨hne, ?_⟩
    -- u.1 = ℓ ∨ u.1 = ℓ+1, similarly for w. In all cases, anchors agree.
    have hu_or : u.1 = ℓ ∨ u.1 = ℓ + 1 := by
      rcases Finset.mem_union.mp hu with h | h
      · exact Or.inl ((mem_block p ℓ u).mp h)
      · exact Or.inr ((mem_block p (ℓ + 1) u).mp h)
    have hw_or : w.1 = ℓ ∨ w.1 = ℓ + 1 := by
      rcases Finset.mem_union.mp hw with h | h
      · exact Or.inl ((mem_block p ℓ w).mp h)
      · exact Or.inr ((mem_block p (ℓ + 1) w).mp h)
    have ha_u : activeAnchor p odd u.1 = ℓ := by
      rcases hu_or with h | h
      · rw [h]; exact ha_ℓ
      · rw [h]; exact ha_ℓ1
    have ha_w : activeAnchor p odd w.1 = ℓ := by
      rcases hw_or with h | h
      · rw [h]; exact ha_ℓ
      · rw [h]; exact ha_ℓ1
    rw [ha_u, ha_w]
  -- Set up X_S = S ∩ C, X_comp = C \ S.
  set X_S : Finset (VertexSet p) := S ∩ C with hX_S_def
  set X_comp : Finset (VertexSet p) := C \ S with hX_comp_def
  -- Translate filter-by-first-coord cards.
  have hSℓ_eq : S.filter (fun v => v.1 = ℓ) = S ∩ block p ℓ := by
    ext w; simp [Finset.mem_inter, mem_block, Finset.mem_filter]
  have hSℓ1_eq : S.filter (fun v => v.1 = ℓ + 1) = S ∩ block p (ℓ + 1) := by
    ext w; simp [Finset.mem_inter, mem_block, Finset.mem_filter]
  have hSℓ_card : 2 * (S ∩ block p ℓ).card ≤ p.k := by
    rw [← hSℓ_eq]; exact hℓ_light
  have hSℓ1_card : p.k < 2 * (S ∩ block p (ℓ + 1)).card := by
    rw [← hSℓ1_eq]; exact hℓ_heavy
  -- X_S = (S ∩ block ℓ) ∪ (S ∩ block (ℓ+1)).
  have hX_S_eq : X_S = (S ∩ block p ℓ) ∪ (S ∩ block p (ℓ + 1)) := by
    rw [hX_S_def, hC_def, Finset.inter_union_distrib_left]
  have hX_S_card_low : p.k + 1 ≤ 2 * X_S.card := by
    have hdisj' : Disjoint (S ∩ block p ℓ) (S ∩ block p (ℓ + 1)) :=
      hCdisj.mono Finset.inter_subset_right Finset.inter_subset_right
    rw [hX_S_eq, Finset.card_union_of_disjoint hdisj']
    have h2 : 2 * ((S ∩ block p ℓ).card + (S ∩ block p (ℓ + 1)).card) =
        2 * (S ∩ block p ℓ).card + 2 * (S ∩ block p (ℓ + 1)).card := by ring
    rw [h2]
    have hineq : p.k < 2 * (S ∩ block p (ℓ + 1)).card := hSℓ1_card
    omega
  -- X_comp.card ≥ p.k / 2 (specifically 2 * X_comp.card ≥ p.k).
  -- Use that V_ℓ \ S ⊆ X_comp, and 2 * |V_ℓ \ S| = 2*p.k - 2*|S ∩ V_ℓ| ≥ p.k.
  have hVℓ_S_sub : block p ℓ \ S ⊆ X_comp := by
    intro v hv
    rw [Finset.mem_sdiff] at hv
    obtain ⟨hvℓ, hvS⟩ := hv
    rw [hX_comp_def, Finset.mem_sdiff]
    exact ⟨Finset.mem_union_left _ hvℓ, hvS⟩
  have hVℓ_S_card : (block p ℓ \ S).card = p.k - (S ∩ block p ℓ).card := by
    have hcard : (block p ℓ \ S).card = (block p ℓ).card - (S ∩ block p ℓ).card :=
      Finset.card_sdiff
    rw [hcard, card_block]
  have hX_comp_card_low : p.k ≤ 2 * X_comp.card := by
    have h1 : (block p ℓ \ S).card ≤ X_comp.card := Finset.card_le_card hVℓ_S_sub
    have h2 : 2 * (block p ℓ \ S).card ≤ 2 * X_comp.card := by omega
    rw [hVℓ_S_card] at h2
    have h3 : (S ∩ block p ℓ).card ≤ p.k := by
      calc (S ∩ block p ℓ).card ≤ (block p ℓ).card := Finset.card_le_card Finset.inter_subset_right
        _ = p.k := card_block p ℓ
    have h4 : 2 * (p.k - (S ∩ block p ℓ).card) ≥ p.k := by
      have : 2 * (S ∩ block p ℓ).card ≤ p.k := hSℓ_card
      omega
    omega
  -- edgesBetween S (univ \ S) ≥ X_S.card * X_comp.card via the clique.
  have hcut_ge : X_S.card * X_comp.card ≤
      TemporalGraph.edgesBetween (lowerBoundGraph p) t S (Finset.univ \ S) := by
    -- The product X_S ×ˢ X_comp embeds into the filter (S ×ˢ (univ\S)).filter Adj.
    -- All pairs are adjacent (clique), and X_S ⊆ S, X_comp ⊆ univ \ S.
    show X_S.card * X_comp.card ≤
      ((S ×ˢ (Finset.univ \ S)).filter
        (fun pr => ((lowerBoundGraph p).snapshot t).Adj pr.1 pr.2)).card
    rw [← Finset.card_product]
    apply Finset.card_le_card
    intro pr hpr
    rcases Finset.mem_product.mp hpr with ⟨huXS, hwXcomp⟩
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · refine Finset.mem_product.mpr ⟨?_, ?_⟩
      · exact (Finset.mem_inter.mp (by rw [hX_S_def] at huXS; exact huXS)).1
      · -- pr.2 ∈ univ \ S: from X_comp = C \ S, so pr.2 ∉ S.
        have : pr.2 ∈ C ∧ pr.2 ∉ S := by
          rw [hX_comp_def, Finset.mem_sdiff] at hwXcomp; exact hwXcomp
        rw [Finset.mem_sdiff]
        exact ⟨Finset.mem_univ _, this.2⟩
    · -- Adjacency: pr.1 ∈ X_S ⊆ C, pr.2 ∈ X_comp ⊆ C, pr.1 ≠ pr.2.
      have hu_C : pr.1 ∈ C := by
        rw [hX_S_def, Finset.mem_inter] at huXS; exact huXS.2
      have hw_C : pr.2 ∈ C := by
        rw [hX_comp_def, Finset.mem_sdiff] at hwXcomp; exact hwXcomp.1
      have hne : pr.1 ≠ pr.2 := by
        intro hEq
        have : pr.1 ∈ S := (Finset.mem_inter.mp (by rw [hX_S_def] at huXS; exact huXS)).1
        have : pr.2 ∉ S := by
          rw [hX_comp_def, Finset.mem_sdiff] at hwXcomp; exact hwXcomp.2
        rw [hX_comp_def, Finset.mem_sdiff] at hwXcomp
        rw [hEq] at huXS
        rw [hX_S_def, Finset.mem_inter] at huXS
        exact hwXcomp.2 huXS.1
      exact hclique pr.1 hu_C pr.2 hw_C hne
  -- Volume of S = |S| * (2 * p.k - 1).
  have hvol_eq : TemporalGraph.volume (lowerBoundGraph p) t S = S.card * (2 * p.k - 1) := by
    have hreg :
        ∀ u v : VertexSet p,
          TemporalGraph.deg (lowerBoundGraph p) u =
            TemporalGraph.deg (lowerBoundGraph p) v := by
      intro u v
      simp [TemporalGraph.deg, lowerBoundGraph_degree]
    have hne : Nonempty (VertexSet p) := inferInstance
    calc TemporalGraph.volume (lowerBoundGraph p) t S
        = TemporalGraph.volume (lowerBoundGraph p) 0 S :=
            TemporalGraph.volume_fixed (lowerBoundGraph p)
              (lowerBoundGraph_fixedDegrees p) S t 0
      _ = S.card * TemporalGraph.deg (lowerBoundGraph p)
            (Classical.choice hne) :=
            TemporalGraph.volume_eq_card_mul_deg_of_regular
              (lowerBoundGraph p) hreg S
      _ = S.card * (2 * p.k - 1) := by
            congr 1
            simp [TemporalGraph.deg, lowerBoundGraph_degree]
  -- Final arithmetic.
  unfold SimpleGraph.setConductance
  rw [show ((lowerBoundGraph p).snapshot t).volume S = S.card * (2 * p.k - 1) from hvol_eq]
  -- Goal: 1/(4z) ≤ edgesBetween / (|S| * (2k-1))
  -- Equivalently: |S| * (2k-1) ≤ 4z * edgesBetween.
  have hScard_pos : 0 < S.card := by
    -- S.card > 0 since some block has 2|S∩V_x| > p.k ≥ 1.
    have hpos : 0 < (S.filter (fun v => v.1 = ℓ + 1)).card := by
      have : 0 < 2 * (S.filter (fun v => v.1 = ℓ + 1)).card := by omega
      omega
    have hsub : (S.filter (fun v => v.1 = ℓ + 1)).card ≤ S.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    omega
  have h2k1_pos : 0 < 2 * p.k - 1 := by omega
  have hden_pos_nat : 0 < S.card * (2 * p.k - 1) := Nat.mul_pos hScard_pos h2k1_pos
  have hden_pos : (0 : ℝ) < ((S.card * (2 * p.k - 1) : ℕ) : ℝ) := by
    exact_mod_cast hden_pos_nat
  have hpz_pos_R : (0 : ℝ) < 4 * (p.z : ℝ) := by
    have : (0 : ℝ) < (p.z : ℝ) := by exact_mod_cast p.hz_pos
    linarith
  rw [div_le_div_iff₀ hpz_pos_R hden_pos]
  -- Goal: 1 * (|S| * (2k-1)) ≤ edgesBetween * (4 * z)
  -- Move to ℕ via key inequality.
  have hSV : Fintype.card (VertexSet p) = p.k * p.z := card_vertexSet p
  -- Key ℕ inequality: S.card * (2*p.k - 1) ≤ 4 * p.z * (X_S.card * X_comp.card).
  have hkey_nat :
      S.card * (2 * p.k - 1) ≤ 4 * p.z * (X_S.card * X_comp.card) := by
    -- Step a: 2 * S.card ≤ p.k * p.z (from hS_card_le and hSV).
    have h2S : 2 * S.card ≤ p.k * p.z := by rw [← hSV]; exact hS_card_le
    -- Step b: 4 * (X_S.card * X_comp.card) ≥ (p.k + 1) * p.k from 2*X_S ≥ p.k+1, 2*X_comp ≥ p.k.
    have hprod_low : (p.k + 1) * p.k ≤ 4 * (X_S.card * X_comp.card) := by
      have h1 : (p.k + 1) * p.k ≤ (2 * X_S.card) * (2 * X_comp.card) :=
        Nat.mul_le_mul hX_S_card_low hX_comp_card_low
      have h2 : (2 * X_S.card) * (2 * X_comp.card) = 4 * (X_S.card * X_comp.card) := by ring
      linarith
    -- Step c: 2 * p.k * (2 * p.k - 1) ≤ 8 * (X_S.card * X_comp.card).
    -- We use: p.k * (2*p.k - 1) ≤ 2 * (p.k + 1) * p.k (since 2*p.k - 1 ≤ 2*(p.k+1) = 2*p.k+2).
    have hpk2 : p.k * (2 * p.k - 1) ≤ 2 * ((p.k + 1) * p.k) := by
      have hh : 2 * p.k - 1 ≤ 2 * (p.k + 1) := by omega
      have := Nat.mul_le_mul_left p.k hh
      -- p.k * (2*p.k - 1) ≤ p.k * (2 * (p.k + 1)) = 2 * ((p.k + 1) * p.k)
      have heq : p.k * (2 * (p.k + 1)) = 2 * ((p.k + 1) * p.k) := by ring
      linarith
    have hmul1 : p.k * (2 * p.k - 1) ≤ 8 * (X_S.card * X_comp.card) := by
      have h2 : 2 * ((p.k + 1) * p.k) ≤ 2 * (4 * (X_S.card * X_comp.card)) :=
        Nat.mul_le_mul_left _ hprod_low
      have heq : 2 * (4 * (X_S.card * X_comp.card)) = 8 * (X_S.card * X_comp.card) := by ring
      linarith
    -- Step d: 2 * S.card * (2k-1) ≤ p.z * (p.k * (2*p.k - 1)) ≤ p.z * (8 * (X_S * X_comp)).
    have hSk : 2 * (S.card * (2 * p.k - 1)) ≤ p.k * p.z * (2 * p.k - 1) := by
      have h := Nat.mul_le_mul_right (2 * p.k - 1) h2S
      linarith
    have hpz_mul : p.z * (p.k * (2 * p.k - 1)) ≤ p.z * (8 * (X_S.card * X_comp.card)) :=
      Nat.mul_le_mul_left _ hmul1
    have heq : p.k * p.z * (2 * p.k - 1) = p.z * (p.k * (2 * p.k - 1)) := by ring
    have hbig : 2 * (S.card * (2 * p.k - 1)) ≤ p.z * (8 * (X_S.card * X_comp.card)) := by
      calc 2 * (S.card * (2 * p.k - 1)) ≤ p.k * p.z * (2 * p.k - 1) := hSk
        _ = p.z * (p.k * (2 * p.k - 1)) := heq
        _ ≤ p.z * (8 * (X_S.card * X_comp.card)) := hpz_mul
    -- p.z * (8 * X) = 2 * (4 * p.z * X), so divide by 2.
    have heq3 : p.z * (8 * (X_S.card * X_comp.card)) =
        2 * (4 * p.z * (X_S.card * X_comp.card)) := by ring
    rw [heq3] at hbig
    linarith
  -- Cast to ℝ.
  have hcut_ℕ_le_ℝ :
      ((X_S.card * X_comp.card : ℕ) : ℝ) ≤
        ((TemporalGraph.edgesBetween (lowerBoundGraph p) t S (Finset.univ \ S) : ℕ) : ℝ) := by
    exact_mod_cast hcut_ge
  have hkey_ℝ :
      ((S.card * (2 * p.k - 1) : ℕ) : ℝ) ≤
        4 * p.z * ((X_S.card * X_comp.card : ℕ) : ℝ) := by
    have := hkey_nat
    have h1 : ((S.card * (2 * p.k - 1) : ℕ) : ℝ) ≤
        ((4 * p.z * (X_S.card * X_comp.card) : ℕ) : ℝ) := by exact_mod_cast this
    have hpush : ((4 * p.z * (X_S.card * X_comp.card) : ℕ) : ℝ) =
        4 * p.z * ((X_S.card * X_comp.card : ℕ) : ℝ) := by push_cast; ring
    rw [hpush] at h1
    exact h1
  -- Combine: |S| * (2k-1) ≤ 4z * |X_S| * |X_comp| ≤ 4z * edgesBetween.
  have hpz_pos : (0 : ℝ) ≤ 4 * (p.z : ℝ) := by positivity
  nlinarith [hcut_ℕ_le_ℝ, hkey_ℝ]


/-- \label{lem:clique-lower-bound-conductance}

General-window strengthening of `clique_lower_bound_conductance`: for any
starting time `t_start ≥ 0` and any `S` with `1 ≤ |S| ≤ n/2`, the cumulative
conductance over the window `Icc t_start (t_start + 3T - 1)` is at least
`T/(4z)`.

The proof picks `j = t_start / T + 1` (so `j ≥ 1`); the two consecutive
`T`-intervals `Icc (j*T) ((j+1)*T - 1)` and `Icc ((j+1)*T) ((j+2)*T - 1)` are
both fully contained in `Icc t_start (t_start + 3T - 1)`. By the per-step
Case 1 / Case 2 bounds, one of them already contributes at least `T/(4z)`. -/
theorem clique_lower_bound_conductance_general
    (p : Params) (hk : 1 ≤ p.k)
    (t_start : ℕ)
    (S : Finset (VertexSet p))
    (hS_nonempty : S.Nonempty)
    (hS_card_le : 2 * S.card ≤ Fintype.card (VertexSet p)) :
    (p.T : ℝ) / (4 * p.z) ≤
      ∑ t ∈ Finset.Icc t_start (t_start + 3 * p.T - 1),
        ((lowerBoundGraph p).snapshot t).setConductance S := by
  classical
  set j : ℕ := t_start / p.T + 1 with hj_def
  have hj_pos : 0 < j := by simp [hj_def]
  have hT_pos : 0 < p.T := p.hT_pos
  have hT_pos_R : (0 : ℝ) < p.T := Nat.cast_pos.mpr hT_pos
  have hz_pos_R : (0 : ℝ) < p.z := Nat.cast_pos.mpr p.hz_pos
  have hz2 : 2 ≤ p.z := p.hz_two_le
  have hz2_R : (2 : ℝ) ≤ (p.z : ℝ) := by exact_mod_cast hz2
  -- j * p.T = (t_start / p.T) * p.T + p.T
  have hjT_eq : j * p.T = t_start / p.T * p.T + p.T := by
    simp [hj_def]; ring
  -- (j + 2) * p.T = (t_start / p.T) * p.T + 3 * p.T
  have hjp2T_eq : (j + 2) * p.T = t_start / p.T * p.T + 3 * p.T := by
    simp [hj_def]; ring
  -- t_start ≤ j * p.T
  have h_lo : t_start ≤ j * p.T := by
    have h2 : t_start < t_start / p.T * p.T + p.T := Nat.lt_div_mul_add hT_pos
    omega
  -- (j+2) * p.T ≤ t_start + 3 * p.T
  have h_hi : (j + 2) * p.T ≤ t_start + 3 * p.T := by
    have h1 : t_start / p.T * p.T ≤ t_start := Nat.div_mul_le_self _ _
    omega
  -- For both m = j + 1 and m = j + 2, the T-interval Icc ((m-1)*T) (m*T - 1)
  -- is contained in Icc t_start (t_start + 3T - 1).
  have hcontain : ∀ m, j + 1 ≤ m → m ≤ j + 2 →
      Finset.Icc ((m - 1) * p.T) (m * p.T - 1) ⊆
        Finset.Icc t_start (t_start + 3 * p.T - 1) := by
    intro m hm_lo hm_hi t ht
    rw [Finset.mem_Icc] at ht ⊢
    have hmT_lo : j * p.T ≤ (m - 1) * p.T :=
      Nat.mul_le_mul_right _ (by omega)
    have hmT_hi : m * p.T ≤ (j + 2) * p.T := Nat.mul_le_mul_right _ hm_hi
    have h_jp1_T_pos : 1 ≤ (j + 1) * p.T := Nat.mul_pos (by omega) hT_pos
    have h_mT_pos : 1 ≤ m * p.T := by
      have h2 : (j + 1) * p.T ≤ m * p.T := Nat.mul_le_mul_right _ hm_lo
      omega
    refine ⟨?_, ?_⟩
    · omega
    · omega
  -- Card of T-interval is exactly p.T.
  have hcard_T : ∀ m, 1 ≤ m → (Finset.Icc ((m - 1) * p.T) (m * p.T - 1)).card = p.T := by
    intro m hm
    rw [Nat.card_Icc]
    have hT1 : 1 ≤ m * p.T := Nat.one_le_iff_ne_zero.mpr (by
      intro h
      rcases Nat.mul_eq_zero.mp h with h | h
      · omega
      · omega)
    have hh : m * p.T - 1 + 1 = m * p.T := Nat.sub_add_cancel hT1
    rw [hh]
    have heq : (m - 1) * p.T = m * p.T - p.T := by
      rw [Nat.sub_mul, Nat.one_mul]
    rw [heq]
    have hT2 : p.T ≤ m * p.T := by
      have : 1 * p.T ≤ m * p.T := Nat.mul_le_mul_right _ hm
      linarith
    omega
  by_cases hcase1 : ∀ x : Fin p.z, 2 * (S.filter (fun v => v.1 = x)).card ≤ p.k
  · -- Case 1: pick m = j + 1, every step gives ≥ 1/2.
    have hjp1_pos : 1 ≤ j + 1 := by omega
    have hsubset := hcontain (j + 1) (le_refl _) (by omega)
    have hstep : ∀ t ∈ Finset.Icc ((j + 1 - 1) * p.T) ((j + 1) * p.T - 1),
        (1 / 2 : ℝ) ≤ ((lowerBoundGraph p).snapshot t).setConductance S :=
      fun t _ => case1_conductance_ge_half p hk t S hS_nonempty hcase1
    have hcard := hcard_T (j + 1) hjp1_pos
    have hsub_ge : (p.T : ℝ) * (1 / 2) ≤
        ∑ t ∈ Finset.Icc ((j + 1 - 1) * p.T) ((j + 1) * p.T - 1),
          ((lowerBoundGraph p).snapshot t).setConductance S := by
      have hge := Finset.card_nsmul_le_sum
          (Finset.Icc ((j + 1 - 1) * p.T) ((j + 1) * p.T - 1))
          (fun t => ((lowerBoundGraph p).snapshot t).setConductance S)
          (1 / 2 : ℝ) hstep
      rw [hcard, nsmul_eq_mul] at hge
      exact hge
    have hbig_ge :
        ∑ t ∈ Finset.Icc ((j + 1 - 1) * p.T) ((j + 1) * p.T - 1),
          ((lowerBoundGraph p).snapshot t).setConductance S ≤
        ∑ t ∈ Finset.Icc t_start (t_start + 3 * p.T - 1),
          ((lowerBoundGraph p).snapshot t).setConductance S := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro t _ _
      exact ((lowerBoundGraph p).snapshot t).setConductance_nonneg S
    -- T/2 ≥ T/(4z) (since z ≥ 2 so 4z ≥ 8 > 2).
    have hT_4z_le_T_2 : (p.T : ℝ) / (4 * p.z) ≤ (p.T : ℝ) / 2 := by
      have h4z_pos : (0 : ℝ) < 4 * p.z := by linarith
      rw [div_le_div_iff₀ h4z_pos (by norm_num : (0 : ℝ) < 2)]
      nlinarith
    have hT_eq : (p.T : ℝ) / 2 = (p.T : ℝ) * (1 / 2) := by rw [mul_one_div]
    linarith
  · -- Case 2: pigeonhole gives ℓ. Pick m ∈ {j+1, j+2} with m % 2 ≠ ℓ.val % 2.
    push Not at hcase1
    obtain ⟨ℓ, hℓ_light, hℓ_heavy⟩ := case2_pigeonhole p S hS_card_le hcase1
    -- Choose m ∈ {j+1, j+2} with right parity.
    obtain ⟨m, hm_lo, hm_hi, hpar_m⟩ : ∃ m : ℕ,
        j + 1 ≤ m ∧ m ≤ j + 2 ∧ m % 2 ≠ ℓ.val % 2 := by
      rcases Nat.mod_two_eq_zero_or_one (j + 1) with hjp1_e | hjp1_o
      · -- j + 1 even, so j + 2 odd.
        rcases Nat.mod_two_eq_zero_or_one ℓ.val with hℓ_e | hℓ_o
        · -- both even: pick m = j + 2 (odd)
          refine ⟨j + 2, by omega, by omega, ?_⟩
          have hjp2_o : (j + 2) % 2 = 1 := by omega
          rw [hjp2_o, hℓ_e]; decide
        · -- ℓ odd: pick m = j + 1 (even)
          refine ⟨j + 1, by omega, by omega, ?_⟩
          rw [hjp1_e, hℓ_o]; decide
      · -- j + 1 odd, so j + 2 even.
        rcases Nat.mod_two_eq_zero_or_one ℓ.val with hℓ_e | hℓ_o
        · -- ℓ even: pick m = j + 1 (odd)
          refine ⟨j + 1, by omega, by omega, ?_⟩
          rw [hjp1_o, hℓ_e]; decide
        · -- both odd: pick m = j + 2 (even)
          refine ⟨j + 2, by omega, by omega, ?_⟩
          have hjp2_e : (j + 2) % 2 = 0 := by omega
          rw [hjp2_e, hℓ_o]; decide
    have hm_pos : 1 ≤ m := by omega
    have hsubset := hcontain m hm_lo hm_hi
    have hstep : ∀ t ∈ Finset.Icc ((m - 1) * p.T) (m * p.T - 1),
        (1 : ℝ) / (4 * p.z) ≤ ((lowerBoundGraph p).snapshot t).setConductance S := by
      intro t ht
      rw [Finset.mem_Icc] at ht
      exact case2_per_step_bound p hk m hm_pos S hS_card_le ℓ hℓ_light hℓ_heavy hpar_m
        t ht.1 ht.2
    have hcard := hcard_T m hm_pos
    have hsub_ge : (p.T : ℝ) * (1 / (4 * p.z)) ≤
        ∑ t ∈ Finset.Icc ((m - 1) * p.T) (m * p.T - 1),
          ((lowerBoundGraph p).snapshot t).setConductance S := by
      have hge := Finset.card_nsmul_le_sum
          (Finset.Icc ((m - 1) * p.T) (m * p.T - 1))
          (fun t => ((lowerBoundGraph p).snapshot t).setConductance S)
          (1 / (4 * p.z) : ℝ) hstep
      rw [hcard, nsmul_eq_mul] at hge
      exact hge
    have hbig_ge :
        ∑ t ∈ Finset.Icc ((m - 1) * p.T) (m * p.T - 1),
          ((lowerBoundGraph p).snapshot t).setConductance S ≤
        ∑ t ∈ Finset.Icc t_start (t_start + 3 * p.T - 1),
          ((lowerBoundGraph p).snapshot t).setConductance S := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro t _ _
      exact ((lowerBoundGraph p).snapshot t).setConductance_nonneg S
    have heq_ratio : (p.T : ℝ) / (4 * p.z) = (p.T : ℝ) * (1 / (4 * p.z)) := by
      rw [mul_one_div]
    rw [heq_ratio]
    linarith

end TemporalGraph.VoterProcess.LowerBound
