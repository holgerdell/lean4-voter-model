module

import VoterProcess.Expectation
import VoterProcess.TwoOpinion
public import VoterProcess.Step
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Algebra.Order.Star.Real

/-! ## Stepwise edges bound

**Paper reference**: `lem:stepwise-edges-bound`.

On a temporal graph with fixed degrees and a voter model process `vm`:
```
E[|e_t(S_{j+1}, S̄_{j+1}) − e_t(S_j, S̄_j)| | ℱ_j] ≤ e_j(S_j, S̄_j)  a.s.
```

## Main results

- `VoterModel.edgesBetween_change_bound` — deterministic bound: cut change ≤ degree sum of
  changed vertices.
- `VoterModel.expected_swap_degree_sum` — expected degree-sum of swapped vertices equals
  the cut.
- `VoterModelAbstract.stepwise_edges_bound` — the a.s. conditional-expectation form of the bound,
  using `vm.S (j+1)`, `vm.S j`, and `vm.μ[· | vm.ℱ j]`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators symmDiff

noncomputable section

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]

-- ════════════════════════════════════════════════════════════════════
-- Part 1 : Deterministic bound on the cut change
-- ════════════════════════════════════════════════════════════════════

namespace VoterModel

/-- Deterministic bound: the cut decreases by at most the total degree of changed vertices. -/
theorem edgesBetween_change_bound
    (G : TemporalGraph V) (t' : ℕ) (S S' : Finset V) :
    (TemporalGraph.edgesBetween G t' S (Finset.univ \ S) : ℝ) -
      (TemporalGraph.edgesBetween G t' S' (Finset.univ \ S') : ℝ) ≤
      ∑ v ∈ S ∆ S', (TemporalGraph.degree G t' v : ℝ) := by
  -- It suffices to prove the ℕ-level inequality:
  -- edgesBetween(S,S̄) ≤ edgesBetween(S',S̄') + ∑_{v ∈ S∆S'} deg(v)
  suffices h : TemporalGraph.edgesBetween G t' S (Finset.univ \ S)
      ≤ TemporalGraph.edgesBetween G t' S' (Finset.univ \ S') +
        ∑ v ∈ S ∆ S', TemporalGraph.degree G t' v by
    have h' : (TemporalGraph.edgesBetween G t' S (Finset.univ \ S) : ℝ) ≤
        (TemporalGraph.edgesBetween G t' S' (Finset.univ \ S') : ℝ) +
        ∑ v ∈ S ∆ S', (TemporalGraph.degree G t' v : ℝ) := by
      exact_mod_cast h
    linarith
  -- Every edge (u,w) in cut(S) either stays in cut(S') or has an endpoint in S∆S'.
  simp only [TemporalGraph.edgesBetween, SimpleGraph.edgesBetween, TemporalGraph.degree,
    SimpleGraph.degree]
  -- Rewrite card of filtered product as a sum using sum_product'
  have hcard_eq_sum : ∀ (A B : Finset V),
      ((A ×ˢ B).filter (fun p => (G.snapshot t').Adj p.1 p.2)).card
      = ∑ v ∈ A, (B.filter (fun w => (G.snapshot t').Adj v w)).card := by
    intro A B; simp_rw [Finset.card_filter]
    exact (Finset.sum_product' A B (fun v w => if (G.snapshot t').Adj v w then 1 else 0))
  rw [hcard_eq_sum S (Finset.univ \ S), hcard_eq_sum S' (Finset.univ \ S')]
  -- Step A: Split ∑_{v∈S} = ∑_{v∈S∩S'} + ∑_{v∈S\S'} without rewriting S elsewhere
  have hS_disj : Disjoint (S ∩ S') (S \ S') := by
    simp [Finset.disjoint_left]; tauto
  have hsum_split : ∑ v ∈ S, ((Finset.univ \ S).filter (fun w => (G.snapshot t').Adj v w)).card
      = ∑ v ∈ S ∩ S', ((Finset.univ \ S).filter (fun w => (G.snapshot t').Adj v w)).card
        + ∑ v ∈ S \ S', ((Finset.univ \ S).filter (fun w => (G.snapshot t').Adj v w)).card := by
    rw [← Finset.sum_union hS_disj]
    congr 1; ext v; simp [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_union]; tauto
  rw [hsum_split]
  -- Step B: For v ∈ S∩S', bound #{w∈univ\S | adj v w} ≤ #{w∈univ\S' | adj} + #{w∈S'\S | adj}
  have huniv_split : ∀ v, (v ∈ S ∩ S') →
      ((Finset.univ \ S).filter (fun w => (G.snapshot t').Adj v w)).card
      ≤ ((Finset.univ \ S').filter (fun w => (G.snapshot t').Adj v w)).card
        + ((S' \ S).filter (fun w => (G.snapshot t').Adj v w)).card := by
    intro v _
    calc ((Finset.univ \ S).filter (fun w => (G.snapshot t').Adj v w)).card
        ≤ (((Finset.univ \ S').filter (fun w => (G.snapshot t').Adj v w)) ∪
            ((S' \ S).filter (fun w => (G.snapshot t').Adj v w))).card := by
          apply Finset.card_le_card
          intro w hw
          simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and,
            Finset.mem_union] at hw ⊢
          by_cases hwS' : w ∈ S'
          · exact Or.inr ⟨⟨hwS', hw.1⟩, hw.2⟩
          · exact Or.inl ⟨hwS', hw.2⟩
      _ ≤ _ := Finset.card_union_le _ _
  -- Step C: Bound the S∩S' part using huniv_split
  have h_inter : ∑ v ∈ S ∩ S', ((Finset.univ \ S).filter (fun w => (G.snapshot t').Adj v w)).card
      ≤ ∑ v ∈ S ∩ S', ((Finset.univ \ S').filter (fun w => (G.snapshot t').Adj v w)).card
        + ∑ v ∈ S ∩ S', ((S' \ S).filter (fun w => (G.snapshot t').Adj v w)).card := by
    calc ∑ v ∈ S ∩ S', ((Finset.univ \ S).filter (fun w => (G.snapshot t').Adj v w)).card
        ≤ ∑ v ∈ S ∩ S', (((Finset.univ \ S').filter (fun w => (G.snapshot t').Adj v w)).card
            + ((S' \ S).filter (fun w => (G.snapshot t').Adj v w)).card) :=
          Finset.sum_le_sum huniv_split
      _ = _ := Finset.sum_add_distrib
  -- Part 1: ∑_{v∈S∩S'} #{w∈univ\S' | adj} ≤ ∑_{v∈S'} #{w∈univ\S' | adj}  (since S∩S' ⊆ S')
  have h_sub_S' : ∑ v ∈ S ∩ S', ((Finset.univ \ S').filter (fun w => (G.snapshot t').Adj v w)).card
      ≤ ∑ v ∈ S', ((Finset.univ \ S').filter (fun w => (G.snapshot t').Adj v w)).card :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.inter_subset_right) (by intros; omega)
  -- Part 2: ∑_{v∈S∩S'} #{w∈S'\S | adj v w} ≤ ∑_{w∈S'\S} deg(w)
  -- Count bipartite edges between S∩S' and S'\S via product sets, then use swap injection
  have h_cross : ∑ v ∈ S ∩ S', ((S' \ S).filter (fun w => (G.snapshot t').Adj v w)).card
      ≤ ∑ w ∈ S' \ S, (Finset.univ.filter (fun v => (G.snapshot t').Adj w v)).card := by
    calc ∑ v ∈ S ∩ S', ((S' \ S).filter (fun w => (G.snapshot t').Adj v w)).card
        = (((S ∩ S') ×ˢ (S' \ S)).filter (fun p => (G.snapshot t').Adj p.1 p.2)).card :=
          (hcard_eq_sum (S ∩ S') (S' \ S)).symm
      _ = ((((S ∩ S') ×ˢ (S' \ S)).filter (fun p => (G.snapshot t').Adj p.1 p.2)).image
            Prod.swap).card :=
          (Finset.card_image_of_injective _ Prod.swap_injective).symm
      _ ≤ (((S' \ S) ×ˢ Finset.univ).filter (fun p => (G.snapshot t').Adj p.1 p.2)).card := by
          apply Finset.card_le_card
          intro ⟨w, v⟩ hwv
          simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_product, Prod.swap,
            Prod.mk.injEq, Finset.mem_univ] at hwv ⊢
          obtain ⟨⟨a, b⟩, ⟨⟨ha_mem, hb_mem⟩, hadj⟩, rfl, rfl⟩ := hwv
          exact ⟨⟨hb_mem, trivial⟩, ((G.snapshot t').adj_comm a b).mp hadj⟩
      _ = ∑ w ∈ S' \ S, (Finset.univ.filter (fun v => (G.snapshot t').Adj w v)).card :=
          hcard_eq_sum (S' \ S) Finset.univ
  -- Part 3: ∑_{v∈S\S'} #{w∈univ\S | adj v w} ≤ ∑_{v∈S\S'} deg(v)
  have h_diff : ∑ v ∈ S \ S', ((Finset.univ \ S).filter (fun w => (G.snapshot t').Adj v w)).card
      ≤ ∑ v ∈ S \ S', (Finset.univ.filter (fun w => (G.snapshot t').Adj v w)).card :=
    Finset.sum_le_sum (fun v _ => Finset.card_le_card
      (Finset.filter_subset_filter _ Finset.sdiff_subset))
  -- Part 4: S∆S' = (S\S') ⊔ (S'\S), combine the sums
  have h_symm_diff : ∑ v ∈ S ∆ S', (Finset.univ.filter (fun w => (G.snapshot t').Adj v w)).card
      = ∑ v ∈ S \ S', (Finset.univ.filter (fun w => (G.snapshot t').Adj v w)).card
        + ∑ v ∈ S' \ S, (Finset.univ.filter (fun w => (G.snapshot t').Adj v w)).card := by
    rw [symmDiff_def, sup_eq_union]
    exact Finset.sum_union (sdiff_disjoint.mono_right sdiff_le)
  simp only [SimpleGraph.neighborFinset_eq_filter] at *
  linarith [h_inter, h_sub_S', h_cross, h_diff, h_symm_diff]

/-- Absolute-value deterministic bound: `|e(S', S̄') − e(S, S̄)| ≤ Σ_{v ∈ S∆S'} deg(v)`. -/
theorem edgesBetween_change_abs_bound
    (G : TemporalGraph V) (t' : ℕ) (S S' : Finset V) :
    |((TemporalGraph.edgesBetween G t' S' (Finset.univ \ S') : ℝ) -
      (TemporalGraph.edgesBetween G t' S (Finset.univ \ S) : ℝ))| ≤
      ∑ v ∈ S ∆ S', (TemporalGraph.degree G t' v : ℝ) := by
  rw [abs_le]
  constructor
  · linarith [edgesBetween_change_bound G t' S S']
  · have h := edgesBetween_change_bound G t' S' S
    rw [symmDiff_comm] at h
    linarith

/-- Expected degree-sum of vertices that swap opinion equals the cut at time `t`.
    Uses fixed degrees so that `degree G t' v = degree G t v`. -/
theorem expected_swap_degree_sum
    (G : TemporalGraphFixedDegree V)
    (S : Finset V) (t t' : ℕ) :
    ∫ S', (∑ v ∈ S ∆ S', (TemporalGraph.degree G t' v : ℝ))
        ∂((stepDist₂ G t S).toMeasure)
      = (TemporalGraph.edgesBetween G t S (Finset.univ \ S) : ℝ) := by
  rw [← stepDist₂Aux_eq_stepDist₂]
  have hdeg_fixed : ∀ v : V, TemporalGraph.degree G t' v = TemporalGraph.degree G t v :=
    fun v => G.degrees_fixed v t' t
  -- Convert restricted sum to full sum, swap integral and sum via PMF sums
  simp_rw [show ∀ T : Finset V, ∑ v ∈ S ∆ T, (TemporalGraph.degree G t' v : ℝ) =
      ∑ v : V, if v ∈ S ∆ T then (TemporalGraph.degree G t' v : ℝ) else 0 from
    fun T => by rw [← Finset.sum_filter]; congr 1; ext; simp only [Finset.mem_filter,
      Finset.mem_univ, true_and]]
  rw [PMF.integral_eq_sum]
  simp_rw [smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← smul_eq_mul, ← PMF.integral_eq_sum]
  -- Per-vertex: compute ∫_T 1_{v∈T} · deg(v)
  have hind : ∀ v : V,
      ∫ T, (if v ∈ T then (TemporalGraph.degree G t' v : ℝ) else 0)
          ∂((stepDist₂Aux G t S Finset.univ.toList).toMeasure)
      = ((((if v ∈ S then TemporalGraph.degree G t v else 0) +
          TemporalGraph.degreeIn G t v S : ℕ) : ℝ) / 2) := by
    intro v
    rw [indicator_expectation_gen G t S v _ Finset.univ.toList (Finset.nodup_toList _)]
    simpa [List.mem_toFinset, Bool.cond_eq_ite, hdeg_fixed v] using
      nextOpinion_weighted_expectation G t S v
  -- Per-vertex: decompose symmDiff indicator and compute
  have hperV : ∀ v : V,
      ∫ T, (if v ∈ S ∆ T then (TemporalGraph.degree G t' v : ℝ) else 0)
          ∂((stepDist₂Aux G t S Finset.univ.toList).toMeasure)
      = if v ∈ S then
          ((TemporalGraph.degree G t v : ℝ) - (TemporalGraph.degreeIn G t v S : ℝ)) / 2
        else
          (TemporalGraph.degreeIn G t v S : ℝ) / 2 := by
    intro v
    by_cases hvS : v ∈ S
    · -- v ∈ S: 1_{v∈S∆T} = 1 - 1_{v∈T}, so integral = deg - E[1_{v∈T}·deg]
      simp only [hvS, ↓reduceIte]
      simp_rw [show ∀ T : Finset V,
          (if v ∈ S ∆ T then (TemporalGraph.degree G t' v : ℝ) else 0) =
          (TemporalGraph.degree G t' v : ℝ) -
            (if v ∈ T then (TemporalGraph.degree G t' v : ℝ) else 0) from
        fun T => by simp [Finset.mem_symmDiff, hvS]; split <;> simp]
      -- E[deg - ite] = deg·1 - E[ite] using PMF sums
      rw [PMF.integral_eq_sum]
      simp_rw [smul_eq_mul]
      have hmass : ∑ T, ((stepDist₂Aux G t S Finset.univ.toList) T).toReal = 1 := by
        simpa [smul_eq_mul] using
          (PMF.integral_eq_sum (stepDist₂Aux G t S Finset.univ.toList) (fun _ => (1 : ℝ))).symm
      conv_lhs => arg 2; ext T; rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hmass, one_mul,
        show ∑ T, ((stepDist₂Aux G t S Finset.univ.toList) T).toReal *
            (if v ∈ T then (TemporalGraph.degree G t' v : ℝ) else 0)
          = ∫ T, (if v ∈ T then (TemporalGraph.degree G t' v : ℝ) else 0)
              ∂((stepDist₂Aux G t S Finset.univ.toList).toMeasure) from
          by rw [PMF.integral_eq_sum]; simp [smul_eq_mul],
        hind v]
      simp [hvS, hdeg_fixed v]; ring
    · -- v ∉ S: 1_{v∈S∆T} = 1_{v∈T}
      simp only [hvS, ↓reduceIte]
      simp_rw [show ∀ T : Finset V,
          (if v ∈ S ∆ T then (TemporalGraph.degree G t' v : ℝ) else 0) =
          (if v ∈ T then (TemporalGraph.degree G t' v : ℝ) else 0) from
        fun T => by simp [Finset.mem_symmDiff, hvS]]
      rw [hind v]; simp [hvS]
  simp_rw [hperV]
  -- Goal: ∑_v (if v∈S then (deg-ev)/2 else ev/2) = edgesBetween(S, univ\S)
  -- Split sum over univ = S ∪ (univ \ S), simplify ite
  rw [show (Finset.univ : Finset V) = S ∪ (Finset.univ \ S) from
      (Finset.union_sdiff_of_subset (Finset.subset_univ S)).symm,
    Finset.sum_union disjoint_sdiff_self_right,
    show ∑ v ∈ S, (if v ∈ S then
          ((TemporalGraph.degree G t v : ℝ) - (TemporalGraph.degreeIn G t v S : ℝ)) / 2
        else (TemporalGraph.degreeIn G t v S : ℝ) / 2) =
        ∑ v ∈ S, ((TemporalGraph.degree G t v : ℝ) -
          (TemporalGraph.degreeIn G t v S : ℝ)) / 2 from
      Finset.sum_congr rfl (fun v hv => by simp [hv]),
    show ∑ v ∈ Finset.univ \ S, (if v ∈ S then
          ((TemporalGraph.degree G t v : ℝ) - (TemporalGraph.degreeIn G t v S : ℝ)) / 2
        else (TemporalGraph.degreeIn G t v S : ℝ) / 2) =
        ∑ v ∈ Finset.univ \ S, (TemporalGraph.degreeIn G t v S : ℝ) / 2 from
      Finset.sum_congr rfl (fun v hv => by simp [(Finset.mem_sdiff.mp hv).2])]
  -- deg(v) - degreeIn(v,S) = degreeIn(v, univ\S) since S⊔Sᶜ = univ
  have hev_compl : ∀ v : V,
      (TemporalGraph.degree G t v : ℝ) - (TemporalGraph.degreeIn G t v S : ℝ) =
      (TemporalGraph.degreeIn G t v (Finset.univ \ S) : ℝ) := by
    intro v
    have hsplit :
        (Finset.univ.filter fun w => (G.snapshot t).Adj v w) =
          (S.filter fun w => (G.snapshot t).Adj v w) ∪
            ((Finset.univ \ S).filter fun w => (G.snapshot t).Adj v w) := by
      ext w
      by_cases hwS : w ∈ S <;> simp [hwS]
    have hdisj :
        Disjoint
          (S.filter fun w => (G.snapshot t).Adj v w)
          ((Finset.univ \ S).filter fun w => (G.snapshot t).Adj v w) := by
      refine Finset.disjoint_left.2 ?_
      intro w hwS hwCompl
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at hwS hwCompl
      exact hwCompl.1 hwS.1
    have h : TemporalGraph.degree G t v =
        TemporalGraph.degreeIn G t v S +
        TemporalGraph.degreeIn G t v (Finset.univ \ S) := by
      simp only [TemporalGraph.degree, SimpleGraph.degree, TemporalGraph.degreeIn,
        SimpleGraph.degreeIn]
      rw [← Finset.card_union_of_disjoint hdisj, ← hsplit]
      simp [SimpleGraph.neighborFinset_eq_filter]
    push_cast [h]; ring
  simp_rw [hev_compl]
  -- ∑_{v∈A} degreeIn(v,B) = edgesBetween(A,B) via sum_product'
  have hsum_cut : ∀ (A B : Finset V),
      (∑ v ∈ A, (TemporalGraph.degreeIn G t v B : ℝ)) =
      (TemporalGraph.edgesBetween G t A B : ℝ) := by
    intro A B
    have hnat :
        ∑ v ∈ A, TemporalGraph.degreeIn G t v B = TemporalGraph.edgesBetween G t A B := by
      simp only [TemporalGraph.degreeIn, SimpleGraph.degreeIn, TemporalGraph.edgesBetween,
        SimpleGraph.edgesBetween, Finset.card_filter]
      exact (Finset.sum_product' A B
        (fun v w => if (G.snapshot t).Adj v w then (1 : ℕ) else 0)
        ).symm
    exact_mod_cast hnat
  have hcompl_sdiff : (S ∪ (Finset.univ \ S)) \ S = Finset.univ \ S := by
    ext v
    simp
  rw [hcompl_sdiff]
  have hsum_left :
      ∑ x ∈ S, (TemporalGraph.degreeIn G t x (Finset.univ \ S) : ℝ) / (2 : ℝ) =
        (TemporalGraph.edgesBetween G t S (Finset.univ \ S) : ℝ) / (2 : ℝ) := by
    calc
      ∑ x ∈ S, (TemporalGraph.degreeIn G t x (Finset.univ \ S) : ℝ) / (2 : ℝ)
        = (2 : ℝ)⁻¹ * ∑ x ∈ S, (TemporalGraph.degreeIn G t x (Finset.univ \ S) : ℝ) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro x hx
            rw [div_eq_mul_inv, mul_comm]
      _ = (2 : ℝ)⁻¹ * (TemporalGraph.edgesBetween G t S (Finset.univ \ S) : ℝ) := by
            rw [hsum_cut]
      _ = (TemporalGraph.edgesBetween G t S (Finset.univ \ S) : ℝ) / (2 : ℝ) := by
            rw [div_eq_mul_inv, mul_comm]
  have hsum_right :
      ∑ v ∈ Finset.univ \ S, (TemporalGraph.degreeIn G t v S : ℝ) / (2 : ℝ) =
        (TemporalGraph.edgesBetween G t (Finset.univ \ S) S : ℝ) / (2 : ℝ) := by
    calc
      ∑ v ∈ Finset.univ \ S, (TemporalGraph.degreeIn G t v S : ℝ) / (2 : ℝ)
        = (2 : ℝ)⁻¹ * ∑ v ∈ Finset.univ \ S, (TemporalGraph.degreeIn G t v S : ℝ) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro v hv
            rw [div_eq_mul_inv, mul_comm]
      _ = (2 : ℝ)⁻¹ * (TemporalGraph.edgesBetween G t (Finset.univ \ S) S : ℝ) := by
            rw [hsum_cut]
      _ = (TemporalGraph.edgesBetween G t (Finset.univ \ S) S : ℝ) / (2 : ℝ) := by
            rw [div_eq_mul_inv, mul_comm]
  -- edgesBetween(univ\S, S) = edgesBetween(S, univ\S) by adj symmetry
  have hcut_symm : (TemporalGraph.edgesBetween G t (Finset.univ \ S) S : ℝ) =
      (TemporalGraph.edgesBetween G t S (Finset.univ \ S) : ℝ) := by
    have hcut_symm_nat : TemporalGraph.edgesBetween G t (Finset.univ \ S) S =
        TemporalGraph.edgesBetween G t S (Finset.univ \ S) := by
      simp only [TemporalGraph.edgesBetween, SimpleGraph.edgesBetween, Finset.card_filter]
      refine Finset.sum_nbij' (fun x => (x.2, x.1)) (fun x => (x.2, x.1)) ?_ ?_ ?_ ?_ ?_ <;>
        simp [and_comm, SimpleGraph.adj_comm]
    exact_mod_cast hcut_symm_nat
  rw [hsum_left, hsum_right, hcut_symm]
  ring

end VoterModel

-- ════════════════════════════════════════════════════════════════════
-- Part 2 : VoterModel process: conditional-expectation form
-- ════════════════════════════════════════════════════════════════════

namespace TemporalGraph

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {G : TemporalGraph V}

/-! ### Integrability helpers -/

/-- Any `f : Finset V → ℝ` composed with a measurable `Ω → Finset V` is
integrable w.r.t. any finite measure, because `Finset V` is finite. -/
private lemma vm_integrable_comp (vm : VoterModelAbstract G 2 Ω)
    (f : Finset V → ℝ) (g : Ω → Finset V)
    (hg : Measurable g) : Integrable (fun ω => f (g ω)) vm.μ :=
  Integrable.of_bound
    ((measurable_of_finite f).comp hg).aestronglyMeasurable
    (∑ s : Finset V, ‖f s‖)
    (ae_of_all _ (fun ω => Finset.single_le_sum
      (fun s _ => norm_nonneg (f s))
      (Finset.mem_univ (g ω))))

/-- `vm.opinionZeroSet t` is measurable w.r.t. the ambient σ-algebra. -/
private lemma vm_A_measurable (vm : VoterModelAbstract G 2 Ω) (t : ℕ) :
    Measurable (vm.opinionZeroSet t) :=
  Measurable.of_comap_le (vm.A_meas t)

/-! ### Set-integral identity on ℱ_j-atoms -/

/-- On `B ∩ {vm.opinionZeroSet j = A₀}` where `B ∈ ℱ_j`, the integral of
`f(vm.opinionZeroSet (j+1) ω)` equals `(∫ A', f A' ∂stepDist₂(G,j,A₀)) · μ(B ∩ …)`.
This is the VoterModel analogue of `MarkovChain.setIntegral_atom_filtration`.
-/
private lemma vm_setIntegral_atom (vm : VoterModelAbstract G 2 Ω)
    (f : Finset V → ℝ) (j : ℕ) (B : Set Ω) (A₀ : Finset V)
    (hB : @MeasurableSet Ω (vm.ℱ j) B)
    (hmA : MeasurableSet (B ∩ {ω | vm.opinionZeroSet j ω = A₀})) :
    ∫ ω in B ∩ {ω | vm.opinionZeroSet j ω = A₀},
        f (vm.opinionZeroSet (j + 1) ω) ∂vm.μ =
      ∫ _ in B ∩ {ω | vm.opinionZeroSet j ω = A₀},
        (∫ A', f A'
          ∂(VoterModel.stepDist₂ G j A₀).toMeasure) ∂vm.μ := by
  -- RHS: the inner integral is constant, factor it out
  rw [setIntegral_congr_fun hmA
      (fun _ _ => rfl),
    integral_const, smul_eq_mul, measureReal_def,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    mul_comm]
  -- LHS: decompose over values of A(j+1)
  have hmP : ∀ A' : Finset V,
      MeasurableSet (B ∩ {ω | vm.opinionZeroSet j ω = A₀} ∩
        {ω | vm.opinionZeroSet (j + 1) ω = A'}) :=
    fun A' => hmA.inter
      ((vm_A_measurable vm (j + 1)) (measurableSet_singleton A'))
  have hBA_eq : B ∩ {ω | vm.opinionZeroSet j ω = A₀} =
      ⋃ A' : Finset V,
        B ∩ {ω | vm.opinionZeroSet j ω = A₀} ∩
          {ω | vm.opinionZeroSet (j + 1) ω = A'} := by
    ext ω; simp [eq_comm]
  conv_lhs => rw [hBA_eq]
  rw [integral_iUnion_fintype hmP
    (fun a b hab => Set.disjoint_left.mpr
      fun ω ha hb => hab (ha.2 ▸ hb.2))
    (fun A' =>
      (vm_integrable_comp vm f (vm.opinionZeroSet (j + 1))
        (vm_A_measurable vm (j + 1))).integrableOn)]
  -- On each piece, f(A(j+1,ω)) = f(A')
  have hcf : ∀ A',
      ∫ ω in B ∩ {ω | vm.opinionZeroSet j ω = A₀} ∩
          {ω | vm.opinionZeroSet (j + 1) ω = A'},
        f (vm.opinionZeroSet (j + 1) ω) ∂vm.μ =
      f A' * ((vm.μ : Measure _) (B ∩ {ω | vm.opinionZeroSet j ω = A₀} ∩
          {ω | vm.opinionZeroSet (j + 1) ω = A'})).toReal :=
    fun A' => by
      rw [setIntegral_congr_fun (hmP A')
          (fun ω hω => congr_arg f hω.2),
        integral_const, smul_eq_mul, mul_comm,
        measureReal_def,
        Measure.restrict_apply MeasurableSet.univ,
        Set.univ_inter]
  simp_rw [hcf]
  -- B ∩ {A j = A₀} is ℱ_j-measurable
  have hBs_filt :
      @MeasurableSet Ω
        (⨆ k ∈ Finset.Iic j,
          MeasurableSpace.comap (vm.opinionZeroSet k) ⊤)
        (B ∩ {ω | vm.opinionZeroSet j ω = A₀}) :=
    @MeasurableSet.inter _ _ _ _ (vm.fmeas_to_Asup hB)
      (Measurable.of_comap_le
        (le_iSup₂_of_le j
          (Finset.mem_Iic.mpr le_rfl) le_rfl)
        (measurableSet_singleton A₀))
  -- Apply markovProperty to compute each piece's measure
  have hpiece : ∀ A',
      (vm.μ : Measure _) (B ∩ {ω | vm.opinionZeroSet j ω = A₀} ∩
        {ω | vm.opinionZeroSet (j + 1) ω = A'}) =
      VoterModel.stepDist₂ G j A₀ A' *
        (vm.μ : Measure _) (B ∩ {ω | vm.opinionZeroSet j ω = A₀}) :=
    fun A' => by
      rw [vm.A_markovProperty j A' _ hBs_filt,
        setLIntegral_congr_fun hmA
          (fun ω hω => by rw [hω.2]),
        lintegral_const,
        Measure.restrict_apply MeasurableSet.univ,
        Set.univ_inter, mul_comm]
  simp_rw [hpiece, ENNReal.toReal_mul]
  -- Goal: ∑ A', f A' * ((stepDist₂ ..) A').toReal * μ(..).toReal
  --     = (∫ f d stepDist₂) * μ(..).toReal
  -- Factor out μ(..).toReal
  conv_lhs =>
    arg 2; ext A'
    rw [← mul_assoc]
  rw [← Finset.sum_mul]
  -- Now: (∑ f A' * (stepDist₂ A₀ A').toReal) * μ(..).toReal
  --    = (∫ f d stepDist₂) * μ(..).toReal
  -- Suffices to show the sums match
  congr 1
  -- Use PMF.integral_eq_sum to rewrite the integral
  rw [PMF.integral_eq_sum]
  simp only [smul_eq_mul]
  exact Finset.sum_congr rfl fun A' _ => mul_comm _ _

/-! ### Main theorem -/

/-- \label{lem:stepwise-edges-bound}

Let `G` be a temporal graph with fixed degrees and `vm` a voter model on
`G`. Let `(S_t : t ≥ 0)` be the minority set process (`vm.S`). For any
step index `j ≥ 0` and graph-snapshot time `t`:
`E[|e_t(S_{j+1}, S̄_{j+1}) − e_t(S_j, S̄_j)| | ℱ_j] ≤ e_j(S_j, S̄_j)`
a.s.

(LaTeX uses `j` for the post-step index and `j−1` for the pre-step index;
here `j` is the pre-step index and `j+1` the post-step index.) -/
theorem VoterModelAbstract.stepwise_edges_bound
    (G : TemporalGraphFixedDegree V)
    (vm : VoterModelAbstract G 2 Ω)
    -- j = pre-step index (LaTeX's j−1); t = graph-snapshot time (LaTeX's t)
    (j t : ℕ) :
    -- Conclusion: E[|e_t(S_{j+1}, S̄_{j+1}) − e_t(S_j, S̄_j)| | ℱ_j] ≤ e_j(S_j, S̄_j)  a.s.
    ∀ᵐ ω ∂(vm.μ : Measure _),
      (vm.μ : Measure _)[fun ω' =>
              |(edgesBetween G.toTemporalGraph t
                  (vm.S (j + 1) ω')
                  (univ \ vm.S (j + 1) ω') : ℝ)
              - (edgesBetween G.toTemporalGraph t
                  (vm.S j ω')
                  (univ \ vm.S j ω') : ℝ)|
          | vm.ℱ j] ω
      ≤ (vm.cutS j ω : ℝ) := by
  -- Rewrite using edgesBetween_minoritySet: vm.S = minoritySet, edgesBetween of minority = edgesBetween of A
  have hrewrite : (fun ω' =>
      |(edgesBetween G t
          (vm.S (j + 1) ω')
          (univ \ vm.S (j + 1) ω') : ℝ)
        - (edgesBetween G t
          (vm.S j ω')
          (univ \ vm.S j ω') : ℝ)|) =
    (fun ω' =>
      |(edgesBetween G t
          (vm.opinionZeroSet (j + 1) ω')
          (univ \ vm.opinionZeroSet (j + 1) ω') : ℝ)
        - (edgesBetween G t
          (vm.opinionZeroSet j ω')
          (univ \ vm.opinionZeroSet j ω') : ℝ)|) := by
    ext ω'
    simp only [VoterModelAbstract.S]
    rw [VoterModelAbstract.edgesBetween_minoritySet G.toTemporalGraph t (j + 1),
      VoterModelAbstract.edgesBetween_minoritySet G.toTemporalGraph t j]
  rw [hrewrite]
  -- Abbreviations
  let ecut : Finset V → ℝ := fun A =>
    (edgesBetween G t A (univ \ A) : ℝ)
  let hg : Finset V → ℝ := fun A₀ =>
    ∫ A', |ecut A' - ecut A₀|
      ∂(VoterModel.stepDist₂ G j A₀).toMeasure
  -- h(ω) = kernel average of |ecut(·) - ecut(A_j(ω))|
  set h : Ω → ℝ := fun ω => hg (vm.opinionZeroSet j ω) with hh_def
  -- Key facts
  have hAj_meas := vm_A_measurable vm j
  have hAj1_meas := vm_A_measurable vm (j + 1)
  have hint_ecut_j1 := vm_integrable_comp vm ecut _ hAj1_meas
  have hint_ecut_j := vm_integrable_comp vm ecut _ hAj_meas
  have hint_f : Integrable
      (fun ω => |ecut (vm.opinionZeroSet (j + 1) ω) -
        ecut (vm.opinionZeroSet j ω)|) vm.μ :=
    (hint_ecut_j1.sub hint_ecut_j).abs
  have hint_h : Integrable h vm.μ :=
    vm_integrable_comp vm hg _ hAj_meas
  have hAj_filt :
      @Measurable Ω (Finset V) (vm.ℱ j) ⊤ (vm.opinionZeroSet j) :=
    (vm.A_stronglyAdapted j).measurable
  -- Step 1: Show h =ᵐ E[f|ℱ_j] via set integral identity
  have hset_eq : ∀ B : Set Ω,
      @MeasurableSet Ω (vm.ℱ j) B → (vm.μ : Measure _) B < ⊤ →
      ∫ ω in B, h ω ∂vm.μ =
      ∫ ω in B, |ecut (vm.opinionZeroSet (j + 1) ω) -
        ecut (vm.opinionZeroSet j ω)| ∂vm.μ := by
    intro B hB _
    have hBm := vm.ℱ.le j _ hB
    have hmA₀ : ∀ A₀ : Finset V,
        MeasurableSet (B ∩ {ω | vm.opinionZeroSet j ω = A₀}) :=
      fun A₀ => hBm.inter
        (hAj_meas (measurableSet_singleton A₀))
    have hpw : Pairwise fun a b =>
        Disjoint (B ∩ {ω | vm.opinionZeroSet j ω = a})
          (B ∩ {ω | vm.opinionZeroSet j ω = b}) :=
      fun a b hab => Set.disjoint_left.mpr
        fun ω ha hb => hab (ha.2 ▸ hb.2)
    have hB_eq : B = ⋃ A₀ : Finset V,
        B ∩ {ω | vm.opinionZeroSet j ω = A₀} := by
      ext ω; simp [eq_comm]
    rw [hB_eq,
      integral_iUnion_fintype hmA₀ hpw
        (fun _ => hint_h.integrableOn),
      integral_iUnion_fintype hmA₀ hpw
        (fun _ => hint_f.integrableOn)]
    refine Finset.sum_congr rfl fun A₀ _ => ?_
    -- On the atom: h(ω) = hg(A₀) is constant
    have hlhs : ∫ ω in B ∩ {ω | vm.opinionZeroSet j ω = A₀}, h ω ∂vm.μ =
        ∫ ω in B ∩ {ω | vm.opinionZeroSet j ω = A₀}, hg A₀ ∂vm.μ :=
      setIntegral_congr_fun (hmA₀ A₀)
        (fun ω hω => by show hg (vm.opinionZeroSet j ω) = hg A₀; rw [hω.2])
    -- Rewrite RHS: A_j(ω) = A₀ on the atom
    have hrhs : ∫ ω in B ∩ {ω | vm.opinionZeroSet j ω = A₀},
        |ecut (vm.opinionZeroSet (j + 1) ω) - ecut (vm.opinionZeroSet j ω)| ∂vm.μ =
      ∫ ω in B ∩ {ω | vm.opinionZeroSet j ω = A₀},
        |ecut (vm.opinionZeroSet (j + 1) ω) - ecut A₀| ∂vm.μ :=
      setIntegral_congr_fun (hmA₀ A₀)
        (fun ω hω => by rw [show vm.opinionZeroSet j ω = A₀ from hω.2])
    rw [hlhs, hrhs]
    exact (vm_setIntegral_atom vm
      (fun A' => |ecut A' - ecut A₀|)
      j B A₀ hB (hmA₀ A₀)).symm
  -- Conclude h =ᵐ E[f|ℱ_j]
  have hm_h : AEStronglyMeasurable[vm.ℱ j] h vm.μ :=
    ((measurable_of_finite hg).comp
      hAj_filt).aestronglyMeasurable
  have heq : h =ᵐ[(vm.μ : Measure _)]
      (vm.μ : Measure _)[fun ω => |ecut (vm.opinionZeroSet (j + 1) ω) -
        ecut (vm.opinionZeroSet j ω)| | vm.ℱ j] :=
    ae_eq_condExp_of_forall_setIntegral_eq
      (vm.ℱ.le j) hint_f
      (fun _ _ _ => hint_h.integrableOn)
      hset_eq hm_h
  -- Step 2: h ω ≤ cutS j ω pointwise, by inlining the PMF-level bound
  have hbound : ∀ ω, h ω ≤ (vm.cutS j ω : ℝ) := by
    intro ω
    show hg (vm.opinionZeroSet j ω) ≤ _
    rw [VoterModelAbstract.cutS_eq_edgesBetween_A]
    -- Inline the PMF-level bound (was: stepwise_edges_bound_old G hfix (vm.opinionZeroSet j ω) j t)
    -- Step 1: pointwise bound
    have hpw' : ∀ S' : Finset V,
        |((edgesBetween G.toTemporalGraph t S' (Finset.univ \ S') : ℝ) -
          (edgesBetween G.toTemporalGraph t (vm.opinionZeroSet j ω)
            (Finset.univ \ vm.opinionZeroSet j ω) : ℝ))| ≤
        ∑ v ∈ vm.opinionZeroSet j ω ∆ S', (TemporalGraph.degree G.toTemporalGraph t v : ℝ) :=
      fun S' => VoterModel.edgesBetween_change_abs_bound G.toTemporalGraph t
        (vm.opinionZeroSet j ω) S'
    -- Step 2: integrate
    have hmono' :
        hg (vm.opinionZeroSet j ω) ≤
        ∫ S', (∑ v ∈ vm.opinionZeroSet j ω ∆ S', (TemporalGraph.degree G t v : ℝ))
          ∂((VoterModel.stepDist₂ G j (vm.opinionZeroSet j ω)).toMeasure) := by
      show ∫ A', |ecut A' - ecut (vm.opinionZeroSet j ω)|
              ∂(VoterModel.stepDist₂ G j (vm.opinionZeroSet j ω)).toMeasure ≤ _
      rw [PMF.integral_eq_sum, PMF.integral_eq_sum]
      apply Finset.sum_le_sum
      intro S' _
      apply smul_le_smul_of_nonneg_left
      · exact hpw' S'
      · exact ENNReal.toReal_nonneg
    -- Step 3: degree sum integral = cut
    linarith [VoterModel.expected_swap_degree_sum G (vm.opinionZeroSet j ω) j t]
  -- Combine
  filter_upwards [heq] with ω hω
  rw [← hω]; exact hbound ω

end TemporalGraph
