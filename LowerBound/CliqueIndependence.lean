module

import VoterProcess.Expectation
public import LowerBound.StaticClique

/-! ## K_{2k} clique symmetry and boundary-pair independence

This file provides two groups of lemmas used in the lower-bound martingale proof:

**Phase A — Clique symmetry**: The voter model on a single K_{2k} clique is symmetric
under the complement involution: `P[reaching univ | start S] = P[reaching ∅ | start S̄]`.
Concretely, `stepDist₂` commutes with the complement-on-clique operation.

**Phase C — Boundary-pair independence**: The joint evolution of two *disjoint* cliques
`cliqueFinset aL` and `cliqueFinset aR` over one interval factors as a product of marginals.

## Main results
- `cliqueComplement` — complement-on-clique operation.
- `stepDist₂_clique_complement_symmetric` — one-step symmetry.
- `opinionProcess₂_boundary_pair_factors` — joint factorization for two disjoint cliques.
-/

@[expose] public section

noncomputable section

namespace TemporalGraph.VoterProcess.LowerBound

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators

/-! ### Phase A: K_{2k} complement symmetry -/

/-! ### Helpers for clique complement symmetry -/

/-! ### Phase C: Boundary-pair joint independence -/

/-- `stepDist₂Aux` is invariant under list permutation.
    (Private copy from SubProcess.lean — same proof.) -/
private theorem stepDist₂Aux_perm_ci
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraph V) (t : ℕ) (S : Finset V)
    {l₁ l₂ : List V} (h : List.Perm l₁ l₂) :
    VoterModel.stepDist₂Aux G t S l₁ = VoterModel.stepDist₂Aux G t S l₂ := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [VoterModel.stepDist₂Aux, ih]
  | swap u w l =>
    simp only [VoterModel.stepDist₂Aux]
    rw [PMF.bind_bind, PMF.bind_bind]
    apply congr_arg ((VoterModel.stepDist₂Aux G t S l).bind)
    funext T
    rw [PMF.bind_map, PMF.bind_map]
    apply PMF.ext
    intro T'
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
    rw [hRHS_form, hLHS_form]
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

/-! ### Phase D: Static-clique balanced absorption symmetry

The voter dynamics on the static clique `K_{2k}` is invariant under any permutation
`σ : CliqueVertex k ≃ CliqueVertex k` (because the underlying graph is the complete
graph, on which every permutation is an automorphism). In particular, for any
"balanced" initial state `T₀` with `|T₀| = k`, the symmetric automorphism that
exchanges the two halves of the clique maps `T₀` to its complement; combined with
the standard complement symmetry of the voter dynamics, this yields equal
absorption probabilities at `Finset.univ` and at `∅`. -/

/-- Complement-symmetry of the iterated opinion process (private copy from
    `DeterministicFiber.lean` to avoid an upward dependency). -/
private lemma opinionProcess₂_complement_full
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraph V) (t₀ : ℕ) (Δ : ℕ) (a : Finset V) :
    VoterModel.opinionProcess₂ G t₀ Δ (Finset.univ \ a) =
      (VoterModel.opinionProcess₂ G t₀ Δ a).map (fun T => Finset.univ \ T) := by
  induction Δ with
  | zero => simp [VoterModel.opinionProcess₂, PMF.pure_map]
  | succ Δ' ih =>
    show (VoterModel.opinionProcess₂ G t₀ Δ' (Finset.univ \ a)).bind
            (fun S' => VoterModel.stepDist₂ G (t₀ + Δ') S') =
        ((VoterModel.opinionProcess₂ G t₀ Δ' a).bind
            (fun S' => VoterModel.stepDist₂ G (t₀ + Δ') S')).map (fun T => Finset.univ \ T)
    rw [ih, PMF.bind_map, PMF.map_bind]
    congr 1
    funext T
    exact VoterModel.stepDist₂_complement G (t₀ + Δ') T

/-! ### Static-clique permutation invariance -/

/-- For an `Equiv σ : V ≃ V` and a finset `s : Finset V`, the PMF
    `PMF.uniformOfFinset (s.image σ) _` equals `(PMF.uniformOfFinset s _).map σ`. -/
private lemma uniformOfFinset_image_equiv {α : Type*} [DecidableEq α] [Fintype α]
    (σ : α ≃ α) (s : Finset α) (hs : s.Nonempty) :
    PMF.map σ (PMF.uniformOfFinset s hs) =
      PMF.uniformOfFinset (s.image σ) (hs.image σ) := by
  apply PMF.ext; intro b
  rw [PMF.map_apply, PMF.uniformOfFinset_apply]
  rw [tsum_fintype]
  by_cases hb : b ∈ s.image σ
  · -- Only `σ.symm b` contributes.
    have hbpre : σ.symm b ∈ s := by
      rcases Finset.mem_image.mp hb with ⟨a, ha, rfl⟩
      simpa using ha
    rw [Finset.sum_eq_single (σ.symm b)]
    · have heq : b = σ (σ.symm b) := by simp
      rw [if_pos heq, PMF.uniformOfFinset_apply_of_mem hs hbpre, if_pos hb,
          Finset.card_image_of_injective s σ.injective]
    · intro a _ ha
      have hne : b ≠ σ a := by
        intro h
        apply ha
        have : σ.symm b = σ.symm (σ a) := by rw [h]
        simp at this
        exact this.symm
      simp [hne]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · -- All terms vanish.
    rw [if_neg hb]
    apply Finset.sum_eq_zero
    intro a _
    by_cases hab : b = σ a
    · by_cases has : a ∈ s
      · exfalso
        apply hb
        rw [hab]
        exact Finset.mem_image.mpr ⟨a, has, rfl⟩
      · rw [if_pos hab, PMF.uniformOfFinset_apply_of_notMem hs has]
    · simp [hab]

/-- The static-clique neighborhood is invariant under vertex permutations:
    `(staticCliqueGraph k).neighborFinset t (σ v)` is the image under σ of
    `(staticCliqueGraph k).neighborFinset t v`. -/
private lemma neighborFinset_staticClique_perm (k : ℕ) [NeZero k]
    (σ : CliqueVertex k ≃ CliqueVertex k) (t : ℕ) (v : CliqueVertex k) :
    (staticCliqueGraph k).neighborFinset t (σ v) =
      ((staticCliqueGraph k).neighborFinset t v).image σ := by
  rw [neighbors_staticClique, neighbors_staticClique]
  rw [Finset.image_erase σ.injective, Finset.image_univ_equiv]

/-- The static-clique neighborhood of a vertex is nonempty: for `CliqueVertex k = Fin (2k)`
    with `NeZero k` (so `k ≥ 1`, hence `2k ≥ 2`). -/
private lemma neighborFinset_staticClique_nonempty (k : ℕ) [NeZero k]
    (t : ℕ) (v : CliqueVertex k) :
    ((staticCliqueGraph k).neighborFinset t v).Nonempty := by
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  rw [neighbors_staticClique]
  apply Finset.Nontrivial.erase_nonempty
  rw [Finset.univ_nontrivial_iff]
  rw [show (CliqueVertex k : Type) = Fin (2 * k) from rfl]
  exact Fin.nontrivial_iff_two_le.mpr (by omega)

/-- Single-vertex permutation equivariance for `nextOpinionDist₂` on the static clique:
    `nextOpinionDist₂ (staticCliqueGraph k) t (S.image σ) (σ v) =
       nextOpinionDist₂ (staticCliqueGraph k) t S v`. -/
private lemma nextOpinionDist₂_staticClique_perm
    (k : ℕ) [NeZero k] (σ : CliqueVertex k ≃ CliqueVertex k)
    (t : ℕ) (S : Finset (CliqueVertex k)) (v : CliqueVertex k) :
    VoterModel.nextOpinionDist₂ (staticCliqueGraph k) t (S.image σ) (σ v) =
      VoterModel.nextOpinionDist₂ (staticCliqueGraph k) t S v := by
  have hN : ((staticCliqueGraph k).neighborFinset t v).Nonempty :=
    neighborFinset_staticClique_nonempty k t v
  have hN' : ((staticCliqueGraph k).neighborFinset t (σ v)).Nonempty :=
    neighborFinset_staticClique_nonempty k t (σ v)
  rw [VoterModel.nextOpinionDist₂_eq_bind_of_nonempty _ _ _ _ hN]
  rw [VoterModel.nextOpinionDist₂_eq_bind_of_nonempty _ _ _ _ hN']
  congr 1
  funext b
  cases b
  · simp only [cond_false]
    -- LHS: (uniformOfFinset (nbr (σ v)) hN').map (fun w => decide (w ∈ S.image σ))
    -- RHS: (uniformOfFinset (nbr v) hN).map (fun w => decide (w ∈ S))
    have hNbr : (staticCliqueGraph k).neighborFinset t (σ v) =
        ((staticCliqueGraph k).neighborFinset t v).image σ :=
      neighborFinset_staticClique_perm k σ t v
    have hN_img : (((staticCliqueGraph k).neighborFinset t v).image σ).Nonempty :=
      hN.image σ
    -- Rewrite the LHS uniformOfFinset via congruence in its first argument.
    have hPMFeq :
        PMF.uniformOfFinset ((staticCliqueGraph k).neighborFinset t (σ v)) hN' =
        PMF.uniformOfFinset (((staticCliqueGraph k).neighborFinset t v).image σ) hN_img := by
      congr 1
    rw [hPMFeq]
    rw [← uniformOfFinset_image_equiv σ _ hN]
    rw [PMF.map_comp]
    congr 1
    funext w
    simp only [Function.comp_apply]
    exact decide_eq_decide.mpr (Function.Injective.mem_finset_image σ.injective)
  · simp only [cond_true]
    congr 1
    exact decide_eq_decide.mpr (Function.Injective.mem_finset_image σ.injective)

/-- `stepDist₂Aux` on the static clique is invariant under vertex permutation:
    pulling σ through both the initial state and the list of vertices preserves the PMF
    (up to applying σ to outputs). -/
private lemma stepDist₂Aux_staticClique_perm
    (k : ℕ) [NeZero k] (σ : CliqueVertex k ≃ CliqueVertex k)
    (t : ℕ) (S : Finset (CliqueVertex k)) (l : List (CliqueVertex k)) :
    VoterModel.stepDist₂Aux (staticCliqueGraph k) t (S.image σ) (l.map σ) =
      (VoterModel.stepDist₂Aux (staticCliqueGraph k) t S l).map (fun T => T.image σ) := by
  induction l with
  | nil => simp [VoterModel.stepDist₂Aux, PMF.pure_map]
  | cons w ws ih =>
    simp only [List.map_cons, VoterModel.stepDist₂Aux]
    rw [PMF.map_bind]
    rw [ih]
    rw [PMF.bind_map]
    -- Now both sides are bind over the same PMF; compare the inner functions
    congr 1
    funext T
    -- LHS: (nextOpinionDist₂ .. t (S.image σ) (σ w)).map (fun b => cond b (insert (σ w) (T.image σ)) (T.image σ))
    -- RHS: ((nextOpinionDist₂ .. t S w).map (fun b => cond b (insert w T) T)).map (fun U => U.image σ)
    rw [PMF.map_comp]
    rw [nextOpinionDist₂_staticClique_perm k σ t S w]
    show PMF.map (fun isZero => bif isZero then insert (σ w) (T.image σ) else T.image σ)
            (VoterModel.nextOpinionDist₂ (staticCliqueGraph k) t S w) =
         PMF.map (Finset.image σ ∘ fun isZero => bif isZero then insert w T else T)
            (VoterModel.nextOpinionDist₂ (staticCliqueGraph k) t S w)
    congr 1
    funext b
    cases b
    · simp
    · simp [Finset.image_insert]

/-- `stepDist₂` on the static clique is invariant under vertex permutation. -/
private lemma stepDist₂_staticClique_perm
    (k : ℕ) [NeZero k] (σ : CliqueVertex k ≃ CliqueVertex k)
    (t : ℕ) (S : Finset (CliqueVertex k)) :
    VoterModel.stepDist₂ (staticCliqueGraph k) t (S.image σ) =
      (VoterModel.stepDist₂ (staticCliqueGraph k) t S).map (fun T => T.image σ) := by
  rw [← VoterModel.stepDist₂Aux_eq_stepDist₂ (staticCliqueGraph k) t (S.image σ),
      ← VoterModel.stepDist₂Aux_eq_stepDist₂ (staticCliqueGraph k) t S]
  -- Need stepDist₂Aux on .toList = stepDist₂Aux on (.toList.map σ) up to perm of list
  have hperm : List.Perm ((Finset.univ : Finset (CliqueVertex k)).toList.map σ)
                 (Finset.univ : Finset (CliqueVertex k)).toList := by
    apply List.perm_of_nodup_nodup_toFinset_eq
    · refine List.Nodup.map σ.injective ?_
      exact Finset.nodup_toList _
    · exact Finset.nodup_toList _
    · ext x
      simp only [Finset.toList_toFinset, List.mem_toFinset, List.mem_map, Finset.mem_toList,
        Finset.mem_univ, true_and, iff_true]
      exact ⟨σ.symm x, by simp⟩
  calc VoterModel.stepDist₂Aux (staticCliqueGraph k) t (S.image σ)
        (Finset.univ : Finset (CliqueVertex k)).toList
      = VoterModel.stepDist₂Aux (staticCliqueGraph k) t (S.image σ)
          ((Finset.univ : Finset (CliqueVertex k)).toList.map σ) := by
        exact (stepDist₂Aux_perm_ci (staticCliqueGraph k) t (S.image σ) hperm).symm
    _ = (VoterModel.stepDist₂Aux (staticCliqueGraph k) t S
          (Finset.univ : Finset (CliqueVertex k)).toList).map (fun T => T.image σ) :=
        stepDist₂Aux_staticClique_perm k σ t S _

/-- `opinionProcess₂` on the static clique is invariant under vertex permutation. -/
private lemma opinionProcess₂_staticClique_perm
    (k : ℕ) [NeZero k] (σ : CliqueVertex k ≃ CliqueVertex k)
    (t n : ℕ) (S : Finset (CliqueVertex k)) :
    VoterModel.opinionProcess₂ (staticCliqueGraph k) t n (S.image σ) =
      (VoterModel.opinionProcess₂ (staticCliqueGraph k) t n S).map (fun T => T.image σ) := by
  induction n with
  | zero => simp [VoterModel.opinionProcess₂, PMF.pure_map]
  | succ n' ih =>
    show (VoterModel.opinionProcess₂ (staticCliqueGraph k) t n' (S.image σ)).bind
            (fun S' => VoterModel.stepDist₂ (staticCliqueGraph k) (t + n') S') =
          ((VoterModel.opinionProcess₂ (staticCliqueGraph k) t n' S).bind
            (fun S' => VoterModel.stepDist₂ (staticCliqueGraph k) (t + n') S')).map
              (fun T => T.image σ)
    rw [ih, PMF.bind_map, PMF.map_bind]
    congr 1
    funext T
    exact stepDist₂_staticClique_perm k σ (t + n') T

/-- An involution `σ : CliqueVertex k ≃ CliqueVertex k` that maps a balanced subset
    `T₀` (with `|T₀| = k`) to its complement `Finset.univ \ T₀`. -/
private lemma exists_perm_image_eq_compl
    (k : ℕ) [NeZero k] (T₀ : Finset (CliqueVertex k)) (hT₀ : T₀.card = k) :
    ∃ σ : CliqueVertex k ≃ CliqueVertex k,
      T₀.image σ = Finset.univ \ T₀ := by
  classical
  -- The complement has cardinality k.
  have hcompl_card : (Finset.univ \ T₀).card = k := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ T₀), Finset.card_univ]
    show Fintype.card (CliqueVertex k) - T₀.card = k
    have : Fintype.card (CliqueVertex k) = 2 * k := Fintype.card_fin _
    rw [this, hT₀]; omega
  -- Get e : ↥T₀ ≃ ↥(univ \ T₀).
  have hcard_eq : T₀.card = (Finset.univ \ T₀).card := by rw [hT₀, hcompl_card]
  let e : ↥T₀ ≃ ↥(Finset.univ \ T₀) := Finset.equivOfCardEq hcard_eq
  -- Build σ : CliqueVertex k → CliqueVertex k as an involution.
  let f : CliqueVertex k → CliqueVertex k := fun v =>
    if hv : v ∈ T₀ then (e ⟨v, hv⟩).val
    else if hv' : v ∈ Finset.univ \ T₀ then (e.symm ⟨v, hv'⟩).val
    else v
  -- Compute f on each branch.
  have hfT : ∀ v (hv : v ∈ T₀), f v = (e ⟨v, hv⟩).val := by
    intro v hv; show (if hv : v ∈ T₀ then (e ⟨v, hv⟩).val else _) = _; rw [dif_pos hv]
  have hfC : ∀ v (hv' : v ∈ Finset.univ \ T₀), f v = (e.symm ⟨v, hv'⟩).val := by
    intro v hv'
    have hvT : v ∉ T₀ := (Finset.mem_sdiff.mp hv').2
    show (if hv : v ∈ T₀ then (e ⟨v, hv⟩).val
            else if hv' : v ∈ Finset.univ \ T₀ then (e.symm ⟨v, hv'⟩).val else v) = _
    rw [dif_neg hvT, dif_pos hv']
  -- Step 1: f maps T₀ into T₀ᶜ and T₀ᶜ into T₀.
  have hf_T : ∀ v ∈ T₀, f v ∈ Finset.univ \ T₀ := by
    intro v hv
    rw [hfT v hv]
    exact (e ⟨v, hv⟩).property
  have hf_C : ∀ v ∈ Finset.univ \ T₀, f v ∈ T₀ := by
    intro v hv
    rw [hfC v hv]
    exact (e.symm ⟨v, hv⟩).property
  -- Step 2: f is an involution.
  have hff : ∀ v, f (f v) = v := by
    intro v
    by_cases hv : v ∈ T₀
    · have h1 := hfT v hv
      have hfv_compl : f v ∈ Finset.univ \ T₀ := hf_T v hv
      rw [hfC (f v) hfv_compl]
      have h3 : (⟨f v, hfv_compl⟩ : ↥(Finset.univ \ T₀)) = e ⟨v, hv⟩ :=
        Subtype.ext h1
      rw [h3]
      simp
    · by_cases hv' : v ∈ Finset.univ \ T₀
      · have h1 := hfC v hv'
        have hfv_T : f v ∈ T₀ := hf_C v hv'
        rw [hfT (f v) hfv_T]
        have h3 : (⟨f v, hfv_T⟩ : ↥T₀) = e.symm ⟨v, hv'⟩ :=
          Subtype.ext h1
        rw [h3]
        simp
      · -- v ∉ T₀ and v ∉ univ \ T₀, impossible
        exfalso
        apply hv'
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hv⟩
  -- Build the Equiv.
  refine ⟨⟨f, f, hff, hff⟩, ?_⟩
  -- Show T₀.image f = univ \ T₀
  ext y
  simp only [Finset.mem_image, Finset.mem_sdiff, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hfx_compl : f x ∈ Finset.univ \ T₀ := hf_T x hx
    exact (Finset.mem_sdiff.mp hfx_compl).2
  · intro hy
    have hy_compl : y ∈ Finset.univ \ T₀ := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hy⟩
    refine ⟨f y, hf_C y hy_compl, ?_⟩
    exact hff y

/-- Static-clique balanced absorption symmetry. For any `T₀ ⊆ CliqueVertex k` with
`|T₀| = k`, the probability that `opinionProcess₂ (staticCliqueGraph k) t n T₀`
reaches `Finset.univ` equals the probability it reaches `∅`.

**Math content**: For balanced `T₀` (`|T₀| = k = (2k)/2`), the complement
`Finset.univ \ T₀` also has cardinality `k`. Choose a permutation
`σ : CliqueVertex k ≃ CliqueVertex k` with `T₀.image σ = Finset.univ \ T₀` (exists
because both finsets have the same size). Since `staticCliqueGraph k` is the
complete graph, `σ` is a graph automorphism and so the voter dynamics is
σ-equivariant. Combined with the complement involution on the voter dynamics
(`VoterModel.stepDist₂_complement`, lifted inductively to `opinionProcess₂` via
`opinionProcess₂_complement_full`), this gives
`opP T₀ univ = opP (univ \ T₀) ∅ = opP T₀ ∅`. -/
theorem opinionProcess₂_staticClique_balanced_absorption_symmetric
    (k : ℕ) [NeZero k] (_hk : 1 ≤ k)
    (t n : ℕ) (T₀ : Finset (CliqueVertex k)) (hT₀ : T₀.card = k) :
    VoterModel.opinionProcess₂ (staticCliqueGraph k) t n T₀ Finset.univ =
      VoterModel.opinionProcess₂ (staticCliqueGraph k) t n T₀ ∅ := by
  -- Step 1: by complement-map, opP T₀ univ = opP (univ \ T₀) ∅
  -- Indeed: P (opP T₀) univ = P (opP T₀.map (univ\·)) ∅ = P (opP (univ\T₀)) ∅
  -- by opinionProcess₂_complement_full applied with a := T₀.
  have h1 : VoterModel.opinionProcess₂ (staticCliqueGraph k) t n T₀ Finset.univ =
            VoterModel.opinionProcess₂ (staticCliqueGraph k) t n (Finset.univ \ T₀) ∅ := by
    rw [opinionProcess₂_complement_full (staticCliqueGraph k) t n T₀]
    rw [PMF.map_apply]
    rw [tsum_eq_single Finset.univ]
    · simp
    · intro T hT
      have : ¬ (∅ : Finset (CliqueVertex k)) = Finset.univ \ T := fun h => by
        have h' : Finset.univ \ T = ∅ := h.symm
        have hT_eq : T = Finset.univ :=
          Finset.eq_univ_of_forall fun x => by
            by_contra hx
            have : x ∈ Finset.univ \ T := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx⟩
            rw [h'] at this; exact Finset.notMem_empty _ this
        exact hT hT_eq
      simp [this]
  -- Step 2: get σ : CliqueVertex k ≃ CliqueVertex k with T₀.image σ = univ \ T₀.
  obtain ⟨σ, hσ⟩ := exists_perm_image_eq_compl k T₀ hT₀
  -- Step 3: by perm-invariance, opP (univ \ T₀) ∅ = opP T₀ ∅.
  -- (opP T₀ ∅).map (image σ) = opP (T₀.image σ) (∅.image σ) = opP (univ \ T₀) ∅
  -- so opP (univ \ T₀) S' = opP T₀ (σ.symm.image S') (using injectivity).
  -- In particular at S' = ∅: σ.symm.image ∅ = ∅.
  have hperm : VoterModel.opinionProcess₂ (staticCliqueGraph k) t n T₀ ∅ =
                VoterModel.opinionProcess₂ (staticCliqueGraph k) t n (Finset.univ \ T₀) ∅ := by
    have hkey := opinionProcess₂_staticClique_perm k σ t n T₀
    -- hkey: opP (T₀.image σ) = (opP T₀).map (image σ)
    -- so opP (univ \ T₀) = (opP T₀).map (image σ)
    rw [hσ] at hkey
    rw [hkey, PMF.map_apply]
    -- Sum over T with (T.image σ) = ∅
    rw [tsum_eq_single ∅]
    · simp [Finset.image_empty]
    · intro T hT
      -- Need: (if ∅ = T.image σ then p T else 0) = 0
      -- Suffices to show ∅ ≠ T.image σ
      have hne : (∅ : Finset (CliqueVertex k)) ≠ T.image σ := by
        intro h
        apply hT
        -- h : ∅ = T.image σ, so T.image σ = ∅. Since σ injective, T = ∅.
        have h' : T.image σ = ∅ := h.symm
        by_contra hT_ne
        obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hT_ne
        have hσx : σ x ∈ T.image σ := Finset.mem_image.mpr ⟨x, hx, rfl⟩
        rw [h'] at hσx
        exact (Finset.notMem_empty _) hσx
      simp [hne]
  rw [h1, ← hperm]

end TemporalGraph.VoterProcess.LowerBound
