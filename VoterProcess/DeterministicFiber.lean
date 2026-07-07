module

import VoterProcess.TwoOpinion
public import VoterProcess.Step

/-! ## DeterministicFiber

σ-algebra bridge: if a stopping time equals a constant deterministically, its
stopped σ-algebra equals the filtration at that time step.

## Main results
- `multistep_markov_filtration₂`: iterated Markov property over the filtration `ℱ_t`.
- `cylinder_markov_finite_tuple`: finite-tuple cylinder factorization of the opinion process.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory TemporalGraph

namespace VoterModel

/-- Iterated Markov property over the filtration `ℱ_t`.

For any `B ∈ ℱ_t`, the joint event `B ∩ {A_{t+Δ} = S'}` has probability
`∫_B (opinionProcess₂ G t Δ (A_t ω)) S' dμ`.

Proof by induction on `Δ`. The base case (`Δ = 0`) reduces to
`B ∩ {A_t = S'}` and an indicator computation. The step case partitions over
the atoms `{A_{t+Δ'} = T'}` and applies the one-step `markovProperty` field
together with the inductive hypothesis.

Relocated from `Spec/TheoremUpperBound.lean` (was `private`) so it can also
be used in `condExp_const_voter_fiber` (L58). -/
theorem multistep_markov_filtration₂
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (G : TemporalGraph V) (vm : TemporalGraph.VoterModelAbstract G 2 Ω)
    (t Δ : ℕ) (S' : Finset V) (B : Set Ω)
    (hB : @MeasurableSet Ω (vm.ℱ t) B) :
    (vm.μ : Measure _) (B ∩ {ω | vm.opinionZeroSet (t + Δ) ω = S'}) =
      ∫⁻ ω in B, (VoterModel.opinionProcess₂ G t Δ (vm.opinionZeroSet t ω)) S' ∂vm.μ := by
  -- Measurability helpers
  have hAmeas : ∀ (j : ℕ), @Measurable Ω (Finset V) mΩ ⊤ (vm.opinionZeroSet j) :=
    fun j s _ => vm.A_meas j _ ⟨s, trivial, rfl⟩
  have hAset_meas : ∀ (j : ℕ) (T : Finset V), MeasurableSet {ω : Ω | vm.opinionZeroSet j ω = T} :=
    fun j T => hAmeas j (measurableSet_singleton T)
  -- Ambient measurability of B (from vm.ℱ t ≤ mΩ)
  have hBm : MeasurableSet B := vm.ℱ.le t B hB
  -- Measurability of opinionProcess₂ values as functions on Ω
  have hmeas_op : ∀ (n : ℕ) (T' : Finset V),
      Measurable (fun ω => (VoterModel.opinionProcess₂ G t n (vm.opinionZeroSet t ω)) T') :=
    fun n T' => (measurable_of_finite (fun s => (VoterModel.opinionProcess₂ G t n s) T')).comp
      (hAmeas t)
  induction Δ generalizing S' with
  | zero =>
    -- opinionProcess₂ G t 0 a = PMF.pure a, so (PMF.pure a) S' = if S' = a then 1 else 0
    simp only [VoterModel.opinionProcess₂, PMF.pure_apply, Nat.add_zero]
    -- Goal: (vm.μ : Measure _) (B ∩ {ω | vm.opinionZeroSet t ω = S'}) = ∫⁻ ω in B, if S' = vm.opinionZeroSet t ω then 1 else 0 ∂vm.μ
    have hbase : ∫⁻ (ω : Ω) in B, (if S' = vm.opinionZeroSet t ω then (1:ENNReal) else 0) ∂vm.μ
        = (vm.μ : Measure _) (B ∩ {x | vm.opinionZeroSet t x = S'}) := by
      have heq : ∀ ω, (if S' = vm.opinionZeroSet t ω then (1:ENNReal) else 0) =
          Set.indicator {x | vm.opinionZeroSet t x = S'} (fun _ => 1) ω :=
        fun ω => by simp [Set.indicator_apply, eq_comm]
      simp_rw [heq, setLIntegral_indicator (hAset_meas t S'), setLIntegral_one, Set.inter_comm]
    exact_mod_cast hbase.symm
  | succ Δ' ih =>
    -- Step case: t + (Δ' + 1) = (t + Δ') + 1
    show (vm.μ : Measure _) (B ∩ {ω | vm.opinionZeroSet ((t + Δ') + 1) ω = S'}) =
      ∫⁻ ω in B, (VoterModel.opinionProcess₂ G t (Δ' + 1) (vm.opinionZeroSet t ω)) S' ∂vm.μ
    -- opinionProcess₂ G t (Δ'+1) a S' = ∑' T', opinionProcess₂ G t Δ' a T' * stepDist₂ G (t+Δ') T' S'
    simp only [VoterModel.opinionProcess₂, PMF.bind_apply]
    -- Partition B ∩ {A(t+Δ'+1)=S'} over atoms {A(t+Δ')=T'}
    have hB_eq : B ∩ {ω | vm.opinionZeroSet ((t + Δ') + 1) ω = S'} =
        ⋃ T' : Finset V, B ∩ {ω | vm.opinionZeroSet (t + Δ') ω = T'} ∩ {ω | vm.opinionZeroSet ((t + Δ') + 1) ω = S'} := by
      ext ω; simp [eq_comm]
    have hpw : Pairwise fun (T1 T2 : Finset V) =>
        Disjoint (B ∩ {ω | vm.opinionZeroSet (t + Δ') ω = T1} ∩ {ω | vm.opinionZeroSet ((t + Δ') + 1) ω = S'})
                 (B ∩ {ω | vm.opinionZeroSet (t + Δ') ω = T2} ∩ {ω | vm.opinionZeroSet ((t + Δ') + 1) ω = S'}) :=
      fun T1 T2 hne => Set.disjoint_left.mpr fun ω h1 h2 => hne (h1.1.2 ▸ h2.1.2)
    have hmset : ∀ T' : Finset V,
        MeasurableSet (B ∩ {ω | vm.opinionZeroSet (t + Δ') ω = T'} ∩ {ω | vm.opinionZeroSet ((t + Δ') + 1) ω = S'}) :=
      fun T' => (hBm.inter (hAset_meas (t + Δ') T')).inter (hAset_meas ((t + Δ') + 1) S')
    -- LHS: partition over T'
    rw [hB_eq, measure_iUnion (fun T1 T2 hne => hpw hne) hmset]
    -- ℱ(t+Δ')-measurability of B (upgraded from ℱ t via filtration monotonicity)
    have hBt_meas : @MeasurableSet Ω (vm.ℱ (t + Δ')) B :=
      vm.ℱ.mono (Nat.le_add_right t Δ') B hB
    -- Apply markovProperty to each atom: μ(B∩{A(t+Δ')=T'}∩{A(t+Δ'+1)=S'}) = stepDist₂ T' S' * μ(B∩{...})
    have hcM : ∀ T' : Finset V,
        (vm.μ : Measure _) (B ∩ {ω | vm.opinionZeroSet (t + Δ') ω = T'} ∩ {ω | vm.opinionZeroSet ((t + Δ') + 1) ω = S'}) =
          (VoterModel.stepDist₂ G (t + Δ') T') S' * (vm.μ : Measure _) (B ∩ {ω | vm.opinionZeroSet (t + Δ') ω = T'}) := by
      intro T'
      have hBT'_filt : @MeasurableSet Ω (⨆ j ∈ Finset.Iic (t + Δ'),
          MeasurableSpace.comap (vm.opinionZeroSet j) ⊤) (B ∩ {ω | vm.opinionZeroSet (t + Δ') ω = T'}) := by
        apply @MeasurableSet.inter _ _ _ _ (vm.fmeas_to_Asup hBt_meas)
        exact Measurable.of_comap_le
          (le_iSup₂_of_le (t + Δ') (Finset.mem_Iic.mpr le_rfl) le_rfl)
          (measurableSet_singleton T')
      rw [vm.A_markovProperty (t + Δ') S' (B ∩ {ω | vm.opinionZeroSet (t + Δ') ω = T'}) hBT'_filt]
      rw [setLIntegral_congr_fun (hBm.inter (hAset_meas (t + Δ') T'))
          (fun ω hω => by rw [hω.2])]
      rw [setLIntegral_const, mul_comm]
    simp_rw [hcM]
    -- Apply IH: μ(B∩{A(t+Δ')=T'}) = ∫⁻ ω in B, opinionProcess₂ G t Δ' (A t ω) T' ∂μ
    simp_rw [ih]
    -- Pull constant stepDist₂ out of integral and commute ∑' with ∫⁻
    have hpull : ∀ T' : Finset V,
        (VoterModel.stepDist₂ G (t + Δ') T') S' *
            ∫⁻ (ω : Ω) in B, (VoterModel.opinionProcess₂ G t Δ' (vm.opinionZeroSet t ω)) T' ∂vm.μ =
          ∫⁻ (ω : Ω) in B,
            (VoterModel.stepDist₂ G (t + Δ') T') S' *
              (VoterModel.opinionProcess₂ G t Δ' (vm.opinionZeroSet t ω)) T' ∂vm.μ :=
      fun T' => (lintegral_const_mul _ (hmeas_op Δ' T')).symm
    trans (∑' T' : Finset V,
        ∫⁻ (ω : Ω) in B,
          (VoterModel.stepDist₂ G (t + Δ') T') S' *
            (VoterModel.opinionProcess₂ G t Δ' (vm.opinionZeroSet t ω)) T' ∂vm.μ)
    · congr 1; ext T'; exact hpull T'
    · rw [← lintegral_tsum (fun T' => ((hmeas_op Δ' T').const_mul _).aemeasurable.restrict)]
      congr 1; ext ω; apply tsum_congr; intro T'; ring

/-- Cylinder Markov identity: for any cylinder of opinion-set values at consecutive
post-`t` times, the joint measure factors as `μ(B)` times the path-product of
`stepDist₂`. Proved by induction on the path length, using `vm.A_markovProperty` at each
step. -/
theorem cylinder_markov_finite_tuple
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (G : TemporalGraph V) (vm : TemporalGraph.VoterModelAbstract G 2 Ω)
    (t : ℕ) (Δ : ℕ) (B : Set Ω) (hB : MeasurableSet[vm.ℱ t] B)
    (a : Finset V) (hBa : ∀ ω ∈ B, vm.opinionZeroSet t ω = a)
    (π : ℕ → Finset V) (hπ0 : π 0 = a) :
    (vm.μ : Measure _) (B ∩ ⋂ j ∈ Finset.range Δ, {ω | vm.opinionZeroSet (t + j + 1) ω = π (j + 1)})
      = (vm.μ : Measure _) B *
        ∏ j ∈ Finset.range Δ,
          (VoterModel.stepDist₂ G (t + j) (π j)) (π (j + 1)) := by
  -- Measurability helpers
  have hAmeas : ∀ (j : ℕ), @Measurable Ω (Finset V) mΩ ⊤ (vm.opinionZeroSet j) :=
    fun j s _ => vm.A_meas j _ ⟨s, trivial, rfl⟩
  have hAset_meas : ∀ (j : ℕ) (T : Finset V), MeasurableSet {ω : Ω | vm.opinionZeroSet j ω = T} :=
    fun j T => hAmeas j (measurableSet_singleton T)
  have hBm : MeasurableSet B := vm.ℱ.le t B hB
  induction Δ with
  | zero =>
    simp [Finset.range_zero, Set.iInter_of_empty, Set.inter_univ]
  | succ Δ' ih =>
    -- Peel off the last factor j = Δ' from the intersection.
    have hrange_succ : (Finset.range (Δ' + 1) : Finset ℕ) = insert Δ' (Finset.range Δ') :=
      Finset.range_add_one
    have hbiInter_eq :
        (⋂ j ∈ Finset.range (Δ' + 1), {ω : Ω | vm.opinionZeroSet (t + j + 1) ω = π (j + 1)}) =
          {ω | vm.opinionZeroSet (t + Δ' + 1) ω = π (Δ' + 1)} ∩
            ⋂ j ∈ Finset.range Δ', {ω : Ω | vm.opinionZeroSet (t + j + 1) ω = π (j + 1)} := by
      rw [hrange_succ, Finset.set_biInter_insert]
    -- Let B' be the partial cylinder; rewrite the LHS to μ(B' ∩ {A (t+Δ'+1) = π(Δ'+1)}).
    set B' : Set Ω :=
      B ∩ ⋂ j ∈ Finset.range Δ', {ω : Ω | vm.opinionZeroSet (t + j + 1) ω = π (j + 1)} with hB'_def
    have hLHS_eq :
        B ∩ ⋂ j ∈ Finset.range (Δ' + 1), {ω : Ω | vm.opinionZeroSet (t + j + 1) ω = π (j + 1)} =
          B' ∩ {ω | vm.opinionZeroSet (t + Δ' + 1) ω = π (Δ' + 1)} := by
      rw [hbiInter_eq, hB'_def]
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
      tauto
    -- Step 1: show B' is measurable w.r.t. ⨆ j ∈ Iic (t+Δ'), comap (A j) ⊤.
    have hB'_filt : @MeasurableSet Ω (⨆ j ∈ Finset.Iic (t + Δ'),
        MeasurableSpace.comap (vm.opinionZeroSet j) ⊤) B' := by
      have hB_in : @MeasurableSet Ω (⨆ j ∈ Finset.Iic (t + Δ'),
          MeasurableSpace.comap (vm.opinionZeroSet j) ⊤) B := by
        have : vm.ℱ t ≤ vm.ℱ (t + Δ') := vm.ℱ.mono (Nat.le_add_right t Δ')
        exact vm.fmeas_to_Asup (this B hB)
      refine MeasurableSet.inter hB_in ?_
      -- ⋂_{j ∈ range Δ'} {A (t+j+1) = π(j+1)} is measurable w.r.t. ⨆_{Iic (t+Δ')}.
      refine MeasurableSet.biInter (Finset.range Δ').countable_toSet ?_
      intro j hj
      have hj_lt : j < Δ' := Finset.mem_range.mp hj
      have hk_le : t + j + 1 ≤ t + Δ' := by omega
      -- {A (t+j+1) = π(j+1)} ∈ comap (A (t+j+1)) ⊤ ⊆ ⨆_{Iic (t+Δ')}.
      exact Measurable.of_comap_le
        (le_iSup₂_of_le (t + j + 1) (Finset.mem_Iic.mpr hk_le) le_rfl)
        (measurableSet_singleton (π (j + 1)))
    -- Step 2: apply markovProperty at time (t+Δ') with state π(Δ'+1) to B'.
    have hcM := vm.A_markovProperty (t + Δ') (π (Δ' + 1)) B' hB'_filt
    -- hcM : μ(B' ∩ {ω | A (t+Δ'+1) ω = π(Δ'+1)}) = ∫⁻ ω in B', stepDist₂ (t+Δ') (A (t+Δ') ω) (π(Δ'+1)) ∂μ
    -- Step 3: on B', A (t+Δ') ω = π Δ' pointwise.
    have hA_on_B' : ∀ ω ∈ B', vm.opinionZeroSet (t + Δ') ω = π Δ' := by
      intro ω hω
      have hω₁ : ω ∈ B := hω.1
      have hω₂ : ω ∈ ⋂ j ∈ Finset.range Δ', {ω | vm.opinionZeroSet (t + j + 1) ω = π (j + 1)} := hω.2
      rcases Nat.eq_zero_or_pos Δ' with hΔ' | hΔ'
      · -- Δ' = 0: A (t+0) ω = A t ω = a = π 0 = π Δ'.
        subst hΔ'
        have := hBa ω hω₁
        simp [this, hπ0]
      · -- Δ' > 0: B' ⊆ {A (t + (Δ'-1) + 1) ω = π (Δ'-1+1)} = {A (t+Δ') = π Δ'}.
        have hΔ'_mem : (Δ' - 1) ∈ Finset.range Δ' := Finset.mem_range.mpr (Nat.sub_lt hΔ' Nat.one_pos)
        rw [Set.mem_iInter] at hω₂
        have hω₂' := hω₂ (Δ' - 1)
        rw [Set.mem_iInter] at hω₂'
        have hω₂'' : vm.opinionZeroSet (t + (Δ' - 1) + 1) ω = π ((Δ' - 1) + 1) := hω₂' hΔ'_mem
        have heq1 : t + (Δ' - 1) + 1 = t + Δ' := by omega
        have heq2 : (Δ' - 1) + 1 = Δ' := Nat.sub_add_cancel hΔ'
        rw [heq1, heq2] at hω₂''
        exact hω₂''
    -- Step 4: the integrand on B' is the constant stepDist₂ (t+Δ') (π Δ') (π(Δ'+1)).
    have hB'_meas : MeasurableSet B' := by
      refine hBm.inter ?_
      exact MeasurableSet.biInter (Finset.range Δ').countable_toSet
        (fun j _ => hAset_meas (t + j + 1) (π (j + 1)))
    have hint_eq :
        ∫⁻ ω in B', (VoterModel.stepDist₂ G (t + Δ') (vm.opinionZeroSet (t + Δ') ω)) (π (Δ' + 1)) ∂vm.μ
          = ∫⁻ _ω in B',
              ((VoterModel.stepDist₂ G (t + Δ') (π Δ')) (π (Δ' + 1)) : ENNReal) ∂vm.μ := by
      apply setLIntegral_congr_fun hB'_meas
      intro ω hω
      show (VoterModel.stepDist₂ G (t + Δ') (vm.opinionZeroSet (t + Δ') ω)) (π (Δ' + 1)) =
        (VoterModel.stepDist₂ G (t + Δ') (π Δ')) (π (Δ' + 1))
      rw [hA_on_B' ω hω]
    -- Step 5: pull the constant out and combine with the IH.
    have hLHS :
        (vm.μ : Measure _) (B ∩ ⋂ j ∈ Finset.range (Δ' + 1), {ω | vm.opinionZeroSet (t + j + 1) ω = π (j + 1)})
          = (VoterModel.stepDist₂ G (t + Δ') (π Δ')) (π (Δ' + 1)) * (vm.μ : Measure _) B' := by
      rw [hLHS_eq, hcM, hint_eq, setLIntegral_const]
    rw [hLHS]
    -- Apply IH for μ(B').
    rw [show B' = B ∩ ⋂ j ∈ Finset.range Δ', {ω : Ω | vm.opinionZeroSet (t + j + 1) ω = π (j + 1)} from rfl]
    rw [ih]
    -- Now: stepDist₂ (t+Δ') (π Δ') (π(Δ'+1)) * (μ B * ∏_{range Δ'} stepDist₂ (t+j) (π j) (π(j+1)))
    --       = μ B * ∏_{range (Δ'+1)} stepDist₂ (t+j) (π j) (π(j+1))
    rw [Finset.prod_range_succ]
    ring

/-! ### Per-fiber Markov constancy bridge

The proof of `condExp_const_voter_fiber` decomposes Ω (a.s.) into two
`ℱ_t`-measurable fibers, applies the iterated conditional Markov property
on each fiber, and assembles via `ae_of_ae_restrict_fiber_cover` (L59).

We have proved:
* The two-fiber pointwise cover (`fiber_cover_pointwise`).
* Measurability of each fiber in `ℱ_t` (`A_measurable_in_filtration`).
* Iterated marginal Markov property (`multistep_markov_filtration₂`).
* Assembly via L59 (`ae_of_ae_restrict_fiber_cover`).
* Per-fiber constancy (`hH38_per_fiber`): on each A-fiber `{A t = a}`,
  the conditional expectation equals the unconditional integral.
-/

/-- The opinion-set process `vm.opinionZeroSet t` is measurable w.r.t. the filtration `vm.ℱ t`. -/
private lemma A_measurable_in_filtration
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    {Ω : Type*} [MeasurableSpace Ω]
    {G : TemporalGraph V} (vm : G.VoterModelAbstract 2 Ω) (t : ℕ) :
    @Measurable Ω (Finset V) (vm.ℱ t) ⊤ (vm.opinionZeroSet t) :=
  (vm.A_stronglyAdapted t).measurable


/-! ### Kernel.traj-mediated bridge

We adopt the Mathlib Ionescu–Tulcea API
(`Mathlib.Probability.Kernel.IonescuTulcea.Traj`) to set up the bridge
from the one-step conditional Markov property `vm.A_markovProperty` to a
path-level factorization of `∫_B φ(T_next, S_{T_next}) dμ`.

The opinion-set values live in `Finset V`, which we equip locally with
the discrete (top) σ-algebra (matching the convention used elsewhere in
this file, e.g. `cylinder_markov_finite_tuple` at line ~162 which has
`@Measurable Ω (Finset V) mΩ ⊤ (vm.opinionZeroSet j)`).

The current proof skeleton routes through `cylinder_markov_finite_tuple`
(the finite-tuple cylinder factorization, already proved), with the
remaining substantive content packaged into `fiber_factorization_at_total`. -/

section KernelTrajBridge

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]

/-- Local discrete σ-algebra on `Finset V` for the kernel construction.
Matching the convention in this file's earlier proofs (codomain `⊤`). -/
private instance : MeasurableSpace (Finset V) := ⊤

/-- All sets in `Finset V` are measurable under the discrete σ-algebra. -/
private instance : DiscreteMeasurableSpace (Finset V) := ⟨fun _ => trivial⟩

variable {Ω : Type*} [MeasurableSpace Ω]

end KernelTrajBridge

/-! ### Helper lemmas for `fiber_factorization_at_total`

The following helpers structure the cylinder-enumeration proof:

* `minoritySet_complement_eq_of_no_tie` — definitional collapse of
  `minoritySet` on complement pairs at non-ties.
* `minoritySet_volume_eq` — `vol (minoritySet G k T)` depends only on
  `(vol T, vol (univ\T))` (in fact on the smaller of the two).
-/

/-- For any `T : Finset V`, the volumes of `T` and `univ \ T` jointly determine
the volume of `minoritySet G k T` (as the minimum of the two). This is the
direct consequence of the `if` branch in the definition of `minoritySet`. -/
private lemma minoritySet_volume_eq
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraph V) (k : ℕ) (T : Finset V) :
    TemporalGraph.volume G k (VoterModel.minoritySet G k T) =
      min (TemporalGraph.volume G k T) (TemporalGraph.volume G k (Finset.univ \ T)) := by
  unfold VoterModel.minoritySet
  split_ifs with h
  · exact (min_eq_left h).symm
  · push Not at h
    exact (min_eq_right h.le).symm

/-- On non-ties (`vol T ≠ vol (univ \ T)`), `minoritySet` collapses complement
pairs: `minoritySet G k T = minoritySet G k (univ \ T)`. -/
private lemma minoritySet_complement_eq_of_no_tie
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraph V) (k : ℕ) (T : Finset V)
    (hne : TemporalGraph.volume G k T ≠ TemporalGraph.volume G k (Finset.univ \ T)) :
    VoterModel.minoritySet G k T = VoterModel.minoritySet G k (Finset.univ \ T) := by
  unfold VoterModel.minoritySet
  have hcompl : Finset.univ \ (Finset.univ \ T) = T :=
    Finset.sdiff_sdiff_eq_self (Finset.subset_univ T)
  rw [hcompl]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- vol T < vol (univ\T): both branches return T.
    rw [if_pos hlt.le, if_neg (by push Not; exact hlt)]
  · -- vol T > vol (univ\T): both branches return univ\T.
    rw [if_neg (by push Not; exact hgt), if_pos hgt.le]

/-- \label{lem:fiber-factorization-T-next-constant-on-cylinder}

**T_next is constant on each cylinder (L86; sub-task for L80 closure).**

Setup: `t : ℕ`, `N : ℕ` with `t ≤ N`, and `vm` voter model. Suppose
`T_next : Ω → ℕ` satisfies `hT_bound : ∀ω, T_next ω ≤ N` and the bounded
volume-determined form `hT_indep`. For ω₁, ω₂ such that the `vm.opinionZeroSet` values
agree pointwise on the closed interval `[t, N]` (split into `vm.opinionZeroSet k ω₁ =
vm.opinionZeroSet k ω₂` for `t < k ≤ N` via the cylinder and `vm.opinionZeroSet t ω₁ = vm.opinionZeroSet t ω₂`
via the calling context's `hS_const` + A-fiber atom constraint), we have
`T_next ω₁ = T_next ω₂`.

**Proof.** Apply `hT_indep` to reduce to showing
`vol(vm.S k ω₁) = vol(vm.S k ω₂)` for `k ∈ [t, N]`. Since
`vm.S k = minoritySet G k (vm.opinionZeroSet k)` (definitional unfolding), pointwise
equality of `vm.opinionZeroSet k ω₁` and `vm.opinionZeroSet k ω₂` (from `hA_eq`/`hA_t_eq`) yields
the volume equality by `rfl` after rewriting `vm.opinionZeroSet`.
-/
lemma fiber_factorization_T_next_constant_on_cylinder
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    {Ω : Type*} [MeasurableSpace Ω]
    (G : TemporalGraph V) (vm : G.VoterModelAbstract 2 Ω)
    (t : ℕ) (N : ℕ) (_htN : t ≤ N)
    (T_next : Ω → ℕ)
    (_hT_bound : ∀ ω, T_next ω ≤ N)
    (hT_indep : ∀ ω₁ ω₂, (∀ k, t ≤ k → k ≤ N →
        TemporalGraph.volume G k (vm.S k ω₁) = TemporalGraph.volume G k (vm.S k ω₂)) →
      T_next ω₁ = T_next ω₂)
    (ω₁ ω₂ : Ω)
    -- Cylinder constraint: `vm.opinionZeroSet k ω₁ = vm.opinionZeroSet k ω₂` for `k ∈ (t, N]`.
    (hA_eq : ∀ k, t < k → k ≤ N → vm.opinionZeroSet k ω₁ = vm.opinionZeroSet k ω₂)
    -- A-fiber atom constraint: `vm.opinionZeroSet t ω₁ = vm.opinionZeroSet t ω₂` (from `hS_const` + `hBa`).
    (hA_t_eq : vm.opinionZeroSet t ω₁ = vm.opinionZeroSet t ω₂) :
    T_next ω₁ = T_next ω₂ := by
  apply hT_indep
  intro k hkt hkN
  -- Obtain `vm.opinionZeroSet k ω₁ = vm.opinionZeroSet k ω₂` from the appropriate hypothesis.
  have hAk : vm.opinionZeroSet k ω₁ = vm.opinionZeroSet k ω₂ := by
    rcases eq_or_lt_of_le hkt with hkt_eq | hkt_lt
    · -- `k = t`: use `hA_t_eq`.
      cases hkt_eq; exact hA_t_eq
    · -- `t < k ≤ N`: use `hA_eq`.
      exact hA_eq k hkt_lt hkN
  -- `vm.S k ω = minoritySet G k (vm.opinionZeroSet k ω)` by definition; rewriting `vm.opinionZeroSet` closes by `rfl`.
  show TemporalGraph.volume G k (VoterModel.minoritySet G k (vm.opinionZeroSet k ω₁)) =
       TemporalGraph.volume G k (VoterModel.minoritySet G k (vm.opinionZeroSet k ω₂))
  rw [hAk]

/-- \label{lem:fiber-factorization-S-at-T-next-constant-on-cylinder}

**`vm.S (T_next)` is constant on each cylinder (L87; sub-task for L80 closure).**

Setup as in `fiber_factorization_T_next_constant_on_cylinder` (L86), with the
additional hypothesis `hT_next_ge_t : ∀ ω, t ≤ T_next ω` ensuring
`T_next ω ∈ [t, N]`. For ω₁, ω₂ such that the `vm.opinionZeroSet` values agree pointwise
on `(t, N]` (via `hA_eq`) and at `t` (via `hA_t_eq`),
`vm.S (T_next ω₁) ω₁ = vm.S (T_next ω₂) ω₂`.

**Proof.** Apply L86 to obtain `T_next ω₁ = T_next ω₂ =: k`. Reduce the goal
to `vm.S k ω₁ = vm.S k ω₂`. Since
`vm.S k = VoterModel.minoritySet G k (vm.opinionZeroSet k)` definitionally, and
`vm.opinionZeroSet k ω₁ = vm.opinionZeroSet k ω₂` (by `hA_t_eq` if `k = t`, else by `hA_eq`), the
conclusion follows.
-/
lemma fiber_factorization_S_at_T_next_constant_on_cylinder
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    {Ω : Type*} [MeasurableSpace Ω]
    (G : TemporalGraph V) (vm : G.VoterModelAbstract 2 Ω)
    (t : ℕ) (N : ℕ) (htN : t ≤ N)
    (T_next : Ω → ℕ)
    (hT_bound : ∀ ω, T_next ω ≤ N)
    (hT_indep : ∀ ω₁ ω₂, (∀ k, t ≤ k → k ≤ N →
        TemporalGraph.volume G k (vm.S k ω₁) = TemporalGraph.volume G k (vm.S k ω₂)) →
      T_next ω₁ = T_next ω₂)
    (ω₁ ω₂ : Ω)
    -- Cylinder constraint: `vm.opinionZeroSet k ω₁ = vm.opinionZeroSet k ω₂` for `k ∈ (t, N]`.
    (hA_eq : ∀ k, t < k → k ≤ N → vm.opinionZeroSet k ω₁ = vm.opinionZeroSet k ω₂)
    -- A-fiber atom constraint: `vm.opinionZeroSet t ω₁ = vm.opinionZeroSet t ω₂` (from `hS_const` + `hBa`).
    (hA_t_eq : vm.opinionZeroSet t ω₁ = vm.opinionZeroSet t ω₂)
    -- `T_next ω ≥ t` for all ω, ensuring `T_next ω ∈ [t, N]`.
    (hT_next_ge_t : ∀ ω, t ≤ T_next ω) :
    vm.S (T_next ω₁) ω₁ = vm.S (T_next ω₂) ω₂ := by
  -- Step 1: Apply L86 to identify the two times.
  have hT_eq : T_next ω₁ = T_next ω₂ :=
    fiber_factorization_T_next_constant_on_cylinder
      G vm t N htN T_next hT_bound hT_indep ω₁ ω₂ hA_eq hA_t_eq
  -- Step 2: Rewrite the goal using `hT_eq` to share a common time `T_next ω₁`.
  rw [← hT_eq]
  -- Goal: `vm.S (T_next ω₁) ω₁ = vm.S (T_next ω₁) ω₂`.
  -- Step 3: Obtain `vm.opinionZeroSet (T_next ω₁) ω₁ = vm.opinionZeroSet (T_next ω₁) ω₂` from `hA_eq`/`hA_t_eq`.
  have hkt : t ≤ T_next ω₁ := hT_next_ge_t ω₁
  have hkN : T_next ω₁ ≤ N := hT_bound ω₁
  have hAk : vm.opinionZeroSet (T_next ω₁) ω₁ = vm.opinionZeroSet (T_next ω₁) ω₂ := by
    rcases eq_or_lt_of_le hkt with hkt_eq | hkt_lt
    · -- `t = T_next ω₁`: use `hA_t_eq`.
      rw [← hkt_eq]; exact hA_t_eq
    · -- `t < T_next ω₁ ≤ N`: use `hA_eq`.
      exact hA_eq (T_next ω₁) hkt_lt hkN
  -- Step 4: `vm.S k ω = minoritySet G k (vm.opinionZeroSet k ω)` definitionally; close by `rw [hAk]`.
  show VoterModel.minoritySet G (T_next ω₁) (vm.opinionZeroSet (T_next ω₁) ω₁) =
       VoterModel.minoritySet G (T_next ω₁) (vm.opinionZeroSet (T_next ω₁) ω₂)
  rw [hAk]

/-! ### L88 helpers — path extension and cylinder set

Notation:
- A "post-anchor path" is `π : Fin (N - t) → Finset V`, representing the
  values `(vm.opinionZeroSet (t+1), vm.opinionZeroSet (t+2), …, vm.opinionZeroSet N)`.
- `extendPath a π : ℕ → Finset V` prepends `a` so we have
  `(extendPath a π) 0 = a` and `(extendPath a π) (k+1) = π k`
  (within the valid range), matching the shape expected by
  `cylinder_markov_finite_tuple`.
- `cylinderOf t π : Set Ω` is the cylinder
  `⋂ k : Fin (N - t), {ω | vm.opinionZeroSet (t + k.val + 1) ω = π k}`.
-/

/-- Prepend `a` to a finite path `π : Fin Δ → Finset V`, producing a
`ℕ → Finset V` with `extendPath a π 0 = a` and
`extendPath a π (k+1) = π ⟨k, …⟩` for `k < Δ` (otherwise returns `∅`). -/
noncomputable def extendPath {V : Type*} [Fintype V] [DecidableEq V]
    {Δ : ℕ} (a : Finset V) (π : Fin Δ → Finset V) : ℕ → Finset V := fun k =>
  if k = 0 then a else
    if h' : k - 1 < Δ then π ⟨k - 1, h'⟩ else ∅

private lemma extendPath_zero {V : Type*} [Fintype V] [DecidableEq V]
    {Δ : ℕ} (a : Finset V) (π : Fin Δ → Finset V) :
    extendPath a π 0 = a := by
  unfold extendPath; simp

private lemma extendPath_succ {V : Type*} [Fintype V] [DecidableEq V]
    {Δ : ℕ} (a : Finset V) (π : Fin Δ → Finset V) (k : ℕ) (hk : k < Δ) :
    extendPath a π (k + 1) = π ⟨k, hk⟩ := by
  unfold extendPath
  have hk_ne : k + 1 ≠ 0 := Nat.succ_ne_zero k
  rw [if_neg hk_ne]
  have hsub : k + 1 - 1 = k := rfl
  rw [dif_pos (by rw [hsub]; exact hk)]
  congr

/-- The cylinder set determined by a post-anchor path `π : Fin (N - t) → Finset V`:
the set of `ω` whose `vm.opinionZeroSet` values at `t + 1, t + 2, …, N` match `π`. -/
def cylinderOf {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    {Ω : Type*} [MeasurableSpace Ω] {G : TemporalGraph V} (vm : G.VoterModelAbstract 2 Ω)
    (t N : ℕ) (π : Fin (N - t) → Finset V) : Set Ω :=
  ⋂ k : Fin (N - t), {ω | vm.opinionZeroSet (t + k.val + 1) ω = π k}

/-- `cylinderOf` is ambient-measurable. -/
private lemma cylinderOf_measurable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {G : TemporalGraph V} (vm : G.VoterModelAbstract 2 Ω)
    (t N : ℕ) (π : Fin (N - t) → Finset V) :
    MeasurableSet (cylinderOf vm t N π) := by
  have hAmeas : ∀ (j : ℕ), @Measurable Ω (Finset V) mΩ ⊤ (vm.opinionZeroSet j) :=
    fun j s _ => vm.A_meas j _ ⟨s, trivial, rfl⟩
  refine MeasurableSet.iInter (fun k => ?_)
  exact hAmeas (t + k.val + 1) (measurableSet_singleton (π k))

/-- The cylinder partition cover: every `ω ∈ B ⊆ Ω` lies in exactly one
cylinder, the one determined by its own `vm.opinionZeroSet` values on `(t, N]`. -/
private lemma cylinder_cover {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    {Ω : Type*} [MeasurableSpace Ω] {G : TemporalGraph V} (vm : G.VoterModelAbstract 2 Ω)
    (t N : ℕ) :
    (⋃ π : Fin (N - t) → Finset V, cylinderOf vm t N π) = Set.univ := by
  ext ω
  refine ⟨fun _ => Set.mem_univ ω, fun _ => ?_⟩
  refine Set.mem_iUnion.mpr ⟨fun k => vm.opinionZeroSet (t + k.val + 1) ω, ?_⟩
  unfold cylinderOf
  refine Set.mem_iInter.mpr (fun k => ?_)
  rfl

/-- Distinct cylinders are disjoint. -/
private lemma cylinder_disjoint {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    {Ω : Type*} [MeasurableSpace Ω] {G : TemporalGraph V} (vm : G.VoterModelAbstract 2 Ω)
    (t N : ℕ) :
    Pairwise (Function.onFun Disjoint
      (fun π : Fin (N - t) → Finset V => cylinderOf vm t N π)) := by
  intro π₁ π₂ hne
  show Disjoint (cylinderOf vm t N π₁) (cylinderOf vm t N π₂)
  refine Set.disjoint_left.mpr (fun ω hω₁ hω₂ => hne ?_)
  funext k
  unfold cylinderOf at hω₁ hω₂
  rw [Set.mem_iInter] at hω₁ hω₂
  have h₁ : vm.opinionZeroSet (t + k.val + 1) ω = π₁ k := hω₁ k
  have h₂ : vm.opinionZeroSet (t + k.val + 1) ω = π₂ k := hω₂ k
  exact h₁.symm.trans h₂

/-- Bridge from a post-anchor path's cylinder to the
`cylinder_markov_finite_tuple` shape using `extendPath`. -/
private lemma cylinderOf_eq_extendPath_inter {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    {Ω : Type*} [MeasurableSpace Ω] {G : TemporalGraph V} (vm : G.VoterModelAbstract 2 Ω)
    (t N : ℕ) (a : Finset V) (π : Fin (N - t) → Finset V) :
    cylinderOf vm t N π =
      ⋂ j ∈ Finset.range (N - t),
        {ω | vm.opinionZeroSet (t + j + 1) ω = extendPath a π (j + 1)} := by
  unfold cylinderOf
  ext ω
  simp only [Set.mem_iInter, Set.mem_setOf_eq, Finset.mem_range]
  constructor
  · intro h j hj
    rw [extendPath_succ a π j hj]
    exact h ⟨j, hj⟩
  · intro h k
    have hk := h k.val k.isLt
    rw [extendPath_succ a π k.val k.isLt] at hk
    convert hk

open Classical in
/-- \label{lem:fiber-factorization-cylinder-partition-mass}

**L88: Cylinder partition mass on a deterministic A-fiber.**

Sub-task 3 of 4 for closing L80 (`fiber_factorization_at_total`).

For `B ∈ vm.ℱ t` with `B ⊆ {vm.opinionZeroSet t = a}` (a is the A-fiber anchor),
`∫_B φ(T_next, S_{T_next}) dμ` equals
`((vm.μ : Measure _) B).toReal · ∑ π, (∏ k, stepDist₂ (t+k) (extendPath a π k) (extendPath a π (k+1)))
  · φ (T_π_witness π) (S_π_witness π)`,
where the sum ranges over all post-anchor paths `π : Fin (N - t) → Finset V`
(unreachable paths contribute `0 · _ = 0`), and `T_π_witness`, `S_π_witness`
are the (constant) values of `T_next` and `vm.S (T_next)` on the cylinder
(chosen by `Classical.choose`; default values on empty cylinders don't
affect the sum).

**Proof.** Partition `B` into cylinders `B ∩ cylinderOf π` (finitely many,
indexed by `Fin (N - t) → Finset V`, which is finite since `Finset V` is
finite). The integrand `φ(T_next, vm.S (T_next))` is constant on each
cylinder (by L86 + L87). For each `π`,
`cylinder_markov_finite_tuple` gives
`μ(B ∩ cylinderOf π) = μ(B) · ∏ stepDist₂ (t+k) (extendPath a π k) (extendPath a π (k+1))`.
Sum.
-/
lemma fiber_factorization_cylinder_partition_mass
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    {Ω : Type*} [MeasurableSpace Ω]
    (G : TemporalGraph V) (vm : G.VoterModelAbstract 2 Ω)
    (t : ℕ) (N : ℕ) (_htN : t ≤ N)
    (T_next : Ω → ℕ)
    (hT_next_ge : ∀ ω, t ≤ T_next ω)
    (hT_bound : ∀ ω, T_next ω ≤ N)
    (hT_indep : ∀ ω₁ ω₂, (∀ k, t ≤ k → k ≤ N →
        TemporalGraph.volume G k (vm.S k ω₁) = TemporalGraph.volume G k (vm.S k ω₂)) →
      T_next ω₁ = T_next ω₂)
    (φ : ℕ → Finset V → ℝ)
    (hφ_int : Integrable (fun ω => φ (T_next ω) (vm.S (T_next ω) ω)) vm.μ)
    (a : Finset V)
    (B : Set Ω) (hB : MeasurableSet[vm.ℱ t] B)
    (hBa : ∀ ω ∈ B, vm.opinionZeroSet t ω = a) :
    -- Conclusion: ∫_B f dμ = (μ B).toReal · (∑ π, ∏ stepDist₂ · φ-on-cylinder).
    ∫ ω in B, φ (T_next ω) (vm.S (T_next ω) ω) ∂vm.μ
      = ((vm.μ : Measure _) B).toReal *
        ∑ π : Fin (N - t) → Finset V,
          (∏ k ∈ Finset.range (N - t),
              (VoterModel.stepDist₂ G (t + k) (extendPath a π k))
                (extendPath a π (k + 1))).toReal *
          (if h : (B ∩ cylinderOf vm t N π).Nonempty then
              φ (T_next h.choose) (vm.S (T_next h.choose) h.choose)
            else 0) := by
  -- Abbreviations.
  set f : Ω → ℝ := fun ω => φ (T_next ω) (vm.S (T_next ω) ω) with hf_def
  have hBm : MeasurableSet B := vm.ℱ.le t B hB
  -- The cylinder family, restricted to B (these partition B).
  set C : (Fin (N - t) → Finset V) → Set Ω :=
    fun π => B ∩ cylinderOf vm t N π with hC_def
  have hC_meas : ∀ π, MeasurableSet (C π) := fun π =>
    hBm.inter (cylinderOf_measurable vm t N π)
  -- Pairwise disjoint cylinders ⇒ pairwise disjoint restrictions.
  have hC_disj : Pairwise (Function.onFun Disjoint C) := by
    intro π₁ π₂ hne
    have hcyl := cylinder_disjoint vm t N hne
    show Disjoint (B ∩ cylinderOf vm t N π₁) (B ∩ cylinderOf vm t N π₂)
    refine Set.disjoint_left.mpr fun ω hω₁ hω₂ => ?_
    exact (Set.disjoint_left.mp hcyl) hω₁.2 hω₂.2
  -- B = ⋃_π C π via the cylinder cover.
  have hB_eq : B = ⋃ π : Fin (N - t) → Finset V, C π := by
    have hcov := cylinder_cover vm t N
    ext ω
    constructor
    · intro hω
      have : ω ∈ (⋃ π, cylinderOf vm t N π) := hcov ▸ Set.mem_univ ω
      rcases Set.mem_iUnion.mp this with ⟨π, hπ⟩
      exact Set.mem_iUnion.mpr ⟨π, hω, hπ⟩
    · intro hω
      rcases Set.mem_iUnion.mp hω with ⟨_, hω₁, _⟩
      exact hω₁
  -- f restricted to each cylinder is integrable (since hφ_int is global).
  have hf_intOn : ∀ π, IntegrableOn f (C π) vm.μ := fun π =>
    hφ_int.integrableOn
  -- Split the set integral along the cylinder partition.
  have hsplit :
      ∫ ω in B, f ω ∂vm.μ = ∑ π : Fin (N - t) → Finset V, ∫ ω in C π, f ω ∂vm.μ := by
    rw [hB_eq]
    exact integral_iUnion_fintype hC_meas hC_disj hf_intOn
  -- On each cylinder, f is constant. We extract that constant via Classical.choose.
  -- Define the witness function and the constant value on each cylinder.
  have hf_const : ∀ π : Fin (N - t) → Finset V, ∀ ω ∈ C π,
      f ω = (if h : (B ∩ cylinderOf vm t N π).Nonempty then
              φ (T_next h.choose) (vm.S (T_next h.choose) h.choose)
            else 0) := by
    intro π ω hω
    have hNE : (B ∩ cylinderOf vm t N π).Nonempty := ⟨ω, hω⟩
    rw [dif_pos hNE]
    -- Both `h.choose` and `ω` are in `B ∩ cylinderOf vm t N π`.
    set ω₀ := hNE.choose with hω₀_def
    have hω₀ : ω₀ ∈ B ∩ cylinderOf vm t N π := hNE.choose_spec
    -- Apply L86 + L87 to identify the values at ω and ω₀.
    have hA_t_eq : vm.opinionZeroSet t ω = vm.opinionZeroSet t ω₀ := by
      rw [hBa ω hω.1, hBa ω₀ hω₀.1]
    have hA_eq : ∀ k, t < k → k ≤ N → vm.opinionZeroSet k ω = vm.opinionZeroSet k ω₀ := by
      intro k hkt hkN
      -- k = t + (k - t), with 0 < k - t ≤ N - t. Use the cylinder constraint at index k - t - 1.
      have hkt' : 1 ≤ k - t := Nat.sub_pos_of_lt hkt
      have hkN_sub : k - t ≤ N - t := Nat.sub_le_sub_right hkN t
      have hlt : (k - t - 1) < N - t := by omega
      have hidx_eq : t + (k - t - 1) + 1 = k := by omega
      -- Membership facts from the cylinder.
      have hω_cyl : ω ∈ cylinderOf vm t N π := hω.2
      have hω₀_cyl : ω₀ ∈ cylinderOf vm t N π := hω₀.2
      unfold cylinderOf at hω_cyl hω₀_cyl
      rw [Set.mem_iInter] at hω_cyl hω₀_cyl
      have h₁ : vm.opinionZeroSet (t + (k - t - 1) + 1) ω = π ⟨k - t - 1, hlt⟩ := hω_cyl ⟨k - t - 1, hlt⟩
      have h₂ : vm.opinionZeroSet (t + (k - t - 1) + 1) ω₀ = π ⟨k - t - 1, hlt⟩ := hω₀_cyl ⟨k - t - 1, hlt⟩
      rw [hidx_eq] at h₁ h₂
      rw [h₁, h₂]
    -- Apply L87 to identify `f ω = f ω₀`.
    have hS_eq : vm.S (T_next ω) ω = vm.S (T_next ω₀) ω₀ :=
      fiber_factorization_S_at_T_next_constant_on_cylinder G vm t N _htN T_next hT_bound
        hT_indep ω ω₀ hA_eq hA_t_eq hT_next_ge
    -- Also need T_next ω = T_next ω₀ via L86.
    have hT_eq : T_next ω = T_next ω₀ :=
      fiber_factorization_T_next_constant_on_cylinder G vm t N _htN T_next hT_bound
        hT_indep ω ω₀ hA_eq hA_t_eq
    show φ (T_next ω) (vm.S (T_next ω) ω) = φ (T_next ω₀) (vm.S (T_next ω₀) ω₀)
    rw [hS_eq, hT_eq]
  -- Rewrite each cylinder integral using `f` constant.
  have hperC :
      ∀ π : Fin (N - t) → Finset V,
        ∫ ω in C π, f ω ∂vm.μ
          = ((vm.μ : Measure _) (C π)).toReal *
            (if h : (B ∩ cylinderOf vm t N π).Nonempty then
                φ (T_next h.choose) (vm.S (T_next h.choose) h.choose)
              else 0) := by
    intro π
    set v : ℝ := if h : (B ∩ cylinderOf vm t N π).Nonempty then
        φ (T_next h.choose) (vm.S (T_next h.choose) h.choose)
      else 0 with hv_def
    have hf_eq : ∀ ω ∈ C π, f ω = v := hf_const π
    rw [setIntegral_congr_fun (hC_meas π) hf_eq, MeasureTheory.setIntegral_const,
        Measure.real, smul_eq_mul]
  -- Now use cylinder_markov_finite_tuple to express μ(C π).
  have hμC :
      ∀ π : Fin (N - t) → Finset V,
        (vm.μ : Measure _) (C π) = (vm.μ : Measure _) B *
          ∏ k ∈ Finset.range (N - t),
            (VoterModel.stepDist₂ G (t + k) (extendPath a π k)) (extendPath a π (k + 1)) := by
    intro π
    have hcyl := cylinder_markov_finite_tuple G vm t (N - t) B hB a hBa
      (extendPath a π) (extendPath_zero a π)
    -- hcyl : (vm.μ : Measure _) (B ∩ ⋂ j ∈ range (N-t), {A (t+j+1) = extendPath a π (j+1)})
    --       = (vm.μ : Measure _) B * ∏ stepDist₂...
    -- We need to identify the LHS with (vm.μ : Measure _) (C π).
    have hC_eq :
        B ∩ ⋂ j ∈ Finset.range (N - t),
            {ω | vm.opinionZeroSet (t + j + 1) ω = extendPath a π (j + 1)} = C π := by
      rw [hC_def]
      congr 1
      exact (cylinderOf_eq_extendPath_inter vm t N a π).symm
    rw [← hC_eq]; exact hcyl
  -- Convert ENNReal arithmetic to ℝ via toReal (legitimate since μ B, μ C π < ∞).
  have hB_ne_top : (vm.μ : Measure _) B ≠ ⊤ := measure_ne_top (vm.μ : Measure _) B
  have hC_ne_top : ∀ π, (vm.μ : Measure _) (C π) ≠ ⊤ := fun π => measure_ne_top (vm.μ : Measure _) (C π)
  -- Final assembly.
  rw [hsplit]
  -- Use hperC term-by-term.
  rw [Finset.sum_congr rfl (fun π _ => hperC π)]
  -- Replace μ(C π).toReal using hμC.
  have hreal :
      ∀ π : Fin (N - t) → Finset V,
        ((vm.μ : Measure _) (C π)).toReal =
          ((vm.μ : Measure _) B).toReal *
            (∏ k ∈ Finset.range (N - t),
                (VoterModel.stepDist₂ G (t + k) (extendPath a π k))
                  (extendPath a π (k + 1))).toReal := by
    intro π
    rw [hμC π]
    rw [ENNReal.toReal_mul]
  -- Apply hreal term-by-term and rearrange to factor out (μ B).toReal.
  rw [show
      (∑ π : Fin (N - t) → Finset V,
          ((vm.μ : Measure _) (C π)).toReal *
            (if h : (B ∩ cylinderOf vm t N π).Nonempty then
                φ (T_next h.choose) (vm.S (T_next h.choose) h.choose)
              else 0)) =
        ∑ π : Fin (N - t) → Finset V,
          ((vm.μ : Measure _) B).toReal *
            ((∏ k ∈ Finset.range (N - t),
                (VoterModel.stepDist₂ G (t + k) (extendPath a π k))
                  (extendPath a π (k + 1))).toReal *
              (if h : (B ∩ cylinderOf vm t N π).Nonempty then
                  φ (T_next h.choose) (vm.S (T_next h.choose) h.choose)
                else 0))
      from by
        apply Finset.sum_congr rfl
        intro π _
        rw [hreal π]
        ring]
  rw [← Finset.mul_sum]

open Classical in
/-- \label{lem:fiber-factorization-complement-bijection-symmetry}

**L89: Complement-bijection symmetry of the L88-RHS sum.**

Sub-task 4 of 4 for closing L80 (`fiber_factorization_at_total`).

For the L88-RHS sum (the explicit "constant `c_a`" formula), the value at
`a = s` (with `B = E_s = {vm.opinionZeroSet t = s}`) equals the value at
`a = univ \ s` (with `B = E_{univ\s} = {vm.opinionZeroSet t = univ \ s}`).

**Proof.** The involution `π ↦ π̄ := (univ \ ·) ∘ π` on
`Fin (N - t) → Finset V` is the path bijection. Under it:
  (a) the per-step product `∏ stepDist₂ (t+k) (extendPath a π k)
      (extendPath a π (k+1))` is invariant by `stepDist₂_complement`
      (L57) applied at each factor (the involution sends `a ↦ univ\a`,
      so the `extendPath` prefix is also flipped to `univ\·`).
  (b) the empty/nonempty status of `E_a ∩ cylinderOf π` matches the
      empty/nonempty status of `E_{univ\a} ∩ cylinderOf π̄`: if `ω` is
      in the first, then any `ω̄` with `vm.opinionZeroSet k ω̄ = univ \ vm.opinionZeroSet k ω`
      pointwise would be in the second; in the absence of such a
      canonical `ω̄`, we instead route through
      `cylinder_markov_finite_tuple`, which equates `μ(E_a ∩ cyl π) = 0
      ↔ ∏ stepDist₂ · μ(E_a) = 0`; under `μ E_a, μ E_{univ\s} > 0` (the
      caller's responsibility) this gives the empty/nonempty match.
  (c) the witness value `φ (T_next h.choose) (vm.S (T_next h.choose)
      h.choose)` agrees across the pair: pick witnesses `ω₁ ∈ E_s ∩ cyl
      π` and `ω₂ ∈ E_{univ\s} ∩ cyl π̄`; by `hT_indep`, `T_next ω₁ =
      T_next ω₂` (since `vol(S_k)` agrees pointwise on `[t,N]` between
      `ω₁` and `ω₂` because complement-flipped `A_k`-values have the
      same minoritySet-volume); and `vm.S (T_next) ω₁ = vm.S (T_next)
      ω₂` (or its complement under tie), with `hφ_inv` handling the
      tie case.
-/
lemma fiber_factorization_complement_bijection_symmetry
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    {Ω : Type*} [MeasurableSpace Ω]
    (G : TemporalGraph V) (vm : G.VoterModelAbstract 2 Ω)
    (t : ℕ) (N : ℕ) (htN : t ≤ N)
    (s : Finset V)
    (T_next : Ω → ℕ)
    (hT_next_ge : ∀ ω, t ≤ T_next ω)
    (hT_bound : ∀ ω, T_next ω ≤ N)
    (hT_indep : ∀ ω₁ ω₂, (∀ k, t ≤ k → k ≤ N →
        TemporalGraph.volume G k (vm.S k ω₁) = TemporalGraph.volume G k (vm.S k ω₂)) →
      T_next ω₁ = T_next ω₂)
    (φ : ℕ → Finset V → ℝ)
    -- Vol-tie symmetry of φ.
    (hφ_inv : ∀ k T,
        TemporalGraph.volume G k T = TemporalGraph.volume G k (Finset.univ \ T) →
        φ k T = φ k (Finset.univ \ T))
    -- Positivity of both A-fiber atoms (the caller dispatches the null cases).
    (hμE_s_pos : (vm.μ : Measure _) {ω | vm.opinionZeroSet t ω = s} ≠ 0)
    (hμE_sbar_pos : (vm.μ : Measure _) {ω | vm.opinionZeroSet t ω = Finset.univ \ s} ≠ 0) :
    -- Conclusion: the L88-RHS sum at (a := s, B := {vm.opinionZeroSet t = s}) equals
    -- the L88-RHS sum at (a := univ \ s, B := {vm.opinionZeroSet t = univ \ s}).
    (∑ π : Fin (N - t) → Finset V,
        (∏ k ∈ Finset.range (N - t),
            (VoterModel.stepDist₂ G (t + k) (extendPath s π k))
              (extendPath s π (k + 1))).toReal *
        (if h : ({ω | vm.opinionZeroSet t ω = s} ∩ cylinderOf vm t N π).Nonempty then
            φ (T_next h.choose) (vm.S (T_next h.choose) h.choose)
          else 0))
      =
    (∑ π : Fin (N - t) → Finset V,
        (∏ k ∈ Finset.range (N - t),
            (VoterModel.stepDist₂ G (t + k) (extendPath (Finset.univ \ s) π k))
              (extendPath (Finset.univ \ s) π (k + 1))).toReal *
        (if h : ({ω | vm.opinionZeroSet t ω = Finset.univ \ s} ∩ cylinderOf vm t N π).Nonempty then
            φ (T_next h.choose) (vm.S (T_next h.choose) h.choose)
          else 0)) := by
  -- Path involution: π̄ k := univ \ π k.
  set ι : (Fin (N - t) → Finset V) → (Fin (N - t) → Finset V) :=
    fun π k => Finset.univ \ π k with hι_def
  have hι_invol : ∀ π, ι (ι π) = π := by
    intro π; funext k
    simp [hι_def, Finset.sdiff_sdiff_eq_self (Finset.subset_univ _)]
  -- Volume-of-complement helper for minoritySet.
  -- The L88 RHS sum: define each anchor's term function (as a `let`, not `set`,
  -- to avoid an extra hypothesis that slows unfolding).
  let term : (Finset V) → (Set Ω) → (Fin (N - t) → Finset V) → ℝ :=
    fun a B π =>
      (∏ k ∈ Finset.range (N - t),
          (VoterModel.stepDist₂ G (t + k) (extendPath a π k))
            (extendPath a π (k + 1))).toReal *
      (if h : (B ∩ cylinderOf vm t N π).Nonempty then
          φ (T_next h.choose) (vm.S (T_next h.choose) h.choose)
        else 0)
  -- Anchor sets for `s` and `univ \ s`.
  set E_s : Set Ω := {ω | vm.opinionZeroSet t ω = s} with hE_s_def
  set E_sbar : Set Ω := {ω | vm.opinionZeroSet t ω = Finset.univ \ s} with hE_sbar_def
  -- We must show ∑ π, term s E_s π = ∑ π, term (univ\s) E_sbar π.
  -- Strategy: reindex the LHS sum via the involution `ι`, then
  -- show termwise equality `term s E_s π = term (univ\s) E_sbar (ι π)`.
  -- Step 1: termwise equality.
  -- Substep 1a: stepDist₂ product equality (via L57 at each factor).
  have hprod_eq : ∀ π : Fin (N - t) → Finset V,
      (∏ k ∈ Finset.range (N - t),
          (VoterModel.stepDist₂ G (t + k) (extendPath s π k))
            (extendPath s π (k + 1))) =
      (∏ k ∈ Finset.range (N - t),
          (VoterModel.stepDist₂ G (t + k) (extendPath (Finset.univ \ s) (ι π) k))
            (extendPath (Finset.univ \ s) (ι π) (k + 1))) := by
    intro π
    refine Finset.prod_congr rfl (fun k hk => ?_)
    have hk_lt : k < N - t := Finset.mem_range.mp hk
    -- We need:
    -- stepDist₂ (t+k) (extendPath s π k) (extendPath s π (k+1))
    --   = stepDist₂ (t+k) (extendPath (univ\s) (ι π) k) (extendPath (univ\s) (ι π) (k+1)).
    -- Compute both sides:
    -- LHS prefix: extendPath s π k =
    --   if k = 0 then s else π ⟨k-1, _⟩.
    -- RHS prefix: extendPath (univ\s) (ι π) k =
    --   if k = 0 then univ\s else (ι π) ⟨k-1, _⟩ = univ \ π ⟨k-1, _⟩.
    -- In all cases, RHS prefix = univ \ (LHS prefix).
    -- LHS post: extendPath s π (k+1) = π ⟨k, hk_lt⟩.
    -- RHS post: extendPath (univ\s) (ι π) (k+1) = (ι π) ⟨k, hk_lt⟩
    --                                            = univ \ π ⟨k, hk_lt⟩.
    -- So RHS post = univ \ (LHS post).
    -- The complement relation `stepDist₂ (t+k) (univ \ X) (univ \ Y) = stepDist₂ (t+k) X Y`
    -- follows from L57 (`stepDist₂_complement`):
    -- `stepDist₂ t (univ\S) = (stepDist₂ t S).map (univ\·)`; eval at univ\Y gives
    -- `(stepDist₂ t S).map (univ\·) (univ\Y) = ∑'. with x = Y ↦ stepDist₂ t S Y`.
    have hLHS_pre : extendPath s π k =
        Finset.univ \ extendPath (Finset.univ \ s) (ι π) k := by
      by_cases hk0 : k = 0
      · subst hk0
        simp [extendPath_zero, Finset.sdiff_sdiff_eq_self (Finset.subset_univ s)]
      · -- k > 0: both sides reduce to "π ⟨k-1, _⟩" up to complement.
        have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
        rcases Nat.exists_eq_succ_of_ne_zero hk0 with ⟨j, hj⟩
        subst hj
        have hj_lt : j < N - t := by omega
        rw [extendPath_succ s π j hj_lt, extendPath_succ (Finset.univ \ s) (ι π) j hj_lt]
        show π ⟨j, hj_lt⟩ = Finset.univ \ (ι π) ⟨j, hj_lt⟩
        simp [hι_def, Finset.sdiff_sdiff_eq_self (Finset.subset_univ _)]
    have hLHS_post : extendPath s π (k + 1) =
        Finset.univ \ extendPath (Finset.univ \ s) (ι π) (k + 1) := by
      rw [extendPath_succ s π k hk_lt, extendPath_succ (Finset.univ \ s) (ι π) k hk_lt]
      show π ⟨k, hk_lt⟩ = Finset.univ \ (ι π) ⟨k, hk_lt⟩
      simp [hι_def, Finset.sdiff_sdiff_eq_self (Finset.subset_univ _)]
    -- Apply L57: `stepDist₂ (t+k) (univ\X) = (stepDist₂ (t+k) X).map (univ\·)`.
    -- Hence `stepDist₂ (t+k) (univ\X) (univ\Y) = stepDist₂ (t+k) X Y` (since `univ\·` is involutive).
    rw [hLHS_pre, hLHS_post]
    set X := extendPath (Finset.univ \ s) (ι π) k
    set Y := extendPath (Finset.univ \ s) (ι π) (k + 1)
    -- Goal: stepDist₂ (t+k) (univ\X) (univ\Y) = stepDist₂ (t+k) X Y.
    -- Use toMeasure_map_apply via the complement-involution. The cleanest route:
    -- map_apply: `(p.map f) b = ∑' a, if b = f a then p a else 0`. For f = (univ \ ·),
    -- this is `∑' z, if univ\Y = univ\z then p z else 0 = p Y` by injectivity.
    rw [VoterModel.stepDist₂_complement G (t + k) X, PMF.map_apply]
    -- The injection (univ \ ·) is an involution, so (univ\Y = univ\z) ↔ (Y = z).
    have hinj : ∀ z : Finset V, (Finset.univ \ Y = Finset.univ \ z) ↔ z = Y := by
      intro z
      refine ⟨fun h => ?_, fun h => by rw [h]⟩
      have h' : Finset.univ \ (Finset.univ \ Y) = Finset.univ \ (Finset.univ \ z) := by rw [h]
      rw [Finset.sdiff_sdiff_eq_self (Finset.subset_univ _),
          Finset.sdiff_sdiff_eq_self (Finset.subset_univ _)] at h'
      exact h'.symm
    -- Reduce the tsum: rewrite `univ\Y = univ\z` to `z = Y`, then apply `tsum_ite_eq`.
    refine (tsum_congr ?_).trans (tsum_ite_eq Y _)
    intro z
    by_cases hz : z = Y
    · simp [hz]
    · have hne : Finset.univ \ Y ≠ Finset.univ \ z := by
        intro h
        exact hz ((hinj z).mp h)
      simp [hne, hz]
  -- Substep 1b: empty/nonempty pairing across the bijection.
  -- For each π, the witness values match across `(E_s, π)` and `(E_sbar, ι π)`.
  -- Key sub-lemma: if `ω₁ ∈ E_s ∩ cylinderOf vm t N π` and
  -- `ω₂ ∈ E_sbar ∩ cylinderOf vm t N (ι π)`, then
  -- `φ (T_next ω₁) (vm.S (T_next ω₁) ω₁) = φ (T_next ω₂) (vm.S (T_next ω₂) ω₂)`.
  have hwitness_eq : ∀ (π : Fin (N - t) → Finset V) (ω₁ ω₂ : Ω),
      ω₁ ∈ E_s ∩ cylinderOf vm t N π →
      ω₂ ∈ E_sbar ∩ cylinderOf vm t N (ι π) →
      φ (T_next ω₁) (vm.S (T_next ω₁) ω₁) =
        φ (T_next ω₂) (vm.S (T_next ω₂) ω₂) := by
    intro π ω₁ ω₂ hω₁ hω₂
    -- Pointwise complement on [t, N]: vm.opinionZeroSet k ω₁ = univ \ vm.opinionZeroSet k ω₂ for k ∈ [t, N].
    have hA_complement : ∀ k, t ≤ k → k ≤ N →
        vm.opinionZeroSet k ω₁ = Finset.univ \ vm.opinionZeroSet k ω₂ := by
      intro k hkt hkN
      rcases eq_or_lt_of_le hkt with hkt_eq | hkt_lt
      · -- k = t: vm.opinionZeroSet t ω₁ = s, vm.opinionZeroSet t ω₂ = univ \ s.
        cases hkt_eq
        rw [show vm.opinionZeroSet t ω₁ = s from hω₁.1,
            show vm.opinionZeroSet t ω₂ = Finset.univ \ s from hω₂.1,
            Finset.sdiff_sdiff_eq_self (Finset.subset_univ _)]
      · -- t < k ≤ N: use cylinders. ω₁ ∈ cyl π gives vm.opinionZeroSet (t+(k-t-1)+1) ω₁ = π ⟨k-t-1,_⟩;
        -- ω₂ ∈ cyl (ι π) gives vm.opinionZeroSet (t+(k-t-1)+1) ω₂ = (ι π) ⟨k-t-1,_⟩ = univ \ π ⟨k-t-1,_⟩.
        have hkt' : 1 ≤ k - t := Nat.sub_pos_of_lt hkt_lt
        have hkN_sub : k - t ≤ N - t := Nat.sub_le_sub_right hkN t
        have hlt : (k - t - 1) < N - t := by omega
        have hidx_eq : t + (k - t - 1) + 1 = k := by omega
        have hω₁_cyl : ω₁ ∈ cylinderOf vm t N π := hω₁.2
        have hω₂_cyl : ω₂ ∈ cylinderOf vm t N (ι π) := hω₂.2
        unfold cylinderOf at hω₁_cyl hω₂_cyl
        rw [Set.mem_iInter] at hω₁_cyl hω₂_cyl
        have h₁ : vm.opinionZeroSet (t + (k - t - 1) + 1) ω₁ = π ⟨k - t - 1, hlt⟩ :=
          hω₁_cyl ⟨k - t - 1, hlt⟩
        have h₂ : vm.opinionZeroSet (t + (k - t - 1) + 1) ω₂ = (ι π) ⟨k - t - 1, hlt⟩ :=
          hω₂_cyl ⟨k - t - 1, hlt⟩
        rw [hidx_eq] at h₁ h₂
        rw [h₁, h₂]
        show π ⟨k - t - 1, hlt⟩ = Finset.univ \ (ι π) ⟨k - t - 1, hlt⟩
        simp [hι_def, Finset.sdiff_sdiff_eq_self (Finset.subset_univ _)]
    -- Volume of minoritySet is the same at complement-flipped arguments.
    have hvol_eq : ∀ k, t ≤ k → k ≤ N →
        TemporalGraph.volume G k (vm.S k ω₁) =
          TemporalGraph.volume G k (vm.S k ω₂) := by
      intro k hkt hkN
      show TemporalGraph.volume G k (VoterModel.minoritySet G k (vm.opinionZeroSet k ω₁)) =
            TemporalGraph.volume G k (VoterModel.minoritySet G k (vm.opinionZeroSet k ω₂))
      rw [minoritySet_volume_eq, minoritySet_volume_eq, hA_complement k hkt hkN,
          Finset.sdiff_sdiff_eq_self (Finset.subset_univ _), min_comm]
    -- T_next ω₁ = T_next ω₂.
    have hT_eq : T_next ω₁ = T_next ω₂ := hT_indep ω₁ ω₂ hvol_eq
    -- Common time as a local abbreviation (no `set` to avoid substitution issues).
    have hk₀_range : t ≤ T_next ω₂ ∧ T_next ω₂ ≤ N := ⟨hT_next_ge ω₂, hT_bound ω₂⟩
    -- vm.opinionZeroSet (T_next ω₂) ω₁ = univ \ vm.opinionZeroSet (T_next ω₂) ω₂.
    have hAk₀ : vm.opinionZeroSet (T_next ω₂) ω₁ = Finset.univ \ vm.opinionZeroSet (T_next ω₂) ω₂ :=
      hA_complement (T_next ω₂) hk₀_range.1 hk₀_range.2
    rw [hT_eq]
    -- Goal: φ (T_next ω₂) (vm.S (T_next ω₂) ω₁) = φ (T_next ω₂) (vm.S (T_next ω₂) ω₂).
    by_cases htie :
        TemporalGraph.volume G (T_next ω₂) (vm.opinionZeroSet (T_next ω₂) ω₂) =
          TemporalGraph.volume G (T_next ω₂) (Finset.univ \ vm.opinionZeroSet (T_next ω₂) ω₂)
    · -- Tie at ω₂. Use hφ_inv to bridge.
      have hφ_swap :
          φ (T_next ω₂) (vm.opinionZeroSet (T_next ω₂) ω₂) =
            φ (T_next ω₂) (Finset.univ \ vm.opinionZeroSet (T_next ω₂) ω₂) :=
        hφ_inv (T_next ω₂) (vm.opinionZeroSet (T_next ω₂) ω₂) htie
      -- Case analysis on minoritySet branches.
      have hS₁ : vm.S (T_next ω₂) ω₁ = vm.opinionZeroSet (T_next ω₂) ω₁ ∨
                  vm.S (T_next ω₂) ω₁ = Finset.univ \ vm.opinionZeroSet (T_next ω₂) ω₁ := by
        show VoterModel.minoritySet G (T_next ω₂) (vm.opinionZeroSet (T_next ω₂) ω₁) = vm.opinionZeroSet (T_next ω₂) ω₁ ∨
              VoterModel.minoritySet G (T_next ω₂) (vm.opinionZeroSet (T_next ω₂) ω₁) =
                Finset.univ \ vm.opinionZeroSet (T_next ω₂) ω₁
        unfold VoterModel.minoritySet; split_ifs <;> tauto
      have hS₂ : vm.S (T_next ω₂) ω₂ = vm.opinionZeroSet (T_next ω₂) ω₂ ∨
                  vm.S (T_next ω₂) ω₂ = Finset.univ \ vm.opinionZeroSet (T_next ω₂) ω₂ := by
        show VoterModel.minoritySet G (T_next ω₂) (vm.opinionZeroSet (T_next ω₂) ω₂) = vm.opinionZeroSet (T_next ω₂) ω₂ ∨
              VoterModel.minoritySet G (T_next ω₂) (vm.opinionZeroSet (T_next ω₂) ω₂) =
                Finset.univ \ vm.opinionZeroSet (T_next ω₂) ω₂
        unfold VoterModel.minoritySet; split_ifs <;> tauto
      -- Now case-by-case.
      rcases hS₁ with h1 | h1 <;> rcases hS₂ with h2 | h2
      · -- vm.S ω₁ = vm.opinionZeroSet ω₁; vm.S ω₂ = vm.opinionZeroSet ω₂.
        rw [h1, h2, hAk₀]
        exact hφ_swap.symm
      · -- vm.S ω₁ = vm.opinionZeroSet ω₁; vm.S ω₂ = univ \ vm.opinionZeroSet ω₂.
        rw [h1, h2, hAk₀]
      · -- vm.S ω₁ = univ \ vm.opinionZeroSet ω₁; vm.S ω₂ = vm.opinionZeroSet ω₂.
        rw [h1, h2, hAk₀]
        rw [Finset.sdiff_sdiff_eq_self (Finset.subset_univ _)]
      · -- vm.S ω₁ = univ \ vm.opinionZeroSet ω₁; vm.S ω₂ = univ \ vm.opinionZeroSet ω₂.
        rw [h1, h2, hAk₀]
        rw [Finset.sdiff_sdiff_eq_self (Finset.subset_univ _)]
        exact hφ_swap
    · -- Non-tie at ω₂. Then minoritySet collapses complement pairs.
      have hmin :
          VoterModel.minoritySet G (T_next ω₂) (Finset.univ \ vm.opinionZeroSet (T_next ω₂) ω₂) =
            VoterModel.minoritySet G (T_next ω₂) (vm.opinionZeroSet (T_next ω₂) ω₂) := by
        rw [minoritySet_complement_eq_of_no_tie G (T_next ω₂) (vm.opinionZeroSet (T_next ω₂) ω₂) htie]
      show φ (T_next ω₂) (VoterModel.minoritySet G (T_next ω₂) (vm.opinionZeroSet (T_next ω₂) ω₁)) =
            φ (T_next ω₂) (VoterModel.minoritySet G (T_next ω₂) (vm.opinionZeroSet (T_next ω₂) ω₂))
      rw [hAk₀, hmin]
  -- Substep 1c: from hprod_eq + cylinder_markov_finite_tuple, the empty/nonempty
  -- status pairs across π ↔ ι π provided the underlying anchor sets have positive
  -- measure. We bypass this by showing termwise equality directly, treating
  -- both empty/nonempty cases:
  -- Filtration-measurability of the anchor fibers.
  have hAmeas_F : @Measurable Ω (Finset V) (vm.ℱ t) ⊤ (vm.opinionZeroSet t) :=
    A_measurable_in_filtration vm t
  have hE_s_F : MeasurableSet[vm.ℱ t] E_s :=
    hAmeas_F (by trivial : MeasurableSet ({s} : Set (Finset V)))
  have hE_sbar_F : MeasurableSet[vm.ℱ t] E_sbar :=
    hAmeas_F (by trivial : MeasurableSet ({Finset.univ \ s} : Set (Finset V)))
  have hBa_s : ∀ ω ∈ E_s, vm.opinionZeroSet t ω = s := fun _ hω => hω
  have hBa_sbar : ∀ ω ∈ E_sbar, vm.opinionZeroSet t ω = Finset.univ \ s := fun _ hω => hω
  -- Cylinder factorization at each anchor (per-path).
  have hcyl_s_at : ∀ π : Fin (N - t) → Finset V,
      (vm.μ : Measure _) (E_s ∩ cylinderOf vm t N π) = (vm.μ : Measure _) E_s *
        ∏ k ∈ Finset.range (N - t),
          (VoterModel.stepDist₂ G (t + k) (extendPath s π k))
            (extendPath s π (k + 1)) := by
    intro π
    have hcyl := cylinder_markov_finite_tuple G vm t (N - t) E_s hE_s_F s hBa_s
      (extendPath s π) (extendPath_zero s π)
    have hC_eq :
        E_s ∩ ⋂ j ∈ Finset.range (N - t),
            {ω | vm.opinionZeroSet (t + j + 1) ω = extendPath s π (j + 1)} =
          E_s ∩ cylinderOf vm t N π := by
      congr 1
      exact (cylinderOf_eq_extendPath_inter vm t N s π).symm
    rw [hC_eq] at hcyl
    exact hcyl
  have hcyl_sbar_at : ∀ π : Fin (N - t) → Finset V,
      (vm.μ : Measure _) (E_sbar ∩ cylinderOf vm t N π) = (vm.μ : Measure _) E_sbar *
        ∏ k ∈ Finset.range (N - t),
          (VoterModel.stepDist₂ G (t + k) (extendPath (Finset.univ \ s) π k))
            (extendPath (Finset.univ \ s) π (k + 1)) := by
    intro π
    have hcyl := cylinder_markov_finite_tuple G vm t (N - t) E_sbar hE_sbar_F
      (Finset.univ \ s) hBa_sbar (extendPath (Finset.univ \ s) π)
      (extendPath_zero (Finset.univ \ s) π)
    have hC_eq :
        E_sbar ∩ ⋂ j ∈ Finset.range (N - t),
            {ω | vm.opinionZeroSet (t + j + 1) ω = extendPath (Finset.univ \ s) π (j + 1)} =
          E_sbar ∩ cylinderOf vm t N π := by
      congr 1
      exact (cylinderOf_eq_extendPath_inter vm t N (Finset.univ \ s) π).symm
    rw [hC_eq] at hcyl
    exact hcyl
  -- Termwise equality (clean dispatch via the ∏ = 0 vs > 0 case split).
  have hterm_eq : ∀ π : Fin (N - t) → Finset V,
      term s E_s π = term (Finset.univ \ s) E_sbar (ι π) := by
    intro π
    show
      (∏ k ∈ Finset.range (N - t),
          (VoterModel.stepDist₂ G (t + k) (extendPath s π k))
            (extendPath s π (k + 1))).toReal *
      (if h : (E_s ∩ cylinderOf vm t N π).Nonempty then
          φ (T_next h.choose) (vm.S (T_next h.choose) h.choose)
        else 0) =
      (∏ k ∈ Finset.range (N - t),
          (VoterModel.stepDist₂ G (t + k) (extendPath (Finset.univ \ s) (ι π) k))
            (extendPath (Finset.univ \ s) (ι π) (k + 1))).toReal *
      (if h : (E_sbar ∩ cylinderOf vm t N (ι π)).Nonempty then
          φ (T_next h.choose) (vm.S (T_next h.choose) h.choose)
        else 0)
    rw [hprod_eq π]
    -- Goal: (∏ stepDist₂ on (univ\s)-anchor (ι π)).toReal * (if E_s ∩ cyl π then φ.. else 0)
    --     = (∏ stepDist₂ on (univ\s)-anchor (ι π)).toReal * (if E_sbar ∩ cyl ι π then φ.. else 0).
    -- Two cases on whether the (common) product equals 0.
    set P : ENNReal :=
      ∏ k ∈ Finset.range (N - t),
        (VoterModel.stepDist₂ G (t + k) (extendPath (Finset.univ \ s) (ι π) k))
          (extendPath (Finset.univ \ s) (ι π) (k + 1)) with hP_def
    by_cases hP_zero : P = 0
    · -- Both terms collapse: (P).toReal = 0 multiplies both if-blocks to 0.
      rw [hP_zero, ENNReal.toReal_zero, zero_mul, zero_mul]
    · -- P > 0. Then μ(E_s ∩ cyl π) > 0 (via hcyl_s_at, hprod_eq, hμE_s_pos);
      -- and μ(E_sbar ∩ cyl ι π) > 0 (via hcyl_sbar_at, hμE_sbar_pos). Hence both
      -- cylinders are nonempty. Use witness-equality.
      -- The product appearing in `hcyl_s_at π` equals P (via hprod_eq).
      have hP_eq_s :
          (∏ k ∈ Finset.range (N - t),
              (VoterModel.stepDist₂ G (t + k) (extendPath s π k))
                (extendPath s π (k + 1))) = P := by
        rw [hP_def, ← hprod_eq π]
      -- (a) μ(E_s ∩ cyl π) > 0:
      have hmu_s_pos : (vm.μ : Measure _) (E_s ∩ cylinderOf vm t N π) ≠ 0 := by
        rw [hcyl_s_at π, hP_eq_s]
        exact mul_ne_zero hμE_s_pos hP_zero
      have h₁ : (E_s ∩ cylinderOf vm t N π).Nonempty := by
        rcases Set.eq_empty_or_nonempty (E_s ∩ cylinderOf vm t N π) with hempty | hne
        · exfalso; apply hmu_s_pos; rw [hempty, measure_empty]
        · exact hne
      -- (b) μ(E_sbar ∩ cyl ι π) > 0:
      have hmu_sbar_pos : (vm.μ : Measure _) (E_sbar ∩ cylinderOf vm t N (ι π)) ≠ 0 := by
        rw [hcyl_sbar_at (ι π)]
        exact mul_ne_zero hμE_sbar_pos hP_zero
      have h₂ : (E_sbar ∩ cylinderOf vm t N (ι π)).Nonempty := by
        rcases Set.eq_empty_or_nonempty (E_sbar ∩ cylinderOf vm t N (ι π)) with hempty | hne
        · exfalso; apply hmu_sbar_pos; rw [hempty, measure_empty]
        · exact hne
      -- Both nonempty: use witness equality and congr.
      congr 1
      rw [dif_pos h₁, dif_pos h₂]
      set ω₁ := h₁.choose
      set ω₂ := h₂.choose
      have hω₁ : ω₁ ∈ E_s ∩ cylinderOf vm t N π := h₁.choose_spec
      have hω₂ : ω₂ ∈ E_sbar ∩ cylinderOf vm t N (ι π) := h₂.choose_spec
      exact hwitness_eq π ω₁ ω₂ hω₁ hω₂
  -- Step 2: reindex via the involution `ι`.
  -- Use `Fintype.sum_bijective` directly: with `e := ι`, `f := term s E_s`,
  -- `g := term (univ\s) E_sbar`, the bijection condition is `f π = g (ι π)`,
  -- which is exactly `hterm_eq`.
  have hι_bij : Function.Bijective ι :=
    Function.bijective_iff_has_inverse.mpr ⟨ι, hι_invol, hι_invol⟩
  exact Fintype.sum_bijective ι hι_bij _ _ hterm_eq

end VoterModel
