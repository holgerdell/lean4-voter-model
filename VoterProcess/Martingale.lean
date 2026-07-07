module

import TemporalGraph.Basic
import VoterProcess.Volume
import VoterProcess.TwoOpinion
public import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.CondVar
public import VoterProcess.Step
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Algebra.Order.Star.Real

/-! ## Martingale and supermartingale properties of the voter model

Proves that `Vol(A_t)` is a martingale and `Vol(S_t)` is a supermartingale
w.r.t. the standard filtration `vm.ℱ = σ(A_0, …, A_t)`.

## Main results

- `vol_opinion_martingale`: `Vol(A_t)` and `Vol(V \ A_t)` are both martingales.
- `vol_minority_supermartingale`: `Vol(S_t)` is a supermartingale.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators

noncomputable section

namespace TemporalGraph

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]

section VoterCondExp

variable {Ω : Type*} [MeasurableSpace Ω] {G : TemporalGraph V}

/-- Any function of `vm.opinionZeroSet j` is integrable since `Finset V` is finite. -/
private lemma voter_integrable_comp_A
    (vm : VoterModelAbstract G 2 Ω) (f : Finset V → ℝ) (j : ℕ) :
    Integrable (fun ω => f (vm.opinionZeroSet j ω)) vm.μ := by
  have hA_meas : @Measurable Ω (Finset V) _ ⊤ (vm.opinionZeroSet j) :=
    fun s _ => vm.A_meas j _ ⟨s, trivial, rfl⟩
  exact Integrable.of_bound
    (measurable_of_finite f |>.comp hA_meas).aestronglyMeasurable
    (∑ s : Finset V, ‖f s‖)
    (ae_of_all _ fun ω =>
      Finset.single_le_sum (fun s _ => norm_nonneg (f s)) (Finset.mem_univ (vm.opinionZeroSet j ω)))

/-- On an `vm.ℱ j`-measurable set `B`, integrating `f (vm.opinionZeroSet (j + 1))` over `B`
agrees with integrating the step-distribution average over `B`. -/
private lemma voter_setIntegral_filtration
    (vm : VoterModelAbstract G 2 Ω) (f : Finset V → ℝ) (j : ℕ)
    (B : Set Ω) (hB : @MeasurableSet Ω (vm.ℱ j) B) :
    ∫ ω in B, f (vm.opinionZeroSet (j + 1) ω) ∂vm.μ =
    ∫ ω in B, (∫ S', f S' ∂(VoterModel.stepDist₂ G j (vm.opinionZeroSet j ω)).toMeasure) ∂vm.μ := by
  have hBm : MeasurableSet B := vm.ℱ.le j _ hB
  have hA_meas : @Measurable Ω (Finset V) _ ⊤ (vm.opinionZeroSet j) :=
    fun s _ => vm.A_meas j _ ⟨s, trivial, rfl⟩
  have hAsucc_meas : @Measurable Ω (Finset V) _ ⊤ (vm.opinionZeroSet (j + 1)) :=
    fun s _ => vm.A_meas (j + 1) _ ⟨s, trivial, rfl⟩
  have hB_eq : B = ⋃ s : Finset V, B ∩ {ω | vm.opinionZeroSet j ω = s} := by
    ext ω
    simp [eq_comm]
  have hmA : ∀ s : Finset V, MeasurableSet (B ∩ {ω : Ω | vm.opinionZeroSet j ω = s}) :=
    fun s => hBm.inter (hA_meas (measurableSet_singleton s))
  have hpw : Pairwise fun a b => Disjoint (B ∩ {ω : Ω | vm.opinionZeroSet j ω = a})
      (B ∩ {ω | vm.opinionZeroSet j ω = b}) :=
    fun a b hab => Set.disjoint_left.mpr fun ω ha hb => hab (ha.2 ▸ hb.2)
  rw [hB_eq]
  rw [integral_iUnion_fintype hmA hpw
    (fun s => (voter_integrable_comp_A vm f (j + 1)).integrableOn)]
  rw [integral_iUnion_fintype hmA hpw
    (fun s => (voter_integrable_comp_A vm
      (fun s' => ∫ T', f T' ∂(VoterModel.stepDist₂ G j s').toMeasure) j).integrableOn)]
  apply Finset.sum_congr rfl
  intro s _
  have hrhs : ∫ ω in B ∩ {ω | vm.opinionZeroSet j ω = s},
      (∫ S', f S' ∂(VoterModel.stepDist₂ G j (vm.opinionZeroSet j ω)).toMeasure) ∂vm.μ =
      (∫ S', f S' ∂(VoterModel.stepDist₂ G j s).toMeasure) *
        ((vm.μ : Measure _) (B ∩ {ω | vm.opinionZeroSet j ω = s})).toReal := by
    have heq : ∀ ω ∈ B ∩ {ω | vm.opinionZeroSet j ω = s},
        (∫ S', f S' ∂(VoterModel.stepDist₂ G j (vm.opinionZeroSet j ω)).toMeasure) =
          ∫ S', f S' ∂(VoterModel.stepDist₂ G j s).toMeasure :=
      fun ω hω => by rw [hω.2]
    rw [setIntegral_congr_fun (hmA s) heq,
      integral_const, smul_eq_mul, mul_comm, measureReal_def,
      Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  have hlhs : ∫ ω in B ∩ {ω | vm.opinionZeroSet j ω = s}, f (vm.opinionZeroSet (j + 1) ω) ∂vm.μ =
      (∫ S', f S' ∂(VoterModel.stepDist₂ G j s).toMeasure) *
        ((vm.μ : Measure _) (B ∩ {ω | vm.opinionZeroSet j ω = s})).toReal := by
    have hmP : ∀ s' : Finset V,
        MeasurableSet (B ∩ {ω | vm.opinionZeroSet j ω = s} ∩ {ω | vm.opinionZeroSet (j + 1) ω = s'}) :=
      fun s' => (hmA s).inter (hAsucc_meas (measurableSet_singleton s'))
    have hset_eq : B ∩ {ω | vm.opinionZeroSet j ω = s} =
        ⋃ s' : Finset V, B ∩ {ω | vm.opinionZeroSet j ω = s} ∩ {ω | vm.opinionZeroSet (j + 1) ω = s'} := by
      ext ω
      simp [eq_comm]
    rw [hset_eq]
    rw [integral_iUnion_fintype hmP
      (fun a b hab => Set.disjoint_left.mpr fun ω ha hb => hab (ha.2 ▸ hb.2))
      (fun s' => (voter_integrable_comp_A vm f (j + 1)).integrableOn)]
    have hcf : ∀ s', ∫ ω in B ∩ {ω | vm.opinionZeroSet j ω = s} ∩ {ω | vm.opinionZeroSet (j + 1) ω = s'},
        f (vm.opinionZeroSet (j + 1) ω) ∂vm.μ =
          f s' * ((vm.μ : Measure _) (B ∩ {ω | vm.opinionZeroSet j ω = s} ∩ {ω | vm.opinionZeroSet (j + 1) ω = s'})).toReal :=
      fun s' => by
        rw [setIntegral_congr_fun (hmP s') (fun ω hω => congr_arg f hω.2)]
        rw [integral_const, smul_eq_mul, mul_comm, measureReal_def,
          Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    simp_rw [hcf]
    have hBs_filt : @MeasurableSet Ω (⨆ k ∈ Finset.Iic j,
        MeasurableSpace.comap (vm.opinionZeroSet k) ⊤) (B ∩ {ω | vm.opinionZeroSet j ω = s}) := by
      apply @MeasurableSet.inter _ _ _ _ (vm.fmeas_to_Asup hB)
      exact Measurable.of_comap_le
        (le_iSup₂_of_le j (Finset.mem_Iic.mpr le_rfl) le_rfl)
        (measurableSet_singleton s)
    have hpiece : ∀ s',
        (vm.μ : Measure _) (B ∩ {ω | vm.opinionZeroSet j ω = s} ∩ {ω | vm.opinionZeroSet (j + 1) ω = s'}) =
          (VoterModel.stepDist₂ G j s) s' * (vm.μ : Measure _) (B ∩ {ω | vm.opinionZeroSet j ω = s}) := fun s' => by
      have := vm.A_markovProperty j s' (B ∩ {ω | vm.opinionZeroSet j ω = s}) hBs_filt
      rw [this]
      rw [setLIntegral_congr_fun (hmA s) (fun ω hω => by rw [hω.2])]
      rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, mul_comm]
    simp_rw [hpiece, ENNReal.toReal_mul, ← mul_assoc]
    rw [← Finset.sum_mul]
    have hsum_eq : ∑ s' : Finset V, f s' * ((VoterModel.stepDist₂ G j s) s').toReal =
        ∫ S', f S' ∂(VoterModel.stepDist₂ G j s).toMeasure := by
      rw [PMF.integral_eq_sum]
      congr 1
      ext s'
      rw [smul_eq_mul, mul_comm]
    rw [hsum_eq, ← hset_eq]
  linarith [hlhs, hrhs]

/-- Conditional-expectation form of `vm.A_markovProperty`. -/
private lemma voter_condExp_eq_stepDist₂Avg
    (vm : VoterModelAbstract G 2 Ω) (f : Finset V → ℝ) (j : ℕ) :
    (vm.μ : Measure _)[fun ω => f (vm.opinionZeroSet (j + 1) ω) | vm.ℱ j] =ᵐ[(vm.μ : Measure _)]
      fun ω => (∫ S', f S' ∂(VoterModel.stepDist₂ G j (vm.opinionZeroSet j ω)).toMeasure) := by
  have hm : vm.ℱ.seq j ≤ ‹MeasurableSpace Ω› := vm.ℱ.le j
  have hA_Fmeas : @Measurable Ω (Finset V) (vm.ℱ j) ⊤ (vm.opinionZeroSet j) :=
    (vm.A_stronglyAdapted j).measurable
  have hstep_avg_meas : Measurable (fun s => ∫ S', f S' ∂(VoterModel.stepDist₂ G j s).toMeasure) :=
    measurable_of_finite _
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm
    (voter_integrable_comp_A vm f (j + 1))
    (fun A _ _ => (voter_integrable_comp_A vm
      (fun s' => ∫ T', f T' ∂(VoterModel.stepDist₂ G j s').toMeasure) j).integrableOn)
    (fun A hA _ => (voter_setIntegral_filtration vm f j A hA).symm)
    ?_).symm
  exact (hstep_avg_meas.comp hA_Fmeas).aestronglyMeasurable

end VoterCondExp

/-- \label{lem:volume_A_martingale}

**Martingale property**: `Vol(A_t)` and `Vol(V \ A_t)` are both martingales
w.r.t. `vm.ℱ`. Adaptedness is derived from `A_stronglyAdapted`, and the
conditional-expectation step is derived from `vm.A_markovProperty`. -/
theorem vol_opinion_martingale
    (G : TemporalGraphFixedDegree V)
    {Ω : Type*} [MeasurableSpace Ω]
    (vm : VoterModelAbstract G 2 Ω) :
    Martingale (fun t ω => ((G.snapshot t).volume (vm.opinionZeroSet t ω) : ℝ)) vm.ℱ vm.μ ∧
    Martingale (fun t ω => ((G.snapshot t).volume (univ \ vm.opinionZeroSet t ω) : ℝ)) vm.ℱ vm.μ := by
  have hAdapted : StronglyAdapted vm.ℱ (fun t ω => (volume G.toTemporalGraph t (vm.opinionZeroSet t ω) : ℝ)) := by
    intro t
    have hA : StronglyMeasurable[vm.ℱ t] (vm.opinionZeroSet t) := TemporalGraph.VoterModelAbstract.A_stronglyAdapted vm t
    have hvol : Measurable (fun s : Finset V => (volume G.toTemporalGraph t s : ℝ)) := by
      exact measurable_of_finite _
    exact hvol.stronglyMeasurable.comp_measurable hA.measurable
  have hAcAdapted : StronglyAdapted vm.ℱ (fun t ω => (volume G.toTemporalGraph t (univ \ vm.opinionZeroSet t ω) : ℝ)) := by
    intro t
    have hA_comp : @Measurable Ω (Finset V) (vm.ℱ t) ⊤ (fun ω => univ \ vm.opinionZeroSet t ω) := by
      have hA : @Measurable Ω (Finset V) (vm.ℱ t) ⊤ (vm.opinionZeroSet t) :=
        (TemporalGraph.VoterModelAbstract.A_stronglyAdapted vm t).measurable
      exact measurable_of_finite _ |>.comp hA
    have hvol : Measurable (fun s : Finset V => (volume G.toTemporalGraph t s : ℝ)) := by
      exact measurable_of_finite _
    exact hvol.stronglyMeasurable.comp_measurable hA_comp
  have hIntA : ∀ t, Integrable (fun ω => (volume G.toTemporalGraph t (vm.opinionZeroSet t ω) : ℝ)) vm.μ := by
    intro t
    exact voter_integrable_comp_A vm (fun s => (volume G.toTemporalGraph t s : ℝ)) t
  have hStepA : ∀ i,
      (fun ω => (volume G.toTemporalGraph i (vm.opinionZeroSet i ω) : ℝ)) =ᵐ[(vm.μ : Measure _)]
        (vm.μ : Measure _)[fun ω => (volume G.toTemporalGraph (i + 1) (vm.opinionZeroSet (i + 1) ω) : ℝ) | vm.ℱ i] := by
    intro i
    refine (voter_condExp_eq_stepDist₂Avg vm (fun s => (volume G.toTemporalGraph (i + 1) s : ℝ)) i).trans ?_ |>.symm
    exact Filter.EventuallyEq.of_eq <| by
      funext ω
      simpa [VoterModel.opinionProcess₂] using VoterModel.expected_volume_constant G i (vm.opinionZeroSet i ω) 1
  have hVolA : Martingale (fun t ω => (volume G.toTemporalGraph t (vm.opinionZeroSet t ω) : ℝ)) vm.ℱ vm.μ := by
    exact martingale_nat hAdapted hIntA hStepA
  have hAc_eq :
      (fun t ω => (volume G.toTemporalGraph t (univ \ vm.opinionZeroSet t ω) : ℝ)) =
        fun t ω => (volume G.toTemporalGraph 0 univ : ℝ) - (volume G.toTemporalGraph t (vm.opinionZeroSet t ω) : ℝ) := by
    funext t ω
    have hsum : volume G.toTemporalGraph t (vm.opinionZeroSet t ω) + volume G.toTemporalGraph t (univ \ vm.opinionZeroSet t ω) = volume G.toTemporalGraph t univ := by
      simp only [TemporalGraph.volume, SimpleGraph.volume]
      rw [← Finset.sum_union]
      · rw [Finset.union_sdiff_of_subset (Finset.subset_univ _)]
      · exact Finset.disjoint_sdiff
    have hsum_real : (volume G.toTemporalGraph t (vm.opinionZeroSet t ω) : ℝ) + (volume G.toTemporalGraph t (univ \ vm.opinionZeroSet t ω) : ℝ) =
        (volume G.toTemporalGraph t univ : ℝ) := by
      exact_mod_cast hsum
    have hfixed : (volume G.toTemporalGraph t univ : ℝ) = (volume G.toTemporalGraph 0 univ : ℝ) := by
      exact_mod_cast G.volume_fixed univ t 0
    linarith
  have hVolAc : Martingale (fun t ω => (volume G.toTemporalGraph t (univ \ vm.opinionZeroSet t ω) : ℝ)) vm.ℱ vm.μ := by
    rw [hAc_eq]
    exact (martingale_const vm.ℱ vm.μ (volume G.toTemporalGraph 0 univ : ℝ)).sub hVolA
  exact ⟨hVolA, hVolAc⟩

/-- `Vol(S_t)` is a supermartingale w.r.t. `vm.ℱ`. Uses the fact that
`S_t = minoritySet` is the pointwise minimum of `A_t` and `V \ A_t` by volume,
and derives the two volume martingales from `vol_opinion_martingale`. -/
theorem vol_minority_supermartingale
    {Ω : Type*} [MeasurableSpace Ω]
    {G : TemporalGraphFixedDegree V}
    (vm : VoterModelAbstract G 2 Ω) :
    Supermartingale (fun t ω => ((G.snapshot t).volume (vm.S t ω) : ℝ)) vm.ℱ vm.μ := by
  obtain ⟨hVolA, hVolAc⟩ := vol_opinion_martingale G vm
  have h := VoterModel.vol_minority_supermartingale vm hVolA hVolAc
  convert h using 2
  ext t
  simp only [VoterModel.volMinorityProcess, VoterModelAbstract.S, _root_.VoterModel.minoritySet]

/-- `√Vol(S_t)` is a supermartingale w.r.t. `vm.ℱ`.

Proof strategy: for `i ≤ j`, let `h = E[psiS j | ℱ i]`. Since `(psiS j)² = volS j`, the
conditional variance identity gives `h² ≤ E[(psiS j)² | ℱ i] = E[volS j | ℱ i] ≤ volS i
= (psiS i)²`. Combined with `h ≥ 0` and `psiS i ≥ 0` this yields `h ≤ psiS i`. -/
theorem psiS_supermartingale
    {Ω : Type*} [MeasurableSpace Ω]
    {G : TemporalGraphFixedDegree V}
    (vm : G.VoterModelAbstract 2 Ω) :
    Supermartingale vm.psiS vm.ℱ vm.μ := by
  have hVolSup : Supermartingale (fun t ω => (volume G.toTemporalGraph t (vm.S t ω) : ℝ)) vm.ℱ vm.μ :=
    vol_minority_supermartingale vm
  -- Helper: vol function is m-strongly measurable at each time
  have hv_meas : ∀ k, StronglyMeasurable[vm.ℱ k] (fun ω => (volume G.toTemporalGraph k (vm.S k ω) : ℝ)) :=
    hVolSup.stronglyAdapted
  -- Helper: psiS k is AEStronglyMeasurable w.r.t. vm.μ
  have hpsi_aemeas : ∀ k, AEStronglyMeasurable (vm.psiS k) vm.μ := fun k =>
    Real.continuous_sqrt.comp_aestronglyMeasurable
      ((hv_meas k).mono (vm.ℱ.le k)).aestronglyMeasurable
  -- Helper: psiS k ω ≤ sqrt(volume G.toTemporalGraph k univ) for all ω
  have hpsi_bnd : ∀ k, ∀ᵐ ω ∂(vm.μ : Measure _), ‖vm.psiS k ω‖ ≤ Real.sqrt (volume G.toTemporalGraph k Finset.univ : ℝ) :=
    fun k => ae_of_all _ fun ω => by
      simp only [Real.norm_of_nonneg (Real.sqrt_nonneg _), VoterModelAbstract.psiS, potential]
      exact Real.sqrt_le_sqrt (by exact_mod_cast Finset.sum_le_sum_of_subset (Finset.subset_univ _))
  refine ⟨?adapted, ?condExp, ?integrable⟩
  case adapted =>
    -- psiS i = sqrt ∘ volS i, and volS i is ℱ i-strongly measurable
    intro i
    exact Real.continuous_sqrt.comp_stronglyMeasurable (hv_meas i)
  case integrable =>
    intro i
    exact memLp_one_iff_integrable.mp (MemLp.of_bound (hpsi_aemeas i) _ (hpsi_bnd i))
  case condExp =>
    intro i j hij
    -- Step 1: psiS j ∈ MemLp 2
    have hpsiLp : MemLp (vm.psiS j) 2 vm.μ :=
      MemLp.of_bound (hpsi_aemeas j) _ (hpsi_bnd j)
    -- Step 2: nonnegativity
    have hpsiS_nn : 0 ≤ᵐ[(vm.μ : Measure _)] vm.psiS i := ae_of_all _ fun ω => Real.sqrt_nonneg _
    have hcond_nn : 0 ≤ᵐ[(vm.μ : Measure _)] (vm.μ : Measure _)[vm.psiS j | vm.ℱ i] :=
      condExp_nonneg (ae_of_all _ fun ω => Real.sqrt_nonneg _)
    -- Step 3: (psiS j)^2 = volS j pointwise
    have hpsisq : vm.psiS j ^ 2 =ᵐ[(vm.μ : Measure _)] fun ω => (volume G.toTemporalGraph j (vm.S j ω) : ℝ) :=
      ae_of_all _ fun ω => by
        simp only [Pi.pow_apply, VoterModelAbstract.psiS, potential]
        exact Real.sq_sqrt (by positivity)
    -- Step 4: conditional variance identity: Var[psiS j | ℱ i] = E[(psiS j)^2 | ℱ i] - h^2
    have hvar : ProbabilityTheory.condVar (vm.ℱ i) (vm.psiS j) vm.μ =ᵐ[(vm.μ : Measure _)]
        (vm.μ : Measure _)[vm.psiS j ^ 2 | vm.ℱ i] - (vm.μ : Measure _)[vm.psiS j | vm.ℱ i] ^ 2 :=
      condVar_ae_eq_condExp_sq_sub_sq_condExp (vm.ℱ.le i) hpsiLp
    -- Var[psiS j | ℱ i] ≥ 0 (condExp of a nonneg function)
    have hvar_nn : 0 ≤ᵐ[(vm.μ : Measure _)] ProbabilityTheory.condVar (vm.ℱ i) (vm.psiS j) vm.μ :=
      condExp_nonneg (ae_of_all _ fun ω => sq_nonneg _)
    -- Step 5: E[(psiS j)^2 | ℱ i] = E[volS j | ℱ i] ≤ volS i
    have hcondexp_sq_eq : (vm.μ : Measure _)[vm.psiS j ^ 2 | vm.ℱ i] =ᵐ[(vm.μ : Measure _)]
        (vm.μ : Measure _)[fun ω => (volume G.toTemporalGraph j (vm.S j ω) : ℝ) | vm.ℱ i] :=
      condExp_congr_ae hpsisq
    have hvol_le : (vm.μ : Measure _)[fun ω => (volume G.toTemporalGraph j (vm.S j ω) : ℝ) | vm.ℱ i] ≤ᵐ[(vm.μ : Measure _)]
        fun ω => (volume G.toTemporalGraph i (vm.S i ω) : ℝ) :=
      hVolSup.2.1 i j hij
    -- Step 6: h^2 ≤ (psiS i)^2 a.e.
    have hcond_sq_le : (vm.μ : Measure _)[vm.psiS j | vm.ℱ i] ^ 2 ≤ᵐ[(vm.μ : Measure _)] vm.psiS i ^ 2 := by
      filter_upwards [hvar, hvar_nn, hcondexp_sq_eq, hvol_le] with ω h1 h2 h3 h4
      simp only [Pi.pow_apply, Pi.sub_apply, Pi.zero_apply] at h1 h2 ⊢
      -- h2 : 0 ≤ Var ω = h1 : E[f^2|m] ω - h^2 ω, so h^2 ω ≤ E[f^2|m] ω
      have hh2_le : ((vm.μ : Measure _)[vm.psiS j | vm.ℱ i]) ω ^ 2 ≤ ((vm.μ : Measure _)[vm.psiS j ^ 2 | vm.ℱ i]) ω := by
        linarith [h2.trans_eq h1]
      -- psiS i ω ^ 2 = vol(S i ω) (as reals)
      have hpsi_sq : vm.psiS i ω ^ 2 = (volume G.toTemporalGraph i (vm.S i ω) : ℝ) := by
        simp only [VoterModelAbstract.psiS, potential]; exact Real.sq_sqrt (by positivity)
      linarith [h3 ▸ hh2_le, h4]
    -- Step 7: h ≤ psiS i from h^2 ≤ (psiS i)^2 and both ≥ 0
    filter_upwards [hcond_sq_le, hcond_nn, hpsiS_nn] with ω h1 h2 h3
    simp only [Pi.pow_apply, Pi.zero_apply] at h1 h2 h3
    exact (sq_le_sq₀ h2 h3).mp h1

end TemporalGraph
