module

public import TemporalGraph.Degree
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import VoterProcess.TwoOpinion
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Algebra.Order.Star.Real
import VoterProcess.Expectation
public import VoterProcess.Step

@[expose] public section
open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators

noncomputable section

namespace VoterModel

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]

/-! ## Potential-decrease helper machinery

Conditional-expectation form of the voter Markov property (`section VoterCondExp`) and
the bulk of the one-step / stable-interval helper lemmas (`section PotDecHelpers`).
These are the private building blocks used by the public `potential_decrease_*` theorems. -/
section VoterCondExp

variable {Ω : Type*} [MeasurableSpace Ω] {G : TemporalGraph V}

/-- Any function of `vm.opinionZeroSet j` is integrable (Finset V is finite). -/
lemma voter_integrable_comp_A
    (vm : G.VoterModelAbstract 2 Ω) (f : Finset V → ℝ) (j : ℕ) :
    Integrable (fun ω => f (vm.opinionZeroSet j ω)) vm.μ := by
  have hA_meas : @Measurable Ω (Finset V) _ ⊤ (vm.opinionZeroSet j) :=
    fun s _ => vm.A_meas j _ ⟨s, trivial, rfl⟩
  exact Integrable.of_bound
    (measurable_of_finite f |>.comp hA_meas).aestronglyMeasurable
    (∑ s : Finset V, ‖f s‖)
    (ae_of_all _ fun ω =>
      Finset.single_le_sum (fun s _ => norm_nonneg (f s)) (Finset.mem_univ (vm.opinionZeroSet j ω)))

/-- On a `vm.ℱ j`-measurable set `B`, the set-integral of `f(vm.opinionZeroSet(j+1))` equals the
set-integral of the stepDist₂ average `∫ S', f S' ∂stepDist₂(G, j, vm.opinionZeroSet j ω)`.
Proved by decomposing over the atoms `{vm.opinionZeroSet j = s}` and applying `vm.A_markovProperty`. -/
private lemma voter_setIntegral_filtration
    (vm : G.VoterModelAbstract 2 Ω) (f : Finset V → ℝ) (j : ℕ)
    (B : Set Ω) (hB : @MeasurableSet Ω (vm.ℱ j) B) :
    ∫ ω in B, f (vm.opinionZeroSet (j + 1) ω) ∂vm.μ =
    ∫ ω in B, ∫ S', f S' ∂(stepDist₂ G j (vm.opinionZeroSet j ω)).toMeasure ∂vm.μ := by
  have hBm : MeasurableSet B := vm.ℱ.le j _ hB
  -- Measurability of vm.opinionZeroSet j
  have hA_meas : @Measurable Ω (Finset V) _ ⊤ (vm.opinionZeroSet j) :=
    fun s _ => vm.A_meas j _ ⟨s, trivial, rfl⟩
  have hAsucc_meas : @Measurable Ω (Finset V) _ ⊤ (vm.opinionZeroSet (j + 1)) :=
    fun s _ => vm.A_meas (j + 1) _ ⟨s, trivial, rfl⟩
  -- Partition: B = ⋃ s, B ∩ {vm.opinionZeroSet j = s}
  have hB_eq : B = ⋃ s : Finset V, B ∩ {ω | vm.opinionZeroSet j ω = s} := by
    ext ω; simp [eq_comm]
  have hmA : ∀ s : Finset V, MeasurableSet (B ∩ {ω : Ω | vm.opinionZeroSet j ω = s}) :=
    fun s => hBm.inter (hA_meas (measurableSet_singleton s))
  have hpw : Pairwise fun a b => Disjoint (B ∩ {ω : Ω | vm.opinionZeroSet j ω = a})
      (B ∩ {ω | vm.opinionZeroSet j ω = b}) :=
    fun a b hab => Set.disjoint_left.mpr fun ω ha hb => hab (ha.2 ▸ hb.2)
  -- Split both integrals over atoms
  rw [hB_eq]
  rw [integral_iUnion_fintype hmA hpw
    (fun s => (voter_integrable_comp_A vm f (j + 1)).integrableOn)]
  rw [integral_iUnion_fintype hmA hpw
    (fun s => (voter_integrable_comp_A vm
      (fun s' => ∫ T', f T' ∂(stepDist₂ G j s').toMeasure) j).integrableOn)]
  apply Finset.sum_congr rfl; intro s _
  -- On each atom: vm.opinionZeroSet j ω = s, so stepDist₂ average is constant
  -- RHS on atom: ∫_B∩{A_j=s} (∫ f dstepDist₂(s)) = (∫ f dstepDist₂(s)) * μ(B ∩ {A_j=s})
  have hrhs : ∫ ω in B ∩ {ω | vm.opinionZeroSet j ω = s},
      ∫ S', f S' ∂(stepDist₂ G j (vm.opinionZeroSet j ω)).toMeasure ∂vm.μ =
      (∫ S', f S' ∂(stepDist₂ G j s).toMeasure) *
        ((vm.μ : Measure _) (B ∩ {ω | vm.opinionZeroSet j ω = s})).toReal := by
    have heq : ∀ ω ∈ B ∩ {ω | vm.opinionZeroSet j ω = s},
        (∫ S', f S' ∂(stepDist₂ G j (vm.opinionZeroSet j ω)).toMeasure) =
        ∫ S', f S' ∂(stepDist₂ G j s).toMeasure :=
      fun ω hω => by rw [hω.2]
    rw [setIntegral_congr_fun (hmA s) heq,
        integral_const, smul_eq_mul, mul_comm, measureReal_def,
        Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  -- LHS on atom: decompose over values of A(j+1)
  have hlhs : ∫ ω in B ∩ {ω | vm.opinionZeroSet j ω = s}, f (vm.opinionZeroSet (j + 1) ω) ∂vm.μ =
      (∫ S', f S' ∂(stepDist₂ G j s).toMeasure) *
        ((vm.μ : Measure _) (B ∩ {ω | vm.opinionZeroSet j ω = s})).toReal := by
    -- Decompose over {A(j+1) = s'}
    have hmP : ∀ s' : Finset V,
        MeasurableSet (B ∩ {ω | vm.opinionZeroSet j ω = s} ∩ {ω | vm.opinionZeroSet (j + 1) ω = s'}) :=
      fun s' => (hmA s).inter (hAsucc_meas (measurableSet_singleton s'))
    have hset_eq : B ∩ {ω | vm.opinionZeroSet j ω = s} =
        ⋃ s' : Finset V, B ∩ {ω | vm.opinionZeroSet j ω = s} ∩ {ω | vm.opinionZeroSet (j + 1) ω = s'} := by
      ext ω; simp [eq_comm]
    rw [hset_eq]
    rw [integral_iUnion_fintype hmP
        (fun a b hab => Set.disjoint_left.mpr fun ω ha hb => hab (ha.2 ▸ hb.2))
        (fun s' => (voter_integrable_comp_A vm f (j + 1)).integrableOn)]
    -- On each piece, f(A(j+1)) = f(s')
    have hcf : ∀ s', ∫ ω in B ∩ {ω | vm.opinionZeroSet j ω = s} ∩ {ω | vm.opinionZeroSet (j + 1) ω = s'},
        f (vm.opinionZeroSet (j + 1) ω) ∂vm.μ =
        f s' * ((vm.μ : Measure _) (B ∩ {ω | vm.opinionZeroSet j ω = s} ∩ {ω | vm.opinionZeroSet (j + 1) ω = s'})).toReal :=
      fun s' => by
        rw [setIntegral_congr_fun (hmP s') (fun ω hω => congr_arg f hω.2)]
        rw [integral_const, smul_eq_mul, mul_comm, measureReal_def,
            Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    simp_rw [hcf]
    -- Apply markovProperty: B ∩ {A_j = s} is vm.ℱ j-measurable
    have hBs_filt : @MeasurableSet Ω (⨆ k ∈ Finset.Iic j,
        MeasurableSpace.comap (vm.opinionZeroSet k) ⊤) (B ∩ {ω | vm.opinionZeroSet j ω = s}) := by
      apply @MeasurableSet.inter _ _ _ _ (vm.fmeas_to_Asup hB)
      exact Measurable.of_comap_le
        (le_iSup₂_of_le j (Finset.mem_Iic.mpr le_rfl) le_rfl)
        (measurableSet_singleton s)
    -- markovProperty gives: μ(B ∩ {A_j=s} ∩ {A(j+1)=s'}) = ∫⁻_{B∩{A_j=s}} stepDist₂(j,A_j)(s') dμ
    have hpiece : ∀ s', (vm.μ : Measure _) (B ∩ {ω | vm.opinionZeroSet j ω = s} ∩ {ω | vm.opinionZeroSet (j + 1) ω = s'}) =
        (stepDist₂ G j s) s' * (vm.μ : Measure _) (B ∩ {ω | vm.opinionZeroSet j ω = s}) := fun s' => by
      have := vm.A_markovProperty j s' (B ∩ {ω | vm.opinionZeroSet j ω = s}) hBs_filt
      rw [this]
      rw [setLIntegral_congr_fun (hmA s) (fun ω hω => by rw [hω.2])]
      rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, mul_comm]
    simp_rw [hpiece, ENNReal.toReal_mul, ← mul_assoc]
    -- Now: ∑ s', f(s') * stepDist₂(s)(s').toReal * μ(B∩{A_j=s}).toReal
    --     = (∫ f dstepDist₂(s)) * μ(B∩{A_j=s}).toReal
    rw [← Finset.sum_mul]
    -- ∑ s', f(s') * stepDist₂(s)(s').toReal = ∫ S', f S' ∂stepDist₂(j,s).toMeasure
    have hsum_eq : ∑ s' : Finset V, f s' * ((stepDist₂ G j s) s').toReal =
        ∫ S', f S' ∂(stepDist₂ G j s).toMeasure := by
      rw [PMF.integral_eq_sum]
      congr 1; ext s'; rw [smul_eq_mul, mul_comm]
    rw [hsum_eq, ← hset_eq]
  linarith [hlhs, hrhs]

/-- **Conditional expectation form of the voter model Markov property.**

`E[f(vm.opinionZeroSet(j+1)) | vm.ℱ j] = (fun ω => ∫ S', f S' ∂stepDist₂(G, j, vm.opinionZeroSet j ω))` a.s.

This lifts `vm.A_markovProperty` (a measure-level identity) to the conditional-expectation level,
following the same pattern as `MarkovChain.condExp_succ_eq_kernelAvg`. -/
lemma voter_condExp_eq_stepDist₂Avg
    (vm : G.VoterModelAbstract 2 Ω) (f : Finset V → ℝ) (j : ℕ) :
    (vm.μ : Measure _)[fun ω => f (vm.opinionZeroSet (j + 1) ω) | vm.ℱ j] =ᵐ[(vm.μ : Measure _)]
      fun ω => ∫ S', f S' ∂(stepDist₂ G j (vm.opinionZeroSet j ω)).toMeasure := by
  have hm : vm.ℱ.seq j ≤ ‹MeasurableSpace Ω› := vm.ℱ.le j
  have hA_meas : @Measurable Ω (Finset V) _ ⊤ (vm.opinionZeroSet j) :=
    fun s _ => vm.A_meas j _ ⟨s, trivial, rfl⟩
  -- vm.opinionZeroSet j is measurable w.r.t. vm.ℱ j
  have hA_Fmeas : @Measurable Ω (Finset V) (vm.ℱ j) ⊤ (vm.opinionZeroSet j) :=
    (vm.A_stronglyAdapted j).measurable
  -- The stepDist₂ average function is measurable as a composition
  have hstep_avg_meas : Measurable (fun s => ∫ S', f S' ∂(stepDist₂ G j s).toMeasure) :=
    measurable_of_finite _
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm
    (voter_integrable_comp_A vm f (j + 1))
    (fun A _ _ => (voter_integrable_comp_A vm
      (fun s' => ∫ T', f T' ∂(stepDist₂ G j s').toMeasure) j).integrableOn)
    (fun A hA _ => (voter_setIntegral_filtration vm f j A hA).symm)
    ?_).symm
  -- AEStronglyMeasurable w.r.t. vm.ℱ j: the function factors through vm.opinionZeroSet j
  exact (hstep_avg_meas.comp hA_Fmeas).aestronglyMeasurable

end VoterCondExp

/-! ## Helper lemmas for potential decrease

Two private lemmas used to prove `potential_decrease_one_step`:
1. `sqrt_le_linear_minus_quadratic` — pointwise upper bound on sqrt
   with a quadratic correction term (follows from a clean AM-GM identity).
2. `stepDist₂_variance_lb` — lower bound on the variance of `Vol(A_{t+1})`
   under one voter step, using the independence of vertex updates. -/

section PotDecHelpers

variable {Ω : Type*} [MeasurableSpace Ω]



/-- **Taylor bound for √(1+x).**

For `x ≥ -1`: `√(1+x) ≤ 1 + x/2 - x²/8 + x³/16`.

This is the third-order Taylor upper bound for the concave function `√(1+x)`.
The bound is tight at `x = 0` and the error term `x⁴/...` is always non-negative. -/
private lemma sqrt_one_add_taylor3 (x : ℝ) (hx : -1 ≤ x) :
    Real.sqrt (1 + x) ≤ 1 + x / 2 - x ^ 2 / 8 + x ^ 3 / 16 := by
  have hp : 0 ≤ 1 + x / 2 - x ^ 2 / 8 + x ^ 3 / 16 := by
    nlinarith [sq_nonneg (x + 1), sq_nonneg x]
  have hsq : 1 + x ≤ (1 + x / 2 - x ^ 2 / 8 + x ^ 3 / 16) ^ 2 := by
    nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x - 2), sq_nonneg x, sq_nonneg (x * (x + 1))]
  calc Real.sqrt (1 + x)
      ≤ Real.sqrt ((1 + x / 2 - x ^ 2 / 8 + x ^ 3 / 16) ^ 2) := Real.sqrt_le_sqrt (by linarith)
    _ = |1 + x / 2 - x ^ 2 / 8 + x ^ 3 / 16| := Real.sqrt_sq_eq_abs _
    _ = 1 + x / 2 - x ^ 2 / 8 + x ^ 3 / 16 := abs_of_nonneg hp




-- Sub-lemma C (Sub-task C): Given the Y-replaced PMF `D'` over `Finset V`,
-- prove the Taylor bound `∫ √Vol(A') ∂D' ≤ √Vol(s) − d_min·cut/(32·Vol(s)^{3/2})`.
-- Strategy: factor √Vol(A') = √Vol(s)·√(1+Δ'/Vol(s)), apply sqrt_one_add_taylor3,
-- use E[Δ']=0 (volume preservation), E[Δ'²] ≥ d_min·cut/4, E[Δ'³] ≤ 0
-- (since Y_u ∈ {0,λ_u} for u∉s and λ_u ≤ d_u by lambdaCut_le_degree).
-- Requires: constructing D' as the PMF induced by ∑_v Y_v (YPMF) shift from Vol(s).

/-- The independent sum of per-vertex YPMF variables (over `Finset.univ : Finset V`)
gives a `PMF ℤ` whose:
- mean is zero: `E[∑_v Y_v] = ∑_{v∈s}(-λ_v/2) + ∑_{v∉s}(+λ_v/2) = 0`
  (since `∑_{v∈s} λ_v = cut = ∑_{v∉s} λ_v` by edge symmetry).
- second moment satisfies `E[(∑_v Y_v)²] ≥ d_min·cut/4`:
  `E[(∑_v Y_v)²] = ∑_v E[Y_v²]` (independence) `≥ ∑_{v∈s} d_min·λ_v/2 = d_min·cut/2 ≥ d_min·cut/4`.
- third moment satisfies `E[(∑_v Y_v)³] ≤ 0` (majority Y_v ≥ 0 contributes non-negatively,
  but minority Y_v ∈ {-d_v, 0} contributes negatively; cross terms vanish by independence;
  net third moment ≤ 0 because minority cube terms dominate).

`Y_sum_pmf G.toTemporalGraph t s` is defined as the `Finset.univ.foldl`-iterated bind of `YPMF G.toTemporalGraph t s v`. -/
private noncomputable def Y_sum_pmf_list (G : TemporalGraph V) (t : ℕ) (s : Finset V) :
    List V → PMF ℤ
  | [] => PMF.pure 0
  | v :: vs => (Y_sum_pmf_list G t s vs).bind (fun z => (YPMF G t s v).map (· + z))

private noncomputable def Y_sum_pmf (G : TemporalGraph V) (t : ℕ) (s : Finset V) : PMF ℤ :=
  Y_sum_pmf_list G t s (Finset.univ : Finset V).toList

/-- The mean of `Y_sum_pmf` is zero:
`∫ z ∂Y_sum_pmf = ∑_v E[Y_v] = ∑_{v∈s}(-λ_v/2) + ∑_{v∉s}(+λ_v/2) = 0`
using `lambdaCut` edge symmetry (`∑_{v∈s} λ_v = edgesBetween = ∑_{v∉s} λ_v`). -/
-- Helper: integral of `Y_sum_pmf_list` over a list equals the list sum of per-vertex YPMF means.
-- Proof: induction on the list; for cons, the bind integral satisfies
-- E[∑_{v::vs} Y_v] = E[Y_v] + E[∑_{vs} Y_v] by linearity of expectation.
-- We use that (p.bind (fun x => q.map (·+x))) has mean = E[q] + E[p] when both are integrable,
-- proved via PMF.integral_eq_tsum and the absolute convergence of the double tsum.
-- Helper: integrability of the identity for YPMF.
-- YPMF G t s v is either `PMF.pure 0` or a 2-point PMF (atoms at 0 and one integer value).
-- In both cases `fun z => (z : ℝ)` is bounded μ-a.e. by max(degree G t v, 1), hence integrable.
-- Strategy: use `Integrable.of_bound` with `C = degree G t v + 1` (all atoms ≤ degree).
private lemma YPMF_int_integrable
    (G : TemporalGraph V) (t : ℕ) (s : Finset V) (v : V) :
    Integrable (fun z : ℤ => (z : ℝ)) (YPMF G t s v).toMeasure := by
  simp only [YPMF]
  split_ifs with hd hv
  · simp only [PMF.toMeasure_pure]
    exact integrable_dirac (by simp)
  · -- twoPointPMF _ _ val = (PMF.ofFintype _ _).map (fun b => cond b val 0)
    -- Its toMeasure = (PMF.ofFintype _ _).toMeasure.map (fun b => cond b val 0)
    -- Integrability follows from Bool being Finite (Integrable.of_finite)
    simp only [twoPointPMF, ← PMF.toMeasure_map _ _ (measurable_of_finite _)]
    rw [integrable_map_measure
        (Measurable.aestronglyMeasurable (fun s _ => MeasurableSpace.measurableSet_top))
        (measurable_of_finite _).aemeasurable]
    exact Integrable.of_finite
  · simp only [twoPointPMF, ← PMF.toMeasure_map _ _ (measurable_of_finite _)]
    rw [integrable_map_measure
        (Measurable.aestronglyMeasurable (fun s _ => MeasurableSpace.measurableSet_top))
        (measurable_of_finite _).aemeasurable]
    exact Integrable.of_finite

-- Helper: integral over bind of map-shift equals sum of integrals.
-- E[p.bind (fun x => q.map (· + x))] = E[q] + E[p]
-- This is "linearity of expectation for independent sum" for finitely-supported PMFs over ℤ.
-- Proof: use integral_eq_tsum on the bind PMF, expand bind_apply, use tsum_comm via finite support
-- of p to interchange sums, substitute u = w - x, and identify each tsum as E[q] + x.
private lemma pmf_integral_bind_add_map
    (p q : PMF ℤ) (hp_fin : p.support.Finite)
    (hq_int : Integrable (fun z : ℤ => (z : ℝ)) q.toMeasure) :
    ∫ z, (z : ℝ) ∂(p.bind (fun x => q.map (· + x))).toMeasure =
      (∫ z, (z : ℝ) ∂q.toMeasure) + (∫ z, (z : ℝ) ∂p.toMeasure) := by
  -- Elements outside hp_fin.toFinset have p x = 0 (as ENNReal, since PMF.FunLike gives ENNReal)
  have hmem : ∀ x ∉ hp_fin.toFinset, p x = 0 :=
    fun x hx => (PMF.apply_eq_zero_iff p x).mpr (fun h => hx (hp_fin.mem_toFinset.mpr h))
  -- Shifting q by x has integral E[q] + x
  have hshift : ∀ x : ℤ, ∫ z, (z : ℝ) ∂(q.map (· + x)).toMeasure =
      (∫ z, (z : ℝ) ∂q.toMeasure) + (x : ℝ) := fun x => by
    rw [← PMF.toMeasure_map (· + x) q (measurable_add_const x)]
    rw [MeasureTheory.integral_map (measurable_add_const x).aemeasurable
          (Measurable.of_discrete.aestronglyMeasurable)]
    push_cast
    rw [integral_add hq_int (integrable_const _), integral_const, probReal_univ, one_smul]
  -- Identity is integrable w.r.t. any shift of q
  have hqshift_int : ∀ x : ℤ,
      Integrable (fun z : ℤ => (z : ℝ)) (q.map (· + x)).toMeasure := fun x => by
    rw [← PMF.toMeasure_map (· + x) q (measurable_add_const x)]
    rw [integrable_map_measure Measurable.of_discrete.aestronglyMeasurable
          (measurable_add_const x).aemeasurable]
    simp only [Function.comp_def, Int.cast_add]
    exact hq_int.add (integrable_const _)
  -- Identity is integrable w.r.t. p.toMeasure (finite support)
  have hp_int : Integrable (fun z : ℤ => (z : ℝ)) p.toMeasure := by
    rw [← PMF.restrict_toMeasure_support p]; exact IntegrableOn.of_finite hp_fin
  -- The bind measure equals a finite weighted sum of shifted measures
  have hbind_meas : (p.bind (fun x => q.map (· + x))).toMeasure =
      ∑ x ∈ hp_fin.toFinset, p x • (q.map (· + x)).toMeasure := by
    ext s hs
    rw [PMF.toMeasure_bind_apply p (fun x => q.map (· + x)) s hs]
    simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
    exact tsum_eq_sum (s := hp_fin.toFinset) (fun x hx => by simp [hmem x hx])
  -- p x < ∞ for all x (PMF values are finite)
  have hlt : ∀ x : ℤ, p x ≠ ⊤ := PMF.apply_ne_top p
  -- The integral over shifted-smul-measure uses integral_smul_measure
  have hshift_smul : ∀ x : ℤ,
      ∫ z, (z : ℝ) ∂p x • (q.map (· + x)).toMeasure =
        (p x).toReal • (∫ z, (z : ℝ) ∂(q.map (· + x)).toMeasure) :=
    fun x => integral_smul_measure _ (p x)
  -- Sum of PMF probabilities equals 1
  have hone : ∑ x ∈ hp_fin.toFinset, (p x).toReal = 1 := by
    have : ∑' a, p a = 1 := PMF.tsum_coe p
    rw [tsum_eq_sum (s := hp_fin.toFinset) hmem] at this
    calc ∑ x ∈ hp_fin.toFinset, (p x).toReal
        = (∑ x ∈ hp_fin.toFinset, p x).toReal := by
            rw [ENNReal.toReal_sum (fun x _ => hlt x)]
      _ = (1 : ENNReal).toReal := by rw [this]
      _ = 1 := ENNReal.toReal_one
  -- The finite sum of (p x).toReal * x equals the integral of p
  have hint_p : ∑ x ∈ hp_fin.toFinset, (p x).toReal * (x : ℝ) =
      ∫ z, (z : ℝ) ∂p.toMeasure := by
    rw [PMF.integral_eq_tsum _ _ hp_int]
    conv_rhs => rw [tsum_eq_sum (s := hp_fin.toFinset) (fun x hx => by
        simp [smul_eq_mul, show (p x).toReal = 0 from by simp [hmem x hx]])]
    apply Finset.sum_congr rfl
    intro x _; simp [smul_eq_mul]
  rw [hbind_meas,
      integral_finsetSum_measure (f := fun z : ℤ => (z : ℝ))
        (μ := fun x => p x • (q.map (· + x)).toMeasure)
        (fun x _ => (hqshift_int x).smul_measure (hlt x))]
  simp_rw [hshift_smul, hshift]
  -- goal should now be ∑ x, (p x).toReal • (∫q + ↑x) = ∫q + ∫p
  simp_rw [smul_add, smul_eq_mul, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, hone, one_mul, hint_p]

-- Helper: for `y` in the support of `YPMF G t s v`, we have `y ≥ -(d_v)`.
private lemma YPMF_support_lb (G : TemporalGraph V) (t : ℕ) (s : Finset V) (v : V) :
    ∀ y ∈ (YPMF G t s v).support, -(G.degree t v : ℤ) ≤ y := by
  simp only [YPMF]
  split_ifs with hd hv
  · -- degree = 0: support = {0}, and -(0 : ℤ) ≤ 0
    intro y hy
    simp only [PMF.support_pure, Set.mem_singleton_iff] at hy
    subst hy; simp [hd]
  · -- v ∈ s: support ⊆ {0, -(d_v)}
    simp only [twoPointPMF, PMF.support_map, Set.mem_image]
    intro y ⟨b, _, hby⟩
    cases b
    · -- b = false: y = 0, need -(d_v) ≤ 0
      simp only [cond_false] at hby; subst hby
      exact neg_nonpos.mpr (Int.natCast_nonneg _)
    · -- b = true: y = -(d_v), trivial
      simp only [cond_true] at hby; subst hby; exact le_refl _
  · -- v ∉ s: support ⊆ {0, +λ_v}, both ≥ 0 ≥ -(d_v)
    simp only [twoPointPMF, PMF.support_map, Set.mem_image]
    intro y ⟨b, _, hby⟩
    cases b
    · -- b = false: y = 0, need -(d_v) ≤ 0
      simp only [cond_false] at hby; subst hby
      exact neg_nonpos.mpr (Int.natCast_nonneg _)
    · -- b = true: y = λ_v ≥ 0 ≥ -(d_v)
      simp only [cond_true] at hby; subst hby
      exact le_trans (neg_nonpos.mpr (Int.natCast_nonneg _)) (Int.natCast_nonneg _)

-- Helper: elements in the support of `Y_sum_pmf_list G t s l` are `≥ -(sum of d_v for v∈s∩l)`.
-- The conclusion is stated as: `≥ -(∑ v ∈ s.filter (· ∈ l), d_v)`.
-- Requires l to have no duplicates (Nodup) so each vertex is counted at most once.
private lemma Y_sum_pmf_list_support_lb (G : TemporalGraph V) (t : ℕ) (s : Finset V)
    (l : List V) (hnodup : l.Nodup) :
    ∀ z ∈ (Y_sum_pmf_list G t s l).support,
      -(∑ v ∈ s.filter (· ∈ l), (G.degree t v : ℤ)) ≤ z := by
  induction l with
  | nil =>
    intro z hz
    simp [Y_sum_pmf_list, PMF.support_pure] at hz
    subst hz; simp
  | cons v vs ih =>
    rw [List.nodup_cons] at hnodup
    obtain ⟨hv_notin, hnodup_vs⟩ := hnodup
    intro z hz
    simp only [Y_sum_pmf_list, PMF.support_bind, PMF.support_map, Set.mem_iUnion,
      Set.mem_image] at hz
    obtain ⟨w, hw, y, hy, hyz⟩ := hz
    rw [← hyz]
    have ihw := ih hnodup_vs w hw
    have hYPMF_lb : -(G.degree t v : ℤ) ≤ y := YPMF_support_lb G t s v y hy
    -- Bound: -(∑ u ∈ s.filter(·∈v::vs), d_u) ≤ w + y
    -- Case analysis on v ∈ s:
    -- v ∈ s, v ∉ vs: filter(v::vs) = insert v (filter vs) disjoint,
    --   so ∑_{·∈v::vs} = d_v + ∑_{·∈vs}, giving -(∑_{·∈v::vs}) = -d_v + (-∑_{·∈vs}) ≤ y + w
    -- v ∉ s: filter(v::vs) = filter(vs), and y ≥ 0 (YPMF outside s outputs ≥ 0)
    --   so -(∑_{·∈v::vs}) = -∑_{·∈vs} ≤ w ≤ w + y
    by_cases hv : v ∈ s
    · -- v ∈ s, v ∉ vs (by Nodup)
      -- filter(v::vs) = insert v (filter(vs)) since v ∉ vs means v ∉ s.filter(·∈vs)
      have hv_notin_filt : v ∉ s.filter (· ∈ vs) := by
        simp [Finset.mem_filter, hv_notin]
      have hfilt_eq : s.filter (· ∈ v :: vs) = insert v (s.filter (· ∈ vs)) := by
        ext u
        simp only [Finset.mem_filter, List.mem_cons, Finset.mem_insert]
        constructor
        · rintro ⟨hus, rfl | huvs⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨hus, huvs⟩
        · rintro (rfl | ⟨hus, huvs⟩)
          · exact ⟨hv, Or.inl rfl⟩
          · exact ⟨hus, Or.inr huvs⟩
      rw [hfilt_eq, Finset.sum_insert hv_notin_filt]
      linarith
    · -- v ∉ s: filter(v::vs) = filter(vs), y ≥ 0
      have hfilt_eq : s.filter (· ∈ v :: vs) = s.filter (· ∈ vs) := by
        ext u
        simp only [Finset.mem_filter, List.mem_cons]
        constructor
        · rintro ⟨hus, rfl | huvs⟩
          · exact absurd hus hv
          · exact ⟨hus, huvs⟩
        · rintro ⟨hus, huvs⟩
          exact ⟨hus, Or.inr huvs⟩
      rw [hfilt_eq]
      -- y ≥ 0 since v ∉ s means YPMF outputs 0 or +λ_v
      have hy_nn : (0 : ℤ) ≤ y := by
        have : y ∈ (YPMF G t s v).support := hy
        unfold YPMF at this
        by_cases hd : G.degree t v = 0
        · simp only [dif_pos hd, PMF.support_pure, Set.mem_singleton_iff] at this
          subst this; exact le_refl _
        · rw [dif_neg hd] at this
          by_cases hvs : v ∈ s
          · exact absurd hvs hv
          · rw [if_neg hvs] at this
            simp only [twoPointPMF, PMF.support_map, Set.mem_image] at this
            obtain ⟨b, _, hby⟩ := this; cases b
            · simp only [cond_false] at hby; subst hby; exact le_refl _
            · simp only [cond_true] at hby; subst hby; exact Int.natCast_nonneg _
      linarith

-- Helper: `Y_sum_pmf_list G t s l` has finite support (by induction on l).
-- Base: PMF.pure 0 has support {0} (finite).
-- Step: bind of finite-support PMF with (YPMF's finite support shifted) is finite.
private lemma Y_sum_pmf_list_support_finite (G : TemporalGraph V) (t : ℕ) (s : Finset V)
    (l : List V) : (Y_sum_pmf_list G t s l).support.Finite := by
  induction l with
  | nil => simp [Y_sum_pmf_list, PMF.support_pure]
  | cons v vs ih =>
    simp only [Y_sum_pmf_list, PMF.support_bind]
    apply Set.Finite.biUnion ih
    intro z _
    simp only [PMF.support_map]
    -- Support of q.map (· + z) is a shift of the support of q.
    -- Since YPMF has support ⊆ {val, 0} (finite), so does the map.
    apply Set.Finite.image
    -- YPMF G t s v has finite support (it's a 2-point PMF)
    simp only [YPMF]
    split_ifs with hd hv
    · simp [PMF.support_pure]
    · -- twoPointPMF = (PMF.ofFintype …).map f for f : Bool → ℤ, and Bool is finite
      simp only [twoPointPMF, PMF.support_map]
      exact Set.Finite.image _ (Set.toFinite _)
    · simp only [twoPointPMF, PMF.support_map]
      exact Set.Finite.image _ (Set.toFinite _)

private lemma Y_sum_pmf_list_integral (G : TemporalGraph V) (t : ℕ) (s : Finset V)
    (l : List V) :
    ∫ z, (z : ℝ) ∂(Y_sum_pmf_list G t s l).toMeasure =
      (l.map (fun v => if v ∈ s then -(lambdaCut G t s v : ℝ) / 2
                                 else (lambdaCut G t s v : ℝ) / 2)).sum := by
  induction l with
  | nil => simp [Y_sum_pmf_list, PMF.toMeasure_pure]
  | cons v vs ih =>
    simp only [Y_sum_pmf_list, List.map_cons, List.sum_cons]
    -- E[Y_{v::vs}] = E[YPMF v] + E[Y_vs]  by linearity (pmf_integral_bind_add_map)
    rw [pmf_integral_bind_add_map (Y_sum_pmf_list G t s vs) (YPMF G t s v)
      (Y_sum_pmf_list_support_finite G t s vs)
      (YPMF_int_integrable G t s v)]
    rw [ih, integral_YPMF_id]

private lemma Y_sum_pmf_mean_zero
    (G : TemporalGraph V)
    (t : ℕ) (s : Finset V) :
    ∫ z, (z : ℝ) ∂(Y_sum_pmf G t s).toMeasure = 0 := by
  unfold Y_sum_pmf
  rw [Y_sum_pmf_list_integral]
  -- Rewrite list.sum to Finset.sum using Finset.sum_map_toList
  rw [Finset.sum_map_toList]
  -- Show ∑ v : V, (if v∈s then -λ/2 else λ/2) = 0
  -- Split into v∈s and v∉s parts and use cut symmetry
  rw [show (Finset.univ : Finset V) = s ∪ (Finset.univ \ s) from
      (Finset.union_sdiff_of_subset (Finset.subset_univ s)).symm,
    Finset.sum_union disjoint_sdiff_self_right]
  rw [Finset.sum_congr rfl (fun v hv => show (if v ∈ s then -(lambdaCut G t s v : ℝ) / 2
      else (lambdaCut G t s v : ℝ) / 2) = -(lambdaCut G t s v : ℝ) / 2 from by simp [hv]),
    Finset.sum_congr rfl (fun v hv => show (if v ∈ s then -(lambdaCut G t s v : ℝ) / 2
      else (lambdaCut G t s v : ℝ) / 2) = (lambdaCut G t s v : ℝ) / 2 from
      by simp [(Finset.mem_sdiff.mp hv).2])]
  -- Each sum equals ±edgesBetween/2 by the degreeIn = edgesBetween identity
  have hsum_cut : ∀ (A B : Finset V),
      (∑ v ∈ A, (G.degreeIn t v B : ℝ)) =
      (G.edgesBetween t A B : ℝ) := by
    intro A B
    have : ∑ v ∈ A, G.degreeIn t v B = G.edgesBetween t A B := by
      simp only [TemporalGraph.degreeIn, SimpleGraph.degreeIn, TemporalGraph.edgesBetween,
        SimpleGraph.edgesBetween, Finset.card_filter]
      exact (Finset.sum_product' A B
        (fun v w => if (G.snapshot t).Adj v w then (1 : ℕ) else 0)).symm
    exact_mod_cast this
  rw [Finset.sum_congr rfl (fun v hv => show -(lambdaCut G t s v : ℝ) / 2 =
      -(G.degreeIn t v (Finset.univ \ s) : ℝ) / 2 from by
      simp [lambdaCut, hv]),
    Finset.sum_congr rfl (fun v hv => show (lambdaCut G t s v : ℝ) / 2 =
      (G.degreeIn t v s : ℝ) / 2 from by
      simp [lambdaCut, (Finset.mem_sdiff.mp hv).2])]
  have hs1 : ∑ v ∈ s, -(G.degreeIn t v (Finset.univ \ s) : ℝ) / 2 =
      -(G.edgesBetween t s (Finset.univ \ s) : ℝ) / 2 := by
    have : ∑ v ∈ s, -(G.degreeIn t v (Finset.univ \ s) : ℝ) / 2 =
        -(∑ v ∈ s, (G.degreeIn t v (Finset.univ \ s) : ℝ)) / 2 := by
      simp_rw [neg_div]
      rw [Finset.sum_neg_distrib, Finset.sum_div]
    rw [this, hsum_cut]
  have hs2 : ∑ v ∈ Finset.univ \ s, (G.degreeIn t v s : ℝ) / 2 =
      (G.edgesBetween t (Finset.univ \ s) s : ℝ) / 2 := by
    rw [← hsum_cut _ s, Finset.sum_div]
  rw [hs1, hs2, G.edgesBetween_comm' t (Finset.univ \ s) s]
  ring

-- Helper: bind-map expansion for second moment:
-- ∫z²∂(p.bind(fun x => q.map(·+x))) = ∫z²∂q + 2·(∫z∂q)·(∫z∂p) + ∫z²∂p
private lemma pmf_integral_bind_sq
    (p q : PMF ℤ) (hp_fin : p.support.Finite)
    (hq_int : Integrable (fun z : ℤ => (z : ℝ)) q.toMeasure)
    (hq_sq : Integrable (fun z : ℤ => (z : ℝ) ^ 2) q.toMeasure) :
    ∫ z, (z : ℝ) ^ 2 ∂(p.bind (fun x => q.map (· + x))).toMeasure =
      (∫ z, (z : ℝ) ^ 2 ∂q.toMeasure) + 2 * (∫ z, (z : ℝ) ∂q.toMeasure) *
        (∫ z, (z : ℝ) ∂p.toMeasure) + (∫ z, (z : ℝ) ^ 2 ∂p.toMeasure) := by
  have hmem : ∀ x ∉ hp_fin.toFinset, p x = 0 :=
    fun x hx => (PMF.apply_eq_zero_iff p x).mpr (fun h => hx (hp_fin.mem_toFinset.mpr h))
  have hlt : ∀ x : ℤ, p x ≠ ⊤ := PMF.apply_ne_top p
  have hp_int : Integrable (fun z : ℤ => (z : ℝ)) p.toMeasure := by
    rw [← PMF.restrict_toMeasure_support p]; exact IntegrableOn.of_finite hp_fin
  have hp_sq : Integrable (fun z : ℤ => (z : ℝ) ^ 2) p.toMeasure := by
    rw [← PMF.restrict_toMeasure_support p]; exact IntegrableOn.of_finite hp_fin
  -- Shifting q by x: ∫z²∂q.map(·+x) = ∫z²∂q + 2x·∫z∂q + x²
  have hshift_sq : ∀ x : ℤ, ∫ z, (z : ℝ) ^ 2 ∂(q.map (· + x)).toMeasure =
      (∫ z, (z : ℝ) ^ 2 ∂q.toMeasure) + 2 * (x : ℝ) * (∫ z, (z : ℝ) ∂q.toMeasure) +
        (x : ℝ) ^ 2 := fun x => by
    rw [← PMF.toMeasure_map (· + x) q (measurable_add_const x),
        MeasureTheory.integral_map (measurable_add_const x).aemeasurable
          (Measurable.of_discrete.aestronglyMeasurable)]
    push_cast
    -- goal: ∫y, (y+x)² ∂q = ∫z²∂q + 2x·∫z∂q + x²
    -- Compute step by step to avoid simp-normalizer form mismatches
    have h_mul : ∫ y : ℤ, 2 * (x : ℝ) * (y : ℝ) ∂q.toMeasure =
        2 * (x : ℝ) * ∫ y : ℤ, (y : ℝ) ∂q.toMeasure :=
      integral_const_mul (2 * (x : ℝ)) (fun y : ℤ => (y : ℝ))
    have h1 : ∫ y : ℤ, ((y : ℝ) ^ 2 + 2 * (x : ℝ) * (y : ℝ)) ∂q.toMeasure =
        ∫ y : ℤ, (y : ℝ) ^ 2 ∂q.toMeasure + 2 * (x : ℝ) * ∫ y : ℤ, (y : ℝ) ∂q.toMeasure :=
      (integral_add hq_sq (hq_int.const_mul _)).trans (by linarith [h_mul])
    have h2 : ∫ y : ℤ, ((y : ℝ) ^ 2 + 2 * (x : ℝ) * (y : ℝ) + (x : ℝ) ^ 2) ∂q.toMeasure =
        ∫ y : ℤ, (y : ℝ) ^ 2 ∂q.toMeasure + 2 * (x : ℝ) * ∫ y : ℤ, (y : ℝ) ∂q.toMeasure +
          (x : ℝ) ^ 2 := by
      haveI : IsProbabilityMeasure q.toMeasure := PMF.toMeasure.isProbabilityMeasure q
      have h3 := integral_add (hq_sq.add (hq_int.const_mul (2 * (x : ℝ))))
        (integrable_const ((x : ℝ)^2))
      simp only [integral_const, probReal_univ, one_smul] at h3
      have h4 : ∫ y : ℤ, ((y : ℝ) ^ 2 + 2 * (x : ℝ) * (y : ℝ) + (x : ℝ) ^ 2) ∂q.toMeasure =
          ∫ y : ℤ, ((y : ℝ) ^ 2 + 2 * (x : ℝ) * (y : ℝ)) ∂q.toMeasure + (x : ℝ) ^ 2 := by
        have := integral_add (hq_sq.add (hq_int.const_mul (2 * (x : ℝ))))
          (integrable_const ((x : ℝ)^2))
        simp only [integral_const, probReal_univ, one_smul] at this
        exact h3
      linarith [h1]
    calc ∫ y : ℤ, ((y : ℝ) + ↑x) ^ 2 ∂q.toMeasure
        = ∫ y : ℤ, ((y : ℝ) ^ 2 + 2 * (x : ℝ) * (y : ℝ) + (x : ℝ) ^ 2) ∂q.toMeasure := by
            congr 1; ext y; ring
      _ = ∫ y : ℤ, (y : ℝ) ^ 2 ∂q.toMeasure + 2 * (x : ℝ) * ∫ y : ℤ, (y : ℝ) ∂q.toMeasure +
            (x : ℝ) ^ 2 := h2
  -- Integrability of z² under shifted q
  have hqshift_sq : ∀ x : ℤ,
      Integrable (fun z : ℤ => (z : ℝ) ^ 2) (q.map (· + x)).toMeasure := fun x => by
    rw [← PMF.toMeasure_map (· + x) q (measurable_add_const x),
        integrable_map_measure Measurable.of_discrete.aestronglyMeasurable
          (measurable_add_const x).aemeasurable]
    simp only [Function.comp_def]
    have heq : (fun y : ℤ => ((y + x : ℤ) : ℝ) ^ 2) =
        fun y : ℤ => (y : ℝ) ^ 2 + 2 * (x : ℝ) * (y : ℝ) + (x : ℝ) ^ 2 := by
      ext y; push_cast; ring
    rw [heq]; exact (hq_sq.add (hq_int.const_mul _)).add (integrable_const _)
  -- The bind measure as a finite weighted sum
  have hbind_meas : (p.bind (fun x => q.map (· + x))).toMeasure =
      ∑ x ∈ hp_fin.toFinset, p x • (q.map (· + x)).toMeasure := by
    ext s hs
    rw [PMF.toMeasure_bind_apply p (fun x => q.map (· + x)) s hs]
    simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
    exact tsum_eq_sum (s := hp_fin.toFinset) (fun x hx => by simp [hmem x hx])
  have hone : ∑ x ∈ hp_fin.toFinset, (p x).toReal = 1 := by
    have : ∑' a, p a = 1 := PMF.tsum_coe p
    rw [tsum_eq_sum (s := hp_fin.toFinset) hmem] at this
    calc ∑ x ∈ hp_fin.toFinset, (p x).toReal
        = (∑ x ∈ hp_fin.toFinset, p x).toReal := by rw [ENNReal.toReal_sum (fun x _ => hlt x)]
      _ = (1 : ENNReal).toReal := by rw [this]
      _ = 1 := ENNReal.toReal_one
  have hint_p : ∑ x ∈ hp_fin.toFinset, (p x).toReal * (x : ℝ) =
      ∫ z, (z : ℝ) ∂p.toMeasure := by
    rw [PMF.integral_eq_tsum _ _ hp_int]
    conv_rhs => rw [tsum_eq_sum (s := hp_fin.toFinset) (fun x hx => by
        simp [smul_eq_mul, show (p x).toReal = 0 from by simp [hmem x hx]])]
    apply Finset.sum_congr rfl; intro x _; simp [smul_eq_mul]
  have hint_p_sq : ∑ x ∈ hp_fin.toFinset, (p x).toReal * (x : ℝ) ^ 2 =
      ∫ z, (z : ℝ) ^ 2 ∂p.toMeasure := by
    rw [PMF.integral_eq_tsum _ _ hp_sq]
    conv_rhs => rw [tsum_eq_sum (s := hp_fin.toFinset) (fun x hx => by
        simp [smul_eq_mul, show (p x).toReal = 0 from by simp [hmem x hx]])]
    apply Finset.sum_congr rfl; intro x _; simp [smul_eq_mul]
  rw [hbind_meas, integral_finsetSum_measure (f := fun z : ℤ => (z : ℝ) ^ 2)
        (μ := fun x => p x • (q.map (· + x)).toMeasure)
        (fun x _ => (hqshift_sq x).smul_measure (hlt x))]
  simp_rw [integral_smul_measure _ (p _), hshift_sq]
  -- goal: ∑ x, (p x).toReal • (∫z²∂q + 2x·∫z∂q + x²) = ∫z²∂q + 2·∫z∂q·∫z∂p + ∫z²∂p
  simp_rw [smul_add, smul_eq_mul, Finset.sum_add_distrib]
  -- Simplify each of the three sums
  set Eq2 := ∫ z, (z : ℝ) ^ 2 ∂q.toMeasure
  set Eq := ∫ z, (z : ℝ) ∂q.toMeasure
  have hfst : ∑ x ∈ hp_fin.toFinset, (p x).toReal * Eq2 = Eq2 := by
    rw [← Finset.sum_mul, hone, one_mul]
  have hmid : ∑ x ∈ hp_fin.toFinset, (p x).toReal * (2 * ↑x * Eq) =
      2 * Eq * ∫ z, (z : ℝ) ∂p.toMeasure := by
    rw [show (fun x : ℤ => (p x).toReal * (2 * ↑x * Eq)) =
        (fun x : ℤ => 2 * Eq * ((p x).toReal * ↑x)) from by ext x; ring]
    rw [← Finset.mul_sum, hint_p]
  rw [hfst, hint_p_sq, hmid]

-- Helper: variance decomposition for Y_sum_pmf_list:
-- ∫z²∂(Y_sum_list l) - (∫z∂(Y_sum_list l))² = ∑_{v∈l} (∫z²∂YPMF_v - (∫z∂YPMF_v)²)
private lemma Y_sum_pmf_list_variance_eq (G : TemporalGraph V) (t : ℕ) (s : Finset V)
    (l : List V) :
    ∫ z, (z : ℝ) ^ 2 ∂(Y_sum_pmf_list G t s l).toMeasure -
      (∫ z, (z : ℝ) ∂(Y_sum_pmf_list G t s l).toMeasure) ^ 2 =
    (l.map (fun v => ∫ z, (z : ℝ) ^ 2 ∂(YPMF G t s v).toMeasure -
      (∫ z, (z : ℝ) ∂(YPMF G t s v).toMeasure) ^ 2)).sum := by
  induction l with
  | nil =>
    simp [Y_sum_pmf_list, PMF.toMeasure_pure]
  | cons v vs ih =>
    simp only [Y_sum_pmf_list, List.map_cons, List.sum_cons]
    -- Let p = Y_sum_pmf_list vs, q = YPMF v
    set p := Y_sum_pmf_list G t s vs with hp_def
    set q := YPMF G t s v with hq_def
    have hp_fin : p.support.Finite := Y_sum_pmf_list_support_finite G t s vs
    have hq_int : Integrable (fun z : ℤ => (z : ℝ)) q.toMeasure := YPMF_int_integrable G t s v
    have hq_sq : Integrable (fun z : ℤ => (z : ℝ) ^ 2) q.toMeasure := by
      rw [← PMF.restrict_toMeasure_support q]
      apply IntegrableOn.of_finite
      simp only [hq_def, YPMF]
      split_ifs with hd hv
      · simp [PMF.support_pure]
      · simp only [twoPointPMF, PMF.support_map]; exact Set.Finite.image _ (Set.toFinite _)
      · simp only [twoPointPMF, PMF.support_map]; exact Set.Finite.image _ (Set.toFinite _)
    -- Apply bind-sq expansion
    rw [pmf_integral_bind_sq p q hp_fin hq_int hq_sq,
        pmf_integral_bind_add_map p q hp_fin hq_int]
    -- Expand and simplify using ih (variance of list = sum of individual variances)
    -- Goal: A + 2BC + D - (B+C)² = (A - B²) + E, given ih: D - C² = E
    -- Reduces to: A + 2BC + D - B² - 2BC - C² = A - B² + E, i.e., D - C² = E
    set A := ∫ z, (z : ℝ) ^ 2 ∂q.toMeasure
    set B := ∫ z, (z : ℝ) ∂q.toMeasure
    set C := ∫ z, (z : ℝ) ∂p.toMeasure
    set D := ∫ z, (z : ℝ) ^ 2 ∂p.toMeasure
    set E := (List.map (fun v => ∫ z, (z : ℝ) ^ 2 ∂(YPMF G t s v).toMeasure -
      (∫ z, (z : ℝ) ∂(YPMF G t s v).toMeasure) ^ 2) vs).sum
    linear_combination ih

/-- Second moment lower bound for `Y_sum_pmf`:
`E[(∑_v Y_v)²] ≥ d_min · edgesBetween(s, V\s) / 4`.

Proof: By independence `E[(∑_v Y_v)²] = ∑_v E[Y_v²]`.
For `v ∈ s`: `E[Y_v²] = d_v · λ_v / 2 ≥ d_min · λ_v / 2`.
Summing over `v ∈ s`: `∑_{v∈s} E[Y_v²] ≥ d_min/2 · ∑_{v∈s} λ_v = d_min · cut / 2 ≥ d_min · cut / 4`. -/
private lemma Y_sum_pmf_second_moment_lb
    (G : TemporalGraphFixedDegree V)
    (t : ℕ) (s : Finset V) :
    (G.minDegreeAt 0 : ℝ) * (G.edgesBetween t s (univ \ s) : ℝ) / 4
      ≤ ∫ z, (z : ℝ) ^ 2 ∂(Y_sum_pmf G.toTemporalGraph t s).toMeasure := by
  -- Step 1: ∫z²∂Y_sum = ∑_v Var(Y_v) (since mean = 0)
  have hmean : ∫ z, (z : ℝ) ∂(Y_sum_pmf G.toTemporalGraph t s).toMeasure = 0 :=
    Y_sum_pmf_mean_zero G.toTemporalGraph t s
  have hvar_eq : ∫ z, (z : ℝ) ^ 2 ∂(Y_sum_pmf G.toTemporalGraph t s).toMeasure =
      (Finset.univ.toList.map (fun v => ∫ z, (z : ℝ) ^ 2 ∂(YPMF G.toTemporalGraph t s v).toMeasure -
        (∫ z, (z : ℝ) ∂(YPMF G.toTemporalGraph t s v).toMeasure) ^ 2)).sum := by
    have hv := Y_sum_pmf_list_variance_eq G.toTemporalGraph t s Finset.univ.toList
    -- Y_sum_pmf = Y_sum_pmf_list ... Finset.univ.toList
    unfold Y_sum_pmf at hmean
    have hmean0 : (∫ z, (z : ℝ) ∂(Y_sum_pmf_list G.toTemporalGraph t s Finset.univ.toList).toMeasure) ^ 2 = 0 :=
      by rw [hmean]; ring
    unfold Y_sum_pmf
    linarith [hv, hmean0]
  rw [hvar_eq]
  -- Step 2: sum over list = sum over Finset.univ
  rw [Finset.sum_map_toList]
  -- Step 3: lower bound by minority contributions only
  -- Var(Y_v) ≥ 0 for majority; Var(Y_v) ≥ d_min·λ_v/4 for minority
  -- ∑_{v∈s} λ_v = edgesBetween(s, V\s)
  have hcut : ∑ v ∈ s, lambdaCut G.toTemporalGraph t s v = G.edgesBetween t s (univ \ s) := by
    rw [Finset.sum_congr rfl (fun v hv => show lambdaCut G.toTemporalGraph t s v =
        G.degreeIn t v (univ \ s) from by simp [lambdaCut, hv])]
    simp only [SimpleGraph.degreeIn, SimpleGraph.edgesBetween, Finset.card_filter]
    exact (Finset.sum_product' s (univ \ s)
      (fun v w => if (G.snapshot t).Adj v w then (1 : ℕ) else 0)).symm
  -- Shorthand: Var(Y_v)
  set Varv : V → ℝ := fun v => ∫ z, (z : ℝ) ^ 2 ∂(YPMF G.toTemporalGraph t s v).toMeasure -
      (∫ z, (z : ℝ) ∂(YPMF G.toTemporalGraph t s v).toMeasure) ^ 2
  -- Step 3a: d_min·λ_v/4 ≤ Varv(v) for minority v∈s
  have h_min_lb : ∀ v ∈ s, (G.minDegreeAt 0 : ℝ) * (lambdaCut G.toTemporalGraph t s v : ℝ) / 4 ≤ Varv v := by
    intro v hv
    simp only [Varv, integral_YPMF_sq, integral_YPMF_id, if_pos hv]
    have hd_le : (G.minDegreeAt 0 : ℝ) ≤ (G.degree t v : ℝ) := by
      have := G.minDegreeAt_le_degree t v
      rw [← G.minDegreeAt_eq 0 t] at this; exact_mod_cast this
    have hlam : (lambdaCut G.toTemporalGraph t s v : ℝ) ≤ (G.degree t v : ℝ) :=
      by exact_mod_cast lambdaCut_le_degree G.toTemporalGraph t s v
    have hlam_nn : (0 : ℝ) ≤ lambdaCut G.toTemporalGraph t s v := by positivity
    nlinarith
  -- Step 3b: Varv(v) ≥ 0 for all v
  have h_var_nn : ∀ v : V, 0 ≤ Varv v := by
    intro v
    simp only [Varv, integral_YPMF_sq, integral_YPMF_id]
    split_ifs with hv
    · have hlam : (lambdaCut G.toTemporalGraph t s v : ℝ) ≤ (G.degree t v : ℝ) :=
        by exact_mod_cast lambdaCut_le_degree G.toTemporalGraph t s v
      have hlam_nn : (0 : ℝ) ≤ lambdaCut G.toTemporalGraph t s v := by positivity
      have hd_nn : (0 : ℝ) ≤ G.degree t v := by positivity
      nlinarith
    · have hlam_nn : (0 : ℝ) ≤ lambdaCut G.toTemporalGraph t s v := by positivity
      nlinarith [sq_nonneg ((lambdaCut G.toTemporalGraph t s v : ℝ))]
  calc (G.minDegreeAt 0 : ℝ) * (G.edgesBetween t s (univ \ s) : ℝ) / 4
      = ∑ v ∈ s, (G.minDegreeAt 0 : ℝ) * (lambdaCut G.toTemporalGraph t s v : ℝ) / 4 := by
          have : (G.edgesBetween t s (univ \ s) : ℝ) =
              ∑ v ∈ s, (lambdaCut G.toTemporalGraph t s v : ℝ) := by
            exact_mod_cast hcut.symm
          rw [this, Finset.mul_sum, Finset.sum_div]
      _ ≤ ∑ v ∈ s, Varv v :=
          Finset.sum_le_sum h_min_lb
      _ ≤ ∑ v : V, Varv v :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
            (fun v _ _ => h_var_nn v)

-- Helper: bind-map expansion for third moment:
-- ∫z³∂(p.bind(fun x => q.map(·+x))) = ∫z³∂q + 3·∫z²∂q·∫z∂p + 3·∫z∂q·∫z²∂p + ∫z³∂p
private lemma pmf_integral_bind_cube
    (p q : PMF ℤ) (hp_fin : p.support.Finite)
    (hq_int : Integrable (fun z : ℤ => (z : ℝ)) q.toMeasure)
    (hq_sq : Integrable (fun z : ℤ => (z : ℝ) ^ 2) q.toMeasure)
    (hq_cube : Integrable (fun z : ℤ => (z : ℝ) ^ 3) q.toMeasure) :
    ∫ z, (z : ℝ) ^ 3 ∂(p.bind (fun x => q.map (· + x))).toMeasure =
      (∫ z, (z : ℝ) ^ 3 ∂q.toMeasure) +
      3 * (∫ z, (z : ℝ) ^ 2 ∂q.toMeasure) * (∫ z, (z : ℝ) ∂p.toMeasure) +
      3 * (∫ z, (z : ℝ) ∂q.toMeasure) * (∫ z, (z : ℝ) ^ 2 ∂p.toMeasure) +
      (∫ z, (z : ℝ) ^ 3 ∂p.toMeasure) := by
  have hmem : ∀ x ∉ hp_fin.toFinset, p x = 0 :=
    fun x hx => (PMF.apply_eq_zero_iff p x).mpr (fun h => hx (hp_fin.mem_toFinset.mpr h))
  have hlt : ∀ x : ℤ, p x ≠ ⊤ := PMF.apply_ne_top p
  have hp_int : Integrable (fun z : ℤ => (z : ℝ)) p.toMeasure := by
    rw [← PMF.restrict_toMeasure_support p]; exact IntegrableOn.of_finite hp_fin
  have hp_sq : Integrable (fun z : ℤ => (z : ℝ) ^ 2) p.toMeasure := by
    rw [← PMF.restrict_toMeasure_support p]; exact IntegrableOn.of_finite hp_fin
  have hp_cube : Integrable (fun z : ℤ => (z : ℝ) ^ 3) p.toMeasure := by
    rw [← PMF.restrict_toMeasure_support p]; exact IntegrableOn.of_finite hp_fin
  -- Shifting q by x: ∫z³∂q.map(·+x) = ∫z³∂q + 3x·∫z²∂q + 3x²·∫z∂q + x³
  have hshift_cube : ∀ x : ℤ, ∫ z, (z : ℝ) ^ 3 ∂(q.map (· + x)).toMeasure =
      (∫ z, (z : ℝ) ^ 3 ∂q.toMeasure) + 3 * (x : ℝ) * (∫ z, (z : ℝ) ^ 2 ∂q.toMeasure) +
      3 * (x : ℝ) ^ 2 * (∫ z, (z : ℝ) ∂q.toMeasure) + (x : ℝ) ^ 3 := fun x => by
    rw [← PMF.toMeasure_map (· + x) q (measurable_add_const x),
        MeasureTheory.integral_map (measurable_add_const x).aemeasurable
          (Measurable.of_discrete.aestronglyMeasurable)]
    push_cast
    -- goal: ∫y, (y+x)³∂q = ∫z³∂q + 3x·∫z²∂q + 3x²·∫z∂q + x³
    haveI : IsProbabilityMeasure q.toMeasure := PMF.toMeasure.isProbabilityMeasure q
    have h_expand : ∫ y : ℤ, ((y : ℝ) + ↑x) ^ 3 ∂q.toMeasure =
        ∫ y : ℤ, ((y : ℝ) ^ 3 + 3 * (x : ℝ) * (y : ℝ) ^ 2 +
          3 * (x : ℝ) ^ 2 * (y : ℝ) + (x : ℝ) ^ 3) ∂q.toMeasure := by
      congr 1; ext y; ring
    rw [h_expand]
    haveI hprob : IsProbabilityMeasure q.toMeasure := PMF.toMeasure.isProbabilityMeasure q
    -- Rewrite ∫(a+b+c+d)∂μ as ∫a + ∫b + ∫c + ∫d using integral_add
    have ha : Integrable (fun y : ℤ => (y : ℝ) ^ 3) q.toMeasure := hq_cube
    have hb : Integrable (fun y : ℤ => 3 * (x : ℝ) * (y : ℝ) ^ 2) q.toMeasure :=
      hq_sq.const_mul _
    have hc : Integrable (fun y : ℤ => 3 * (x : ℝ) ^ 2 * (y : ℝ)) q.toMeasure :=
      hq_int.const_mul _
    have hd : Integrable (fun _ : ℤ => (x : ℝ) ^ 3) q.toMeasure := integrable_const _
    have hbc : Integrable (fun y : ℤ => 3 * (x : ℝ) * (y : ℝ) ^ 2 + 3 * (x : ℝ) ^ 2 * (y : ℝ))
        q.toMeasure := hb.add hc
    have hbcd : Integrable (fun y : ℤ => 3 * (x : ℝ) * (y : ℝ) ^ 2 +
        3 * (x : ℝ) ^ 2 * (y : ℝ) + (x : ℝ) ^ 3) q.toMeasure := hbc.add hd
    conv_lhs =>
      rw [show (fun y : ℤ => (y : ℝ) ^ 3 + 3 * (x : ℝ) * (y : ℝ) ^ 2 +
          3 * (x : ℝ) ^ 2 * (y : ℝ) + (x : ℝ) ^ 3) =
        fun y : ℤ => (y : ℝ) ^ 3 + (3 * (x : ℝ) * (y : ℝ) ^ 2 +
          3 * (x : ℝ) ^ 2 * (y : ℝ) + (x : ℝ) ^ 3) from by ext y; ring]
    rw [integral_add ha hbcd,
      show (fun y : ℤ => 3 * (x : ℝ) * (y : ℝ) ^ 2 + 3 * (x : ℝ) ^ 2 * (y : ℝ) + (x : ℝ) ^ 3) =
        fun y : ℤ => (3 * (x : ℝ) * (y : ℝ) ^ 2 + 3 * (x : ℝ) ^ 2 * (y : ℝ)) + (x : ℝ) ^ 3
        from by ext y; ring,
      integral_add hbc hd,
      show (fun y : ℤ => 3 * (x : ℝ) * (y : ℝ) ^ 2 + 3 * (x : ℝ) ^ 2 * (y : ℝ)) =
        fun y : ℤ => 3 * (x : ℝ) * (y : ℝ) ^ 2 + 3 * (x : ℝ) ^ 2 * (y : ℝ)
        from rfl,
      integral_add hb hc]
    simp only [integral_const_mul, integral_const, probReal_univ, one_smul]
    ring
  -- Integrability of z³ under shifted q
  have hqshift_cube : ∀ x : ℤ,
      Integrable (fun z : ℤ => (z : ℝ) ^ 3) (q.map (· + x)).toMeasure := fun x => by
    rw [← PMF.toMeasure_map (· + x) q (measurable_add_const x),
        integrable_map_measure Measurable.of_discrete.aestronglyMeasurable
          (measurable_add_const x).aemeasurable]
    simp only [Function.comp_def]
    have heq : (fun y : ℤ => ((y + x : ℤ) : ℝ) ^ 3) =
        fun y : ℤ => (y : ℝ) ^ 3 + 3 * (x : ℝ) * (y : ℝ) ^ 2 +
          3 * (x : ℝ) ^ 2 * (y : ℝ) + (x : ℝ) ^ 3 := by
      ext y; push_cast; ring
    rw [heq]
    exact (((hq_cube.add (hq_sq.const_mul _)).add (hq_int.const_mul _)).add (integrable_const _))
  -- The bind measure as a finite weighted sum
  have hbind_meas : (p.bind (fun x => q.map (· + x))).toMeasure =
      ∑ x ∈ hp_fin.toFinset, p x • (q.map (· + x)).toMeasure := by
    ext s hs
    rw [PMF.toMeasure_bind_apply p (fun x => q.map (· + x)) s hs]
    simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
    exact tsum_eq_sum (s := hp_fin.toFinset) (fun x hx => by simp [hmem x hx])
  have hone : ∑ x ∈ hp_fin.toFinset, (p x).toReal = 1 := by
    have : ∑' a, p a = 1 := PMF.tsum_coe p
    rw [tsum_eq_sum (s := hp_fin.toFinset) hmem] at this
    calc ∑ x ∈ hp_fin.toFinset, (p x).toReal
        = (∑ x ∈ hp_fin.toFinset, p x).toReal := by rw [ENNReal.toReal_sum (fun x _ => hlt x)]
      _ = (1 : ENNReal).toReal := by rw [this]
      _ = 1 := ENNReal.toReal_one
  have hint_p : ∑ x ∈ hp_fin.toFinset, (p x).toReal * (x : ℝ) =
      ∫ z, (z : ℝ) ∂p.toMeasure := by
    rw [PMF.integral_eq_tsum _ _ hp_int]
    conv_rhs => rw [tsum_eq_sum (s := hp_fin.toFinset) (fun x hx => by
        simp [smul_eq_mul, show (p x).toReal = 0 from by simp [hmem x hx]])]
    apply Finset.sum_congr rfl; intro x _; simp [smul_eq_mul]
  have hint_p_sq : ∑ x ∈ hp_fin.toFinset, (p x).toReal * (x : ℝ) ^ 2 =
      ∫ z, (z : ℝ) ^ 2 ∂p.toMeasure := by
    rw [PMF.integral_eq_tsum _ _ hp_sq]
    conv_rhs => rw [tsum_eq_sum (s := hp_fin.toFinset) (fun x hx => by
        simp [smul_eq_mul, show (p x).toReal = 0 from by simp [hmem x hx]])]
    apply Finset.sum_congr rfl; intro x _; simp [smul_eq_mul]
  have hint_p_cube : ∑ x ∈ hp_fin.toFinset, (p x).toReal * (x : ℝ) ^ 3 =
      ∫ z, (z : ℝ) ^ 3 ∂p.toMeasure := by
    rw [PMF.integral_eq_tsum _ _ hp_cube]
    conv_rhs => rw [tsum_eq_sum (s := hp_fin.toFinset) (fun x hx => by
        simp [smul_eq_mul, show (p x).toReal = 0 from by simp [hmem x hx]])]
    apply Finset.sum_congr rfl; intro x _; simp [smul_eq_mul]
  rw [hbind_meas, integral_finsetSum_measure (f := fun z : ℤ => (z : ℝ) ^ 3)
        (μ := fun x => p x • (q.map (· + x)).toMeasure)
        (fun x _ => (hqshift_cube x).smul_measure (hlt x))]
  simp_rw [integral_smul_measure _ (p _), hshift_cube]
  simp_rw [smul_add, smul_eq_mul, Finset.sum_add_distrib]
  set Eq3 := ∫ z, (z : ℝ) ^ 3 ∂q.toMeasure
  set Eq2 := ∫ z, (z : ℝ) ^ 2 ∂q.toMeasure
  set Eq := ∫ z, (z : ℝ) ∂q.toMeasure
  have hfst : ∑ x ∈ hp_fin.toFinset, (p x).toReal * Eq3 = Eq3 := by
    rw [← Finset.sum_mul, hone, one_mul]
  have hm1 : ∑ x ∈ hp_fin.toFinset, (p x).toReal * (3 * ↑x * Eq2) =
      3 * Eq2 * ∫ z, (z : ℝ) ∂p.toMeasure := by
    rw [show (fun x : ℤ => (p x).toReal * (3 * ↑x * Eq2)) =
        (fun x : ℤ => 3 * Eq2 * ((p x).toReal * ↑x)) from by ext x; ring]
    rw [← Finset.mul_sum, hint_p]
  have hm2 : ∑ x ∈ hp_fin.toFinset, (p x).toReal * (3 * ↑x ^ 2 * Eq) =
      3 * Eq * ∫ z, (z : ℝ) ^ 2 ∂p.toMeasure := by
    rw [show (fun x : ℤ => (p x).toReal * (3 * ↑x ^ 2 * Eq)) =
        (fun x : ℤ => 3 * Eq * ((p x).toReal * ↑x ^ 2)) from by ext x; ring]
    rw [← Finset.mul_sum, hint_p_sq]
  linarith [hfst, hint_p_cube, hm1, hm2]

-- Helper: cube formula for Y_sum_pmf_list:
-- ∫z³∂(Y_sum_list l) = ∑(E[Y³] - 3E[Y²]E[Y] + 2(EY)³)
--   + 3·(∫z²∂list)·(∫z∂list) - 2·(∫z∂list)³
private lemma Y_sum_pmf_list_cube_formula (G : TemporalGraph V) (t : ℕ) (s : Finset V)
    (l : List V) :
    ∫ z, (z : ℝ) ^ 3 ∂(Y_sum_pmf_list G t s l).toMeasure =
      (l.map (fun v => ∫ z, (z : ℝ) ^ 3 ∂(YPMF G t s v).toMeasure
        - 3 * (∫ z, (z : ℝ) ^ 2 ∂(YPMF G t s v).toMeasure) *
              (∫ z, (z : ℝ) ∂(YPMF G t s v).toMeasure)
        + 2 * (∫ z, (z : ℝ) ∂(YPMF G t s v).toMeasure) ^ 3)).sum
      + 3 * (∫ z, (z : ℝ) ^ 2 ∂(Y_sum_pmf_list G t s l).toMeasure) *
            (∫ z, (z : ℝ) ∂(Y_sum_pmf_list G t s l).toMeasure)
      - 2 * (∫ z, (z : ℝ) ∂(Y_sum_pmf_list G t s l).toMeasure) ^ 3 := by
  induction l with
  | nil => simp [Y_sum_pmf_list, PMF.toMeasure_pure]
  | cons v vs ih =>
    simp only [Y_sum_pmf_list, List.map_cons, List.sum_cons]
    set p := Y_sum_pmf_list G t s vs with hp_def
    set q := YPMF G t s v with hq_def
    have hp_fin : p.support.Finite := Y_sum_pmf_list_support_finite G t s vs
    have hq_int : Integrable (fun z : ℤ => (z : ℝ)) q.toMeasure := YPMF_int_integrable G t s v
    have hq_sq : Integrable (fun z : ℤ => (z : ℝ) ^ 2) q.toMeasure := by
      rw [← PMF.restrict_toMeasure_support q]; apply IntegrableOn.of_finite
      simp only [hq_def, YPMF]; split_ifs with hd hv
      · simp [PMF.support_pure]
      · simp only [twoPointPMF, PMF.support_map]; exact Set.Finite.image _ (Set.toFinite _)
      · simp only [twoPointPMF, PMF.support_map]; exact Set.Finite.image _ (Set.toFinite _)
    have hq_cube : Integrable (fun z : ℤ => (z : ℝ) ^ 3) q.toMeasure := by
      rw [← PMF.restrict_toMeasure_support q]; apply IntegrableOn.of_finite
      simp only [hq_def, YPMF]; split_ifs with hd hv
      · simp [PMF.support_pure]
      · simp only [twoPointPMF, PMF.support_map]; exact Set.Finite.image _ (Set.toFinite _)
      · simp only [twoPointPMF, PMF.support_map]; exact Set.Finite.image _ (Set.toFinite _)
    rw [pmf_integral_bind_cube p q hp_fin hq_int hq_sq hq_cube,
        pmf_integral_bind_sq p q hp_fin hq_int hq_sq,
        pmf_integral_bind_add_map p q hp_fin hq_int]
    -- Use ih to substitute the cube integral of p
    set M1 := ∫ z, (z : ℝ) ∂p.toMeasure
    set M2 := ∫ z, (z : ℝ) ^ 2 ∂p.toMeasure
    set M3 := ∫ z, (z : ℝ) ^ 3 ∂p.toMeasure
    set m1 := ∫ z, (z : ℝ) ∂q.toMeasure
    set m2 := ∫ z, (z : ℝ) ^ 2 ∂q.toMeasure
    set m3 := ∫ z, (z : ℝ) ^ 3 ∂q.toMeasure
    set C := (List.map (fun v => ∫ z, (z : ℝ) ^ 3 ∂(YPMF G t s v).toMeasure
      - 3 * (∫ z, (z : ℝ) ^ 2 ∂(YPMF G t s v).toMeasure) *
            (∫ z, (z : ℝ) ∂(YPMF G t s v).toMeasure)
      + 2 * (∫ z, (z : ℝ) ∂(YPMF G t s v).toMeasure) ^ 3) vs).sum
    -- ih: M3 = C + 3·M2·M1 - 2·M1³
    have hih : M3 = C + 3 * M2 * M1 - 2 * M1 ^ 3 := ih
    linear_combination hih

/-- Third moment non-positivity for `Y_sum_pmf`:
`E[(∑_v Y_v)³] ≤ 0`.

Proof: By independence, `E[(∑_v Y_v)³] = ∑_v E[Y_v³]` (plus cross terms; cross terms vanish
for independent zero-mean-ish variables when we use the multinomial expansion).
Actually for minority `v ∈ s`: `E[Y_v³] = -d_v² · λ_v / 2 ≤ 0`.
For majority `v ∉ s`: `E[Y_v³] = λ_v³ / 2 ≥ 0`.
The net sign requires showing the minority cube terms dominate; this follows from
`λ_v ≤ d_v` (`lambdaCut_le_degree`) giving `λ_v³ ≤ d_v² · λ_v`,
so `E[Y_v³]_{majority} ≤ -E[Y_v³]_{minority}` per matching `λ_v` value. -/
private lemma Y_sum_pmf_third_moment_nonpos
    (G : TemporalGraph V)
    (t : ℕ) (s : Finset V) :
    ∫ z, (z : ℝ) ^ 3 ∂(Y_sum_pmf G t s).toMeasure ≤ 0 := by
  -- Step 1: apply cube formula, use mean = 0 to simplify
  have hmean : ∫ z, (z : ℝ) ∂(Y_sum_pmf_list G t s Finset.univ.toList).toMeasure = 0 := by
    have := Y_sum_pmf_mean_zero G t s; simpa [Y_sum_pmf] using this
  unfold Y_sum_pmf
  rw [Y_sum_pmf_list_cube_formula, hmean]
  simp only [mul_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    add_zero]
  -- Goal: (Finset.univ.toList.map ...).sum ≤ 0
  -- This equals ∑ v, -λ_v(λ_v - d_v)(λ_v - 2d_v)/4
  -- which factors as ≤ 0 since λ_v ∈ [0, d_v]
  rw [Finset.sum_map_toList]
  apply Finset.sum_nonpos
  intro v _
  simp only [integral_YPMF_cube, integral_YPMF_sq, integral_YPMF_id]
  split_ifs with hv
  · -- minority: E[Y³] - 3E[Y²]E[Y] + 2(EY)³ = -lam(lam-d)(lam-2d)/4
    -- = -d²lam/2 - 3(dlam/2)(-lam/2) + 2(-lam/2)³
    -- = -d²lam/2 + 3dlam²/4 - lam³/4
    set d := (G.degree t v : ℝ) with hd_def
    set lam := (lambdaCut G t s v : ℝ) with hlam_def
    have hlam_nn : 0 ≤ lam := by positivity
    have hlam_le_d : lam ≤ d := by
      have := lambdaCut_le_degree G t s v
      rw [hlam_def, hd_def]; exact_mod_cast this
    have hd_nn : 0 ≤ d := by positivity
    nlinarith [sq_nonneg (d - lam), sq_nonneg lam, mul_nonneg hlam_nn (sub_nonneg.mpr hlam_le_d)]
  · -- majority: E[Y³] - 3E[Y²]E[Y] + 2(EY)³ = 0
    set lam := (lambdaCut G t s v : ℝ)
    ring_nf
    nlinarith [sq_nonneg lam]

/-- Taylor bound for `∫ Real.sqrt (ψ + z) ∂Y_sum_pmf` where `ψ = Vol(s)`.

Given the three moment conditions on `Y_sum_pmf` (`mean = 0`, `E[z²] ≥ d_min·cut/4`,
`E[z³] ≤ 0`) and the Taylor bound `sqrt_one_add_taylor3`, we get:
`∫ √(ψ + z) ∂Y_sum_pmf ≤ √ψ − d_min·cut/(32·ψ^{3/2})`.

Proof: Write `√(ψ+z) = √ψ·√(1+z/ψ)`, apply `sqrt_one_add_taylor3` pointwise,
integrate, substitute moment bounds. -/
private lemma Y_sum_pmf_int_sqrt_bound
    (G : TemporalGraphFixedDegree V)
    (t : ℕ) (s : Finset V)
    -- ψ = Vol(s) > 0 needed for 1/ψ and ψ^{3/2}
    (hψ : (0 : ℝ) < (G.snapshot t).volume s) :
    ∫ z, Real.sqrt ((G.snapshot t).volume s + z : ℝ) ∂(Y_sum_pmf G.toTemporalGraph t s).toMeasure
      ≤ Real.sqrt ((G.snapshot t).volume s : ℝ)
        - (G.minDegreeAt 0 : ℝ) * (G.edgesBetween t s (univ \ s) : ℝ)
          / (32 * ((G.snapshot t).volume s : ℝ) ^ (3 / 2 : ℝ)) := by
  set ψ := ((G.snapshot t).volume s : ℝ) with hψ_def
  set sqψ := Real.sqrt ψ with hsqψ_def
  have hsqψ_pos : 0 < sqψ := Real.sqrt_pos.mpr hψ
  -- Finite support facts
  have hsupp_fin : (Y_sum_pmf G.toTemporalGraph t s).support.Finite := by
    unfold Y_sum_pmf; exact Y_sum_pmf_list_support_finite G.toTemporalGraph t s _
  -- All powers of z are integrable w.r.t. Y_sum_pmf (finite support)
  have hint_sq : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (Y_sum_pmf G.toTemporalGraph t s).toMeasure := by
    rw [← PMF.restrict_toMeasure_support]; exact IntegrableOn.of_finite hsupp_fin
  have hint_cube : Integrable (fun z : ℤ => (z : ℝ) ^ 3) (Y_sum_pmf G.toTemporalGraph t s).toMeasure := by
    rw [← PMF.restrict_toMeasure_support]; exact IntegrableOn.of_finite hsupp_fin
  -- Support lower bound: z ∈ supp(Y_sum_pmf) → z ≥ -Vol(s)
  have hsupp_lb : ∀ z ∈ (Y_sum_pmf G.toTemporalGraph t s).support, -((G.snapshot t).volume s : ℤ) ≤ z := by
    unfold Y_sum_pmf
    intro z hz
    have hfilt := Y_sum_pmf_list_support_lb G.toTemporalGraph t s Finset.univ.toList
      (Finset.univ.nodup_toList) z hz
    have heq : s.filter (· ∈ Finset.univ.toList) = s := by
      ext v; simp [Finset.mem_toList]
    rw [heq] at hfilt
    have hvol : (∑ v ∈ s, (G.degree t v : ℤ)) = ((G.snapshot t).volume s : ℤ) := by
      simp only [SimpleGraph.volume]
      push_cast; rfl
    linarith [hvol ▸ hfilt]
  -- Pointwise Taylor bound: for z ∈ supp, √(ψ+z) ≤ √ψ + z/(2√ψ) - z²/(8ψ^{3/2}) + z³/(16ψ^{5/2})
  -- Write as: √(ψ+z) ≤ √ψ · (1 + (z/ψ)/2 - (z/ψ)²/8 + (z/ψ)³/16)
  -- Equivalently: √(ψ+z) ≤ √ψ + z/(2√ψ) - z²/(8·ψ^{3/2}) + z³/(16·ψ^{5/2})
  have hψ32 : ψ ^ (3 / 2 : ℝ) = sqψ ^ 3 := by
    have : sqψ = ψ ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow ψ
    rw [this, ← Real.rpow_natCast (ψ ^ (1/2 : ℝ)) 3, ← Real.rpow_mul hψ.le]; norm_num
  have hψ52 : ψ ^ (5 / 2 : ℝ) = sqψ ^ 5 := by
    have : sqψ = ψ ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow ψ
    rw [this, ← Real.rpow_natCast (ψ ^ (1/2 : ℝ)) 5, ← Real.rpow_mul hψ.le]; norm_num
  have hsqψ_sq : sqψ ^ 2 = ψ := Real.sq_sqrt hψ.le
  -- The Taylor RHS function
  set f_taylor : ℤ → ℝ :=
    fun z => sqψ + (z : ℝ) / (2 * sqψ) - (z : ℝ) ^ 2 / (8 * ψ ^ (3 / 2 : ℝ))
              + (z : ℝ) ^ 3 / (16 * ψ ^ (5 / 2 : ℝ)) with hf_taylor_def
  -- Pointwise: √(ψ+z) ≤ f_taylor z for all z ∈ supp
  have hpw : ∀ z ∈ (Y_sum_pmf G.toTemporalGraph t s).support,
      Real.sqrt (ψ + (z : ℝ)) ≤ f_taylor z := by
    intro z hz
    have hlb := hsupp_lb z hz
    -- z ≥ -ψ since -Vol(s) ≥ -ψ (both are ψ)
    have hz_lb : -(ψ) ≤ (z : ℝ) := by
      rw [hψ_def]; exact_mod_cast hlb
    -- Apply sqrt_one_add_taylor3 with x = z/ψ
    have hx_lb : (-1 : ℝ) ≤ (z : ℝ) / ψ := by
      rw [le_div_iff₀ hψ]; linarith
    have h1 : Real.sqrt (ψ + (z : ℝ)) = sqψ * Real.sqrt (1 + (z : ℝ) / ψ) := by
      rw [show ψ + (z : ℝ) = ψ * (1 + (z : ℝ) / ψ) by field_simp]
      rw [Real.sqrt_mul hψ.le, hsqψ_def]
    rw [h1]
    have htaylor := sqrt_one_add_taylor3 ((z : ℝ) / ψ) hx_lb
    have hbound : sqψ * Real.sqrt (1 + (z : ℝ) / ψ) ≤
        sqψ * (1 + (z : ℝ) / ψ / 2 - ((z : ℝ) / ψ) ^ 2 / 8 + ((z : ℝ) / ψ) ^ 3 / 16) :=
      mul_le_mul_of_nonneg_left htaylor hsqψ_pos.le
    calc sqψ * Real.sqrt (1 + (z : ℝ) / ψ)
        ≤ sqψ * (1 + (z : ℝ) / ψ / 2 - ((z : ℝ) / ψ) ^ 2 / 8 + ((z : ℝ) / ψ) ^ 3 / 16) :=
            hbound
      _ = f_taylor z := by
            simp only [hf_taylor_def, hψ32, hψ52]
            have hψ2 : sqψ ^ 2 = ψ := hsqψ_sq
            have hsqψ_ne : sqψ ≠ 0 := hsqψ_pos.ne'
            have hψ_ne : ψ ≠ 0 := hψ.ne'
            -- Eliminate ψ using ψ = sqψ² then use field_simp + ring
            have hψ_eq : ψ = sqψ ^ 2 := hψ2.symm
            rw [hψ_eq]
            field_simp [hsqψ_ne]
  -- Integrability of f_taylor under Y_sum_pmf
  have hint_id : Integrable (fun z : ℤ => (z : ℝ)) (Y_sum_pmf G.toTemporalGraph t s).toMeasure := by
    rw [← PMF.restrict_toMeasure_support]; exact IntegrableOn.of_finite hsupp_fin
  have hint_lhs : Integrable (fun z : ℤ => Real.sqrt (ψ + (z : ℝ)))
      (Y_sum_pmf G.toTemporalGraph t s).toMeasure := by
    rw [← PMF.restrict_toMeasure_support]; exact IntegrableOn.of_finite hsupp_fin
  have hint_rhs : Integrable f_taylor (Y_sum_pmf G.toTemporalGraph t s).toMeasure := by
    rw [← PMF.restrict_toMeasure_support]; exact IntegrableOn.of_finite hsupp_fin
  -- Step 1: ∫ √(ψ+z) ≤ ∫ f_taylor by integral_mono_ae
  have hstep1 : ∫ z, Real.sqrt (ψ + (z : ℝ)) ∂(Y_sum_pmf G.toTemporalGraph t s).toMeasure
      ≤ ∫ z, f_taylor z ∂(Y_sum_pmf G.toTemporalGraph t s).toMeasure := by
    apply MeasureTheory.integral_mono_ae hint_lhs hint_rhs
    -- The ae bound follows from the support bound (PMF.toMeasure = restrict on support)
    rw [← PMF.restrict_toMeasure_support]
    exact ae_restrict_of_forall_mem (PMF.support_countable _).measurableSet
      (fun z hz => hpw z hz)
  -- Step 2: evaluate ∫ f_taylor using moment bounds
  have hint_rhs_eq : ∫ z, f_taylor z ∂(Y_sum_pmf G.toTemporalGraph t s).toMeasure =
      sqψ + (∫ z, (z : ℝ) ∂(Y_sum_pmf G.toTemporalGraph t s).toMeasure) / (2 * sqψ)
        - (∫ z, (z : ℝ) ^ 2 ∂(Y_sum_pmf G.toTemporalGraph t s).toMeasure) / (8 * ψ ^ (3 / 2 : ℝ))
        + (∫ z, (z : ℝ) ^ 3 ∂(Y_sum_pmf G.toTemporalGraph t s).toMeasure) / (16 * ψ ^ (5 / 2 : ℝ)) := by
    simp only [hf_taylor_def]
    haveI hprob : IsProbabilityMeasure (Y_sum_pmf G.toTemporalGraph t s).toMeasure :=
      PMF.toMeasure.isProbabilityMeasure _
    have h_intA : Integrable (fun z : ℤ => (z : ℝ) / (2 * sqψ)) (Y_sum_pmf G.toTemporalGraph t s).toMeasure :=
      hint_id.div_const _
    have h_intB : Integrable (fun z : ℤ => (z : ℝ) ^ 2 / (8 * ψ ^ (3/2:ℝ))) (Y_sum_pmf G.toTemporalGraph t s).toMeasure :=
      hint_sq.div_const _
    have h_intC : Integrable (fun z : ℤ => (z : ℝ) ^ 3 / (16 * ψ ^ (5/2:ℝ))) (Y_sum_pmf G.toTemporalGraph t s).toMeasure :=
      hint_cube.div_const _
    have h_intconst : Integrable (fun _ : ℤ => sqψ) (Y_sum_pmf G.toTemporalGraph t s).toMeasure :=
      integrable_const _
    have h_int1 : Integrable (fun z : ℤ => sqψ + (z:ℝ) / (2*sqψ)) (Y_sum_pmf G.toTemporalGraph t s).toMeasure :=
      h_intconst.add h_intA
    have h_int2 : Integrable (fun z : ℤ => sqψ + (z:ℝ)/(2*sqψ) - (z:ℝ)^2/(8*ψ^(3/2:ℝ)))
        (Y_sum_pmf G.toTemporalGraph t s).toMeasure := h_int1.sub h_intB
    conv_lhs => rw [show (fun z : ℤ => sqψ + (z:ℝ)/(2*sqψ) - (z:ℝ)^2/(8*ψ^(3/2:ℝ))
                            + (z:ℝ)^3/(16*ψ^(5/2:ℝ))) =
                      fun z : ℤ => (sqψ + (z:ℝ)/(2*sqψ) - (z:ℝ)^2/(8*ψ^(3/2:ℝ)))
                            + (z:ℝ)^3/(16*ψ^(5/2:ℝ)) from by ext; ring]
    rw [integral_add h_int2 h_intC]
    conv_lhs => rw [show (fun z : ℤ => sqψ + (z:ℝ)/(2*sqψ) - (z:ℝ)^2/(8*ψ^(3/2:ℝ))) =
                      fun z : ℤ => (sqψ + (z:ℝ)/(2*sqψ)) - (z:ℝ)^2/(8*ψ^(3/2:ℝ)) from
                      by ext; ring]
    rw [integral_sub h_int1 h_intB, integral_add h_intconst h_intA,
        integral_const, probReal_univ, one_smul,
        integral_div, integral_div, integral_div]
  -- Step 3: substitute moment bounds
  have hmean := Y_sum_pmf_mean_zero G.toTemporalGraph t s
  have hmom2 := Y_sum_pmf_second_moment_lb G t s
  have hmom3 := Y_sum_pmf_third_moment_nonpos G.toTemporalGraph t s
  rw [hψ_def] at hstep1
  calc ∫ z, Real.sqrt (↑((G.snapshot t).volume s) + ↑z) ∂(Y_sum_pmf G.toTemporalGraph t s).toMeasure
      ≤ ∫ z, f_taylor z ∂(Y_sum_pmf G.toTemporalGraph t s).toMeasure := hstep1
    _ = sqψ + (∫ z, (z : ℝ) ∂(Y_sum_pmf G.toTemporalGraph t s).toMeasure) / (2 * sqψ)
          - (∫ z, (z : ℝ) ^ 2 ∂(Y_sum_pmf G.toTemporalGraph t s).toMeasure) / (8 * ψ ^ (3 / 2 : ℝ))
          + (∫ z, (z : ℝ) ^ 3 ∂(Y_sum_pmf G.toTemporalGraph t s).toMeasure) / (16 * ψ ^ (5 / 2 : ℝ)) :=
            hint_rhs_eq
    _ ≤ sqψ + 0 / (2 * sqψ)
          - ((G.minDegreeAt 0 : ℝ) * (G.edgesBetween t s (univ \ s) : ℝ) / 4)
              / (8 * ψ ^ (3 / 2 : ℝ))
          + 0 / (16 * ψ ^ (5 / 2 : ℝ)) := by
            have hψ32_pos : (0 : ℝ) < 8 * ψ ^ (3 / 2 : ℝ) := by positivity
            have hψ52_pos : (0 : ℝ) < 16 * ψ ^ (5 / 2 : ℝ) := by positivity
            have h3le : (∫ z, (z : ℝ) ^ 3 ∂(Y_sum_pmf G.toTemporalGraph t s).toMeasure) /
                (16 * ψ ^ (5 / 2 : ℝ)) ≤ 0 :=
              div_nonpos_of_nonpos_of_nonneg hmom3 hψ52_pos.le
            have h1eq : (∫ z, (z : ℝ) ∂(Y_sum_pmf G.toTemporalGraph t s).toMeasure) = 0 := hmean
            -- -(E[z²])/(8ψ^{3/2}) ≤ -(dmin·cut/4)/(8ψ^{3/2}) from dmin·cut/4 ≤ E[z²]
            have h2div : (∫ z, (z : ℝ) ^ 2 ∂(Y_sum_pmf G.toTemporalGraph t s).toMeasure) /
                (8 * ψ ^ (3 / 2 : ℝ)) ≥
                ((G.minDegreeAt 0 : ℝ) * (G.edgesBetween t s (univ \ s) : ℝ) / 4) /
                (8 * ψ ^ (3 / 2 : ℝ)) :=
              div_le_div_of_nonneg_right hmom2 hψ32_pos.le
            have h1div : (∫ z, (z : ℝ) ∂(Y_sum_pmf G.toTemporalGraph t s).toMeasure) / (2 * sqψ) = 0 := by
              rw [h1eq]; simp
            have hzero1 : (0 : ℝ) / (2 * sqψ) = 0 := zero_div _
            have hzero2 : (0 : ℝ) / (16 * ψ ^ (5 / 2 : ℝ)) = 0 := zero_div _
            linarith
    _ = sqψ - (G.minDegreeAt 0 : ℝ) * (G.edgesBetween t s (univ \ s) : ℝ)
          / (32 * ψ ^ (3 / 2 : ℝ)) := by ring
    _ = Real.sqrt ((G.snapshot t).volume s : ℝ)
          - (G.minDegreeAt 0 : ℝ) * (G.edgesBetween t s (univ \ s) : ℝ)
            / (32 * ((G.snapshot t).volume s : ℝ) ^ (3 / 2 : ℝ)) := by
              rw [← hψ_def, ← hsqψ_def]

/-! ### X-side parallel infrastructure

Mirror of the `Y_sum_pmf` infrastructure using the original per-vertex contribution
`XPMF G.toTemporalGraph t s v : PMF ℤ` (see `VoterModel.Spec.VoterModel`) instead of the replaced
variable `YPMF`. The marginal volume change `Δ_v` for vertex `v` under `stepDist₂Aux`
is `±d_v` w.p. `λ_v/(2 d_v)` (± on minority/majority), which is exactly `XPMF`.

The sum `X_sum_pmf G.toTemporalGraph t s` is the independent sum `∑_v X_v` assembled by iterated
bind/map over `Finset.univ.toList`. It shares the minority branch with `YPMF`,
so their means agree (`integral_XPMF_eq_YPMF_id`) and the edge-symmetry argument
behind `Y_sum_pmf_mean_zero` transfers verbatim to show `∫ z ∂X_sum_pmf = 0`. -/

/-- Independent sum of per-vertex `XPMF G t s v` over a list `l` of vertices, built
by iterated `bind`/`map`. Mirrors `Y_sum_pmf_list`; used via `X_sum_pmf`. -/
private noncomputable def X_sum_pmf_list (G : TemporalGraph V) (t : ℕ) (s : Finset V) :
    List V → PMF ℤ
  | [] => PMF.pure 0
  | v :: vs => (X_sum_pmf_list G t s vs).bind (fun z => (XPMF G t s v).map (· + z))

/-- Independent sum `∑_{v : V} X_v` of per-vertex `XPMF` contributions. Mirror of
`Y_sum_pmf`. -/
private noncomputable def X_sum_pmf (G : TemporalGraph V) (t : ℕ) (s : Finset V) : PMF ℤ :=
  X_sum_pmf_list G t s (Finset.univ : Finset V).toList

-- `X_sum_pmf_list G t s l` has finite support (by induction on l).
-- Base: PMF.pure 0 has support {0} (finite).
-- Step: bind of finite-support PMF with XPMF's finite support shifted is finite.
private lemma X_sum_pmf_list_support_finite (G : TemporalGraph V) (t : ℕ) (s : Finset V)
    (l : List V) : (X_sum_pmf_list G t s l).support.Finite := by
  induction l with
  | nil => simp [X_sum_pmf_list, PMF.support_pure]
  | cons v vs ih =>
    simp only [X_sum_pmf_list, PMF.support_bind]
    apply Set.Finite.biUnion ih
    intro z _
    simp only [PMF.support_map]
    apply Set.Finite.image
    simp only [XPMF]
    split_ifs with hd hv
    · simp [PMF.support_pure]
    · simp only [twoPointPMF, PMF.support_map]
      exact Set.Finite.image _ (Set.toFinite _)
    · simp only [twoPointPMF, PMF.support_map]
      exact Set.Finite.image _ (Set.toFinite _)

/-! ### Per-vertex integral identity: `nextOpinionDist₂` matches `XPMF` under shift

The paper's "per-vertex ΔVol correspondence": the volume shift contributed by vertex `v`
under the voter update (from `stepDist₂`) has the same distribution as `XPMF G t s v`.
We state this at the integral level (equal expectations against any `f : ℝ → ℝ`),
which is precisely what's needed for the `stepDist₂Aux → X_sum_pmf_list` induction. -/

/-- Helper: `degreeIn(v, s) + degreeIn(v, univ \ s) = d_v`. -/
private lemma degreeIn_add_compl (G : TemporalGraph V) (t : ℕ) (s : Finset V) (v : V) :
    G.degreeIn t v s
      + G.degreeIn t v (Finset.univ \ s)
      = G.degree t v := by
  have h1 : G.degreeIn t v s
      = (((G.snapshot t).neighborFinset v).filter (fun w => w ∈ s)).card := by
    simp only [TemporalGraph.degreeIn, SimpleGraph.degreeIn]
    congr 1; ext w; simp [and_comm]
  have h2 : G.degreeIn t v (Finset.univ \ s)
      = (((G.snapshot t).neighborFinset v).filter (fun w => w ∉ s)).card := by
    simp only [TemporalGraph.degreeIn, SimpleGraph.degreeIn]
    congr 1; ext w; simp [and_comm]
  rw [h1, h2, Finset.card_filter_add_card_filter_not]
  rfl

/-- Helper: degreeIn(v, s) ≤ d_v. -/
private lemma degreeIn_le_degree' (G : TemporalGraph V) (t : ℕ) (s : Finset V) (v : V) :
    G.degreeIn t v s ≤ G.degree t v := by
  have := degreeIn_add_compl G t s v; omega

/-- Reduced per-vertex integral identity at the "computed" level.

For a general real function `f : ℝ → ℝ` and real constant `C`, the expectation of
`f(C + (cond iZ d_v 0))` under `nextOpinionDist₂ G t s v` equals the expectation of
`f(C_shifted + z)` under `XPMF G t s v`, where `C_shifted = C + (if v ∈ s then d_v else 0)`.

This expresses the equivalence between `stepDist₂`'s per-vertex update (adding d_v when
the vertex's new opinion is 0) and `XPMF`'s discrete distribution. -/
private lemma integral_nextOpinionDist₂_eq_integral_XPMF
    (G : TemporalGraph V) (t : ℕ) (s : Finset V) (v : V)
    (C : ℝ) (f : ℝ → ℝ) :
    ∫ iZ, f (C + (if iZ then (G.degree t v : ℝ) else 0))
        ∂(nextOpinionDist₂ G t s v).toMeasure
      = ∫ z, f ((if v ∈ s then (G.degree t v : ℝ) else 0) + C + (z : ℝ))
          ∂(XPMF G t s v).toMeasure := by
  letI : MeasurableSpace V := ⊤
  haveI : MeasurableSingletonClass V := ⟨fun _ => trivial⟩
  by_cases hd : G.degree t v = 0
  · -- d = 0: nextOpinionDist₂ = pure, XPMF = pure 0. Both sides evaluate to f(C) or f(C) + 0.
    have hN : ¬(G.neighborFinset t v).Nonempty := by
      intro h
      have : (G.neighborFinset t v).card = G.degree t v := rfl
      rw [hd] at this
      exact (Finset.card_pos.mpr h).ne' this
    rw [nextOpinionDist₂_eq_pure_of_not_nonempty G t s v hN, PMF.toMeasure_pure,
      integral_dirac]
    simp only [XPMF, hd, dite_true, PMF.toMeasure_pure]
    rw [integral_dirac]
    simp only [Nat.cast_zero, Int.cast_zero, add_zero]
    by_cases hvs : v ∈ s <;> simp [hvs]
  · -- d ≠ 0: both have two-point structure. Compute both sides directly.
    have hN : (G.neighborFinset t v).Nonempty := by
      by_contra h
      apply hd
      have : (G.neighborFinset t v).card = G.degree t v := rfl
      rw [← this, Finset.card_eq_zero]
      exact Finset.not_nonempty_iff_eq_empty.mp h
    have hd_pos : (0 : ℝ) < G.degree t v := by
      exact_mod_cast Nat.pos_of_ne_zero hd
    have hncard_eq : ((G.neighborFinset t v).card : ℝ) = G.degree t v := by rfl
    -- LHS = (1/2)·f(C + (if v∈s then d else 0)) + (1/2)·∫ w, f(C + (if w∈s then d else 0)) ∂unif
    --     = (1/2)·{v∈s case} + (1/2)·{(degIn(v,s)/d)·f(C+d) + (1 - degIn(v,s)/d)·f(C)}
    have hLHS :
        ∫ iZ, f (C + (if iZ then (G.degree t v : ℝ) else 0))
            ∂(nextOpinionDist₂ G t s v).toMeasure =
        (1/2 : ℝ) * f (C + (if v ∈ s then (G.degree t v : ℝ) else 0))
          + (1/2) * ((G.degreeIn t v s : ℝ) / G.degree t v
              * f (C + G.degree t v)
              + (1 - (G.degreeIn t v s : ℝ) / G.degree t v)
                * f C) := by
      rw [nextOpinionDist₂_eq_bind_of_nonempty G t s v hN, pmf_integral_bind,
        PMF.integral_eq_sum, Fintype.sum_bool]
      -- Simplify fair-coin weights
      simp only [PMF.uniformOfFintype_apply, Fintype.card_bool, cond_true, cond_false, smul_eq_mul]
      have h12 : ((↑(2 : ℕ) : ENNReal)⁻¹).toReal = 1 / 2 := by
        rw [ENNReal.toReal_inv]; norm_num
      rw [h12]
      -- True branch: pure (decide (v ∈ s)) ⟹ integral equals f (C + (if v ∈ s then d else 0))
      have hTrue : ∫ iZ, f (C + (if iZ then (G.degree t v : ℝ) else 0))
            ∂((PMF.pure (decide (v ∈ s))).toMeasure) =
          f (C + (if v ∈ s then (G.degree t v : ℝ) else 0)) := by
        rw [PMF.toMeasure_pure, integral_dirac]
        by_cases hvs : v ∈ s <;> simp [hvs]
      -- False branch: unif.map decide ⟹ compute explicitly
      have hFalse : ∫ iZ, f (C + (if iZ then (G.degree t v : ℝ) else 0))
            ∂(((PMF.uniformOfFinset (G.neighborFinset t v) hN).map
                fun w => decide (w ∈ s))).toMeasure =
          (G.degreeIn t v s : ℝ) / G.degree t v
              * f (C + G.degree t v)
            + (1 - (G.degreeIn t v s : ℝ) / G.degree t v)
              * f C := by
        rw [← PMF.toMeasure_map _ _ (measurable_of_finite _),
          MeasureTheory.integral_map (measurable_of_finite _).aemeasurable
            (measurable_of_finite _).aestronglyMeasurable]
        rw [PMF.integral_eq_sum]
        simp only [PMF.uniformOfFinset_apply, smul_eq_mul]
        -- Restrict sum to neighbor finset (terms outside are zero).
        rw [← Finset.sum_subset (Finset.subset_univ (G.neighborFinset t v))
            (fun x _ hx => by simp [hx])]
        -- Simplify weight and decide: rewrite the entire sum to use 1/d weights.
        trans ∑ w ∈ G.neighborFinset t v,
            (1 / (G.degree t v : ℝ)) *
              f (C + (if w ∈ s then (G.degree t v : ℝ) else 0))
        · apply Finset.sum_congr rfl
          intro x hx
          simp only [hx, if_true, decide_eq_true_iff]
          rw [ENNReal.toReal_inv, ENNReal.toReal_natCast, hncard_eq]
          congr 2; field_simp
        -- Split into v ∈ s and v ∉ s
        rw [← Finset.sum_filter_add_sum_filter_not (G.neighborFinset t v) (fun w => w ∈ s)]
        -- Compute each side
        have hcardS : ((G.neighborFinset t v).filter (fun w => w ∈ s)).card =
            G.degreeIn t v s := by
          simp only [TemporalGraph.degreeIn, SimpleGraph.degreeIn]
          congr 1; ext w
          simp [TemporalGraph.neighborFinset, SimpleGraph.neighborFinset,
            SimpleGraph.mem_neighborSet, and_comm]
        have hcardNS : ((G.neighborFinset t v).filter (fun w => ¬ w ∈ s)).card =
            G.degreeIn t v (Finset.univ \ s) := by
          simp only [TemporalGraph.degreeIn, SimpleGraph.degreeIn]
          congr 1; ext w
          simp [TemporalGraph.neighborFinset, SimpleGraph.neighborFinset,
            SimpleGraph.mem_neighborSet, Finset.mem_sdiff, and_comm]
        have hfS : ∑ w ∈ (G.neighborFinset t v).filter (fun w => w ∈ s),
              (1 / (G.degree t v : ℝ)) *
                f (C + (if w ∈ s then (G.degree t v : ℝ) else 0)) =
            ((G.neighborFinset t v).filter (fun w => w ∈ s)).card *
              ((1 / (G.degree t v : ℝ)) *
                f (C + G.degree t v)) := by
          trans ∑ _ ∈ (G.neighborFinset t v).filter (fun w => w ∈ s),
              (1 / (G.degree t v : ℝ)) * f (C + G.degree t v)
          · apply Finset.sum_congr rfl; intro w hw
            simp only [Finset.mem_filter] at hw; simp [hw.2]
          · simp [Finset.sum_const, nsmul_eq_mul]
        have hfNS : ∑ w ∈ (G.neighborFinset t v).filter (fun w => ¬ w ∈ s),
              (1 / (G.degree t v : ℝ)) *
                f (C + (if w ∈ s then (G.degree t v : ℝ) else 0)) =
            ((G.neighborFinset t v).filter (fun w => ¬ w ∈ s)).card *
              ((1 / (G.degree t v : ℝ)) * f C) := by
          trans ∑ _ ∈ (G.neighborFinset t v).filter (fun w => ¬ w ∈ s),
              (1 / (G.degree t v : ℝ)) * f C
          · apply Finset.sum_congr rfl; intro w hw
            simp only [Finset.mem_filter] at hw; simp [hw.2]
          · simp [Finset.sum_const, nsmul_eq_mul]
        rw [hfS, hfNS]
        rw [hcardS, hcardNS]
        have hne : (G.degree t v : ℝ) ≠ 0 := ne_of_gt hd_pos
        have hcompl : (G.degreeIn t v (Finset.univ \ s) : ℝ)
            / G.degree t v
            = 1 - (G.degreeIn t v s : ℝ) / G.degree t v := by
          have hsum : (G.degreeIn t v s : ℝ)
              + G.degreeIn t v (Finset.univ \ s)
              = G.degree t v := by
            exact_mod_cast degreeIn_add_compl G t s v
          field_simp; linarith
        rw [show ((G.degreeIn t v s : ℕ) : ℝ) *
                (1 / (G.degree t v : ℝ) *
                  f (C + G.degree t v)) +
              ((G.degreeIn t v (Finset.univ \ s) : ℕ) : ℝ) *
                (1 / (G.degree t v : ℝ) * f C) =
            (G.degreeIn t v s : ℝ) / G.degree t v *
              f (C + G.degree t v) +
            (G.degreeIn t v (Finset.univ \ s) : ℝ)
              / G.degree t v * f C from by ring]
        rw [hcompl]
      rw [hTrue, hFalse]
    -- Now evaluate RHS using integral_twoPointPMF_real.
    have hlamCoe : (lambdaCutNNP G t s v hd : ℝ) =
        (lambdaCut G t s v : ℝ) / (2 * G.degree t v) := by
      unfold lambdaCutNNP; rfl
    have hRHS :
        ∫ z, f ((if v ∈ s then (G.degree t v : ℝ) else 0) + C + (z : ℝ))
            ∂(XPMF G t s v).toMeasure =
        (lambdaCut G t s v : ℝ) / (2 * G.degree t v) *
            f ((if v ∈ s then (G.degree t v : ℝ) else 0) + C
              + (if v ∈ s then -(G.degree t v : ℝ)
                          else (G.degree t v : ℝ)))
          + (1 - (lambdaCut G t s v : ℝ) / (2 * G.degree t v)) *
            f ((if v ∈ s then (G.degree t v : ℝ) else 0) + C) := by
      -- Define shifted function g so integral has the form ∫ g(z : ℝ) ∂twoPointPMF.
      set g : ℝ → ℝ :=
        fun x => f ((if v ∈ s then (G.degree t v : ℝ) else 0) + C + x) with hg_def
      show ∫ z, g (z : ℝ) ∂(XPMF G t s v).toMeasure = _
      simp only [XPMF, dif_neg hd]
      by_cases hvs : v ∈ s
      · simp only [if_pos hvs]
        rw [integral_twoPointPMF_real, hlamCoe]
        simp only [Int.cast_neg, Int.cast_natCast, hvs, if_true, hg_def, add_zero]
      · simp only [if_neg hvs]
        rw [integral_twoPointPMF_real, hlamCoe]
        simp only [Int.cast_natCast, hvs, if_false, hg_def, add_zero]
    rw [hLHS, hRHS]
    -- Now arithmetic identity: show the two computed forms are equal.
    have hne : (G.degree t v : ℝ) ≠ 0 := ne_of_gt hd_pos
    by_cases hvs : v ∈ s
    · -- v ∈ s: LHS-middle is f(C+d), LHS-base is f(C). RHS-val: -d term becomes 0.
      simp only [hvs, if_true]
      have hle := degreeIn_le_degree' G t s v
      have hlam : (lambdaCut G t s v : ℝ) = G.degree t v
          - G.degreeIn t v s := by
        rw [lambdaCut, if_pos hvs]
        have hd_compl : G.degreeIn t v (Finset.univ \ s)
            = G.degree t v - G.degreeIn t v s := by
          have := degreeIn_add_compl G t s v; omega
        rw [hd_compl, Nat.cast_sub hle]
      rw [hlam]
      have hCd : (G.degree t v : ℝ) + C + -(G.degree t v : ℝ) = C := by
        ring
      rw [hCd]
      have hdc : (G.degree t v : ℝ) + C = C + G.degree t v := by ring
      rw [hdc]
      field_simp
      ring
    · -- v ∉ s: LHS-middle is f(C), same as RHS-base; RHS-val: +d
      simp only [hvs, if_false]
      have hlam : (lambdaCut G t s v : ℝ) = G.degreeIn t v s := by
        rw [lambdaCut, if_neg hvs]
      rw [hlam]
      simp only [zero_add]
      field_simp
      ring_nf

/-! ### Pushforward identity: `stepDist₂` volume integral matches `X_sum_pmf`

Identifies `∫ f(C + Vol(T)) ∂stepDist₂Aux(L)` with
`∫ f(C + Vol(s ∩ L) + z) ∂X_sum_pmf_list(L)` by induction on `L`, using the
per-vertex bridge `integral_nextOpinionDist₂_eq_integral_XPMF`. The top-level
specialization `stepDist₂_integral_sqrt_eq_X_sum_pmf` with `f = Real.sqrt`,
`C = 0`, `L = Finset.univ.toList` recovers the "stepDist₂ → X_sum_pmf"
pushforward used by `stepDist₂_majorized_by_Y_sum`. -/

-- Helper: bind-over-integer-PMF integral via finite support of the outer.
-- For a finite-support outer PMF `p : PMF ℤ` and a family `q : ℤ → PMF ℤ` whose
-- integrals of `g : ℤ → ℝ` are all finite, the bind-integral equals the outer
-- integral of the inner `q`-integrals. Mirrors `pmf_integral_bind`.
private lemma pmf_integral_bind_intFamily
    (p : PMF ℤ) (hp_fin : p.support.Finite)
    (q : ℤ → PMF ℤ) (g : ℤ → ℝ)
    (hq_int : ∀ x, Integrable g (q x).toMeasure) :
    ∫ z, g z ∂(p.bind q).toMeasure =
      ∫ x, (∫ z, g z ∂(q x).toMeasure) ∂p.toMeasure := by
  -- Elements outside hp_fin.toFinset have p x = 0 (as ENNReal, since PMF values are ENNReal)
  have hmem : ∀ x ∉ hp_fin.toFinset, p x = 0 :=
    fun x hx => (PMF.apply_eq_zero_iff p x).mpr (fun h => hx (hp_fin.mem_toFinset.mpr h))
  -- The bind measure equals a finite weighted sum of inner measures.
  have hbind_meas : (p.bind q).toMeasure =
      ∑ x ∈ hp_fin.toFinset, p x • (q x).toMeasure := by
    ext E hE
    rw [PMF.toMeasure_bind_apply p q E hE]
    simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
    exact tsum_eq_sum (s := hp_fin.toFinset) (fun x hx => by simp [hmem x hx])
  have hlt : ∀ x : ℤ, p x ≠ ⊤ := PMF.apply_ne_top p
  rw [hbind_meas,
    integral_finsetSum_measure (f := g)
      (μ := fun x => p x • (q x).toMeasure)
      (fun x _ => (hq_int x).smul_measure (hlt x))]
  -- LHS is now ∑ x ∈ hp_fin.toFinset, ∫ z, g z ∂(p x • (q x).toMeasure)
  simp_rw [integral_smul_measure]
  -- RHS: expand outer integral on p over hp_fin.toFinset (outside is zero).
  have hpint : Integrable (fun x : ℤ => ∫ z, g z ∂(q x).toMeasure) p.toMeasure := by
    rw [← PMF.restrict_toMeasure_support p]; exact IntegrableOn.of_finite hp_fin
  have hint_decomp :
      ∫ x, (∫ z, g z ∂(q x).toMeasure) ∂p.toMeasure
      = ∑ x ∈ hp_fin.toFinset, (p x).toReal * (∫ z, g z ∂(q x).toMeasure) := by
    rw [PMF.integral_eq_tsum _ _ hpint]
    rw [tsum_eq_sum (s := hp_fin.toFinset)]
    · refine Finset.sum_congr rfl ?_
      intro x _; rw [smul_eq_mul]
    · intro x hx
      simp [show (p x).toReal = 0 from by simp [hmem x hx]]
  rw [hint_decomp]
  refine Finset.sum_congr rfl ?_
  intro x _
  rw [smul_eq_mul]

/-- List-parameterized pushforward: for any `f : ℝ → ℝ`, any `C : ℝ`, and any
nodup list `L`, the expectation of `f(C + Vol(T))` under `stepDist₂Aux G t s L`
equals the expectation of `f(C + Vol(s ∩ L) + z)` under `X_sum_pmf_list G t s L`.

Induction on `L`:
- base `L = []`: `stepDist₂Aux = pure ∅`, `X_sum_pmf_list = pure 0`, both sides collapse
  to `f(C)`.
- step `L = v :: vs`: expand `stepDist₂Aux` as a bind of `nextOpinionDist₂ G t s v`
  over `stepDist₂Aux G t s vs`; pull `v ∉ T'` out (from `stepDist₂Aux_support_subset`)
  to compute `Vol(insert v T') = Vol(T') + d_v`; apply the per-vertex identity
  `integral_nextOpinionDist₂_eq_integral_XPMF`; then apply IH with the shifted
  constant to reassemble as a bind over `X_sum_pmf_list G t s vs`. -/
private lemma stepDist₂Aux_integral_eq_X_sum_pmf_list
    (G : TemporalGraph V) (t : ℕ) (s : Finset V) :
    ∀ (L : List V), L.Nodup → ∀ (C : ℝ) (f : ℝ → ℝ),
      ∫ T, f (C + (G.volume t T : ℝ))
          ∂(stepDist₂Aux G t s L).toMeasure
        = ∫ z, f (C + (∑ v ∈ s.filter (· ∈ L),
                (G.degree t v : ℝ)) + (z : ℝ))
            ∂(X_sum_pmf_list G t s L).toMeasure := by
  letI : MeasurableSpace V := ⊤
  haveI : MeasurableSingletonClass V := ⟨fun _ => trivial⟩
  intro L hnd
  induction L with
  | nil =>
    intro C f
    -- Both sides: pure with single atom → f(C + 0).
    have hvol_empty : (G.volume t (∅ : Finset V) : ℝ) = 0 := by
      simp [TemporalGraph.volume, SimpleGraph.volume]
    have hfilt : s.filter (· ∈ ([] : List V)) = ∅ := by
      ext u; simp
    simp only [stepDist₂Aux, PMF.toMeasure_pure, integral_dirac, X_sum_pmf_list,
      Int.cast_zero]
    rw [hvol_empty, add_zero, hfilt, Finset.sum_empty, add_zero, add_zero]
  | cons v vs ih =>
    have hnd' : vs.Nodup := (List.nodup_cons.mp hnd).2
    have hv_notin_vs : v ∉ vs := (List.nodup_cons.mp hnd).1
    intro C f
    -- LHS: expand stepDist₂Aux(v::vs) as bind over stepDist₂Aux(vs).
    -- For every T' in support, v ∉ T' (since T' ⊆ vs.toFinset and v ∉ vs.toFinset).
    set p := stepDist₂Aux G t s vs with hp_def
    -- Rewrite the inner `.map` integral pointwise, noting `v ∉ T'` on the support.
    have hv_notin_toFinset : v ∉ vs.toFinset := List.mem_toFinset.not.mpr hv_notin_vs
    -- Step (a): unfold stepDist₂Aux(v::vs) and apply pmf_integral_bind.
    have hbind :
        ∫ T, f (C + (G.volume t T : ℝ))
            ∂(stepDist₂Aux G t s (v :: vs)).toMeasure =
        ∫ T', (∫ y, f (C + (G.volume t y : ℝ))
              ∂((nextOpinionDist₂ G t s v).map fun isZero : Bool =>
                  bif isZero then insert v T' else T').toMeasure)
          ∂p.toMeasure := by
      show ∫ T, _ ∂((p.bind fun T' =>
          (nextOpinionDist₂ G t s v).map fun isZero : Bool =>
            bif isZero then insert v T' else T')).toMeasure = _
      rw [pmf_integral_bind]
    rw [hbind]
    -- Step (b): rewrite `.map` integral via change-of-variables; for every T' in
    -- the support, expand to an integral over nextOpinionDist₂ of an `iZ`-dependent
    -- shift, using `v ∉ T'` to compute Vol(insert v T') = Vol(T') + d_v.
    have hinner_eq :
        ∀ T' : Finset V, T' ∈ p.support →
          ∫ y, f (C + (G.volume t y : ℝ))
              ∂((nextOpinionDist₂ G t s v).map fun isZero : Bool =>
                  bif isZero then insert v T' else T').toMeasure =
          ∫ iZ, f ((C + (G.volume t T' : ℝ)) +
                (if iZ then (G.degree t v : ℝ) else 0))
              ∂(nextOpinionDist₂ G t s v).toMeasure := by
      intro T' hT'
      have hvT' : v ∉ T' :=
        fun hvT' => hv_notin_toFinset (stepDist₂Aux_support_subset G t s vs T' hT' hvT')
      -- Change of variables on `.map`.
      rw [← PMF.toMeasure_map _ _ (measurable_of_finite _),
        MeasureTheory.integral_map (measurable_of_finite _).aemeasurable
          (measurable_of_finite _).aestronglyMeasurable]
      refine MeasureTheory.integral_congr_ae (ae_of_all _ ?_)
      intro iZ
      cases iZ with
      | true =>
        simp only [cond_true, if_true]
        -- Vol(insert v T') = Vol(T') + d_v.
        have hvol : G.volume t (insert v T')
            = G.volume t T' + G.degree t v := by
          simp only [TemporalGraph.volume, SimpleGraph.volume]
          rw [Finset.sum_insert hvT']
          ring
        rw [hvol]
        push_cast
        ring_nf
      | false =>
        simp only [cond_false]
        rw [show (if false then (G.degree t v : ℝ) else 0) = 0 from rfl,
          add_zero]
    -- Step (c): bind-integral equals sum over T' of per-fiber integrals, so we can
    -- replace each fiber by the rewritten form a.e. To do so: use the sum expansion of
    -- the bind integral and factor.
    have hLHS :
        ∫ T', (∫ y, f (C + (G.volume t y : ℝ))
              ∂((nextOpinionDist₂ G t s v).map fun isZero : Bool =>
                  bif isZero then insert v T' else T').toMeasure)
            ∂p.toMeasure
        = ∫ T', (∫ iZ, f ((C + (G.volume t T' : ℝ)) +
                  (if iZ then (G.degree t v : ℝ) else 0))
                ∂(nextOpinionDist₂ G t s v).toMeasure)
            ∂p.toMeasure := by
      -- Pointwise equal on support; equal almost-everywhere w.r.t. `p`.
      rw [PMF.integral_eq_sum, PMF.integral_eq_sum]
      refine Finset.sum_congr rfl ?_
      intro T' _
      by_cases hT'_pos : p T' = 0
      · simp [hT'_pos]
      · have hT'_supp : T' ∈ p.support := (PMF.mem_support_iff _ _).mpr hT'_pos
        rw [hinner_eq T' hT'_supp]
    rw [hLHS]
    -- Step (d): apply per-vertex identity `integral_nextOpinionDist₂_eq_integral_XPMF`
    -- pointwise inside the outer p-integral, viewing the result as `f' (C + Vol T')`
    -- where `f' : ℝ → ℝ` is the "integrate-out-XPMF" shift of `f`.
    set f' : ℝ → ℝ := fun x =>
      ∫ z, f ((if v ∈ s then (G.degree t v : ℝ) else 0) + x + (z : ℝ))
        ∂(XPMF G t s v).toMeasure with hf'_def
    have hpervertex :
        ∀ T' : Finset V,
          ∫ iZ, f ((C + (G.volume t T' : ℝ)) +
                (if iZ then (G.degree t v : ℝ) else 0))
              ∂(nextOpinionDist₂ G t s v).toMeasure
          = f' (C + (G.volume t T' : ℝ)) :=
      fun T' => integral_nextOpinionDist₂_eq_integral_XPMF G t s v
        (C + (G.volume t T' : ℝ)) f
    simp_rw [hpervertex]
    -- Step (e): apply IH to the outer p-integral with function f' (same C, new f).
    rw [ih hnd' C f']
    -- Step (f): filter identity for cons.
    have hfilt_cons :
        (∑ u ∈ s.filter (· ∈ v :: vs), (G.degree t u : ℝ))
          = (if v ∈ s then (G.degree t v : ℝ) else 0)
              + (∑ u ∈ s.filter (· ∈ vs), (G.degree t u : ℝ)) := by
      by_cases hv : v ∈ s
      · have hv_notin_filt : v ∉ s.filter (· ∈ vs) := by
          simp [Finset.mem_filter, hv_notin_vs]
        have hfilt_eq : s.filter (· ∈ v :: vs) = insert v (s.filter (· ∈ vs)) := by
          ext u
          simp only [Finset.mem_filter, List.mem_cons, Finset.mem_insert]
          constructor
          · rintro ⟨hus, rfl | huvs⟩
            · exact Or.inl rfl
            · exact Or.inr ⟨hus, huvs⟩
          · rintro (rfl | ⟨hus, huvs⟩)
            · exact ⟨hv, Or.inl rfl⟩
            · exact ⟨hus, Or.inr huvs⟩
        rw [hfilt_eq, Finset.sum_insert hv_notin_filt, if_pos hv]
      · have hfilt_eq : s.filter (· ∈ v :: vs) = s.filter (· ∈ vs) := by
          ext u
          simp only [Finset.mem_filter, List.mem_cons]
          constructor
          · rintro ⟨hus, rfl | huvs⟩
            · exact absurd hus hv
            · exact ⟨hus, huvs⟩
          · rintro ⟨hus, huvs⟩
            exact ⟨hus, Or.inr huvs⟩
        rw [hfilt_eq, if_neg hv, zero_add]
    -- Step (g): unfold the RHS of the goal as a bind, then use the finite-support
    -- `pmf_integral_bind_intFamily` and change of variables on the inner `.map`.
    show _ = ∫ z, f (C + (∑ u ∈ s.filter (· ∈ v :: vs), (G.degree t u : ℝ))
              + (z : ℝ)) ∂(X_sum_pmf_list G t s (v :: vs)).toMeasure
    rw [show X_sum_pmf_list G t s (v :: vs) =
          (X_sum_pmf_list G t s vs).bind (fun z => (XPMF G t s v).map (· + z)) from rfl]
    -- Integrability of the integrand on each inner `.map` fiber: since XPMF has finite
    -- support and the integrand is bounded on it, finite-support integrability suffices.
    have hXPMF_fin : ∀ z_vs : ℤ,
        (((XPMF G t s v).map (· + z_vs)).support).Finite := by
      intro z_vs
      simp only [PMF.support_map]
      apply Set.Finite.image
      simp only [XPMF]
      split_ifs with hd hv
      · simp [PMF.support_pure]
      · simp only [twoPointPMF, PMF.support_map]
        exact Set.Finite.image _ (Set.toFinite _)
      · simp only [twoPointPMF, PMF.support_map]
        exact Set.Finite.image _ (Set.toFinite _)
    have hinner_int : ∀ z_vs : ℤ, Integrable
        (fun y : ℤ => f (C +
              (∑ u ∈ s.filter (· ∈ v :: vs), (G.degree t u : ℝ))
            + (y : ℝ)))
        ((XPMF G t s v).map (· + z_vs)).toMeasure := by
      intro z_vs
      rw [← PMF.restrict_toMeasure_support]
      exact IntegrableOn.of_finite (hXPMF_fin z_vs)
    rw [pmf_integral_bind_intFamily (X_sum_pmf_list G t s vs)
      (X_sum_pmf_list_support_finite G t s vs)
      (fun z_vs => (XPMF G t s v).map (· + z_vs))
      (fun y : ℤ => f (C +
            (∑ u ∈ s.filter (· ∈ v :: vs), (G.degree t u : ℝ))
          + (y : ℝ)))
      hinner_int]
    -- Inner `.map (·+z_vs)` integral: change of variables.
    have hmap_integral : ∀ z_vs : ℤ,
        ∫ y, f (C + (∑ u ∈ s.filter (· ∈ v :: vs), (G.degree t u : ℝ))
              + (y : ℝ)) ∂((XPMF G t s v).map (· + z_vs)).toMeasure
        = ∫ z, f (C + (∑ u ∈ s.filter (· ∈ v :: vs), (G.degree t u : ℝ))
              + ((z + z_vs : ℤ) : ℝ)) ∂(XPMF G t s v).toMeasure := by
      intro z_vs
      rw [← PMF.toMeasure_map _ _ (measurable_add_const z_vs),
        MeasureTheory.integral_map (measurable_add_const z_vs).aemeasurable
          Measurable.of_discrete.aestronglyMeasurable]
    simp_rw [hmap_integral]
    -- Goal: ∫ z_vs, f' (C + baseline(vs) + (z_vs : ℝ)) ∂X_sum_pmf_list(vs)
    --     = ∫ z_vs, ∫ z, f(C + baseline(v::vs) + (z + z_vs : ℤ)) ∂XPMF_v
    --         ∂X_sum_pmf_list(vs)
    -- Both sides are integrals over X_sum_pmf_list(vs); match integrands pointwise.
    refine MeasureTheory.integral_congr_ae (ae_of_all _ ?_)
    intro z_vs
    -- Unfold f' and match with baseline-cons identity.
    show f' (C + (∑ v' ∈ s.filter (· ∈ vs), (G.degree t v' : ℝ))
              + (z_vs : ℝ)) = _
    rw [hf'_def]
    -- Match arguments inside the integrals.
    refine MeasureTheory.integral_congr_ae (ae_of_all _ ?_)
    intro z
    rw [hfilt_cons]
    push_cast
    ring_nf

/-- Top-level pushforward: `∫ √Vol(A') ∂stepDist₂(s) = ∫ √(Vol(s) + z) ∂X_sum_pmf(s)`.

Specialization of `stepDist₂Aux_integral_eq_X_sum_pmf_list` with `L = Finset.univ.toList`,
`C = 0`, `f = Real.sqrt`. The volume identity `∑_{v ∈ s} d_v = Vol(s)` collapses the
RHS constant. Provides the clean pushforward used by `stepDist₂_majorized_by_Y_sum`. -/
private lemma stepDist₂_integral_sqrt_eq_X_sum_pmf
    (G : TemporalGraph V)
    (t : ℕ) (s : Finset V) :
    ∫ A', Real.sqrt (G.volume t A' : ℝ) ∂(stepDist₂ G t s).toMeasure
      = ∫ z, Real.sqrt (G.volume t s + z : ℝ)
          ∂(X_sum_pmf G t s).toMeasure := by
  -- Unfold stepDist₂ via stepDist₂Aux, X_sum_pmf via X_sum_pmf_list.
  rw [← stepDist₂Aux_eq_stepDist₂]
  show _ = ∫ z, Real.sqrt (G.volume t s + z : ℝ)
        ∂(X_sum_pmf_list G t s (Finset.univ : Finset V).toList).toMeasure
  -- Apply list helper with C = 0 and f = Real.sqrt.
  have hnd := Finset.nodup_toList (univ : Finset V)
  have hkey := stepDist₂Aux_integral_eq_X_sum_pmf_list G t s _ hnd 0 Real.sqrt
  -- Simplify the LHS (0 + x = x).
  simp only [zero_add] at hkey
  rw [hkey]
  -- RHS: match constants — `∑_{v ∈ s.filter (· ∈ univ.toList)} d_v = Vol(s)`.
  have hfilt : s.filter (· ∈ (Finset.univ : Finset V).toList) = s := by
    ext u; simp [Finset.mem_toList]
  rw [hfilt]
  -- Now goal: ∫ z, √(∑_{v∈s} d_v + z) = ∫ z, √(Vol(s) + z).
  -- The LHS uses `∑ v ∈ s, ↑(deg v) + (z : ℝ)`, RHS uses `↑(Vol s) + z`.
  -- By definition `Vol s = ∑ v ∈ s, deg v`, so the integrands agree up to a cast.
  refine MeasureTheory.integral_congr_ae (ae_of_all _ ?_)
  intro z
  have hvol : (∑ v ∈ s, (G.degree t v : ℝ))
      = (G.volume t s : ℝ) := by
    simp only [TemporalGraph.volume, SimpleGraph.volume, Nat.cast_sum]
  rw [hvol]

/-- Two-point concave swap: for a concave `f` on `[0, ∞)`, if `0 ≤ lam ≤ d` and `0 < d`,
then `(lam/(2d)) · f(c + d) + (1 - lam/(2d)) · f(c) ≤ (1/2) · f(c + lam) + (1/2) · f(c)`.

Proof sketch: slope-antitonicity on `[c, c + lam, c + d]`
(`ConcaveOn.slope_anti_adjacent`) gives
`lam · (f(c+d) - f(c+lam)) ≤ (d - lam) · (f(c+lam) - f(c))`, which rearranges to the claim
after multiplying both sides by `2d`. Edge cases `lam = 0` and `lam = d` are equalities. -/
private lemma concave_two_point_swap
    (f : ℝ → ℝ) (hf : ConcaveOn ℝ (Set.Ici (0 : ℝ)) f)
    (c d lam : ℝ) (hc : 0 ≤ c) (hd : 0 < d) (hlam0 : 0 ≤ lam) (hlamd : lam ≤ d) :
    (lam / (2 * d)) * f (c + d) + (1 - lam / (2 * d)) * f c
      ≤ (1 / 2) * f (c + lam) + (1 / 2) * f c := by
  rcases eq_or_lt_of_le hlam0 with hlam0_eq | hlam0_lt
  · -- lam = 0 case: both sides reduce to f(c).
    subst hlam0_eq
    have hzd : (0 : ℝ) / (2 * d) = 0 := by simp
    rw [hzd, zero_mul, zero_add, sub_zero, one_mul, add_zero]
    linarith
  · rcases eq_or_lt_of_le hlamd with hlamd_eq | hlamd_lt
    · -- lam = d case: both sides equal (1/2)·f(c+d) + (1/2)·f(c).
      rw [hlamd_eq]
      have hd_ne : (d : ℝ) ≠ 0 := ne_of_gt hd
      have hdd : d / (2 * d) = 1 / 2 := by field_simp
      rw [hdd]
      ring_nf
      exact le_refl _
    · -- 0 < lam < d strict: apply slope_anti_adjacent.
      have hcmem : c ∈ Set.Ici (0 : ℝ) := hc
      have hczd : c + d ∈ Set.Ici (0 : ℝ) := by
        simp [Set.mem_Ici]; linarith
      have hxy : c < c + lam := by linarith
      have hyz : c + lam < c + d := by linarith
      have hslope := hf.slope_anti_adjacent hcmem hczd hxy hyz
      -- slope_anti_adjacent: (f(c+d) - f(c+lam)) / ((c+d) - (c+lam))
      --                    ≤ (f(c+lam) - f c) / ((c+lam) - c)
      have hlam_pos : (0 : ℝ) < lam := hlam0_lt
      have hdlam_pos : (0 : ℝ) < d - lam := by linarith
      -- Clear denominators: lam · (f(c+d) - f(c+lam)) ≤ (d - lam) · (f(c+lam) - f c)
      have hkey : lam * (f (c + d) - f (c + lam))
          ≤ (d - lam) * (f (c + lam) - f c) := by
        have hz1 : (c + d) - (c + lam) = d - lam := by ring
        have hz2 : (c + lam) - c = lam := by ring
        rw [hz1, hz2] at hslope
        have := (div_le_div_iff₀ hdlam_pos hlam_pos).mp hslope
        linarith
      -- Rearrange: want (lam/(2d)) f(c+d) + (1 - lam/(2d)) f c
      --          ≤ (1/2) f(c+lam) + (1/2) f c
      -- Equivalently (×2d): lam f(c+d) + (2d - lam) f c ≤ d f(c+lam) + d f c
      -- Equivalently: lam f(c+d) + (d - lam) f c ≤ d f(c+lam)
      have hd_ne : (d : ℝ) ≠ 0 := ne_of_gt hd
      have h2d_pos : (0 : ℝ) < 2 * d := by linarith
      -- Derive: lam f(c+d) + (d - lam) f c ≤ d f(c+lam)
      have hkey2 : lam * f (c + d) + (d - lam) * f c ≤ d * f (c + lam) := by
        linarith [hkey]
      -- Divide both sides by 2d.
      have : (lam / (2 * d)) * f (c + d) + (1 - lam / (2 * d)) * f c
          - ((1 / 2) * f (c + lam) + (1 / 2) * f c)
          = (lam * f (c + d) + (d - lam) * f c - d * f (c + lam)) / (2 * d) := by
        field_simp
        ring
      linarith [div_nonpos_of_nonpos_of_nonneg (by linarith : lam * f (c + d)
        + (d - lam) * f c - d * f (c + lam) ≤ 0) h2d_pos.le,
        (show (lam / (2 * d)) * f (c + d) + (1 - lam / (2 * d)) * f c
            - ((1 / 2) * f (c + lam) + (1 / 2) * f c)
            = (lam * f (c + d) + (d - lam) * f c - d * f (c + lam)) / (2 * d) from this)]

/-- Elements in the support of `X_sum_pmf_list G t s l` are `≥ -(∑ v ∈ s.filter(· ∈ l), d_v)`.
Mirror of `Y_sum_pmf_list_support_lb`; both use `XPMF`/`YPMF` equal on the minority branch. -/
private lemma X_sum_pmf_list_support_lb (G : TemporalGraph V) (t : ℕ) (s : Finset V)
    (l : List V) (hnodup : l.Nodup) :
    ∀ z ∈ (X_sum_pmf_list G t s l).support,
      -(∑ v ∈ s.filter (· ∈ l), (G.degree t v : ℤ)) ≤ z := by
  induction l with
  | nil =>
    intro z hz
    simp [X_sum_pmf_list, PMF.support_pure] at hz
    subst hz; simp
  | cons v vs ih =>
    rw [List.nodup_cons] at hnodup
    obtain ⟨hv_notin, hnodup_vs⟩ := hnodup
    intro z hz
    simp only [X_sum_pmf_list, PMF.support_bind, PMF.support_map, Set.mem_iUnion,
      Set.mem_image] at hz
    obtain ⟨w, hw, y, hy, hyz⟩ := hz
    rw [← hyz]
    have ihw := ih hnodup_vs w hw
    -- XPMF support: on minority, ⊆ {0, -d_v}; on majority (d ≠ 0), ⊆ {0, +d_v}.
    have hXPMF_lb : -(G.degree t v : ℤ) ≤ y := by
      have : y ∈ (XPMF G t s v).support := hy
      unfold XPMF at this
      by_cases hd : G.degree t v = 0
      · rw [dif_pos hd] at this
        simp only [PMF.support_pure, Set.mem_singleton_iff] at this
        subst this; simp [hd]
      · rw [dif_neg hd] at this
        by_cases hvs : v ∈ s
        · rw [if_pos hvs] at this
          simp only [twoPointPMF, PMF.support_map, Set.mem_image] at this
          obtain ⟨b, _, hby⟩ := this
          cases b
          · simp only [cond_false] at hby; subst hby
            exact neg_nonpos.mpr (Int.natCast_nonneg _)
          · simp only [cond_true] at hby; subst hby; exact le_refl _
        · rw [if_neg hvs] at this
          simp only [twoPointPMF, PMF.support_map, Set.mem_image] at this
          obtain ⟨b, _, hby⟩ := this
          cases b
          · simp only [cond_false] at hby; subst hby
            exact neg_nonpos.mpr (Int.natCast_nonneg _)
          · simp only [cond_true] at hby; subst hby
            exact le_trans (neg_nonpos.mpr (Int.natCast_nonneg _)) (Int.natCast_nonneg _)
    by_cases hv : v ∈ s
    · have hv_notin_filt : v ∉ s.filter (· ∈ vs) := by
        simp [Finset.mem_filter, hv_notin]
      have hfilt_eq : s.filter (· ∈ v :: vs) = insert v (s.filter (· ∈ vs)) := by
        ext u
        simp only [Finset.mem_filter, List.mem_cons, Finset.mem_insert]
        constructor
        · rintro ⟨hus, rfl | huvs⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨hus, huvs⟩
        · rintro (rfl | ⟨hus, huvs⟩)
          · exact ⟨hv, Or.inl rfl⟩
          · exact ⟨hus, Or.inr huvs⟩
      rw [hfilt_eq, Finset.sum_insert hv_notin_filt]
      linarith
    · -- v ∉ s: y ≥ 0 since XPMF on majority outputs 0 or +d_v.
      have hfilt_eq : s.filter (· ∈ v :: vs) = s.filter (· ∈ vs) := by
        ext u
        simp only [Finset.mem_filter, List.mem_cons]
        constructor
        · rintro ⟨hus, rfl | huvs⟩
          · exact absurd hus hv
          · exact ⟨hus, huvs⟩
        · rintro ⟨hus, huvs⟩
          exact ⟨hus, Or.inr huvs⟩
      rw [hfilt_eq]
      have hy_nn : (0 : ℤ) ≤ y := by
        have : y ∈ (XPMF G t s v).support := hy
        unfold XPMF at this
        by_cases hd : G.degree t v = 0
        · rw [dif_pos hd] at this
          simp only [PMF.support_pure, Set.mem_singleton_iff] at this
          subst this; exact le_refl _
        · rw [dif_neg hd] at this
          rw [if_neg hv] at this
          simp only [twoPointPMF, PMF.support_map, Set.mem_image] at this
          obtain ⟨b, _, hby⟩ := this
          cases b
          · simp only [cond_false] at hby; subst hby; exact le_refl _
          · simp only [cond_true] at hby; subst hby; exact Int.natCast_nonneg _
      linarith

/-- Per-vertex inner-integral inequality: with `c = Vol(s) + z_vs + ∑_{w∈s.filter(· ∈ vs)} d_w ≥ 0`,
`∫ y, √(c + y) ∂XPMF_v ≤ ∫ y, √(c + y) ∂YPMF_v`.

Cases: `v ∈ s` (minority) — XPMF = YPMF, equality.
`v ∉ s`, `d_v = 0` — both `pure 0`, equal.
`v ∉ s`, `d_v ≠ 0` — apply `concave_two_point_swap` with `lam = lambdaCut ≤ d_v`. -/
private lemma XPMF_le_YPMF_inner_integral_sqrt
    (G : TemporalGraph V) (t : ℕ) (s : Finset V) (v : V) (c : ℝ) (hc : 0 ≤ c) :
    ∫ y, Real.sqrt (c + (y : ℝ)) ∂(XPMF G t s v).toMeasure
      ≤ ∫ y, Real.sqrt (c + (y : ℝ)) ∂(YPMF G t s v).toMeasure := by
  -- Case split on v ∈ s: XPMF and YPMF coincide.
  by_cases hv : v ∈ s
  · -- Minority branch: XPMF = YPMF.
    have heq : XPMF G t s v = YPMF G t s v := by
      unfold XPMF YPMF
      split_ifs with hd <;> rfl
    rw [heq]
  · -- Majority branch.
    by_cases hd : G.degree t v = 0
    · -- Degree 0: both are PMF.pure 0.
      have heq : XPMF G t s v = YPMF G t s v := by
        unfold XPMF YPMF
        rw [dif_pos hd, dif_pos hd]
      rw [heq]
    · -- Nontrivial majority: XPMF = twoPointPMF λ/(2d) at +d; YPMF = twoPointPMF 1/2 at λ.
      -- Compute both integrals using integral_twoPointPMF_real.
      have hd' : (0 : ℝ) < (G.degree t v : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hd
      have hlam_le : lambdaCut G t s v ≤ G.degree t v :=
        lambdaCut_le_degree G t s v
      have hlam_le_R : (lambdaCut G t s v : ℝ) ≤ (G.degree t v : ℝ) := by
        exact_mod_cast hlam_le
      have hlam_nn_R : (0 : ℝ) ≤ (lambdaCut G t s v : ℝ) := by exact_mod_cast Nat.zero_le _
      -- Set g := fun x ↦ √(c + x) and apply integral_twoPointPMF_real.
      set g : ℝ → ℝ := fun x => Real.sqrt (c + x) with hg_def
      have hLHS : ∫ y, Real.sqrt (c + (y : ℝ)) ∂(XPMF G t s v).toMeasure =
          (lambdaCut G t s v : ℝ) / (2 * G.degree t v)
              * Real.sqrt (c + (G.degree t v : ℝ))
            + (1 - (lambdaCut G t s v : ℝ) / (2 * G.degree t v))
              * Real.sqrt (c + 0) := by
        show ∫ y, g (y : ℝ) ∂(XPMF G t s v).toMeasure = _
        simp only [XPMF, dif_neg hd, if_neg hv]
        rw [integral_twoPointPMF_real]
        have hlamCoe : (lambdaCutNNP G t s v hd : ℝ) =
            (lambdaCut G t s v : ℝ) / (2 * G.degree t v) := by
          unfold lambdaCutNNP; rfl
        rw [hlamCoe]
        simp [hg_def, Int.cast_natCast]
      have hRHS : ∫ y, Real.sqrt (c + (y : ℝ)) ∂(YPMF G t s v).toMeasure =
          (1 / 2 : ℝ) * Real.sqrt (c + (lambdaCut G t s v : ℝ))
            + (1 - (1 / 2 : ℝ)) * Real.sqrt (c + 0) := by
        show ∫ y, g (y : ℝ) ∂(YPMF G t s v).toMeasure = _
        simp only [YPMF, dif_neg hd, if_neg hv]
        rw [integral_twoPointPMF_real]
        simp [hg_def, Int.cast_natCast]
      rw [hLHS, hRHS]
      -- Apply concave_two_point_swap with f = √, d = d_v, lam = λ_v.
      have hconc : ConcaveOn ℝ (Set.Ici (0 : ℝ)) Real.sqrt :=
        StrictConcaveOn.concaveOn Real.strictConcaveOn_sqrt
      have hkey := concave_two_point_swap Real.sqrt hconc c
        (G.degree t v : ℝ) (lambdaCut G t s v : ℝ)
        hc hd' hlam_nn_R hlam_le_R
      -- hkey: (λ/(2d)) √(c+d) + (1 - λ/(2d)) √c ≤ (1/2) √(c+λ) + (1/2) √c
      -- Match via √(c+0) = √c.
      have h0 : Real.sqrt (c + 0) = Real.sqrt c := by rw [add_zero]
      rw [h0]
      linarith [hkey]

/-- Generalized list-level majorization with parametric shift `A`.

For any nodup list `L`, any `A ≥ ∑_{v ∈ s.filter(· ∈ L)} d_v`:
`∫ z, √(A + z) ∂X_sum_pmf_list L ≤ ∫ z, √(A + z) ∂Y_sum_pmf_list L`.

Proof by induction on `L`:
- `nil`: both sides equal `√A`.
- `cons v vs`: expand binds via `pmf_integral_bind_intFamily`, apply the pointwise
  `XPMF_le_YPMF_inner_integral_sqrt` swap on `X_sum_pmf_list vs` support (using the
  support lower bound to guarantee `A + z_vs + y ≥ 0`), then apply IH to majorize
  the outer `X_sum_pmf_list vs` → `Y_sum_pmf_list vs` using integrand
  `λ x. ∫ y, √(x + y) ∂YPMF_v`, which is a nonnegative linear combination of
  concave-sqrt shifts valid on the effective support range. -/
private lemma X_sum_pmf_list_majorized_by_Y_sum_pmf_list_aux
    (G : TemporalGraph V) (t : ℕ) (s : Finset V) :
    ∀ (L : List V), L.Nodup → ∀ (A : ℝ),
      (∑ v ∈ s.filter (· ∈ L), (G.degree t v : ℝ)) ≤ A →
      ∫ z, Real.sqrt (A + z) ∂(X_sum_pmf_list G t s L).toMeasure
        ≤ ∫ z, Real.sqrt (A + z) ∂(Y_sum_pmf_list G t s L).toMeasure := by
  intro L hnd
  induction L with
  | nil =>
    intro A _
    simp [X_sum_pmf_list, Y_sum_pmf_list, PMF.toMeasure_pure, integral_dirac]
  | cons v vs ih =>
    have hnd_cons := List.nodup_cons.mp hnd
    have hv_notin : v ∉ vs := hnd_cons.1
    have hnd_vs : vs.Nodup := hnd_cons.2
    intro A hA
    -- A ≥ ∑_{v ∈ s.filter(·∈vs)} d_v and (if v ∈ s) A ≥ ∑ + d_v.
    have hA_vs : (∑ v ∈ s.filter (· ∈ vs), (G.degree t v : ℝ)) ≤ A := by
      -- s.filter(· ∈ vs) ⊆ s.filter(· ∈ v :: vs).
      have hsub : s.filter (· ∈ vs) ⊆ s.filter (· ∈ v :: vs) := by
        intro u hu
        simp only [Finset.mem_filter, List.mem_cons] at hu ⊢
        exact ⟨hu.1, Or.inr hu.2⟩
      have hsum_le :
          (∑ u ∈ s.filter (· ∈ vs), (G.degree t u : ℝ))
            ≤ ∑ u ∈ s.filter (· ∈ v :: vs), (G.degree t u : ℝ) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
        intro u _ _; exact_mod_cast Nat.zero_le _
      linarith
    -- Abbreviations.
    set g : ℝ → ℝ := fun z => Real.sqrt (A + z) with hg_def
    set gvs : ℝ → ℝ := fun z => Real.sqrt (A + z) with hgvs_def
    -- Finiteness.
    have hX_fin : (X_sum_pmf_list G t s vs).support.Finite :=
      X_sum_pmf_list_support_finite G t s vs
    have hY_fin : (Y_sum_pmf_list G t s vs).support.Finite :=
      Y_sum_pmf_list_support_finite G t s vs
    -- Integrability of inner integrands.
    have hX_inner_int : ∀ z_vs : ℤ,
        Integrable (fun y : ℤ => g ((y : ℝ)))
          ((XPMF G t s v).map (· + z_vs)).toMeasure := by
      intro z_vs
      rw [← PMF.restrict_toMeasure_support]
      exact IntegrableOn.of_finite (by
        simp only [PMF.support_map]
        exact Set.Finite.image _ (by
          simp only [XPMF]; split_ifs with hd hvs
          · simp [PMF.support_pure]
          · simp only [twoPointPMF, PMF.support_map]
            exact Set.Finite.image _ (Set.toFinite _)
          · simp only [twoPointPMF, PMF.support_map]
            exact Set.Finite.image _ (Set.toFinite _)))
    have hY_inner_int : ∀ z_vs : ℤ,
        Integrable (fun y : ℤ => g ((y : ℝ)))
          ((YPMF G t s v).map (· + z_vs)).toMeasure := by
      intro z_vs
      rw [← PMF.restrict_toMeasure_support]
      exact IntegrableOn.of_finite (by
        simp only [PMF.support_map]
        exact Set.Finite.image _ (by
          simp only [YPMF]; split_ifs with hd hvs
          · simp [PMF.support_pure]
          · simp only [twoPointPMF, PMF.support_map]
            exact Set.Finite.image _ (Set.toFinite _)
          · simp only [twoPointPMF, PMF.support_map]
            exact Set.Finite.image _ (Set.toFinite _)))
    -- Expand via bind.
    have hLHS_expand :
        ∫ z, g z ∂(X_sum_pmf_list G t s (v :: vs)).toMeasure
          = ∫ z_vs, (∫ y, g ((y : ℝ))
              ∂((XPMF G t s v).map (· + z_vs)).toMeasure)
              ∂(X_sum_pmf_list G t s vs).toMeasure := by
      show ∫ z, g z ∂((X_sum_pmf_list G t s vs).bind
          (fun z_vs => (XPMF G t s v).map (· + z_vs))).toMeasure = _
      rw [pmf_integral_bind_intFamily (X_sum_pmf_list G t s vs) hX_fin
        (fun z_vs => (XPMF G t s v).map (· + z_vs))
        (fun z : ℤ => g (z : ℝ)) hX_inner_int]
    have hRHS_expand :
        ∫ z, g z ∂(Y_sum_pmf_list G t s (v :: vs)).toMeasure
          = ∫ z_vs, (∫ y, g ((y : ℝ))
              ∂((YPMF G t s v).map (· + z_vs)).toMeasure)
              ∂(Y_sum_pmf_list G t s vs).toMeasure := by
      show ∫ z, g z ∂((Y_sum_pmf_list G t s vs).bind
          (fun z_vs => (YPMF G t s v).map (· + z_vs))).toMeasure = _
      rw [pmf_integral_bind_intFamily (Y_sum_pmf_list G t s vs) hY_fin
        (fun z_vs => (YPMF G t s v).map (· + z_vs))
        (fun z : ℤ => g (z : ℝ)) hY_inner_int]
    -- Change of variables on map-shift.
    have hmap_X : ∀ z_vs : ℤ,
        ∫ y, g ((y : ℝ)) ∂((XPMF G t s v).map (· + z_vs)).toMeasure
          = ∫ y, g (((y + z_vs : ℤ) : ℝ)) ∂(XPMF G t s v).toMeasure := by
      intro z_vs
      rw [← PMF.toMeasure_map _ _ (measurable_add_const z_vs),
        MeasureTheory.integral_map (measurable_add_const z_vs).aemeasurable
          Measurable.of_discrete.aestronglyMeasurable]
    have hmap_Y : ∀ z_vs : ℤ,
        ∫ y, g ((y : ℝ)) ∂((YPMF G t s v).map (· + z_vs)).toMeasure
          = ∫ y, g (((y + z_vs : ℤ) : ℝ)) ∂(YPMF G t s v).toMeasure := by
      intro z_vs
      rw [← PMF.toMeasure_map _ _ (measurable_add_const z_vs),
        MeasureTheory.integral_map (measurable_add_const z_vs).aemeasurable
          Measurable.of_discrete.aestronglyMeasurable]
    rw [hLHS_expand, hRHS_expand]
    simp_rw [hmap_X, hmap_Y]
    -- Reshape inner integrals: ∫ y, g((y+z_vs:ℤ):ℝ) ∂PMF = ∫ y, √((A+z_vs) + y) ∂PMF.
    set FX : ℤ → ℝ := fun z_vs =>
      ∫ y, Real.sqrt ((A + (z_vs : ℝ)) + (y : ℝ)) ∂(XPMF G t s v).toMeasure with hFX_def
    set FY : ℤ → ℝ := fun z_vs =>
      ∫ y, Real.sqrt ((A + (z_vs : ℝ)) + (y : ℝ)) ∂(YPMF G t s v).toMeasure with hFY_def
    have hLHS_as_FX :
        ∫ z_vs, (∫ y, g (((y + z_vs : ℤ) : ℝ)) ∂(XPMF G t s v).toMeasure)
            ∂(X_sum_pmf_list G t s vs).toMeasure
          = ∫ z_vs, FX z_vs ∂(X_sum_pmf_list G t s vs).toMeasure := by
      refine MeasureTheory.integral_congr_ae (ae_of_all _ ?_)
      intro z_vs
      simp only [hFX_def]
      refine MeasureTheory.integral_congr_ae (ae_of_all _ ?_)
      intro y
      simp only [hg_def, hgvs_def]
      push_cast
      congr 1; ring
    have hRHS_as_FY :
        ∫ z_vs, (∫ y, g (((y + z_vs : ℤ) : ℝ)) ∂(YPMF G t s v).toMeasure)
            ∂(Y_sum_pmf_list G t s vs).toMeasure
          = ∫ z_vs, FY z_vs ∂(Y_sum_pmf_list G t s vs).toMeasure := by
      refine MeasureTheory.integral_congr_ae (ae_of_all _ ?_)
      intro z_vs
      simp only [hFY_def]
      refine MeasureTheory.integral_congr_ae (ae_of_all _ ?_)
      intro y
      simp only [hg_def, hgvs_def]
      push_cast
      congr 1; ring
    rw [hLHS_as_FX, hRHS_as_FY]
    -- Step (a): pointwise swap FX ≤ FY on X_sum_pmf_list vs support.
    -- For z_vs in support: A + z_vs ≥ A - ∑_{s.filter(·∈vs)} d_w ≥ 0 (if v ∈ s; when v ∉ s,
    -- equivalently s.filter(·∈v::vs) = s.filter(·∈vs)).
    have hX_support_swap : ∀ z_vs ∈ (X_sum_pmf_list G t s vs).support,
        FX z_vs ≤ FY z_vs := by
      intro z_vs hz_vs
      have hlb := X_sum_pmf_list_support_lb G t s vs hnd_vs z_vs hz_vs
      -- Convert to ℝ: z_vs ≥ -(∑ w ∈ s.filter(·∈vs), d_w : ℝ).
      have hlb_R : -(∑ w ∈ s.filter (· ∈ vs), (G.degree t w : ℝ))
          ≤ (z_vs : ℝ) := by
        have : (-(∑ w ∈ s.filter (· ∈ vs), (G.degree t w : ℤ)) : ℝ)
            ≤ (z_vs : ℝ) := by exact_mod_cast hlb
        push_cast at this; linarith
      have hAz : (0 : ℝ) ≤ A + (z_vs : ℝ) := by linarith [hA_vs]
      exact XPMF_le_YPMF_inner_integral_sqrt G t s v (A + (z_vs : ℝ)) hAz
    -- Integrability of FX, FY over both PMFs (finite support).
    have hFX_int_X : Integrable FX (X_sum_pmf_list G t s vs).toMeasure := by
      rw [← PMF.restrict_toMeasure_support]; exact IntegrableOn.of_finite hX_fin
    have hFY_int_X : Integrable FY (X_sum_pmf_list G t s vs).toMeasure := by
      rw [← PMF.restrict_toMeasure_support]; exact IntegrableOn.of_finite hX_fin
    have hFY_int_Y : Integrable FY (Y_sum_pmf_list G t s vs).toMeasure := by
      rw [← PMF.restrict_toMeasure_support]; exact IntegrableOn.of_finite hY_fin
    have hFX_le_FY_ae : ∀ᵐ z_vs ∂(X_sum_pmf_list G t s vs).toMeasure, FX z_vs ≤ FY z_vs := by
      rw [← PMF.restrict_toMeasure_support]
      exact MeasureTheory.ae_restrict_of_forall_mem hX_fin.measurableSet hX_support_swap
    have hstep_a :
        ∫ z_vs, FX z_vs ∂(X_sum_pmf_list G t s vs).toMeasure
          ≤ ∫ z_vs, FY z_vs ∂(X_sum_pmf_list G t s vs).toMeasure :=
      MeasureTheory.integral_mono_ae hFX_int_X hFY_int_X hFX_le_FY_ae
    -- Step (b): apply IH to compare ∫ FY ∂X_list vs vs ∫ FY ∂Y_list vs.
    -- FY z_vs = ∫ y, √((A + z_vs) + y) ∂YPMF_v
    --         = (in majority, d_v ≠ 0) (1/2)√(A + z_vs + λ_v) + (1/2)√(A + z_vs)
    --         (in minority, d_v ≠ 0) (λ/(2d))·√(A + z_vs - d_v) + (1 - λ/(2d))·√(A + z_vs)
    --         (in degree-0 case)    √(A + z_vs).
    -- In ALL cases, FY z_vs = a_0·√(A + z_vs + c_0) + a_1·√(A + z_vs + c_1) for some
    -- a_0, a_1 ≥ 0 and shifts c_0, c_1 ∈ {0, λ_v, -d_v}.
    -- For z_vs in X_list(vs) support, we have A + z_vs + c_i ≥ 0 provided
    -- A ≥ ∑_{s.filter(·∈vs)} d_w + (-c_i). Worst case (v ∈ s minority): c_i = -d_v, needs
    -- A ≥ ∑_{s.filter(·∈vs)} d_w + d_v = ∑_{s.filter(·∈v::vs)} d_w. Given by hA.
    -- Then FY = a_0·g_0 + a_1·g_1 with g_i(z) := √(A + z + c_i), and each g_i satisfies
    -- the form √(A + c_i + z) with shift A_i = A + c_i. IH on vs with A_i applies each
    -- case iff A_i ≥ ∑_{s.filter(·∈vs)} d_w; in worst minority case, A_i = A - d_v
    -- and we need A - d_v ≥ ∑_{s.filter(·∈vs)} d_w, which holds since A ≥ ∑_{s.filter(·∈v::vs)}
    -- d_w = d_v + ∑_{s.filter(·∈vs)} d_w (when v ∈ s, v ∉ vs).
    -- Case on v ∈ s and d_v = 0 to unfold YPMF.
    by_cases hd : G.degree t v = 0
    · -- Degree-0 case: YPMF = PMF.pure 0, so FY z_vs = √(A + z_vs).
      have hFY_simple : ∀ z_vs : ℤ, FY z_vs = Real.sqrt (A + (z_vs : ℝ)) := by
        intro z_vs
        simp only [hFY_def, YPMF, dif_pos hd, PMF.toMeasure_pure, integral_dirac,
          Int.cast_zero, add_zero]
      -- Goal: ∫ FY ∂X_list vs ≤ ∫ FY ∂Y_list vs.
      -- After unfolding, = ∫ √(A + z_vs) ∂X_list vs and ≤ by IH with same A.
      have hIH := ih hnd_vs A hA_vs
      calc ∫ z_vs, FX z_vs ∂(X_sum_pmf_list G t s vs).toMeasure
          ≤ ∫ z_vs, FY z_vs ∂(X_sum_pmf_list G t s vs).toMeasure := hstep_a
        _ = ∫ z_vs, Real.sqrt (A + (z_vs : ℝ)) ∂(X_sum_pmf_list G t s vs).toMeasure := by
              apply MeasureTheory.integral_congr_ae
              exact ae_of_all _ (fun z_vs => hFY_simple z_vs)
        _ ≤ ∫ z_vs, Real.sqrt (A + (z_vs : ℝ)) ∂(Y_sum_pmf_list G t s vs).toMeasure := hIH
        _ = ∫ z_vs, FY z_vs ∂(Y_sum_pmf_list G t s vs).toMeasure := by
              apply MeasureTheory.integral_congr_ae
              exact ae_of_all _ (fun z_vs => (hFY_simple z_vs).symm)
    · -- d_v ≠ 0.
      by_cases hv : v ∈ s
      · -- Minority: YPMF = twoPointPMF (λ/(2d)) at -d_v.
        -- FY z_vs = (λ/(2d)) √(A + z_vs - d_v) + (1 - λ/(2d)) √(A + z_vs).
        have hlam_le_d : (lambdaCut G t s v : ℝ) ≤ (G.degree t v : ℝ) := by
          exact_mod_cast lambdaCut_le_degree G t s v
        have hlam_nn : (0 : ℝ) ≤ (lambdaCut G t s v : ℝ) := by exact_mod_cast Nat.zero_le _
        have hd_pos : (0 : ℝ) < (G.degree t v : ℝ) := by
          exact_mod_cast Nat.pos_of_ne_zero hd
        -- Coefficient factor.
        set p : ℝ := (lambdaCut G t s v : ℝ) / (2 * G.degree t v) with hp_def
        have hp_nn : 0 ≤ p := by simp [hp_def]; positivity
        have hp_le : p ≤ 1 := by
          simp [hp_def]
          rw [div_le_one (by linarith)]; linarith
        have h1_p_nn : 0 ≤ 1 - p := by linarith
        have hFY_minority : ∀ z_vs : ℤ,
            FY z_vs = p * Real.sqrt ((A + (z_vs : ℝ)) + (-(G.degree t v : ℝ)))
              + (1 - p) * Real.sqrt ((A + (z_vs : ℝ)) + 0) := by
          intro z_vs
          simp only [hFY_def, YPMF, dif_neg hd, if_pos hv]
          set gy : ℝ → ℝ := fun x => Real.sqrt (A + (z_vs : ℝ) + x) with hgy_def
          show ∫ y, gy (y : ℝ)
              ∂(twoPointPMF (lambdaCutNNP G t s v hd) _ (-(G.degree t v : ℤ))).toMeasure
              = _
          rw [integral_twoPointPMF_real]
          have hlamCoe : (lambdaCutNNP G t s v hd : ℝ) =
              (lambdaCut G t s v : ℝ) / (2 * G.degree t v) := by
            unfold lambdaCutNNP; rfl
          simp only [hgy_def, hlamCoe, Int.cast_neg, Int.cast_natCast, hp_def]
        -- Apply IH twice with shifted A.
        -- For the d_v-shift: A' = A - d_v, need A' ≥ ∑_{s.filter(·∈vs)} d_w.
        -- Since v ∈ s, v ∉ vs: s.filter(·∈v::vs) = insert v (s.filter(·∈vs)) (disjoint).
        have hv_notin_filt : v ∉ s.filter (· ∈ vs) := by
          simp [Finset.mem_filter, hv_notin]
        have hfilt_cons : s.filter (· ∈ v :: vs) = insert v (s.filter (· ∈ vs)) := by
          ext u
          simp only [Finset.mem_filter, List.mem_cons, Finset.mem_insert]
          constructor
          · rintro ⟨hus, rfl | huvs⟩
            · exact Or.inl rfl
            · exact Or.inr ⟨hus, huvs⟩
          · rintro (rfl | ⟨hus, huvs⟩)
            · exact ⟨hv, Or.inl rfl⟩
            · exact ⟨hus, Or.inr huvs⟩
        have hA_minus_d : (∑ w ∈ s.filter (· ∈ vs), (G.degree t w : ℝ))
            ≤ A - (G.degree t v : ℝ) := by
          have hcons_sum : (∑ w ∈ s.filter (· ∈ v :: vs), (G.degree t w : ℝ))
              = (G.degree t v : ℝ)
                + ∑ w ∈ s.filter (· ∈ vs), (G.degree t w : ℝ) := by
            rw [hfilt_cons, Finset.sum_insert hv_notin_filt]
          linarith
        -- IH with A' := A - d_v, giving ∫ √(A' + ·) ∂X_list vs ≤ ∫ √(A' + ·) ∂Y_list vs.
        have hIH_minus : ∫ z_vs, Real.sqrt ((A - (G.degree t v : ℝ))
              + (z_vs : ℝ)) ∂(X_sum_pmf_list G t s vs).toMeasure
            ≤ ∫ z_vs, Real.sqrt ((A - (G.degree t v : ℝ))
              + (z_vs : ℝ)) ∂(Y_sum_pmf_list G t s vs).toMeasure :=
          ih hnd_vs (A - (G.degree t v : ℝ)) hA_minus_d
        have hIH_0 : ∫ z_vs, Real.sqrt (A + (z_vs : ℝ))
              ∂(X_sum_pmf_list G t s vs).toMeasure
            ≤ ∫ z_vs, Real.sqrt (A + (z_vs : ℝ))
              ∂(Y_sum_pmf_list G t s vs).toMeasure :=
          ih hnd_vs A hA_vs
        -- Reshape FY via linearity of integral into p·A_-d + (1-p)·A.
        -- Integrability helpers for the pieces.
        have hpart_int_X : ∀ (B : ℝ), Integrable (fun z_vs : ℤ => Real.sqrt (B + (z_vs : ℝ)))
            (X_sum_pmf_list G t s vs).toMeasure := by
          intro B
          rw [← PMF.restrict_toMeasure_support]; exact IntegrableOn.of_finite hX_fin
        have hpart_int_Y : ∀ (B : ℝ), Integrable (fun z_vs : ℤ => Real.sqrt (B + (z_vs : ℝ)))
            (Y_sum_pmf_list G t s vs).toMeasure := by
          intro B
          rw [← PMF.restrict_toMeasure_support]; exact IntegrableOn.of_finite hY_fin
        -- Compute ∫ FY and split.
        have hFY_int_eq_X :
            ∫ z_vs, FY z_vs ∂(X_sum_pmf_list G t s vs).toMeasure
              = p * ∫ z_vs, Real.sqrt ((A - (G.degree t v : ℝ))
                  + (z_vs : ℝ)) ∂(X_sum_pmf_list G t s vs).toMeasure
                + (1 - p) * ∫ z_vs, Real.sqrt (A + (z_vs : ℝ))
                  ∂(X_sum_pmf_list G t s vs).toMeasure := by
          rw [show (fun z_vs : ℤ => FY z_vs) = fun z_vs : ℤ =>
              p * Real.sqrt ((A - (G.degree t v : ℝ)) + (z_vs : ℝ))
                + (1 - p) * Real.sqrt (A + (z_vs : ℝ))
              from by
                ext z_vs
                rw [hFY_minority z_vs]
                congr 2
                · ring_nf
                · ring_nf]
          rw [integral_add ((hpart_int_X _).const_mul p)
                ((hpart_int_X _).const_mul (1 - p)),
            integral_const_mul, integral_const_mul]
        have hFY_int_eq_Y :
            ∫ z_vs, FY z_vs ∂(Y_sum_pmf_list G t s vs).toMeasure
              = p * ∫ z_vs, Real.sqrt ((A - (G.degree t v : ℝ))
                  + (z_vs : ℝ)) ∂(Y_sum_pmf_list G t s vs).toMeasure
                + (1 - p) * ∫ z_vs, Real.sqrt (A + (z_vs : ℝ))
                  ∂(Y_sum_pmf_list G t s vs).toMeasure := by
          rw [show (fun z_vs : ℤ => FY z_vs) = fun z_vs : ℤ =>
              p * Real.sqrt ((A - (G.degree t v : ℝ)) + (z_vs : ℝ))
                + (1 - p) * Real.sqrt (A + (z_vs : ℝ))
              from by
                ext z_vs
                rw [hFY_minority z_vs]
                congr 2
                · ring_nf
                · ring_nf]
          rw [integral_add ((hpart_int_Y _).const_mul p)
                ((hpart_int_Y _).const_mul (1 - p)),
            integral_const_mul, integral_const_mul]
        calc ∫ z_vs, FX z_vs ∂(X_sum_pmf_list G t s vs).toMeasure
            ≤ ∫ z_vs, FY z_vs ∂(X_sum_pmf_list G t s vs).toMeasure := hstep_a
          _ = p * ∫ z_vs, Real.sqrt ((A - (G.degree t v : ℝ))
                  + (z_vs : ℝ)) ∂(X_sum_pmf_list G t s vs).toMeasure
                + (1 - p) * ∫ z_vs, Real.sqrt (A + (z_vs : ℝ))
                  ∂(X_sum_pmf_list G t s vs).toMeasure := hFY_int_eq_X
          _ ≤ p * ∫ z_vs, Real.sqrt ((A - (G.degree t v : ℝ))
                  + (z_vs : ℝ)) ∂(Y_sum_pmf_list G t s vs).toMeasure
                + (1 - p) * ∫ z_vs, Real.sqrt (A + (z_vs : ℝ))
                  ∂(Y_sum_pmf_list G t s vs).toMeasure := by
                    gcongr
          _ = ∫ z_vs, FY z_vs ∂(Y_sum_pmf_list G t s vs).toMeasure := hFY_int_eq_Y.symm
      · -- Majority, d_v ≠ 0: YPMF = twoPointPMF (1/2) at λ_v.
        -- FY z_vs = (1/2) √(A + z_vs + λ_v) + (1/2) √(A + z_vs).
        have hlam_nn : (0 : ℝ) ≤ (lambdaCut G t s v : ℝ) := by exact_mod_cast Nat.zero_le _
        have hFY_majority : ∀ z_vs : ℤ,
            FY z_vs = (1/2 : ℝ) * Real.sqrt ((A + (z_vs : ℝ)) + (lambdaCut G t s v : ℝ))
              + (1 - (1/2 : ℝ)) * Real.sqrt ((A + (z_vs : ℝ)) + 0) := by
          intro z_vs
          simp only [hFY_def, YPMF, dif_neg hd, if_neg hv]
          set gy : ℝ → ℝ := fun x => Real.sqrt (A + (z_vs : ℝ) + x) with hgy_def
          show ∫ y, gy (y : ℝ)
              ∂(twoPointPMF (1/2) (by norm_num)
                  ((lambdaCut G t s v : ℤ))).toMeasure = _
          rw [integral_twoPointPMF_real]
          simp only [hgy_def, Int.cast_natCast]
          push_cast
          ring
        -- Apply IH twice: shift 0 (same A), shift λ_v (A' = A + λ_v ≥ A ≥ ...).
        have hA_plus_lam : (∑ w ∈ s.filter (· ∈ vs), (G.degree t w : ℝ))
            ≤ A + (lambdaCut G t s v : ℝ) := by linarith
        have hIH_plus : ∫ z_vs, Real.sqrt ((A + (lambdaCut G t s v : ℝ)) + (z_vs : ℝ))
              ∂(X_sum_pmf_list G t s vs).toMeasure
            ≤ ∫ z_vs, Real.sqrt ((A + (lambdaCut G t s v : ℝ)) + (z_vs : ℝ))
              ∂(Y_sum_pmf_list G t s vs).toMeasure :=
          ih hnd_vs (A + (lambdaCut G t s v : ℝ)) hA_plus_lam
        have hIH_0 : ∫ z_vs, Real.sqrt (A + (z_vs : ℝ))
              ∂(X_sum_pmf_list G t s vs).toMeasure
            ≤ ∫ z_vs, Real.sqrt (A + (z_vs : ℝ))
              ∂(Y_sum_pmf_list G t s vs).toMeasure :=
          ih hnd_vs A hA_vs
        have hpart_int_X : ∀ (B : ℝ), Integrable (fun z_vs : ℤ => Real.sqrt (B + (z_vs : ℝ)))
            (X_sum_pmf_list G t s vs).toMeasure := by
          intro B
          rw [← PMF.restrict_toMeasure_support]; exact IntegrableOn.of_finite hX_fin
        have hpart_int_Y : ∀ (B : ℝ), Integrable (fun z_vs : ℤ => Real.sqrt (B + (z_vs : ℝ)))
            (Y_sum_pmf_list G t s vs).toMeasure := by
          intro B
          rw [← PMF.restrict_toMeasure_support]; exact IntegrableOn.of_finite hY_fin
        have hFY_eq_lam : ∀ z_vs : ℤ,
            FY z_vs = (1/2 : ℝ) * Real.sqrt ((A + (lambdaCut G t s v : ℝ)) + (z_vs : ℝ))
              + (1/2 : ℝ) * Real.sqrt (A + (z_vs : ℝ)) := by
          intro z_vs
          rw [hFY_majority z_vs]
          have h2 : (1 : ℝ) - (1 / 2) = (1 / 2) := by norm_num
          rw [h2]
          have harg1 : (A + (z_vs : ℝ)) + (lambdaCut G t s v : ℝ)
              = (A + (lambdaCut G t s v : ℝ)) + (z_vs : ℝ) := by ring
          have harg2 : (A + (z_vs : ℝ)) + 0 = A + (z_vs : ℝ) := by ring
          rw [harg1, harg2]
        have hFY_int_eq_X :
            ∫ z_vs, FY z_vs ∂(X_sum_pmf_list G t s vs).toMeasure
              = (1/2 : ℝ) * ∫ z_vs, Real.sqrt ((A + (lambdaCut G t s v : ℝ))
                  + (z_vs : ℝ)) ∂(X_sum_pmf_list G t s vs).toMeasure
                + (1/2 : ℝ) * ∫ z_vs, Real.sqrt (A + (z_vs : ℝ))
                  ∂(X_sum_pmf_list G t s vs).toMeasure := by
          have hfun_eq : (fun z_vs : ℤ => FY z_vs) = fun z_vs : ℤ =>
              (1/2 : ℝ) * Real.sqrt ((A + (lambdaCut G t s v : ℝ)) + (z_vs : ℝ))
                + (1/2 : ℝ) * Real.sqrt (A + (z_vs : ℝ)) := by
            ext z_vs; exact hFY_eq_lam z_vs
          rw [hfun_eq]
          rw [integral_add ((hpart_int_X _).const_mul (1/2))
                ((hpart_int_X _).const_mul (1/2)),
            integral_const_mul, integral_const_mul]
        have hFY_int_eq_Y :
            ∫ z_vs, FY z_vs ∂(Y_sum_pmf_list G t s vs).toMeasure
              = (1/2 : ℝ) * ∫ z_vs, Real.sqrt ((A + (lambdaCut G t s v : ℝ))
                  + (z_vs : ℝ)) ∂(Y_sum_pmf_list G t s vs).toMeasure
                + (1/2 : ℝ) * ∫ z_vs, Real.sqrt (A + (z_vs : ℝ))
                  ∂(Y_sum_pmf_list G t s vs).toMeasure := by
          have hfun_eq : (fun z_vs : ℤ => FY z_vs) = fun z_vs : ℤ =>
              (1/2 : ℝ) * Real.sqrt ((A + (lambdaCut G t s v : ℝ)) + (z_vs : ℝ))
                + (1/2 : ℝ) * Real.sqrt (A + (z_vs : ℝ)) := by
            ext z_vs; exact hFY_eq_lam z_vs
          rw [hfun_eq]
          rw [integral_add ((hpart_int_Y _).const_mul (1/2))
                ((hpart_int_Y _).const_mul (1/2)),
            integral_const_mul, integral_const_mul]
        calc ∫ z_vs, FX z_vs ∂(X_sum_pmf_list G t s vs).toMeasure
            ≤ ∫ z_vs, FY z_vs ∂(X_sum_pmf_list G t s vs).toMeasure := hstep_a
          _ = (1/2 : ℝ) * ∫ z_vs, Real.sqrt ((A + (lambdaCut G t s v : ℝ))
                  + (z_vs : ℝ)) ∂(X_sum_pmf_list G t s vs).toMeasure
                + (1/2 : ℝ) * ∫ z_vs, Real.sqrt (A + (z_vs : ℝ))
                  ∂(X_sum_pmf_list G t s vs).toMeasure := hFY_int_eq_X
          _ ≤ (1/2 : ℝ) * ∫ z_vs, Real.sqrt ((A + (lambdaCut G t s v : ℝ))
                  + (z_vs : ℝ)) ∂(Y_sum_pmf_list G t s vs).toMeasure
                + (1/2 : ℝ) * ∫ z_vs, Real.sqrt (A + (z_vs : ℝ))
                  ∂(Y_sum_pmf_list G t s vs).toMeasure := by
                    have h12 : (0 : ℝ) ≤ 1 / 2 := by norm_num
                    gcongr
          _ = ∫ z_vs, FY z_vs ∂(Y_sum_pmf_list G t s vs).toMeasure := hFY_int_eq_Y.symm

/-- List-level majorization specialized at `A = Vol(s)`.
Consequence of `X_sum_pmf_list_majorized_by_Y_sum_pmf_list_aux` with
`A := Vol(s) ≥ ∑_{v ∈ s.filter(· ∈ L)} d_v` since `s.filter(· ∈ L) ⊆ s`. -/
private lemma X_sum_pmf_list_majorized_by_Y_sum_pmf_list
    (G : TemporalGraph V) (t : ℕ) (s : Finset V) :
    ∀ (L : List V), L.Nodup →
      ∫ z, Real.sqrt ((G.volume t s : ℝ) + z)
          ∂(X_sum_pmf_list G t s L).toMeasure
        ≤ ∫ z, Real.sqrt ((G.volume t s : ℝ) + z)
            ∂(Y_sum_pmf_list G t s L).toMeasure := by
  intro L hnd
  refine X_sum_pmf_list_majorized_by_Y_sum_pmf_list_aux G t s L hnd
    (G.volume t s : ℝ) ?_
  have hsub : s.filter (· ∈ L) ⊆ s := Finset.filter_subset _ _
  have hsum_le : (∑ v ∈ s.filter (· ∈ L), G.degree t v)
      ≤ ∑ v ∈ s, G.degree t v :=
    Finset.sum_le_sum_of_subset hsub
  have hvolS : (∑ v ∈ s, G.degree t v) = G.volume t s := by
    simp only [TemporalGraph.volume, SimpleGraph.volume]
  rw [hvolS] at hsum_le
  exact_mod_cast hsum_le

/-- Core majorization: `∫ √Vol ∂stepDist₂ ≤ ∫ √(Vol(s)+z) ∂Y_sum_pmf`.

Combines `stepDist₂_integral_sqrt_eq_X_sum_pmf` (pushforward LHS = X_sum_pmf integral)
with `X_sum_pmf_list_majorized_by_Y_sum_pmf_list` (X → Y majorization via per-vertex
concave swap). -/
private lemma stepDist₂_majorized_by_Y_sum
    (G : TemporalGraph V)
    (t : ℕ) (s : Finset V) :
    ∫ A', Real.sqrt (G.volume t A' : ℝ) ∂(stepDist₂ G t s).toMeasure
      ≤ ∫ z, Real.sqrt (G.volume t s + z : ℝ) ∂(Y_sum_pmf G t s).toMeasure := by
  -- Step 1: rewrite LHS via pushforward.
  rw [stepDist₂_integral_sqrt_eq_X_sum_pmf G t s]
  -- Step 2: match normal form of the integrand.
  have hX_eq : ∫ z, Real.sqrt (G.volume t s + z : ℝ)
        ∂(X_sum_pmf G t s).toMeasure
      = ∫ z, Real.sqrt ((G.volume t s : ℝ) + z)
        ∂(X_sum_pmf_list G t s (Finset.univ : Finset V).toList).toMeasure := by
    show ∫ z, Real.sqrt (G.volume t s + z : ℝ)
        ∂(X_sum_pmf_list G t s (Finset.univ : Finset V).toList).toMeasure = _
    refine MeasureTheory.integral_congr_ae (ae_of_all _ ?_)
    intro z; push_cast; rfl
  have hY_eq : ∫ z, Real.sqrt (G.volume t s + z : ℝ)
        ∂(Y_sum_pmf G t s).toMeasure
      = ∫ z, Real.sqrt ((G.volume t s : ℝ) + z)
        ∂(Y_sum_pmf_list G t s (Finset.univ : Finset V).toList).toMeasure := by
    show ∫ z, Real.sqrt (G.volume t s + z : ℝ)
        ∂(Y_sum_pmf_list G t s (Finset.univ : Finset V).toList).toMeasure = _
    refine MeasureTheory.integral_congr_ae (ae_of_all _ ?_)
    intro z; push_cast; rfl
  rw [hX_eq, hY_eq]
  exact X_sum_pmf_list_majorized_by_Y_sum_pmf_list G t s
    (Finset.univ : Finset V).toList (Finset.nodup_toList _)


/-- **Taylor + replaceRV bound for `E[√Vol(A')]` over `stepDist₂(G, t, s)`.**

For any non-empty `s` with non-empty complement:
`∫ √Vol(A') ∂stepDist₂(s) ≤ √Vol(s) − d_min · cut(s, V\s) / (32 · Vol(s)^{3/2})`.

**Proof sketch** (Berenbrink et al., ICALP 2016, Lemma 2.1):
1. Factor: `√Vol(A') = √Vol(s) · √(1 + Δ/Vol(s))` where `Δ = Vol(A') − Vol(s)`.
2. Taylor (`sqrt_one_add_taylor3`): `√(1+x) ≤ 1 + x/2 − x²/8 + x³/16`.
3. Define per-vertex replacement RVs `Y_u` (replaceRV trick):
   for `u ∈ V¹`: `Y_u = λ_u` w.p. `1/2` (instead of `d_u` w.p. `λ_u/(2d_u)`).
4. Stochastic domination (Lemma replaceRV): `E[√(1+Δ/ψ²)] ≤ E[√(1+Δ'/ψ²)]`
   by concavity of `√(1+·)`.
5. `E[Δ'] = 0` (volume preservation), `E[Δ'²] ≥ d_min·cut/4`,
   `E[Δ'³] ≤ 0` (third moment of replaced variables, uses `λ_u ≤ d_u`).
6. Combine: `≤ √Vol(s) · (1 − d_min·cut/(32·Vol(s)²))`. -/
private lemma stepDist₂_sqrt_vol_taylor
    (G : TemporalGraphFixedDegree V)
    (t : ℕ) (s : Finset V) (hs : s.Nonempty) :
    ∫ A', Real.sqrt ((G.snapshot t).volume A' : ℝ)
        ∂(stepDist₂ G.toTemporalGraph t s).toMeasure
      ≤ Real.sqrt ((G.snapshot t).volume s : ℝ)
        - (G.minDegreeAt 0 : ℝ) * (G.edgesBetween t s (univ \ s) : ℝ)
          / (32 * ((G.snapshot t).volume s : ℝ) ^ (3 / 2 : ℝ)) := by
  have hψ : (0 : ℝ) < (G.snapshot t).volume s := by
    obtain ⟨v, hv⟩ := hs.exists_mem
    have hdeg_pos : 0 < G.degree t v := G.degrees_pos v t
    have : 0 < (G.snapshot t).volume s :=
      Nat.lt_of_lt_of_le hdeg_pos (Finset.single_le_sum (fun v _ => Nat.zero_le _) hv)
    exact_mod_cast this
  exact le_trans (stepDist₂_majorized_by_Y_sum G.toTemporalGraph t s)
    (Y_sum_pmf_int_sqrt_bound G t s hψ)

omit [Nonempty V] in
private lemma decide_mem_compl (v : V) (s : Finset V) :
    decide (v ∈ univ \ s) = !decide (v ∈ s) := by
  by_cases hv : v ∈ s <;> simp [hv]

private lemma nextOpinionDist₂_map_not
    (G : TemporalGraph V) (t : ℕ) (s : Finset V) (v : V) :
    (nextOpinionDist₂ G t s v).map Bool.not = nextOpinionDist₂ G t (univ \ s) v := by
  by_cases hN : (G.neighborFinset t v).Nonempty
  · rw [nextOpinionDist₂_eq_bind_of_nonempty G t s v hN,
        nextOpinionDist₂_eq_bind_of_nonempty G t (univ \ s) v hN,
        PMF.map_bind]
    congr 1; ext bern
    cases bern with
    | false =>
      simp [cond_false, PMF.map_comp, PMF.map_apply, Function.comp_apply]
    | true =>
      simp only [cond_true, PMF.pure_map]
      rw [decide_mem_compl]
  · rw [nextOpinionDist₂_eq_pure_of_not_nonempty G t s v hN,
        nextOpinionDist₂_eq_pure_of_not_nonempty G t (univ \ s) v hN,
        PMF.pure_map, decide_mem_compl]

private lemma insert_sdiff_insert {α : Type*} [DecidableEq α]
    {U : Finset α} {v : α} {T : Finset α} (hv : v ∉ U) :
    (insert v U) \ insert v T = U \ T := by
  ext w; simp only [Finset.mem_sdiff, Finset.mem_insert]
  constructor
  · rintro ⟨hw, hnw⟩
    exact ⟨hw.resolve_left (fun h => hnw (Or.inl h)), fun h => hnw (Or.inr h)⟩
  · rintro ⟨hw, hnw⟩
    exact ⟨Or.inr hw, fun h => h.elim (fun e => hv (e ▸ hw)) hnw⟩

private lemma insert_sdiff_of_not_mem {α : Type*} [DecidableEq α]
    {U : Finset α} {v : α} {T : Finset α} (hv : v ∉ U) (hT : T ⊆ U) :
    (insert v U) \ T = insert v (U \ T) := by
  ext w; simp only [Finset.mem_sdiff, Finset.mem_insert]
  constructor
  · rintro ⟨hw, hnw⟩
    exact hw.elim (fun h => Or.inl h) (fun h => Or.inr ⟨h, hnw⟩)
  · rintro (rfl | ⟨hw, hnw⟩)
    · exact ⟨Or.inl rfl, fun h => hv (hT h)⟩
    · exact ⟨Or.inr hw, hnw⟩

private lemma stepDist₂Aux_map_compl
    (G : TemporalGraph V) (t : ℕ) (s : Finset V) :
    ∀ (L : List V), L.Nodup →
      (stepDist₂Aux G t s L).map (fun T => L.toFinset \ T) =
        stepDist₂Aux G t (univ \ s) L := by
  intro L hnd
  induction L with
  | nil => simp [stepDist₂Aux, PMF.pure_map]
  | cons v vs ih =>
    have hnd' := (List.nodup_cons.mp hnd).2
    have hv_notin_vs : v ∉ vs := (List.nodup_cons.mp hnd).1
    have hv_notin_toFinset : v ∉ vs.toFinset := List.mem_toFinset.not.mpr hv_notin_vs
    simp only [stepDist₂Aux]
    -- LHS: ((stepDist₂Aux s vs).bind(…)).map((v::vs).toFinset \ ·)
    rw [PMF.map_bind]
    -- Use IH: rewrite stepDist₂Aux(V\s, vs) = stepDist₂Aux(s, vs).map(vs.toFinset \ ·)
    rw [← ih hnd', PMF.bind_map]
    -- Both: stepDist₂Aux(s, vs).bind(fun T => ...)
    ext A
    simp only [PMF.bind_apply]
    apply tsum_congr; intro T
    by_cases hT_zero : (stepDist₂Aux G t s vs) T = 0
    · simp [hT_zero]
    · have hT_supp : T ∈ (stepDist₂Aux G t s vs).support := by
        rwa [PMF.mem_support_iff]
      have hT_sub : T ⊆ vs.toFinset := stepDist₂Aux_support_subset G t s vs T hT_supp
      congr 1
      -- LHS: (nod(s,v).map(cond · (ins v T) T)).map((v::vs).toFinset \ ·)
      -- RHS: nod(V\s,v).map(cond · (ins v (vs.toFinset\T)) (vs.toFinset\T))
      rw [PMF.map_comp]
      -- LHS: nod(s,v).map(fun b => (v::vs).toFinset \ cond b (ins v T) T)
      -- RHS: nod(V\s,v).map(fun b => cond b (ins v (vs.toFinset\T)) (vs.toFinset\T))
      -- Goal shape after PMF.map_comp:
      -- nod(s,v).map(f) = nod(V\s,v).map(g)
      -- where f = (toFinset \ ·) ∘ (cond · (ins v T) T)
      --       g = cond · (ins v (vs.toFinset\T)) (vs.toFinset\T)
      -- We show f = g ∘ Bool.not, then use nextOpinionDist₂_map_not
      have hfun :
          (fun T_1 : Finset V => (v :: vs).toFinset \ T_1) ∘
            (fun isZero : Bool => bif isZero then insert v T else T) =
          (fun b : Bool =>
            bif b then insert v (vs.toFinset \ T) else vs.toFinset \ T) ∘
            Bool.not := by
        funext b; simp only [Function.comp_apply]
        rw [List.toFinset_cons]
        cases b with
        | true =>
          simp only [cond_true, Bool.not_true, cond_false]
          exact insert_sdiff_insert hv_notin_toFinset
        | false =>
          simp only [cond_false, Bool.not_false, cond_true]
          exact insert_sdiff_of_not_mem hv_notin_toFinset hT_sub
      rw [hfun, ← PMF.map_comp, nextOpinionDist₂_map_not]
      simp only [Function.comp_apply]

/-- **Flip symmetry:** `stepDist₂(G,t,s).map(V\·) = stepDist₂(G,t,V\s)`.

The per-vertex probability satisfies `p_v(V\s) = 1 − p_v(s)` because
`decide(v ∈ V\s) = !decide(v ∈ s)` and `decide(w ∈ V\s) = !decide(w ∈ s)`.
Since vertex updates are independent, the product distribution flips:
`Pr[A' | s] = Pr[V\A' | V\s]` for all `A'`. -/
private lemma stepDist₂_map_compl
    (G : TemporalGraph V) (t : ℕ) (s : Finset V) :
    (stepDist₂ G t s).map (fun A' => univ \ A') = stepDist₂ G t (univ \ s) := by
  rw [← stepDist₂Aux_eq_stepDist₂, ← stepDist₂Aux_eq_stepDist₂]
  have hnd := Finset.nodup_toList (univ : Finset V)
  have key := stepDist₂Aux_map_compl G t s _ hnd
  rw [Finset.toList_toFinset] at key
  exact key

/-- **Integral flip symmetry:** `∫ f(V\A') ∂stepDist₂(s) = ∫ f(A') ∂stepDist₂(V\s)`. -/
private lemma stepDist₂_integral_compl
    (G : TemporalGraph V) (t : ℕ) (s : Finset V) (f : Finset V → ℝ) :
    ∫ A', f (univ \ A') ∂(stepDist₂ G t s).toMeasure
      = ∫ A', f A' ∂(stepDist₂ G t (univ \ s)).toMeasure := by
  have hmeas : Measurable (fun A' : Finset V => univ \ A') := measurable_of_finite _
  -- Step 1: ∫ f(V\A') ∂μ = ∫ f ∂(μ.map (V\·))  by change of variables
  rw [← MeasureTheory.integral_map hmeas.aemeasurable
    (measurable_of_finite f).aestronglyMeasurable,
  -- Step 2: μ.map (V\·) = (stepDist₂(s).map (V\·)).toMeasure  by PMF.toMeasure_map
    PMF.toMeasure_map (fun A' => univ \ A') (stepDist₂ G t s) hmeas,
  -- Step 3: stepDist₂(s).map (V\·) = stepDist₂(V\s)  by flip symmetry
    stepDist₂_map_compl G t s]

/-- **Taylor + replaceRV bound for `E[√Vol(V\A')]` over `stepDist₂(G, t, s)`.**

For any non-empty `s` with non-empty complement:
`∫ √Vol(V\A') ∂stepDist₂(s) ≤ √Vol(V\s) − d_min · cut(s, V\s) / (32 · Vol(V\s)^{3/2})`.

Derived from `stepDist₂_sqrt_vol_taylor` applied to `V\s` via flip symmetry
`stepDist₂_integral_compl`. -/
private lemma stepDist₂_sqrt_compl_vol_taylor
    (G : TemporalGraphFixedDegree V)
    (t : ℕ) (s : Finset V) (hs : s.Nonempty) (hs_compl : (univ \ s).Nonempty) :
    ∫ A', Real.sqrt ((G.snapshot t).volume (univ \ A') : ℝ)
        ∂(stepDist₂ G.toTemporalGraph t s).toMeasure
      ≤ Real.sqrt ((G.snapshot t).volume (univ \ s) : ℝ)
        - (G.minDegreeAt 0 : ℝ) * (G.edgesBetween t s (univ \ s) : ℝ)
          / (32 * ((G.snapshot t).volume (univ \ s) : ℝ) ^ (3 / 2 : ℝ)) := by
  -- Rewrite LHS via flip symmetry: ∫ √Vol(V\A') ∂stepDist₂(s) = ∫ √Vol(A') ∂stepDist₂(V\s)
  rw [stepDist₂_integral_compl G.toTemporalGraph t s (fun A' => Real.sqrt ((G.snapshot t).volume A' : ℝ))]
  -- Apply stepDist₂_sqrt_vol_taylor to V\s (with V\(V\s) = s)
  have hs' : (univ \ s).Nonempty := hs_compl
  have hs_compl' : (univ \ (univ \ s)).Nonempty := by
    rwa [Finset.sdiff_sdiff_eq_self (Finset.subset_univ s)]
  have hcut : G.edgesBetween t (univ \ s) (univ \ (univ \ s))
      = G.edgesBetween t s (univ \ s) := by
    simp only [TemporalGraphFixedDegree.edgesBetween]
    rw [Finset.sdiff_sdiff_eq_self (Finset.subset_univ s),
      TemporalGraph.edgesBetween_comm']
  rw [← hcut]
  exact stepDist₂_sqrt_vol_taylor G t (univ \ s) hs'

lemma stepDist₂_sqrt_minority_volume_upper
    (G : TemporalGraphFixedDegree V)
    (t : ℕ) (s : Finset V) (hs : s.Nonempty) (hs_compl : (univ \ s).Nonempty) :
    ∫ A', Real.sqrt ((G.snapshot t).volume (VoterModel.minoritySet G.toTemporalGraph t A') : ℝ)
        ∂(stepDist₂ G.toTemporalGraph t s).toMeasure
      ≤ Real.sqrt ((G.snapshot t).volume (VoterModel.minoritySet G.toTemporalGraph t s) : ℝ)
        - (G.minDegreeAt 0 : ℝ) * (G.edgesBetween t s (univ \ s) : ℝ)
          / (32 * ((G.snapshot t).volume (VoterModel.minoritySet G.toTemporalGraph t s) : ℝ)
              ^ (3 / 2 : ℝ)) := by
  -- Pointwise: Vol(minSet(A')) ≤ Vol(A') for all A'
  have h_le_vol : ∀ A' : Finset V,
      ((G.snapshot t).volume (VoterModel.minoritySet G.toTemporalGraph t A') : ℝ)
        ≤ ((G.snapshot t).volume A' : ℝ) := by
    intro A'; unfold VoterModel.minoritySet; split_ifs with h
    · exact le_refl _
    · push Not at h; exact_mod_cast h.le
  -- Pointwise: Vol(minSet(A')) ≤ Vol(V\A') for all A'
  have h_le_compl : ∀ A' : Finset V,
      ((G.snapshot t).volume (VoterModel.minoritySet G.toTemporalGraph t A') : ℝ)
        ≤ ((G.snapshot t).volume (univ \ A') : ℝ) := by
    intro A'; unfold VoterModel.minoritySet; split_ifs with h
    · exact_mod_cast h
    · exact le_refl _
  -- Case split on whether s is minority or majority
  by_cases hmin : (G.snapshot t).volume s ≤ (G.snapshot t).volume (univ \ s)
  · -- Minority case: minSet(s) = s
    have h_minSet_eq : VoterModel.minoritySet G.toTemporalGraph t s = s := by
      simp [VoterModel.minoritySet, hmin]
    rw [h_minSet_eq]
    -- √Vol(minSet(A')) ≤ √Vol(A') pointwise, so integrate
    calc ∫ A', Real.sqrt ((G.snapshot t).volume
            (VoterModel.minoritySet G.toTemporalGraph t A') : ℝ)
          ∂(stepDist₂ G.toTemporalGraph t s).toMeasure
        ≤ ∫ A', Real.sqrt ((G.snapshot t).volume A' : ℝ)
            ∂(stepDist₂ G.toTemporalGraph t s).toMeasure := by
          exact MeasureTheory.integral_mono_ae Integrable.of_finite Integrable.of_finite
            (ae_of_all _ fun A' => Real.sqrt_le_sqrt (h_le_vol A'))
      _ ≤ _ := stepDist₂_sqrt_vol_taylor G t s hs
  · -- Majority case: minSet(s) = V\s
    push Not at hmin
    have h_minSet_eq : VoterModel.minoritySet G.toTemporalGraph t s = univ \ s := by
      unfold VoterModel.minoritySet; exact if_neg (not_le.mpr hmin)
    rw [h_minSet_eq]
    -- √Vol(minSet(A')) ≤ √Vol(V\A') pointwise, so integrate
    calc ∫ A', Real.sqrt ((G.snapshot t).volume
            (VoterModel.minoritySet G.toTemporalGraph t A') : ℝ)
          ∂(stepDist₂ G.toTemporalGraph t s).toMeasure
        ≤ ∫ A', Real.sqrt ((G.snapshot t).volume (univ \ A') : ℝ)
            ∂(stepDist₂ G.toTemporalGraph t s).toMeasure := by
          exact MeasureTheory.integral_mono_ae Integrable.of_finite Integrable.of_finite
            (ae_of_all _ fun A' => Real.sqrt_le_sqrt (h_le_compl A'))
      _ ≤ _ := stepDist₂_sqrt_compl_vol_taylor G t s hs hs_compl

end PotDecHelpers

end VoterModel
