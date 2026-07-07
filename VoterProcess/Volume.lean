module

import VoterProcess.Expectation
import Probability.Supermartingale
public import VoterProcess.Step
public import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import TemporalGraph.Basic


@[expose] public section
open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators

noncomputable section

namespace VoterModel

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V] {Ω : Type*}

/-! ## Named volume processes

These abbreviations give names to the real-valued volume processes
`Vol(Aₜ)` and `Vol(Sₜ)` for use in martingale/supermartingale statements. -/

/-- The volume-of-opinion-0-set process: `Vol(Aₜ)(ω) = Vol(G, t, A t ω)`. -/
abbrev volOpinionProcess (G : TemporalGraph V) (A : ℕ → Ω → Finset V) :
    ℕ → Ω → ℝ :=
  fun t ω => (TemporalGraph.volume G t (A t ω) : ℝ)

/-- The volume-of-complement process: `Vol(V \ Aₜ)(ω)`. -/
abbrev volComplementProcess (G : TemporalGraph V) (A : ℕ → Ω → Finset V) :
    ℕ → Ω → ℝ :=
  fun t ω => (TemporalGraph.volume G t (univ \ A t ω) : ℝ)

/-- The minority-set volume process: `Vol(Sₜ)(ω) = Vol(minoritySet(Aₜ))(ω)`. -/
abbrev volMinorityProcess (G : TemporalGraph V) (A : ℕ → Ω → Finset V) :
    ℕ → Ω → ℝ :=
  fun t ω => (TemporalGraph.volume G t (minoritySet G t (A t ω)) : ℝ)

/-! ## One-step expected volume identity -/

private theorem expected_volume_step
  (G : TemporalGraphFixedDegree V)
  (S : Finset V) (t : ℕ) :
    ∫ S', (TemporalGraph.volume G.toTemporalGraph (t + 1) S' : ℝ)
        ∂((stepDist₂ G.toTemporalGraph t S).toMeasure)
      = TemporalGraph.volume G.toTemporalGraph t S := by
  rw [← stepDist₂Aux_eq_stepDist₂ (G := G.toTemporalGraph) (t := t) (S := S)]
  have hvol :
      (fun T : Finset V => (TemporalGraph.volume G.toTemporalGraph (t + 1) T : ℝ))
        = fun T => ∑ u, if u ∈ T then (TemporalGraph.degree G.toTemporalGraph (t + 1) u : ℝ)
            else 0 := by
    funext T
    unfold TemporalGraph.volume TemporalGraph.degree SimpleGraph.volume SimpleGraph.degree
    simp
  simp_rw [hvol]
  rw [PMF.integral_eq_sum]
  simp_rw [smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hsum_as_integral :
      (∑ y : V, ∑ x : Finset V, ((stepDist₂Aux G.toTemporalGraph t S Finset.univ.toList) x).toReal *
          (if y ∈ x then (TemporalGraph.degree G.toTemporalGraph (t + 1) y : ℝ) else 0))
        =
      ∑ y : V, ∫ x : Finset V,
          (if y ∈ x then (TemporalGraph.degree G.toTemporalGraph (t + 1) y : ℝ) else 0)
          ∂((stepDist₂Aux G.toTemporalGraph t S Finset.univ.toList).toMeasure) := by
    refine Finset.sum_congr rfl ?_
    intro y hy
    exact (PMF.integral_eq_sum (stepDist₂Aux G.toTemporalGraph t S Finset.univ.toList)
      (fun x : Finset V =>
        if y ∈ x then (TemporalGraph.degree G.toTemporalGraph (t + 1) y : ℝ) else 0)).symm
  rw [hsum_as_integral]
  calc
    (∑ u : V, ∫ x : Finset V,
        (if u ∈ x then (TemporalGraph.degree G.toTemporalGraph (t + 1) u : ℝ) else 0)
          ∂((stepDist₂Aux G.toTemporalGraph t S Finset.univ.toList).toMeasure))
      = ∑ u : V,
          ((((if u ∈ S then TemporalGraph.degree G.toTemporalGraph t u else 0) +
              TemporalGraph.degreeIn G.toTemporalGraph t u S : ℕ) : ℝ) / 2) := by
          refine Finset.sum_congr rfl ?_
          intro u hu
          rw [indicator_expectation_gen (G := G.toTemporalGraph) (t := t) (S := S) (u := u)
            (c := TemporalGraph.degree G.toTemporalGraph (t + 1) u) Finset.univ.toList
            (Finset.nodup_toList _)]
          have hdeg_fixed : TemporalGraph.degree G.toTemporalGraph (t + 1) u =
              TemporalGraph.degree G.toTemporalGraph t u := by
            exact G.degrees_fixed u (t + 1) t
          simp [hdeg_fixed, nextOpinion_weighted_expectation]
    _ = TemporalGraph.volume G.toTemporalGraph t S := by
      have hself :
          (∑ v, ((if v ∈ S then TemporalGraph.degree G.toTemporalGraph t v else 0 : ℕ) : ℝ))
            = TemporalGraph.volume G.toTemporalGraph t S := by
        classical
        simp only [TemporalGraph.volume, TemporalGraph.degree, SimpleGraph.volume,
          SimpleGraph.degree, Nat.cast_sum]
        simp
      have hneigh :
          (∑ v, (TemporalGraph.degreeIn G.toTemporalGraph t v S : ℝ)) =
            TemporalGraph.volume G.toTemporalGraph t S := by
        exact_mod_cast TemporalGraph.sum_edgesVertex_eq_volume G.toTemporalGraph t S
      simp_rw [Nat.cast_add, add_div]
      rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div, hself, hneigh]
      ring

/-! ## Expected volume is constant (martingale property in PMF framework) -/

/-- \label{lem:expected_volume_constant}

Let `𝒢` be a temporal graph whose vertex-degrees are fixed. Let `t₀ ∈ ℕ`
and let `a ⊆ V` be a fixed set. Let `(Aᵢ : i ≥ t₀)` with `A_{t₀} = a` be
the evolution of `a` in the standard voter model on `𝒢` started at time `t₀`.

For all `t ∈ ℕ`, we have `E[Vol(A_{t₀+t})] = Vol(a)`. -/
theorem expected_volume_constant
  (G : TemporalGraphFixedDegree V)
  -- t₀ ∈ ℕ, a ⊆ V(G)
  (t₀ : ℕ) (a : Finset V)
  -- t ∈ ℕ
  (t : ℕ) :
    -- Conclusion: E[Vol(A_{t₀+t})] = Vol(a)
    ∫ A', (TemporalGraph.volume G.toTemporalGraph (t₀ + t) A' : ℝ)
        ∂((opinionProcess₂ G.toTemporalGraph t₀ t a).toMeasure)
      = TemporalGraph.volume G.toTemporalGraph t₀ a := by
  induction t with
  | zero =>
      unfold opinionProcess₂
      rw [PMF.toMeasure_pure]; simp
  | succ t ih =>
      unfold opinionProcess₂
      have hbind :
          ∫ S', (TemporalGraph.volume G.toTemporalGraph (t₀ + (t + 1)) S' : ℝ)
              ∂((((opinionProcess₂ G.toTemporalGraph t₀ t a) : PMF (Finset V)).bind
                (fun S' : Finset V => stepDist₂ G.toTemporalGraph (t₀ + t) S')).toMeasure)
            =
              ∫ S, (∫ S', (TemporalGraph.volume G.toTemporalGraph (t₀ + (t + 1)) S' : ℝ)
                  ∂((stepDist₂ G.toTemporalGraph (t₀ + t) S).toMeasure))
                ∂((opinionProcess₂ G.toTemporalGraph t₀ t a).toMeasure) := by
        exact pmf_integral_bind ((opinionProcess₂ G.toTemporalGraph t₀ t a) : PMF (Finset V))
          (fun S' : Finset V => stepDist₂ G.toTemporalGraph (t₀ + t) S')
          (fun S' : Finset V => TemporalGraph.volume G.toTemporalGraph (t₀ + (t + 1)) S')
      rw [hbind]
      have hstep :
          ∀ S : Finset V,
            ∫ S', (TemporalGraph.volume G.toTemporalGraph (t₀ + (t + 1)) S' : ℝ)
                ∂((stepDist₂ G.toTemporalGraph (t₀ + t) S).toMeasure)
              = TemporalGraph.volume G.toTemporalGraph (t₀ + t) S := by
        intro S
        simpa [Nat.add_assoc] using expected_volume_step G S (t₀ + t)
      simp_rw [hstep]
      simpa using ih

/-! ## Martingale and supermartingale properties -/


/-- \label{cor:vol-minority-supermartingale}

Let `𝒢` be a temporal graph whose vertex-degrees are fixed. Let `Aₜ` be
the opinion-0 set at time `t` in the standard voter model on `𝒢` with
`κ = 2` opinions (implicit throughout the formalization).
Then `Vol(Sₜ)` is a supermartingale.

**Proof:** By `opinionProcess₂_volume_martingale`, both `Vol(Aₜ)` and
`Vol(V \ Aₜ)` are martingales. By `min_martingale_supermartingale`,
their pointwise minimum `Vol(Sₜ) = Vol(minoritySet(Aₜ))` is a
supermartingale. -/
theorem vol_minority_supermartingale
    {Ω : Type*} [MeasurableSpace Ω]
    {G : TemporalGraph V}
    (vm : TemporalGraph.VoterModelAbstract G 2 Ω)
    -- Vol(A_t) and Vol(V \ A_t) are martingales (from opinionProcess₂_volume_martingale)
    (hVolA : Martingale (volOpinionProcess G vm.opinionZeroSet) vm.ℱ vm.μ)
    (hVolAc : Martingale (volComplementProcess G vm.opinionZeroSet) vm.ℱ vm.μ) :
    -- Conclusion: Vol(S_t) is a supermartingale
    Supermartingale (volMinorityProcess G vm.opinionZeroSet) vm.ℱ vm.μ := by
  have heq : volMinorityProcess G vm.opinionZeroSet =
      fun t ω => min (volOpinionProcess G vm.opinionZeroSet t ω) (volComplementProcess G vm.opinionZeroSet t ω) := by
    ext t ω; simp only [volMinorityProcess, volOpinionProcess, volComplementProcess, minoritySet]
    split_ifs with h <;> simp [min_def, show (TemporalGraph.volume G t (vm.opinionZeroSet t ω) : ℝ) ≤
      TemporalGraph.volume G t (univ \ vm.opinionZeroSet t ω) ↔ TemporalGraph.volume G t (vm.opinionZeroSet t ω) ≤
      TemporalGraph.volume G t (univ \ vm.opinionZeroSet t ω) from Nat.cast_le] <;> omega
  rw [heq]
  exact min_martingale_supermartingale hVolA hVolAc

end VoterModel
