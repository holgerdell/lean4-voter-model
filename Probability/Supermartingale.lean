module

public import Mathlib.Probability.Martingale.Basic


@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

/-- \label{lem:from-martingale-to-supermartingale}

Let `M` and `N` be discrete martingales w.r.t. the same filtration `(ℱ_t)`.
Then `X_t = min(M_t, N_t)` is a supermartingale w.r.t. `(ℱ_t)`. -/
theorem min_martingale_supermartingale
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω}
    -- Filtration (ℱ_t)
    {ℱ : Filtration ℕ (‹MeasurableSpace Ω›)}
    -- Discrete martingales M_t and N_t w.r.t. (ℱ_t)
    {M N : ℕ → Ω → ℝ}
    (hM : Martingale M ℱ μ)
    (hN : Martingale N ℱ μ) :
    -- Conclusion: X_t = min(M_t, N_t) is a supermartingale
    Supermartingale (fun i ω => min (M i ω) (N i ω)) ℱ μ := by
  refine ⟨?adapted, ?condExp, ?integrable⟩
  case adapted =>
    intro i
    exact @StronglyMeasurable.inf Ω ℝ (M i) (N i) (ℱ i) _ _ _
      (hM.stronglyAdapted i) (hN.stronglyAdapted i)
  case integrable =>
    intro i
    exact (hM.integrable i).inf (hN.integrable i)
  case condExp =>
    -- E[min(M_j, N_j) | ℱ_i] ≤ min(M_i, N_i)
    -- Since min(M_j, N_j) ≤ M_j, by condExp_mono: E[min(M_j,N_j)|ℱ_i] ≤ E[M_j|ℱ_i] =ᵃˢ M_i
    -- Similarly: E[min(M_j, N_j)|ℱ_i] ≤ E[N_j|ℱ_i] =ᵃˢ N_i
    intro i j hij
    have hmin_int := (hM.integrable j).inf (hN.integrable j)
    have hcond_le_M := condExp_mono (m := ℱ i) hmin_int (hM.integrable j)
      (ae_of_all μ (fun ω => min_le_left (M j ω) (N j ω)))
    have hcond_le_N := condExp_mono (m := ℱ i) hmin_int (hN.integrable j)
      (ae_of_all μ (fun ω => min_le_right (M j ω) (N j ω)))
    have hM_eq := hM.condExp_ae_eq hij
    have hN_eq := hN.condExp_ae_eq hij
    filter_upwards [hcond_le_M, hcond_le_N, hM_eq, hN_eq] with ω h1 h2 h3 h4
    exact le_min (h1.trans (le_of_eq h3)) (h2.trans (le_of_eq h4))
