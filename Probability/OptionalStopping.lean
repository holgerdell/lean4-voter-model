module

public import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalStopping
public import Mathlib.Probability.Notation


@[expose] public section
open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators

noncomputable section

/-- Case 2 for submartingales: if `T` is bounded by a constant, then
`E[X_T] ≥ E[X_0]`. -/
theorem optional_stopping_time_submartingale_of_bounded_stopping_time
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ (‹MeasurableSpace Ω›)}
    {X : ℕ → Ω → ℝ}
    (hsub : Submartingale X ℱ μ)
    {T : Ω → ℕ} (hT : IsStoppingTime ℱ (fun ω => (T ω : ℕ∞)))
    -- T is bounded by a constant
    {N : ℕ} (hT_bdd : ∀ ω, T ω ≤ N) :
    -- Conclusion: E[X_T] ≥ E[X_0]
    μ[fun ω => X (T ω) ω] ≥ μ[X 0] := by
  have hτ0 : IsStoppingTime ℱ (fun _ => (0 : ℕ∞)) := isStoppingTime_const ℱ 0
  calc
    ∫ ω, X 0 ω ∂μ = ∫ ω, stoppedValue X (fun _ => (0 : ℕ∞)) ω ∂μ := by
      congr 1
    _ ≤ ∫ ω, stoppedValue X (fun ω => (T ω : ℕ∞)) ω ∂μ :=
      hsub.expected_stoppedValue_mono hτ0 hT (fun ω => by simp) (fun ω => by exact_mod_cast hT_bdd ω)
    _ = ∫ ω, X (T ω) ω ∂μ := by
      congr 1

/-- Case 2 for supermartingales: if `T` is bounded by a constant, then
`E[X_T] ≤ E[X_0]`. -/
theorem optional_stopping_time_supermartingale_of_bounded_stopping_time
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ (‹MeasurableSpace Ω›)}
    {X : ℕ → Ω → ℝ}
    (hsuper : Supermartingale X ℱ μ)
    {T : Ω → ℕ} (hT : IsStoppingTime ℱ (fun ω => (T ω : ℕ∞)))
    -- T is bounded by a constant
    {N : ℕ} (hT_bdd : ∀ ω, T ω ≤ N) :
    -- Conclusion: E[X_T] ≤ E[X_0]
    μ[fun ω => X (T ω) ω] ≤ μ[X 0] := by
  have hneg :
      ∫ ω, (-X) (T ω) ω ∂μ ≥ ∫ ω, (-X) 0 ω ∂μ :=
    optional_stopping_time_submartingale_of_bounded_stopping_time
      (μ := μ) (ℱ := ℱ) (X := -X) hsuper.neg hT hT_bdd
  simpa only [Pi.neg_apply, integral_neg, neg_le_neg_iff] using hneg


