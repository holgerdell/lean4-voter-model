module

public import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.CondVar


@[expose] public section
open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators

noncomputable section



/-- Conditional Jensen for `x ↦ x^2`: `(μ[Y | m]) ^ 2 ≤ μ[Y ^ 2 | m]` a.e., for `Y ∈ L^2`. -/
theorem sq_condExp_le_condExp_sq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {Y : Ω → ℝ} (hY : MemLp Y 2 μ) :
    ∀ᵐ ω ∂μ, (μ[Y | m]) ω ^ 2 ≤ (μ[Y ^ 2 | m]) ω := by
  have hvar_eq := condVar_ae_eq_condExp_sq_sub_sq_condExp hm hY
  have hvar_nn : 0 ≤ᵐ[μ] Var[Y; μ | m] :=
    condExp_nonneg (ae_of_all μ fun ω => sq_nonneg _)
  filter_upwards [hvar_eq, hvar_nn] with ω hω_eq hω_nn
  simp only [Pi.sub_apply, Pi.pow_apply, Pi.zero_apply] at hω_eq hω_nn
  linarith

/-- \label{lem:markov-inequality}

Let `X` be a non-negative random variable and `a > 0`. Then
`P(X ≥ a) ≤ E[X] / a`. -/
theorem markov_inequality
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} (hX_nn : 0 ≤ᵐ[μ] X) (hX : Integrable X μ)
    {a : ℝ} (ha : 0 < a) :
    μ {ω | a ≤ X ω} ≤ ENNReal.ofReal (μ[X] / a) := by
  have hX_meas : AEMeasurable (fun ω => ENNReal.ofReal (X ω)) μ :=
    hX.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have ha0 : ENNReal.ofReal a ≠ 0 := by
    positivity
  have hmarkov :
      μ {ω | ENNReal.ofReal a ≤ ENNReal.ofReal (X ω)}
        ≤ (∫⁻ ω, ENNReal.ofReal (X ω) ∂μ) / ENNReal.ofReal a :=
    meas_ge_le_lintegral_div (μ := μ) (f := fun ω => ENNReal.ofReal (X ω)) hX_meas ha0
      ENNReal.ofReal_ne_top
  have hset : {ω | ENNReal.ofReal a ≤ ENNReal.ofReal (X ω)} = {ω | a ≤ X ω} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h
      by_contra hx
      have hx' : X ω < a := lt_of_not_ge hx
      have : ENNReal.ofReal (X ω) < ENNReal.ofReal a := (ENNReal.ofReal_lt_ofReal_iff ha).2 hx'
      exact not_lt_of_ge h this
    · intro h
      exact ENNReal.ofReal_le_ofReal h
  rw [hset, ← ofReal_integral_eq_lintegral_ofReal hX hX_nn] at hmarkov
  simpa [ENNReal.ofReal_div_of_pos ha] using hmarkov





private theorem hasCondSubgaussianMGF_of_mem_Icc_of_condExp_eq_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
  {X : Ω → ℝ} (hXm : Measurable[mΩ] X)
    {a b : ℝ}
    (hb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b)
    (hc : μ[X | m] =ᵐ[μ] 0) :
    HasCondSubgaussianMGF m hm X ((‖b - a‖₊ / 2) ^ 2) μ := by
  rw [HasCondSubgaussianMGF]
  refine Kernel.HasSubgaussianMGF.of_rat ?_ ?_
  · intro t
    have h_int : Integrable (fun ω ↦ Real.exp (t * X ω)) μ :=
      integrable_exp_mul_of_mem_Icc hXm.aemeasurable hb
    rw [condExpKernel_comp_trim (μ := μ) (m := m) (mΩ := mΩ) hm]
    exact h_int
  · let s : Set Ω := X ⁻¹' (Set.Icc a b)ᶜ
    have hs : @MeasurableSet Ω mΩ s := hXm (isClosed_Icc.measurableSet.compl)
    have hs_zero : μ s = 0 := by
      have hs_ae : sᶜ ∈ ae μ := by
        filter_upwards [hb] with ω hω
        simpa [s] using hω
      exact compl_mem_ae_iff.1 hs_ae
    have h_ind_zero : Set.indicator s (fun _ => (1 : ℝ)) =ᵐ[μ] 0 := by
      filter_upwards [compl_mem_ae_iff.2 hs_zero] with ω hω
      have hsω : ω ∉ s := by simpa using hω
      simp [hsω]
    have hcond_prob_zero : μ⟦s | m⟧ =ᵐ[μ] 0 := by
      change μ[Set.indicator s (fun _ => (1 : ℝ)) | m] =ᵐ[μ] 0
      exact (condExp_congr_ae h_ind_zero).trans <|
        Filter.EventuallyEq.of_eq (condExp_zero (μ := μ) (m := m))
    have hcond_prob_zero_trim : μ⟦s | m⟧ =ᵐ[μ.trim hm] 0 :=
      stronglyMeasurable_condExp.ae_eq_trim_of_stronglyMeasurable hm stronglyMeasurable_zero
        hcond_prob_zero
    have hkernel_zero : (fun ω ↦ (condExpKernel (mΩ := mΩ) μ m ω).real s) =ᵐ[μ.trim hm] 0 :=
      (condExpKernel_ae_eq_trim_condExp (μ := μ) (m := m) (mΩ := mΩ) hm hs).trans
        hcond_prob_zero_trim
    have hkernel_mem :
        ∀ᵐ ω ∂μ.trim hm, ∀ᵐ y ∂condExpKernel (mΩ := mΩ) μ m ω, X y ∈ Set.Icc a b := by
      filter_upwards [hkernel_zero] with ω hω
      have hω' : ((condExpKernel (mΩ := mΩ) μ m ω).real s) = 0 := by
        simpa using hω
      have hs_zero' : condExpKernel (mΩ := mΩ) μ m ω s = 0 := by
        rw [measureReal_def, ENNReal.toReal_eq_zero_iff] at hω'
        rcases hω' with hω' | hω'
        · exact hω'
        · exact (measure_ne_top _ _ hω').elim
      filter_upwards [compl_mem_ae_iff.2 hs_zero'] with y hy
      simpa [s] using hy
    have hX_int : Integrable X μ := Integrable.of_mem_Icc a b hXm.aemeasurable hb
    have hc_trim : μ[X | m] =ᵐ[μ.trim hm] 0 :=
      stronglyMeasurable_condExp.ae_eq_trim_of_stronglyMeasurable hm stronglyMeasurable_zero hc
    have hkernel_int_zero : ∀ᵐ ω ∂μ.trim hm, ∫ y, X y ∂condExpKernel (mΩ := mΩ) μ m ω = 0 := by
      filter_upwards [condExp_ae_eq_trim_integral_condExpKernel (μ := μ) (m := m) (mΩ := mΩ) hm hX_int,
        hc_trim] with ω hω_int hω_zero
      rw [hω_zero] at hω_int
      simpa using hω_int.symm
    intro q
    filter_upwards [hkernel_mem, hkernel_int_zero] with ω hω_mem hω_int
    have hsubG : HasSubgaussianMGF X ((‖b - a‖₊ / 2) ^ 2) (condExpKernel (mΩ := mΩ) μ m ω) :=
      hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
        (hXm.aemeasurable : AEMeasurable X (condExpKernel (mΩ := mΩ) μ m ω)) hω_mem hω_int
    simpa using hsubG.mgf_le q

/-- \label{lem:azuma-inequality}

One-sided Azuma's inequality — the paper's `lem:azuma-inequality` (one-sided form
`P(Yₙ − Y₀ ≥ T) ≤ exp(−T²/(2∑cᵢ²))`). Also the internal helper underlying the
two-sided variant.

Let `(Y_t)` be a martingale w.r.t. a filtration `(ℱ_t)`. Let `n ∈ ℕ` and
suppose there exist constants `c₁, …, cₙ ≥ 0` such that
`|Y_i − Y_{i−1}| ≤ cᵢ` a.s. for every `i ∈ {1, …, n}`. Then for every
`T ≥ 0`,
`P(Yₙ − Y₀ ≥ T) ≤ exp(−T² / (2 ∑_{i=1}^{n} cᵢ²))`.

The `StandardBorelSpace Ω` hypothesis is not in the paper but is required by the Mathlib
sub-Gaussian MGF machinery (`hasCondSubgaussianMGF_of_mem_Icc_of_condExp_eq_zero` and
`measure_sum_ge_le_of_hasCondSubgaussianMGF` both require it for measure disintegration
via `condExpKernel`). In our application `Ω` is finite, so this is automatically satisfied. -/
theorem azuma_inequality
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y : ℕ → Ω → ℝ}
    {ℱ : Filtration ℕ (‹MeasurableSpace Ω›)}
    (hmart : Martingale Y ℱ μ)
    -- Constants c₁, …, cₙ with |Y_i − Y_{i−1}| ≤ cᵢ for i ∈ {1, …, n}
    {n : ℕ} {c : ℕ → ℝ}
    (hc : ∀ i, 1 ≤ i → i ≤ n → ∀ᵐ ω ∂μ, |Y i ω - Y (i - 1) ω| ≤ c i)
    -- T ≥ 0
    {T : ℝ} (hT : 0 ≤ T) :
    -- Conclusion: P(Yₙ − Y₀ ≥ T) ≤ exp(−T² / (2 ∑_{i=1}^{n} cᵢ²))
    (μ {ω | Y n ω - Y 0 ω ≥ T}).toReal ≤
      Real.exp (- T ^ 2 / (2 * Finset.sum (Finset.Icc 1 n) (fun i => c i ^ 2))) := by
  -- Reduce to 0-indexed internals
  have hc' : ∀ i, i < n → ∀ᵐ ω ∂μ, |Y (i + 1) ω - Y i ω| ≤ c (i + 1) := by
    intro i hi
    have h := hc (i + 1) (by omega) (by omega)
    simpa using h
  let D : ℕ → Ω → ℝ
    | 0 => 0
    | i + 1 => Y (i + 1) - Y i
  let v : ℕ → NNReal
    | 0 => 0
    | i + 1 => ⟨c (i + 1) ^ 2, sq_nonneg _⟩
  have hD_adapted : StronglyAdapted ℱ D := by
    intro k
    cases k with
    | zero => simpa [D] using (stronglyMeasurable_zero : StronglyMeasurable[ℱ 0] (0 : Ω → ℝ))
    | succ i =>
      simpa [D] using ((hmart.stronglyMeasurable (i + 1)).sub
        (hmart.stronglyAdapted.stronglyMeasurable_le (i := i) (j := i + 1) (Nat.le_succ i)))
  have hD0 : HasSubgaussianMGF (D 0) 0 μ := by
    simp [D]
  have hD_subG :
      ∀ i < n,
        HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (D (i + 1)) (v (i + 1)) μ := by
    intro i hi
    have hci_nonneg : 0 ≤ c (i + 1) :=
      ((hc' i hi).mono (fun _ h => le_trans (abs_nonneg _) h)).exists.choose_spec
    have hD_meas : Measurable (D (i + 1)) := by
      simpa [D] using ((((hmart.stronglyMeasurable (i + 1)).mono (ℱ.le _)).sub
        ((hmart.stronglyAdapted.stronglyMeasurable_le (i := i) (j := i + 1) (Nat.le_succ i)).mono
          (ℱ.le _))).measurable)
    have hD_bdd : ∀ᵐ ω ∂μ, D (i + 1) ω ∈ Set.Icc (-c (i + 1)) (c (i + 1)) := by
      simpa [D, abs_le, Set.mem_Icc] using hc' i hi
    have hD_zero : μ[D (i + 1) | ℱ i] =ᵐ[μ] 0 := by
      refine (condExp_sub (hmart.integrable (i + 1)) (hmart.integrable i) (ℱ i)).trans ?_
      filter_upwards [hmart.condExp_ae_eq (Nat.le_succ i), hmart.condExp_ae_eq (le_refl i)] with ω h1 h2
      simp [h1, h2]
    have hv_i : ((‖c (i + 1) - -c (i + 1)‖₊ / 2) ^ 2 : NNReal) = v (i + 1) := by
      apply Subtype.ext
      simp [v, hci_nonneg, pow_two, abs_of_nonneg]
    rw [← hv_i]
    exact
      hasCondSubgaussianMGF_of_mem_Icc_of_condExp_eq_zero (μ := μ) (m := ℱ i) (hm := ℱ.le i)
        (a := -c (i + 1)) (b := c (i + 1)) hD_meas hD_bdd hD_zero
  have hsum : ∀ ω, ∑ i ∈ Finset.range (n + 1), D i ω = Y n ω - Y 0 ω := by
    suffices ∀ m ω, ∑ i ∈ Finset.range (m + 1), D i ω = Y m ω - Y 0 ω from this n
    intro m ω; induction m with
    | zero => simp [D]
    | succ m ih => rw [Finset.sum_range_succ, ih]; simp [D]
  have htail := measure_sum_ge_le_of_hasCondSubgaussianMGF (μ := μ) (ℱ := ℱ)
    (Y := D) (cY := v) hD_adapted hD0 (n + 1) hD_subG hT
  have hset : {ω | T ≤ ∑ i ∈ Finset.range (n + 1), D i ω} = {ω | Y n ω - Y 0 ω ≥ T} := by
    ext ω
    simp [hsum ω, ge_iff_le]
  have hvsum' : (((∑ i ∈ Finset.range (n + 1), v i : NNReal) : NNReal) : ℝ) =
      ∑ i ∈ Finset.Icc 1 n, c i ^ 2 := by
    have hvsum : ∀ m, ∑ i ∈ Finset.range (m + 1), (v i : ℝ) = ∑ i ∈ Finset.range m, c (i + 1) ^ 2 := by
      intro m; induction m with
      | zero => simp [v]
      | succ m ih => rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]; simp only [v]; rfl
    have hrange_eq_icc : ∑ i ∈ Finset.range n, c (i + 1) ^ 2 = ∑ i ∈ Finset.Icc 1 n, c i ^ 2 := by
      have : Finset.Icc 1 n = (Finset.range n).map ⟨(· + 1), Nat.succ_injective⟩ := by
        ext i; simp [Finset.mem_map, Finset.mem_range, Finset.mem_Icc]; constructor
        · intro ⟨h1, h2⟩; exact ⟨i - 1, by omega, by omega⟩
        · rintro ⟨j, hj, rfl⟩; omega
      rw [this, Finset.sum_map]; rfl
    simpa using (hvsum n).trans hrange_eq_icc
  rw [measureReal_def, hset, hvsum'] at htail
  exact htail
