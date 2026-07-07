module

public import UpperBound.MultiOpinion.Metaphase
import Mathlib.Algebra.Order.Star.Real


/-! ## §3.4 multi-opinion: the per-metaphase 2/3 bound (Tier C)

This file assembles the core probabilistic content of the §3.4 "Proof of Claim"
(`sections/3.4_multi_opinion.tex`, eqs `multi-opinion-0a … 1` and
`small-1/small-2`): conditioned on being inside a metaphase, the probability that
the metaphase fails to end within `ξ_α` further phases is at most `2/3`.

The argument has three pieces, mirroring the paper:

* **C1 (`small_opinions_card_ge`, eq `small-1`).** A pure counting fact: the
  number of *small* opinions present at time `s` is at least
  `|𝒪(s)| − (2/τ)|O_α|`, where `τm/|O_α|` (with `τ = 14/3`) is the smallness
  volume threshold.  Each non-small opinion has volume `> τm/|O_α|`; if there
  were more than `(2/τ)|O_α|` of them their total volume would exceed
  `Vol(V) = 2m`.

* **C2 (`cond_markov_sum_indicators`, eq `1`).** A conditional Markov inequality
  for the nonnegative sum `Y = ∑_{q ∈ O⁻} X_q`: pointwise
  `𝟙{Y ≥ c} ≤ Y/c`, so by `condExp_mono` and linearity of conditional
  expectation, `μ[𝟙{Y ≥ c} | ℱ_s] ≤ (∑_{q ∈ O⁻} μ[X_q | ℱ_s]) / c`.

* **C3 (`per_metaphase_two_thirds`, eqs `0a–1`).** The glue: combining C1, C2,
  the per-opinion small bound `μ[X_q | ℱ_s] ≤ 1/2` (the output of
  `condExp_Xq_le_half`) and the event inclusion
  `{R_{α+1} > r + ξ_α} ∩ D ⊆ {∑_{q ∈ O⁻} X_q ≥ c}`, one obtains
  `μ[𝟙{R_{α+1} > r + ξ_α} | ℱ_{t_r}] ≤ 2/3` on the conditioning event `D`.

## FORMALIZATION NOTES (Lean-specific structural choices)

* **Fixed `O⁻`, `O_α` via pinning hypotheses.** The small-opinion set `O⁻` and
  the opinion count `|𝒪(s)|` are random (depend on `ω`).  Rather than sum over a
  random index set, `per_metaphase_two_thirds` is parameterized by a *fixed*
  `Os, Oα : Finset (Fin κ)` and a fixed `Ocard : ℕ`, together with hypotheses
  pinning them on the `ℱ_s`-measurable conditioning event `D`
  (`hOspin`, `hOpin`).  This is exactly the paper's "let `O_α` be the value …
  determined by `H_{t_r}`".

* **Per-opinion bound and the event inclusion as hypotheses.** The bound
  `μ[X_q | ℱ_s] ≤ 1/2` on `D` (`hsmallbnd`) is *literally* the conclusion of
  `condExp_Xq_le_half` once `D ⊆ E_s^q`; supplying it as a hypothesis keeps the
  threshold reconciliation (smallness ⇒ `E_s^q`-membership, eq `small-2`) in the
  Tier-D layer that instantiates this lemma.  Likewise the inclusion `hED`
  packages eqs `0a–0c` (`{R_{α+1} > r + ξ} ⊆ {|𝒪(t_{r+ξ})| ≥ ρ|O_α|} ⊆
  {∑_{q ∈ O⁻} X_q ≥ c}`, with shrink factor `ρ = 6/7`), whose proof is
  deterministic but tangled with the metaphase definition.

* **`D`-localized conditional monotonicity.** Conditional expectation is not
  monotone "on a set", so the restriction to `D` is threaded through
  `condExp_indicator`: `μ[𝟙_E | ℱ_s] =ᵐ[μ|_D] μ[D.indicator 𝟙_E | ℱ_s]`, and the
  global `condExp_mono` is applied to the `D`-localized indicators.

## Main results
- `volume_opinionSet_eq_univ` — the volumes of the present opinions partition
  `Vol(V)`.
- `small_opinions_card_ge` — C1.
- `cond_markov_sum_indicators` — C2.
- `per_metaphase_two_thirds` — C3, the per-metaphase 2/3 bound.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Classical ENNReal

noncomputable section

namespace TemporalGraph

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
variable {κ : ℕ} [NeZero κ] {Ω : Type*} [mΩ : MeasurableSpace Ω] {G : TemporalGraph V}

/-! ### C1: the small-opinion counting bound -/

/-- The volumes of the present opinions partition the total volume:
`∑_{q ∈ 𝒪(s)} Vol(phiQ q (ξ_s)) = Vol(V)`.  Indeed the sets `phiQ q (ξ_s)`,
`q ∈ 𝒪(s)`, are the nonempty fibers of `ξ_s` and so partition `V`. -/
theorem volume_opinionSet_eq_univ (vm : VoterModelAbstract G κ Ω) (s : ℕ) (ω : Ω) :
    ∑ q ∈ vm.opinionSet s ω, TemporalGraph.volume G s (VoterModel.phiQ q (vm.ξ s ω))
      = TemporalGraph.volume G s Finset.univ := by
  simp only [TemporalGraph.volume, SimpleGraph.volume, VoterModel.phiQ, VoterModelAbstract.opinionSet]
  exact Finset.sum_fiberwise_of_maps_to
    (fun v _ => Finset.mem_image_of_mem _ (Finset.mem_univ v))
    (fun v => (G.snapshot s).degree v)

/-- \label{eq:multi-opinion-small-1}

**§3.4 small-opinion counting bound (Tier C, eq `small-1`).**

The number of *small* opinions at time `s` (those `q ∈ 𝒪(s)` with
`Vol(phiQ q (ξ_s)) ≤ τm/|O_α|`, volume threshold `τ = 14/3`) is at least
`|𝒪(s)| − (2/τ)|O_α| = |𝒪(s)| − (3/7)|O_α|`.

The hypothesis `hvol : Vol(V) ≤ 2m` is the handshake bound; `0 < m` and
`0 < |O_α|` make the threshold `τm/|O_α|` meaningful.  The proof is the
contrapositive volume count of the paper: each non-small opinion has volume
`> τm/|O_α|`, and `(#non-small) · τm/|O_α| ≤ Vol(V) ≤ 2m` forces
`#non-small ≤ (2/τ)|O_α|`. -/
theorem small_opinions_card_ge (vm : VoterModelAbstract G κ Ω) (s : ℕ)
    (Oα : Finset (Fin κ)) (m : ℕ) (ω : Ω)
    (hm : 0 < m) (hOα : 0 < Oα.card)
    (hvol : (TemporalGraph.volume G s Finset.univ : ℝ) ≤ 2 * m) :
    ((vm.opinionSet s ω).card : ℝ) - 3 * (Oα.card : ℝ) / 7
      ≤ (vm.smallOpinions s Oα m ω).card := by
  classical
  set O := vm.opinionSet s ω with hO
  set t0 : ℝ := 14 * (m : ℝ) / (3 * (Oα.card : ℝ)) with ht0
  set vol : Fin κ → ℝ :=
    fun q => (TemporalGraph.volume G s (VoterModel.phiQ q (vm.ξ s ω)) : ℝ) with hvolf
  set Os := vm.smallOpinions s Oα m ω with hOs
  have hOs_def : Os = O.filter (fun q => vol q ≤ t0) := rfl
  set NS := O.filter (fun q => ¬ vol q ≤ t0) with hNS
  -- |O| = |Os| + |NS|
  have hcard_split : O.card = Os.card + NS.card := by
    rw [hOs_def, hNS]
    exact (Finset.card_filter_add_card_filter_not _).symm
  -- partition of the total volume, cast to ℝ
  have hpart : ∑ q ∈ O, vol q = (TemporalGraph.volume G s Finset.univ : ℝ) := by
    rw [hvolf]
    rw [show (∑ q ∈ O, ((TemporalGraph.volume G s (VoterModel.phiQ q (vm.ξ s ω)) : ℝ)))
          = ((∑ q ∈ O, TemporalGraph.volume G s (VoterModel.phiQ q (vm.ξ s ω)) : ℕ) : ℝ) by
        rw [Nat.cast_sum]]
    rw [hO, volume_opinionSet_eq_univ vm s ω]
  have hOαR : (0 : ℝ) < Oα.card := by exact_mod_cast hOα
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  -- lower bound: |NS| · t0 ≤ ∑_{NS} vol
  have hlb : (NS.card : ℝ) * t0 ≤ ∑ q ∈ NS, vol q := by
    have h := Finset.card_nsmul_le_sum NS vol t0 (fun q hq => ?_)
    · simpa [nsmul_eq_mul] using h
    · rw [hNS, Finset.mem_filter] at hq
      exact le_of_lt (not_le.mp hq.2)
  -- upper bound: ∑_{NS} vol ≤ Vol(V)
  have hub : ∑ q ∈ NS, vol q ≤ (TemporalGraph.volume G s Finset.univ : ℝ) := by
    rw [← hpart]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · rw [hNS]; exact Finset.filter_subset _ _
    · intro q _ _; rw [hvolf]; positivity
  have hcombine : (NS.card : ℝ) * t0 ≤ 2 * (m : ℝ) := hlb.trans (hub.trans hvol)
  -- clear the denominator
  have h3OαR : (0 : ℝ) < 3 * (Oα.card : ℝ) := by linarith
  rw [ht0, ← mul_div_assoc] at hcombine
  have hcleared : (NS.card : ℝ) * (14 * m) ≤ 2 * m * (3 * (Oα.card : ℝ)) :=
    (div_le_iff₀ h3OαR).mp hcombine
  have h14 : (NS.card : ℝ) * 14 ≤ 6 * (Oα.card : ℝ) := by
    have hc : (NS.card : ℝ) * 14 * m ≤ 6 * (Oα.card : ℝ) * m := by nlinarith [hcleared]
    exact le_of_mul_le_mul_right hc hmR
  have hsplitR : (O.card : ℝ) = (Os.card : ℝ) + (NS.card : ℝ) := by exact_mod_cast hcard_split
  rw [hsplitR]
  linarith [h14]

/-! ### C2: conditional Markov inequality for a sum of indicators -/

/-- \label{eq:multi-opinion-1}

**§3.4 conditional Markov inequality for indicator sums (Tier C, eq `1`).**

For a fixed finite set `Os` of opinions, the nonnegative sum
`Y = ∑_{q ∈ Os} X_q (s+K)` satisfies, for any threshold `c > 0`,

  `μ[ 𝟙{Y ≥ c} | ℱ_s ] ≤ (∑_{q ∈ Os} μ[X_q (s+K) | ℱ_s]) / c`   a.e.

The proof is the pointwise Markov bound `𝟙{Y ≥ c} ≤ Y/c` (valid since `Y ≥ 0`
and `c > 0`), followed by `condExp_mono`, `condExp_smul` and `condExp_finset_sum`. -/
theorem cond_markov_sum_indicators (vm : VoterModelAbstract G κ Ω) (s K : ℕ)
    (Os : Finset (Fin κ)) (c : ℝ) (hc : 0 < c) :
    (vm.μ : Measure Ω)[Set.indicator {ω | c ≤ ∑ q ∈ Os, vm.Xq q (s + K) ω} (fun _ => (1 : ℝ))
          | (vm.ℱ s : MeasurableSpace Ω)]
      ≤ᵐ[(vm.μ : Measure Ω)]
        (fun ω => (∑ q ∈ Os, (vm.μ : Measure Ω)[vm.Xq q (s + K) | (vm.ℱ s : MeasurableSpace Ω)] ω) / c) := by
  -- integrability of each indicator-like building block
  have hXqint : ∀ q, Integrable (vm.Xq q (s + K)) vm.μ := by
    intro q
    refine Integrable.mono' (integrable_const (1 : ℝ))
      ((vm.Xq_measurable q (s + K)).mono (vm.ℱ.le (s + K)) le_rfl).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    rw [VoterModelAbstract.Xq]; split_ifs <;> simp
  have hXq_meas : ∀ q, Measurable (vm.Xq q (s + K)) :=
    fun q => (vm.Xq_measurable q (s + K)).mono (vm.ℱ.le (s + K)) le_rfl
  have hYmeas : Measurable (fun ω => ∑ q ∈ Os, vm.Xq q (s + K) ω) :=
    Finset.measurable_sum _ (fun q _ => hXq_meas q)
  have hYint : Integrable (fun ω => ∑ q ∈ Os, vm.Xq q (s + K) ω) vm.μ :=
    integrable_finsetSum Os (fun q _ => hXqint q)
  have hSmeas : MeasurableSet {ω | c ≤ ∑ q ∈ Os, vm.Xq q (s + K) ω} :=
    measurableSet_le measurable_const hYmeas
  have hIndint : Integrable
      (Set.indicator {ω | c ≤ ∑ q ∈ Os, vm.Xq q (s + K) ω} (fun _ => (1 : ℝ))) vm.μ :=
    (integrable_const (1 : ℝ)).indicator hSmeas
  have hYcint : Integrable (fun ω => (∑ q ∈ Os, vm.Xq q (s + K) ω) / c) vm.μ :=
    hYint.div_const c
  -- pointwise Markov bound
  have hpt : ∀ ω, Set.indicator {ω | c ≤ ∑ q ∈ Os, vm.Xq q (s + K) ω} (fun _ => (1 : ℝ)) ω
      ≤ (∑ q ∈ Os, vm.Xq q (s + K) ω) / c := by
    intro ω
    have hYnn : 0 ≤ ∑ q ∈ Os, vm.Xq q (s + K) ω :=
      Finset.sum_nonneg (fun q _ => by rw [VoterModelAbstract.Xq]; split_ifs <;> norm_num)
    rw [Set.indicator_apply]
    split_ifs with hmem
    · rw [Set.mem_setOf_eq] at hmem
      rw [le_div_iff₀ hc, one_mul]; exact hmem
    · exact div_nonneg hYnn hc.le
  -- condExp monotonicity
  have hmono : (vm.μ : Measure Ω)[Set.indicator {ω | c ≤ ∑ q ∈ Os, vm.Xq q (s + K) ω} (fun _ => (1 : ℝ)) | (vm.ℱ s : MeasurableSpace Ω)]
      ≤ᵐ[(vm.μ : Measure Ω)] (vm.μ : Measure Ω)[(fun ω => (∑ q ∈ Os, vm.Xq q (s + K) ω) / c) | (vm.ℱ s : MeasurableSpace Ω)] :=
    condExp_mono hIndint hYcint (ae_of_all _ hpt)
  -- rewrite the right conditional expectation via `condExp_smul` and `condExp_finsetSum`
  have hce : (vm.μ : Measure Ω)[(fun ω => (∑ q ∈ Os, vm.Xq q (s + K) ω) / c) | (vm.ℱ s : MeasurableSpace Ω)]
      =ᵐ[(vm.μ : Measure Ω)]
        (fun ω => (∑ q ∈ Os, (vm.μ : Measure Ω)[vm.Xq q (s + K) | (vm.ℱ s : MeasurableSpace Ω)] ω) / c) := by
    have hfun : (fun ω => (∑ q ∈ Os, vm.Xq q (s + K) ω) / c)
        = c⁻¹ • (∑ q ∈ Os, vm.Xq q (s + K)) := by
      funext ω
      simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, div_eq_inv_mul]
    rw [hfun]
    have hsmul := condExp_smul (μ := (vm.μ : Measure Ω)) c⁻¹ (∑ q ∈ Os, vm.Xq q (s + K))
      (vm.ℱ s : MeasurableSpace Ω)
    have hsum := condExp_finsetSum (μ := (vm.μ : Measure Ω)) (f := fun q => vm.Xq q (s + K))
      (s := Os) (fun q _ => hXqint q) (vm.ℱ s : MeasurableSpace Ω)
    filter_upwards [hsmul, hsum] with ω h1 h2
    rw [h1]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [h2, Finset.sum_apply, div_eq_inv_mul]
  exact hmono.trans hce.le

/-! ### C3: the per-metaphase 2/3 bound -/

/-- \label{eq:multi-opinion-goal}

**§3.4 per-metaphase 2/3 bound (Tier C, eqs `0a–1`).**

Inside metaphase `α` (the `ℱ_{t_r}`-measurable conditioning event `D`, on which
the opinion count `|𝒪(t_r)|` equals `Ocard` and the small opinions equal `Os`),
the conditional probability that the metaphase fails to end within `ξ` further
phases — i.e. that `R_{α+1} > r + ξ` — is at most `2/3`.

Here `c = ρ|O_α| − Ocard + |Os|` (shrink factor `ρ = 6/7`) is the Markov
threshold of eq `0c`.  The
hypotheses are: the handshake bound `hvol`; `hOle : |𝒪(t_r)| ≤ |O_α|` (opinions
only die); the per-opinion small bound `hsmallbnd` (the conclusion of
`condExp_Xq_le_half`); and the event inclusion `hED` (eqs `0a–0c`).  See the
file-level FORMALIZATION NOTES. -/
theorem per_metaphase_two_thirds (vm : VoterModelAbstract G κ Ω)
    (B : ℝ) (m d_min : ℕ) (Δ : ℕ → ℕ) (φ : ℕ → ℝ)
    (α r ξ s K : ℕ)
    (Oα Os : Finset (Fin κ)) (Ocard : ℕ)
    -- conditioning event `D` (intended: `{R_α ≤ r < R_{α+1}}`, pinning `O_α`, `𝒪(t_r)`)
    (D : Set Ω) (hDmeas : @MeasurableSet Ω (vm.ℱ s) D)
    (hOspin : ∀ ω ∈ D, vm.smallOpinions s Oα m ω = Os)
    (hOpin : ∀ ω ∈ D, (vm.opinionSet s ω).card = Ocard)
    -- numeric side conditions
    (hm : 0 < m) (hOα : 0 < Oα.card)
    (hvol : (TemporalGraph.volume G s Finset.univ : ℝ) ≤ 2 * m)
    (hOle : (Ocard : ℝ) ≤ Oα.card)
    -- per-opinion small bound (output of `condExp_Xq_le_half`)
    (hsmallbnd : ∀ q ∈ Os,
      (vm.μ : Measure Ω)[vm.Xq q (s + K) | (vm.ℱ s : MeasurableSpace Ω)]
        ≤ᵐ[(vm.μ : Measure Ω).restrict D] (fun _ => (1 / 2 : ℝ)))
    -- event-inclusion bridge (eqs `0a–0c`), with `E = {R_{α+1} > r + ξ}`
    (hEmeas : MeasurableSet {ω | r + ξ < vm.metaphase B m d_min Δ φ (α + 1) ω})
    (hED : ∀ᵐ ω ∂(vm.μ : Measure Ω), ω ∈ {ω | r + ξ < vm.metaphase B m d_min Δ φ (α + 1) ω} ∩ D →
      ((6 : ℝ) / 7 * Oα.card - Ocard + Os.card)
        ≤ ∑ q ∈ Os, vm.Xq q (s + K) ω) :
    (vm.μ : Measure Ω)[Set.indicator {ω | r + ξ < vm.metaphase B m d_min Δ φ (α + 1) ω} (fun _ => (1 : ℝ))
          | (vm.ℱ s : MeasurableSpace Ω)]
      ≤ᵐ[(vm.μ : Measure Ω).restrict D] (fun _ => (2 / 3 : ℝ)) := by
  set E := {ω | r + ξ < vm.metaphase B m d_min Δ φ (α + 1) ω} with hEdef
  set c : ℝ := (6 : ℝ) / 7 * Oα.card - Ocard + Os.card with hc_def
  set Sset := {ω | c ≤ ∑ q ∈ Os, vm.Xq q (s + K) ω} with hSdef
  -- `D` is `mΩ`-measurable
  have hDμ : MeasurableSet D := vm.ℱ.le s _ hDmeas
  rcases Set.eq_empty_or_nonempty D with hDe | ⟨ω₀, hω₀⟩
  · subst hDe; simp only [Measure.restrict_empty, ae_zero]; exact Filter.eventually_bot
  -- C1 counting on `D`
  have hOαR : (0 : ℝ) < Oα.card := by exact_mod_cast hOα
  have hA : (Ocard : ℝ) - 3 * (Oα.card : ℝ) / 7 ≤ (Os.card : ℝ) := by
    have h := small_opinions_card_ge vm s Oα m ω₀ hm hOα hvol
    rw [hOspin ω₀ hω₀, hOpin ω₀ hω₀] at h
    exact h
  -- `c > 0`
  have hc : 0 < c := by rw [hc_def]; nlinarith [hA, hOαR]
  -- abbreviations
  set IE := Set.indicator E (fun _ => (1 : ℝ)) with hIE
  set IS := Set.indicator Sset (fun _ => (1 : ℝ)) with hIS
  -- integrability of the indicators
  have hXq_meas : ∀ q, Measurable (vm.Xq q (s + K)) :=
    fun q => (vm.Xq_measurable q (s + K)).mono (vm.ℱ.le (s + K)) le_rfl
  have hSmeas : MeasurableSet Sset :=
    measurableSet_le measurable_const (Finset.measurable_sum _ (fun q _ => hXq_meas q))
  have hIEint : Integrable IE vm.μ := (integrable_const (1 : ℝ)).indicator hEmeas
  have hISint : Integrable IS vm.μ := (integrable_const (1 : ℝ)).indicator hSmeas
  have hDIEint : Integrable (D.indicator IE) vm.μ := hIEint.indicator hDμ
  have hDISint : Integrable (D.indicator IS) vm.μ := hISint.indicator hDμ
  -- pointwise domination of the `D`-localized indicators
  have hdom : (D.indicator IE) ≤ᵐ[(vm.μ : Measure Ω)] (D.indicator IS) := by
    filter_upwards [hED] with ω hED_ω
    by_cases hD : ω ∈ D
    · rw [Set.indicator_of_mem hD, Set.indicator_of_mem hD, hIE, hIS]
      by_cases hE : ω ∈ E
      · have hmem : ω ∈ Sset := hED_ω ⟨hE, hD⟩
        rw [Set.indicator_of_mem hE, Set.indicator_of_mem hmem]
      · rw [Set.indicator_of_notMem hE]
        exact Set.indicator_nonneg (fun _ _ => by norm_num) ω
    · rw [Set.indicator_of_notMem hD, Set.indicator_of_notMem hD]
  have hmono : (vm.μ : Measure Ω)[D.indicator IE | (vm.ℱ s : MeasurableSpace Ω)] ≤ᵐ[(vm.μ : Measure Ω)] (vm.μ : Measure Ω)[D.indicator IS | (vm.ℱ s : MeasurableSpace Ω)] :=
    condExp_mono hDIEint hDISint hdom
  -- `D.indicator g =ᵐ[μ|_D] g`
  have hindD : ∀ g : Ω → ℝ, D.indicator g =ᵐ[(vm.μ : Measure Ω).restrict D] g :=
    fun g => (ae_restrict_iff' hDμ).mpr (ae_of_all _ (fun ω hω => Set.indicator_of_mem hω g))
  -- localize the two conditional expectations to `D`
  have e1 : (vm.μ : Measure Ω)[IE | (vm.ℱ s : MeasurableSpace Ω)]
      =ᵐ[(vm.μ : Measure Ω).restrict D] (vm.μ : Measure Ω)[D.indicator IE | (vm.ℱ s : MeasurableSpace Ω)] := by
    filter_upwards [hindD ((vm.μ : Measure Ω)[IE | (vm.ℱ s : MeasurableSpace Ω)]),
      ae_restrict_of_ae (condExp_indicator hIEint hDmeas)] with ω hω hh
    rw [← hω, hh]
  have e2 : (vm.μ : Measure Ω)[D.indicator IS | (vm.ℱ s : MeasurableSpace Ω)]
      =ᵐ[(vm.μ : Measure Ω).restrict D] (vm.μ : Measure Ω)[IS | (vm.ℱ s : MeasurableSpace Ω)] := by
    filter_upwards [hindD ((vm.μ : Measure Ω)[IS | (vm.ℱ s : MeasurableSpace Ω)]),
      ae_restrict_of_ae (condExp_indicator hISint hDmeas)] with ω hω hh
    rw [hh, hω]
  -- C2 and the sum bound on `D`
  have hC2 : (vm.μ : Measure Ω)[IS | (vm.ℱ s : MeasurableSpace Ω)]
      ≤ᵐ[(vm.μ : Measure Ω).restrict D] (fun ω => (∑ q ∈ Os, (vm.μ : Measure Ω)[vm.Xq q (s + K) | (vm.ℱ s : MeasurableSpace Ω)] ω) / c) :=
    ae_restrict_of_ae (cond_markov_sum_indicators vm s K Os c hc)
  have hall : ∀ᵐ ω ∂((vm.μ : Measure Ω).restrict D), ∀ q ∈ Os, (vm.μ : Measure Ω)[vm.Xq q (s + K) | (vm.ℱ s : MeasurableSpace Ω)] ω ≤ (1 / 2 : ℝ) :=
    (Finset.eventually_all Os).mpr (fun q hq => hsmallbnd q hq)
  have hsumbnd : (fun ω => ∑ q ∈ Os, (vm.μ : Measure Ω)[vm.Xq q (s + K) | (vm.ℱ s : MeasurableSpace Ω)] ω)
      ≤ᵐ[(vm.μ : Measure Ω).restrict D] (fun _ => (Os.card : ℝ) / 2) := by
    filter_upwards [hall] with ω hω
    calc ∑ q ∈ Os, (vm.μ : Measure Ω)[vm.Xq q (s + K) | (vm.ℱ s : MeasurableSpace Ω)] ω
        ≤ ∑ _q ∈ Os, (1 / 2 : ℝ) := Finset.sum_le_sum (fun q hq => hω q hq)
      _ = (Os.card : ℝ) / 2 := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hfinal : (fun ω => (∑ q ∈ Os, (vm.μ : Measure Ω)[vm.Xq q (s + K) | (vm.ℱ s : MeasurableSpace Ω)] ω) / c)
      ≤ᵐ[(vm.μ : Measure Ω).restrict D] (fun _ => (2 / 3 : ℝ)) := by
    filter_upwards [hsumbnd] with ω hω
    rw [div_le_iff₀ hc]
    calc ∑ q ∈ Os, (vm.μ : Measure Ω)[vm.Xq q (s + K) | (vm.ℱ s : MeasurableSpace Ω)] ω
        ≤ (Os.card : ℝ) / 2 := hω
      _ ≤ 2 / 3 * c := by rw [hc_def]; nlinarith [hA, hOle]
  -- assemble
  calc (vm.μ : Measure Ω)[IE | (vm.ℱ s : MeasurableSpace Ω)]
      =ᵐ[(vm.μ : Measure Ω).restrict D] (vm.μ : Measure Ω)[D.indicator IE | (vm.ℱ s : MeasurableSpace Ω)] := e1
    _ ≤ᵐ[(vm.μ : Measure Ω).restrict D] (vm.μ : Measure Ω)[D.indicator IS | (vm.ℱ s : MeasurableSpace Ω)] := ae_restrict_of_ae hmono
    _ =ᵐ[(vm.μ : Measure Ω).restrict D] (vm.μ : Measure Ω)[IS | (vm.ℱ s : MeasurableSpace Ω)] := e2
    _ ≤ᵐ[(vm.μ : Measure Ω).restrict D] (fun ω => (∑ q ∈ Os, (vm.μ : Measure Ω)[vm.Xq q (s + K) | (vm.ℱ s : MeasurableSpace Ω)] ω) / c) := hC2
    _ ≤ᵐ[(vm.μ : Measure Ω).restrict D] (fun _ => (2 / 3 : ℝ)) := hfinal

end TemporalGraph
