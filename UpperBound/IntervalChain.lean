module

public import UpperBound.EmbeddedChain


@[expose] public section
open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators

noncomputable section

/-! ## Embedded Voter Process and Good Processes

Definitions supporting §3.3 of the paper: the embedded volume process obtained
by sampling the volume at stopping times, and the notion of a
`(ξ, ζ)`-good process with stable/unstable steps. -/

namespace VoterModel

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {ℱ : Filtration ℕ (‹MeasurableSpace Ω›)}



/-! ## Absorption time vs embedded process hitting time -/


/-- \label{lem:unstable-jump-from-conductance-on-fiber}

**Fiber-relative variant of `unstable_jump_from_conductance` (L52).**

Let `F ∈ ℱ_{t_j}` be a fiber with `T_j ω = t_j` and `S_{t_j} ω = s_j` on `F`.
Given the F-restricted positive-form unstable hypothesis on `F` (i.e., the
a.e.-on-F negation of `IsStableInterval`), the same bound transports to the
fixed-time filtration value `ℱ_{t_j}` with the outer `vm.volS T_j ω`
rewritten as the constant `vol(t_j, s_j)`.

Bridge content has two pieces:

1. **σ-algebra bridge.** `condExp_stopping_time_ae_eq_restrict_eq_of_countable`
   (Mathlib) gives `E[f | hT_stop.ms] =ᵐ[μ.restrict {T_j = t_j}] E[f | ℱ_{t_j}]`.
   Since `F ⊆ {T_j = t_j}` (by `hF_T`), the bridge holds on `μ.restrict F` too.

2. **Outer-value conversion.** On `F`, `vm.volS T_j ω = vol(t_j, s_j)` via
   `hF_T`, `hF_S`. So `(1/8) * vm.volS T_j ω = (1/8) * vol(t_j, s_j)` on `F`.

The conclusion matches L78's `hjump_F` parameter exactly. -/
theorem unstable_jump_from_conductance_on_fiber
    {Ω : Type*} [MeasurableSpace Ω]
    (G : TemporalGraph V) (vm : TemporalGraph.VoterModelAbstract G 2 Ω)
    -- Realized value s_j and realized time t_j
    (s_j : Finset V) (t_j : ℕ)
    -- Embedded chain parameters
    (Δ : ℕ → ℕ) (j : ℕ)
    -- Fiber F: measurable in ℱ_{t_j}, with T_j = t_j and S_{t_j} = s_j on F
    (F : Set Ω)
    (hF_meas : MeasurableSet[vm.ℱ t_j] F)
    (hF_T : ∀ ω ∈ F, embeddedChainTime G vm Δ j ω = t_j)
    (hF_S : ∀ ω ∈ F, vm.S t_j ω = s_j)
    -- Stopping-time certificate for T_j (matches L52's hT_stop)
    (hT_stop : IsStoppingTime vm.ℱ
        (fun ω => (embeddedChainTime G vm Δ j ω : ℕ∞)))
    -- F-restricted positive unstable hypothesis (in stopped-σ-alg form,
    -- with outer RHS in `vm.volS T_j ω` form — the a.e.-on-F negation
    -- of `IsStableInterval G vm Δ (1/8) j hT_stop`)
    (hUnstable_F : ∀ᵐ ω ∂((vm.μ : Measure _).restrict F),
        ((vm.μ : Measure _)[fun ω' =>
            |vm.volS (embeddedChainTime G vm Δ (j + 1) ω') ω' -
              vm.volS (embeddedChainTime G vm Δ j ω') ω'|
            | hT_stop.measurableSpace]) ω
          ≥ (1 / 8 : ℝ) * vm.volS (embeddedChainTime G vm Δ j ω) ω) :
    -- Conclusion: matches L78's `hjump_F` form exactly
    ∀ᵐ ω ∂((vm.μ : Measure _).restrict F),
      ((vm.μ : Measure _)[fun ω' =>
          |vm.volS (embeddedChainTime G vm Δ (j + 1) ω') ω' -
            vm.volS (embeddedChainTime G vm Δ j ω') ω'| | vm.ℱ t_j]) ω
        ≥ (1 / 8 : ℝ) * (TemporalGraph.volume G t_j s_j : ℝ) := by
  classical
  -- The integrand `f` whose conditional expectation appears in the conclusion.
  set f : Ω → ℝ := fun ω' =>
    |vm.volS (embeddedChainTime G vm Δ (j + 1) ω') ω' -
      vm.volS (embeddedChainTime G vm Δ j ω') ω'| with hf_def
  -- Instances needed for `condExp_stopping_time_ae_eq_restrict_eq_of_countable`.
  haveI : SigmaFiniteFiltration vm.μ vm.ℱ := inferInstance
  haveI : SigmaFinite ((vm.μ : Measure _).trim hT_stop.measurableSpace_le) := inferInstance
  -- ── Piece 1: σ-alg bridge ────────────────────────────────────────────────
  -- `condExp_stopping_time_ae_eq_restrict_eq_of_countable` (Mathlib) supplies:
  -- E[f | hT_stop.ms] =ᵐ[μ.restrict {T_j = t_j}] E[f | ℱ_{t_j}]
  set Eset : Set Ω := {ω | (embeddedChainTime G vm Δ j ω : ℕ∞) = (t_j : ℕ∞)} with hEset_def
  have h_bridge_on_E :
      (vm.μ : Measure _)[f | hT_stop.measurableSpace] =ᵐ[(vm.μ : Measure _).restrict Eset]
        (vm.μ : Measure _)[f | (vm.ℱ t_j : MeasurableSpace Ω)] :=
    condExp_stopping_time_ae_eq_restrict_eq_of_countable hT_stop t_j
  -- F ⊆ Eset, hence μ.restrict F ≤ μ.restrict Eset and a.e. on E ⇒ a.e. on F.
  have hF_subset_E : F ⊆ Eset := by
    intro ω hω
    show (embeddedChainTime G vm Δ j ω : ℕ∞) = (t_j : ℕ∞)
    exact_mod_cast hF_T ω hω
  have h_restrict_le : (vm.μ : Measure _).restrict F ≤ (vm.μ : Measure _).restrict Eset :=
    Measure.restrict_mono hF_subset_E le_rfl
  have h_bridge_on_F :
      (vm.μ : Measure _)[f | hT_stop.measurableSpace] =ᵐ[(vm.μ : Measure _).restrict F]
        (vm.μ : Measure _)[f | (vm.ℱ t_j : MeasurableSpace Ω)] :=
    h_bridge_on_E.filter_mono (MeasureTheory.ae_mono h_restrict_le)
  -- ── Piece 2: outer-value conversion on F ─────────────────────────────────
  -- On F, vm.volS T_j ω = vol(t_j, s_j); transport this to a.e.-on-F.
  have hF_meas_top : MeasurableSet F := vm.ℱ.le t_j _ hF_meas
  have h_volS_on_F : ∀ ω ∈ F,
      vm.volS (embeddedChainTime G vm Δ j ω) ω = (TemporalGraph.volume G t_j s_j : ℝ) := by
    intro ω hω
    show (TemporalGraph.volume G (embeddedChainTime G vm Δ j ω)
            (vm.S (embeddedChainTime G vm Δ j ω) ω) : ℝ) =
        (TemporalGraph.volume G t_j s_j : ℝ)
    rw [hF_T ω hω, hF_S ω hω]
  have h_volS_ae :
      ∀ᵐ ω ∂((vm.μ : Measure _).restrict F),
        vm.volS (embeddedChainTime G vm Δ j ω) ω = (TemporalGraph.volume G t_j s_j : ℝ) := by
    rw [ae_restrict_iff' hF_meas_top]
    exact ae_of_all _ h_volS_on_F
  -- ── Combine: rewrite hUnstable_F using both pieces ───────────────────────
  filter_upwards [hUnstable_F, h_bridge_on_F, h_volS_ae] with ω hU hBr hV
  -- hU  : E[f | hT_stop.ms] ω ≥ (1/8) * vm.volS T_j ω
  -- hBr : E[f | hT_stop.ms] ω = E[f | vm.ℱ t_j] ω
  -- hV  : vm.volS T_j ω = vol(t_j, s_j)
  rw [hBr] at hU
  rw [hV] at hU
  exact hU


end VoterModel
