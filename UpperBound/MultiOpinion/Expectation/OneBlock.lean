module

import UpperBound.MultiOpinion.MetaphaseClaim
import UpperBound.MultiOpinion.CondExp
public import TemporalGraph.Degree
import VoterProcess.Expectation
public import TemporalGraph.Conductance
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Positivity.Finset
public import UpperBound.MultiOpinion.Expectation.Metaphase
import TemporalGraph.Basic
import UpperBound.MultiOpinion.Expectation.GeomTail

/-! ## Main results

The single-block obligations of §3.4 (`VoterModelAbstract.one_block_*`): from the
per-pinned-leaf threshold bounds (`one_block_hsmallbnd`, `one_block_hED`, …) to the
random-index sum (`one_block_random_index`), the tail bound (`htail_of_one_block`),
and the conditional metaphase-increment bound (`metaphase_increment_le_final`). -/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Classical ENNReal

noncomputable section

namespace TemporalGraph

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
variable {κ : ℕ} [NeZero κ] {G : TemporalGraphFixedDegree V}
variable {Ω : Type*} [MeasurableSpace Ω] (vm : VoterModelAbstract G.toTemporalGraph κ Ω)
  (B : ℝ) (m d_min : ℕ) (b : ℝ) (Δ : ℕ → ℕ) (φ : ℕ → ℝ)

/-- **Per-piece converter.** A conditional-expectation bound on `μ.restrict D`
turns into a set-integral bound on `D`: if `μ[f | mσ] ≤ C` a.e. on `D` and `D` is
`mσ`-measurable, then `∫_D f ≤ C·μ(D)`. This packages the `setIntegral_condExp`
step used to pass from `per_metaphase_two_thirds` (a `μ.restrict D` bound) to the
per-pinned-piece set-integral bound feeding the `one_block_random_index` sum. -/
theorem setIntegral_le_of_condExp_le_restrict {Ω : Type*} {mσ m₀ : MeasurableSpace Ω}
    (hmσ : mσ ≤ m₀) {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : Integrable f μ)
    {D : Set Ω} (hD : MeasurableSet[mσ] D) {C : ℝ}
    (hle : μ[f | mσ] ≤ᵐ[μ.restrict D] (fun _ => C)) :
    ∫ ω in D, f ω ∂μ ≤ C * (μ D).toReal := by
  calc ∫ ω in D, f ω ∂μ
      = ∫ ω in D, (μ[f | mσ]) ω ∂μ := (setIntegral_condExp hmσ hf hD).symm
    _ ≤ ∫ _ω in D, C ∂μ := integral_mono_ae integrable_condExp.integrableOn
          (integrable_const C).integrableOn hle
    _ = C * (μ D).toReal := by rw [setIntegral_const, smul_eq_mul, mul_comm]; rfl

/-- The minority set has volume at most that of the set itself (it is the smaller
of `S` and its complement). -/
theorem volume_minoritySet_le (t : ℕ) (Sset : Finset V) :
    (G.snapshot t).volume (VoterModel.minoritySet G.toTemporalGraph t Sset)
      ≤ (G.snapshot t).volume Sset := by
  unfold VoterModel.minoritySet
  split
  · exact le_rfl
  · exact (not_le.mp ‹_›).le

omit [NeZero κ] in
/-- **Obligation 3 threshold kernel.** On a leaf where opinion `q` is *small*
(`Vol_s(phiQ q ξ) ≤ 6m/|Oα|`), the `condExp_Xq_le_half` threshold
`b·(Vol₀(minoritySet(phiQ q ξ))/d_min + log(1+…))` is at most `ξ_α − 1`.
Combines `volume_minoritySet_le`, time-invariance `volume_fixed`, and the green
arithmetic kernel `xiAlpha_sub_one_ge`. -/
theorem threshold_le_of_small
    (hd_pos : 0 < d_min) (hb : 0 ≤ b) (s : ℕ) (Oα : Finset (Fin κ)) (hOα : 0 < Oα.card)
    (q : Fin κ) (ξcfg : V → Fin κ)
    (hsmall : ((G.snapshot s).volume (VoterModel.phiQ q ξcfg) : ℝ)
      ≤ 14 * (m : ℝ) / (3 * (Oα.card : ℝ))) :
    b * (((G.snapshot 0).volume
              (VoterModel.minoritySet G.toTemporalGraph 0 (VoterModel.phiQ q ξcfg)) : ℝ)
            / (d_min : ℝ)
          + Real.log (1 + ((G.snapshot 0).volume
              (VoterModel.minoritySet G.toTemporalGraph 0 (VoterModel.phiQ q ξcfg)) : ℝ)))
      ≤ (TemporalGraph.xiAlpha b m d_min Oα.card : ℝ) - 1 := by
  set x := (TemporalGraph.volume G.toTemporalGraph 0
    (VoterModel.minoritySet G.toTemporalGraph 0 (VoterModel.phiQ q ξcfg)) : ℝ) with hx
  have hx_nn : 0 ≤ x := by rw [hx]; positivity
  have hx_le : x ≤ 14 * (m : ℝ) / (3 * (Oα.card : ℝ)) := by
    have h1 : TemporalGraph.volume G.toTemporalGraph 0 (VoterModel.minoritySet G.toTemporalGraph 0 (VoterModel.phiQ q ξcfg))
        ≤ TemporalGraph.volume G.toTemporalGraph 0 (VoterModel.phiQ q ξcfg) :=
      volume_minoritySet_le 0 (VoterModel.phiQ q ξcfg)
    have h2 : TemporalGraph.volume G.toTemporalGraph 0 (VoterModel.phiQ q ξcfg)
        = TemporalGraph.volume G.toTemporalGraph s (VoterModel.phiQ q ξcfg) :=
      TemporalGraph.volume_fixed G.toTemporalGraph G.fixed _ 0 s
    rw [hx]
    calc (TemporalGraph.volume G.toTemporalGraph 0
            (VoterModel.minoritySet G.toTemporalGraph 0 (VoterModel.phiQ q ξcfg)) : ℝ)
        ≤ (TemporalGraph.volume G.toTemporalGraph 0 (VoterModel.phiQ q ξcfg) : ℝ) := by exact_mod_cast h1
      _ = (TemporalGraph.volume G.toTemporalGraph s (VoterModel.phiQ q ξcfg) : ℝ) := by rw [h2]
      _ ≤ 14 * (m : ℝ) / (3 * (Oα.card : ℝ)) := hsmall
  exact TemporalGraph.xiAlpha_sub_one_ge b m d_min hb (by exact_mod_cast hd_pos)
    Oα.card hOα x hx_nn hx_le

/-- **Obligation 3 (`one_block_hsmallbnd`).** On a leaf `D` pinning `(r_α, Oα)` where
opinion `q` is small at the block start `s = phaseTime(r_α + k·ξ)`
(`Vol_s(phiQ q ξ_s) ≤ 6m/|Oα|` on `D`), the conditional expectation of the §3.4
indicator `Xq q` at the *next* block start `phaseTime(r_α+(k+1)·ξ)` given `ℱ_s` is
`≤ 1/2` a.e. on `D`. Instantiates `condExp_Xq_le_half` at base `r := s` with the
shifted sequences `Δ'_j = Δ_{ℓ_s+j}`, `φ'_j = φ_{ℓ_s+j}` and `J = ℓ_{r_α+(k+1)ξ} − ℓ_s − 1`,
discharging its window via `phaseTime_add_sum_shift` and its threshold via
`threshold_le_of_small` + `phase_budget_block_ge`. -/
theorem VoterModelAbstract.one_block_hsmallbnd
    (hd : d_min = G.minDegreeAt 0) (hd_pos : 0 < d_min)
    (hΔ_pos : ∀ j, 1 ≤ Δ j) (hφ_nn : ∀ j, 0 ≤ φ j) (hφ_le1 : ∀ j, φ j ≤ 1)
    (hreach : TemporalGraph.reachUpToRMax B m d_min φ)
    (hwin : ∀ j, ∀ Sc ∈ G.admissibleCuts,
      φ j ≤ G.maxSetConductanceOnInterval (∑ i ∈ Finset.range j, Δ i) (Δ j) Sc)
    (hb_large : (5462 : ℝ) ≤ b)
    (k r_α : ℕ) (Oα : Finset (Fin κ)) (hOα : 0 < Oα.card) (q : Fin κ) (D : Set Ω)
    (hkrM : r_α + (k + 1) * TemporalGraph.xiAlpha b m d_min Oα.card
              ≤ TemporalGraph.rMax B m d_min)
    (hsmallD : ∀ ω ∈ D,
      (TemporalGraph.volume G.toTemporalGraph (TemporalGraph.phaseTime Δ φ
            (r_α + k * TemporalGraph.xiAlpha b m d_min Oα.card))
          (VoterModel.phiQ q (vm.ξ (TemporalGraph.phaseTime Δ φ
            (r_α + k * TemporalGraph.xiAlpha b m d_min Oα.card)) ω)) : ℝ)
        ≤ 14 * (m : ℝ) / (3 * (Oα.card : ℝ))) :
    (vm.μ : Measure Ω)[vm.Xq q (TemporalGraph.phaseTime Δ φ
            (r_α + (k + 1) * TemporalGraph.xiAlpha b m d_min Oα.card))
          | (vm.ℱ (TemporalGraph.phaseTime Δ φ
            (r_α + k * TemporalGraph.xiAlpha b m d_min Oα.card)) : MeasurableSpace Ω)]
      ≤ᵐ[(vm.μ : Measure Ω).restrict D] (fun _ => (1 / 2 : ℝ)) := by
  set ξc := TemporalGraph.xiAlpha b m d_min Oα.card with hξc
  set ℓs := TemporalGraph.phaseIndex φ (r_α + k * ξc) with hℓs
  set s := TemporalGraph.phaseTime Δ φ (r_α + k * ξc) with hs
  have hξc1 : 1 ≤ ξc := by rw [hξc]; unfold TemporalGraph.xiAlpha; omega
  -- local reachability at the two block levels, from `reachUpToRMax` + the cap `hkrM`
  have hle_lohi : r_α + k * ξc ≤ r_α + (k + 1) * ξc := by
    have h1 : (k + 1) * ξc = k * ξc + ξc := by ring
    omega
  have hreach_lo : ∃ ℓ, ((r_α + k * ξc : ℕ) : ℝ) ≤ ∑ j ∈ Finset.range ℓ, φ j :=
    hreach _ (le_trans hle_lohi hkrM)
  have hreach_hi' : ∃ ℓ, (((r_α + k * ξc) + ξc : ℕ) : ℝ) ≤ ∑ j ∈ Finset.range ℓ, φ j := by
    rw [show (r_α + k * ξc) + ξc = r_α + (k + 1) * ξc by ring]; exact hreach _ hkrM
  have hℓlt : ℓs < TemporalGraph.phaseIndex φ (r_α + (k + 1) * ξc) := by
    rw [hℓs, show r_α + (k + 1) * ξc = (r_α + k * ξc) + ξc by ring]
    exact phaseIndex_lt_of_pos φ hφ_nn hφ_le1 (r_α + k * ξc) ξc hξc1 hreach_lo hreach_hi'
  set J := TemporalGraph.phaseIndex φ (r_α + (k + 1) * ξc) - ℓs - 1 with hJ
  have hJ1 : ℓs + (J + 1) = TemporalGraph.phaseIndex φ (r_α + (k + 1) * ξc) := by omega
  -- shifted sequences
  set Δ' : ℕ → ℕ := fun j => Δ (ℓs + j) with hΔ'
  set φ' : ℕ → ℝ := fun j => φ (ℓs + j) with hφ'
  -- the window hypothesis for the shifted sequences, from the global `hwin`
  have hwin' : ∀ j, ∀ Sc ∈ TemporalGraph.admissibleCuts G.toTemporalGraph,
      φ' j ≤ TemporalGraph.maxSetConductanceOnInterval G.toTemporalGraph
        ((∑ i ∈ Finset.range j, Δ' i) + s) (Δ' j) Sc := by
    intro j Sc hSc
    have hg := hwin (ℓs + j) Sc hSc
    have hsum : (∑ i ∈ Finset.range j, Δ' i) + s = ∑ i ∈ Finset.range (ℓs + j), Δ i := by
      rw [hs, hℓs]; exact phaseTime_add_sum_shift Δ φ (r_α + k * ξc) j
    rw [hsum]
    exact hg
  -- apply `condExp_Xq_le_half`
  have hcond := condExp_Xq_le_half vm q s d_min hd hd_pos Δ'
    (fun j => hΔ_pos (ℓs + j)) φ' (fun j => hφ_nn (ℓs + j)) (fun j => hφ_le1 (ℓs + j))
    hwin' b hb_large J
  -- rewrite the `Xq` time: `s + ∑_{range (J+1)} Δ' = phaseTime(r_α+(k+1)ξ)`
  have htime : s + ∑ j ∈ Finset.range (J + 1), Δ' j
      = TemporalGraph.phaseTime Δ φ (r_α + (k + 1) * ξc) := by
    have h := phaseTime_add_sum_shift Δ φ (r_α + k * ξc) (J + 1)
    rw [← hℓs, ← hs] at h
    rw [add_comm s _, h, hJ1, TemporalGraph.phaseTime]
  rw [htime] at hcond
  -- the conditioning event of `condExp_Xq_le_half` contains `D`
  refine MeasureTheory.ae_restrict_of_ae_restrict_of_subset (fun ω hω => ?_) hcond
  -- `ω ∈ D ⟹ ω ∈ E_s`
  have hthr := threshold_le_of_small (m := m) (d_min := d_min) (b := b) hd_pos
    (le_trans (by norm_num) hb_large) s Oα hOα q (vm.ξ s ω) (hsmallD ω hω)
  have hbudget : (ξc : ℝ) - 1 ≤ ∑ ℓ ∈ Finset.range (J + 1), φ' ℓ := by
    have hb1 := phase_budget_block_ge φ hφ_le1 (r_α + k * ξc) ξc hreach_lo hreach_hi'
    rw [show r_α + k * ξc + ξc = r_α + (k + 1) * ξc by ring] at hb1
    rw [← hℓs] at hb1
    have hreindex : ∑ ℓ ∈ Finset.range (J + 1), φ' ℓ
        = ∑ i ∈ Finset.Ico ℓs (TemporalGraph.phaseIndex φ (r_α + (k + 1) * ξc)), φ i := by
      rw [Finset.sum_Ico_eq_sum_range,
        show TemporalGraph.phaseIndex φ (r_α + (k + 1) * ξc) - ℓs = J + 1 from by omega]
    rw [hreindex]; exact hb1
  simp only [Set.mem_setOf_eq]
  exact le_trans hthr hbudget

/-- **Obligation 4 (`one_block_hED`, the counting bridge, eqs `0a–0c`).** Given the
opinion-set monotonicity `𝒪(s+K) ⊆ 𝒪(s)`, the small-opinion inclusion `Os ⊆ 𝒪(s)`,
the threshold `(6/7)|Oα| < |𝒪(s+K)|` (from survival of the metaphase), and
`|𝒪(s+K)| ≥ 2`, the §3.4 counting inequality
`(6/7)|Oα| − Ocard + |Os| ≤ ∑_{q∈Os} X_q(s+K)` holds. Here, since `|𝒪(s+K)| ≥ 2`,
`X_q = 𝟙[q ∈ 𝒪(s+K)]`, so `∑_{q∈Os} X_q = |Os ∩ 𝒪(s+K)|`, and inclusion–exclusion
(`Os ∪ 𝒪(s+K) ⊆ 𝒪(s)`) gives `|Os ∩ 𝒪(s+K)| ≥ |Os| + |𝒪(s+K)| − Ocard`. -/
theorem VoterModelAbstract.one_block_hED
    (s K : ℕ) (Oα Os : Finset (Fin κ)) (Ocard : ℕ) (ω : Ω)
    (hOs_sub : Os ⊆ vm.opinionSet s ω)
    (hOcard : (vm.opinionSet s ω).card = Ocard)
    (hmono_sK : vm.opinionSet (s + K) ω ⊆ vm.opinionSet s ω)
    (hbig : (6 / 7 : ℝ) * (Oα.card : ℝ) < ((vm.opinionSet (s + K) ω).card : ℝ))
    (h2 : 2 ≤ (vm.opinionSet (s + K) ω).card) :
    ((6 : ℝ) / 7 * (Oα.card : ℝ) - (Ocard : ℝ) + (Os.card : ℝ))
      ≤ ∑ q ∈ Os, vm.Xq q (s + K) ω := by
  -- on `Os`, `X_q = 𝟙[q ∈ 𝒪(s+K)]`
  have hXq : ∀ q ∈ Os, vm.Xq q (s + K) ω
      = if q ∈ vm.opinionSet (s + K) ω then (1 : ℝ) else 0 := by
    intro q _
    unfold VoterModelAbstract.Xq
    by_cases hq : q ∈ vm.opinionSet (s + K) ω
    · rw [if_pos hq]
      refine if_neg ?_
      rintro (hempty | huniv)
      · obtain ⟨v, hv⟩ := (vm.mem_opinionSet).mp hq
        have hvm : v ∈ VoterModel.phiQ q (vm.ξ (s + K) ω) := by simp [VoterModel.phiQ, hv]
        rw [hempty] at hvm; exact absurd hvm (Finset.notMem_empty v)
      · have hcard1 : (vm.opinionSet (s + K) ω).card ≤ 1 := by
          refine Finset.card_le_one.mpr (fun a ha b hb => ?_)
          obtain ⟨va, hva⟩ := (vm.mem_opinionSet).mp ha
          obtain ⟨vb, hvb⟩ := (vm.mem_opinionSet).mp hb
          have hva' : vm.ξ (s + K) ω va = q := by
            have hmem : va ∈ VoterModel.phiQ q (vm.ξ (s + K) ω) := huniv ▸ Finset.mem_univ va
            simpa [VoterModel.phiQ] using hmem
          have hvb' : vm.ξ (s + K) ω vb = q := by
            have hmem : vb ∈ VoterModel.phiQ q (vm.ξ (s + K) ω) := huniv ▸ Finset.mem_univ vb
            simpa [VoterModel.phiQ] using hmem
          rw [← hva, ← hvb, hva', hvb']
        omega
    · rw [if_neg hq]
      refine if_pos (Or.inl ?_)
      rw [Finset.eq_empty_iff_forall_notMem]
      intro v hv
      exact hq ((vm.mem_opinionSet).mpr ⟨v, by simpa [VoterModel.phiQ] using hv⟩)
  rw [Finset.sum_congr rfl hXq, Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul, mul_one]
  -- `|Os ∪ 𝒪(s+K)| ≤ Ocard`
  have hunion_le : (Os ∪ vm.opinionSet (s + K) ω).card ≤ Ocard := by
    rw [← hOcard]
    exact Finset.card_le_card (Finset.union_subset hOs_sub hmono_sK)
  have hie : (Os ∩ vm.opinionSet (s + K) ω).card + (Os ∪ vm.opinionSet (s + K) ω).card
      = Os.card + (vm.opinionSet (s + K) ω).card := Finset.card_inter_add_card_union _ _
  have hunionR : ((Os ∪ vm.opinionSet (s + K) ω).card : ℝ) ≤ (Ocard : ℝ) := by
    exact_mod_cast hunion_le
  have hieR : ((Os ∩ vm.opinionSet (s + K) ω).card : ℝ)
      + ((Os ∪ vm.opinionSet (s + K) ω).card : ℝ)
      = (Os.card : ℝ) + ((vm.opinionSet (s + K) ω).card : ℝ) := by exact_mod_cast hie
  linarith [hbig, hieR, hunionR]

/-- **Obligation 4 threshold (`hbig` source).** For metaphase index `α = γ+1`: if the
opinion count at the boundary `R_α` is at most `θ_{α-1} = max⌈(6/7)^γ κ⌉ 1`, and phase
`rr` survives the metaphase (`rr < R_{α+1}`), then `(6/7)|𝒪(t_{R_α})| < |𝒪(t_{rr})|`.
Composes `metaphase_succ_lt_opinionCard_gt` with `opinion_threshold_arith`. -/
theorem VoterModelAbstract.one_block_threshold_gt (γ rr : ℕ) (ω : Ω)
    (hOα_le : (vm.opinionSet (TemporalGraph.phaseTime Δ φ
          (vm.metaphase B m d_min Δ φ (γ + 1) ω)) ω).card ≤ max ⌈(6 / 7 : ℝ) ^ γ * (κ : ℝ)⌉₊ 1)
    (hE : rr < vm.metaphase B m d_min Δ φ (γ + 2) ω) :
    (6 / 7 : ℝ) * ((vm.opinionSet (TemporalGraph.phaseTime Δ φ
          (vm.metaphase B m d_min Δ φ (γ + 1) ω)) ω).card : ℝ)
      < ((vm.opinionSet (TemporalGraph.phaseTime Δ φ rr) ω).card : ℝ) :=
  opinion_threshold_arith γ _ _ hOα_le
    (vm.metaphase_succ_lt_opinionCard_gt B m d_min Δ φ (γ + 1) rr ω hE)

/-- **a.e. `hED`** for the pinned leaf `D` (the form `per_metaphase_two_thirds` now
consumes). For `α = 0` the survival event is empty (it would force `|𝒪| > κ`), so the
implication is vacuous; for `α = γ+1` it is `one_block_hED` fed by `one_block_threshold_gt`
(`hbig`), `metaphase_succ_opinionCard_le` (`|Oα| ≤ θ_{α-1}`, with `R_α = rMax` excluded on
the survival event) and `opinionSet_subset_ae` (a.e. monotonicity). -/
theorem VoterModelAbstract.one_block_hED_ae
    (hmono : Monotone (TemporalGraph.phaseTime Δ φ))
    (α k r_α : ℕ) (Oα Os : Finset (Fin κ)) (Ocard : ℕ) (D : Set Ω)
    (hDmeta : ∀ ω ∈ D, vm.metaphase B m d_min Δ φ α ω = r_α)
    (hDOα : ∀ ω ∈ D, vm.opinionSet (TemporalGraph.phaseTime Δ φ r_α) ω = Oα)
    (hDOs : ∀ ω ∈ D, vm.smallOpinions (TemporalGraph.phaseTime Δ φ
        (r_α + k * TemporalGraph.xiAlpha b m d_min Oα.card)) Oα m ω = Os)
    (hDcard : ∀ ω ∈ D, (vm.opinionSet (TemporalGraph.phaseTime Δ φ
        (r_α + k * TemporalGraph.xiAlpha b m d_min Oα.card)) ω).card = Ocard) :
    ∀ᵐ ω ∂(vm.μ : Measure Ω), ω ∈ {ω | r_α + (k + 1) * TemporalGraph.xiAlpha b m d_min Oα.card
          < vm.metaphase B m d_min Δ φ (α + 1) ω} ∩ D →
      ((6 : ℝ) / 7 * Oα.card - Ocard + Os.card)
        ≤ ∑ q ∈ Os, vm.Xq q (TemporalGraph.phaseTime Δ φ
            (r_α + (k + 1) * TemporalGraph.xiAlpha b m d_min Oα.card)) ω := by
  set ξc := TemporalGraph.xiAlpha b m d_min Oα.card with hξc
  set s := TemporalGraph.phaseTime Δ φ (r_α + k * ξc) with hs
  set sK := TemporalGraph.phaseTime Δ φ (r_α + (k + 1) * ξc) with hsK
  have hsK_le : s ≤ sK := hmono (by nlinarith)
  set K := sK - s with hKdef
  have hK : s + K = sK := Nat.add_sub_cancel' hsK_le
  cases α with
  | zero =>
    refine Filter.Eventually.of_forall (fun ω hω => ?_)
    exfalso
    have hgt := vm.metaphase_succ_lt_opinionCard_gt B m d_min Δ φ 0 (r_α + (k + 1) * ξc) ω hω.1
    rw [pow_zero, one_mul] at hgt
    have hcardle : (vm.opinionSet (TemporalGraph.phaseTime Δ φ (r_α + (k + 1) * ξc)) ω).card ≤ κ := by
      calc (vm.opinionSet (TemporalGraph.phaseTime Δ φ (r_α + (k + 1) * ξc)) ω).card
          ≤ (Finset.univ : Finset (Fin κ)).card := Finset.card_le_univ _
        _ = κ := by simp
    have hκ : κ ≤ max ⌈(κ : ℝ)⌉₊ 1 := by rw [Nat.ceil_natCast]; exact le_max_left _ _
    omega
  | succ γ =>
    filter_upwards [vm.opinionSet_subset_ae (s := s) (t := sK) hsK_le] with ω hmono_ω hω
    obtain ⟨hE, hD⟩ := hω
    have hmeta := hDmeta ω hD
    have hOα_pin := hDOα ω hD
    have hOs_pin := hDOs ω hD
    have hcard_pin := hDcard ω hD
    -- `|Oα| ≤ θ_{γ}`, ruling out `R_α = rMax` on the survival event
    have hOα_le : (vm.opinionSet (TemporalGraph.phaseTime Δ φ
        (vm.metaphase B m d_min Δ φ (γ + 1) ω)) ω).card ≤ max ⌈(6 / 7 : ℝ) ^ γ * (κ : ℝ)⌉₊ 1 := by
      rcases vm.metaphase_succ_opinionCard_le B m d_min Δ φ γ ω with hrmax | hcl
      · exfalso
        rw [hmeta] at hrmax
        have hR' := vm.metaphase_le_rMax B m d_min Δ φ (γ + 2) ω
        have : r_α + (k + 1) * ξc < vm.metaphase B m d_min Δ φ (γ + 2) ω := hE
        omega
      · exact hcl
    -- `hbig`
    have hbig := vm.one_block_threshold_gt B m d_min Δ φ γ (r_α + (k + 1) * ξc) ω hOα_le hE
    rw [hmeta, hOα_pin] at hbig
    -- `h2`
    have h2gt := vm.metaphase_succ_lt_opinionCard_gt B m d_min Δ φ (γ + 1) (r_α + (k + 1) * ξc) ω hE
    have h2 : 2 ≤ (vm.opinionSet sK ω).card := by
      have hθ1 : 1 ≤ max ⌈(6 / 7 : ℝ) ^ (γ + 1) * (κ : ℝ)⌉₊ 1 := le_max_right _ _
      have : max ⌈(6 / 7 : ℝ) ^ (γ + 1) * (κ : ℝ)⌉₊ 1
          < (vm.opinionSet (TemporalGraph.phaseTime Δ φ (r_α + (k + 1) * ξc)) ω).card := h2gt
      change _ < (vm.opinionSet sK ω).card at this
      omega
    -- assemble via `one_block_hED`
    have hOs_sub : Os ⊆ vm.opinionSet s ω := by
      rw [← hOs_pin]; exact Finset.filter_subset _ _
    have hmono_sK : vm.opinionSet (s + K) ω ⊆ vm.opinionSet s ω := by rw [hK]; exact hmono_ω
    have hbig' : (6 / 7 : ℝ) * (Oα.card : ℝ) < ((vm.opinionSet (s + K) ω).card : ℝ) := by
      rw [hK]; exact hbig
    have h2' : 2 ≤ (vm.opinionSet (s + K) ω).card := by rw [hK]; exact h2
    have hcount := vm.one_block_hED s K Oα Os Ocard ω hOs_sub hcard_pin hmono_sK hbig' h2'
    rw [hK] at hcount
    exact hcount

/-- **Obligation 2 (leaf measurability).** The pinned leaf
`S ∩ {R_α = r_α} ∩ {𝒪(t_{r_α}) = Oα} ∩ {r_α + k·ξ < R_{α+1}}` (with the *concrete*
`ξ = xiAlpha b m d_min |Oα|`) is `ℱ_s`-measurable at the level-`k` block start
`s = phaseTime(r_α + k·ξ)`. Combines the stopping-time σ-algebra
(`measurableSet_inter_eq_iff`), `opinionSet_measurable`, and `metaphase_le_measurable`. -/
theorem VoterModelAbstract.one_block_leaf_measurable
    (hmono : Monotone (TemporalGraph.phaseTime Δ φ)) (α k r_α : ℕ) (Oα Os : Finset (Fin κ))
    (Ocard : ℕ) (S : Set Ω)
    (hS : MeasurableSet[(vm.metaphase_isStoppingTime B m d_min Δ φ hmono α).measurableSpace] S) :
    @MeasurableSet Ω
      (vm.ℱ (TemporalGraph.phaseTime Δ φ (r_α + k * TemporalGraph.xiAlpha b m d_min Oα.card)))
      (S ∩ {ω | vm.metaphase B m d_min Δ φ α ω = r_α}
         ∩ {ω | vm.opinionSet (TemporalGraph.phaseTime Δ φ r_α) ω = Oα}
         ∩ {ω | vm.smallOpinions (TemporalGraph.phaseTime Δ φ
                  (r_α + k * TemporalGraph.xiAlpha b m d_min Oα.card)) Oα m ω = Os}
         ∩ {ω | (vm.opinionSet (TemporalGraph.phaseTime Δ φ
                  (r_α + k * TemporalGraph.xiAlpha b m d_min Oα.card)) ω).card = Ocard}
         ∩ {ω | r_α + k * TemporalGraph.xiAlpha b m d_min Oα.card
                  < vm.metaphase B m d_min Δ φ (α + 1) ω}) := by
  set ξc := TemporalGraph.xiAlpha b m d_min Oα.card with hξc
  set s := TemporalGraph.phaseTime Δ φ (r_α + k * ξc) with hs
  set hτ := vm.metaphase_isStoppingTime B m d_min Δ φ hmono α with hτdef
  have hle1 : TemporalGraph.phaseTime Δ φ r_α ≤ s := hmono (Nat.le_add_right _ _)
  -- conjunct 1: S ∩ {R_α = r_α} is `ℱ_{t_{r_α}}`-measurable, hence `ℱ_s`-measurable
  have hc1 : @MeasurableSet Ω (vm.ℱ s)
      (S ∩ {ω | vm.metaphase B m d_min Δ φ α ω = r_α}) := by
    have hmem : MeasurableSet[hτ.measurableSpace]
        (S ∩ {ω | (vm.metaphase B m d_min Δ φ α ω : WithTop ℕ) = (r_α : WithTop ℕ)}) :=
      hS.inter (hτ.measurableSet_eq' r_α)
    have hf := (hτ.measurableSet_inter_eq_iff S r_α).mp hmem
    have hf' := vm.ℱ.mono hle1 _ hf
    convert hf' using 2
    ext ω
    simp only [Set.mem_setOf_eq]
    exact Nat.cast_inj.symm
  -- conjunct 2: {𝒪(t_{r_α}) = Oα} is `ℱ_{t_{r_α}}`-measurable
  have hc2 : @MeasurableSet Ω (vm.ℱ s)
      {ω | vm.opinionSet (TemporalGraph.phaseTime Δ φ r_α) ω = Oα} :=
    vm.ℱ.mono hle1 _ (vm.opinionSet_measurable (TemporalGraph.phaseTime Δ φ r_α)
      (measurableSet_singleton Oα))
  -- conjunct 4: {smallOpinions s Oα m = Os} is `ℱ_s`-measurable
  have hc4 : @MeasurableSet Ω (vm.ℱ s) {ω | vm.smallOpinions s Oα m ω = Os} :=
    vm.smallOpinions_measurable s Oα m (measurableSet_singleton Os)
  -- conjunct 5: {|𝒪(s)| = Ocard} is `ℱ_s`-measurable
  have hc5 : @MeasurableSet Ω (vm.ℱ s) {ω | (vm.opinionSet s ω).card = Ocard} :=
    (measurable_from_top (f := fun t : Finset (Fin κ) => t.card)).comp
      (vm.opinionSet_measurable s) (measurableSet_singleton Ocard)
  -- conjunct 3: {r_α + k·ξ < R_{α+1}} is `ℱ_s`-measurable
  have hc3 : @MeasurableSet Ω (vm.ℱ s)
      {ω | r_α + k * ξc < vm.metaphase B m d_min Δ φ (α + 1) ω} := by
    have hle := vm.metaphase_le_measurable B m d_min Δ φ hmono (α + 1) (r_α + k * ξc)
    have hcompl : {ω | r_α + k * ξc < vm.metaphase B m d_min Δ φ (α + 1) ω}
        = {ω | vm.metaphase B m d_min Δ φ (α + 1) ω ≤ r_α + k * ξc}ᶜ := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
    rw [hcompl]
    exact hle.compl
  exact ((((hc1.inter hc2).inter hc4).inter hc5).inter hc3)

/-- **Single-leaf bound** (`per_metaphase_two_thirds` ∘ the per-piece converter).
On a pinned `ℱ_s`-measurable leaf `D`, the set-integral of the survival indicator
`𝟙_{r+ξ < R_{α+1}}` is at most `(2/3)·μ(D)`. This is the per-leaf ingredient of
`one_block_random_index`; the finite sum over leaves (obligation 1/5) and the
discharge of `hsmallbnd`/`hED` (obligations 3/4) feed its hypotheses. -/
theorem VoterModelAbstract.one_block_leaf
    (α r ξ s K : ℕ) (Oα Os : Finset (Fin κ)) (Ocard : ℕ)
    (D : Set Ω) (hDmeas : @MeasurableSet Ω (vm.ℱ s) D)
    (hOspin : ∀ ω ∈ D, vm.smallOpinions s Oα m ω = Os)
    (hOpin : ∀ ω ∈ D, (vm.opinionSet s ω).card = Ocard)
    (hm_pos : 0 < m) (hOα : 0 < Oα.card)
    (hvol : ((G.snapshot s).volume Finset.univ : ℝ) ≤ 2 * m) (hOle : (Ocard : ℝ) ≤ Oα.card)
    (hsmallbnd : ∀ q ∈ Os,
      (vm.μ : Measure Ω)[vm.Xq q (s + K) | (vm.ℱ s : MeasurableSpace Ω)]
        ≤ᵐ[(vm.μ : Measure Ω).restrict D] (fun _ => (1 / 2 : ℝ)))
    (hEmeas : MeasurableSet {ω | r + ξ < vm.metaphase B m d_min Δ φ (α + 1) ω})
    (hED : ∀ᵐ ω ∂(vm.μ : Measure Ω), ω ∈ {ω | r + ξ < vm.metaphase B m d_min Δ φ (α + 1) ω} ∩ D →
      ((6 : ℝ) / 7 * Oα.card - Ocard + Os.card)
        ≤ ∑ q ∈ Os, vm.Xq q (s + K) ω) :
    ∫ ω in D, ({ω | r + ξ < vm.metaphase B m d_min Δ φ (α + 1) ω}).indicator (fun _ => (1 : ℝ)) ω
        ∂vm.μ
      ≤ (2 / 3) * ((vm.μ : Measure Ω) D).toReal :=
  setIntegral_le_of_condExp_le_restrict (vm.ℱ.le s)
    ((integrable_const (1 : ℝ)).indicator hEmeas) hDmeas
    (TemporalGraph.per_metaphase_two_thirds vm B m d_min Δ φ α r ξ s K Oα Os Ocard D
      hDmeas hOspin hOpin hm_pos hOα hvol hOle hsmallbnd hEmeas hED)

/-- **Per-leaf complete bound** (obligations 2+3+4 assembled, unconditional).
On the pinned leaf `D_leaf = S ∩ {R_α=r_α} ∩ {𝒪(t_{r_α})=Oα} ∩ {smallOpinions=Os} ∩
{|𝒪(s)|=Ocard} ∩ {r_α+k·ξ<R_{α+1}}` (with `ξ = xiAlpha b m d_min |Oα|`,
`s = phaseTime(r_α+k·ξ)`), the survival set-integral is `≤ (2/3)·μ(D_leaf)`. Combines
`one_block_leaf` (per_metaphase ∘ converter) with `one_block_hsmallbnd` (hsmallbnd) and
`one_block_hED_ae` (a.e. hED); the numeric `hOα`/`hOle` come from a non-null leaf via
`opinionSet_subset_ae`, the null leaf being trivial. -/
theorem VoterModelAbstract.one_block_leaf_final
    (hmono : Monotone (TemporalGraph.phaseTime Δ φ))
    (hd : d_min = G.minDegreeAt 0) (hd_pos : 0 < d_min) (hΔ_pos : ∀ j, 1 ≤ Δ j)
    (hφ_nn : ∀ j, 0 ≤ φ j) (hφ_le1 : ∀ j, φ j ≤ 1)
    (hreach : TemporalGraph.reachUpToRMax B m d_min φ)
    (hwin : ∀ j, ∀ Sc ∈ G.admissibleCuts,
      φ j ≤ G.maxSetConductanceOnInterval (∑ i ∈ Finset.range j, Δ i) (Δ j) Sc)
    (hb_large : (5462 : ℝ) ≤ b) (hm_pos : 0 < m)
    (hvol : ∀ t, (TemporalGraph.volume G.toTemporalGraph t Finset.univ : ℝ) ≤ 2 * m)
    (α k r_α : ℕ) (Oα Os : Finset (Fin κ)) (Ocard : ℕ) (S : Set Ω)
    (hS : MeasurableSet[(vm.metaphase_isStoppingTime B m d_min Δ φ hmono α).measurableSpace] S) :
    ∫ ω in (S ∩ {ω | vm.metaphase B m d_min Δ φ α ω = r_α}
         ∩ {ω | vm.opinionSet (TemporalGraph.phaseTime Δ φ r_α) ω = Oα}
         ∩ {ω | vm.smallOpinions (TemporalGraph.phaseTime Δ φ
                  (r_α + k * TemporalGraph.xiAlpha b m d_min Oα.card)) Oα m ω = Os}
         ∩ {ω | (vm.opinionSet (TemporalGraph.phaseTime Δ φ
                  (r_α + k * TemporalGraph.xiAlpha b m d_min Oα.card)) ω).card = Ocard}
         ∩ {ω | r_α + k * TemporalGraph.xiAlpha b m d_min Oα.card
                  < vm.metaphase B m d_min Δ φ (α + 1) ω}),
        ({ω | r_α + (k + 1) * TemporalGraph.xiAlpha b m d_min Oα.card
              < vm.metaphase B m d_min Δ φ (α + 1) ω}).indicator (fun _ => (1 : ℝ)) ω ∂vm.μ
      ≤ (2 / 3) * ((vm.μ : Measure Ω) (S ∩ {ω | vm.metaphase B m d_min Δ φ α ω = r_α}
         ∩ {ω | vm.opinionSet (TemporalGraph.phaseTime Δ φ r_α) ω = Oα}
         ∩ {ω | vm.smallOpinions (TemporalGraph.phaseTime Δ φ
                  (r_α + k * TemporalGraph.xiAlpha b m d_min Oα.card)) Oα m ω = Os}
         ∩ {ω | (vm.opinionSet (TemporalGraph.phaseTime Δ φ
                  (r_α + k * TemporalGraph.xiAlpha b m d_min Oα.card)) ω).card = Ocard}
         ∩ {ω | r_α + k * TemporalGraph.xiAlpha b m d_min Oα.card
                  < vm.metaphase B m d_min Δ φ (α + 1) ω})).toReal := by
  set ξc := TemporalGraph.xiAlpha b m d_min Oα.card with hξc
  set s := TemporalGraph.phaseTime Δ φ (r_α + k * ξc) with hs
  set sK := TemporalGraph.phaseTime Δ φ (r_α + (k + 1) * ξc) with hsK
  set E := {ω | r_α + (k + 1) * ξc < vm.metaphase B m d_min Δ φ (α + 1) ω} with hEdef
  set D := S ∩ {ω | vm.metaphase B m d_min Δ φ α ω = r_α}
         ∩ {ω | vm.opinionSet (TemporalGraph.phaseTime Δ φ r_α) ω = Oα}
         ∩ {ω | vm.smallOpinions s Oα m ω = Os}
         ∩ {ω | (vm.opinionSet s ω).card = Ocard}
         ∩ {ω | r_α + k * ξc < vm.metaphase B m d_min Δ φ (α + 1) ω} with hDdef
  have hsK_le : s ≤ sK := hmono (by nlinarith)
  have hK : s + (sK - s) = sK := Nat.add_sub_cancel' hsK_le
  -- case split on whether the next block start `r_α+(k+1)·ξ` is within the cap `r_max`
  by_cases hkrM : r_α + (k + 1) * ξc ≤ TemporalGraph.rMax B m d_min
  case neg =>
    -- past the cap: the survival event `E` is empty since `R_{α+1} ≤ r_max`, so the
    -- integrand vanishes and the bound is trivial
    have hEempty : E = ∅ := by
      rw [hEdef]; ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      exact le_trans (vm.metaphase_le_rMax B m d_min Δ φ (α + 1) ω) (le_of_lt (not_le.mp hkrM))
    simp only [hEempty, Set.indicator_empty, integral_zero]
    positivity
  -- pins extracted from membership
  have hDmeta : ∀ ω ∈ D, vm.metaphase B m d_min Δ φ α ω = r_α := fun ω hω => hω.1.1.1.1.2
  have hDOα : ∀ ω ∈ D, vm.opinionSet (TemporalGraph.phaseTime Δ φ r_α) ω = Oα :=
    fun ω hω => hω.1.1.1.2
  have hDOs : ∀ ω ∈ D, vm.smallOpinions s Oα m ω = Os := fun ω hω => hω.1.1.2
  have hDcard : ∀ ω ∈ D, (vm.opinionSet s ω).card = Ocard := fun ω hω => hω.1.2
  -- measurability
  have hDmeas : @MeasurableSet Ω (vm.ℱ s) D :=
    vm.one_block_leaf_measurable B m d_min b Δ φ hmono α k r_α Oα Os Ocard S hS
  have hEmeas : MeasurableSet E :=
    measurableSet_lt measurable_const (vm.metaphase_measurable B m d_min Δ φ hmono (α + 1))
  by_cases hD0 : (vm.μ : Measure Ω) D = 0
  · -- null leaf: both sides 0
    rw [setIntegral_measure_zero _ hD0]
    rw [hD0, ENNReal.toReal_zero, mul_zero]
  · -- non-null leaf
    -- a.e. monotonicity `𝒪(s) ⊆ 𝒪(t_{r_α})`
    have hmono1 : ∀ᵐ ω ∂(vm.μ : Measure Ω), vm.opinionSet s ω
        ⊆ vm.opinionSet (TemporalGraph.phaseTime Δ φ r_α) ω :=
      vm.opinionSet_subset_ae (hmono (Nat.le_add_right _ _))
    have hDM : ∃ ω, ω ∈ D ∧ vm.opinionSet s ω
        ⊆ vm.opinionSet (TemporalGraph.phaseTime Δ φ r_α) ω := by
      by_contra hcon
      simp only [not_exists, not_and] at hcon
      exact hD0 (measure_mono_null (fun ω hω => hcon ω hω) (ae_iff.mp hmono1))
    obtain ⟨ω₀, hω₀D, hω₀M⟩ := hDM
    have hOα : 0 < Oα.card := by
      rw [← hDOα ω₀ hω₀D]
      exact Finset.Nonempty.card_pos ((Finset.univ_nonempty).image _)
    have hOle : (Ocard : ℝ) ≤ Oα.card := by
      have hsub := Finset.card_le_card hω₀M
      rw [hDcard ω₀ hω₀D, hDOα ω₀ hω₀D] at hsub
      exact_mod_cast hsub
    -- hsmallbnd (with `Xq` time `s + (sK - s) = sK`)
    have hsmallbnd : ∀ q ∈ Os,
        (vm.μ : Measure Ω)[vm.Xq q (s + (sK - s)) | (vm.ℱ s : MeasurableSpace Ω)]
          ≤ᵐ[(vm.μ : Measure Ω).restrict D] (fun _ => (1 / 2 : ℝ)) := by
      intro q hq
      have hsmallD : ∀ ω ∈ D, (TemporalGraph.volume G.toTemporalGraph s
          (VoterModel.phiQ q (vm.ξ s ω)) : ℝ) ≤ 14 * (m : ℝ) / (3 * (Oα.card : ℝ)) := by
        intro ω hω
        have hmem : q ∈ vm.smallOpinions s Oα m ω := by rw [hDOs ω hω]; exact hq
        rw [VoterModelAbstract.smallOpinions, Finset.mem_filter] at hmem
        exact hmem.2
      have hcond := vm.one_block_hsmallbnd B m d_min b Δ φ hd hd_pos hΔ_pos hφ_nn hφ_le1
        hreach hwin hb_large k r_α Oα hOα q D hkrM hsmallD
      rw [hK]; exact hcond
    -- hED a.e. (with `Xq` time `s + (sK - s) = sK`)
    have hED : ∀ᵐ ω ∂(vm.μ : Measure Ω), ω ∈ {ω | r_α + (k + 1) * ξc
          < vm.metaphase B m d_min Δ φ (α + 1) ω} ∩ D →
        ((6 : ℝ) / 7 * Oα.card - Ocard + Os.card)
          ≤ ∑ q ∈ Os, vm.Xq q (s + (sK - s)) ω := by
      have h := vm.one_block_hED_ae B m d_min b Δ φ hmono α k r_α Oα Os Ocard D
        hDmeta hDOα hDOs hDcard
      filter_upwards [h] with ω hω hmem
      rw [hK]; exact hω hmem
    -- apply one_block_leaf with `r = r_α+(k+1)ξc`, `ξ = 0` (so `r+ξ = r_α+(k+1)ξc`)
    exact vm.one_block_leaf B m d_min Δ φ α (r_α + (k + 1) * ξc) 0 s (sK - s) Oα Os Ocard D
      hDmeas hDOs hDcard hm_pos hOα (hvol s) hOle hsmallbnd hEmeas hED

/-- **STEP 1 (`one_block_random_index`).** The single-block bound at the *random* block
start: for `S` in the stopping-time σ-algebra,
`∫_{S∩B^k} 𝟙_{B^{k+1}} ≤ (2/3)·μ(S∩B^k)`. Proved by the finite decomposition of `S∩B^k`
over the pinned leaves `(r_α, Oα, Os, Ocard)` (pairwise disjoint, union `= S∩B^k`),
`one_block_leaf_final` per leaf, and `integral_finset_biUnion`/`measure_biUnion_finset`. -/
theorem VoterModelAbstract.one_block_random_index
    (hmono : Monotone (TemporalGraph.phaseTime Δ φ))
    (hd : d_min = G.minDegreeAt 0) (hd_pos : 0 < d_min) (hΔ_pos : ∀ j, 1 ≤ Δ j)
    (hφ_nn : ∀ j, 0 ≤ φ j) (hφ_le1 : ∀ j, φ j ≤ 1)
    (hreach : TemporalGraph.reachUpToRMax B m d_min φ)
    (hwin : ∀ j, ∀ Sc ∈ G.admissibleCuts,
      φ j ≤ G.maxSetConductanceOnInterval (∑ i ∈ Finset.range j, Δ i) (Δ j) Sc)
    (hb_large : (5462 : ℝ) ≤ b) (hm_pos : 0 < m)
    (hvol : ∀ t, (TemporalGraph.volume G.toTemporalGraph t Finset.univ : ℝ) ≤ 2 * m)
    (α k : ℕ) (S : Set Ω)
    (hS : MeasurableSet[(vm.metaphase_isStoppingTime B m d_min Δ φ hmono α).measurableSpace] S) :
    ∫ ω in S ∩ vm.blockTailSet B m d_min b Δ φ α k,
        (vm.blockTailSet B m d_min b Δ φ α (k + 1)).indicator (fun _ => (1 : ℝ)) ω ∂vm.μ
      ≤ (2 / 3) * ((vm.μ : Measure Ω) (S ∩ vm.blockTailSet B m d_min b Δ φ α k)).toReal := by
  classical
  set Dl : ℕ × Finset (Fin κ) × Finset (Fin κ) × ℕ → Set Ω := fun p =>
    S ∩ {ω | vm.metaphase B m d_min Δ φ α ω = p.1}
      ∩ {ω | vm.opinionSet (TemporalGraph.phaseTime Δ φ p.1) ω = p.2.1}
      ∩ {ω | vm.smallOpinions (TemporalGraph.phaseTime Δ φ
              (p.1 + k * TemporalGraph.xiAlpha b m d_min p.2.1.card)) p.2.1 m ω = p.2.2.1}
      ∩ {ω | (vm.opinionSet (TemporalGraph.phaseTime Δ φ
              (p.1 + k * TemporalGraph.xiAlpha b m d_min p.2.1.card)) ω).card = p.2.2.2}
      ∩ {ω | p.1 + k * TemporalGraph.xiAlpha b m d_min p.2.1.card
              < vm.metaphase B m d_min Δ φ (α + 1) ω} with hDl
  set I : Finset (ℕ × Finset (Fin κ) × Finset (Fin κ) × ℕ) :=
    Finset.range (TemporalGraph.rMax B m d_min + 1) ×ˢ Finset.univ ×ˢ Finset.univ
      ×ˢ Finset.range (κ + 1) with hI
  have hBk1meas : MeasurableSet (vm.blockTailSet B m d_min b Δ φ α (k + 1)) :=
    vm.blockTailSet_measurable B m d_min b Δ φ hmono α (k + 1)
  -- leaf measurability
  have hmeas : ∀ p ∈ I, MeasurableSet (Dl p) := by
    intro p _
    exact (vm.ℱ.le _) _
      (vm.one_block_leaf_measurable B m d_min b Δ φ hmono α k p.1 p.2.1 p.2.2.1 p.2.2.2 S hS)
  -- `metaphaseXi` is the concrete `ξc` on a leaf
  have hξ_leaf : ∀ p, ∀ ω ∈ Dl p,
      vm.metaphaseXi B m d_min b Δ φ α ω = TemporalGraph.xiAlpha b m d_min p.2.1.card := by
    intro p ω hω
    have hm1 : vm.metaphase B m d_min Δ φ α ω = p.1 := hω.1.1.1.1.2
    have hm2 : vm.opinionSet (TemporalGraph.phaseTime Δ φ p.1) ω = p.2.1 := hω.1.1.1.2
    unfold VoterModelAbstract.metaphaseXi
    rw [hm1, hm2]
  -- union `= S ∩ B^k`
  have hunion : S ∩ vm.blockTailSet B m d_min b Δ φ α k = ⋃ p ∈ I, Dl p := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_inter_iff, exists_prop]
    constructor
    · rintro ⟨hSω, hBk⟩
      set r_α := vm.metaphase B m d_min Δ φ α ω with hr_α
      set Oα := vm.opinionSet (TemporalGraph.phaseTime Δ φ r_α) ω with hOα
      set ξc := TemporalGraph.xiAlpha b m d_min Oα.card with hξc
      set s := TemporalGraph.phaseTime Δ φ (r_α + k * ξc) with hs
      refine ⟨(r_α, Oα, vm.smallOpinions s Oα m ω, (vm.opinionSet s ω).card), ?_, ?_⟩
      · simp only [hI, Finset.mem_product, Finset.mem_range, Finset.mem_univ, true_and]
        refine ⟨Nat.lt_succ_of_le (vm.metaphase_le_rMax B m d_min Δ φ α ω), ?_⟩
        exact Nat.lt_succ_of_le (le_trans (Finset.card_le_univ _) (by simp))
      · have hξeq : vm.metaphaseXi B m d_min b Δ φ α ω = ξc := by
          unfold VoterModelAbstract.metaphaseXi; rw [← hr_α, ← hOα]
        refine ⟨⟨⟨⟨⟨hSω, rfl⟩, rfl⟩, rfl⟩, rfl⟩, ?_⟩
        simp only [VoterModelAbstract.blockTailSet, Set.mem_setOf_eq] at hBk ⊢
        rw [hξeq] at hBk; exact hBk
    · rintro ⟨p, hpI, hω⟩
      refine ⟨hω.1.1.1.1.1, ?_⟩
      simp only [VoterModelAbstract.blockTailSet, Set.mem_setOf_eq]
      have hm1 : vm.metaphase B m d_min Δ φ α ω = p.1 := hω.1.1.1.1.2
      rw [hm1, hξ_leaf p ω hω]
      exact hω.2
  -- pairwise disjoint
  have hdisj : (↑I : Set _).Pairwise (Function.onFun Disjoint Dl) := by
    intro p _ q _ hpq
    apply Set.disjoint_left.mpr
    intro ω hωp hωq
    apply hpq
    have hp1 : vm.metaphase B m d_min Δ φ α ω = p.1 := hωp.1.1.1.1.2
    have hq1 : vm.metaphase B m d_min Δ φ α ω = q.1 := hωq.1.1.1.1.2
    have h1 : p.1 = q.1 := by rw [← hp1, hq1]
    have hp2 : vm.opinionSet (TemporalGraph.phaseTime Δ φ p.1) ω = p.2.1 := hωp.1.1.1.2
    have hq2 : vm.opinionSet (TemporalGraph.phaseTime Δ φ q.1) ω = q.2.1 := hωq.1.1.1.2
    have h2 : p.2.1 = q.2.1 := by rw [← hp2, ← hq2, h1]
    have hp3 : vm.smallOpinions (TemporalGraph.phaseTime Δ φ
        (p.1 + k * TemporalGraph.xiAlpha b m d_min p.2.1.card)) p.2.1 m ω = p.2.2.1 := hωp.1.1.2
    have hq3 : vm.smallOpinions (TemporalGraph.phaseTime Δ φ
        (q.1 + k * TemporalGraph.xiAlpha b m d_min q.2.1.card)) q.2.1 m ω = q.2.2.1 := hωq.1.1.2
    have h3 : p.2.2.1 = q.2.2.1 := by rw [← hp3, ← hq3, h1, h2]
    have hp4 : (vm.opinionSet (TemporalGraph.phaseTime Δ φ
        (p.1 + k * TemporalGraph.xiAlpha b m d_min p.2.1.card)) ω).card = p.2.2.2 := hωp.1.2
    have hq4 : (vm.opinionSet (TemporalGraph.phaseTime Δ φ
        (q.1 + k * TemporalGraph.xiAlpha b m d_min q.2.1.card)) ω).card = q.2.2.2 := hωq.1.2
    have h4 : p.2.2.2 = q.2.2.2 := by rw [← hp4, ← hq4, h1, h2]
    exact Prod.ext h1 (Prod.ext h2 (Prod.ext h3 h4))
  -- integrability on each leaf
  have hint : ∀ p ∈ I, MeasureTheory.IntegrableOn
      ((vm.blockTailSet B m d_min b Δ φ α (k + 1)).indicator (fun _ => (1 : ℝ))) (Dl p) vm.μ :=
    fun p _ => ((integrable_const (1 : ℝ)).indicator hBk1meas).integrableOn
  -- assemble
  rw [hunion, MeasureTheory.integral_biUnion_finset I hmeas hdisj hint,
    measure_biUnion_finset hdisj hmeas,
    ENNReal.toReal_sum (fun p _ => measure_ne_top _ _), Finset.mul_sum]
  refine Finset.sum_le_sum (fun p hp => ?_)
  -- on the leaf, the survival indicator equals the concrete one
  have hindeq : ∫ ω in Dl p,
        (vm.blockTailSet B m d_min b Δ φ α (k + 1)).indicator (fun _ => (1 : ℝ)) ω ∂vm.μ
      = ∫ ω in Dl p, ({ω | p.1 + (k + 1) * TemporalGraph.xiAlpha b m d_min p.2.1.card
              < vm.metaphase B m d_min Δ φ (α + 1) ω}).indicator (fun _ => (1 : ℝ)) ω ∂vm.μ := by
    refine MeasureTheory.setIntegral_congr_fun (hmeas p hp) (fun ω hω => ?_)
    have hm1 : vm.metaphase B m d_min Δ φ α ω = p.1 := hω.1.1.1.1.2
    have hiff : ω ∈ vm.blockTailSet B m d_min b Δ φ α (k + 1) ↔
        ω ∈ {ω | p.1 + (k + 1) * TemporalGraph.xiAlpha b m d_min p.2.1.card
            < vm.metaphase B m d_min Δ φ (α + 1) ω} := by
      simp only [VoterModelAbstract.blockTailSet, Set.mem_setOf_eq, hm1, hξ_leaf p ω hω]
    by_cases hb : ω ∈ vm.blockTailSet B m d_min b Δ φ α (k + 1)
    · rw [Set.indicator_of_mem hb, Set.indicator_of_mem (hiff.mp hb)]
    · rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem (fun h => hb (hiff.mpr h))]
  rw [hindeq]
  exact vm.one_block_leaf_final B m d_min b Δ φ hmono hd hd_pos hΔ_pos hφ_nn hφ_le1 hreach hwin
    hb_large hm_pos hvol α k p.1 p.2.1 p.2.2.1 p.2.2.2 S hS

/-- **STEP 2.** From the single-block bound (STEP 1), the geometric tail
`htail` follows by a set-integral induction on `k` (no tower required, since
`B_α^{k+1} ⊆ B_α^k` chains the bound directly). -/
theorem VoterModelAbstract.htail_of_one_block
    (hmono : Monotone (TemporalGraph.phaseTime Δ φ)) (α : ℕ)
    (hone : ∀ k S, MeasurableSet[(vm.metaphase_isStoppingTime B m d_min Δ φ hmono α).measurableSpace] S →
      ∫ ω in S ∩ vm.blockTailSet B m d_min b Δ φ α k,
          (vm.blockTailSet B m d_min b Δ φ α (k + 1)).indicator (fun _ => (1 : ℝ)) ω ∂vm.μ
        ≤ (2 / 3) * ((vm.μ : Measure Ω) (S ∩ vm.blockTailSet B m d_min b Δ φ α k)).toReal) :
    ∀ k, (vm.μ : Measure Ω)[Set.indicator {ω | k + 1 ≤ vm.metaphaseBlockCount B m d_min b Δ φ α ω}
          (fun _ => (1 : ℝ)) | (vm.metaphase_isStoppingTime B m d_min Δ φ hmono α).measurableSpace]
        ≤ᵐ[(vm.μ : Measure Ω)] (fun _ => ((2 : ℝ) / 3) ^ k) := by
  set hτ := vm.metaphase_isStoppingTime B m d_min Δ φ hmono α with hτdef
  have hm := hτ.measurableSpace_le
  have hBmeas : ∀ k, MeasurableSet (vm.blockTailSet B m d_min b Δ φ α k) :=
    fun k => vm.blockTailSet_measurable B m d_min b Δ φ hmono α k
  -- set-integral form of the tail bound
  have hSI : ∀ k, ∀ S, MeasurableSet[hτ.measurableSpace] S →
      ∫ ω in S, (vm.blockTailSet B m d_min b Δ φ α k).indicator (fun _ => (1 : ℝ)) ω ∂vm.μ
        ≤ (2 / 3) ^ k * ((vm.μ : Measure Ω) S).toReal := by
    intro k
    induction k with
    | zero =>
      intro S hS
      rw [vm.setIntegral_indicator_one S _ (hBmeas 0)]
      simp only [pow_zero, one_mul]
      exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono Set.inter_subset_left)
    | succ k ih =>
      intro S hS
      have hSm := hm S hS
      have h1 := hone k S hS
      -- LHS at k+1 over S equals over S ∩ B_k (since B_{k+1} ⊆ B_k)
      have hbridge : ∫ ω in S,
            (vm.blockTailSet B m d_min b Δ φ α (k + 1)).indicator (fun _ => (1 : ℝ)) ω ∂vm.μ
          = ∫ ω in S ∩ vm.blockTailSet B m d_min b Δ φ α k,
            (vm.blockTailSet B m d_min b Δ φ α (k + 1)).indicator (fun _ => (1 : ℝ)) ω ∂vm.μ := by
        rw [vm.setIntegral_indicator_one S _ (hBmeas (k + 1)),
          vm.setIntegral_indicator_one _ _ (hBmeas (k + 1))]
        congr 1
        rw [Set.inter_assoc, Set.inter_eq_self_of_subset_right
          (vm.blockTailSet_antitone B m d_min b Δ φ α k)]
      rw [hbridge]
      -- μ(S ∩ B_k).toReal = ∫_S 𝟙_{B_k}
      have hval : ((vm.μ : Measure Ω) (S ∩ vm.blockTailSet B m d_min b Δ φ α k)).toReal
          = ∫ ω in S, (vm.blockTailSet B m d_min b Δ φ α k).indicator (fun _ => (1 : ℝ)) ω ∂vm.μ :=
        (vm.setIntegral_indicator_one S _ (hBmeas k)).symm
      calc ∫ ω in S ∩ vm.blockTailSet B m d_min b Δ φ α k,
              (vm.blockTailSet B m d_min b Δ φ α (k + 1)).indicator (fun _ => (1 : ℝ)) ω ∂vm.μ
          ≤ (2 / 3) * ((vm.μ : Measure Ω) (S ∩ vm.blockTailSet B m d_min b Δ φ α k)).toReal := h1
        _ = (2 / 3) * ∫ ω in S,
              (vm.blockTailSet B m d_min b Δ φ α k).indicator (fun _ => (1 : ℝ)) ω ∂vm.μ := by
            rw [hval]
        _ ≤ (2 / 3) * ((2 / 3) ^ k * ((vm.μ : Measure Ω) S).toReal) := by
            apply mul_le_mul_of_nonneg_left (ih S hS) (by norm_num)
        _ = (2 / 3) ^ (k + 1) * ((vm.μ : Measure Ω) S).toReal := by ring
  -- convert to conditional expectation
  intro k
  rw [vm.blockCount_succ_le_eq_blockTailSet B m d_min b Δ φ α k]
  refine condExp_le_const_of_forall_setIntegral_le hm
    ((integrable_const (1 : ℝ)).indicator (hBmeas k)) (fun S hS => ?_)
  rw [setIntegral_const, smul_eq_mul, mul_comm]
  exact hSI k S hS

/-- **STEP 3.** The unconditional metaphase-increment bound, taking only the
single-block bound (STEP 1) as input: `E[R_{α+1} − R_α | 𝒢_{R_α}] ≤ 3·ξ_α`. -/
theorem VoterModelAbstract.metaphase_increment_le_of_one_block
    (hmono : Monotone (TemporalGraph.phaseTime Δ φ)) (hb : 0 ≤ b) (hd : 0 < d_min) (α : ℕ)
    (hone : ∀ k S, MeasurableSet[(vm.metaphase_isStoppingTime B m d_min Δ φ hmono α).measurableSpace] S →
      ∫ ω in S ∩ vm.blockTailSet B m d_min b Δ φ α k,
          (vm.blockTailSet B m d_min b Δ φ α (k + 1)).indicator (fun _ => (1 : ℝ)) ω ∂vm.μ
        ≤ (2 / 3) * ((vm.μ : Measure Ω) (S ∩ vm.blockTailSet B m d_min b Δ φ α k)).toReal) :
    (vm.μ : Measure Ω)[(fun ω => (vm.metaphase B m d_min Δ φ (α + 1) ω : ℝ)
            - (vm.metaphase B m d_min Δ φ α ω : ℝ)) |
        (vm.metaphase_isStoppingTime B m d_min Δ φ hmono α).measurableSpace]
      ≤ᵐ[(vm.μ : Measure Ω)] (fun ω => 3 * (vm.metaphaseXi B m d_min b Δ φ α ω : ℝ)) :=
  vm.metaphase_increment_le B m d_min b Δ φ hmono hb hd α
    (vm.htail_of_one_block B m d_min b Δ φ hmono α hone)

/-- **Metaphase increment bound (unconditional, §3.4).**
`E[R_{α+1} − R_α | 𝒢_{R_α}] ≤ 3·ξ_α`. The full assembly: the single-block bound
`one_block_random_index` (finite decomposition + `per_metaphase_two_thirds` per leaf)
feeds the geometric-tail `htail_of_one_block`, closing `metaphase_increment_le`. -/
theorem VoterModelAbstract.metaphase_increment_le_final
    (hmono : Monotone (TemporalGraph.phaseTime Δ φ))
    (hd : d_min = G.minDegreeAt 0) (hd_pos : 0 < d_min) (hb : 0 ≤ b) (hΔ_pos : ∀ j, 1 ≤ Δ j)
    (hφ_nn : ∀ j, 0 ≤ φ j) (hφ_le1 : ∀ j, φ j ≤ 1)
    (hreach : TemporalGraph.reachUpToRMax B m d_min φ)
    (hwin : ∀ j, ∀ Sc ∈ G.admissibleCuts,
      φ j ≤ G.maxSetConductanceOnInterval (∑ i ∈ Finset.range j, Δ i) (Δ j) Sc)
    (hb_large : (5462 : ℝ) ≤ b) (hm_pos : 0 < m)
    (hvol : ∀ t, (TemporalGraph.volume G.toTemporalGraph t Finset.univ : ℝ) ≤ 2 * m) (α : ℕ) :
    (vm.μ : Measure Ω)[(fun ω => (vm.metaphase B m d_min Δ φ (α + 1) ω : ℝ)
            - (vm.metaphase B m d_min Δ φ α ω : ℝ)) |
        (vm.metaphase_isStoppingTime B m d_min Δ φ hmono α).measurableSpace]
      ≤ᵐ[(vm.μ : Measure Ω)] (fun ω => 3 * (vm.metaphaseXi B m d_min b Δ φ α ω : ℝ)) :=
  vm.metaphase_increment_le_of_one_block B m d_min b Δ φ hmono hb hd_pos α
    (fun k S hS => vm.one_block_random_index B m d_min b Δ φ hmono hd hd_pos hΔ_pos hφ_nn
      hφ_le1 hreach hwin hb_large hm_pos hvol α k S hS)

end TemporalGraph
