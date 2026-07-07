module

public import VoterProcess.OpinionCoupling
import VoterProcess.Absorption.Basic

/-! ## Multi-opinion Markov properties via the per-opinion (`phiQ`) coupling

For the general κ-opinion voter model `TemporalGraph.VoterModelAbstract G κ Ω`, this file
lifts the conditional one-step Markov property `vm.markovProperty` to a multistep,
filtration-level identity, and then projects it through the per-opinion map
`phiQ q ξ = {v | ξ v = q}` to obtain the two-opinion `opinionProcess₂` factorization
on the `q`-set. These are the load-bearing identities for the §3.4 reduction of the
multi-opinion bound to the two-opinion bound (opinion `q` versus all the rest).

The development generalizes `VoterModel/Proof/DeterministicFiber.lean`
(`multistep_markov_filtration₂`, two opinions) and the fiber helpers of
`VoterModel/Spec/VoterModelTwoOpinion.lean` (the `q = 0`, `κ = 2` case)
from `phiZero`/`Fin 2` to `phiQ q`/`Fin κ`.

## Main results

- `VoterModel.phiQ_consensus` — at consensus the `q`-set is `∅` or `univ`.
- `TemporalGraph.multistep_markov_filtration` — for `B ∈ ℱ_t`,
  `μ(B ∩ {ξ_{t+Δ} = g}) = ∫_B opinionProcess G t Δ (ξ_t ω) g dμ`.
- `TemporalGraph.multistep_markov_phiQ` — for `B ∈ ℱ_t`,
  `μ(B ∩ {phiQ q ξ_{t+Δ} = T}) = ∫_B opinionProcess₂ G t Δ (phiQ q ξ_t ω) T dμ`.
- `TemporalGraph.qset_persistent` — `phiQ q ξ ∈ {∅, univ}` persists one step a.s.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Classical

noncomputable section

namespace VoterModel

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V] {κ : ℕ} [NeZero κ]


end VoterModel

namespace TemporalGraph

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V] {κ : ℕ} [NeZero κ]
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {G : TemporalGraph V}

/-! ### `phiQ`-fiber machinery (generalizing the `phiZero` helpers) -/

/-- The fiber of `phiQ q` over `T`: opinion functions whose `q`-set is `T`. -/
def fibQ (q : Fin κ) (T : Finset V) : Finset (V → Fin κ) :=
  Finset.univ.filter (fun f => VoterModel.phiQ q f = T)

omit [Nonempty V] [NeZero κ] in
theorem mem_fibQ {q : Fin κ} {f : V → Fin κ} {T : Finset V} :
    f ∈ fibQ q T ↔ VoterModel.phiQ q f = T := by
  simp [fibQ]

/-- Each fiber event `{ω | ξ_j ω = g}` is measurable (discrete σ-algebra on `V → Fin κ`). -/
theorem xiK_eq_measurable (vm : VoterModelAbstract G κ Ω) (j : ℕ) (g : V → Fin κ) :
    MeasurableSet {ω | vm.ξ j ω = g} :=
  vm.hξ_meas j _ ⟨{g}, trivial, by ext ω; simp [Set.mem_preimage]⟩

/-- Decompose `{ω | phiQ q (ξ_j ω) = T}` as the disjoint union of fiber events. -/
theorem phiQ_event_eq (vm : VoterModelAbstract G κ Ω) (j : ℕ) (q : Fin κ) (T : Finset V) :
    {ω | VoterModel.phiQ q (vm.ξ j ω) = T} = ⋃ g ∈ fibQ q T, {ω | vm.ξ j ω = g} := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, mem_fibQ]
  exact ⟨fun h => ⟨vm.ξ j ω, h, rfl⟩, fun ⟨_, hf, hω⟩ => hω ▸ hf⟩

/-- The event `{ω | phiQ q (ξ_j ω) = T}` is `ℱ_j`-measurable. -/
theorem phiQ_event_filtration (vm : VoterModelAbstract G κ Ω) (j : ℕ) (q : Fin κ) (T : Finset V) :
    @MeasurableSet Ω (vm.ℱ j) {ω | VoterModel.phiQ q (vm.ξ j ω) = T} := by
  rw [phiQ_event_eq vm j q T]
  refine MeasurableSet.biUnion (fibQ q T).countable_toSet (fun g _ => ?_)
  exact Measurable.of_comap_le (le_iSup₂_of_le j (Finset.mem_Iic.mpr le_rfl) le_rfl)
    (show @MeasurableSet (V → Fin κ) ⊤ {g} from trivial)

omit [Nonempty V] [NeZero κ] in
/-- Summing a `PMF` over a fiber of `phiQ q` equals its pushforward value. -/
theorem fibQ_sum_eq_map (q : Fin κ) (P : PMF (V → Fin κ)) (T : Finset V) :
    ∑ g ∈ fibQ q T, P g = (P.map (VoterModel.phiQ q)) T := by
  rw [PMF.map_apply, tsum_fintype]
  unfold fibQ
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun g _ => ?_
  by_cases h : VoterModel.phiQ q g = T
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg fun he => h he.symm]

/-- `ω ↦ opinionProcess G t Δ (ξ_t ω) g` is measurable. -/
theorem opinionProcess_apply_measurable (vm : VoterModelAbstract G κ Ω) (t Δ : ℕ) (g : V → Fin κ) :
    Measurable (fun ω => (VoterModel.opinionProcess G t Δ (vm.ξ t ω)) g) := by
  have hξ : @Measurable Ω (V → Fin κ) mΩ ⊤ (vm.ξ t) :=
    measurable_iff_comap_le.mpr (vm.hξ_meas t)
  exact (measurable_from_top (f := fun f => (VoterModel.opinionProcess G t Δ f) g)).comp hξ

/-! ### Multistep κ-level Markov property over the filtration -/

/-- Iterated Markov property over the filtration `ℱ_t` for the κ-opinion process.

For any `B ∈ ℱ_t`, the joint event `B ∩ {ξ_{t+Δ} = g}` has probability
`∫_B (opinionProcess G t Δ (ξ_t ω)) g dμ`. Proof by induction on `Δ`, using the
one-step `vm.markovProperty` and the inductive hypothesis on each atom `{ξ_{t+Δ'} = c}`.
This is the κ-opinion generalization of `multistep_markov_filtration₂`. -/
theorem multistep_markov_filtration
    (G : TemporalGraph V) (vm : VoterModelAbstract G κ Ω)
    (t Δ : ℕ) (g : V → Fin κ) (B : Set Ω)
    (hB : @MeasurableSet Ω (vm.ℱ t) B) :
    (vm.μ : Measure _) (B ∩ {ω | vm.ξ (t + Δ) ω = g}) =
      ∫⁻ ω in B, (VoterModel.opinionProcess G t Δ (vm.ξ t ω)) g ∂vm.μ := by
  have hξset_meas : ∀ (j : ℕ) (c : V → Fin κ), MeasurableSet {ω : Ω | vm.ξ j ω = c} :=
    fun j c => xiK_eq_measurable vm j c
  have hBm : MeasurableSet B := vm.ℱ.le t B hB
  have hmeas_op : ∀ (n : ℕ) (c : V → Fin κ),
      Measurable (fun ω => (VoterModel.opinionProcess G t n (vm.ξ t ω)) c) :=
    fun n c => opinionProcess_apply_measurable vm t n c
  induction Δ generalizing g with
  | zero =>
    simp only [VoterModel.opinionProcess, PMF.pure_apply, Nat.add_zero]
    have hbase : ∫⁻ (ω : Ω) in B, (if g = vm.ξ t ω then (1 : ENNReal) else 0) ∂vm.μ
        = (vm.μ : Measure _) (B ∩ {x | vm.ξ t x = g}) := by
      have heq : ∀ ω, (if g = vm.ξ t ω then (1 : ENNReal) else 0) =
          Set.indicator {x | vm.ξ t x = g} (fun _ => 1) ω :=
        fun ω => by simp [Set.indicator_apply, eq_comm]
      simp_rw [heq, setLIntegral_indicator (hξset_meas t g), setLIntegral_one, Set.inter_comm]
    exact_mod_cast hbase.symm
  | succ Δ' ih =>
    show (vm.μ : Measure _) (B ∩ {ω | vm.ξ ((t + Δ') + 1) ω = g}) =
      ∫⁻ ω in B, (VoterModel.opinionProcess G t (Δ' + 1) (vm.ξ t ω)) g ∂vm.μ
    simp only [VoterModel.opinionProcess, PMF.bind_apply]
    have hB_eq : B ∩ {ω | vm.ξ ((t + Δ') + 1) ω = g} =
        ⋃ c : V → Fin κ, B ∩ {ω | vm.ξ (t + Δ') ω = c} ∩ {ω | vm.ξ ((t + Δ') + 1) ω = g} := by
      ext ω; simp [eq_comm]
    have hpw : Pairwise fun (c1 c2 : V → Fin κ) =>
        Disjoint (B ∩ {ω | vm.ξ (t + Δ') ω = c1} ∩ {ω | vm.ξ ((t + Δ') + 1) ω = g})
                 (B ∩ {ω | vm.ξ (t + Δ') ω = c2} ∩ {ω | vm.ξ ((t + Δ') + 1) ω = g}) :=
      fun c1 c2 hne => Set.disjoint_left.mpr fun ω h1 h2 => hne (h1.1.2 ▸ h2.1.2)
    have hmset : ∀ c : V → Fin κ,
        MeasurableSet (B ∩ {ω | vm.ξ (t + Δ') ω = c} ∩ {ω | vm.ξ ((t + Δ') + 1) ω = g}) :=
      fun c => (hBm.inter (hξset_meas (t + Δ') c)).inter (hξset_meas ((t + Δ') + 1) g)
    rw [hB_eq, measure_iUnion (fun c1 c2 hne => hpw hne) hmset]
    have hBt_meas : @MeasurableSet Ω (vm.ℱ (t + Δ')) B :=
      vm.ℱ.mono (Nat.le_add_right t Δ') B hB
    have hcM : ∀ c : V → Fin κ,
        (vm.μ : Measure _) (B ∩ {ω | vm.ξ (t + Δ') ω = c} ∩ {ω | vm.ξ ((t + Δ') + 1) ω = g}) =
          (VoterModel.stepDist G (t + Δ') c) g
            * (vm.μ : Measure _) (B ∩ {ω | vm.ξ (t + Δ') ω = c}) := by
      intro c
      have hBc_filt : @MeasurableSet Ω (⨆ j ∈ Finset.Iic (t + Δ'),
          MeasurableSpace.comap (vm.ξ j) ⊤) (B ∩ {ω | vm.ξ (t + Δ') ω = c}) := by
        apply @MeasurableSet.inter _ _ _ _ hBt_meas
        exact Measurable.of_comap_le
          (le_iSup₂_of_le (t + Δ') (Finset.mem_Iic.mpr le_rfl) le_rfl)
          (show @MeasurableSet (V → Fin κ) ⊤ {c} from trivial)
      rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
          vm.markovProperty (t + Δ') g (B ∩ {ω | vm.ξ (t + Δ') ω = c}) hBc_filt]
      simp only [← VoterModel.stepDist_apply]
      rw [setLIntegral_congr_fun (hBm.inter (hξset_meas (t + Δ') c))
          (fun ω hω => by rw [hω.2])]
      rw [setLIntegral_const, mul_comm]
    simp_rw [hcM]
    simp_rw [ih]
    have hpull : ∀ c : V → Fin κ,
        (VoterModel.stepDist G (t + Δ') c) g *
            ∫⁻ (ω : Ω) in B, (VoterModel.opinionProcess G t Δ' (vm.ξ t ω)) c ∂vm.μ =
          ∫⁻ (ω : Ω) in B,
            (VoterModel.stepDist G (t + Δ') c) g *
              (VoterModel.opinionProcess G t Δ' (vm.ξ t ω)) c ∂vm.μ :=
      fun c => (lintegral_const_mul _ (hmeas_op Δ' c)).symm
    trans (∑' c : V → Fin κ,
        ∫⁻ (ω : Ω) in B,
          (VoterModel.stepDist G (t + Δ') c) g *
            (VoterModel.opinionProcess G t Δ' (vm.ξ t ω)) c ∂vm.μ)
    · congr 1; ext c; exact hpull c
    · rw [← lintegral_tsum (fun c => ((hmeas_op Δ' c).const_mul _).aemeasurable.restrict)]
      congr 1; ext ω; apply tsum_congr; intro c; ring

/-! ### Projection through `phiQ` -/

/-- Multistep Markov property projected through `phiQ q`.

For any `B ∈ ℱ_t` and target `q`-set `T`,
`μ(B ∩ {phiQ q ξ_{t+Δ} = T}) = ∫_B opinionProcess₂ G t Δ (phiQ q ξ_t ω) T dμ`,
the two-opinion `opinionProcess₂` on the `q`-set. Combines
`multistep_markov_filtration`, the fiber decomposition, and the pushforward
`opinionProcess_map_phiQ`. -/
theorem multistep_markov_phiQ
    (G : TemporalGraph V) (vm : VoterModelAbstract G κ Ω)
    (t Δ : ℕ) (q : Fin κ) (T : Finset V) (B : Set Ω)
    (hB : @MeasurableSet Ω (vm.ℱ t) B) :
    (vm.μ : Measure _) (B ∩ {ω | VoterModel.phiQ q (vm.ξ (t + Δ) ω) = T}) =
      ∫⁻ ω in B, (VoterModel.opinionProcess₂ G t Δ (VoterModel.phiQ q (vm.ξ t ω))) T ∂vm.μ := by
  have hBmΩ : MeasurableSet B := vm.ℱ.le t B hB
  rw [phiQ_event_eq vm (t + Δ) q T, Set.inter_iUnion₂,
      measure_biUnion_finset
        (by
          intro g _ g' _ hgg
          refine Set.disjoint_left.mpr fun ω hω hω' => hgg ?_
          simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at hω hω'
          exact hω.2 ▸ hω'.2)
        (fun g _ => hBmΩ.inter (xiK_eq_measurable vm (t + Δ) g))]
  rw [Finset.sum_congr rfl (fun g _ => multistep_markov_filtration G vm t Δ g B hB),
      ← lintegral_finsetSum (fibQ q T)
        (fun g _ => opinionProcess_apply_measurable vm t Δ g)]
  refine lintegral_congr fun ω => ?_
  rw [fibQ_sum_eq_map, VoterModel.opinionProcess_map_phiQ]

/-! ### One-step persistence of the boundary `q`-sets -/

/-- Membership of `phiQ q (ξ_j ω) = T` events is ambient-measurable. -/
theorem xiK_eq_measurable_phiQ (vm : VoterModelAbstract G κ Ω) (j : ℕ) (q : Fin κ) (T : Finset V) :
    MeasurableSet {ω | VoterModel.phiQ q (vm.ξ j ω) = T} :=
  vm.ℱ.le j _ (phiQ_event_filtration vm j q T)

/-- `opinionProcess₂ G s 1 Z Z = 1` whenever `stepDist₂ G s Z = PMF.pure Z`. -/
private theorem opinionProcess₂_one_fixed (s : ℕ) (Z : Finset V)
    (hZ : VoterModel.stepDist₂ G s Z = PMF.pure Z) :
    VoterModel.opinionProcess₂ G s 1 Z Z = 1 := by
  show ((VoterModel.opinionProcess₂ G s 0 Z).bind
      (fun ζ => VoterModel.stepDist₂ G (s + 0) ζ)) Z = 1
  rw [show VoterModel.opinionProcess₂ G s 0 Z = PMF.pure Z from rfl, PMF.pure_bind,
      Nat.add_zero, hZ, PMF.pure_apply]
  simp

private theorem qset_persistent_aux (vm : VoterModelAbstract G κ Ω) (q : Fin κ) (s : ℕ)
    (Z : Finset V) (hZ : VoterModel.opinionProcess₂ G s 1 Z Z = 1) :
    ∀ᵐ ω ∂(vm.μ : Measure _), VoterModel.phiQ q (vm.ξ s ω) = Z →
      VoterModel.phiQ q (vm.ξ (s + 1) ω) = Z := by
  set B : Set Ω := {ω | VoterModel.phiQ q (vm.ξ s ω) = Z} with hBdef
  set C : Set Ω := {ω | VoterModel.phiQ q (vm.ξ (s + 1) ω) = Z} with hCdef
  have hB_filt : @MeasurableSet Ω (vm.ℱ s) B := phiQ_event_filtration vm s q Z
  have hBm : MeasurableSet B := vm.ℱ.le s B hB_filt
  have hCm : MeasurableSet C := xiK_eq_measurable_phiQ vm (s + 1) q Z
  -- Mass identity: μ(B ∩ C) = μ B.
  have hkey : (vm.μ : Measure _) (B ∩ C) = (vm.μ : Measure _) B := by
    have h5 := multistep_markov_phiQ G vm s 1 q Z B hB_filt
    show (vm.μ : Measure _) (B ∩ {ω | VoterModel.phiQ q (vm.ξ (s + 1) ω) = Z})
      = (vm.μ : Measure _) B
    rw [h5, setLIntegral_congr_fun hBm (fun ω hω => by
      show VoterModel.opinionProcess₂ G s 1 (VoterModel.phiQ q (vm.ξ s ω)) Z = 1
      rw [(hω : VoterModel.phiQ q (vm.ξ s ω) = Z)]; exact hZ)]
    rw [setLIntegral_one]
  -- Hence μ(B \ C) = 0.
  have hdiff : (vm.μ : Measure _) (B \ C) = 0 := by
    have hadd := measure_inter_add_sdiff (μ := (vm.μ : Measure _)) B hCm
    rw [hkey] at hadd
    have hBfin : (vm.μ : Measure _) B ≠ ⊤ := measure_ne_top _ _
    simpa [hBfin] using hadd
  rw [ae_iff]
  have hset : {ω | ¬ (VoterModel.phiQ q (vm.ξ s ω) = Z →
      VoterModel.phiQ q (vm.ξ (s + 1) ω) = Z)} = B \ C := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_sdiff, Classical.not_imp, hBdef, hCdef]
  rw [hset]; exact hdiff

/-- The boundary `q`-sets `∅` and `univ` are one-step absorbing a.s.: if the `q`-set
of `ξ_s` is `∅` (resp. `univ`) then a.s. the `q`-set of `ξ_{s+1}` is `∅` (resp. `univ`).
Reduces, via the pushforward `stepDist_map_phiQ`, to the two-opinion `stepDist₂`
empty/univ persistence (`stepDist₂_empty`, `stepDist₂_univ`). -/
theorem qset_persistent (vm : VoterModelAbstract G κ Ω) (q : Fin κ) (s : ℕ) :
    (∀ᵐ ω ∂(vm.μ : Measure _), VoterModel.phiQ q (vm.ξ s ω) = ∅ →
        VoterModel.phiQ q (vm.ξ (s + 1) ω) = ∅) ∧
    (∀ᵐ ω ∂(vm.μ : Measure _), VoterModel.phiQ q (vm.ξ s ω) = univ →
        VoterModel.phiQ q (vm.ξ (s + 1) ω) = univ) := by
  refine ⟨qset_persistent_aux vm q s ∅ ?_, qset_persistent_aux vm q s univ ?_⟩
  · exact opinionProcess₂_one_fixed s ∅ (VoterModel.stepDist₂_empty G s)
  · exact opinionProcess₂_one_fixed s univ (VoterModel.stepDist₂_univ G s)

end TemporalGraph
