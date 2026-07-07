module

public import VoterProcess.TwoOpinion
public import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-! ## Canonical construction of `TemporalGraph.VoterModelAbstract G κ Ω` (general `κ`)

This file provides a `TemporalGraph.VoterModelAbstract G κ Ω` for any temporal graph `G`
and any opinion count `κ`, where `Ω = ℕ → (V → Fin κ)` is the full trajectory space of
opinion functions, carrying the Ionescu–Tulcea trajectory measure built from the
`κ`-opinion step kernel `stepDist`. Unlike the two-opinion
`CanonicalConstruction.lean`, the opinion process is the coordinate evaluation
`ξ t ω = ω t` directly, so no `phiZero` bridge is needed.

The existence of this term certifies that the abstract `TemporalGraph.VoterModelAbstract`
structure is **non-vacuous** for every `κ`: the universally quantified headline
upper-bound theorems are not vacuously true.

## Main definitions

- `voterKernel G n` — the `κ`-opinion step kernel on path prefixes.
- `ofDeterministicAbstract G ξ₀` — the canonical `VoterModelAbstract G κ (ℕ → (V → Fin κ))` with
  deterministic initial law `ξ₀` and coordinate process `ξ t ω = ω t`.

## Main results

- `voterTrajectoryMeasureFrom_markovProperty` — conditional Markov property.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Preorder Filter
open scoped BigOperators ENNReal Topology

noncomputable section

namespace VoterModel

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V] {κ : ℕ} [NeZero κ]

/-- The state-space family for the `κ`-opinion trajectory-space realization. -/
abbrev OpinionStateFamily (V : Type*) (κ : ℕ) : ℕ → Type _ := fun _ => (V → Fin κ)

/-- The space of `κ`-opinion trajectories. -/
abbrev OpinionTrajectorySpace (V : Type*) (κ : ℕ) : Type _ := ℕ → (V → Fin κ)

/-- The prefix type recording opinion functions up to time `n`. -/
abbrev OpinionPrefixType (V : Type*) (κ : ℕ) (n : ℕ) : Type _ :=
  Π i : Finset.Iic n, OpinionStateFamily V κ i

/-- The `κ`-opinion voter step kernel on path prefixes. -/
def voterKernel (G : TemporalGraph V) (n : ℕ) :
    Kernel (OpinionPrefixType V κ n) (V → Fin κ) :=
  Kernel.ofFunOfCountable (fun x => (stepDist G n (x ⟨n, by simp⟩)).toMeasure)

instance (G : TemporalGraph V) (n : ℕ) : IsMarkovKernel (voterKernel G (κ := κ) n) where
  isProbabilityMeasure x := by
    change IsProbabilityMeasure ((stepDist G n (x ⟨n, by simp⟩)).toMeasure)
    infer_instance

/-- The `κ`-opinion path law obtained by iterating `voterKernel` from `μ0`. -/
abbrev voterTrajectoryMeasureFrom (G : TemporalGraph V) (μ0 : Measure (V → Fin κ)) :
    Measure (OpinionTrajectorySpace V κ) :=
  Kernel.trajMeasure (X := OpinionStateFamily V κ) μ0 (fun n => voterKernel G n)

omit [NeZero κ] in
/-- The conditional Markov property of the `κ`-opinion trajectory measure: for any
set `B` measurable w.r.t. the path filtration up to `n`,
`μ(B ∩ {ω (n+1) = g}) = ∫⁻ ω in B, stepDist G n (ω n) {g} ∂μ`. -/
theorem voterTrajectoryMeasureFrom_markovProperty
    (G : TemporalGraph V) (μ₀ : Measure (V → Fin κ)) [IsProbabilityMeasure μ₀]
    (n : ℕ) (g : V → Fin κ) (B : Set (OpinionTrajectorySpace V κ))
    (hB : @MeasurableSet (OpinionTrajectorySpace V κ) (⨆ i ∈ Finset.Iic n,
      MeasurableSpace.comap (fun ω : OpinionTrajectorySpace V κ => ω i)
        (inferInstance : MeasurableSpace (V → Fin κ))) B) :
    voterTrajectoryMeasureFrom G μ₀ (B ∩ {ω | ω (n + 1) = g}) =
      ∫⁻ ω in B, (stepDist G n (ω n)).toMeasure {g}
        ∂voterTrajectoryMeasureFrom G μ₀ := by
  classical
  set μ := voterTrajectoryMeasureFrom G μ₀
  have hcompProd :
      μ.map (frestrictLe n) ⊗ₘ voterKernel G n =
        μ.map (fun x => (frestrictLe n x, x (n + 1))) :=
    ProbabilityTheory.Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
  have hfilt_eq :
      (⨆ i ∈ Finset.Iic n,
        MeasurableSpace.comap (fun (ω : OpinionTrajectorySpace V κ) => ω i)
          (inferInstance : MeasurableSpace (V → Fin κ))) =
      MeasureTheory.Filtration.piLE (X := OpinionStateFamily V κ) n := by
    rw [Filtration.piLE_eq_comap_frestrictLe]
    change _ = MeasurableSpace.pi.comap (frestrictLe (π := OpinionStateFamily V κ) n)
    unfold MeasurableSpace.pi
    rw [MeasurableSpace.comap_iSup]
    simp only [MeasurableSpace.comap_comp]
    apply le_antisymm
    · apply iSup₂_le
      intro i hi
      rw [Finset.mem_Iic] at hi
      exact le_trans (le_of_eq (by congr 1))
        (le_iSup _ ⟨i, Finset.mem_Iic.mpr hi⟩)
    · apply iSup_le
      intro ⟨j, hj⟩
      rw [Finset.mem_Iic] at hj
      exact le_trans (le_of_eq (by congr 1))
        (le_iSup₂ j (Finset.mem_Iic.mpr hj))
  rw [hfilt_eq, Filtration.piLE_eq_comap_frestrictLe] at hB
  obtain ⟨A, hA, hAB⟩ := MeasurableSpace.measurableSet_comap.mp hB
  subst hAB
  have hinter :
      frestrictLe (π := OpinionStateFamily V κ) n ⁻¹' A ∩ {ω | ω (n + 1) = g} =
      (fun ω => (frestrictLe n ω, ω (n + 1))) ⁻¹' (A ×ˢ {g}) := by
    ext ω; simp [Set.mem_prod]
  rw [hinter,
    ← Measure.map_apply (by fun_prop) (hA.prod (MeasurableSet.singleton g)),
    ← hcompProd,
    Measure.compProd_apply_prod hA (MeasurableSet.singleton g)]
  have hκ_meas : Measurable (fun h => voterKernel G n h {g}) := by
    refine (Kernel.measurable_coe _ (MeasurableSet.singleton g)).comp ?_
    exact measurable_id
  rw [setLIntegral_map hA hκ_meas (measurable_frestrictLe n)]
  refine setLIntegral_congr_fun (measurable_frestrictLe n hA) (fun ω _ => ?_)
  show voterKernel G n (frestrictLe n ω) {g} = (stepDist G n (ω n)).toMeasure {g}
  simp only [voterKernel, Kernel.ofFunOfCountable]
  rfl

omit [NeZero κ] in
/-- The conditional Markov property iterated `Δ` steps:
`μ(B ∩ {ω (t+Δ) = S'}) = ∫⁻ ω in B, opinionProcess G t Δ (ω t) S' ∂μ`
for `B` measurable in `⨆ i ∈ Iic t, comap (eval i) ⊤`. -/
theorem voterTrajectoryMeasureFrom_multistep_filtration
    (G : TemporalGraph V) (μ₀ : Measure (V → Fin κ)) [IsProbabilityMeasure μ₀]
    (t Δ : ℕ) (S' : V → Fin κ) (B : Set (OpinionTrajectorySpace V κ))
    (hB : @MeasurableSet (OpinionTrajectorySpace V κ) (⨆ i ∈ Finset.Iic t,
      MeasurableSpace.comap (fun ω : OpinionTrajectorySpace V κ => ω i)
        (inferInstance : MeasurableSpace (V → Fin κ))) B) :
    voterTrajectoryMeasureFrom G μ₀ (B ∩ {ω | ω (t + Δ) = S'}) =
      ∫⁻ ω in B, (VoterModel.opinionProcess G t Δ (ω t)) S'
        ∂voterTrajectoryMeasureFrom G μ₀ := by
  classical
  set μ := voterTrajectoryMeasureFrom G μ₀ with hμ_def
  -- Ambient measurability of B
  have hBm : MeasurableSet B := by
    have hle : (⨆ i ∈ Finset.Iic t,
        MeasurableSpace.comap (fun ω : OpinionTrajectorySpace V κ => ω i)
          (inferInstance : MeasurableSpace (V → Fin κ))) ≤
      (inferInstance : MeasurableSpace (OpinionTrajectorySpace V κ)) := by
      apply iSup₂_le
      intro i _
      exact (measurable_pi_apply i).comap_le
    exact hle _ hB
  -- The function ω ↦ opinionProcess G t n (ω t) S' is measurable
  have hmeas_op : ∀ (n : ℕ) (T' : V → Fin κ),
      Measurable (fun ω : OpinionTrajectorySpace V κ =>
        (VoterModel.opinionProcess G t n (ω t)) T') := by
    intro n T'
    have hop_meas : Measurable
        (fun s : V → Fin κ => (VoterModel.opinionProcess G t n s) T') :=
      measurable_of_finite _
    exact hop_meas.comp (measurable_pi_apply t)
  have hAset_meas : ∀ (j : ℕ) (T : V → Fin κ),
      MeasurableSet {ω : OpinionTrajectorySpace V κ | ω j = T} := by
    intro j T
    have : Measurable (fun ω : OpinionTrajectorySpace V κ => ω j) := measurable_pi_apply j
    exact this (by exact MeasurableSet.singleton T : MeasurableSet ({T} : Set (V → Fin κ)))
  induction Δ generalizing S' with
  | zero =>
    -- opinionProcess G t 0 a = PMF.pure a
    simp only [VoterModel.opinionProcess, PMF.pure_apply, Nat.add_zero]
    have hbase : ∫⁻ (ω : OpinionTrajectorySpace V κ) in B,
          (if S' = ω t then (1:ENNReal) else 0) ∂μ =
        μ (B ∩ {x | x t = S'}) := by
      have heq : ∀ ω : OpinionTrajectorySpace V κ,
          (if S' = ω t then (1:ENNReal) else 0) =
          Set.indicator {x : OpinionTrajectorySpace V κ | x t = S'} (fun _ => 1) ω :=
        fun ω => by simp [Set.indicator_apply, eq_comm]
      simp_rw [heq, setLIntegral_indicator (hAset_meas t S'), setLIntegral_one,
        Set.inter_comm]
    exact_mod_cast hbase.symm
  | succ Δ' ih =>
    show μ (B ∩ {ω | ω ((t + Δ') + 1) = S'}) =
      ∫⁻ ω in B, (VoterModel.opinionProcess G t (Δ' + 1) (ω t)) S' ∂μ
    -- opinionProcess G t (Δ'+1) a = (opinionProcess G t Δ' a).bind (stepDist G (t+Δ'))
    simp only [VoterModel.opinionProcess, PMF.bind_apply]
    -- Partition B ∩ {ω (t+Δ'+1) = S'} over atoms {ω (t+Δ') = T'}
    have hB_eq : B ∩ {ω : OpinionTrajectorySpace V κ | ω ((t + Δ') + 1) = S'} =
        ⋃ T' : V → Fin κ,
          B ∩ {ω | ω (t + Δ') = T'} ∩ {ω | ω ((t + Δ') + 1) = S'} := by
      ext ω; simp [eq_comm]
    have hpw : Pairwise fun (T1 T2 : V → Fin κ) =>
        Disjoint
          (B ∩ {ω : OpinionTrajectorySpace V κ | ω (t + Δ') = T1} ∩
            {ω | ω ((t + Δ') + 1) = S'})
          (B ∩ {ω | ω (t + Δ') = T2} ∩ {ω | ω ((t + Δ') + 1) = S'}) :=
      fun T1 T2 hne =>
        Set.disjoint_left.mpr fun ω h1 h2 => hne (h1.1.2 ▸ h2.1.2)
    have hmset : ∀ T' : V → Fin κ,
        MeasurableSet
          (B ∩ {ω : OpinionTrajectorySpace V κ | ω (t + Δ') = T'} ∩
            {ω | ω ((t + Δ') + 1) = S'}) :=
      fun T' =>
        (hBm.inter (hAset_meas (t + Δ') T')).inter (hAset_meas ((t + Δ') + 1) S')
    rw [hB_eq, measure_iUnion (fun T1 T2 hne => hpw hne) hmset]
    -- B ∈ ⨆ j ∈ Iic (t+Δ'), comap (eval j) ⊤, since t ≤ t+Δ'
    have hBt_meas : @MeasurableSet (OpinionTrajectorySpace V κ)
        (⨆ i ∈ Finset.Iic (t + Δ'),
          MeasurableSpace.comap (fun ω : OpinionTrajectorySpace V κ => ω i)
            (inferInstance : MeasurableSpace (V → Fin κ))) B := by
      have hmono : (⨆ i ∈ Finset.Iic t,
          MeasurableSpace.comap (fun ω : OpinionTrajectorySpace V κ => ω i)
            (inferInstance : MeasurableSpace (V → Fin κ))) ≤
        (⨆ i ∈ Finset.Iic (t + Δ'),
          MeasurableSpace.comap (fun ω : OpinionTrajectorySpace V κ => ω i)
            (inferInstance : MeasurableSpace (V → Fin κ))) := by
        apply iSup₂_le
        intro i hi
        rw [Finset.mem_Iic] at hi
        exact le_iSup₂_of_le i
          (Finset.mem_Iic.mpr (le_trans hi (Nat.le_add_right t Δ'))) le_rfl
      exact hmono _ hB
    -- For each T', apply markovProperty at (t+Δ') with B' := B ∩ {ω (t+Δ') = T'}.
    have hcM : ∀ T' : V → Fin κ,
        μ (B ∩ {ω : OpinionTrajectorySpace V κ | ω (t + Δ') = T'} ∩
            {ω | ω ((t + Δ') + 1) = S'}) =
          (VoterModel.stepDist G (t + Δ') T').toMeasure {S'} *
            μ (B ∩ {ω | ω (t + Δ') = T'}) := by
      intro T'
      have hBT'_filt : @MeasurableSet (OpinionTrajectorySpace V κ)
          (⨆ i ∈ Finset.Iic (t + Δ'),
            MeasurableSpace.comap (fun ω : OpinionTrajectorySpace V κ => ω i)
              (inferInstance : MeasurableSpace (V → Fin κ)))
          (B ∩ {ω | ω (t + Δ') = T'}) := by
        apply MeasurableSet.inter hBt_meas
        have hsub : MeasurableSpace.comap
            (fun ω : OpinionTrajectorySpace V κ => ω (t + Δ'))
            (inferInstance : MeasurableSpace (V → Fin κ)) ≤
          (⨆ i ∈ Finset.Iic (t + Δ'),
            MeasurableSpace.comap (fun ω : OpinionTrajectorySpace V κ => ω i)
              (inferInstance : MeasurableSpace (V → Fin κ))) :=
          le_iSup₂_of_le (t + Δ') (Finset.mem_Iic.mpr le_rfl) le_rfl
        apply hsub
        exact ⟨{T'}, MeasurableSet.singleton T', by ext; simp⟩
      rw [voterTrajectoryMeasureFrom_markovProperty G μ₀ (t + Δ') S'
        (B ∩ {ω | ω (t + Δ') = T'}) hBT'_filt]
      rw [setLIntegral_congr_fun (hBm.inter (hAset_meas (t + Δ') T'))
        (g := fun _ => (VoterModel.stepDist G (t + Δ') T').toMeasure {S'})
        (fun ω hω => by
          show (VoterModel.stepDist G (t + Δ') (ω (t + Δ'))).toMeasure {S'} =
            (VoterModel.stepDist G (t + Δ') T').toMeasure {S'}
          rw [show ω (t + Δ') = T' from hω.2])]
      rw [setLIntegral_const, mul_comm]
    simp_rw [hcM]
    -- Apply IH
    simp_rw [ih]
    -- Pull constant stepDist out of integral, swap with tsum
    have hpull : ∀ T' : V → Fin κ,
        (VoterModel.stepDist G (t + Δ') T').toMeasure {S'} *
            ∫⁻ (ω : OpinionTrajectorySpace V κ) in B,
              (VoterModel.opinionProcess G t Δ' (ω t)) T' ∂μ =
          ∫⁻ (ω : OpinionTrajectorySpace V κ) in B,
            (VoterModel.stepDist G (t + Δ') T').toMeasure {S'} *
              (VoterModel.opinionProcess G t Δ' (ω t)) T' ∂μ :=
      fun T' => (lintegral_const_mul _ (hmeas_op Δ' T')).symm
    trans (∑' T' : V → Fin κ,
        ∫⁻ (ω : OpinionTrajectorySpace V κ) in B,
          (VoterModel.stepDist G (t + Δ') T').toMeasure {S'} *
            (VoterModel.opinionProcess G t Δ' (ω t)) T' ∂μ)
    · congr 1; ext T'; exact hpull T'
    · rw [← lintegral_tsum
        (fun T' => ((hmeas_op Δ' T').const_mul _).aemeasurable.restrict)]
      congr 1; ext ω
      apply tsum_congr
      intro T'
      -- (stepDist G (t+Δ') T').toMeasure {S'} = (stepDist G (t+Δ') T') S'
      rw [show (VoterModel.stepDist G (t + Δ') T').toMeasure {S'} =
        (VoterModel.stepDist G (t + Δ') T') S' from by
        rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _)]]
      ring

omit [NeZero κ] in
/-- Multistep marginal Markov property: derived from the multistep filtered
form by taking `B = {ω | ω t = T}`. -/
theorem voterTrajectoryMeasureFrom_markovMarginal
    (G : TemporalGraph V) (μ₀ : Measure (V → Fin κ)) [IsProbabilityMeasure μ₀]
    (t Δ : ℕ) (T S' : V → Fin κ) :
    voterTrajectoryMeasureFrom G μ₀
        ({ω | ω t = T} ∩ {ω | ω (t + Δ) = S'}) =
      voterTrajectoryMeasureFrom G μ₀ {ω | ω t = T} *
        (VoterModel.opinionProcess G t Δ T) S' := by
  classical
  have hB_filt : @MeasurableSet (OpinionTrajectorySpace V κ)
      (⨆ i ∈ Finset.Iic t,
        MeasurableSpace.comap (fun ω : OpinionTrajectorySpace V κ => ω i)
          (inferInstance : MeasurableSpace (V → Fin κ)))
      {ω | ω t = T} := by
    have hsub : MeasurableSpace.comap (fun ω : OpinionTrajectorySpace V κ => ω t)
        (inferInstance : MeasurableSpace (V → Fin κ)) ≤
      (⨆ i ∈ Finset.Iic t,
        MeasurableSpace.comap (fun ω : OpinionTrajectorySpace V κ => ω i)
          (inferInstance : MeasurableSpace (V → Fin κ))) :=
      le_iSup₂_of_le t (Finset.mem_Iic.mpr le_rfl) le_rfl
    apply hsub
    exact ⟨{T}, MeasurableSet.singleton T, by ext; simp⟩
  rw [voterTrajectoryMeasureFrom_multistep_filtration G μ₀ t Δ S' _ hB_filt]
  have hmB : MeasurableSet {ω : OpinionTrajectorySpace V κ | ω t = T} := by
    have : Measurable (fun ω : OpinionTrajectorySpace V κ => ω t) := measurable_pi_apply t
    exact this (by exact MeasurableSet.singleton T : MeasurableSet ({T} : Set (V → Fin κ)))
  rw [setLIntegral_congr_fun hmB
    (g := fun _ => (VoterModel.opinionProcess G t Δ T) S')
    (fun ω hω => by
      show (VoterModel.opinionProcess G t Δ (ω t)) S' =
        (VoterModel.opinionProcess G t Δ T) S'
      rw [show ω t = T from hω])]
  rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    mul_comm]

omit [NeZero κ] in
/-- The initial marginal of `voterTrajectoryMeasureFrom G μ₀` equals `μ₀`. -/
theorem voterTrajectoryMeasureFrom_eval_zero
    (G : TemporalGraph V) (μ₀ : Measure (V → Fin κ)) [IsProbabilityMeasure μ₀] :
    (voterTrajectoryMeasureFrom G μ₀).map
      (fun ω : OpinionTrajectorySpace V κ => ω 0) = μ₀ := by
  classical
  set kern : (n : ℕ) → Kernel (OpinionPrefixType V κ n) (V → Fin κ) :=
    fun n => voterKernel G n
  set μA : Measure (OpinionTrajectorySpace V κ) := voterTrajectoryMeasureFrom G μ₀ with hμA_def
  have hcomp : (fun ω : OpinionTrajectorySpace V κ => ω 0) =
      (fun x : OpinionPrefixType V κ 0 => x ⟨0, by simp⟩) ∘
        Preorder.frestrictLe (π := OpinionStateFamily V κ) 0 := by
    funext ω; rfl
  rw [show μA.map (fun ω : OpinionTrajectorySpace V κ => ω 0) = _ from rfl, hcomp,
      ← Measure.map_map (by fun_prop) (by fun_prop)]
  rw [show μA = Kernel.trajMeasure μ₀ kern from rfl, Kernel.trajMeasure,
      Measure.map_comp _ _ (by fun_prop), Kernel.traj_map_frestrictLe,
      Kernel.partialTraj_self, Measure.id_comp]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  have hid : (fun x : OpinionPrefixType V κ 0 => x ⟨0, by simp⟩) ∘
      (MeasurableEquiv.piUnique
        ((fun i : Finset.Iic 0 ↦ OpinionStateFamily V κ i))).symm = id := by
    funext x; rfl
  rw [hid, Measure.map_id]

omit [NeZero κ] in
/-- Initial marginal: `μA {ω 0 = ξ₀} = μ₀ {ξ₀}`. -/
theorem voterTrajectoryMeasureFrom_marginal_zero
    (G : TemporalGraph V) (μ₀ : Measure (V → Fin κ)) [IsProbabilityMeasure μ₀]
    (ξ₀ : V → Fin κ) :
    voterTrajectoryMeasureFrom G μ₀ {ω | ω 0 = ξ₀} = μ₀ {ξ₀} := by
  have hpre : (fun ω : OpinionTrajectorySpace V κ => ω 0) ⁻¹' {ξ₀} = {ω | ω 0 = ξ₀} := by
    ext ω; simp [Set.mem_preimage, Set.mem_singleton_iff]
  rw [← hpre, ← Measure.map_apply (by fun_prop) (MeasurableSet.singleton ξ₀),
      voterTrajectoryMeasureFrom_eval_zero]

/-- Canonical `κ`-opinion voter model on `G` with deterministic initial state `ξ₀`,
built on the full trajectory space `ℕ → (V → Fin κ)` carrying the Ionescu–Tulcea
trajectory measure. The opinion process is the coordinate evaluation `ξ t ω = ω t`. -/
noncomputable def ofDeterministicAbstract (G : TemporalGraph V) (ξ₀ : V → Fin κ) :
    TemporalGraph.VoterModelAbstract G κ (OpinionTrajectorySpace V κ) where
  μ := ⟨voterTrajectoryMeasureFrom G (Measure.dirac ξ₀), by
    haveI : IsProbabilityMeasure (Measure.dirac ξ₀ : Measure (V → Fin κ)) :=
      Measure.dirac.isProbabilityMeasure
    infer_instance⟩
  ξ := fun t ω => ω t
  hξ_meas := fun t => by
    -- The structure hardcodes the codomain σ-algebra as `⊤`; bridge to the global
    -- `MeasurableSpace (V → Fin κ)` via `inferInstance = ⊤` (finite/discrete space).
    have htop : (inferInstance : MeasurableSpace (V → Fin κ)) = ⊤ :=
      le_antisymm le_top (fun _ _ => MeasurableSet.of_discrete)
    rw [← htop]
    exact (measurable_pi_apply (δ := ℕ) (X := fun _ => V → Fin κ) t).comap_le
  markovProperty := by
    intro t g B hB
    rw [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    haveI : IsProbabilityMeasure (Measure.dirac ξ₀ : Measure (V → Fin κ)) :=
      Measure.dirac.isProbabilityMeasure
    have htop : (inferInstance : MeasurableSpace (V → Fin κ)) = ⊤ :=
      le_antisymm le_top (fun _ _ => MeasurableSet.of_discrete)
    -- Bridge the structure's `⊤`-filtration hypothesis to the global-instance one.
    have hB' : @MeasurableSet (OpinionTrajectorySpace V κ) (⨆ i ∈ Finset.Iic t,
        MeasurableSpace.comap (fun ω : OpinionTrajectorySpace V κ => ω i)
          (inferInstance : MeasurableSpace (V → Fin κ))) B := by
      have hfeq : (⨆ i ∈ Finset.Iic t,
          MeasurableSpace.comap (fun ω : OpinionTrajectorySpace V κ => ω i)
            (inferInstance : MeasurableSpace (V → Fin κ))) =
          (⨆ i ∈ Finset.Iic t,
            MeasurableSpace.comap (fun ω : OpinionTrajectorySpace V κ => ω i)
              (⊤ : MeasurableSpace (V → Fin κ))) := by
        simp only [htop]
      rw [hfeq]; exact hB
    simp only [← stepDist_apply]
    show voterTrajectoryMeasureFrom G (Measure.dirac ξ₀) (B ∩ {ω | ω (t + 1) = g}) =
      ∫⁻ ω in B, (stepDist G t (ω t)) g
        ∂voterTrajectoryMeasureFrom G (Measure.dirac ξ₀)
    rw [voterTrajectoryMeasureFrom_markovProperty G (Measure.dirac ξ₀) t g B hB']
    refine setLIntegral_congr_fun ?_ (fun ω _ => ?_)
    · have hle : (⨆ i ∈ Finset.Iic t,
          MeasurableSpace.comap (fun ω : OpinionTrajectorySpace V κ => ω i)
            (inferInstance : MeasurableSpace (V → Fin κ))) ≤
        (inferInstance : MeasurableSpace (OpinionTrajectorySpace V κ)) := by
        apply iSup₂_le
        intro i _
        exact (measurable_pi_apply i).comap_le
      exact hle _ hB'
    · exact PMF.toMeasure_apply_singleton (stepDist G t (ω t)) g (MeasurableSet.singleton g)

end VoterModel

namespace VoterModel

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]

/-- For the canonical κ=2 voter model `ofDeterministicAbstract G ξ₀` with `Measure.dirac ξ₀`
initial law, the marginal of the opinion-0 set process `A` at any time `Δ` equals the
PMF `opinionProcess₂ G 0 Δ (phiZero ξ₀)`. This bridges the coordinate process
`ξ t ω = ω t` (general `κ`) to the two-opinion set process via `phiZero`. -/
theorem ofDeterministicAbstract_markov_almostSure_init
    (G : TemporalGraph V) (ξ₀ : V → Fin 2) (Δ : ℕ) (S' : Finset V) :
    ((ofDeterministicAbstract G ξ₀).μ : Measure (OpinionTrajectorySpace V 2))
        {ω | (ofDeterministicAbstract G ξ₀).opinionZeroSet Δ ω = S'} =
      VoterModel.opinionProcess₂ G 0 Δ (phiZero ξ₀) S' := by
  classical
  haveI : IsProbabilityMeasure (Measure.dirac ξ₀ : Measure (V → Fin 2)) :=
    Measure.dirac.isProbabilityMeasure
  -- `A Δ ω = phiZero (ω Δ)` since `ξ t ω = ω t` and `A = {v | ξ v = 0} = phiZero`.
  have hA : ∀ ω : OpinionTrajectorySpace V 2,
      (ofDeterministicAbstract G ξ₀).opinionZeroSet Δ ω = phiZero (ω Δ) := fun ω => rfl
  simp only [hA]
  show voterTrajectoryMeasureFrom G (Measure.dirac ξ₀)
      {ω : OpinionTrajectorySpace V 2 | phiZero (ω Δ) = S'}
      = VoterModel.opinionProcess₂ G 0 Δ (phiZero ξ₀) S'
  set μ := voterTrajectoryMeasureFrom G (Measure.dirac ξ₀) with hμ
  haveI : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
  -- The initial coordinate equals `ξ₀` almost surely.
  have hinit : μ {ω : OpinionTrajectorySpace V 2 | ω 0 = ξ₀} = 1 := by
    rw [hμ, voterTrajectoryMeasureFrom_marginal_zero]
    simp
  have hmeas0 : MeasurableSet {ω : OpinionTrajectorySpace V 2 | ω 0 = ξ₀} := by
    have hm : Measurable (fun ω : OpinionTrajectorySpace V 2 => ω 0) := measurable_pi_apply 0
    exact hm (MeasurableSet.singleton ξ₀)
  have hcompl : {ω : OpinionTrajectorySpace V 2 | ω 0 ≠ ξ₀} = {ω | ω 0 = ξ₀}ᶜ := by
    ext ω; simp [Set.mem_compl_iff]
  have hmeas_ne : MeasurableSet {ω : OpinionTrajectorySpace V 2 | ω 0 ≠ ξ₀} := by
    rw [hcompl]; exact hmeas0.compl
  have hzero : μ {ω : OpinionTrajectorySpace V 2 | ω 0 ≠ ξ₀} = 0 := by
    rw [hcompl, measure_compl hmeas0 (measure_ne_top _ _), measure_univ, hinit]
    simp
  -- Per-state marginal: `μ {ω Δ = g} = opinionProcess G 0 Δ ξ₀ g`.
  have hg : ∀ g : V → Fin 2,
      μ {ω : OpinionTrajectorySpace V 2 | ω Δ = g}
        = VoterModel.opinionProcess G 0 Δ ξ₀ g := by
    intro g
    have hmarkov := voterTrajectoryMeasureFrom_markovMarginal G (Measure.dirac ξ₀) 0 Δ ξ₀ g
    rw [show (0 + Δ) = Δ from by ring, ← hμ, hinit, one_mul] at hmarkov
    have hmeasΔ : MeasurableSet {ω : OpinionTrajectorySpace V 2 | ω Δ = g} := by
      have hm : Measurable (fun ω : OpinionTrajectorySpace V 2 => ω Δ) := measurable_pi_apply Δ
      exact hm (MeasurableSet.singleton g)
    have hzero_other :
        μ ({ω : OpinionTrajectorySpace V 2 | ω 0 ≠ ξ₀} ∩ {ω | ω Δ = g}) = 0 :=
      measure_mono_null Set.inter_subset_left hzero
    have hsplit : {ω : OpinionTrajectorySpace V 2 | ω Δ = g} =
        ({ω | ω 0 = ξ₀} ∩ {ω | ω Δ = g}) ∪ ({ω | ω 0 ≠ ξ₀} ∩ {ω | ω Δ = g}) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff, Ne]
      constructor
      · intro h
        by_cases h0 : ω 0 = ξ₀
        · exact Or.inl ⟨h0, h⟩
        · exact Or.inr ⟨h0, h⟩
      · rintro (⟨_, h⟩ | ⟨_, h⟩) <;> exact h
    have hdisj : Disjoint ({ω : OpinionTrajectorySpace V 2 | ω 0 = ξ₀} ∩ {ω | ω Δ = g})
        ({ω | ω 0 ≠ ξ₀} ∩ {ω | ω Δ = g}) := by
      rw [Set.disjoint_left]
      intro ω ⟨h1, _⟩ ⟨h2, _⟩
      exact h2 h1
    rw [hsplit, measure_union hdisj (hmeas_ne.inter hmeasΔ), hzero_other, add_zero]
    exact hmarkov
  -- Decompose `{ω | phiZero (ω Δ) = S'}` over the `phiZero`-fiber of `S'`.
  have hunion : {ω : OpinionTrajectorySpace V 2 | phiZero (ω Δ) = S'} =
      ⋃ g : V → Fin 2,
        (if phiZero g = S' then {ω : OpinionTrajectorySpace V 2 | ω Δ = g} else ∅) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro h
      exact ⟨ω Δ, by simp only [if_pos h, Set.mem_setOf_eq]⟩
    · rintro ⟨g, hg'⟩
      by_cases hpz : phiZero g = S'
      · rw [if_pos hpz] at hg'
        rw [show ω Δ = g from hg']; exact hpz
      · rw [if_neg hpz] at hg'; exact absurd hg' (by simp)
  have hmeas_fiber : ∀ g : V → Fin 2,
      MeasurableSet
        (if phiZero g = S' then {ω : OpinionTrajectorySpace V 2 | ω Δ = g} else ∅) := by
    intro g
    by_cases h : phiZero g = S'
    · rw [if_pos h]
      have hm : Measurable (fun ω : OpinionTrajectorySpace V 2 => ω Δ) := measurable_pi_apply Δ
      exact hm (MeasurableSet.singleton g)
    · rw [if_neg h]; exact MeasurableSet.empty
  have hdisj' : Pairwise (Function.onFun Disjoint
      (fun g : V → Fin 2 =>
        if phiZero g = S' then {ω : OpinionTrajectorySpace V 2 | ω Δ = g} else ∅)) := by
    intro g1 g2 hne
    simp only [Function.onFun]
    by_cases h1 : phiZero g1 = S' <;> by_cases h2 : phiZero g2 = S'
    · rw [if_pos h1, if_pos h2, Set.disjoint_left]
      intro ω ha hb; exact hne (ha ▸ hb)
    · rw [if_neg h2]; simp
    · rw [if_neg h1]; simp
    · rw [if_neg h1]; simp
  rw [hunion, measure_iUnion hdisj' hmeas_fiber,
      ← VoterModel.opinionProcess_map_phiZero, PMF.map_apply]
  apply tsum_congr
  intro g
  by_cases h : phiZero g = S'
  · rw [if_pos h, if_pos h.symm]; exact hg g
  · rw [if_neg h, if_neg (fun he => h he.symm), measure_empty]

end VoterModel
