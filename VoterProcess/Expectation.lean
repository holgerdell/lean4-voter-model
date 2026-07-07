module

public import VoterProcess.CrossCut
import Mathlib.Probability.ProbabilityMassFunction.Integrals


@[expose] public section
open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators

noncomputable section

namespace VoterModel

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]

instance finsetMeasurableSpace : MeasurableSpace (Finset V) := ⊤

theorem pmf_integral_bind
    {α β : Type*} [Fintype α] [Fintype β]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (p : PMF α) (f : α → PMF β) (g : β → ℝ) :
    ∫ y, g y ∂((p.bind f).toMeasure)
      = ∫ x, (∫ y, g y ∂((f x).toMeasure)) ∂(p.toMeasure) := by
  rw [PMF.integral_eq_sum, PMF.integral_eq_sum]
  simp_rw [PMF.integral_eq_sum, PMF.bind_apply, tsum_fintype, smul_eq_mul]
  calc
    ∑ b, (∑ a, p a * (f a) b).toReal * g b
      = ∑ b, ∑ a, (p a * (f a) b).toReal * g b := by
          refine Finset.sum_congr rfl (fun b _ => ?_)
          rw [ENNReal.toReal_sum]
          · rw [Finset.sum_mul]
          · intro a _
            exact ENNReal.mul_ne_top (ne_of_lt (PMF.apply_lt_top p a))
              (ne_of_lt (PMF.apply_lt_top (f a) b))
    _ = ∑ b, ∑ a, ((p a).toReal * ((f a) b).toReal) * g b := by
          simp_rw [ENNReal.toReal_mul]
    _ = ∑ a, ∑ b, ((p a).toReal * ((f a) b).toReal) * g b := by
          rw [Finset.sum_comm]
    _ = ∑ a, (p a).toReal * ∑ b, ((f a) b).toReal * g b := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun b _ => ?_)
          ring

theorem nextOpinion_weighted_expectation
    (G : TemporalGraph V) (t : ℕ) (S : Finset V) (v : V) :
    ∫ b, cond b ((TemporalGraph.degree G t v : ℝ)) 0 ∂((nextOpinionDist₂ G t S v).toMeasure)
      = ((((if v ∈ S then TemporalGraph.degree G t v else 0) +
          TemporalGraph.degreeIn G t v S : ℕ) : ℝ) / 2) := by
  by_cases hN : (G.neighborFinset t v).Nonempty  -- neighborFinset is abbrev, use directly
  · rw [nextOpinionDist₂_eq_bind_of_nonempty (G := G) (t := t) (S := S) (v := v) hN]
    rw [pmf_integral_bind]
    rw [PMF.integral_eq_sum]
    have hpure_true :
        ∫ b, cond b ((TemporalGraph.degree G t v : ℝ)) 0 ∂((PMF.pure true).toMeasure)
        = TemporalGraph.degree G t v := by simp [PMF.toMeasure_pure]
    have hpure_false :
        ∫ b, cond b ((TemporalGraph.degree G t v : ℝ)) 0 ∂((PMF.pure false).toMeasure)
        = 0 := by simp [PMF.toMeasure_pure]
    have hcopy :
        ∫ b, cond b ((TemporalGraph.degree G t v : ℝ)) 0
            ∂(((PMF.uniformOfFinset (G.neighborFinset t v) hN).map fun w => decide (w ∈ S)).toMeasure)
          = (TemporalGraph.degreeIn G t v S : ℝ) := by
      rw [PMF.integral_eq_sum]
      have hset : ({w ∈ S | (G.snapshot t).Adj v w} : Finset V) = (S ∩ G.neighborFinset t v) := by
        simp only [TemporalGraph.neighborFinset, SimpleGraph.neighborFinset]
        ext w
        simp
      have hne0 : ((G.neighborFinset t v).card : ℝ) ≠ 0 := by
        exact_mod_cast hN.card_ne_zero
      simp [PMF.map_apply, PMF.uniformOfFinset_apply, TemporalGraph.degree,
        TemporalGraph.degreeIn, smul_eq_mul]
      simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
        SimpleGraph.degreeIn, SimpleGraph.degree]
      rw [nsmul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_inv,
        ENNReal.toReal_natCast]
      have hnn : (0 : ℝ) < #((G.snapshot t).neighborFinset v) := by
        have : G.neighborFinset t v = (G.snapshot t).neighborFinset v := by
          simp [TemporalGraph.neighborFinset, SimpleGraph.neighborFinset]
        rw [← this]; exact_mod_cast hN.card_pos
      field_simp [ne_of_gt hnn]
    by_cases hvS : v ∈ S <;> simp [hvS, hpure_true, hpure_false, hcopy, PMF.uniformOfFintype_apply] <;> ring_nf
  · rw [nextOpinionDist₂_eq_pure_of_not_nonempty (G := G) (t := t) (S := S) (v := v) hN]
    rw [PMF.toMeasure_pure]
    have hdeg : TemporalGraph.degree G t v = 0 :=
      Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hN)
    have hedges : TemporalGraph.degreeIn G t v S = 0 := by
      simp only [TemporalGraph.degreeIn, SimpleGraph.degreeIn]
      simp [fun x => show ¬(G.snapshot t).Adj v x from
        fun hx => hN ⟨x, by simp [TemporalGraph.neighborFinset, hx]⟩]
    by_cases hvS : v ∈ S <;> simp [hvS, hdeg, hedges]

def stepDist₂Aux (G : TemporalGraph V) (t : ℕ) (S : Finset V) : List V → PMF (Finset V)
  | [] => PMF.pure ∅
  | v :: vs =>
      (stepDist₂Aux G t S vs).bind fun T =>
        (nextOpinionDist₂ G t S v).map fun isZero : Bool => bif isZero then insert v T else T

theorem stepDist₂Aux_eq_stepDist₂ (G : TemporalGraph V) (t : ℕ) (S : Finset V) :
    stepDist₂Aux G t S Finset.univ.toList = stepDist₂ G t S := by
  show stepDist₂Aux G t S Finset.univ.toList = _
  suffices ∀ (vs : List V), stepDist₂Aux G t S vs = vs.foldr
      (fun v dist => dist.bind fun T =>
        (nextOpinionDist₂ G t S v).map fun isZero : Bool => bif isZero then insert v T else T)
      (PMF.pure ∅) by exact this Finset.univ.toList
  intro vs; induction vs with
  | nil => rfl
  | cons v vs ih => simp [stepDist₂Aux, ih]

theorem stepDist₂Aux_support_subset
    (G : TemporalGraph V) (t : ℕ) (S : Finset V) (vs : List V) :
    ∀ T, T ∈ (stepDist₂Aux G t S vs).support → T ⊆ vs.toFinset := by
  intro T hT
  induction vs generalizing T with
  | nil =>
      simpa [stepDist₂Aux] using hT
  | cons v vs ih =>
      rcases (PMF.mem_support_bind_iff
        (p := stepDist₂Aux G t S vs)
        (f := fun U : Finset V =>
          (nextOpinionDist₂ G t S v).map fun isZero : Bool => bif isZero then insert v U else U)
        (b := T)).1 hT with ⟨U, hU, hmapU⟩
      rcases (PMF.mem_support_map_iff
        (p := nextOpinionDist₂ G t S v)
        (f := fun isZero : Bool => bif isZero then insert v U else U)
        (b := T)).1 hmapU with ⟨b, _, hT'⟩
      subst hT'
      by_cases hbool : b
      · simp [hbool, List.toFinset_cons, Finset.insert_subset_insert, ih U hU]
      · simp [Bool.eq_false_iff.mpr hbool, List.toFinset_cons]
        exact Subset.trans (ih U hU) (Finset.subset_insert v vs.toFinset)

theorem map_indicator_integral
    (G : TemporalGraph V) (t : ℕ) (S : Finset V) (u v : V) (c : ℝ) (a : Finset V) :
    ∫ y, (if u ∈ y then c else 0)
        ∂((PMF.map (fun isZero : Bool => bif isZero then insert v a else a)
          (nextOpinionDist₂ G t S v)).toMeasure)
      =
    ∫ b, (if u ∈ (if b then insert v a else a) then c else 0)
        ∂((nextOpinionDist₂ G t S v).toMeasure) := by
  have : PMF.map (fun isZero : Bool => bif isZero then insert v a else a) (nextOpinionDist₂ G t S v)
      = (nextOpinionDist₂ G t S v).bind (fun b => PMF.pure (bif b then insert v a else a)) := by
    ext y
    simp [PMF.map_apply, PMF.bind_apply, PMF.pure_apply]
    convert rfl
  rw [this, pmf_integral_bind]
  simp [PMF.toMeasure_pure, Bool.cond_eq_ite]

theorem indicator_expectation_gen
    (G : TemporalGraph V) (t : ℕ) (S : Finset V) (u : V) (c : ℝ) :
    ∀ vs, vs.Nodup →
      ∫ T, (if u ∈ T then c else 0)
        ∂((stepDist₂Aux G t S vs).toMeasure)
        = if u ∈ vs.toFinset then
            ∫ b, (bif b then c else 0)
              ∂((nextOpinionDist₂ G t S u).toMeasure)
          else 0 := by
  intro vs
  induction vs with
  | nil =>
      intro _
      rw [stepDist₂Aux, PMF.toMeasure_pure]
      simp
  | cons v vs ih =>
      intro hnodup
      rw [stepDist₂Aux, pmf_integral_bind]
      by_cases huv : u = v
      · subst huv
        have hunot : u ∉ vs.toFinset := by
          simpa using (List.nodup_cons.mp hnodup).1
        have hs0 :
            ∑ a, ((stepDist₂Aux G t S vs) a).toReal •
                ∫ y, (if u ∈ y then c else 0)
                    ∂((PMF.map (fun isZero : Bool => bif isZero then insert u a else a)
                      (nextOpinionDist₂ G t S u)).toMeasure)
              =
            ∑ a, ((stepDist₂Aux G t S vs) a).toReal *
                ∫ b, (if u ∈ (if b then insert u a else a) then c else 0)
                    ∂((nextOpinionDist₂ G t S u).toMeasure) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [smul_eq_mul,
            map_indicator_integral (G := G) (t := t) (S := S) (u := u) (v := u) (c := c) (a := a)]
        have hmain : ∀ T : Finset V,
            T ∈ (stepDist₂Aux G t S vs).support →
            ∫ b, (if u ∈ (if b then insert u T else T) then c else 0)
              ∂((nextOpinionDist₂ G t S u).toMeasure)
            = ∫ b, (bif b then c else 0)
              ∂((nextOpinionDist₂ G t S u).toMeasure) := by
          intro T hT
          have huT : u ∉ T := by
            intro huT
            exact hunot ((stepDist₂Aux_support_subset G t S vs T hT) huT)
          apply integral_congr_ae
          filter_upwards [] with b
          by_cases hb : b
          · simp [hb]
          · simp [hb, huT]
        rw [PMF.integral_eq_sum]
        have hmass : (∑ T, ((stepDist₂Aux G t S vs) T).toReal) = 1 := by
          simpa [smul_eq_mul] using
            (PMF.integral_eq_sum (stepDist₂Aux G t S vs) (fun _ => (1 : ℝ))).symm
        have hconst : ∀ T : Finset V,
            ((stepDist₂Aux G t S vs) T).toReal *
                ∫ b, (if u ∈ (if b then insert u T else T) then c else 0)
                    ∂((nextOpinionDist₂ G t S u).toMeasure)
              =
            ((stepDist₂Aux G t S vs) T).toReal *
                ∫ b, (bif b then c else 0)
                  ∂((nextOpinionDist₂ G t S u).toMeasure) := by
          intro T
          by_cases hT : T ∈ (stepDist₂Aux G t S vs).support
          · rw [hmain T hT]
          · have : (stepDist₂Aux G t S vs) T = 0 := by
              rwa [PMF.mem_support_iff, not_not] at hT
            simp [this]
        rw [hs0, show ∑ T, _ = ∑ T, ((stepDist₂Aux G t S vs) T).toReal *
            ∫ b, (bif b then c else 0)
              ∂((nextOpinionDist₂ G t S u).toMeasure) from
          Finset.sum_congr rfl (fun T _ => hconst T)]
        rw [← Finset.sum_mul, hmass, one_mul]
        simp [hunot]
      · have hkeep : ∀ T : Finset V,
            ∫ b, (if u ∈ (if b then insert v T else T) then c else 0)
                ∂((nextOpinionDist₂ G t S v).toMeasure)
              = if u ∈ T then c else 0 := by
          intro T
          rw [PMF.integral_eq_sum]
          have hmassv : ((nextOpinionDist₂ G t S v) true).toReal
              + ((nextOpinionDist₂ G t S v) false).toReal = 1 := by
            have := congrArg ENNReal.toReal (nextOpinionDist₂ G t S v).tsum_coe
            simp [tsum_fintype, ENNReal.toReal_add
              (ne_of_lt (PMF.apply_lt_top _ true)) (ne_of_lt (PMF.apply_lt_top _ false))] at this
            linarith
          by_cases huT : u ∈ T
          · simp [huT, huv, smul_eq_mul]
            have : ((nextOpinionDist₂ G t S v) true).toReal * c +
                ((nextOpinionDist₂ G t S v) false).toReal * c = c := by
              rw [← add_mul, hmassv, one_mul]
            linarith
          · simp [huT, huv, smul_eq_mul]
        rw [PMF.integral_eq_sum]
        simp_rw [smul_eq_mul,
          show ∀ a, ∫ y, (if u ∈ y then c else 0)
              ∂((PMF.map (fun isZero : Bool => bif isZero then insert v a else a)
                (nextOpinionDist₂ G t S v)).toMeasure)
            = if u ∈ a then c else 0 from
            fun a => by rw [map_indicator_integral, hkeep],
          ← smul_eq_mul, ← PMF.integral_eq_sum]
        rw [ih (List.nodup_cons.mp hnodup).2]
        simp [huv]


end VoterModel
