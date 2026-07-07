module

public import TemporalGraph.Defs
import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.Probability.Distributions.Uniform
import Mathlib.Algebra.Order.Star.Real


@[expose] public section
open MeasureTheory ProbabilityTheory Finset
open scoped Classical

noncomputable section


namespace VoterModel

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Ω : Type*}

/-- Distribution of the next opinion of a single vertex in the voter-model update. -/
def nextOpinionDist₂ [Nonempty V] (G : TemporalGraph V) (t : ℕ) (S : Finset V) (v : V) : PMF Bool :=
  if hN : (G.neighborFinset t v).Nonempty then
    (PMF.uniformOfFintype Bool).bind fun b =>
      cond b (PMF.pure (decide (v ∈ S))) ((PMF.uniformOfFinset (G.neighborFinset t v) hN).map fun w => decide (w ∈ S))
  else PMF.pure (decide (v ∈ S))

theorem nextOpinionDist₂_eq_bind_of_nonempty [Nonempty V]
    (G : TemporalGraph V) (t : ℕ) (S : Finset V) (v : V)
    (hN : (G.neighborFinset t v).Nonempty) :
    nextOpinionDist₂ G t S v =
      (PMF.uniformOfFintype Bool).bind fun b =>
        cond b (PMF.pure (decide (v ∈ S)))
          ((PMF.uniformOfFinset (G.neighborFinset t v) hN).map fun w => decide (w ∈ S)) := by
  simp [nextOpinionDist₂, hN]

@[simp] theorem nextOpinionDist₂_eq_pure_of_not_nonempty [Nonempty V]
    (G : TemporalGraph V) (t : ℕ) (S : Finset V) (v : V)
    (hN : ¬(G.neighborFinset t v).Nonempty) :
    nextOpinionDist₂ G t S v = PMF.pure (decide (v ∈ S)) := by
  simp [nextOpinionDist₂, hN]

/-- \label{stmt:voter-complement-single}

`nextOpinionDist₂ G t (Finset.univ \ S) v = (nextOpinionDist₂ G t S v).map (!)`
-/
theorem nextOpinionDist₂_complement [Nonempty V]
    (G : TemporalGraph V) (t : ℕ) (S : Finset V) (v : V) :
    nextOpinionDist₂ G t (Finset.univ \ S) v = (nextOpinionDist₂ G t S v).map (fun x => !x) := by
  simp only [nextOpinionDist₂]
  split_ifs with hN
  · rw [PMF.map_bind]
    congr 1
    ext b
    cases b
    · simp [PMF.map_comp, Finset.mem_sdiff, Finset.mem_univ]
    · simp [PMF.pure_map, Finset.mem_sdiff, Finset.mem_univ]
  · simp [PMF.pure_map, Finset.mem_sdiff, Finset.mem_univ]

/-- One step of the standard (lazy, synchronous) voter model
    with two opinions on a temporal graph. -/
def stepDist₂ [Nonempty V] (G : TemporalGraph V) (t : ℕ)
    (S : Finset V) : PMF (Finset V) :=
  Finset.univ.toList.foldr
    (fun v dist =>
      dist.bind fun T =>
        (nextOpinionDist₂ G t S v).map fun isZero => cond isZero (insert v T) T)
    (PMF.pure ∅)

private lemma PMF.bind_congr_support {α β : Type*} (p : PMF α) (f g : α → PMF β)
    (h : ∀ a ∈ p.support, f a = g a) : p.bind f = p.bind g := by
  refine PMF.ext fun y => ?_
  simp only [PMF.bind_apply]
  refine tsum_congr fun a => ?_
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · have : p a = 0 := by simpa [PMF.mem_support_iff] using ha
    simp [this]

/-- Combined induction: support invariant and complement identity for the stepDist₂ fold. -/
private lemma stepDist₂_fold_aux [Nonempty V] (G : TemporalGraph V) (t : ℕ) (S : Finset V)
    (l : List V) (hnd : l.Nodup) :
    (∀ T ∈ (l.foldr (fun v dist =>
        dist.bind fun T => (nextOpinionDist₂ G t S v).map fun b => cond b (insert v T) T)
      (PMF.pure ∅)).support, T ⊆ l.toFinset) ∧
    (l.foldr (fun v dist =>
        dist.bind fun T => (nextOpinionDist₂ G t (Finset.univ \ S) v).map fun b =>
          cond b (insert v T) T)
      (PMF.pure ∅) =
    (l.foldr (fun v dist =>
        dist.bind fun T => (nextOpinionDist₂ G t S v).map fun b => cond b (insert v T) T)
      (PMF.pure ∅)).map (fun T => l.toFinset \ T)) := by
  induction l with
  | nil =>
    constructor
    · intro T hT
      simp only [List.foldr_nil, PMF.support_pure, Set.mem_singleton_iff] at hT
      simp [hT]
    · simp only [List.foldr_nil, List.toFinset_nil, PMF.pure_map, Finset.empty_sdiff]
  | cons v tail ih =>
    rw [List.nodup_cons] at hnd
    obtain ⟨hv_not_in_tail, hnd_tail⟩ := hnd
    obtain ⟨ih_supp, ih_comp⟩ := ih hnd_tail
    -- define the fold for S and for complement
    set fold_S : PMF (Finset V) := tail.foldr (fun v dist =>
        dist.bind fun T => (nextOpinionDist₂ G t S v).map fun b => cond b (insert v T) T)
      (PMF.pure ∅) with fold_S_def
    set fold_C : PMF (Finset V) := tail.foldr (fun v dist =>
        dist.bind fun T => (nextOpinionDist₂ G t (Finset.univ \ S) v).map fun b =>
          cond b (insert v T) T)
      (PMF.pure ∅) with fold_C_def
    constructor
    · -- Support invariant: T ⊆ (v :: tail).toFinset
      intro T hT
      simp only [List.foldr_cons, PMF.support_bind, Set.mem_iUnion, PMF.support_map,
        Set.mem_image] at hT
      obtain ⟨T_S, hT_S_supp, b, -, rfl⟩ := hT
      -- T_S ⊆ tail.toFinset by IH
      have hT_S_sub : T_S ⊆ tail.toFinset := ih_supp T_S hT_S_supp
      simp only [List.toFinset_cons]
      cases b with
      | false =>
        simp only [cond_false]
        exact hT_S_sub.trans (Finset.subset_insert v _)
      | true =>
        simp only [cond_true]
        intro x hx
        simp only [Finset.mem_insert]
        rcases Finset.mem_insert.mp hx with rfl | hx
        · left; rfl
        · right; exact hT_S_sub hx
    · -- Complement identity
      simp only [List.foldr_cons, List.toFinset_cons]
      -- refold the tail folds
      rw [← fold_C_def, ← fold_S_def]
      -- rewrite LHS using ih_comp
      rw [ih_comp]
      -- LHS = (fold_S.map (fun T_S => tail.toFinset \ T_S)).bind
      --       (fun T_C => (nextOpinionDist₂ G t (univ\S) v).map fun b => cond b (insert v T_C) T_C)
      -- Rewrite nextOpinionDist₂ for complement using L56
      rw [nextOpinionDist₂_complement]
      -- Apply PMF.bind_map: (p.map f).bind g = p.bind (g ∘ f)
      rw [PMF.bind_map]
      -- Apply PMF.map_bind on RHS: (p.bind f).map g = p.bind (fun x => (f x).map g)
      rw [PMF.map_bind]
      -- Now both sides are fold_S.bind (...), apply congr on support
      apply PMF.bind_congr_support
      intro T_S hT_S_supp
      have hT_S_sub : T_S ⊆ tail.toFinset := ih_supp T_S hT_S_supp
      have hv_not_in_T_S : v ∉ T_S := fun h => hv_not_in_tail (List.mem_toFinset.mp (hT_S_sub h))
      -- Beta-reduce the outer goal: LHS is (fun T => ...) applied to (tail.toFinset \ T_S)
      simp only [Function.comp]
      -- Now LHS = PMF.map (fun b => ...) (PMF.map (!) p), RHS = PMF.map (fun T => ...) (PMF.map (fun b => ...) p)
      -- Use map_comp on both to get a single PMF.map
      rw [PMF.map_comp]
      conv_rhs =>
        rw [PMF.map_comp (fun b => bif b then insert v T_S else T_S)
              (nextOpinionDist₂ G t S v) (fun T => insert v tail.toFinset \ T)]
      -- Now both sides: PMF.map f (nextOpinionDist₂ G t S v); show f = g
      congr 1
      funext b
      have hv_not_in_tailFinset : v ∉ tail.toFinset := by rwa [List.mem_toFinset]
      fin_cases b
      · -- b = true: goal is tail.toFinset \ T_S = insert v tail.toFinset \ insert v T_S
        simp only [Function.comp, Bool.not_true, cond_false, cond_true]
        rw [Finset.insert_sdiff_insert]
        -- Now: tail.toFinset \ T_S = tail.toFinset \ insert v T_S
        -- Since v ∉ tail.toFinset, the extra v in insert v T_S doesn't change the sdiff
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_insert]
        constructor
        · rintro ⟨hx_in, hx_notin_T⟩
          exact ⟨hx_in, fun hx => hx.elim (fun hxv => hv_not_in_tailFinset (hxv ▸ hx_in)) hx_notin_T⟩
        · rintro ⟨hx_in, hx_notin_insT⟩
          exact ⟨hx_in, fun hx => hx_notin_insT (Or.inr hx)⟩
      · -- b = false: LHS = insert v (tail.toFinset \ T_S), RHS = insert v tail.toFinset \ T_S
        simp only [Function.comp, Bool.not_false, cond_true, cond_false]
        exact (Finset.insert_sdiff_of_notMem _ hv_not_in_T_S).symm

/-- \label{stmt:voter-complement-full}

`stepDist₂ G t (Finset.univ \ S) = (stepDist₂ G t S).map (fun T => Finset.univ \ T)`
-/
theorem stepDist₂_complement [Nonempty V] (G : TemporalGraph V) (t : ℕ) (S : Finset V) :
    stepDist₂ G t (Finset.univ \ S) = (stepDist₂ G t S).map (fun T => Finset.univ \ T) := by
  have h := (stepDist₂_fold_aux G t S Finset.univ.toList (Finset.nodup_toList _)).2
  simp only [stepDist₂]
  convert h using 2
  simp [Finset.toList_toFinset]

/-- The opinion-0 set process `(Aₜ : t ≥ 0)`: the distribution of the
opinion-0 set after `t` steps, starting from initial set `a` at time `t₀`.

Matches the paper's `(Aᵢ : i ≥ t₀)` with `A_{t₀} = a`. -/
def opinionProcess₂ [Nonempty V] (G : TemporalGraph V) (t₀ : ℕ) :
    ℕ → Finset V → PMF (Finset V)
  | 0, a => PMF.pure a
  | t + 1, a =>
      ((opinionProcess₂ G t₀ t a) : PMF (Finset V)).bind
        (fun S' : Finset V => stepDist₂ G (t₀ + t) S')

/-- A set is a minority set when `Vol(S) ≤ Vol(V \ S)`. -/
def IsMinority [Nonempty V] (G : TemporalGraph V) (t : ℕ) (S : Finset V) : Prop :=
  TemporalGraph.volume G t S ≤ TemporalGraph.volume G t (Finset.univ \ S)

/-- The minority set: the smaller of `S` and `V \ S` by volume.
Matches the paper's `S_t = argmin{Vol(A_t), Vol(V \ A_t)}`. -/
def minoritySet [Nonempty V] (G : TemporalGraph V) (t : ℕ) (S : Finset V) : Finset V :=
  if TemporalGraph.volume G t S ≤ TemporalGraph.volume G t (Finset.univ \ S)
  then S else Finset.univ \ S


theorem minoritySet_isMinority [Nonempty V] (G : TemporalGraph V) (t : ℕ) (S : Finset V) :
    IsMinority G t (minoritySet G t S) := by
  unfold minoritySet IsMinority
  split_ifs with h
  · exact h
  · push Not at h
    simp [Finset.sdiff_sdiff_eq_self (Finset.subset_univ S)]
    omega

/-! ### Cross-cut neighbor count -/

/-- Number of neighbours of `v` on the other side of the cut `(s, V \ s)`.
For `v ∈ s`: the number of neighbours outside `s`.
For `v ∉ s`: the number of neighbours inside `s`. -/
def lambdaCut [Nonempty V] (G : TemporalGraph V) (t : ℕ) (s : Finset V) (v : V) : ℕ :=
  if v ∈ s then TemporalGraph.degreeIn G t v (Finset.univ \ s)
  else TemporalGraph.degreeIn G t v s

private theorem degreeIn_le_degree [Nonempty V] (G : TemporalGraph V) (t : ℕ) (v : V)
    (N : Finset V) : TemporalGraph.degreeIn G t v N ≤ TemporalGraph.degree G t v := by
  unfold TemporalGraph.degreeIn TemporalGraph.degree SimpleGraph.degreeIn SimpleGraph.degree
  apply Finset.card_le_card
  intro w hw
  simp only [Finset.mem_filter] at hw
  simpa [SimpleGraph.mem_neighborFinset] using hw.2

theorem lambdaCut_le_degree [Nonempty V] (G : TemporalGraph V) (t : ℕ) (s : Finset V) (v : V) :
    lambdaCut G t s v ≤ TemporalGraph.degree G t v := by
  unfold lambdaCut
  split_ifs
  · exact degreeIn_le_degree G t v _
  · exact degreeIn_le_degree G t v _

/-! ### Per-vertex contribution PMFs (Berenbrink et al. ICALP 2016)

`XPMF G t s v` is the original voter per-vertex contribution to `Δ = Vol(A') - Vol(s)`.
`YPMF G t s v` is the replaced per-vertex contribution (replaceRV trick).

Let `d = degree G t v`, `λ = lambdaCut G t s v`:
- `u ∈ s` (minority): both X and Y are `-d` w.p. `λ/(2d)`, else `0`.
- `u ∉ s` (majority), X: `+d` w.p. `λ/(2d)`, else `0`.
- `u ∉ s` (majority), Y: `+λ` w.p. `1/2`, else `0` (the replaceRV replacement). -/

/-- Helper: two-point `PMF ℤ` on `{val, 0}` with `P(val) = p`, `P(0) = 1 - p`. -/
def twoPointPMF (p : NNReal) (hp : p ≤ 1) (val : ℤ) : PMF ℤ :=
  (PMF.ofFintype (fun b : Bool => ((bif b then p else 1 - p : NNReal) : ENNReal))
    (by
      simp only [Fintype.sum_bool, cond_true, cond_false]
      rw [← ENNReal.coe_add, add_tsub_cancel_of_le hp, ENNReal.coe_one])).map
    (fun b => cond b val 0)

/-- Evaluate `∫ z, f (z : ℝ) ∂(twoPointPMF p hp val).toMeasure` directly. -/
theorem integral_twoPointPMF_real (p : NNReal) (hp : p ≤ 1) (val : ℤ) (f : ℝ → ℝ) :
    ∫ z, f (z : ℝ) ∂(twoPointPMF p hp val).toMeasure
      = (p : ℝ) * f (val : ℝ) + (1 - (p : ℝ)) * f 0 := by
  unfold twoPointPMF
  -- Rewrite (PMF.map g q).toMeasure as Measure.map g q.toMeasure
  rw [← PMF.toMeasure_map (fun b : Bool => cond b val (0 : ℤ)) _
      (measurable_of_finite _)]
  -- Apply integral_map: AEMeasurable from Bool (Finite) and AEStronglyMeasurable from ℤ (discrete)
  rw [MeasureTheory.integral_map (measurable_of_finite _).aemeasurable
      (Measurable.aestronglyMeasurable (fun s _ => MeasurableSpace.measurableSet_top))]
  rw [PMF.integral_eq_sum]
  simp only [PMF.ofFintype_apply, Fintype.sum_bool, cond_true, cond_false, smul_eq_mul,
    ENNReal.coe_toReal, NNReal.coe_sub hp, NNReal.coe_one, Int.cast_zero]

/-- `λ / (2d)` as an `NNReal`, where `λ = lambdaCut G t s v` and `d = degree G t v`. -/
def lambdaCutNNP [Nonempty V] (G : TemporalGraph V) (t : ℕ) (s : Finset V)
    (v : V) (hd : TemporalGraph.degree G t v ≠ 0) : NNReal :=
  ⟨(lambdaCut G t s v : ℝ) / (2 * TemporalGraph.degree G t v), by positivity⟩

theorem lambdaCutNNP_le_one [Nonempty V] (G : TemporalGraph V) (t : ℕ)
    (s : Finset V) (v : V) (hd : TemporalGraph.degree G t v ≠ 0) :
    lambdaCutNNP G t s v hd ≤ 1 := by
  unfold lambdaCutNNP
  show (lambdaCut G t s v : ℝ) / (2 * TemporalGraph.degree G t v) ≤ 1
  have hlam : lambdaCut G t s v ≤ TemporalGraph.degree G t v := lambdaCut_le_degree G t s v
  have hd' : (0 : ℝ) < TemporalGraph.degree G t v := by exact_mod_cast Nat.pos_of_ne_zero hd
  have hlam' : (lambdaCut G t s v : ℝ) ≤ TemporalGraph.degree G t v := by exact_mod_cast hlam
  have key : (lambdaCut G t s v : ℝ) / (2 * TemporalGraph.degree G t v) ≤
      TemporalGraph.degree G t v / (2 * TemporalGraph.degree G t v) := by
    apply div_le_div_of_nonneg_right hlam'; linarith
  linarith [show (TemporalGraph.degree G t v : ℝ) / (2 * TemporalGraph.degree G t v) = 1/2 by
    field_simp]

/-- Original per-vertex contribution `X_u` to `Δ = Vol(A') - Vol(s)`
(Berenbrink et al. ICALP 2016, §3).

Let `d = degree G t v`, `λ = lambdaCut G t s v`:
- `v ∈ s` (minority): `-d` w.p. `λ/(2d)`, else `0`.
- `v ∉ s` (majority): `+d` w.p. `λ/(2d)`, else `0`. -/
def XPMF [Nonempty V] (G : TemporalGraph V) (t : ℕ) (s : Finset V) (v : V) : PMF ℤ :=
  if hd : TemporalGraph.degree G t v = 0 then PMF.pure 0
  else if v ∈ s then
    twoPointPMF (lambdaCutNNP G t s v hd) (lambdaCutNNP_le_one G t s v hd)
      (-(TemporalGraph.degree G t v : ℤ))
  else
    twoPointPMF (lambdaCutNNP G t s v hd) (lambdaCutNNP_le_one G t s v hd)
      (TemporalGraph.degree G t v : ℤ)

/-- Replaced per-vertex contribution `Y_u` to `Δ = Vol(A') - Vol(s)`
(Berenbrink et al. ICALP 2016, replaceRV trick, §3).

Let `d = degree G t v`, `λ = lambdaCut G t s v`:
- `v ∈ s` (minority): `-d` w.p. `λ/(2d)`, else `0` (same as `XPMF`).
- `v ∉ s` (majority): `+λ` w.p. `1/2`, else `0` (replaced fair coin). -/
def YPMF [Nonempty V] (G : TemporalGraph V) (t : ℕ) (s : Finset V) (v : V) : PMF ℤ :=
  if hd : TemporalGraph.degree G t v = 0 then PMF.pure 0
  else if v ∈ s then
    twoPointPMF (lambdaCutNNP G t s v hd) (lambdaCutNNP_le_one G t s v hd)
      (-(TemporalGraph.degree G t v : ℤ))
  else
    twoPointPMF (1 / 2) (by norm_num) (lambdaCut G t s v : ℤ)

/-! ### Raw moment lemmas

All moments are real-valued integrals against the `PMF ℤ` viewed as a measure.
We bridge `ℤ` to `ℝ` via `Int.cast_neg` and `Int.cast_natCast`. -/

private theorem lambdaCutNNP_coe_real [Nonempty V] (G : TemporalGraph V) (t : ℕ)
    (s : Finset V) (v : V) (hd : TemporalGraph.degree G t v ≠ 0) :
    (lambdaCutNNP G t s v hd : ℝ) =
      (lambdaCut G t s v : ℝ) / (2 * TemporalGraph.degree G t v) := by
  unfold lambdaCutNNP; rfl

private theorem lambdaCut_eq_zero_of_degree_zero [Nonempty V] (G : TemporalGraph V) (t : ℕ)
    (s : Finset V) (v : V) (hd : TemporalGraph.degree G t v = 0) :
    lambdaCut G t s v = 0 :=
  Nat.le_zero.mp ((lambdaCut_le_degree G t s v).trans (Nat.le_of_eq hd))

/-- Tactic helper: evaluate `∫ z, f (z : ℝ) ∂(twoPointPMF (lambdaCutNNP ...) ... val).toMeasure`. -/
-- Macro for minority-branch moment integral (same for X and Y)
private theorem minority_moment [Nonempty V] (G : TemporalGraph V) (t : ℕ)
    (s : Finset V) (v : V) (hd : TemporalGraph.degree G t v ≠ 0) (f : ℝ → ℝ) :
    ∫ z, f (z : ℝ) ∂(twoPointPMF (lambdaCutNNP G t s v hd)
        (lambdaCutNNP_le_one G t s v hd) (-(TemporalGraph.degree G t v : ℤ))).toMeasure =
      (lambdaCut G t s v : ℝ) / (2 * TemporalGraph.degree G t v) * f (-(TemporalGraph.degree G t v : ℝ)) +
      (1 - (lambdaCut G t s v : ℝ) / (2 * TemporalGraph.degree G t v)) * f 0 := by
  rw [integral_twoPointPMF_real, lambdaCutNNP_coe_real]
  simp only [Int.cast_neg, Int.cast_natCast]

private theorem majority_moment_Y [Nonempty V] (G : TemporalGraph V) (t : ℕ)
    (s : Finset V) (v : V) (f : ℝ → ℝ) :
    ∫ z, f (z : ℝ) ∂(twoPointPMF (1 / 2) (by norm_num : (1/2 : NNReal) ≤ 1)
        (lambdaCut G t s v : ℤ)).toMeasure =
      (1/2 : ℝ) * f (lambdaCut G t s v : ℝ) + (1 - (1/2 : ℝ)) * f 0 := by
  rw [integral_twoPointPMF_real]
  simp only [Int.cast_natCast, NNReal.coe_div, NNReal.coe_ofNat, NNReal.coe_one]

/-- Mean of `YPMF`:
- `v ∈ s` (minority): `E[Y_v] = -λ/2`.
- `v ∉ s` (majority): `E[Y_v] = λ/2`. -/
theorem integral_YPMF_id [Nonempty V] (G : TemporalGraph V) (t : ℕ) (s : Finset V) (v : V) :
    ∫ z, (z : ℝ) ∂(YPMF G t s v).toMeasure =
      if v ∈ s then -(lambdaCut G t s v : ℝ) / 2
      else (lambdaCut G t s v : ℝ) / 2 := by
  simp only [YPMF]
  by_cases hd : TemporalGraph.degree G t v = 0
  · simp only [dif_pos hd, PMF.toMeasure_pure, lambdaCut_eq_zero_of_degree_zero G t s v hd]
    simp
  · simp only [dif_neg hd]
    have hd' : (TemporalGraph.degree G t v : ℝ) ≠ 0 := by exact_mod_cast hd
    by_cases hv : v ∈ s
    · simp only [if_pos hv]
      have h := minority_moment G t s v hd id; simp only [id] at h; rw [h]
      field_simp; ring
    · -- majority side: fair coin on {λ, 0}
      simp only [if_neg hv]
      have h := majority_moment_Y G t s v id; simp only [id] at h; rw [h]; ring

/-- Second moment of `YPMF`:
- `v ∈ s` (minority): `E[Y_v²] = d · λ / 2`.
- `v ∉ s` (majority): `E[Y_v²] = λ² / 2`. -/
theorem integral_YPMF_sq [Nonempty V] (G : TemporalGraph V) (t : ℕ) (s : Finset V) (v : V) :
    ∫ z, (z : ℝ) ^ 2 ∂(YPMF G t s v).toMeasure =
      if v ∈ s then (TemporalGraph.degree G t v : ℝ) * (lambdaCut G t s v : ℝ) / 2
      else (lambdaCut G t s v : ℝ) ^ 2 / 2 := by
  simp only [YPMF]
  by_cases hd : TemporalGraph.degree G t v = 0
  · simp only [dif_pos hd, PMF.toMeasure_pure, lambdaCut_eq_zero_of_degree_zero G t s v hd]
    simp
  · simp only [dif_neg hd]
    have hd' : (TemporalGraph.degree G t v : ℝ) ≠ 0 := by exact_mod_cast hd
    by_cases hv : v ∈ s
    · simp only [if_pos hv]
      have h := minority_moment G t s v hd (fun x => x^2); rw [h]
      field_simp; ring
    · simp only [if_neg hv]
      have h := majority_moment_Y G t s v (fun x => x^2); rw [h]; ring

/-- Third moment of `YPMF`:
- `v ∈ s` (minority): `E[Y_v³] = -d² · λ / 2`.
- `v ∉ s` (majority): `E[Y_v³] = λ³ / 2`. -/
theorem integral_YPMF_cube [Nonempty V] (G : TemporalGraph V) (t : ℕ) (s : Finset V) (v : V) :
    ∫ z, (z : ℝ) ^ 3 ∂(YPMF G t s v).toMeasure =
      if v ∈ s then -(TemporalGraph.degree G t v : ℝ) ^ 2 * (lambdaCut G t s v : ℝ) / 2
      else (lambdaCut G t s v : ℝ) ^ 3 / 2 := by
  simp only [YPMF]
  by_cases hd : TemporalGraph.degree G t v = 0
  · simp only [dif_pos hd, PMF.toMeasure_pure, lambdaCut_eq_zero_of_degree_zero G t s v hd]
    simp
  · simp only [dif_neg hd]
    have hd' : (TemporalGraph.degree G t v : ℝ) ≠ 0 := by exact_mod_cast hd
    by_cases hv : v ∈ s
    · simp only [if_pos hv]
      have h := minority_moment G t s v hd (fun x => x^3); rw [h]
      field_simp; ring
    · simp only [if_neg hv]
      have h := majority_moment_Y G t s v (fun x => x^3); rw [h]; ring


end VoterModel
