module

public import VoterProcess.CrossCut

/-! ## Boundary persistence for the two-opinion voter process

`stepDist₂` fixes `∅` and `Finset.univ`: from either, the next state is a
`PMF.pure` of the same set. `opinionProcess₂` (iterated `stepDist₂`) inherits
this, and composes via Chapman-Kolmogorov (`opinionProcess₂_compose`).

## Main results
- `stepDist₂_empty` — `stepDist₂ G t ∅ = PMF.pure ∅`.
- `stepDist₂_univ` — `stepDist₂ G t Finset.univ = PMF.pure Finset.univ`.
-/

@[expose] public section
open MeasureTheory Finset Filter
open scoped Topology BigOperators

noncomputable section

namespace VoterModel

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]

/-! ## `Finset.univ` persistence -/

private theorem nextOpinionDist₂_univ
    (G : TemporalGraph V) (t : ℕ) (v : V) :
    nextOpinionDist₂ G t Finset.univ v = PMF.pure true := by
  ext b
  cases b
  · by_cases hN : (G.neighborFinset t v).Nonempty
    · rw [nextOpinionDist₂_eq_bind_of_nonempty (G := G) (t := t) (S := Finset.univ) (v := v) hN]
      simp
    · rw [nextOpinionDist₂_eq_pure_of_not_nonempty (G := G) (t := t) (S := Finset.univ) (v := v) hN]
      simp
  · have hsum : nextOpinionDist₂ G t Finset.univ v true + nextOpinionDist₂ G t Finset.univ v false = 1 := by
      simpa using (nextOpinionDist₂ G t Finset.univ v).tsum_coe
    have hfalse : nextOpinionDist₂ G t Finset.univ v false = 0 := by
      by_cases hN : (G.neighborFinset t v).Nonempty
      · rw [nextOpinionDist₂_eq_bind_of_nonempty (G := G) (t := t) (S := Finset.univ) (v := v) hN]
        simp
      · rw [nextOpinionDist₂_eq_pure_of_not_nonempty (G := G) (t := t) (S := Finset.univ) (v := v) hN]
        simp
    rw [hfalse, add_zero] at hsum
    simpa using hsum

theorem stepDist₂_univ
    (G : TemporalGraph V) (t : ℕ) :
    stepDist₂ G t Finset.univ = PMF.pure Finset.univ := by
  unfold stepDist₂
  let F := fun v (dist : PMF (Finset V)) =>
    dist.bind fun T =>
      (nextOpinionDist₂ G t Finset.univ v).map fun isZero => cond isZero (insert v T) T
  have haux : ∀ vs : List V,
      vs.foldr F (PMF.pure ∅) = PMF.pure vs.toFinset := by
    intro vs
    induction vs with
    | nil => simp [F]
    | cons v vs ih =>
        rw [List.foldr_cons, ih]
        dsimp [F]
        rw [nextOpinionDist₂_univ]
        ext s
        simp
  simpa using haux Finset.univ.toList

/-! ## `∅` persistence

Symmetric to `Finset.univ` persistence above (`∅` plays the role of `univ`). -/

private theorem nextOpinionDist₂_empty
    (G : TemporalGraph V) (t : ℕ) (v : V) :
    nextOpinionDist₂ G t ∅ v = PMF.pure false := by
  ext b
  cases b
  · -- b = false: show prob = 1 using tsum complement
    have hsum : nextOpinionDist₂ G t ∅ v true + nextOpinionDist₂ G t ∅ v false = 1 := by
      simpa using (nextOpinionDist₂ G t ∅ v).tsum_coe
    have htrue : nextOpinionDist₂ G t ∅ v true = 0 := by
      by_cases hN : (G.neighborFinset t v).Nonempty
      · rw [nextOpinionDist₂_eq_bind_of_nonempty (G := G) (t := t) (S := ∅) (v := v) hN]
        simp
      · rw [nextOpinionDist₂_eq_pure_of_not_nonempty (G := G) (t := t) (S := ∅) (v := v) hN]
        simp
    rw [htrue, zero_add] at hsum
    simpa using hsum
  · -- b = true: show prob = 0
    by_cases hN : (G.neighborFinset t v).Nonempty
    · rw [nextOpinionDist₂_eq_bind_of_nonempty (G := G) (t := t) (S := ∅) (v := v) hN]
      simp
    · rw [nextOpinionDist₂_eq_pure_of_not_nonempty (G := G) (t := t) (S := ∅) (v := v) hN]
      simp

theorem stepDist₂_empty
    (G : TemporalGraph V) (t : ℕ) :
    stepDist₂ G t ∅ = PMF.pure ∅ := by
  unfold stepDist₂
  let F := fun v (dist : PMF (Finset V)) =>
    dist.bind fun T =>
      (nextOpinionDist₂ G t ∅ v).map fun isZero => cond isZero (insert v T) T
  have haux : ∀ vs : List V,
      vs.foldr F (PMF.pure ∅) = PMF.pure ∅ := by
    intro vs
    induction vs with
    | nil => simp [F]
    | cons v vs ih =>
        rw [List.foldr_cons, ih]
        dsimp [F]
        rw [nextOpinionDist₂_empty]
        ext s
        simp
  simpa using haux Finset.univ.toList

/-! ## Chapman-Kolmogorov -/

-- opinionProcess₂ composes
private theorem opinionProcess₂_compose
    (G : TemporalGraph V) (t n1 n2 : ℕ) (S : Finset V) :
    opinionProcess₂ G t (n1 + n2) S =
      (opinionProcess₂ G t n1 S).bind (fun T => opinionProcess₂ G (t + n1) n2 T) := by
  induction n2 with
  | zero =>
    simp only [add_zero]
    ext T
    simp [opinionProcess₂]
  | succ n2 ih =>
    show opinionProcess₂ G t (n1 + (n2 + 1)) S =
      (opinionProcess₂ G t n1 S).bind fun T => opinionProcess₂ G (t + n1) (n2 + 1) T
    have hlhs : opinionProcess₂ G t (n1 + (n2 + 1)) S =
        (opinionProcess₂ G t (n1 + n2) S).bind (stepDist₂ G (t + (n1 + n2))) := by
      rw [show n1 + (n2 + 1) = (n1 + n2) + 1 from by omega]; rfl
    rw [hlhs, ih, PMF.bind_bind]
    have : t + (n1 + n2) = (t + n1) + n2 := by omega
    simp_rw [this]
    rfl

/-! ## `opinionProcess₂` inherits persistence -/

-- ∅ is absorbing: opinionProcess₂ from ∅ stays at ∅
private theorem opinionProcess₂_empty_eq_pure
    (G : TemporalGraph V) (t : ℕ) (n : ℕ) :
    opinionProcess₂ G t n ∅ = PMF.pure ∅ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show (opinionProcess₂ G t n ∅).bind (stepDist₂ G (t + n)) = PMF.pure ∅
    rw [ih, PMF.pure_bind, stepDist₂_empty]

-- univ is absorbing: opinionProcess₂ from univ stays at univ
private theorem opinionProcess₂_univ_eq_pure
    (G : TemporalGraph V) (t : ℕ) (n : ℕ) :
    opinionProcess₂ G t n Finset.univ = PMF.pure Finset.univ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show (opinionProcess₂ G t n Finset.univ).bind (stepDist₂ G (t + n)) = PMF.pure Finset.univ
    rw [ih, PMF.pure_bind]
    -- Need: stepDist₂ G (t + n) univ = PMF.pure univ (inlined from `stepDist₂_univ`)
    unfold stepDist₂
    let F := fun v (dist : PMF (Finset V)) =>
      dist.bind fun T =>
        (nextOpinionDist₂ G (t + n) Finset.univ v).map fun isZero => cond isZero (insert v T) T
    have haux : ∀ vs : List V,
        vs.foldr F (PMF.pure ∅) = PMF.pure vs.toFinset := by
      intro vs
      induction vs with
      | nil => simp [F]
      | cons v vs ih' =>
          rw [List.foldr_cons, ih']
          dsimp [F]
          have : nextOpinionDist₂ G (t + n) Finset.univ v = PMF.pure true := by
            ext b; cases b
            · by_cases hN : (G.neighborFinset (t + n) v).Nonempty
              · rw [nextOpinionDist₂_eq_bind_of_nonempty (G := G) (t := t + n) (S := Finset.univ) (v := v) hN]; simp
              · rw [nextOpinionDist₂_eq_pure_of_not_nonempty (G := G) (t := t + n) (S := Finset.univ) (v := v) hN]; simp
            · have hsum : nextOpinionDist₂ G (t + n) Finset.univ v true +
                  nextOpinionDist₂ G (t + n) Finset.univ v false = 1 := by
                simpa using (nextOpinionDist₂ G (t + n) Finset.univ v).tsum_coe
              have hfalse : nextOpinionDist₂ G (t + n) Finset.univ v false = 0 := by
                by_cases hN : (G.neighborFinset (t + n) v).Nonempty
                · rw [nextOpinionDist₂_eq_bind_of_nonempty (G := G) (t := t + n) (S := Finset.univ) (v := v) hN]; simp
                · rw [nextOpinionDist₂_eq_pure_of_not_nonempty (G := G) (t := t + n) (S := Finset.univ) (v := v) hN]; simp
              rw [hfalse, add_zero] at hsum
              simpa using hsum
          rw [this]; ext s'; simp
    simpa using haux Finset.univ.toList

end VoterModel
