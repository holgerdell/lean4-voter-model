module

public import VoterProcess.Step

/-! ## Per-opinion coupling of the κ-opinion voter model to two opinions

For any fixed opinion `q : Fin κ`, projecting the κ-opinion configuration `ξ` to
its `q`-set `{v | ξ v = q}` turns the κ-opinion update into the two-opinion
update on that set: a vertex copies a neighbour's opinion, and "is the new
opinion `q`?" depends only on whether the copied/kept vertex was in the `q`-set.
This is the coupling underlying the paper's §3.4 reduction of the multi-opinion
bound to the two-opinion bound (one opinion `q` versus all the rest).

The development mirrors `VoterModelTwoOpinion` (which is the `q = 0`, `κ = 2`
case) but keeps `κ` and `q` general.

## Main results

- `VoterModel.stepDist_map_phiQ` — one-step pushforward to `stepDist₂` on the `q`-set.
- `VoterModel.opinionProcess_map_phiQ` — multi-step pushforward.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Classical

noncomputable section

namespace VoterModel

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V] {κ : ℕ} [NeZero κ]

/-- The `q`-opinion vertex set of a κ-opinion function: `{v | ξ v = q}`. -/
def phiQ (q : Fin κ) (ξ : V → Fin κ) : Finset V := Finset.univ.filter (fun v => ξ v = q)

omit [NeZero κ] in
/-- Per-vertex correspondence: pushing the per-vertex update `nextOpinionDist` along
"is the new opinion `q`?" recovers the two-opinion `nextOpinionDist₂` on the `q`-set. -/
theorem nextOpinionDist_map_phiQ (G : TemporalGraph V) (t : ℕ) (q : Fin κ) (ξ : V → Fin κ) (v : V) :
    (TemporalGraph.VoterModel.nextOpinionDist G t ξ v).map (fun o => decide (o = q))
      = nextOpinionDist₂ G t (phiQ q ξ) v := by
  have hmem : ∀ w : V, decide (w ∈ phiQ q ξ) = decide (ξ w = q) := by intro w; simp [phiQ]
  rw [nextOpinionDist_eq_bind]
  unfold nextOpinionDistBind nextOpinionDist₂
  split_ifs with hN
  · rw [PMF.map_bind]; congr 1; ext b; cases b
    · simp [PMF.map_comp, Function.comp, hmem]
    · simp [PMF.pure_map, hmem]
  · simp [PMF.pure_map, hmem]

/-- Fold-lift auxiliary: along the independent-product fold over a `Nodup` list
`l`, the `q`-set restricted to the processed vertices `l` matches the two-opinion
`Finset`-valued fold. -/
theorem foldK_map_phiQ (G : TemporalGraph V) (t : ℕ) (q : Fin κ) (ξ : V → Fin κ)
    (l : List V) (hnd : l.Nodup) :
    (l.foldr (fun v dist => dist.bind fun f =>
        (TemporalGraph.VoterModel.nextOpinionDist G t ξ v).map fun o => Function.update f v o)
      (PMF.pure (fun _ => 0))).map
      (fun f => l.toFinset.filter (fun u => f u = q)) =
    l.foldr (fun v dist => dist.bind fun T =>
        (nextOpinionDist₂ G t (phiQ q ξ) v).map fun b => cond b (insert v T) T) (PMF.pure ∅) := by
  induction l with
  | nil => simp [PMF.pure_map]
  | cons v tail ih =>
    rw [List.nodup_cons] at hnd
    obtain ⟨hv, hnd'⟩ := hnd
    simp only [List.foldr_cons]
    rw [PMF.map_bind, ← nextOpinionDist_map_phiQ G t q ξ v, ← ih hnd', PMF.bind_map]
    apply congrArg (PMF.bind _)
    funext f
    simp only [Function.comp]
    rw [PMF.map_comp, PMF.map_comp]
    congr 1
    funext o
    simp only [Function.comp, List.toFinset_cons]
    have hvtail : v ∉ tail.toFinset := by simpa using hv
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert]
    by_cases ho : o = q
    · subst ho
      simp only [decide_true, cond_true, Finset.mem_insert, Finset.mem_filter]
      constructor
      · rintro ⟨hx, hxo⟩
        rcases hx with rfl | hx
        · left; rfl
        · right; exact ⟨hx, by rwa [Function.update_of_ne (by rintro rfl; exact hvtail hx)] at hxo⟩
      · rintro (rfl | ⟨hx, hxo⟩)
        · exact ⟨Or.inl rfl, by simp⟩
        · exact ⟨Or.inr hx, by rwa [Function.update_of_ne (by rintro rfl; exact hvtail hx)]⟩
    · simp only [ho, decide_false, cond_false, Finset.mem_filter]
      constructor
      · rintro ⟨hx, hxo⟩
        rcases hx with rfl | hx
        · exact absurd (by simpa using hxo) ho
        · exact ⟨hx, by rwa [Function.update_of_ne (by rintro rfl; exact hvtail hx)] at hxo⟩
      · rintro ⟨hx, hxo⟩
        exact ⟨Or.inr hx, by rwa [Function.update_of_ne (by rintro rfl; exact hvtail hx)]⟩

/-- **One-step pushforward.** Pushing the joint update `stepDist` along the
`q`-set map `phiQ q` recovers the two-opinion step `stepDist₂` on the `q`-set. -/
theorem stepDist_map_phiQ (G : TemporalGraph V) (t : ℕ) (q : Fin κ) (ξ : V → Fin κ) :
    (stepDist G t ξ).map (phiQ q) = stepDist₂ G t (phiQ q ξ) := by
  have h := foldK_map_phiQ G t q ξ Finset.univ.toList (Finset.nodup_toList _)
  rw [stepDist_eq_fold]
  unfold stepDistFold stepDist₂
  rw [← h]
  congr 1
  funext f
  simp [phiQ, Finset.toList_toFinset]

/-- **Multi-step pushforward.** Pushing the multi-step process `opinionProcess`
along `phiQ q` recovers the two-opinion `opinionProcess₂`. -/
theorem opinionProcess_map_phiQ (G : TemporalGraph V) (t₀ : ℕ) (Δ : ℕ) (q : Fin κ)
    (ξ : V → Fin κ) :
    (opinionProcess G t₀ Δ ξ).map (phiQ q) = opinionProcess₂ G t₀ Δ (phiQ q ξ) := by
  induction Δ with
  | zero => simp [opinionProcess, opinionProcess₂, PMF.pure_map]
  | succ Δ ih =>
    rw [opinionProcess, opinionProcess₂, PMF.map_bind]
    simp only [stepDist_map_phiQ]
    rw [← ih, PMF.bind_map]
    rfl

end VoterModel
