module

public import SimpleGraph.Conductance
public import TemporalGraph.Defs


/-! ## Conductance definitions for temporal graphs

Core conductance primitives (`relativeVolume`,
`setConductanceOnInterval`, `admissibleCuts`) together with the
window-guarantee temporal conductance parameter `φ̃(𝒢)`.

## Main results

- `relativeVolume` — `π(S) = Vol(S) / Vol(V)`.
- `(G.snapshot t).setConductance S` — `φ^t(S)` (see `VoterModel.SimpleGraph.Conductance`).
- `setConductanceOnInterval` — `φ^[t₁,t₂](S)`.
- `admissibleCuts` — the set of admissible cuts.
- `hasWindowGuarantee` — the window-guarantee predicate.
- `temporalConductance` — `φ̃(𝒢)`.
- `temporalConductance_nonneg`, `temporalConductance_le_one` — basic bounds.
- `Φ` — `ℝ≥0∞`-valued bridge for `ENNReal`-valued statements, matching the paper's `Φ(G)`.
-/

@[expose] public section

open Finset
open scoped BigOperators ENNReal

noncomputable section

namespace TemporalGraph

/-- \label{eq:set-conductance-on-interval}

`φ^[t₁,t₂](S) = ∑_{t=t₁}^{t₂} φ^t(S)`.
-/
def setConductanceOnInterval {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraph V) (t₁ t₂ : ℕ) (S : Finset V) : ℝ :=
  Finset.sum (Finset.Icc t₁ t₂) (fun t => (G.snapshot t).setConductance S)

theorem setConductanceOnInterval_nonneg {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraph V) (t₁ t₂ : ℕ) (S : Finset V) :
    0 ≤ setConductanceOnInterval G t₁ t₂ S := by
  unfold setConductanceOnInterval
  exact Finset.sum_nonneg (fun t _ => (G.snapshot t).setConductance_nonneg S)

theorem setConductanceOnInterval_consecutive {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraph V) (t Δ₁ Δ₂ : ℕ) (S : Finset V) :
    setConductanceOnInterval G t (t + Δ₁ + Δ₂ + 1) S =
      setConductanceOnInterval G t (t + Δ₁) S +
        setConductanceOnInterval G (t + Δ₁ + 1) (t + Δ₁ + 1 + Δ₂) S := by
  unfold setConductanceOnInterval
  rw [← Finset.Ico_add_one_right_eq_Icc t (t + Δ₁ + Δ₂ + 1),
    ← Finset.Ico_add_one_right_eq_Icc t (t + Δ₁),
    ← Finset.Ico_add_one_right_eq_Icc (t + Δ₁ + 1) (t + Δ₁ + 1 + Δ₂)]
  simpa [add_assoc, add_left_comm, add_comm] using
    (Finset.sum_Ico_consecutive
      (f := fun u => (G.snapshot u).setConductance S)
      (m := t) (n := t + Δ₁ + 1) (k := t + Δ₁ + Δ₂ + 2)
      (by omega) (by omega)).symm

/-- \label{eq:conductance-on-interval}
\label{eq:maximum-set-conductance-on-interval}

Largest conductance of `S` over the length-`Δ` window `[t, t+Δ-1]`. -/
def maxSetConductanceOnInterval {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraph V) (t Δ : ℕ) (S : Finset V) : ℝ :=
  ⨆ s ∈ Finset.Icc t (t + (Δ - 1)), (G.snapshot s).setConductance S

/-- Any per-step conductance in the window lower-bounds the window's maximum. -/
theorem le_maxSetConductanceOnInterval {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraph V) (t Δ : ℕ) (S : Finset V) {s : ℕ}
    (hs : s ∈ Finset.Icc t (t + (Δ - 1))) :
    (G.snapshot s).setConductance S ≤ maxSetConductanceOnInterval G t Δ S := by
  have hbdd : BddAbove (Set.range fun u =>
      ⨆ (_ : u ∈ Finset.Icc t (t + (Δ - 1))), (G.snapshot u).setConductance S) := by
    refine ⟨1, ?_⟩
    rintro x ⟨u, rfl⟩
    simp only []
    by_cases hu : u ∈ Finset.Icc t (t + (Δ - 1))
    · rw [ciSup_pos hu]; exact (G.snapshot u).setConductance_le_one S
    · rw [ciSup_neg hu, Real.sSup_empty]; norm_num
  have h := le_ciSup hbdd s
  rwa [ciSup_pos hs] at h

/-- A common upper bound `c ≥ 0` on every per-step conductance in the window
upper-bounds the window's maximum (`0 ≤ c` covers the degenerate `Δ = 0` case). -/
theorem maxSetConductanceOnInterval_le {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraph V) (t Δ : ℕ) (S : Finset V) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ s ∈ Finset.Icc t (t + (Δ - 1)), (G.snapshot s).setConductance S ≤ c) :
    maxSetConductanceOnInterval G t Δ S ≤ c := by
  apply ciSup_le
  intro s
  by_cases hs : s ∈ Finset.Icc t (t + (Δ - 1))
  · rw [ciSup_pos hs]; exact h s hs
  · rw [ciSup_neg hs, Real.sSup_empty]; exact hc

/-- The window's maximum is attained at some step. -/
theorem exists_mem_eq_maxSetConductanceOnInterval {V : Type*} [Fintype V] [Nonempty V]
    [DecidableEq V] (G : TemporalGraph V) (t Δ : ℕ) (S : Finset V) :
    ∃ s ∈ Finset.Icc t (t + (Δ - 1)),
      maxSetConductanceOnInterval G t Δ S = (G.snapshot s).setConductance S := by
  have hne : (Finset.Icc t (t + (Δ - 1))).Nonempty := Finset.nonempty_Icc.mpr (by omega)
  obtain ⟨s, hs, heq⟩ := Finset.exists_mem_eq_sup' hne
      (fun u => (G.snapshot u).setConductance S)
  refine ⟨s, hs, le_antisymm ?_ (le_maxSetConductanceOnInterval G t Δ S hs)⟩
  apply maxSetConductanceOnInterval_le G t Δ S ((G.snapshot s).setConductance_nonneg S)
  intro u hu
  rw [← heq]
  exact Finset.le_sup' (fun v => (G.snapshot v).setConductance S) hu

theorem maxSetConductanceOnInterval_nonneg {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraph V) (t Δ : ℕ) (S : Finset V) :
    0 ≤ maxSetConductanceOnInterval G t Δ S :=
  Real.iSup_nonneg fun s => Real.iSup_nonneg fun _ => (G.snapshot s).setConductance_nonneg S

/-- Sets S that satisfy 0 < Vol(S) ≤ m. -/
abbrev admissibleCuts {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraph V) : Set (Finset V) :=
  (G.snapshot 0).admissibleCuts

/-- Membership in `admissibleCuts` re-expressed with `relativeVolume`. Requires positive degrees
(so `Vol(V) > 0`); bridges the volume-based definition to proofs phrased with `π(S)`. -/
theorem mem_admissibleCuts_iff_relativeVolume {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraph V)
    (hdeg : ∀ v : V, 0 < degree G 0 v) (S : Finset V) :
    S ∈ admissibleCuts G ↔
      S.Nonempty ∧ S ≠ Finset.univ ∧
        0 < relativeVolume G S ∧ relativeVolume G S ≤ 1 / 2 := by
  have hUpos : 0 < volume G 0 Finset.univ := by
    obtain ⟨v⟩ := ‹Nonempty V›
    exact Nat.lt_of_lt_of_le (hdeg v)
      (Finset.single_le_sum (f := fun u => degree G 0 u)
        (fun u _ => Nat.zero_le _) (Finset.mem_univ v))
  have hUposQ : (0 : ℚ) < (volume G 0 Finset.univ : ℚ) := by exact_mod_cast hUpos
  have hrel : relativeVolume G S = (volume G 0 S : ℚ) / (volume G 0 Finset.univ : ℚ) := rfl
  unfold admissibleCuts SimpleGraph.admissibleCuts
  simp only [Set.mem_setOf_eq, hrel]
  constructor
  · rintro ⟨hpos, hle⟩
    have hne : S.Nonempty := by
      rcases S.eq_empty_or_nonempty with rfl | hne
      · simp [SimpleGraph.volume] at hpos
      · exact hne
    have hpr : S ≠ Finset.univ := by rintro rfl; omega
    refine ⟨hne, hpr, div_pos (by exact_mod_cast hpos) hUposQ, ?_⟩
    rw [div_le_iff₀ hUposQ]
    have h2 : (2 * volume G 0 S : ℚ) ≤ (volume G 0 Finset.univ : ℚ) := by exact_mod_cast hle
    linarith
  · rintro ⟨hne, _hpr, hpos, hle⟩
    refine ⟨?_, ?_⟩
    · obtain ⟨v, hv⟩ := hne
      exact Nat.lt_of_lt_of_le (hdeg v)
        (Finset.single_le_sum (f := fun u => degree G 0 u)
          (fun u _ => Nat.zero_le _) hv)
    · rw [div_le_iff₀ hUposQ] at hle
      have h2 : (2 * volume G 0 S : ℚ) ≤ (volume G 0 Finset.univ : ℚ) := by linarith
      exact_mod_cast h2

/-- \label{eq:delta-window-conductance}

`Δ`-window conductance `φ^Δ(G) = min_t min_{S admissible} φ^{[t, t+Δ-1]}(S)`. -/
def windowConductance {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraph V) (Δ : ℕ) : ℝ :=
  if Δ = 0 then 0  -- degenerate case: empty interval
  else sInf {sInf {maxSetConductanceOnInterval G t Δ S | S ∈ admissibleCuts G} | t : ℕ}

theorem windowConductance_nonneg {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraph V) (Δ : ℕ) :
    0 ≤ windowConductance G Δ := by
  unfold windowConductance
  split_ifs with hΔ
  · norm_num
  · apply Real.sInf_nonneg
    intro x ⟨t, hx⟩
    rw [← hx]
    apply Real.sInf_nonneg
    intro y ⟨S, _hS, heq⟩
    rw [← heq]
    exact maxSetConductanceOnInterval_nonneg G t Δ S

theorem maxSetConductanceOnInterval_le_one {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraph V) (t Δ : ℕ) (S : Finset V) :
    maxSetConductanceOnInterval G t Δ S ≤ 1 :=
  maxSetConductanceOnInterval_le G t Δ S (by norm_num)
    (fun s _ => (G.snapshot s).setConductance_le_one S)

theorem windowConductance_le_one {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraph V) (Δ : ℕ) :
    windowConductance G Δ ≤ 1 := by
  classical
  unfold windowConductance
  split_ifs with hΔ
  · norm_num
  · let minByTime : ℕ → ℝ := fun t =>
      sInf ((fun S => maxSetConductanceOnInterval G t Δ S) '' admissibleCuts G)
    have hle1 : minByTime 0 ≤ 1 := by
      by_cases hs : (admissibleCuts G).Nonempty
      · obtain ⟨S, hS⟩ := hs
        dsimp [minByTime]
        refine le_trans (csInf_le ?_ ⟨S, hS, rfl⟩) ?_
        · refine ⟨0, ?_⟩
          rintro y ⟨S', hS', rfl⟩
          exact maxSetConductanceOnInterval_nonneg G 0 Δ S'
        · simpa using maxSetConductanceOnInterval_le_one G 0 Δ S
      · have hempty : admissibleCuts G = ∅ := Set.not_nonempty_iff_eq_empty.mp hs
        simp [minByTime, hempty]
    calc
      sInf (Set.range minByTime) ≤ minByTime 0 := by
        refine csInf_le ?_ ⟨0, rfl⟩
        refine ⟨0, ?_⟩
        rintro y ⟨t, rfl⟩
        dsimp [minByTime]
        apply Real.sInf_nonneg
        rintro y ⟨S', _hS', rfl⟩
        exact maxSetConductanceOnInterval_nonneg G t Δ S'
      _ ≤ 1 := hle1


/-- A pair `(φ, Δ)` satisfies the *window guarantee* for `𝒢` if in every
length-`Δ` interval `[t₁, t₁ + Δ - 1]`, every admissible cut `S` has at
least one step `t` with `φ^t(S) ≥ φ`. -/
def hasWindowGuarantee {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraph V)
    (φ : ℝ) (Δ : ℕ) : Prop :=
  ∀ t₁ : ℕ, ∀ S ∈ admissibleCuts G,
    ∃ t ∈ Finset.Icc t₁ (t₁ + Δ - 1),
      φ ≤ (G.snapshot t).setConductance S




/-- If `hasWindowGuarantee G φ Δ` holds, then for any starting time `t₁` and
admissible cut `S`, the per-step conductance exceeds `φ`
at some time in `[t₁, t₁+Δ-1]`, hence `φ ≤ maxSetConductanceOnInterval G t₁
(t₁+Δ-1) S`. -/
theorem hasWindowGuarantee_le_maxSetConductanceOnInterval {V : Type*} [Fintype V] [Nonempty V]
    [DecidableEq V] (G : TemporalGraph V)    {φ : ℝ} {Δ : ℕ}
    (hwin : hasWindowGuarantee G φ Δ)
    (t₁ : ℕ) {S : Finset V} (hS : S ∈ admissibleCuts G) :
    φ ≤ maxSetConductanceOnInterval G t₁ Δ S := by
  obtain ⟨t, ht, hφt⟩ := hwin t₁ S hS
  have ht' : t ∈ Finset.Icc t₁ (t₁ + (Δ - 1)) := by
    rw [Finset.mem_Icc] at ht ⊢; omega
  exact le_trans hφt (le_maxSetConductanceOnInterval G t₁ Δ S ht')

theorem le_windowConductance_of_hasWindowGuarantee {V : Type*} [Fintype V] [Nonempty V]
    [DecidableEq V] (G : TemporalGraph V)    (hadm : (admissibleCuts G).Nonempty)
    {φ : ℝ} {Δ : ℕ} (hΔ : 1 ≤ Δ)
    (hwin : hasWindowGuarantee G φ Δ) :
    φ ≤ windowConductance G Δ := by
  have hΔ_ne : Δ ≠ 0 := by omega
  unfold windowConductance
  simp [hΔ_ne]
  refine le_csInf (Set.range_nonempty _) ?_
  rintro y ⟨t, rfl⟩
  refine le_csInf (hadm.image _) ?_
  rintro z ⟨S, hS, rfl⟩
  exact hasWindowGuarantee_le_maxSetConductanceOnInterval G hwin t hS

theorem windowConductance_le_maxSetConductanceOnInterval {V : Type*} [Fintype V] [Nonempty V]
    [DecidableEq V] (G : TemporalGraph V)    {Δ : ℕ} (hΔ : 1 ≤ Δ) (t₁ : ℕ) {S : Finset V}
    (hS : S ∈ admissibleCuts G) :
    windowConductance G Δ ≤
      maxSetConductanceOnInterval G t₁ Δ S := by
  let minByTime : ℕ → ℝ := fun t =>
    sInf ((fun S => maxSetConductanceOnInterval G t Δ S) '' admissibleCuts G)
  have hΔ_ne : Δ ≠ 0 := by omega
  unfold windowConductance
  simp [hΔ_ne]
  calc
    sInf (Set.range minByTime) ≤ minByTime t₁ := by
      refine csInf_le ?_ ⟨t₁, rfl⟩
      refine ⟨0, ?_⟩
      rintro y ⟨t, rfl⟩
      dsimp [minByTime]
      apply Real.sInf_nonneg
      rintro y ⟨S', _hS', rfl⟩
      exact maxSetConductanceOnInterval_nonneg G t Δ S'
    _ ≤ maxSetConductanceOnInterval G t₁ Δ S := by
      dsimp [minByTime]
      refine csInf_le ?_ ⟨S, hS, rfl⟩
      refine ⟨0, ?_⟩
      rintro y ⟨S', _hS', rfl⟩
      exact maxSetConductanceOnInterval_nonneg G t₁ Δ S'

theorem hasWindowGuarantee_of_le_windowConductance {V : Type*} [Fintype V] [Nonempty V]
    [DecidableEq V] (G : TemporalGraph V)    {φ : ℝ} {Δ : ℕ} (hΔ : 1 ≤ Δ)
    (hφ : φ ≤ windowConductance G Δ) :
    hasWindowGuarantee G φ Δ := by
  intro t₁ S hS
  have hdelta_le := windowConductance_le_maxSetConductanceOnInterval G hΔ t₁ hS
  obtain ⟨t, ht, hmax⟩ := exists_mem_eq_maxSetConductanceOnInterval G t₁ Δ S
  have ht' : t ∈ Finset.Icc t₁ (t₁ + Δ - 1) := by
    rw [Finset.mem_Icc] at ht ⊢; omega
  refine ⟨t, ht', ?_⟩
  calc
    φ ≤ windowConductance G Δ := hφ
    _ ≤ maxSetConductanceOnInterval G t₁ Δ S := hdelta_le
    _ = (G.snapshot t).setConductance S := hmax

/-- The ratios `φ^Δ(G)/Δ` for `Δ ≥ 1`, whose supremum defines the temporal conductance. -/
def windowConductanceRatios {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraph V) : Set ℝ :=
  {r : ℝ | ∃ Δ : ℕ, 1 ≤ Δ ∧ r = windowConductance G Δ / (Δ : ℝ)}

/-- \label{eq:temporal-conductance}

Temporal conductance `Φ(G) = sup_{Δ ≥ 1} φ^Δ(G)/Δ`.
When `Φ(G) > 0`, consensus time is `Θ(n/Φ(G))`. -/
def temporalConductance {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraph V) : ℝ :=
  sSup (windowConductanceRatios G)

theorem bddAbove_temporalConductance_set {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraph V) :
    BddAbove (windowConductanceRatios G) := by
  refine ⟨1, fun r hr => ?_⟩
  obtain ⟨Δ, hΔ, rfl⟩ := hr
  calc
    windowConductance G Δ / (Δ : ℝ)
        ≤ windowConductance G Δ := by
          exact div_le_self (windowConductance_nonneg G Δ) (by exact_mod_cast hΔ)
    _ ≤ 1 := windowConductance_le_one G Δ

theorem windowConductance_div_le_temporalConductance {V : Type*} [Fintype V] [Nonempty V]
    [DecidableEq V] (G : TemporalGraph V) {Δ : ℕ} (hΔ : 1 ≤ Δ) :
    windowConductance G Δ / (Δ : ℝ) ≤ temporalConductance G := by
  rw [temporalConductance]
  exact le_csSup (bddAbove_temporalConductance_set G) ⟨Δ, hΔ, rfl⟩

theorem temporalConductance_nonneg {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraph V) :
    0 ≤ temporalConductance G := by
  have h1 := windowConductance_div_le_temporalConductance G (le_refl 1)
  have h0 : (0 : ℝ) ≤ windowConductance G 1 / (1 : ℝ) := by
    simpa using windowConductance_nonneg G 1
  linarith

/-- \label{lem:temporalConductance-ge-of-hasWindowGuarantee}

**L104.** A single `hasWindowGuarantee` witness `(φ, Δ)` with `1 ≤ Δ` and
at least one admissible cut lower-bounds the temporal conductance by
`φ / Δ`. Composes `le_windowConductance_of_hasWindowGuarantee` (per-
cut form) with `windowConductance_div_le_temporalConductance`
(`sSup` membership). Used by the lower-bound theorem T10 to produce a
paper-aligned `Φ(𝒢)`-bound from T41's single window witness. -/
theorem temporalConductance_ge_div_of_hasWindowGuarantee {V : Type*} [Fintype V] [Nonempty V]
    [DecidableEq V] (G : TemporalGraph V) (hadm : (admissibleCuts G).Nonempty)
    {φ : ℝ} {Δ : ℕ} (hΔ : 1 ≤ Δ) (hwin : hasWindowGuarantee G φ Δ) :
    φ / (Δ : ℝ) ≤ temporalConductance G := by
  have hΔ_nn : (0 : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast Nat.zero_le _
  calc φ / (Δ : ℝ)
      ≤ windowConductance G Δ / (Δ : ℝ) :=
        div_le_div_of_nonneg_right
          (le_windowConductance_of_hasWindowGuarantee G hadm hΔ hwin) hΔ_nn
    _ ≤ temporalConductance G :=
        windowConductance_div_le_temporalConductance G hΔ


end TemporalGraph

namespace TemporalGraphFixedDegree

/-- Largest conductance of `S` over the length-`Δ` window `[t, t+Δ-1]`. -/
def maxSetConductanceOnInterval {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraphFixedDegree V) (t Δ : ℕ) (S : Finset V) : ℝ :=
  ⨆ s ∈ Finset.Icc t (t + (Δ - 1)), (G.snapshot s).setConductance S

/-- Sets S that satisfy 0 < Vol(S) ≤ m; for fixed-degree temporal graphs, this condition does not
depend on the time t, so we use t=0. -/
abbrev admissibleCuts {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraphFixedDegree V) : Set (Finset V) :=
  (G.snapshot 0).admissibleCuts

/-- `Δ`-window conductance `φ^Δ(G) = min_t min_{S admissible} φ^{[t, t+Δ-1]}(S)`. -/
def windowConductance {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraphFixedDegree V) (Δ : ℕ) : ℝ :=
  if Δ = 0 then 0  -- degenerate case: empty interval
  else sInf {sInf {G.maxSetConductanceOnInterval t Δ S | S ∈ G.admissibleCuts} | t}

/-- `φ^[t₁,t₂](S) = ∑_{t=t₁}^{t₂} φ^t(S)`, via the underlying `TemporalGraph`. -/
abbrev setConductanceOnInterval {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraphFixedDegree V) (t₁ t₂ : ℕ) (S : Finset V) : ℝ :=
  G.toTemporalGraph.setConductanceOnInterval t₁ t₂ S

/-- Temporal conductance `Φ(G) = sup_{Δ ≥ 1} φ^Δ(G)/Δ`.
When `Φ(G) > 0`, consensus time is `Θ(n/Φ(G))`. -/
abbrev temporalConductance {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraphFixedDegree V) : ℝ :=
  G.toTemporalGraph.temporalConductance

/-- The temporal conductance of `G`: the supremum of `φ^Δ(G)/Δ` for `Δ ≥ 1`. -/
def Φ {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraphFixedDegree V) : ℝ≥0∞ :=
  ⨆ Δ ≥ 1, ENNReal.ofReal (G.windowConductance Δ) / Δ

/-- `Φ` agrees with the `ℝ`-valued `temporalConductance`. -/
theorem Φ_eq {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : TemporalGraphFixedDegree V) :
    G.Φ = ENNReal.ofReal G.temporalConductance := by
  have hterm : ∀ Δ : ℕ, 1 ≤ Δ →
      ENNReal.ofReal (G.windowConductance Δ) / (Δ : ℝ≥0∞)
        = ENNReal.ofReal (G.windowConductance Δ / (Δ : ℝ)) := by
    intro Δ hΔ
    rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hΔ), ENNReal.ofReal_natCast]
  have hub : G.Φ ≤ ENNReal.ofReal G.temporalConductance :=
    iSup₂_le fun Δ hΔ => (hterm Δ hΔ).le.trans <| ENNReal.ofReal_le_ofReal <|
      TemporalGraph.windowConductance_div_le_temporalConductance G.toTemporalGraph hΔ
  refine le_antisymm hub ?_
  have hne_top : G.Φ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hub
  rw [ENNReal.ofReal_le_iff_le_toReal hne_top]
  refine Real.sSup_le (fun r hr => ?_) ENNReal.toReal_nonneg
  obtain ⟨Δ, hΔ, rfl⟩ := hr
  have hmem : ENNReal.ofReal (G.windowConductance Δ / (Δ : ℝ)) ≤ G.Φ := by
    rw [← hterm Δ hΔ]
    exact le_iSup₂ (f := fun (Δ : ℕ) (_ : 1 ≤ Δ) =>
      ENNReal.ofReal (G.windowConductance Δ) / (Δ : ℝ≥0∞)) Δ hΔ
  have hnn : 0 ≤ G.windowConductance Δ / (Δ : ℝ) :=
    div_nonneg (TemporalGraph.windowConductance_nonneg G.toTemporalGraph Δ) (Nat.cast_nonneg Δ)
  calc G.windowConductance Δ / (Δ : ℝ)
      = (ENNReal.ofReal (G.windowConductance Δ / (Δ : ℝ))).toReal :=
        (ENNReal.toReal_ofReal hnn).symm
    _ ≤ G.Φ.toReal := ENNReal.toReal_mono hne_top hmem

end TemporalGraphFixedDegree
