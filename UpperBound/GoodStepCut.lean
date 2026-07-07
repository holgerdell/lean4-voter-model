module

public import TemporalGraph.Conductance
import TemporalGraph.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic



@[expose] public section
open MeasureTheory Finset

namespace VoterModel

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- \label{lem:interval-good-step-cut}

Let `t, Δ ∈ ℕ` with `Δ > 0`. If `φ^{[t, t+Δ−1]}(S) ≥ 1`, then there exists
at least one time step `t'` in `[t, t+Δ−1]` such that
`e_{t'}(S, S̄) ≥ Vol(S) / Δ`. -/
theorem interval_good_step_cut
  [Nonempty V]
  (G : TemporalGraphFixedDegree V) (t Δ : ℕ) (S : Finset V)
  -- Δ > 0
  (hΔ : 0 < Δ)
  -- φ^{[t, t+Δ−1]}(S) ≥ 1
  (hphi : 1 ≤ TemporalGraph.setConductanceOnInterval G t (t + Δ - 1) S) :
  -- Conclusion: ∃ t' ∈ [t, t+Δ−1], e_{t'}(S, S̄) ≥ Vol(S) / Δ
  ∃ t' ∈ Finset.Icc t (t + Δ - 1),
    (TemporalGraph.edgesBetween G t' S (Finset.univ \ S) : ℝ) ≥
      (TemporalGraph.volume G t S : ℝ) / (Δ : ℝ) := by
  let I := Finset.Icc t (t + Δ - 1)
  have hI : I.Nonempty := Finset.nonempty_Icc.mpr (by omega)
  have hcard : I.card = Δ := by simp [I, Nat.card_Icc]; omega
  let vol : ℝ := (TemporalGraph.volume G t S : ℝ)
  let f : ℕ → ℝ := fun t' => (TemporalGraph.edgesBetween G t' S (Finset.univ \ S) : ℝ)
  by_cases hvol0 : vol = 0
  · -- Zero volume: any time step works since threshold is 0.
    obtain ⟨t', ht'⟩ := hI
    exact ⟨t', ht', calc
      (TemporalGraph.edgesBetween G t' S (Finset.univ \ S) : ℝ) ≥ 0 := by positivity
      _ = (TemporalGraph.volume G t S : ℝ) / (Δ : ℝ) := by simp [vol, hvol0]⟩
  · have hvol_pos : 0 < vol := lt_of_le_of_ne (by positivity) (Ne.symm hvol0)
    have hvol_fixed : ∀ t' ∈ I, (TemporalGraph.volume G t' S : ℝ) = vol :=
      fun t' _ => by dsimp [vol]; exact_mod_cast G.volume_fixed S t' t
    -- 1 ≤ ∑ (f / vol), then multiply by vol to get vol ≤ ∑ f
    have hphi' : 1 ≤ ∑ t' ∈ I, f t' / vol := by
      calc 1 ≤ ∑ t' ∈ I, f t' / (TemporalGraph.volume G t' S : ℝ) := by
              simpa [TemporalGraph.setConductanceOnInterval,
                SimpleGraph.setConductance, I, f] using hphi
           _ = ∑ t' ∈ I, f t' / vol :=
              Finset.sum_congr rfl fun t' ht' => by rw [hvol_fixed t' ht']
    have hsum_ge : vol ≤ ∑ t' ∈ I, f t' := by
      have h := mul_le_mul_of_nonneg_right hphi' hvol_pos.le
      rw [one_mul, Finset.sum_mul] at h
      simp_rw [div_mul_cancel₀ _ hvol0] at h
      exact h
    -- Pigeonhole: tmax witnesses f(tmax) ≥ vol / Δ
    obtain ⟨tmax, htmax, hmax⟩ := Finset.exists_max_image I f hI
    refine ⟨tmax, htmax, ?_⟩
    rw [ge_iff_le, div_le_iff₀ (by exact_mod_cast hΔ : (0 : ℝ) < Δ)]
    calc vol ≤ ∑ t' ∈ I, f t' := hsum_ge
      _ ≤ I.card • f tmax := Finset.sum_le_card_nsmul I f _ fun t' ht' => hmax t' ht'
      _ = f tmax * (Δ : ℝ) := by rw [nsmul_eq_mul, hcard]; ring

end VoterModel
