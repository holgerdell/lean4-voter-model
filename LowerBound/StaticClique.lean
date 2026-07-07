module

import TemporalGraph.Regular
import VoterProcess.Construction
import Mathlib.Algebra.Order.Star.Real
public import SimpleGraph.Conductance
public import VoterProcess.CrossCut
import UpperBound.TwoOpinion.Theorem

/-! ## Voter model absorption on a static clique

Formalizes `\label{lem:static-clique-voter}` from §4. The paper's lemma is realized
on the used proof chain in two pieces: the constant `Γ` together with the per-round
`1/2` consensus bound (`berenbrink_step_bound_pmf`, here) and the `α`-amplification to
`1 - 2⁻ᵅ` (`geometric_boundary_bound_pmf_static`, in `SubProcess.lean`).

The self-contained measure-level packaging `static_clique_voter_absorption` (with its
exclusive dependencies) is archived in `attic/` — its pointwise-deterministic-init
hypothesis is not met by the available a.s.-init trajectory construction, so it cannot
be wired into the chain without weakening its statement.

## Main results

- `berenbrink_step_bound_pmf`: there exists a constant `Γ ≥ 1` such that on the
  `2k`-clique consensus is reached within `Γ * k` steps with probability at least `1/2`.
-/

@[expose] public section

open MeasureTheory Finset
open scoped BigOperators

noncomputable section

namespace TemporalGraph.VoterProcess.LowerBound

/-- Vertex set of the static clique `K_{2k}`. -/
abbrev CliqueVertex (k : ℕ) [NeZero k] := Fin (2 * k)

/-- Temporal graph that is constantly the complete graph on `2k` vertices. -/
def staticCliqueGraph (k : ℕ) [NeZero k] : TemporalGraph (CliqueVertex k) where
  snapshot _ := ⊤
  decidableAdj _ := by intro; infer_instance

theorem neighbors_staticClique
    (k : ℕ) [NeZero k] (t : ℕ) (v : CliqueVertex k) :
    TemporalGraph.neighborFinset (staticCliqueGraph k) t v = Finset.univ.erase v := by
  ext w
  by_cases h : w = v
  · subst h
    simp [TemporalGraph.neighborFinset, staticCliqueGraph]
  · have hvw : v ≠ w := Ne.symm h
    simp [TemporalGraph.neighborFinset, staticCliqueGraph, h, hvw]

private theorem degree_staticClique
    (k : ℕ) [NeZero k] (t : ℕ) (v : CliqueVertex k) :
    TemporalGraph.degree (staticCliqueGraph k) t v = 2 * k - 1 := by
  show (TemporalGraph.neighborFinset (staticCliqueGraph k) t v).card = 2 * k - 1
  rw [neighbors_staticClique k t v]
  simp [Fintype.card_fin]

private theorem edgesBetween_staticClique
    (k : ℕ) [NeZero k] (t : ℕ) (S : Finset (CliqueVertex k)) :
    ((staticCliqueGraph k).snapshot t).edgesBetween S (Finset.univ \ S) =
      S.card * (2 * k - S.card) := by
  unfold SimpleGraph.edgesBetween staticCliqueGraph
  have hfilter :
      (S ×ˢ (Finset.univ \ S)).filter (fun p => ¬p.1 = p.2) =
        (S ×ˢ (Finset.univ \ S)) := by
    ext p
    constructor
    · intro hp
      exact (Finset.mem_filter.mp hp).1
    · intro hp
      refine Finset.mem_filter.mpr ⟨hp, ?_⟩
      rcases Finset.mem_product.mp hp with ⟨hpS, hpCompl⟩
      have hpNot : p.2 ∉ S := (Finset.mem_sdiff.mp hpCompl).2
      intro hEq
      exact hpNot (hEq ▸ hpS)
  simp only [SimpleGraph.top_adj]
  rw [hfilter, Finset.card_product, Finset.card_sdiff]
  simp [Finset.card_univ]

private theorem staticClique_fixedDegrees
    (k : ℕ) [NeZero k] : TemporalGraph.FixedDegrees (staticCliqueGraph k) := by
  refine ⟨?_, ?_⟩
  · intro v t₁ t₂
    rw [degree_staticClique, degree_staticClique]
  · intro v t
    rw [degree_staticClique]
    have hk_pos : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
    omega

private theorem volume_staticClique
    (k : ℕ) [NeZero k] (t : ℕ) (S : Finset (CliqueVertex k)) :
    TemporalGraph.volume (staticCliqueGraph k) t S = S.card * (2 * k - 1) := by
  let hfix : TemporalGraph.FixedDegrees (staticCliqueGraph k) := staticClique_fixedDegrees k
  have hregular :
      ∀ u v : CliqueVertex k,
        TemporalGraph.deg (staticCliqueGraph k) u =
          TemporalGraph.deg (staticCliqueGraph k) v := by
    intro u v
    simp [TemporalGraph.deg, degree_staticClique]
  calc
    TemporalGraph.volume (staticCliqueGraph k) t S
      = TemporalGraph.volume (staticCliqueGraph k) 0 S :=
          TemporalGraph.volume_fixed (staticCliqueGraph k) hfix S t 0
    _ = S.card * TemporalGraph.deg (staticCliqueGraph k)
          (Classical.choice (show Nonempty (CliqueVertex k) from inferInstance)) :=
          TemporalGraph.volume_eq_card_mul_deg_of_regular (staticCliqueGraph k) hregular S
    _ = S.card * (2 * k - 1) := by
          congr 1
          simp [TemporalGraph.deg, degree_staticClique]

private theorem setConductanceAt_staticClique
    (k : ℕ) [NeZero k] (t : ℕ) (S : Finset (CliqueVertex k)) :
    ((staticCliqueGraph k).snapshot t).setConductance S =
      ((S.card * (2 * k - S.card) : ℕ) : ℝ) /
        ((S.card * (2 * k - 1) : ℕ) : ℝ) := by
  unfold SimpleGraph.setConductance
  have hvol : ((staticCliqueGraph k).snapshot t).volume S = S.card * (2 * k - 1) :=
    volume_staticClique k t S
  rw [edgesBetween_staticClique, hvol]

/-- \label{lem:static-clique-conductance}

Let `k ≥ 1`. In the complete graph on `2k` vertices, every nonempty set `S`
with `|S| ≤ k` has one-step conductance at least `1/2`.
-/
theorem static_clique_conductance
    (k : ℕ) [NeZero k] (hk : 1 ≤ k)
    (t : ℕ) (S : Finset (CliqueVertex k))
    (hS_nonempty : S.Nonempty)
    (hS_card_le : S.card ≤ k) :
    (1 / 2 : ℝ) ≤ ((staticCliqueGraph k).snapshot t).setConductance S := by
  rw [setConductanceAt_staticClique]
  have hS_pos_nat : 0 < S.card := Finset.card_pos.mpr hS_nonempty
  have hden_pos_nat : 0 < S.card * (2 * k - 1) := by
    have h2k1_pos : 0 < 2 * k - 1 := by omega
    exact Nat.mul_pos hS_pos_nat h2k1_pos
  have hden_pos :
      (0 : ℝ) < ((S.card * (2 * k - 1) : ℕ) : ℝ) := by
    exact_mod_cast hden_pos_nat
  refine (le_div_iff₀ hden_pos).2 ?_
  have hinner : 2 * k - 1 ≤ 2 * (2 * k - S.card) := by
    omega
  have hnat0 : S.card * (2 * k - 1) ≤ S.card * (2 * (2 * k - S.card)) :=
    Nat.mul_le_mul_left _ hinner
  have hnat : S.card * (2 * k - 1) ≤ 2 * (S.card * (2 * k - S.card)) := by
    calc
      S.card * (2 * k - 1) ≤ S.card * (2 * (2 * k - S.card)) := hnat0
      _ = 2 * (S.card * (2 * k - S.card)) := by
            calc
              S.card * (2 * (2 * k - S.card))
                  = (S.card * 2) * (2 * k - S.card) := by rw [Nat.mul_assoc]
              _ = (2 * S.card) * (2 * k - S.card) := by rw [Nat.mul_comm S.card 2]
              _ = 2 * (S.card * (2 * k - S.card)) := by rw [Nat.mul_assoc]
  have hcast :
      (((S.card * (2 * k - 1) : ℕ) : ℝ)) ≤
        (2 : ℝ) * (((S.card * (2 * k - S.card) : ℕ) : ℝ)) := by
    exact_mod_cast hnat
  nlinarith

/-  ---------------------------------------------------------------
    Private helper: time-shift invariance for the static clique.
    The general absorbing-state and Chapman-Kolmogorov lemmas are
    imported from VoterModel.Spec.LemmaAbsorption.
    --------------------------------------------------------------- -/

/-- For the static clique, `opinionProcess₂` is time-shift invariant
because `stepDist₂` only depends on `neighborFinset`, which is constant. -/
private theorem opinionProcess₂_shift'
    (k : ℕ) [NeZero k] (t₁ t₂ n : ℕ) (S : Finset (CliqueVertex k)) :
    VoterModel.opinionProcess₂ (staticCliqueGraph k) t₁ n S =
      VoterModel.opinionProcess₂ (staticCliqueGraph k) t₂ n S := by
  have hstep : ∀ t S', VoterModel.stepDist₂ (staticCliqueGraph k) t S' =
      VoterModel.stepDist₂ (staticCliqueGraph k) 0 S' := by
    intro t S'
    unfold VoterModel.stepDist₂ VoterModel.nextOpinionDist₂
    simp only [neighbors_staticClique]
  induction n generalizing S with
  | zero => rfl
  | succ n ih =>
    show (VoterModel.opinionProcess₂ (staticCliqueGraph k) t₁ n S).bind
        (VoterModel.stepDist₂ (staticCliqueGraph k) (t₁ + n)) =
      (VoterModel.opinionProcess₂ (staticCliqueGraph k) t₂ n S).bind
        (VoterModel.stepDist₂ (staticCliqueGraph k) (t₂ + n))
    rw [ih S]
    have hst : VoterModel.stepDist₂ (staticCliqueGraph k) (t₁ + n) =
               VoterModel.stepDist₂ (staticCliqueGraph k) (t₂ + n) :=
      funext fun T => (hstep (t₁ + n) T).trans (hstep (t₂ + n) T).symm
    rw [hst]



/-- Shared helper: any admissible cut `S` of the static clique satisfies `S.card ≤ k`.
We have `relativeVolume S = |S|/(2k)` (as ℚ), so `relativeVolume ≤ 1/2` ⟹ `|S| ≤ k`. -/
private theorem staticClique_admissible_card_le
    (k : ℕ) [NeZero k] (hk : 1 ≤ k) {S : Finset (CliqueVertex k)}
    (hS : S ∈ TemporalGraph.admissibleCuts (staticCliqueGraph k)) :
    S.card ≤ k := by
  have hk_pos : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have h2k_pos : 0 < 2 * k := by omega
  have h2k1_pos : 0 < 2 * k - 1 := by omega
  -- Unfold `relativeVolume` and compute via `volume_staticClique`.
  have hvolS : TemporalGraph.volume (staticCliqueGraph k) 0 S = S.card * (2 * k - 1) :=
    volume_staticClique k 0 S
  have hvolU :
      TemporalGraph.volume (staticCliqueGraph k) 0 Finset.univ =
        (Finset.univ : Finset (CliqueVertex k)).card * (2 * k - 1) :=
    volume_staticClique k 0 Finset.univ
  have hcardU : (Finset.univ : Finset (CliqueVertex k)).card = 2 * k := by
    simp [Finset.card_univ, Fintype.card_fin]
  -- Get `relativeVolume ≤ 1/2` from admissibility.
  have hrv_le : TemporalGraph.relativeVolume (staticCliqueGraph k) S ≤ 1 / 2 :=
    ((TemporalGraph.mem_admissibleCuts_iff_relativeVolume (staticCliqueGraph k)
      (fun v => (staticClique_fixedDegrees k).2 v 0) S).mp hS).2.2.2
  -- Compute `relativeVolume` in ℚ.
  have hrv_eq :
      TemporalGraph.relativeVolume (staticCliqueGraph k) S =
        ((S.card * (2 * k - 1) : ℕ) : ℚ) /
          ((2 * k * (2 * k - 1) : ℕ) : ℚ) := by
    change ((staticCliqueGraph k).snapshot 0).relativeVolume S = _
    unfold SimpleGraph.relativeVolume
    change
        (TemporalGraph.volume (staticCliqueGraph k) 0 S : ℚ) /
          (TemporalGraph.volume (staticCliqueGraph k) 0 Finset.univ : ℚ) = _
    rw [hvolS, hvolU, hcardU]
  rw [hrv_eq] at hrv_le
  -- Cross-multiply: `|S|*(2k-1) * 2 ≤ 2k*(2k-1) * 1`.
  have hden_pos : (0 : ℚ) < ((2 * k * (2 * k - 1) : ℕ) : ℚ) := by
    exact_mod_cast Nat.mul_pos h2k_pos h2k1_pos
  have hineq :
      ((S.card * (2 * k - 1) : ℕ) : ℚ) * 2 ≤ ((2 * k * (2 * k - 1) : ℕ) : ℚ) * 1 := by
    rw [div_le_div_iff₀ hden_pos (by norm_num : (0 : ℚ) < 2)] at hrv_le
    linarith
  -- Reduce in ℕ.
  have hineq_nat : S.card * (2 * k - 1) * 2 ≤ 2 * k * (2 * k - 1) := by
    have hcast : ((S.card * (2 * k - 1) * 2 : ℕ) : ℚ) ≤
        ((2 * k * (2 * k - 1) : ℕ) : ℚ) := by
      push_cast
      push_cast at hineq
      linarith
    exact_mod_cast hcast
  have h2k1_pos' : 0 < 2 * k - 1 := h2k1_pos
  -- Cancel `(2k-1)`: `|S| * 2 ≤ 2 * k`, hence `|S| ≤ k`.
  have hcancel : S.card * 2 ≤ 2 * k := by
    have h1 : S.card * 2 * (2 * k - 1) ≤ 2 * k * (2 * k - 1) := by
      have : S.card * (2 * k - 1) * 2 = S.card * 2 * (2 * k - 1) := by ring
      linarith
    exact Nat.le_of_mul_le_mul_right h1 h2k1_pos'
  omega

/-- Auxiliary: every admissible cut has set-conductance `≥ 1/2` at every time. -/
private theorem staticClique_admissible_setConductance_half
    (k : ℕ) [NeZero k] (hk : 1 ≤ k)
    (t : ℕ) {S : Finset (CliqueVertex k)}
    (hS : S ∈ TemporalGraph.admissibleCuts (staticCliqueGraph k)) :
    (1 / 2 : ℝ) ≤ ((staticCliqueGraph k).snapshot t).setConductance S :=
  static_clique_conductance k hk t S
    (SimpleGraph.nonempty_of_mem_admissibleCuts _ hS)
    (staticClique_admissible_card_le k hk hS)

/-- Auxiliary: the static clique has a nonempty admissible-cut set. The singleton
`{0}` is admissible because `2k ≥ 2`. -/
private theorem staticClique_admissibleCuts_nonempty
    (k : ℕ) [NeZero k] (hk : 1 ≤ k) :
    (TemporalGraph.admissibleCuts (staticCliqueGraph k)).Nonempty := by
  -- Use the singleton `{0}` (recall `CliqueVertex k = Fin (2*k)` and `2*k ≥ 2`).
  have h2k_pos : 0 < 2 * k := by omega
  have h2k1_pos : 0 < 2 * k - 1 := by omega
  let v₀ : CliqueVertex k := ⟨0, h2k_pos⟩
  have hvolS : TemporalGraph.volume (staticCliqueGraph k) 0 ({v₀} : Finset _) =
      1 * (2 * k - 1) := by
    rw [volume_staticClique]; simp
  have hvolU :
      TemporalGraph.volume (staticCliqueGraph k) 0 Finset.univ =
        (Finset.univ : Finset (CliqueVertex k)).card * (2 * k - 1) :=
    volume_staticClique k 0 Finset.univ
  have hcardU : (Finset.univ : Finset (CliqueVertex k)).card = 2 * k := by
    simp [Finset.card_univ, Fintype.card_fin]
  have hrv_eq :
      TemporalGraph.relativeVolume (staticCliqueGraph k) ({v₀} : Finset _) =
        ((1 * (2 * k - 1) : ℕ) : ℚ) /
          ((2 * k * (2 * k - 1) : ℕ) : ℚ) := by
    change ((staticCliqueGraph k).snapshot 0).relativeVolume ({v₀} : Finset _) = _
    unfold SimpleGraph.relativeVolume
    change
        (TemporalGraph.volume (staticCliqueGraph k) 0 ({v₀} : Finset _) : ℚ) /
          (TemporalGraph.volume (staticCliqueGraph k) 0 Finset.univ : ℚ) = _
    rw [hvolS, hvolU, hcardU]
  refine ⟨{v₀}, (TemporalGraph.mem_admissibleCuts_iff_relativeVolume (staticCliqueGraph k)
    (fun v => (staticClique_fixedDegrees k).2 v 0) {v₀}).mpr ⟨?_, ?_, ?_, ?_⟩⟩
  · exact Finset.singleton_nonempty v₀
  · intro heq
    have hcard : ({v₀} : Finset (CliqueVertex k)).card =
        (Finset.univ : Finset (CliqueVertex k)).card := by rw [heq]
    simp [Finset.card_univ, Fintype.card_fin] at hcard
    omega
  · -- 0 < relativeVolume
    rw [hrv_eq]
    have hnum_pos : (0 : ℚ) < ((1 * (2 * k - 1) : ℕ) : ℚ) := by
      exact_mod_cast Nat.mul_pos (by norm_num : 0 < 1) h2k1_pos
    have hden_pos : (0 : ℚ) < ((2 * k * (2 * k - 1) : ℕ) : ℚ) := by
      exact_mod_cast Nat.mul_pos h2k_pos h2k1_pos
    exact div_pos hnum_pos hden_pos
  · -- relativeVolume ≤ 1/2
    rw [hrv_eq]
    have hden_pos : (0 : ℚ) < ((2 * k * (2 * k - 1) : ℕ) : ℚ) := by
      exact_mod_cast Nat.mul_pos h2k_pos h2k1_pos
    rw [div_le_div_iff₀ hden_pos (by norm_num : (0 : ℚ) < 2)]
    push_cast
    have hk_q : (1 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk
    have h2k1_nn : (0 : ℚ) ≤ ((2 * k - 1 : ℕ) : ℚ) := by exact_mod_cast Nat.zero_le _
    nlinarith

/-- Auxiliary: the static clique has positive `temporalConductance` (needed
for `consensus_time_upper_bound`). In fact `temporalConductance ≥ 1/2`. -/
private theorem staticClique_temporalConductance_ge_half
    (k : ℕ) [NeZero k] (hk : 1 ≤ k) :
    (1 / 2 : ℝ) ≤ TemporalGraph.temporalConductance (staticCliqueGraph k) := by
  -- Witness: `hasWindowGuarantee G (1/2) 1`. Then `temporalConductance ≥ 1/2 / 1 = 1/2`.
  have hadm_ne := staticClique_admissibleCuts_nonempty k hk
  have hwin : TemporalGraph.hasWindowGuarantee (staticCliqueGraph k) (1 / 2 : ℝ) 1 := by
    intro t₁ S hS
    refine ⟨t₁, Finset.mem_Icc.mpr ⟨le_refl _, by omega⟩, ?_⟩
    exact staticClique_admissible_setConductance_half k hk t₁ hS
  have hbound :=
    TemporalGraph.temporalConductance_ge_div_of_hasWindowGuarantee
      (staticCliqueGraph k) hadm_ne (by norm_num : (1 : ℕ) ≤ 1) hwin
  -- hbound : (1/2 : ℝ) / 1 ≤ temporalConductance G
  have hsimp : (1 / 2 : ℝ) / (1 : ℕ) = (1 / 2 : ℝ) := by push_cast; ring
  rw [hsimp] at hbound
  exact hbound


/-- The number of edges in the static `2k`-clique. -/
private theorem staticClique_edge_count
    (k : ℕ) [NeZero k] :
    ((staticCliqueGraph k).snapshot 0).edgeFinset.card = k * (2 * k - 1) := by
  have hk_pos : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  -- `(staticCliqueGraph k).snapshot 0 = ⊤`, so its edge count is `(2k).choose 2 = k*(2k-1)`.
  show (⊤ : SimpleGraph (CliqueVertex k)).edgeFinset.card = k * (2 * k - 1)
  rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
  rw [show Fintype.card (CliqueVertex k) = 2 * k from Fintype.card_fin _]
  rw [Nat.choose_two_right]
  -- `2k * (2k - 1) / 2 = k * (2k - 1)`. Use `2 * k * (2 * k - 1) = 2 * (k * (2 * k - 1))`.
  have h : 2 * k * (2 * k - 1) = 2 * (k * (2 * k - 1)) := by ring
  rw [h, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]

/-- The minimum degree of the static `2k`-clique is `2k - 1`. -/
private theorem staticClique_minDegree
    (k : ℕ) [NeZero k] :
    (staticCliqueGraph k).minDegreeAt 0 = 2 * k - 1 := by
  -- `G.minDegreeAt 0 = inf' (fun v => G.degree 0 v)`.
  -- Every degree equals `2k - 1`, so `inf'` of a constant function is `2k - 1`.
  unfold TemporalGraph.minDegreeAt
  have hdeg : (fun v : CliqueVertex k => (staticCliqueGraph k).degree 0 v) =
      (fun _ => 2 * k - 1) := by
    funext v
    exact degree_staticClique k 0 v
  rw [hdeg]
  exact Finset.inf'_const Finset.univ_nonempty (2 * k - 1)

/-- Berenbrink et al. 2016 absorption bound (PMF form, internal).
Derived from `consensus_time_upper_bound` (T22) applied to the canonical
voter model construction on the static clique.

There exists `C ≥ 1` such that from any initial state on the `2k`-clique,
the probability of reaching consensus in `C * k` steps is at least `1/2`.

The proof builds the canonical vm via `ofDeterministicAbstract` (on the full trajectory space
`ℕ → (V → Fin 2)`, with initial opinion function `phiZeroInv T`), applies
`consensus_time_upper_bound` to get `vm.μ {absorptionTime ≤ N} ≥ 1/2`, uses a.e.
permanence (`ae_minoritySet_empty_of_absorptionTime_le`) to bound this by
`vm.μ {A_N = ∅} + vm.μ {A_N = univ}`, and converts to PMF via
`ofDeterministicAbstract_markov_almostSure_init` (with `phiZero (phiZeroInv T) = T`). -/
private theorem berenbrink_absorption_bound_pmf :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (k : ℕ) [NeZero k] (_ : 1 ≤ k)
      (t : ℕ) (T : Finset (CliqueVertex k)),
    (1 / 2 : ENNReal) ≤
      VoterModel.opinionProcess₂ (staticCliqueGraph k) t (C * k) T Finset.univ +
      VoterModel.opinionProcess₂ (staticCliqueGraph k) t (C * k) T ∅ := by
  -- C is chosen with slack to cover the deadline of `consensus_time_upper_bound`
  -- for the static clique, using `Φt ≥ 1/2` and `m/d_min = k`.
  classical
  refine ⟨1179648, by norm_num, ?_⟩
  intro k _ hk t T
  -- Step 1: time-shift to t = 0.
  rw [opinionProcess₂_shift' k t 0]
  -- Now goal: 1/2 ≤ op(0, 1179648·k, T)(univ) + op(0, 1179648·k, T)(∅).
  set C : ℕ := 1179648 with hC_def
  set N : ℕ := C * k with hN_def
  -- Step 2: build the canonical vm with init T.
  set hfix := staticClique_fixedDegrees k
  let Gf := (staticCliqueGraph k).withFixed hfix
  set vm := VoterModel.ofDeterministicAbstract
    (staticCliqueGraph k) (VoterModel.phiZeroInv T) with hvm_def
  -- Step 3: apply consensus_time_upper_bound (T22 wrapper).
  have hm_eq : (k * (2 * k - 1) : ℕ) = ((staticCliqueGraph k).snapshot 0).edgeFinset.card :=
    (staticClique_edge_count k).symm
  have hd_eq : (2 * k - 1 : ℕ) = (staticCliqueGraph k).minDegreeAt 0 :=
    (staticClique_minDegree k).symm
  have hd_pos : 0 < 2 * k - 1 := by omega
  have hΦt_ge_half : (1 / 2 : ℝ) ≤ TemporalGraph.temporalConductance (staticCliqueGraph k) :=
    staticClique_temporalConductance_ge_half k hk
  have hΦt_pos : 0 < TemporalGraph.temporalConductance (staticCliqueGraph k) :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hΦt_ge_half
  have hUB := VoterModel.consensus_time_upper_bound Gf vm
    (2 * k - 1) hd_eq hd_pos
    49152 (by norm_num) (by norm_num)
    hΦt_pos
  rw [show Gf.numEdges = k * (2 * k - 1) from hm_eq.symm] at hUB
  -- hUB : 1/2 ≤ vm.μ {ω | vm.absorptionTime ω ≤ ⌈8·49152·m/(d·Φt)⌉₊}
  -- where m = k*(2k-1), d_min = 2k-1, so m/d_min = k.
  set B : ℕ := ⌈8 * (49152 : ℝ) * ((k * (2 * k - 1) : ℕ) : ℝ) /
    (((2 * k - 1 : ℕ) : ℝ) * TemporalGraph.temporalConductance (staticCliqueGraph k))⌉₊ with hB_def
  change (1 / 2 : ℝ) ≤ ((vm.μ : Measure _) {ω | vm.absorptionTime ω ≤ (B : ℕ∞)}).toReal at hUB
  -- Step 4: Bound B ≤ N. Then {absorptionTime ≤ B} ⊆ {absorptionTime ≤ N}.
  have hd_pos_r : (0 : ℝ) < ((2 * k - 1 : ℕ) : ℝ) := by exact_mod_cast hd_pos
  have hm_div : ((k * (2 * k - 1) : ℕ) : ℝ) / ((2 * k - 1 : ℕ) : ℝ) = k := by
    push_cast
    field_simp
  have hk_pos : (0 : ℝ) < (k : ℝ) := by
    have : 0 < k := NeZero.pos k
    exact_mod_cast this
  have hk_ge1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  -- Bound the real expression inside ⌈⌉:
  --   8·49152·(k(2k-1)) / ((2k-1)·Φt) = 8·49152·k/Φt ≤ 8·49152·k·2 ≤ 24·49152·k = C·k.
  have hreal_le : 8 * (49152 : ℝ) * ((k * (2 * k - 1) : ℕ) : ℝ) /
      (((2 * k - 1 : ℕ) : ℝ) * TemporalGraph.temporalConductance (staticCliqueGraph k)) ≤ (C * k : ℝ) := by
    have hΦt_ne : TemporalGraph.temporalConductance (staticCliqueGraph k) ≠ 0 := ne_of_gt hΦt_pos
    have hkd_cast : ((k * (2 * k - 1) : ℕ) : ℝ) = (k : ℝ) * ((2 * k - 1 : ℕ) : ℝ) := by
      push_cast; ring
    rw [hkd_cast, show 8 * (49152 : ℝ) * ((k : ℝ) * ((2 * k - 1 : ℕ) : ℝ)) /
        (((2 * k - 1 : ℕ) : ℝ) * TemporalGraph.temporalConductance (staticCliqueGraph k)) =
        8 * (49152 : ℝ) * (k : ℝ) /
        TemporalGraph.temporalConductance (staticCliqueGraph k) from by
      field_simp [hd_pos_r.ne', hΦt_ne]]
    have hC_cast : (C : ℝ) * k = 24 * (49152 : ℝ) * k := by
      rw [hC_def]; push_cast; ring
    rw [hC_cast, div_le_iff₀ hΦt_pos]
    nlinarith [hΦt_ge_half, hk_pos]
  -- Take ceilings: B ≤ ⌈C·k⌉ = C·k.
  have hB_le : B ≤ N := by
    -- hreal_le says the real LHS ≤ (C * k : ℝ).
    -- ⌈real LHS⌉₊ ≤ ⌈(C*k : ℝ)⌉₊ = C*k.
    -- B = ⌈8·49152·m/(d·Φ)⌉₊ ≤ ⌈C·k⌉₊ = C·k = N.
    have hceil : B ≤ ⌈(C * k : ℝ)⌉₊ := Nat.ceil_le_ceil hreal_le
    have hceil_nat : ⌈((C * k : ℕ) : ℝ)⌉₊ = C * k := Nat.ceil_natCast _
    have hN_eq : (N : ℕ) = C * k := hN_def
    have : B ≤ ⌈((C * k : ℕ) : ℝ)⌉₊ := by
      have hcast : ((C * k : ℕ) : ℝ) = (C * k : ℝ) := by push_cast; ring
      rw [hcast]; exact hceil
    rw [hceil_nat] at this
    rw [hN_eq]
    exact this
  -- Step 5: {absorptionTime ≤ B} ⊆ {absorptionTime ≤ N}, so vm.μ extends.
  have hsubset : ({ω | vm.absorptionTime ω ≤ (B : ℕ∞)} : Set _) ⊆
      {ω | vm.absorptionTime ω ≤ (N : ℕ∞)} := by
    intro ω hω
    have hωB : vm.absorptionTime ω ≤ (B : ℕ∞) := hω
    exact le_trans hωB (by exact_mod_cast hB_le)
  -- Steps 6+7 (a.e.): {absorptionTime ≤ N} ⊆ {A_N ∈ {∅, univ}} a.e. via permanence,
  -- since minoritySet G N (A N ω) = ∅ forces A N ω ∈ {∅, univ}.
  have hμ_split : (vm.μ : Measure _) {ω | vm.absorptionTime ω ≤ (N : ℕ∞)} ≤
      (vm.μ : Measure _) {ω | vm.opinionZeroSet N ω = Finset.univ} +
        (vm.μ : Measure _) {ω | vm.opinionZeroSet N ω = ∅} := by
    have hsub_ae : ({ω | vm.absorptionTime ω ≤ (N : ℕ∞)} : Set _) ≤ᵐ[(vm.μ : Measure _)]
        ({ω | vm.opinionZeroSet N ω = Finset.univ} ∪ {ω | vm.opinionZeroSet N ω = ∅} : Set _) := by
      filter_upwards [TemporalGraph.VoterModelAbstract.ae_minoritySet_empty_of_absorptionTime_le
        (G := Gf) vm] with ω hperm
      intro hω
      have hωle : vm.absorptionTime ω ≤ (N : ℕ∞) := hω
      have hmin : VoterModel.minoritySet (staticCliqueGraph k) N (vm.opinionZeroSet N ω) = ∅ :=
        hperm N hωle
      unfold VoterModel.minoritySet at hmin
      split_ifs at hmin with hcond_split
      · -- A N ω = ∅
        right; exact hmin
      · -- univ \ A N ω = ∅, so A N ω = univ.
        left
        apply Finset.eq_univ_of_forall
        intro x
        by_contra hxA
        have : x ∈ Finset.univ \ vm.opinionZeroSet N ω :=
          Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxA⟩
        rw [hmin] at this
        exact Finset.notMem_empty _ this
    refine le_trans (measure_mono_ae hsub_ae) ?_
    exact measure_union_le _ _
  -- Step 8: convert vm.μ {A N = S'} = opinionProcess₂(0, N, T, S') via marginal-init lemma.
  have hμ_univ_eq : (vm.μ : Measure _) {ω | vm.opinionZeroSet N ω = Finset.univ} =
      VoterModel.opinionProcess₂ (staticCliqueGraph k) 0 N T Finset.univ := by
    rw [hvm_def, VoterModel.ofDeterministicAbstract_markov_almostSure_init
      (staticCliqueGraph k) (VoterModel.phiZeroInv T) N Finset.univ, VoterModel.phiZero_phiZeroInv]
  have hμ_emp_eq : (vm.μ : Measure _) {ω | vm.opinionZeroSet N ω = ∅} =
      VoterModel.opinionProcess₂ (staticCliqueGraph k) 0 N T ∅ := by
    rw [hvm_def, VoterModel.ofDeterministicAbstract_markov_almostSure_init
      (staticCliqueGraph k) (VoterModel.phiZeroInv T) N ∅, VoterModel.phiZero_phiZeroInv]
  -- Step 9: Combine.
  have hμ_B_le : (vm.μ : Measure _) {ω | vm.absorptionTime ω ≤ (B : ℕ∞)} ≤
      (vm.μ : Measure _) {ω | vm.absorptionTime ω ≤ (N : ℕ∞)} := measure_mono hsubset
  -- vm.μ {absorptionTime ≤ B} has toReal ≥ 1/2 (from hUB).
  -- vm.μ {absorptionTime ≤ B} ≤ vm.μ {absorptionTime ≤ N} ≤ op(univ) + op(∅).
  have hfin : (vm.μ : Measure _) {ω | vm.absorptionTime ω ≤ (B : ℕ∞)} ≠ ⊤ := measure_ne_top _ _
  have hfin' : (vm.μ : Measure _) {ω | vm.absorptionTime ω ≤ (N : ℕ∞)} ≠ ⊤ :=
    measure_ne_top _ _
  have hfin_sum : VoterModel.opinionProcess₂ (staticCliqueGraph k) 0 N T Finset.univ +
      VoterModel.opinionProcess₂ (staticCliqueGraph k) 0 N T ∅ ≠ ⊤ := by
    rw [← hμ_univ_eq, ← hμ_emp_eq]
    exact ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩
  -- 1/2 ≤ vm.μ {absorptionTime ≤ B}.toReal, so 1/2 ≤ vm.μ {absorptionTime ≤ B} as ENNReal.
  have hUB_ennreal : (1 / 2 : ENNReal) ≤
      (vm.μ : Measure _) {ω | vm.absorptionTime ω ≤ (B : ℕ∞)} := by
    have h12 : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ENNReal) := by
      rw [show (1 / 2 : ℝ) = 2⁻¹ from by norm_num,
        ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num
    rw [← h12]
    exact (ENNReal.ofReal_le_iff_le_toReal hfin).mpr hUB
  calc (1 / 2 : ENNReal)
      ≤ (vm.μ : Measure _) {ω | vm.absorptionTime ω ≤ (B : ℕ∞)} := hUB_ennreal
    _ ≤ (vm.μ : Measure _) {ω | vm.absorptionTime ω ≤ (N : ℕ∞)} := hμ_B_le
    _ ≤ (vm.μ : Measure _) {ω | vm.opinionZeroSet N ω = Finset.univ} +
          (vm.μ : Measure _) {ω | vm.opinionZeroSet N ω = ∅} := hμ_split
    _ = VoterModel.opinionProcess₂ (staticCliqueGraph k) 0 N T Finset.univ +
        VoterModel.opinionProcess₂ (staticCliqueGraph k) 0 N T ∅ := by
            rw [hμ_univ_eq, hμ_emp_eq]

/-- \label{lem:static-clique-voter}

Constant/base part of `lem:static-clique-voter`: PMF-level per-round step bound from
Berenbrink et al. 2016. There exists `Γ ≥ 1` such that on the `2k`-clique consensus is
reached within `Γ * k` steps with probability at least `1/2` (the `α = 1` case). The
`α`-amplification to `1 - 2⁻ᵅ` within `α * Γ * k` steps is
`geometric_boundary_bound_pmf_static`. Exposed for callers. -/
theorem berenbrink_step_bound_pmf :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (k : ℕ) [NeZero k] (_ : 1 ≤ k)
      (t : ℕ) (T : Finset (CliqueVertex k)),
    (1 / 2 : ENNReal) ≤
      VoterModel.opinionProcess₂ (staticCliqueGraph k) t (C * k) T Finset.univ +
      VoterModel.opinionProcess₂ (staticCliqueGraph k) t (C * k) T ∅ :=
  berenbrink_absorption_bound_pmf

end TemporalGraph.VoterProcess.LowerBound
