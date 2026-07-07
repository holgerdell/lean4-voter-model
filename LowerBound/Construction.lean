module

public import TemporalGraph.Defs
import Mathlib.Algebra.Order.Ring.Star


/-! ## Lower-bound temporal graph construction

Formalizes the temporal graph `𝒢^{T,k,z}` from §4 of the paper.

## Main results

- `Params` -- parameters `T`, `k`, `z` with `T, k, z ≥ 1` and `z` even.
 - `VertexSet` -- the vertex set `Fin z × Fin k`.
- `snapshot0`, `snapshot1` -- the two alternating unions of `2k`-vertex cliques.
- `lowerBoundGraph` -- the temporal graph `𝒢^{T,k,z}`. -/

@[expose] public section

open Finset

noncomputable section

namespace TemporalGraph.VoterProcess.LowerBound

/-- Parameters for the temporal graph `𝒢^{T,k,z}` from §4. -/
structure Params where
  T : ℕ
  k : ℕ
  z : ℕ
  hT_pos : 0 < T
  hk_pos : 0 < k
  hz_pos : 0 < z
  hz_even : 2 ∣ z

theorem Params.hz_two_le (p : Params) : 2 ≤ p.z := by
  rcases p.hz_even with ⟨m, hm⟩
  have hm1 : 1 ≤ m := by
    by_contra hmlt
    have hm0 : m = 0 := by omega
    have : p.z = 0 := by simpa [hm0] using hm
    exact Nat.ne_of_gt p.hz_pos this
  have h2m : 2 * 1 ≤ 2 * m := Nat.mul_le_mul_left 2 hm1
  simpa [hm] using h2m

instance (p : Params) : NeZero p.z := ⟨Nat.ne_of_gt p.hz_pos⟩

/-- The vertex set of `𝒢^{T,k,z}`: `z` groups of `k` vertices each. -/
abbrev VertexSet (p : Params) := Fin p.z × Fin p.k

instance (p : Params) : Nonempty (VertexSet p) :=
  ⟨⟨⟨0, p.hz_pos⟩, ⟨0, p.hk_pos⟩⟩⟩

/-- The `i`-th block `V_i` of vertices. We use zero-based indexing, so this is
the paper's `V_{i+1}`. -/
def block (p : Params) (i : Fin p.z) : Finset (VertexSet p) :=
  Finset.univ.image fun j => (i, j)

@[simp] theorem mem_block (p : Params) (i : Fin p.z) (v : VertexSet p) :
    v ∈ block p i ↔ v.1 = i := by
  constructor
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨j, -, hj⟩
    exact (Prod.mk.inj hj |>.1).symm
  · intro hv
    refine Finset.mem_image.mpr ?_
    refine ⟨v.2, mem_univ _, ?_⟩
    cases v
    cases hv
    rfl

@[simp] theorem card_block (p : Params) (i : Fin p.z) : (block p i).card = p.k := by
  unfold block
  rw [Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fin]
  intro a b hab
  exact Prod.mk.inj hab |>.2

theorem block_disjoint (p : Params) {i j : Fin p.z} (hij : i ≠ j) :
    Disjoint (block p i) (block p j) := by
  refine Finset.disjoint_left.mpr ?_
  intro v hvi hvj
  exact hij <| (mem_block p i v).mp hvi ▸ (mem_block p j v).mp hvj


/-- The interval index `j` such that `t ∈ I_j`. Since `T > 0`, this is
`⌊t / T⌋ + 1`. -/
def intervalIndex (p : Params) (t : ℕ) : ℕ :=
  t / p.T + 1

/-- The parity class of active anchors in a snapshot. -/
def parityNat (odd : Bool) : ℕ := cond odd 1 0

/-- The cyclic anchor of the active `2k`-clique containing a given block. -/
def activeAnchor (p : Params) (odd : Bool) (i : Fin p.z) : Fin p.z :=
  if i.val % 2 = parityNat odd then i else i + (-1)

theorem parity_add_one_ne_parity_iff
    (p : Params) (odd : Bool) (a : Fin p.z) :
    ((a + 1).val % 2 ≠ parityNat odd) ↔ a.val % 2 = parityNat odd := by
  have hsucc : ((a + 1).val % 2) = ((a.val + 1) % 2) := by
    calc
      ((a + 1).val % 2) = (((a.val + 1) % p.z) % 2) := by
        simp [Fin.val_add]
      _ = ((a.val + 1) % 2) := by
        rw [Nat.mod_mod_of_dvd _ p.hz_even]
  rw [hsucc]
  cases odd <;> unfold parityNat
  · constructor
    · intro h
      rcases Nat.mod_two_eq_zero_or_one a.val with h0 | h1
      · exact h0
      · exfalso
        have hstep : (a.val + 1) % 2 = ((a.val % 2 + 1) % 2) := by
          calc
            (a.val + 1) % 2 = ((a.val % 2) + (1 % 2)) % 2 := by
              simp [Nat.add_mod]
            _ = ((a.val % 2 + 1) % 2) := by simp
        have : (a.val + 1) % 2 = 0 := by
          simpa [h1] using hstep
        exact h this
    · intro ha
      have hstep : (a.val + 1) % 2 = ((a.val % 2 + 1) % 2) := by
        calc
          (a.val + 1) % 2 = ((a.val % 2) + (1 % 2)) % 2 := by
            simp [Nat.add_mod]
          _ = ((a.val % 2 + 1) % 2) := by simp
      simpa [ha] using hstep
  · constructor
    · intro h
      rcases Nat.mod_two_eq_zero_or_one a.val with h0 | h1
      · exfalso
        have hstep : (a.val + 1) % 2 = ((a.val % 2 + 1) % 2) := by
          calc
            (a.val + 1) % 2 = ((a.val % 2) + (1 % 2)) % 2 := by
              simp [Nat.add_mod]
            _ = ((a.val % 2 + 1) % 2) := by simp
        have : (a.val + 1) % 2 = 1 := by
          simpa [h0] using hstep
        exact h this
      · exact h1
    · intro ha
      have hstep : (a.val + 1) % 2 = ((a.val % 2 + 1) % 2) := by
        calc
          (a.val + 1) % 2 = ((a.val % 2) + (1 % 2)) % 2 := by
            simp [Nat.add_mod]
          _ = ((a.val % 2 + 1) % 2) := by simp
      simpa [ha] using hstep

theorem activeAnchor_parity
    (p : Params) (odd : Bool) (i : Fin p.z) :
    (activeAnchor p odd i).val % 2 = parityNat odd := by
  unfold activeAnchor
  by_cases hi : i.val % 2 = parityNat odd
  · simp [hi]
  · have hsub : (i + (-1) + 1 : Fin p.z) = i := by
      simp [add_assoc]
    have hneq : ((i + (-1) + 1).val % 2 ≠ parityNat odd) := by
      simpa [hsub] using hi
    have hpred : (i + (-1)).val % 2 = parityNat odd :=
      (parity_add_one_ne_parity_iff p odd (i + (-1))).1 hneq
    simp [hi, hpred]

/-- Public parity lemma: when `odd = decide (j % 2 = 1)`,
    `activeAnchor p odd i` has the same parity as `j`. -/
theorem activeAnchor_parity_jmod2 (p : Params) (j : ℕ) (i : Fin p.z) :
    (activeAnchor p (decide (j % 2 = 1)) i).val % 2 = j % 2 := by
  have h := activeAnchor_parity p (decide (j % 2 = 1)) i
  simp only [parityNat] at h
  rcases Nat.mod_two_eq_zero_or_one j with hj | hj <;> simp_all

theorem activeAnchor_eq_iff_eq_or_succ
    (p : Params) (odd : Bool) (a i : Fin p.z)
    (ha : a.val % 2 = parityNat odd) :
    activeAnchor p odd i = a ↔ i = a ∨ i = a + 1 := by
  unfold activeAnchor
  by_cases hi : i.val % 2 = parityNat odd
  · constructor
    · intro h
      left
      simpa [hi] using h
    · rintro (rfl | hsucc)
      · simp [ha]
      · exfalso
        have hneq : ((a + 1).val % 2 ≠ parityNat odd) :=
          (parity_add_one_ne_parity_iff p odd a).2 ha
        exact hneq (hsucc ▸ hi)
  · constructor
    · intro h
      right
      have h' : i + (-1) = a := by
        simpa [hi] using h
      rw [← h']
      simp [add_assoc]
    · rintro (hEq | hEq)
      · exfalso
        subst hEq
        exact hi ha
      · subst hEq
        have hneq : ((a + 1).val % 2 ≠ parityNat odd) :=
          (parity_add_one_ne_parity_iff p odd a).2 ha
        simp [hneq, add_assoc]

/-- Adjacency in one snapshot: two distinct vertices are adjacent when they lie
in the same active pair of consecutive cyclic blocks. -/
def snapshotAdj (p : Params) (odd : Bool) (u v : VertexSet p) : Prop :=
  u ≠ v ∧ activeAnchor p odd u.1 = activeAnchor p odd v.1

instance snapshotAdjDecidable (p : Params) (odd : Bool) : DecidableRel (snapshotAdj p odd) := by
  classical
  infer_instance

/-- The snapshot `G₀` from the paper. In zero-based indexing this uses odd
anchors `a = 1, 3, ..., z - 1`, corresponding to paper indices
`i = 2, 4, ..., z`. -/
def snapshot0 (p : Params) : SimpleGraph (VertexSet p) where
  Adj := snapshotAdj p true
  symm := ⟨fun {_} {_} huv => ⟨huv.1.symm, huv.2.symm⟩⟩
  loopless := ⟨fun u (hu : snapshotAdj p true u u) => hu.1 rfl⟩

/-- The snapshot `G₁` from the paper. In zero-based indexing this uses even
anchors `a = 0, 2, ..., z - 2`, corresponding to paper indices
`i = 1, 3, ..., z - 1`. -/
def snapshot1 (p : Params) : SimpleGraph (VertexSet p) where
  Adj := snapshotAdj p false
  symm := ⟨fun {_} {_} huv => ⟨huv.1.symm, huv.2.symm⟩⟩
  loopless := ⟨fun u (hu : snapshotAdj p false u u) => hu.1 rfl⟩

/-- \label{def:lower-bound-construction}

Let `T, k, z ≥ 1` with `z` even. The temporal graph `𝒢^{T,k,z}` has vertex set
`Fin z × Fin k`, viewed as a disjoint union of `z` blocks of size `k`. For each
interval `I_j = {(j - 1)T, ..., jT - 1}`, the graph is constant on `I_j` and is
equal to `G_{j mod 2}`. -/
def lowerBoundGraph (p : Params) : TemporalGraph (VertexSet p) where
  snapshot t := if intervalIndex p t % 2 = 0 then snapshot0 p else snapshot1 p
  decidableAdj t := by
    classical
    infer_instance

private theorem snapshot_neighborFinset
    (p : Params) (odd : Bool) (v : VertexSet p) :
    Finset.univ.filter (fun w => snapshotAdj p odd v w) =
      (block p (activeAnchor p odd v.1) ∪ block p (activeAnchor p odd v.1 + 1)).erase v := by
  classical
  letI : DecidablePred (fun w => snapshotAdj p odd v w) := Classical.decPred _
  let a : Fin p.z := activeAnchor p odd v.1
  have ha : a.val % 2 = parityNat odd := activeAnchor_parity p odd v.1
  ext w
  constructor
  · intro hw
    rcases Finset.mem_filter.mp hw with ⟨_, hAdj⟩
    rcases hAdj with ⟨hne, hEq⟩
    have hwpair : w.1 = a ∨ w.1 = a + 1 :=
      (activeAnchor_eq_iff_eq_or_succ p odd a w.1 ha).1 (by simpa [a] using hEq.symm)
    rw [Finset.mem_erase, Finset.mem_union, mem_block, mem_block]
    exact ⟨hne.symm, hwpair⟩
  · intro hw
    rw [Finset.mem_erase, Finset.mem_union, mem_block, mem_block] at hw
    rcases hw with ⟨hne, hwpair⟩
    refine Finset.mem_filter.mpr ⟨mem_univ _, ?_⟩
    refine ⟨hne.symm, ?_⟩
    have : activeAnchor p odd w.1 = a :=
      (activeAnchor_eq_iff_eq_or_succ p odd a w.1 ha).2 hwpair
    simpa [a] using this.symm

private theorem snapshot_degree
    (p : Params) (odd : Bool) (v : VertexSet p) :
    (Finset.univ.filter fun w => snapshotAdj p odd v w).card = 2 * p.k - 1 := by
  classical
  letI : DecidablePred (fun w => snapshotAdj p odd v w) := Classical.decPred _
  let a : Fin p.z := activeAnchor p odd v.1
  have ha : a.val % 2 = parityNat odd := activeAnchor_parity p odd v.1
  rw [snapshot_neighborFinset]
  have hv_mem : v ∈ block p a ∪ block p (a + 1) := by
    have hvpair : v.1 = a ∨ v.1 = a + 1 :=
      (activeAnchor_eq_iff_eq_or_succ p odd a v.1 ha).1 rfl
    simp [mem_block, hvpair]
  rw [Finset.card_erase_of_mem hv_mem, Finset.card_union_of_disjoint]
  · simp [card_block]
    ring_nf
  · refine block_disjoint p ?_
    intro h
    have hz2 : 2 ≤ p.z := p.hz_two_le
    have hval : ((a.val + 1) % p.z) = a.val := by
      simpa [Fin.val_add] using congrArg Fin.val h.symm
    by_cases hlt : a.val + 1 < p.z
    · have : a.val + 1 = a.val := by
        simp [Nat.mod_eq_of_lt hlt] at hval
      omega
    · have hz_eq : a.val + 1 = p.z := by omega
      have hzero : (a.val + 1) % p.z = 0 := by
        simp [hz_eq]
      have ha0 : a.val = 0 := by
        rw [hzero] at hval
        exact hval.symm
      omega

theorem lowerBoundGraph_degree (p : Params) (t : ℕ) (v : VertexSet p) :
    TemporalGraph.degree (lowerBoundGraph p) t v = 2 * p.k - 1 := by
  simp only [TemporalGraph.degree]
  by_cases hpar : intervalIndex p t % 2 = 0
  · have hg : (lowerBoundGraph p).snapshot t = snapshot0 p := by simp [lowerBoundGraph, hpar]
    simp only [hg, SimpleGraph.degree, SimpleGraph.neighborFinset, SimpleGraph.neighborSet,
        snapshot0, Set.toFinset_setOf]
    exact snapshot_degree p true v
  · have hg : (lowerBoundGraph p).snapshot t = snapshot1 p := by simp [lowerBoundGraph, hpar]
    simp only [hg, SimpleGraph.degree, SimpleGraph.neighborFinset, SimpleGraph.neighborSet,
        snapshot1, Set.toFinset_setOf]
    exact snapshot_degree p false v

/-- In interval `[j·T, (j+1)·T)`, the neighbors of any vertex in the active
    K_{2k} clique `block p a ∪ block p (a+1)` are exactly the other clique vertices. -/
theorem lowerBoundGraph_neighborFinset_clique (p : Params) (a : Fin p.z)
    (j t : ℕ) (ht_lo : j * p.T ≤ t) (ht_hi : t < (j + 1) * p.T)
    (ha : a.val % 2 = j % 2)
    (v : VertexSet p) (hv : v ∈ block p a ∪ block p (a + 1)) :
    TemporalGraph.neighborFinset (lowerBoundGraph p) t v =
      (block p a ∪ block p (a + 1)).erase v := by
  simp only [Finset.mem_union, mem_block] at hv
  have htdiv : t / p.T = j := by
    have h1 : j ≤ t / p.T := (Nat.le_div_iff_mul_le p.hT_pos).mpr ht_lo
    have h2 : t / p.T < j + 1 := (Nat.div_lt_iff_lt_mul p.hT_pos).mpr ht_hi
    omega
  have hinterval : intervalIndex p t = j + 1 := by
    unfold intervalIndex; rw [htdiv]
  by_cases hj : j % 2 = 0
  · -- j even: graph = snapshot1 (false/even anchors)
    have hpar : intervalIndex p t % 2 ≠ 0 := by rw [hinterval]; omega
    have hgraph : (lowerBoundGraph p).snapshot t = snapshot1 p := by
      simp [lowerBoundGraph, hpar]
    have ha_parity : a.val % 2 = parityNat false := by
      show a.val % 2 = 0; rw [ha]; exact hj
    have hactive : activeAnchor p false v.1 = a :=
      (activeAnchor_eq_iff_eq_or_succ p false a v.1 ha_parity).mpr hv
    simp only [TemporalGraph.neighborFinset, hgraph, snapshot1, SimpleGraph.neighborFinset,
        SimpleGraph.neighborSet, Set.toFinset_setOf]
    rw [snapshot_neighborFinset p false v, hactive]
  · -- j odd: graph = snapshot0 (true/odd anchors)
    have hpar : intervalIndex p t % 2 = 0 := by rw [hinterval]; omega
    have hgraph : (lowerBoundGraph p).snapshot t = snapshot0 p := by
      simp [lowerBoundGraph, hpar]
    have ha_parity : a.val % 2 = parityNat true := by
      show a.val % 2 = 1; rw [ha]; omega
    have hactive : activeAnchor p true v.1 = a :=
      (activeAnchor_eq_iff_eq_or_succ p true a v.1 ha_parity).mpr hv
    simp only [TemporalGraph.neighborFinset, hgraph, snapshot0, SimpleGraph.neighborFinset,
        SimpleGraph.neighborSet, Set.toFinset_setOf]
    rw [snapshot_neighborFinset p true v, hactive]

theorem lowerBoundGraph_fixedDegrees (p : Params) : FixedDegrees (lowerBoundGraph p) := by
  refine ⟨?_, ?_⟩
  · intro v t₁ t₂
    rw [lowerBoundGraph_degree, lowerBoundGraph_degree]
  · intro v t
    rw [lowerBoundGraph_degree]
    have hk : 0 < p.k := p.hk_pos
    omega


theorem card_vertexSet (p : Params) : Fintype.card (VertexSet p) = p.k * p.z := by
  change Fintype.card (Fin p.z × Fin p.k) = p.k * p.z
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Nat.mul_comm]


/-- A set `S` is a *contiguous arc* if it is a consecutive run of `block`s:
`S = block b ∪ block (b+1) ∪ … ∪ block (b+m-1)` for some starting block `b` and length `m ≤ z`.
Used in the lower-bound absorption proof to track the shape of the minority set. -/
def IsContiguousArc (p : Params) (S : Finset (VertexSet p)) : Prop :=
  ∃ (b : Fin p.z) (m : ℕ), m ≤ p.z ∧
    S = (Finset.range m).biUnion fun i =>
      block p ⟨(b.val + i) % p.z, Nat.mod_lt _ p.hz_pos⟩

end TemporalGraph.VoterProcess.LowerBound
