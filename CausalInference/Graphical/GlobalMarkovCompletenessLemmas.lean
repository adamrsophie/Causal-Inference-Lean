/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.SCM.Markov
public import CausalInference.Graphical.DSeparationDecide

/-!
# Auxiliary results for the completeness of d-separation

Auxiliary constructions for `CausalInference.Graphical.GlobalMarkovCompleteness`: distances to
the conditioning set, minimal active trails and the surgeries that shorten them, and Boolean
structural models that violate a conditional independence.

## Main definitions

* `Digraph.distZ G Z v`: the length of a shortest directed path from an ancestor `v` of `Z` to
  `Z`; `Digraph.nextZ G Z v`: the next vertex of such a path.
* `Digraph.IsDTrail G Z x y L`: `L` is an active trail from `x` to `y` given `Z`, written as a
  list of Bayes-ball states, with no repeated vertex.
* `Digraph.trailMeasure G Z L`: the number of states of `L` plus, summed over the colliders `c`
  of `L`, the distance `distZ c`.
* `Digraph.IsCollider L c`: `c` is a collider of the trail `L`.
* `Digraph.BoolRule G`: a deterministic local rule for Boolean variables on the vertices of `G`:
  the value of `v` is computed from the values of the parents of `v` and one fair noise bit.
* `Digraph.BoolRule.toSCM`: the corresponding structural causal model with independent fair
  noise bits.

## Main results

* `Digraph.exists_isDTrail_min`: a d-connection is witnessed by an active simple trail of
  minimal measure.
* `Digraph.IsDTrail.surgery_after`, `Digraph.IsDTrail.surgery_before`,
  `Digraph.IsDTrail.surgery_merge`: shortcuts through the shortest path from a collider to `Z`.
* `Digraph.IsDTrail.iterate_nextZ_notMem_of_min`: on a trail of minimal measure, the shortest
  path from a collider to `Z` meets the trail only at the collider;
  `Digraph.IsDTrail.iterate_nextZ_ne_of_min'`: the paths from distinct colliders are disjoint.
* `Digraph.BoolRule.exists_factorizes_not_condIndep`: a criterion for the failure of
  `{x} ⫫ {y} | Z` in the distribution of a Boolean model, which factorizes according to `G`.
  If in every solution with all of `Z` false the values at `x` and `y` agree, and some noise
  value makes `x` true and all of `Z` false, then `{x}` and `{y}` are not conditionally
  independent given `Z`.
-/

@[expose] public section

namespace Digraph

open CausalInference Finset

/-! ### Distance to the conditioning set -/

section Dist

variable {V : Type*} (G : Digraph V) (Z : Finset V)

/-- `G.NearZ Z k v`: some vertex of `Z` is reachable from `v` by a directed path with at most
`k` edges. -/
def NearZ : ℕ → V → Prop
  | 0, v => v ∈ Z
  | k + 1, v => v ∈ Z ∨ ∃ w, G.Adj v w ∧ NearZ k w

variable {G Z}

theorem nearZ_succ_of_nearZ : ∀ {k : ℕ} {v : V}, G.NearZ Z k v → G.NearZ Z (k + 1) v
  | 0, _, h => Or.inl h
  | _ + 1, _, Or.inl h => Or.inl h
  | _ + 1, _, Or.inr ⟨w, hvw, hw⟩ => Or.inr ⟨w, hvw, nearZ_succ_of_nearZ hw⟩

theorem nearZ_mem_ancestorsOf : ∀ {k : ℕ} {v : V}, G.NearZ Z k v → v ∈ G.ancestorsOf ↑Z
  | 0, _, h => subset_ancestorsOf _ (mem_coe.2 h)
  | _ + 1, _, Or.inl h => subset_ancestorsOf _ (mem_coe.2 h)
  | _ + 1, _, Or.inr ⟨_, hvw, hw⟩ => mem_ancestorsOf_of_adj hvw (nearZ_mem_ancestorsOf hw)

theorem exists_nearZ_of_mem_ancestorsOf {v : V} (h : v ∈ G.ancestorsOf ↑Z) :
    ∃ k, G.NearZ Z k v := by
  obtain ⟨z, hz, hvz⟩ := h
  induction hvz using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, hz⟩
  | head hvw _ ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, Or.inr ⟨_, hvw, hk⟩⟩

variable (G Z) in
open Classical in
/-- The length of a shortest directed path from `v` to `Z` (zero if there is none). -/
noncomputable def distZ (v : V) : ℕ := if h : ∃ k, G.NearZ Z k v then Nat.find h else 0

theorem nearZ_distZ {v : V} (h : v ∈ G.ancestorsOf ↑Z) : G.NearZ Z (G.distZ Z v) v := by
  classical
  have h' := exists_nearZ_of_mem_ancestorsOf h
  rw [distZ, dite_eq_left_of_eq_true (eq_true h')]
  exact Nat.find_spec h'

theorem distZ_le {k : ℕ} {v : V} (h : G.NearZ Z k v) : G.distZ Z v ≤ k := by
  classical
  rw [distZ, dite_eq_left_of_eq_true (eq_true ⟨k, h⟩)]
  exact Nat.find_min' _ h

theorem distZ_eq_zero_iff {v : V} (h : v ∈ G.ancestorsOf ↑Z) : G.distZ Z v = 0 ↔ v ∈ Z := by
  refine ⟨fun h0 => ?_, fun hv => Nat.le_zero.1 (distZ_le (k := 0) hv)⟩
  have := nearZ_distZ h
  rwa [h0] at this

variable (G Z) in
open Classical in
/-- The next vertex on a shortest directed path from `v` to `Z`. -/
noncomputable def nextZ (v : V) : V :=
  if h : ∃ w, G.Adj v w ∧ G.NearZ Z (G.distZ Z v - 1) w then Classical.choose h else v

theorem nextZ_spec {v : V} (h : v ∈ G.ancestorsOf ↑Z) (hv : v ∉ Z) :
    G.Adj v (G.nextZ Z v) ∧ G.nextZ Z v ∈ G.ancestorsOf ↑Z ∧
      G.distZ Z (G.nextZ Z v) + 1 = G.distZ Z v := by
  have hd : G.distZ Z v ≠ 0 := fun h0 => hv ((distZ_eq_zero_iff h).1 h0)
  obtain ⟨d, hd'⟩ := Nat.exists_eq_succ_of_ne_zero hd
  have hn := nearZ_distZ h
  rw [hd'] at hn
  have hex : ∃ w, G.Adj v w ∧ G.NearZ Z (G.distZ Z v - 1) w := by
    rcases hn with hn | hn
    · exact absurd hn hv
    · rw [hd']
      exact hn
  have hspec := Classical.choose_spec hex
  have heq : G.nextZ Z v = Classical.choose hex := by
    classical
    rw [nextZ, dite_eq_left_of_eq_true (eq_true hex)]
  rw [heq]
  refine ⟨hspec.1, nearZ_mem_ancestorsOf hspec.2, ?_⟩
  have h1 := distZ_le hspec.2
  have h2 : G.distZ Z v ≤ G.distZ Z (Classical.choose hex) + 1 :=
    distZ_le (Or.inr ⟨_, hspec.1, nearZ_distZ (nearZ_mem_ancestorsOf hspec.2)⟩)
  omega

theorem iterate_nextZ {c : V} (hc : c ∈ G.ancestorsOf ↑Z) :
    ∀ j ≤ G.distZ Z c, (G.nextZ Z)^[j] c ∈ G.ancestorsOf ↑Z ∧
      G.distZ Z ((G.nextZ Z)^[j] c) + j = G.distZ Z c
  | 0, _ => ⟨hc, rfl⟩
  | j + 1, hj => by
    obtain ⟨h1, h2⟩ := iterate_nextZ hc j (by omega)
    have hZ : (G.nextZ Z)^[j] c ∉ Z := fun h =>
      absurd ((distZ_eq_zero_iff h1).2 h) (by omega)
    obtain ⟨-, h3, h4⟩ := nextZ_spec h1 hZ
    rw [Function.iterate_succ_apply']
    exact ⟨h3, by omega⟩

theorem iterate_nextZ_notMem {c : V} (hc : c ∈ G.ancestorsOf ↑Z) {j : ℕ}
    (hj : j < G.distZ Z c) : (G.nextZ Z)^[j] c ∉ Z := fun h => by
  obtain ⟨h1, h2⟩ := iterate_nextZ hc j hj.le
  rw [(distZ_eq_zero_iff h1).2 h] at h2
  omega

theorem iterate_nextZ_adj {c : V} (hc : c ∈ G.ancestorsOf ↑Z) {j : ℕ}
    (hj : j < G.distZ Z c) : G.Adj ((G.nextZ Z)^[j] c) ((G.nextZ Z)^[j + 1] c) := by
  rw [Function.iterate_succ_apply']
  exact (nextZ_spec (iterate_nextZ hc j hj.le).1 (iterate_nextZ_notMem hc hj)).1

theorem iterate_nextZ_distZ_mem {c : V} (hc : c ∈ G.ancestorsOf ↑Z) :
    (G.nextZ Z)^[G.distZ Z c] c ∈ Z := by
  obtain ⟨h1, h2⟩ := iterate_nextZ hc _ le_rfl
  exact (distZ_eq_zero_iff h1).1 (by omega)

theorem iterate_nextZ_inj {c : V} (hc : c ∈ G.ancestorsOf ↑Z) {i j : ℕ}
    (hi : i ≤ G.distZ Z c) (hj : j ≤ G.distZ Z c)
    (h : (G.nextZ Z)^[i] c = (G.nextZ Z)^[j] c) : i = j := by
  have h1 := (iterate_nextZ hc i hi).2
  have h2 := (iterate_nextZ hc j hj).2
  rw [h] at h1
  omega

end Dist

/-! ### Active trails as lists of Bayes-ball states -/

section Trail

variable {V : Type*} (G : Digraph V) (Z : Finset V)

/-- The collider weight of a list of Bayes-ball states: the sum of `G.distZ Z v` over the
colliders `v` of the trail, that is, over the states `(v, true)` followed by a state with flag
`false`. -/
noncomputable def colSum : List (V × Bool) → ℕ
  | s :: t :: l => (if s.2 = true ∧ t.2 = false then G.distZ Z s.1 else 0) + colSum (t :: l)
  | _ => 0

/-- The measure minimized by the trail used in the completeness proof: the number of states
plus the collider weight. -/
noncomputable def trailMeasure (L : List (V × Bool)) : ℕ := L.length + G.colSum Z L

/-- `G.IsDTrail Z x y L`: the list `L` of Bayes-ball states encodes a simple trail from `x` to
`y` that is active given `Z`. It starts at `(x, false)`, consecutive states are joined in the
Bayes-ball state graph, it ends at `y ∉ Z`, and no vertex is repeated. -/
structure IsDTrail (x y : V) (L : List (V × Bool)) : Prop where
  head : L.head? = some (x, false)
  chain : L.IsChain (G.bayesBall ↑Z).Adj
  last : L.getLast?.map Prod.fst = some y
  last_notMem : y ∉ Z
  nodup : (L.map Prod.fst).Nodup

variable {G Z}

@[simp] theorem colSum_cons_cons (s t : V × Bool) (l : List (V × Bool)) :
    G.colSum Z (s :: t :: l) =
      (if s.2 = true ∧ t.2 = false then G.distZ Z s.1 else 0) + G.colSum Z (t :: l) := rfl

@[simp] theorem colSum_nil : G.colSum Z ([] : List (V × Bool)) = 0 := rfl

@[simp] theorem colSum_singleton (s : V × Bool) : G.colSum Z [s] = 0 := rfl

theorem colSum_le_cons (a : V × Bool) (l : List (V × Bool)) :
    G.colSum Z l ≤ G.colSum Z (a :: l) := by
  cases l with
  | nil => simp
  | cons b l => simp

theorem colSum_cons_le (a : V × Bool) (l : List (V × Bool)) :
    G.colSum Z (a :: l) ≤ G.distZ Z a.1 + G.colSum Z l := by
  cases l with
  | nil => simp
  | cons b l =>
    simp only [colSum_cons_cons]
    split_ifs <;> omega

theorem colSum_le_append (l₁ l₂ : List (V × Bool)) : G.colSum Z l₂ ≤ G.colSum Z (l₁ ++ l₂) := by
  induction l₁ with
  | nil => simp
  | cons a l₁ ih => exact ih.trans (colSum_le_cons a _)

theorem colSum_split (l₁ : List (V × Bool)) (s : V × Bool) (l₂ : List (V × Bool)) :
    G.colSum Z (l₁ ++ s :: l₂) = G.colSum Z (l₁ ++ [s]) + G.colSum Z (s :: l₂) := by
  induction l₁ with
  | nil => simp
  | cons a l₁ ih =>
    cases l₁ with
    | nil => simp
    | cons b l₁ =>
      simp only [List.cons_append, colSum_cons_cons] at ih ⊢
      rw [ih]
      omega

theorem colSum_eq_zero_of_true {l : List (V × Bool)} (h : ∀ s ∈ l, s.2 = true) :
    G.colSum Z l = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => rfl
    | cons b l =>
      rw [colSum_cons_cons, ih fun s hs => h s (List.mem_cons_of_mem _ hs),
        h b (by simp)]
      simp

theorem colSum_append_singleton_eq_zero_of_false {l : List (V × Bool)}
    (h : ∀ s ∈ l, s.2 = false) (s : V × Bool) : G.colSum Z (l ++ [s]) = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => simp [h a (by simp)]
    | cons b l =>
      rw [List.cons_append, List.cons_append, colSum_cons_cons, h a (by simp)]
      simp only [Bool.false_eq_true, false_and, ite_false, zero_add]
      exact ih fun s hs => h s (List.mem_cons_of_mem _ hs)

/-- An active trail in the sense of `Digraph.ActiveTrail` is a chain of Bayes-ball states with
the same vertices. -/
theorem ActiveTrail.exists_states {a : Bool} {u w : V} {l : List V}
    (p : G.ActiveTrail ↑Z a u w l) :
    ∃ L : List (V × Bool), L.map Prod.fst = l ∧ L.head? = some (u, a) ∧
      L.IsChain (G.bayesBall ↑Z).Adj ∧ L.getLast?.map Prod.fst = some w := by
  induction p with
  | @nil a v hv => exact ⟨[(v, a)], rfl, rfl, List.IsChain.singleton _, rfl⟩
  | @fwd a u v w l h hu q ih =>
    obtain ⟨L, h1, h2, h3, h4⟩ := ih
    rcases L with _ | ⟨t, L'⟩
    · simp at h2
    simp only [List.head?_cons, Option.some.injEq] at h2
    subst h2
    refine ⟨(u, a) :: (v, true) :: L', by simp [← h1], rfl, ?_, by simpa using h4⟩
    exact List.IsChain.cons_cons (bayesBall_adj_true.2 ⟨h, hu⟩) h3
  | @bwd u v w l h hu q ih =>
    obtain ⟨L, h1, h2, h3, h4⟩ := ih
    rcases L with _ | ⟨t, L'⟩
    · simp at h2
    simp only [List.head?_cons, Option.some.injEq] at h2
    subst h2
    refine ⟨(u, false) :: (v, false) :: L', by simp [← h1], rfl, ?_, by simpa using h4⟩
    exact List.IsChain.cons_cons (bayesBall_adj_false_false.2 ⟨h, hu⟩) h3
  | @collider u v w l h hu q ih =>
    obtain ⟨L, h1, h2, h3, h4⟩ := ih
    rcases L with _ | ⟨t, L'⟩
    · simp at h2
    simp only [List.head?_cons, Option.some.injEq] at h2
    subst h2
    refine ⟨(u, true) :: (v, false) :: L', by simp [← h1], rfl, ?_, by simpa using h4⟩
    exact List.IsChain.cons_cons (bayesBall_adj_true_false.2 ⟨h, hu⟩) h3

/-- d-connection of two vertices yields a simple active trail as a list of states. -/
theorem exists_isDTrail_of_dConn {x y : V} (h : G.DConn {x} {y} ↑Z) :
    ∃ L, G.IsDTrail Z x y L := by
  obtain ⟨x', rfl, y', rfl, l, hl, hnd⟩ := dConn_iff_dConnPath.1 h
  obtain ⟨L, h1, h2, h3, h4⟩ := hl.exists_states
  exact ⟨L, h2, h3, h4, by simpa using hl.reflTransGen.1, h1 ▸ hnd⟩

/-- A simple active trail of minimal measure. -/
theorem exists_isDTrail_min {x y : V} (h : G.DConn {x} {y} ↑Z) :
    ∃ L, G.IsDTrail Z x y L ∧
      ∀ L', G.IsDTrail Z x y L' → G.trailMeasure Z L ≤ G.trailMeasure Z L' := by
  classical
  have hex : ∃ n, ∃ L, G.IsDTrail Z x y L ∧ G.trailMeasure Z L = n := by
    obtain ⟨L, hL⟩ := exists_isDTrail_of_dConn h
    exact ⟨_, L, hL, rfl⟩
  obtain ⟨L, hL, hn⟩ := Nat.find_spec hex
  exact ⟨L, hL, fun L' hL' => hn ▸ Nat.find_min' hex ⟨L', hL', rfl⟩⟩

/-! ### Descending and ascending along shortest paths to `Z` -/

variable (G Z) in
/-- The states `(nextZ^[1] c, true), ..., (nextZ^[k] c, true)`: a trail descending from `c`
along a shortest path to `Z`. -/
noncomputable def downList (c : V) : ℕ → List (V × Bool)
  | 0 => []
  | k + 1 => downList c k ++ [((G.nextZ Z)^[k + 1] c, true)]

variable (G Z) in
/-- The states `(nextZ^[k - 1] c, false), ..., (c, false)`: a trail ascending to `c` along a
shortest path from `c` to `Z`. -/
noncomputable def upList (c : V) : ℕ → List (V × Bool)
  | 0 => []
  | k + 1 => ((G.nextZ Z)^[k] c, false) :: upList c k

@[simp] theorem length_downList (c : V) (k : ℕ) : (G.downList Z c k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [downList, ih]

@[simp] theorem length_upList (c : V) (k : ℕ) : (G.upList Z c k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [upList, ih]

theorem mem_downList {c : V} {k : ℕ} {s : V × Bool} :
    s ∈ G.downList Z c k ↔ ∃ j, 1 ≤ j ∧ j ≤ k ∧ s = ((G.nextZ Z)^[j] c, true) := by
  induction k with
  | zero => simp [downList]
  | succ k ih =>
    simp only [downList, List.mem_append, ih, List.mem_singleton]
    constructor
    · rintro (⟨j, h1, h2, rfl⟩ | rfl)
      · exact ⟨j, h1, by omega, rfl⟩
      · exact ⟨k + 1, by omega, le_rfl, rfl⟩
    · rintro ⟨j, h1, h2, rfl⟩
      rcases Nat.lt_or_ge j (k + 1) with h | h
      · exact Or.inl ⟨j, h1, by omega, rfl⟩
      · obtain rfl : j = k + 1 := by omega
        exact Or.inr rfl

theorem mem_upList {c : V} {k : ℕ} {s : V × Bool} :
    s ∈ G.upList Z c k ↔ ∃ j, j < k ∧ s = ((G.nextZ Z)^[j] c, false) := by
  induction k with
  | zero => simp [upList]
  | succ k ih =>
    simp only [upList, List.mem_cons, ih]
    constructor
    · rintro (rfl | ⟨j, h1, rfl⟩)
      · exact ⟨k, by omega, rfl⟩
      · exact ⟨j, by omega, rfl⟩
    · rintro ⟨j, h1, rfl⟩
      rcases Nat.lt_or_ge j k with h | h
      · exact Or.inr ⟨j, h, rfl⟩
      · obtain rfl : j = k := by omega
        exact Or.inl rfl

theorem mem_map_fst_downList {c : V} {k : ℕ} {a : V} :
    a ∈ (G.downList Z c k).map Prod.fst ↔ ∃ j, 1 ≤ j ∧ j ≤ k ∧ a = (G.nextZ Z)^[j] c := by
  simp only [List.mem_map, mem_downList]
  constructor
  · rintro ⟨s, ⟨j, h1, h2, rfl⟩, rfl⟩
    exact ⟨j, h1, h2, rfl⟩
  · rintro ⟨j, h1, h2, rfl⟩
    exact ⟨_, ⟨j, h1, h2, rfl⟩, rfl⟩

theorem mem_map_fst_upList {c : V} {k : ℕ} {a : V} :
    a ∈ (G.upList Z c k).map Prod.fst ↔ ∃ j, j < k ∧ a = (G.nextZ Z)^[j] c := by
  simp only [List.mem_map, mem_upList]
  constructor
  · rintro ⟨s, ⟨j, h1, rfl⟩, rfl⟩
    exact ⟨j, h1, rfl⟩
  · rintro ⟨j, h1, rfl⟩
    exact ⟨_, ⟨j, h1, rfl⟩, rfl⟩

theorem flag_of_mem_downList {c : V} {k : ℕ} {s : V × Bool} (h : s ∈ G.downList Z c k) :
    s.2 = true := by
  obtain ⟨j, -, -, rfl⟩ := mem_downList.1 h
  rfl

theorem flag_of_mem_upList {c : V} {k : ℕ} {s : V × Bool} (h : s ∈ G.upList Z c k) :
    s.2 = false := by
  obtain ⟨j, -, rfl⟩ := mem_upList.1 h
  rfl

theorem getLast?_cons_downList (c : V) (k : ℕ) :
    ((c, true) :: G.downList Z c k).getLast? = some ((G.nextZ Z)^[k] c, true) := by
  cases k with
  | zero => rfl
  | succ k =>
    rw [downList, ← List.cons_append, List.getLast?_append]
    rfl

theorem getLast?_upList (c : V) {k : ℕ} (hk : 1 ≤ k) :
    (G.upList Z c k).getLast? = some (c, false) := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk'
    · rfl
    · rw [upList, List.getLast?_cons, ih hk']
      rfl

theorem isChain_cons_downList {c : V} (hc : c ∈ G.ancestorsOf ↑Z) {k : ℕ}
    (hk : k ≤ G.distZ Z c) : ((c, true) :: G.downList Z c k).IsChain (G.bayesBall ↑Z).Adj := by
  induction k with
  | zero => exact List.IsChain.singleton _
  | succ k ih =>
    rw [downList, ← List.cons_append]
    refine (ih (by omega)).append (List.IsChain.singleton _) ?_
    rw [getLast?_cons_downList]
    rintro a ⟨⟩ b ⟨⟩
    exact bayesBall_adj_true.2 ⟨iterate_nextZ_adj hc (by omega),
      mem_coe.not.2 (iterate_nextZ_notMem hc (by omega))⟩

theorem isChain_upList {c : V} (hc : c ∈ G.ancestorsOf ↑Z) {k : ℕ} (hk : k ≤ G.distZ Z c) :
    (G.upList Z c k).IsChain (G.bayesBall ↑Z).Adj := by
  induction k with
  | zero => exact List.IsChain.nil
  | succ k ih =>
    rw [upList]
    refine List.isChain_cons.2 ⟨fun b hb => ?_, ih (by omega)⟩
    cases k with
    | zero => simp [upList] at hb
    | succ k =>
      simp only [upList, List.head?_cons, Option.mem_def, Option.some.injEq] at hb
      subst hb
      exact bayesBall_adj_false_false.2 ⟨iterate_nextZ_adj hc (by omega),
        mem_coe.not.2 (iterate_nextZ_notMem hc (by omega))⟩

theorem nodup_map_cons_downList {c : V} (hc : c ∈ G.ancestorsOf ↑Z) {k : ℕ}
    (hk : k ≤ G.distZ Z c) : (((c, true) :: G.downList Z c k).map Prod.fst).Nodup := by
  induction k with
  | zero => simp [downList]
  | succ k ih =>
    rw [downList, ← List.cons_append, List.map_append, List.nodup_append]
    refine ⟨ih (by omega), List.nodup_singleton _, ?_⟩
    rintro a ha b hb h
    rw [List.map_singleton, List.mem_singleton] at hb
    subst hb h
    obtain ⟨s, hs, h⟩ := List.mem_map.1 ha
    dsimp only at h
    rcases List.mem_cons.1 hs with rfl | hs
    · have := iterate_nextZ_inj hc (i := 0) (j := k + 1) (by omega) hk h
      omega
    · obtain ⟨j, -, hj, rfl⟩ := mem_downList.1 hs
      have := iterate_nextZ_inj hc (i := j) (j := k + 1) (by omega) hk h
      omega

theorem nodup_map_upList {c : V} (hc : c ∈ G.ancestorsOf ↑Z) {k : ℕ}
    (hk : k ≤ G.distZ Z c) : ((G.upList Z c k).map Prod.fst).Nodup := by
  induction k with
  | zero => simp [upList]
  | succ k ih =>
    rw [upList, List.map_cons, List.nodup_cons]
    refine ⟨fun h => ?_, ih (by omega)⟩
    obtain ⟨s, hs, hseq⟩ := List.mem_map.1 h
    obtain ⟨j, hj, rfl⟩ := mem_upList.1 hs
    have := iterate_nextZ_inj hc (i := j) (j := k) (by omega) (by omega) hseq
    omega

/-! ### Surgery on trails -/

theorem bayesBall_adj_true_of {v : V} {f : Bool} {s : V × Bool}
    (h : (G.bayesBall ↑Z).Adj (v, f) s) (hv : v ∈ G.ancestorsOf ↑Z) :
    (G.bayesBall ↑Z).Adj (v, true) s := by
  obtain ⟨u, b⟩ := s
  cases b
  · cases f
    · exact bayesBall_adj_true_false.2 ⟨(bayesBall_adj_false_false.1 h).1, hv⟩
    · exact h
  · exact bayesBall_adj_true.2 (bayesBall_adj_true.1 h)

theorem head?_append_cons_eq {α : Type*} (A X Y : List α) (s : α) :
    (A ++ s :: X).head? = (A ++ s :: Y).head? := by
  cases A <;> rfl

theorem getLast?_map_fst_append_cons {P P' S : List (V × Bool)} {s s' : V × Bool}
    (h : s.1 = s'.1) :
    ((P ++ s :: S).getLast?).map Prod.fst = ((P' ++ s' :: S).getLast?).map Prod.fst := by
  simp only [List.getLast?_append, List.getLast?_cons]
  cases S.getLast? <;> simp [h]

theorem nodup_mid {P S : List V} {a : V} (h : (P ++ a :: S).Nodup) :
    a ∉ P ∧ a ∉ S ∧ ∀ b ∈ P, b ∉ S := by
  rw [List.nodup_append, List.nodup_cons] at h
  obtain ⟨-, ⟨haS, -⟩, hPS⟩ := h
  exact ⟨fun ha => hPS a ha a (List.mem_cons_self) rfl, haS,
    fun b hb hbS => hPS b hb b (List.mem_cons_of_mem _ hbS) rfl⟩

theorem isChain_append_cons_cons {R : V × Bool → V × Bool → Prop} {A B : List (V × Bool)}
    {a b : V × Bool} (h : (A ++ a :: b :: B).IsChain R) : R a b :=
  (List.isChain_cons_cons.1 (List.isChain_append.1 h).2.1).1

/-- **Shortcut through a descent that meets the trail after the collider.** If `c` is a
collider of the trail `L`, the shortest path from `c` to `Z` first meets `L` again at
`t = nextZ^[m + 1] c`, and `t` comes after `c` on `L`, then replacing the part of `L` between
`c` and `t` by that path gives a trail of smaller measure. -/
theorem IsDTrail.surgery_after {x y c w t : V} {f : Bool} {m : ℕ}
    {L A B B₁ B₂ : List (V × Bool)}
    (hL : G.IsDTrail Z x y L) (hcol : L = A ++ (c, true) :: (w, false) :: B)
    (hm : m + 1 ≤ G.distZ Z c) (ht : (G.nextZ Z)^[m + 1] c = t)
    (hfree : ∀ j, 1 ≤ j → j ≤ m → (G.nextZ Z)^[j] c ∉ L.map Prod.fst)
    (hsplit : (w, false) :: B = B₁ ++ (t, f) :: B₂) :
    ∃ L', G.IsDTrail Z x y L' ∧ G.trailMeasure Z L' < G.trailMeasure Z L := by
  have hc : c ∈ G.ancestorsOf ↑Z :=
    (bayesBall_adj_true_false.1 (isChain_append_cons_cons (hcol ▸ hL.chain))).2
  have htA : t ∈ G.ancestorsOf ↑Z := ht ▸ (iterate_nextZ hc _ hm).1
  have hdt : G.distZ Z t + (m + 1) = G.distZ Z c := ht ▸ (iterate_nextZ hc _ hm).2
  have hL' : L = A ++ (c, true) :: (B₁ ++ (t, f) :: B₂) := by rw [hcol, hsplit]
  have hch := hL.chain
  rw [hL', List.isChain_append] at hch
  obtain ⟨hchA, hch2, hJA⟩ := hch
  have hch3 := (List.isChain_append.1 (show ((c, true) :: B₁ ++ (t, f) :: B₂).IsChain _ from
    hch2)).2.1
  obtain ⟨hJt, hchB₂⟩ := List.isChain_cons.1 hch3
  refine ⟨A ++ (c, true) :: (G.downList Z c (m + 1) ++ B₂), ⟨?_, ?_, ?_, hL.last_notMem, ?_⟩, ?_⟩
  · rw [← hL.head, hL', head?_append_cons_eq]
  · rw [List.isChain_append]
    refine ⟨hchA, ?_, hJA⟩
    rw [← List.cons_append, List.isChain_append]
    refine ⟨isChain_cons_downList hc hm, hchB₂, ?_⟩
    rw [getLast?_cons_downList, ht]
    rintro a ⟨⟩ b hb
    exact bayesBall_adj_true_of (hJt b hb) htA
  · have e1 : A ++ (c, true) :: (G.downList Z c (m + 1) ++ B₂) =
        (A ++ (c, true) :: G.downList Z c m) ++ ((G.nextZ Z)^[m + 1] c, true) :: B₂ := by
      rw [downList]
      simp only [List.append_assoc, List.cons_append, List.nil_append]
    have e2 : L = (A ++ (c, true) :: B₁) ++ (t, f) :: B₂ := by
      rw [hL']
      simp only [List.append_assoc, List.cons_append]
    rw [← hL.last, e1, e2]
    exact getLast?_map_fst_append_cons ht
  · have hmemL : ∀ a, a ∈ A.map Prod.fst ∨ a ∈ B₂.map Prod.fst → a ∈ L.map Prod.fst := by
      rintro a (h | h) <;> simp [hL', h]
    have hnd := hL.nodup
    rw [hL'] at hnd
    simp only [List.map_append, List.map_cons, List.nodup_append, List.nodup_cons,
      List.mem_append, List.mem_cons] at hnd
    obtain ⟨hndA, ⟨hcB, hndB₁, ⟨htB₂, hndB₂⟩, hB₁B₂⟩, hAB⟩ := hnd
    have hD := nodup_map_cons_downList hc hm
    rw [List.map_cons, List.nodup_cons] at hD
    simp only [List.map_append, List.map_cons, List.nodup_append, List.nodup_cons,
      List.mem_append]
    refine ⟨hndA, ⟨?_, hD.2, hndB₂, ?_⟩, ?_⟩
    · rintro (h | h)
      · exact hD.1 h
      · exact hcB (Or.inr (Or.inr h))
    · intro a ha b hb hab
      subst hab
      obtain ⟨j, hj1, hj2, rfl⟩ := mem_map_fst_downList.1 ha
      rcases Nat.lt_or_ge j (m + 1) with hj | hj
      · exact hfree j hj1 (by omega) (hmemL _ (Or.inr hb))
      · obtain rfl : j = m + 1 := by omega
        exact htB₂ (ht ▸ hb)
    · intro a ha b hb hab
      subst hab
      simp only [List.mem_cons, List.mem_append] at hb
      rcases hb with rfl | hb | hb
      · exact hAB a ha a (Or.inl rfl) rfl
      · obtain ⟨j, hj1, hj2, rfl⟩ := mem_map_fst_downList.1 hb
        rcases Nat.lt_or_ge j (m + 1) with hj | hj
        · exact hfree j hj1 (by omega) (hmemL _ (Or.inl ha))
        · obtain rfl : j = m + 1 := by omega
          exact hAB _ ha _ (Or.inr (Or.inr (Or.inl ht))) rfl
      · exact hAB a ha a (Or.inr (Or.inr (Or.inr hb))) rfl
  · have e1 : (c, true) :: (G.downList Z c (m + 1) ++ B₂) =
        ((c, true) :: G.downList Z c m) ++ ((G.nextZ Z)^[m + 1] c, true) :: B₂ := by
      rw [downList]
      simp only [List.append_assoc, List.cons_append, List.nil_append]
    have h1 : G.colSum Z (A ++ (c, true) :: (G.downList Z c (m + 1) ++ B₂)) ≤
        G.colSum Z (A ++ [(c, true)]) + (G.distZ Z t + G.colSum Z B₂) := by
      rw [colSum_split A (c, true) (G.downList Z c (m + 1) ++ B₂), e1,
        colSum_split ((c, true) :: G.downList Z c m)
        ((G.nextZ Z)^[m + 1] c, true) B₂, colSum_eq_zero_of_true
          (l := ((c, true) :: G.downList Z c m) ++ [((G.nextZ Z)^[m + 1] c, true)]) ?_, zero_add]
      · have := colSum_cons_le (G := G) (Z := Z) (t, true) B₂
        rw [ht]
        exact Nat.add_le_add_left this _
      · intro s hs
        rw [List.mem_append, List.mem_cons, List.mem_singleton] at hs
        rcases hs with (rfl | hs) | rfl
        · rfl
        · exact flag_of_mem_downList hs
        · rfl
    have h2 : G.colSum Z (A ++ [(c, true)]) + (G.distZ Z c + G.colSum Z B₂) ≤ G.colSum Z L := by
      rw [hcol, colSum_split A (c, true) ((w, false) :: B), colSum_cons_cons, hsplit]
      simp only [and_self, ite_true]
      have := colSum_le_append (G := G) (Z := Z) B₁ ((t, f) :: B₂)
      have := colSum_le_cons (G := G) (Z := Z) (t, f) B₂
      omega
    have h3 : L.length = A.length + B₁.length + B₂.length + 2 := by
      rw [hL']
      simp only [List.length_append, List.length_cons]
      omega
    unfold trailMeasure
    simp only [List.length_append, List.length_cons, length_downList]
    omega

/-- **Shortcut through a descent that meets the trail before the collider.** If `c` is a
collider of the trail `L`, the shortest path from `c` to `Z` first meets `L` again at
`t = nextZ^[m + 1] c`, and `t` comes before `c` on `L`, then replacing the part of `L` between
`t` and `c` by that path, traversed upward, gives a trail of smaller measure. -/
theorem IsDTrail.surgery_before {x y c w t : V} {f : Bool} {m : ℕ}
    {L A₁ A₂ B : List (V × Bool)}
    (hL : G.IsDTrail Z x y L)
    (hcol : L = A₁ ++ (t, f) :: (A₂ ++ (c, true) :: (w, false) :: B))
    (hm : m + 1 ≤ G.distZ Z c) (ht : (G.nextZ Z)^[m + 1] c = t)
    (hfree : ∀ j, 1 ≤ j → j ≤ m → (G.nextZ Z)^[j] c ∉ L.map Prod.fst) :
    ∃ L', G.IsDTrail Z x y L' ∧ G.trailMeasure Z L' < G.trailMeasure Z L := by
  have hcw : (G.bayesBall ↑Z).Adj (c, true) (w, false) := by
    refine isChain_append_cons_cons (A := A₁ ++ (t, f) :: A₂) (B := B) ?_
    simpa [hcol] using hL.chain
  have hc : c ∈ G.ancestorsOf ↑Z := (bayesBall_adj_true_false.1 hcw).2
  have hcZ : c ∉ Z := iterate_nextZ_notMem (j := 0) hc (by omega)
  have htA : t ∈ G.ancestorsOf ↑Z := ht ▸ (iterate_nextZ hc _ hm).1
  have hdt : G.distZ Z t + (m + 1) = G.distZ Z c := ht ▸ (iterate_nextZ hc _ hm).2
  have hch := hL.chain
  rw [hcol, List.isChain_append] at hch
  obtain ⟨hchA, hch2, hJA⟩ := hch
  obtain ⟨hJt, hch3⟩ := List.isChain_cons.1 hch2
  have hchWB : ((w, false) :: B).IsChain (G.bayesBall ↑Z).Adj := by
    have := (List.isChain_append.1 (show (A₂ ++ (c, true) :: (w, false) :: B).IsChain _ from
      hch3)).2.1
    exact (List.isChain_cons.1 this).2
  have htZ : f = false → t ∉ Z := by
    rintro rfl
    obtain ⟨s, hs⟩ : ∃ s, s ∈ (A₂ ++ (c, true) :: (w, false) :: B).head? := by
      cases A₂ <;> simp
    exact mem_coe.not.1 (notMem_of_bayesBall_adj_false (hJt s hs))
  refine ⟨A₁ ++ (t, f) :: (G.upList Z c (m + 1) ++ (w, false) :: B),
    ⟨?_, ?_, ?_, hL.last_notMem, ?_⟩, ?_⟩
  · rw [← hL.head, hcol, head?_append_cons_eq]
  · rw [List.isChain_append]
    refine ⟨hchA, ?_, hJA⟩
    refine List.isChain_cons.2 ⟨?_, ?_⟩
    · rintro b hb
      simp only [upList, List.cons_append, List.head?_cons, Option.mem_def,
        Option.some.injEq] at hb
      subst hb
      have hadj := iterate_nextZ_adj hc (j := m) (by omega)
      rw [ht] at hadj
      cases f
      · exact bayesBall_adj_false_false.2 ⟨hadj, mem_coe.not.2 (htZ rfl)⟩
      · exact bayesBall_adj_true_false.2 ⟨hadj, htA⟩
    · refine (isChain_upList hc hm).append hchWB ?_
      rw [getLast?_upList c (by omega)]
      rintro a ⟨⟩ b ⟨⟩
      exact bayesBall_adj_false_false.2 ⟨(bayesBall_adj_true_false.1 hcw).1, mem_coe.not.2 hcZ⟩
  · have e1 : A₁ ++ (t, f) :: (G.upList Z c (m + 1) ++ (w, false) :: B) =
        (A₁ ++ (t, f) :: G.upList Z c (m + 1)) ++ (w, false) :: B := by
      simp only [List.append_assoc, List.cons_append]
    have e2 : L = (A₁ ++ (t, f) :: (A₂ ++ [(c, true)])) ++ (w, false) :: B := by
      rw [hcol]
      simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [← hL.last, e1, e2]
    exact getLast?_map_fst_append_cons rfl
  · have hmemL : ∀ a, a ∈ A₁.map Prod.fst ∨ a ∈ B.map Prod.fst → a ∈ L.map Prod.fst := by
      rintro a (h | h) <;> simp [hcol, h]
    have hnd := hL.nodup
    rw [hcol] at hnd
    simp only [List.map_append, List.map_cons, List.nodup_append, List.nodup_cons,
      List.mem_append, List.mem_cons] at hnd
    obtain ⟨hndA, ⟨htrest, hndA₂, ⟨hcrest, hwB, hndB⟩, hA₂rest⟩, hArest⟩ := hnd
    have hU := nodup_map_upList hc hm
    have htU : t ∉ (G.upList Z c (m + 1)).map Prod.fst := fun h => by
      obtain ⟨j, hj, hj'⟩ := mem_map_fst_upList.1 h
      rw [← ht] at hj'
      have := iterate_nextZ_inj hc (i := m + 1) (j := j) hm (by omega) hj'
      omega
    have hUL : ∀ a ∈ (G.upList Z c (m + 1)).map Prod.fst, a = c ∨ a ∉ L.map Prod.fst := by
      intro a ha
      obtain ⟨j, hj, rfl⟩ := mem_map_fst_upList.1 ha
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · exact Or.inl rfl
      · exact Or.inr (hfree j hj0 (by omega))
    simp only [List.map_append, List.map_cons, List.nodup_append, List.nodup_cons,
      List.mem_append, List.mem_cons]
    refine ⟨hndA, ⟨?_, ⟨hU, ⟨hwB, hndB⟩, ?_⟩⟩, ?_⟩
    · rintro (h | rfl | h)
      · exact htU h
      · exact htrest (Or.inr (Or.inr (Or.inl rfl)))
      · exact htrest (Or.inr (Or.inr (Or.inr h)))
    · intro a ha b hb hab
      subst hab
      rcases hUL a ha with rfl | ha'
      · rcases hb with rfl | hb
        · exact hcrest (Or.inl rfl)
        · exact hcrest (Or.inr hb)
      · rcases hb with rfl | hb
        · exact ha' (by simp [hcol])
        · exact ha' (hmemL _ (Or.inr hb))
    · intro a ha b hb hab
      subst hab
      rcases hb with rfl | hb | rfl | hb
      · exact hArest a ha a (Or.inl rfl) rfl
      · rcases hUL a hb with rfl | ha'
        · exact hArest a ha a (Or.inr (Or.inr (Or.inl rfl))) rfl
        · exact ha' (hmemL _ (Or.inl ha))
      · exact hArest a ha a (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) rfl
      · exact hArest a ha a (Or.inr (Or.inr (Or.inr (Or.inr hb)))) rfl
  · have h1 : G.colSum Z (A₁ ++ (t, f) :: (G.upList Z c (m + 1) ++ (w, false) :: B)) ≤
        G.colSum Z (A₁ ++ [(t, f)]) + (G.distZ Z t + G.colSum Z ((w, false) :: B)) := by
      rw [colSum_split A₁ (t, f) (G.upList Z c (m + 1) ++ (w, false) :: B), ← List.cons_append,
        colSum_split ((t, f) :: G.upList Z c (m + 1)) (w, false) B]
      have := colSum_cons_le (G := G) (Z := Z) (t, f) (G.upList Z c (m + 1) ++ [(w, false)])
      rw [colSum_append_singleton_eq_zero_of_false (fun s hs => flag_of_mem_upList hs)] at this
      rw [List.cons_append]
      dsimp only at this
      omega
    have h2 : G.colSum Z (A₁ ++ [(t, f)]) + (G.distZ Z c + G.colSum Z ((w, false) :: B)) ≤
        G.colSum Z L := by
      rw [hcol, colSum_split A₁ (t, f) (A₂ ++ (c, true) :: (w, false) :: B)]
      have := colSum_le_append (G := G) (Z := Z) ((t, f) :: A₂) ((c, true) :: (w, false) :: B)
      rw [colSum_cons_cons] at this
      simp only [and_self, ite_true, List.cons_append] at this
      omega
    have h3 : L.length = A₁.length + A₂.length + B.length + 3 := by
      rw [hcol]
      simp only [List.length_append, List.length_cons]
      omega
    unfold trailMeasure
    simp only [List.length_append, List.length_cons, length_upList]
    omega

/-- **Shortcut through two descents that meet.** If `c` and a later `c'` are colliders of the
trail `L` whose shortest paths to `Z` avoid `L` (apart from `c` and `c'`) and first meet at
`nextZ^[m + 1] c = nextZ^[m' + 1] c'`, then going down from `c` to the meeting vertex and up to
`c'` gives a trail of smaller measure. -/
theorem IsDTrail.surgery_merge {x y c w c' w' : V} {m m' : ℕ}
    {L A M B : List (V × Bool)}
    (hL : G.IsDTrail Z x y L)
    (hcol : L = A ++ (c, true) :: (w, false) :: (M ++ (c', true) :: (w', false) :: B))
    (hm : m + 1 ≤ G.distZ Z c) (hm' : m' + 1 ≤ G.distZ Z c')
    (hv : (G.nextZ Z)^[m + 1] c = (G.nextZ Z)^[m' + 1] c')
    (hfree : ∀ j, 1 ≤ j → j ≤ m + 1 → (G.nextZ Z)^[j] c ∉ L.map Prod.fst)
    (hfree' : ∀ j, 1 ≤ j → j ≤ m' → (G.nextZ Z)^[j] c' ∉ L.map Prod.fst)
    (hdisj : ∀ j, j ≤ m → ∀ j', j' ≤ G.distZ Z c' → (G.nextZ Z)^[j] c ≠ (G.nextZ Z)^[j'] c') :
    ∃ L', G.IsDTrail Z x y L' ∧ G.trailMeasure Z L' < G.trailMeasure Z L := by
  have hcw : (G.bayesBall ↑Z).Adj (c, true) (w, false) :=
    isChain_append_cons_cons (hcol ▸ hL.chain)
  have hcw' : (G.bayesBall ↑Z).Adj (c', true) (w', false) := by
    refine isChain_append_cons_cons (A := A ++ (c, true) :: (w, false) :: M) (B := B) ?_
    simpa [hcol] using hL.chain
  have hc : c ∈ G.ancestorsOf ↑Z := (bayesBall_adj_true_false.1 hcw).2
  have hc' : c' ∈ G.ancestorsOf ↑Z := (bayesBall_adj_true_false.1 hcw').2
  have hcZ' : c' ∉ Z := iterate_nextZ_notMem (j := 0) hc' (by omega)
  have hvA : (G.nextZ Z)^[m + 1] c ∈ G.ancestorsOf ↑Z := (iterate_nextZ hc _ hm).1
  have hdv : G.distZ Z ((G.nextZ Z)^[m + 1] c) + (m + 1) = G.distZ Z c :=
    (iterate_nextZ hc _ hm).2
  have hdv' : G.distZ Z ((G.nextZ Z)^[m + 1] c) + (m' + 1) = G.distZ Z c' :=
    hv ▸ (iterate_nextZ hc' _ hm').2
  have hch := hL.chain
  rw [hcol, List.isChain_append] at hch
  obtain ⟨hchA, -, hJA⟩ := hch
  have hchWB : ((w', false) :: B).IsChain (G.bayesBall ↑Z).Adj := by
    have h := hL.chain
    rw [show L = (A ++ (c, true) :: (w, false) :: M ++ [(c', true)]) ++ (w', false) :: B by
      rw [hcol]; simp] at h
    exact (List.isChain_append.1 h).2.1
  have e0 : (c, true) :: (G.downList Z c (m + 1) ++ (G.upList Z c' (m' + 1) ++ (w', false) :: B))
      = ((c, true) :: G.downList Z c m) ++ ((G.nextZ Z)^[m + 1] c, true) ::
        (G.upList Z c' (m' + 1) ++ (w', false) :: B) := by
    rw [downList]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine ⟨A ++ (c, true) :: (G.downList Z c (m + 1) ++ (G.upList Z c' (m' + 1) ++
    (w', false) :: B)), ⟨?_, ?_, ?_, hL.last_notMem, ?_⟩, ?_⟩
  · rw [← hL.head, hcol, head?_append_cons_eq]
  · rw [List.isChain_append]
    refine ⟨hchA, ?_, by simpa using hJA⟩
    rw [← List.cons_append, List.isChain_append]
    refine ⟨isChain_cons_downList hc hm, ?_, ?_⟩
    · refine (isChain_upList hc' hm').append hchWB ?_
      rw [getLast?_upList c' (by omega)]
      rintro a ⟨⟩ b ⟨⟩
      exact bayesBall_adj_false_false.2 ⟨(bayesBall_adj_true_false.1 hcw').1, mem_coe.not.2 hcZ'⟩
    · rw [getLast?_cons_downList]
      rintro a ⟨⟩ b hb
      simp only [upList, List.cons_append, List.head?_cons, Option.mem_def,
        Option.some.injEq] at hb
      subst hb
      have hadj := iterate_nextZ_adj hc' (j := m') (by omega)
      rw [← hv] at hadj
      exact bayesBall_adj_true_false.2 ⟨hadj, hvA⟩
  · have e1 : A ++ (c, true) :: (G.downList Z c (m + 1) ++ (G.upList Z c' (m' + 1) ++
        (w', false) :: B)) = (A ++ (c, true) :: (G.downList Z c (m + 1) ++
          G.upList Z c' (m' + 1))) ++ (w', false) :: B := by
      simp only [List.append_assoc, List.cons_append]
    have e2 : L = (A ++ (c, true) :: (w, false) :: (M ++ [(c', true)])) ++ (w', false) :: B := by
      rw [hcol]
      simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [← hL.last, e1, e2]
    exact getLast?_map_fst_append_cons rfl
  · have hnd := hL.nodup
    have hmemL : ∀ a, a ∈ A.map Prod.fst ∨ a ∈ B.map Prod.fst → a ∈ L.map Prod.fst := by
      rintro a (h | h) <;> simp [hcol, h]
    have hsc := nodup_mid (P := A.map Prod.fst) (a := c)
      (S := w :: (M.map Prod.fst ++ c' :: w' :: B.map Prod.fst)) (by simpa [hcol] using hnd)
    have hsc' := nodup_mid (P := A.map Prod.fst ++ c :: w :: M.map Prod.fst) (a := c')
      (S := w' :: B.map Prod.fst) (by simpa [hcol] using hnd)
    have hndA : (A.map Prod.fst).Nodup := by
      rw [hcol, List.map_append] at hnd
      exact (List.nodup_append.1 hnd).1
    have hndWB : (w' :: B.map Prod.fst).Nodup := by
      rw [show L = (A ++ (c, true) :: (w, false) :: M ++ [(c', true)]) ++ (w', false) :: B by
        rw [hcol]; simp, List.map_append] at hnd
      simpa using (List.nodup_append.1 hnd).2.1
    have hD := nodup_map_cons_downList hc hm
    rw [List.map_cons, List.nodup_cons] at hD
    have hU := nodup_map_upList hc' hm'
    have hDL : ∀ a ∈ (G.downList Z c (m + 1)).map Prod.fst, a ∉ L.map Prod.fst := by
      intro a ha
      obtain ⟨j, hj1, hj2, rfl⟩ := mem_map_fst_downList.1 ha
      exact hfree j hj1 hj2
    have hUL : ∀ a ∈ (G.upList Z c' (m' + 1)).map Prod.fst, a = c' ∨ a ∉ L.map Prod.fst := by
      intro a ha
      obtain ⟨j, hj, rfl⟩ := mem_map_fst_upList.1 ha
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · exact Or.inl rfl
      · exact Or.inr (hfree' j hj0 (by omega))
    have hcL : c ∈ L.map Prod.fst := by simp [hcol]
    have hc'L : c' ∈ L.map Prod.fst := by simp [hcol]
    have hw'L : w' ∈ L.map Prod.fst := by simp [hcol]
    have hcc' : c ≠ c' := fun h => hsc.2.1 (by simp [h])
    simp only [List.map_append, List.map_cons]
    refine List.nodup_append.2 ⟨hndA, List.nodup_cons.2 ⟨?_, List.nodup_append.2 ⟨hD.2,
      List.nodup_append.2 ⟨hU, hndWB, ?_⟩, ?_⟩⟩, ?_⟩
    · intro h
      rcases List.mem_append.1 h with h | h
      · exact hD.1 h
      rcases List.mem_append.1 h with h | h
      · rcases hUL c h with h | h
        · exact hcc' h
        · exact h hcL
      · exact hsc.2.1 (by simp only [List.mem_cons, List.mem_append] at h ⊢; tauto)
    · intro a ha b hb hab
      subst hab
      rcases hUL a ha with rfl | ha'
      · exact hsc'.2.1 hb
      · rcases List.mem_cons.1 hb with rfl | hb
        · exact ha' hw'L
        · exact ha' (hmemL _ (Or.inr hb))
    · intro a ha b hb hab
      subst hab
      have haL := hDL a ha
      rcases List.mem_append.1 hb with hb | hb
      · obtain ⟨j, hj1, hj2, hj⟩ := mem_map_fst_downList.1 ha
        obtain ⟨j', hj', hj'eq⟩ := mem_map_fst_upList.1 hb
        rw [hj] at hj'eq
        rcases Nat.lt_or_ge j (m + 1) with hjm | hjm
        · exact hdisj j (by omega) j' (by omega) hj'eq
        · obtain rfl : j = m + 1 := by omega
          rw [hv] at hj'eq
          have := iterate_nextZ_inj hc' (i := m' + 1) (j := j') hm' (by omega) hj'eq
          omega
      · rcases List.mem_cons.1 hb with rfl | hb
        · exact haL hw'L
        · exact haL (hmemL _ (Or.inr hb))
    · intro a ha b hb hab
      subst hab
      have haL := hmemL a (Or.inl ha)
      rcases List.mem_cons.1 hb with rfl | hb
      · exact hsc.1 ha
      rcases List.mem_append.1 hb with hb | hb
      · exact hDL a hb haL
      rcases List.mem_append.1 hb with hb | hb
      · rcases hUL a hb with rfl | ha'
        · exact hsc'.1 (List.mem_append_left _ ha)
        · exact ha' haL
      · exact hsc.2.2 a ha (by simp only [List.mem_cons, List.mem_append] at hb ⊢; tauto)
  · have h1 : G.colSum Z (A ++ (c, true) :: (G.downList Z c (m + 1) ++
        (G.upList Z c' (m' + 1) ++ (w', false) :: B))) ≤ G.colSum Z (A ++ [(c, true)]) +
          (G.distZ Z ((G.nextZ Z)^[m + 1] c) + G.colSum Z ((w', false) :: B)) := by
      rw [colSum_split A (c, true), e0, colSum_split ((c, true) :: G.downList Z c m)
        ((G.nextZ Z)^[m + 1] c, true), colSum_eq_zero_of_true
          (l := ((c, true) :: G.downList Z c m) ++ [((G.nextZ Z)^[m + 1] c, true)]) ?_, zero_add]
      · have := colSum_cons_le (G := G) (Z := Z) ((G.nextZ Z)^[m + 1] c, true)
          (G.upList Z c' (m' + 1) ++ (w', false) :: B)
        rw [colSum_split (G.upList Z c' (m' + 1)) (w', false) B,
          colSum_append_singleton_eq_zero_of_false (fun s hs => flag_of_mem_upList hs)] at this
        dsimp only at this
        omega
      · intro s hs
        rw [List.mem_append, List.mem_cons, List.mem_singleton] at hs
        rcases hs with (rfl | hs) | rfl
        · rfl
        · exact flag_of_mem_downList hs
        · rfl
    have h2 : G.colSum Z (A ++ [(c, true)]) + (G.distZ Z c + (G.distZ Z c' +
        G.colSum Z ((w', false) :: B))) ≤ G.colSum Z L := by
      rw [hcol, colSum_split A (c, true) ((w, false) :: (M ++ (c', true) :: (w', false) :: B)),
        colSum_cons_cons]
      have := colSum_le_append (G := G) (Z := Z) ((w, false) :: M)
        ((c', true) :: (w', false) :: B)
      rw [colSum_cons_cons] at this
      simp only [and_self, ite_true, List.cons_append] at this ⊢
      omega
    have h3 : L.length = A.length + M.length + B.length + 4 := by
      rw [hcol]
      simp only [List.length_append, List.length_cons]
      omega
    unfold trailMeasure
    simp only [List.length_append, List.length_cons, length_upList, length_downList]
    omega

/-! ### Consequences of minimality -/

/-- In a trail of minimal measure, the shortest path from a collider to `Z` meets the trail only
at the collider. -/
theorem IsDTrail.iterate_nextZ_notMem_of_min {x y c w : V} {L A B : List (V × Bool)}
    (hL : G.IsDTrail Z x y L)
    (hmin : ∀ L', G.IsDTrail Z x y L' → G.trailMeasure Z L ≤ G.trailMeasure Z L')
    (hcol : L = A ++ (c, true) :: (w, false) :: B) {j : ℕ} (hj1 : 1 ≤ j)
    (hj : j ≤ G.distZ Z c) : (G.nextZ Z)^[j] c ∉ L.map Prod.fst := by
  classical
  intro hmem
  have hc : c ∈ G.ancestorsOf ↑Z :=
    (bayesBall_adj_true_false.1 (isChain_append_cons_cons (hcol ▸ hL.chain))).2
  have hex : ∃ k, 1 ≤ k ∧ k ≤ G.distZ Z c ∧ (G.nextZ Z)^[k] c ∈ L.map Prod.fst :=
    ⟨j, hj1, hj, hmem⟩
  obtain ⟨hk1, hk, hkmem⟩ := Nat.find_spec hex
  obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 1 := ⟨Nat.find hex - 1, by omega⟩
  rw [hm] at hk hkmem
  have hfree : ∀ i, 1 ≤ i → i ≤ m → (G.nextZ Z)^[i] c ∉ L.map Prod.fst := fun i hi1 hi him =>
    Nat.find_min hex (by omega) ⟨hi1, by omega, him⟩
  have htc : (G.nextZ Z)^[m + 1] c ≠ c := fun h => by
    have := iterate_nextZ_inj hc (i := m + 1) (j := 0) hk (by omega) h
    omega
  obtain ⟨s, hs, hst⟩ := List.mem_map.1 hkmem
  obtain ⟨u, f⟩ := s
  dsimp only at hst
  subst hst
  rw [hcol] at hs
  rcases List.mem_append.1 hs with hs | hs
  · obtain ⟨A₁, A₂, rfl⟩ := List.append_of_mem hs
    obtain ⟨L', hL', hlt⟩ := hL.surgery_before (A₁ := A₁) (A₂ := A₂) (B := B) (w := w) (f := f)
      (by rw [hcol]; simp) hk rfl hfree
    exact absurd (hmin L' hL') (not_le.2 hlt)
  rcases List.mem_cons.1 hs with hs | hs
  · exact htc (Prod.mk.inj hs).1
  · obtain ⟨B₁, B₂, hsplit⟩ := List.append_of_mem hs
    obtain ⟨L', hL', hlt⟩ := hL.surgery_after hcol hk rfl hfree hsplit
    exact absurd (hmin L' hL') (not_le.2 hlt)

/-- In a trail of minimal measure, the shortest paths from two colliders to `Z` are disjoint. -/
theorem IsDTrail.iterate_nextZ_ne_of_min {x y c w c' w' : V} {L A M B : List (V × Bool)}
    (hL : G.IsDTrail Z x y L)
    (hmin : ∀ L', G.IsDTrail Z x y L' → G.trailMeasure Z L ≤ G.trailMeasure Z L')
    (hcol : L = A ++ (c, true) :: (w, false) :: (M ++ (c', true) :: (w', false) :: B))
    {j j' : ℕ} (hj : j ≤ G.distZ Z c) (hj' : j' ≤ G.distZ Z c') :
    (G.nextZ Z)^[j] c ≠ (G.nextZ Z)^[j'] c' := by
  classical
  intro heq
  have hcol' : L = (A ++ (c, true) :: (w, false) :: M) ++ (c', true) :: (w', false) :: B := by
    rw [hcol]; simp
  have hc : c ∈ G.ancestorsOf ↑Z :=
    (bayesBall_adj_true_false.1 (isChain_append_cons_cons (hcol ▸ hL.chain))).2
  have hc' : c' ∈ G.ancestorsOf ↑Z :=
    (bayesBall_adj_true_false.1 (isChain_append_cons_cons (hcol' ▸ hL.chain))).2
  have N := fun {i} => hL.iterate_nextZ_notMem_of_min hmin hcol (j := i)
  have N' := fun {i} => hL.iterate_nextZ_notMem_of_min hmin hcol' (j := i)
  have hcL : c ∈ L.map Prod.fst := by simp [hcol]
  have hc'L : c' ∈ L.map Prod.fst := by simp [hcol]
  have hcc' : c ≠ c' := by
    intro h
    have hnd := hL.nodup
    rw [hcol] at hnd
    have := (nodup_mid (P := A.map Prod.fst) (a := c)
      (S := w :: (M.map Prod.fst ++ c' :: w' :: B.map Prod.fst)) (by simpa using hnd)).2.1
    exact this (by simp [h])
  have hex : ∃ k, k ≤ G.distZ Z c ∧ ∃ k', k' ≤ G.distZ Z c' ∧
      (G.nextZ Z)^[k] c = (G.nextZ Z)^[k'] c' := ⟨j, hj, j', hj', heq⟩
  obtain ⟨hk, k', hk', hkk'⟩ := Nat.find_spec hex
  have hmin' : ∀ i, i < Nat.find hex → ∀ i', i' ≤ G.distZ Z c' →
      (G.nextZ Z)^[i] c ≠ (G.nextZ Z)^[i'] c' := fun i hi i' hi' h =>
    Nat.find_min hex hi ⟨by omega, i', hi', h⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0] at hkk'
    rcases Nat.eq_zero_or_pos k' with rfl | hk'0
    · exact hcc' hkk'
    · exact N' hk'0 hk' (hkk' ▸ hcL)
  rcases Nat.eq_zero_or_pos k' with rfl | hk'0
  · exact N hpos hk (hkk' ▸ hc'L)
  obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 1 := ⟨Nat.find hex - 1, by omega⟩
  obtain ⟨m', rfl⟩ : ∃ m', k' = m' + 1 := ⟨k' - 1, by omega⟩
  rw [hm] at hk hkk'
  obtain ⟨L', hL', hlt⟩ := hL.surgery_merge hcol hk hk' hkk'
    (fun i hi1 hi => N hi1 (by omega)) (fun i hi1 hi => N' hi1 (by omega))
    (fun i hi i' hi' => hmin' i (by omega) i' hi')
  exact absurd (hmin L' hL') (not_le.2 hlt)

theorem eq_of_append_cons_eq_append_cons : ∀ {P P' S S' : List (V × Bool)} {s s' : V × Bool},
    ((P ++ s :: S).map Prod.fst).Nodup → P ++ s :: S = P' ++ s' :: S' → s.1 = s'.1 →
      P = P' ∧ s = s' ∧ S = S'
  | [], [], _, _, _, _, _, h, _ => by
    simp only [List.nil_append, List.cons.injEq] at h
    exact ⟨rfl, h⟩
  | [], b :: P', S, S', s, s', hnd, h, hss' => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [List.nil_append, List.map_cons, List.nodup_cons] at hnd
    exact absurd (by simp [hss']) hnd.1
  | a :: P, [], S, S', s, s', hnd, h, hss' => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [List.cons_append, List.map_cons, List.nodup_cons] at hnd
    exact absurd (by simp [← hss']) hnd.1
  | a :: P, b :: P', S, S', s, s', hnd, h, hss' => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    simp only [List.cons_append, List.map_cons, List.nodup_cons] at hnd
    obtain ⟨h1, h2, h3⟩ := eq_of_append_cons_eq_append_cons hnd.2 h hss'
    exact ⟨by rw [h1], h2, h3⟩

/-- `IsCollider L c`: the vertex `c` is a collider of the trail `L`. -/
def IsCollider (L : List (V × Bool)) (c : V) : Prop :=
  ∃ A w B, L = A ++ (c, true) :: (w, false) :: B

theorem IsDTrail.mem_ancestorsOf_of_isCollider {x y c : V} {L : List (V × Bool)}
    (hL : G.IsDTrail Z x y L) (hc : IsCollider L c) : c ∈ G.ancestorsOf ↑Z := by
  obtain ⟨A, w, B, hcol⟩ := hc
  exact (bayesBall_adj_true_false.1 (isChain_append_cons_cons (hcol ▸ hL.chain))).2

/-- In a trail of minimal measure, the shortest paths to `Z` from two distinct colliders are
disjoint. -/
theorem IsDTrail.iterate_nextZ_ne_of_min' {x y c c₂ : V} {L : List (V × Bool)}
    (hL : G.IsDTrail Z x y L)
    (hmin : ∀ L', G.IsDTrail Z x y L' → G.trailMeasure Z L ≤ G.trailMeasure Z L')
    (hc : IsCollider L c) (hc₂ : IsCollider L c₂) (hne : c ≠ c₂) {j j₂ : ℕ}
    (hj : j ≤ G.distZ Z c) (hj₂ : j₂ ≤ G.distZ Z c₂) :
    (G.nextZ Z)^[j] c ≠ (G.nextZ Z)^[j₂] c₂ := by
  obtain ⟨A, w, B, hcol⟩ := hc
  obtain ⟨A₂, w₂, B₂, hcol₂⟩ := hc₂
  have hnd := hL.nodup
  have hmem : c₂ ∈ L.map Prod.fst := by simp [hcol₂]
  rw [hcol] at hmem
  obtain ⟨s, hs, hsc⟩ := List.mem_map.1 hmem
  rcases List.mem_append.1 hs with hs | hs
  · obtain ⟨A₀, S₀, rfl⟩ := List.append_of_mem hs
    have heq : A₀ ++ s :: (S₀ ++ (c, true) :: (w, false) :: B) =
        A₂ ++ (c₂, true) :: (w₂, false) :: B₂ := by rw [← hcol₂, hcol]; simp
    obtain ⟨-, rfl, hS⟩ := eq_of_append_cons_eq_append_cons (by rw [heq, ← hcol₂]; exact hnd)
      heq hsc
    rcases S₀ with _ | ⟨m, M⟩
    · simp at hS
    simp only [List.cons_append, List.cons.injEq] at hS
    obtain ⟨rfl, rfl⟩ := hS
    exact (hL.iterate_nextZ_ne_of_min (A := A₀) (M := M) (B := B) (w := w₂) (w' := w) hmin
      (by rw [hcol]; simp) hj₂ hj).symm
  rcases List.mem_cons.1 hs with rfl | hs
  · exact absurd (by simpa using hsc) hne
  obtain ⟨M₀, S, hsplit⟩ := List.append_of_mem hs
  have heq : (A ++ (c, true) :: M₀) ++ s :: S = A₂ ++ (c₂, true) :: (w₂, false) :: B₂ := by
    rw [← hcol₂, hcol, hsplit]; simp
  obtain ⟨-, rfl, rfl⟩ := eq_of_append_cons_eq_append_cons (by rw [heq, ← hcol₂]; exact hnd)
    heq hsc
  rcases M₀ with _ | ⟨m, M⟩
  · simp at hsplit
  simp only [List.cons_append, List.cons.injEq] at hsplit
  obtain ⟨rfl, rfl⟩ := hsplit
  exact hL.iterate_nextZ_ne_of_min hmin hcol hj hj₂

end Trail

section Rule

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]

/-- A local rule for Boolean variables on `G`: `F v x e` is the value of `v` when the other
vertices take the values `x` and the noise bit of `v` is `e`, and it depends on `x` only
through the parents of `v`. The rule maps the all-false configuration with a false noise bit to
false. -/
structure BoolRule (G : Digraph V) where
  /-- The value of `v` given the values `x` of the other vertices and the noise bit `e`. -/
  F : V → (V → Bool) → Bool → Bool
  /-- The rule of `v` reads only the parents of `v`. -/
  congr : ∀ v x x' e, (∀ u, G.Adj u v → x u = x' u) → F v x e = F v x' e
  /-- All-false inputs give a false value. -/
  F_false : ∀ v, F v (fun _ => false) false = false

namespace BoolRule

variable (R : G.BoolRule)

/-- `R.Sol n σ`: the configuration `σ` solves the equations of the rule at the noise value
`n`. -/
def Sol (n σ : V → Bool) : Prop := ∀ v, σ v = R.F v σ (n v)

/-- The structural causal model of a rule on an acyclic graph, with independent fair noise
bits. -/
noncomputable def toSCM (hG : G.IsAcyclic) : SCM G (fun _ => Bool) (fun _ => Bool) where
  acyclic := hG
  f v z e := R.F v (fun u => if h : u ∈ G.parentsFinset v then z ⟨u, h⟩ else false) e
  noise _ := FiniteDist.uniform

theorem isSolution_iff (hG : G.IsAcyclic) (n σ : V → Bool) :
    (R.toSCM hG).IsSolution n σ ↔ R.Sol n σ := by
  refine forall_congr' fun v => ?_
  refine Eq.congr_right (R.congr v _ _ _ fun u hu => ?_)
  simp [Finset.restrict, mem_parentsFinset.2 hu]

theorem sol_solve (hG : G.IsAcyclic) (n : V → Bool) : R.Sol n ((R.toSCM hG).solve n) :=
  (R.isSolution_iff hG _ _).1 ((R.toSCM hG).isSolution_solve n)

theorem solve_false (hG : G.IsAcyclic) :
    (R.toSCM hG).solve (fun _ => false) = fun _ => false :=
  ((R.toSCM hG).eq_solve_of_isSolution
    ((R.isSolution_iff hG _ _).2 fun v => (R.F_false v).symm)).symm

theorem noiseDist_pos (hG : G.IsAcyclic) (n : V → Bool) : 0 < (R.toSCM hG).noiseDist n := by
  refine prod_pos fun v _ => ?_
  change 0 < (FiniteDist.uniform : FiniteDist Bool) (n v)
  rw [FiniteDist.uniform_apply]
  norm_num

/-- **A criterion for conditional dependence.** Suppose that in every solution of the rule in
which all vertices of `Z` are false, the values at `x` and at `y` agree, and that some noise
value yields a solution with `x` true and all of `Z` false. Then in the distribution of the
model, `{x}` and `{y}` are not conditionally independent given `Z`. -/
theorem not_condIndep (hG : G.IsAcyclic) {x y : V} {Z : Finset V}
    (ha : ∀ n σ, R.Sol n σ → (∀ z ∈ Z, σ z = false) → σ x = σ y)
    (hb : ∃ n, ∀ σ, R.Sol n σ → σ x = true ∧ ∀ z ∈ Z, σ z = false) :
    ¬ (R.toSCM hG).dist.CondIndep {x} {y} Z := by
  intro h
  set M := R.toSCM hG
  have key := h (fun _ => true) (fun _ => false) (fun _ => false)
  simp only [SCM.probOf_dist] at key
  have e1 : ∀ (S : Finset V) (b : Bool) (ω : V → Bool),
      S.restrict ω = (fun _ => b) ↔ ∀ v ∈ S, ω v = b := fun S b ω =>
    ⟨fun h v hv => congrFun h ⟨v, hv⟩, fun h => funext fun v => h v v.2⟩
  simp only [e1, mem_singleton, forall_eq] at key
  have h0 : M.noiseDist.probOf (fun n => M.solve n x = true ∧ M.solve n y = false ∧
      ∀ v ∈ Z, M.solve n v = false) = 0 := by
    refine M.noiseDist.probOf_eq_zero fun n ⟨h1, h2, h3⟩ => ?_
    have := ha n _ (R.sol_solve hG n) h3
    rw [h1, h2] at this
    exact Bool.noConfusion this
  obtain ⟨n₁, hn₁⟩ := hb
  obtain ⟨hx₁, hz₁⟩ := hn₁ _ (R.sol_solve hG n₁)
  have hX : 0 < M.noiseDist.probOf (fun n => M.solve n x = true ∧
      ∀ v ∈ Z, M.solve n v = false) :=
    (R.noiseDist_pos hG n₁).trans_le (M.noiseDist.le_probOf n₁ ⟨hx₁, hz₁⟩)
  have hY : 0 < M.noiseDist.probOf (fun n => M.solve n y = false ∧
      ∀ v ∈ Z, M.solve n v = false) := by
    refine (R.noiseDist_pos hG (fun _ => false)).trans_le (M.noiseDist.le_probOf _ ?_)
    simp [M, R.solve_false hG]
  rw [h0, zero_mul] at key
  exact (mul_pos hX hY).ne key

/-- The distribution of the model of a rule factorizes according to the graph and, under the
hypotheses of `Digraph.BoolRule.not_condIndep`, violates `{x} ⫫ {y} | Z`. -/
theorem exists_factorizes_not_condIndep (hG : G.IsAcyclic) {x y : V} {Z : Finset V}
    (ha : ∀ n σ, R.Sol n σ → (∀ z ∈ Z, σ z = false) → σ x = σ y)
    (hb : ∃ n, ∀ σ, R.Sol n σ → σ x = true ∧ ∀ z ∈ Z, σ z = false) :
    ∃ p : FiniteDist (V → Bool), G.Factorizes p ∧ ¬ p.CondIndep {x} {y} Z :=
  ⟨(R.toSCM hG).dist, (R.toSCM hG).factorizes, R.not_condIndep hG ha hb⟩

end BoolRule

end Rule


end Digraph
