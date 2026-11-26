/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Graphical.Mutilation

/-!
# d-separation

d-separation in a directed graph `G : Digraph V`, defined purely graphically through the
"Bayes-ball" reachability formulation, together with its basic theory.

## The definition

A *trail* is a walk in the underlying undirected graph whose steps are labeled with the direction
of the edge they use. An interior vertex `m` of a trail is a *collider* when both trail edges at
`m` point into `m` (`· → m ← ·`); every other vertex of the trail, including both endpoints, is a
*non-collider*. A trail is *active* given `Z` when every collider lies in `G.ancestorsOf Z`
(the collider or one of its descendants is in `Z`) and every non-collider lies outside `Z`.

To make d-connection a reachability question, a trail is recorded as a sequence of states
`(v, b) : V × Bool`, where `b = true` means that the trail arrived at `v` along an edge pointing
into `v`. The state graph `Digraph.bayesBall G Z` has an edge `(v, b) → (w, c)` when the edge
`v → w` (if `c = true`) or `w → v` (if `c = false`) is in `G`, and `v` is allowed to pass the
trail on: `v ∈ G.ancestorsOf Z` if `v` is a collider (`b = true` and `c = false`), and `v ∉ Z`
otherwise. A trail starts in the state `(x, false)`, so its first vertex is never a collider.

* `Digraph.DConn G X Y Z`: some `x ∈ X` and `y ∈ Y`, both outside `Z`, are joined by an active
  trail given `Z`.
* `Digraph.DSep G X Y Z`: the negation, "`X` and `Y` are d-separated by `Z` in `G`".

The file `CausalInference.Graphical.DSeparationDecide` proves that `DConn` agrees with the
textbook definition by active trails and by active simple paths (no repeated vertex), and that
it is decidable on finite graphs.

## Conventions for overlapping sets

Pearl's definition is stated for pairwise disjoint `X`, `Y`, `Z`. The definition here is total:

* an endpoint in `Z` blocks (endpoints are non-colliders), so `G.DSep X Y Z` holds exactly when
  `G.DSep (X \ Z) (Y \ Z) Z` holds (`Digraph.dSep_diff_iff`), and `X ⊆ Z` gives `G.DSep X Y Z`;
* a vertex of `(X ∩ Y) \ Z` is joined to itself by the trivial trail, so d-separation forces
  `X ∩ Y ⊆ Z` (`Digraph.DSep.inter_subset`).

These conventions match the behavior of conditional independence (`X` is independent of anything
given `X`, and a nondegenerate variable is not independent of itself), and with them the
semi-graphoid axioms hold without disjointness hypotheses.

## Main results

* `Digraph.dSep_comm`: symmetry.
* `Digraph.DSep.mono_left`, `Digraph.dSep_union_left`, `Digraph.dSep_empty_left`,
  `Digraph.dSep_iff_forall_singleton` and the right-hand versions.
* `Digraph.DSep.anti_graph`: deleting edges preserves d-separation; hence
  `Digraph.DSep.deleteIncoming`, `Digraph.DSep.deleteOutgoing`, `Digraph.DSep.restrict`.
* `Digraph.DSep.weak_union`, `Digraph.DSep.contraction`: the remaining semi-graphoid axioms.
* Three-vertex facts: `Digraph.dConn_of_adj`, `Digraph.dConn_of_chain`, `Digraph.dConn_of_fork`,
  `Digraph.dConn_of_collider` (conditioning on a collider or a descendant of it opens the path),
  `Digraph.dSep_of_block` (a chain or fork through a conditioned vertex with no other connection
  is blocked), `Digraph.dSep_of_collider` (an unconditioned collider with no descendants blocks).
* `Digraph.IsAcyclic.dSep_nondescendants_parents`: in an acyclic graph a vertex is d-separated
  from its non-descendants given its parents (the graph side of the local Markov property).

## References

* J. Pearl (1988), *Probabilistic Reasoning in Intelligent Systems*.
* T. Verma and J. Pearl (1988), *Causal networks: semantics and expressiveness*.
* S. L. Lauritzen, A. P. Dawid, B. N. Larsen, H.-G. Leimer (1990), *Independence properties of
  directed Markov fields*.
* R. D. Shachter (1998), *Bayes-Ball: The rational pastime*.
* J. Pearl (2009), *Causality: Models, Reasoning, and Inference*, 2nd edition, section 1.2.3.
-/

@[expose] public section

namespace Digraph

open Relation

variable {V : Type*}

/-- `G.Passes Z v b c`: a trail that arrived at `v` (through an arrowhead at `v` if `b = true`)
and leaves `v` along an edge pointing into `v` (if `c = false`) or out of `v` (if `c = true`) is
not blocked at `v` given `Z`. If `v` is a collider of the trail (`b = true` and `c = false`) this
means `v ∈ G.ancestorsOf Z`; otherwise it means `v ∉ Z`. -/
def Passes (G : Digraph V) (Z : Set V) (v : V) (b c : Bool) : Prop :=
  if b = true ∧ c = false then v ∈ G.ancestorsOf Z else v ∉ Z

/-- The Bayes-ball state graph of `G` given `Z`. A state `(v, b)` records a vertex `v` reached by
a trail, with `b = true` when the trail arrived at `v` along an edge pointing into `v`. There is
an edge `(v, b) → (w, c)` when the trail can continue from `v` to `w`: it uses the edge `v → w`
if `c = true` and the edge `w → v` if `c = false`, and `v` lets the trail pass
(`Digraph.Passes`). -/
def bayesBall (G : Digraph V) (Z : Set V) : Digraph (V × Bool) where
  Adj s t := (if t.2 then G.Adj s.1 t.1 else G.Adj t.1 s.1) ∧ G.Passes Z s.1 s.2 t.2

/-- `G.DConn X Y Z`: `X` and `Y` are d-connected given `Z` in `G`. Some `x ∈ X` and `y ∈ Y`,
both outside `Z`, are joined by a trail that is active given `Z`: every collider of the trail is
in `G.ancestorsOf Z` and every other vertex of the trail is outside `Z`. The trail is encoded as
a path of the Bayes-ball state graph starting at `(x, false)`. -/
def DConn (G : Digraph V) (X Y Z : Set V) : Prop :=
  ∃ x ∈ X, ∃ y ∈ Y, x ∉ Z ∧ y ∉ Z ∧ ∃ b, ReflTransGen (G.bayesBall Z).Adj (x, false) (y, b)

/-- `G.DSep X Y Z`: `X` and `Y` are d-separated by `Z` in `G`, that is, not d-connected: every
trail between a vertex of `X \ Z` and a vertex of `Y \ Z` has a collider outside
`G.ancestorsOf Z` or a non-collider in `Z`. -/
def DSep (G : Digraph V) (X Y Z : Set V) : Prop := ¬ G.DConn X Y Z

variable {G H : Digraph V} {X X' Y Y' Z W : Set V} {u v w m : V} {a b c : Bool}

/-! ### The state graph -/

@[simp] theorem bayesBall_adj_true :
    (G.bayesBall Z).Adj (v, a) (w, true) ↔ G.Adj v w ∧ v ∉ Z := by
  simp [bayesBall, Passes]

@[simp] theorem bayesBall_adj_false_false :
    (G.bayesBall Z).Adj (v, false) (w, false) ↔ G.Adj w v ∧ v ∉ Z := by
  simp [bayesBall, Passes]

@[simp] theorem bayesBall_adj_true_false :
    (G.bayesBall Z).Adj (v, true) (w, false) ↔ G.Adj w v ∧ v ∈ G.ancestorsOf Z := by
  simp [bayesBall, Passes]

/-- Passing is invariant under reversing the trail: the arrival and departure flags swap and
are negated. -/
theorem passes_comm : G.Passes Z v b c ↔ G.Passes Z v (!c) (!b) := by
  cases b <;> cases c <;> simp [Passes]

/-- A trail leaving a state that was not entered through an arrowhead starts outside `Z`. -/
theorem notMem_of_bayesBall_adj_false {t : V × Bool} (h : (G.bayesBall Z).Adj (v, false) t) :
    v ∉ Z := by
  obtain ⟨w, c⟩ := t
  cases c
  · exact (bayesBall_adj_false_false.1 h).2
  · exact (bayesBall_adj_true.1 h).2

/-- A trail that is entered through an arrowhead and later arrives somewhere through a tail must
turn at a collider, which is a descendant of its first vertex; so the first vertex is in
`G.ancestorsOf Z`. -/
theorem mem_ancestorsOf_of_reflTransGen_bayesBall {s : V × Bool}
    (h : ReflTransGen (G.bayesBall Z).Adj s (w, false)) (hs : s.2 = true) :
    s.1 ∈ G.ancestorsOf Z := by
  induction h using ReflTransGen.head_induction_on with
  | refl => simp at hs
  | @head s t hst _ ih =>
    obtain ⟨v, b⟩ := s
    obtain ⟨x, c⟩ := t
    simp only at hs
    subst hs
    cases c
    · exact (bayesBall_adj_true_false.1 hst).2
    · exact mem_ancestorsOf_of_adj (bayesBall_adj_true.1 hst).1 (ih rfl)

/-- A directed path out of a vertex that is not an ancestor of `Z` is an active trail given `Z`,
whatever the arrival flag at its first vertex. -/
theorem exists_reflTransGen_bayesBall_of_reflTransGen (h : ReflTransGen G.Adj u w)
    (hu : u ∉ G.ancestorsOf Z) (b : Bool) :
    ∃ c, ReflTransGen (G.bayesBall Z).Adj (u, b) (w, c) := by
  induction h using ReflTransGen.head_induction_on generalizing b with
  | refl => exact ⟨b, ReflTransGen.refl⟩
  | @head u u₁ huu₁ _ ih =>
    obtain ⟨c, hc⟩ := ih (fun h => hu (mem_ancestorsOf_of_adj huu₁ h)) true
    exact ⟨c, ReflTransGen.head
      (bayesBall_adj_true.2 ⟨huu₁, fun h => hu (subset_ancestorsOf Z h)⟩) hc⟩

/-- The state graph is monotone in the graph. -/
theorem bayesBall_mono (h : H ≤ G) : H.bayesBall Z ≤ G.bayesBall Z := by
  rintro ⟨v, b⟩ ⟨w, c⟩ hvw
  cases c
  · cases b
    · exact bayesBall_adj_false_false.2
        ⟨h (bayesBall_adj_false_false.1 hvw).1, (bayesBall_adj_false_false.1 hvw).2⟩
    · exact bayesBall_adj_true_false.2 ⟨h (bayesBall_adj_true_false.1 hvw).1,
        ancestorsOf_mono_graph h Z (bayesBall_adj_true_false.1 hvw).2⟩
  · exact bayesBall_adj_true.2 ⟨h (bayesBall_adj_true.1 hvw).1, (bayesBall_adj_true.1 hvw).2⟩

/-- Reversal of an active trail, generalized over the flags at both ends: a trail from `s` to
`t` that may continue past `t` with departure flag `e` can be reversed into a trail from
`(t.1, !e)` to some `(s.1, c)` that may continue past `s.1` with departure flag `!s.2`. -/
theorem reflTransGen_bayesBall_reverse {s t : V × Bool}
    (h : ReflTransGen (G.bayesBall Z).Adj s t) (e : Bool) (he : G.Passes Z t.1 t.2 e) :
    ∃ c, ReflTransGen (G.bayesBall Z).Adj (t.1, !e) (s.1, c) ∧ G.Passes Z s.1 c (!s.2) := by
  induction h generalizing e with
  | refl => exact ⟨!e, ReflTransGen.refl, passes_comm.1 he⟩
  | @tail t₁ t₂ _ h₁₂ ih =>
    obtain ⟨u, f⟩ := t₁
    obtain ⟨y, d⟩ := t₂
    obtain ⟨hedge, hpass⟩ := h₁₂
    obtain ⟨c, hc, hcp⟩ := ih d hpass
    refine ⟨c, ReflTransGen.head ⟨?_, ?_⟩ hc, hcp⟩
    · cases d <;> simpa using hedge
    · simpa using (passes_comm.1 he)

/-! ### Elementary properties -/

theorem dSep_iff_not_dConn : G.DSep X Y Z ↔ ¬ G.DConn X Y Z := Iff.rfl

/-- d-connection is symmetric. -/
theorem DConn.symm (h : G.DConn X Y Z) : G.DConn Y X Z := by
  obtain ⟨x, hx, y, hy, hxZ, hyZ, b, hxy⟩ := h
  obtain ⟨c, hc, -⟩ := reflTransGen_bayesBall_reverse hxy true (by simpa [Passes] using hyZ)
  exact ⟨y, hy, x, hx, hyZ, hxZ, c, hc⟩

theorem dConn_comm : G.DConn X Y Z ↔ G.DConn Y X Z := ⟨DConn.symm, DConn.symm⟩

/-- d-separation is symmetric. -/
theorem dSep_comm : G.DSep X Y Z ↔ G.DSep Y X Z := not_congr dConn_comm

theorem DSep.symm (h : G.DSep X Y Z) : G.DSep Y X Z := dSep_comm.1 h

theorem DConn.mono_left (h : G.DConn X' Y Z) (hX : X' ⊆ X) : G.DConn X Y Z := by
  obtain ⟨x, hx, rest⟩ := h
  exact ⟨x, hX hx, rest⟩

theorem DConn.mono_right (h : G.DConn X Y' Z) (hY : Y' ⊆ Y) : G.DConn X Y Z :=
  (h.symm.mono_left hY).symm

/-- Decomposition in the first argument: d-separation passes to subsets. -/
theorem DSep.mono_left (hX : X' ⊆ X) (h : G.DSep X Y Z) : G.DSep X' Y Z :=
  fun h' => h (h'.mono_left hX)

/-- Decomposition in the second argument: d-separation passes to subsets. -/
theorem DSep.mono_right (hY : Y' ⊆ Y) (h : G.DSep X Y Z) : G.DSep X Y' Z :=
  fun h' => h (h'.mono_right hY)

theorem dConn_union_left : G.DConn (X ∪ X') Y Z ↔ G.DConn X Y Z ∨ G.DConn X' Y Z := by
  constructor
  · rintro ⟨x, hx | hx, rest⟩
    · exact Or.inl ⟨x, hx, rest⟩
    · exact Or.inr ⟨x, hx, rest⟩
  · rintro (h | h)
    · exact h.mono_left Set.subset_union_left
    · exact h.mono_left Set.subset_union_right

theorem dConn_union_right : G.DConn X (Y ∪ Y') Z ↔ G.DConn X Y Z ∨ G.DConn X Y' Z := by
  rw [dConn_comm, dConn_union_left, dConn_comm, @dConn_comm _ _ _ Y']

/-- d-separation from a union is d-separation from each part (decomposition and composition). -/
theorem dSep_union_left : G.DSep (X ∪ X') Y Z ↔ G.DSep X Y Z ∧ G.DSep X' Y Z := by
  simp only [DSep, dConn_union_left, not_or]

theorem dSep_union_right : G.DSep X (Y ∪ Y') Z ↔ G.DSep X Y Z ∧ G.DSep X Y' Z := by
  simp only [DSep, dConn_union_right, not_or]

@[simp] theorem dSep_empty_left : G.DSep ∅ Y Z := fun ⟨_, hx, _⟩ => hx

@[simp] theorem dSep_empty_right : G.DSep X ∅ Z := fun h => dSep_empty_left h.symm

/-- d-connection of sets reduces to d-connection of a pair of vertices. -/
theorem dConn_iff_exists_singleton :
    G.DConn X Y Z ↔ ∃ x ∈ X, ∃ y ∈ Y, G.DConn {x} {y} Z := by
  constructor
  · rintro ⟨x, hx, y, hy, rest⟩
    exact ⟨x, hx, y, hy, x, rfl, y, rfl, rest⟩
  · rintro ⟨x, hx, y, hy, h⟩
    exact (h.mono_left (Set.singleton_subset_iff.2 hx)).mono_right
      (Set.singleton_subset_iff.2 hy)

/-- d-separation of sets is d-separation of every pair of vertices. -/
theorem dSep_iff_forall_singleton :
    G.DSep X Y Z ↔ ∀ x ∈ X, ∀ y ∈ Y, G.DSep {x} {y} Z := by
  rw [DSep, dConn_iff_exists_singleton]
  simp only [DSep, not_exists, not_and]

/-- Endpoints in `Z` are blocked: only `X \ Z` and `Y \ Z` matter. -/
theorem dConn_diff_iff : G.DConn (X \ Z) (Y \ Z) Z ↔ G.DConn X Y Z := by
  constructor
  · rintro ⟨x, hx, y, hy, rest⟩
    exact ⟨x, hx.1, y, hy.1, rest⟩
  · rintro ⟨x, hx, y, hy, hxZ, hyZ, rest⟩
    exact ⟨x, ⟨hx, hxZ⟩, y, ⟨hy, hyZ⟩, hxZ, hyZ, rest⟩

/-- Endpoints in `Z` are blocked: `G.DSep X Y Z` depends only on `X \ Z` and `Y \ Z`. -/
theorem dSep_diff_iff : G.DSep (X \ Z) (Y \ Z) Z ↔ G.DSep X Y Z := not_congr dConn_diff_iff

/-- A set contained in the conditioning set is d-separated from everything. -/
theorem dSep_of_subset_left (h : X ⊆ Z) : G.DSep X Y Z :=
  fun ⟨_, hx, _, _, hxZ, _⟩ => hxZ (h hx)

theorem dSep_of_subset_right (h : Y ⊆ Z) : G.DSep X Y Z :=
  fun h' => dSep_of_subset_left h h'.symm

/-- A vertex outside `Z` lying in both sets d-connects them (by the trivial trail). -/
theorem dConn_of_mem_inter (hX : v ∈ X) (hY : v ∈ Y) (hZ : v ∉ Z) : G.DConn X Y Z :=
  ⟨v, hX, v, hY, hZ, hZ, false, ReflTransGen.refl⟩

/-- d-separated sets can only overlap inside the conditioning set. -/
theorem DSep.inter_subset (h : G.DSep X Y Z) : X ∩ Y ⊆ Z := fun _ ⟨hX, hY⟩ =>
  by_contra fun hZ => h (dConn_of_mem_inter hX hY hZ)

/-! ### Edge deletion -/

/-- An active trail in a subgraph is an active trail in the larger graph: the subgraph has fewer
edges and a smaller ancestral closure of `Z`, so fewer colliders are open. -/
theorem DConn.mono_graph (hHG : H ≤ G) (h : H.DConn X Y Z) : G.DConn X Y Z := by
  obtain ⟨x, hx, y, hy, hxZ, hyZ, b, hxy⟩ := h
  exact ⟨x, hx, y, hy, hxZ, hyZ, b, ReflTransGen.mono (fun _ _ h => bayesBall_mono hHG h) _ _ hxy⟩

/-- Deleting edges preserves d-separation. -/
theorem DSep.anti_graph (hHG : H ≤ G) (h : G.DSep X Y Z) : H.DSep X Y Z :=
  fun h' => h (h'.mono_graph hHG)

theorem DSep.deleteIncoming (h : G.DSep X Y Z) : (G.deleteIncoming W).DSep X Y Z :=
  h.anti_graph deleteIncoming_le

theorem DSep.deleteOutgoing (h : G.DSep X Y Z) : (G.deleteOutgoing W).DSep X Y Z :=
  h.anti_graph deleteOutgoing_le

theorem DSep.restrict (h : G.DSep X Y Z) : (G.restrict W).DSep X Y Z :=
  h.anti_graph restrict_le

/-! ### Weak union and contraction -/

/-- The core of weak union: an active trail given `Z ∪ W` from `(x, false)` is, up to the first
collider that is an ancestor of `W` but not of `Z`, an active trail given `Z`; at that collider
one can instead follow a directed path down to `W`. -/
theorem reflTransGen_bayesBall_union_or {x : V} {t : V × Bool}
    (h : ReflTransGen (G.bayesBall (Z ∪ W)).Adj (x, false) t) :
    ReflTransGen (G.bayesBall Z).Adj (x, false) t ∨
      ∃ w ∈ W, w ∉ Z ∧ ∃ c, ReflTransGen (G.bayesBall Z).Adj (x, false) (w, c) := by
  induction h with
  | refl => exact Or.inl ReflTransGen.refl
  | @tail t₁ t₂ _ h₁₂ ih =>
    rcases ih with ih | ih
    · obtain ⟨u, f⟩ := t₁
      obtain ⟨v, d⟩ := t₂
      cases d
      · cases f
        · obtain ⟨hvu, hu⟩ := bayesBall_adj_false_false.1 h₁₂
          exact Or.inl (ih.tail (bayesBall_adj_false_false.2 ⟨hvu, fun h => hu (Or.inl h)⟩))
        · obtain ⟨hvu, hu⟩ := bayesBall_adj_true_false.1 h₁₂
          rw [ancestorsOf_union] at hu
          by_cases huZ : u ∈ G.ancestorsOf Z
          · exact Or.inl (ih.tail (bayesBall_adj_true_false.2 ⟨hvu, huZ⟩))
          · obtain ⟨w, hw, huw⟩ := hu.resolve_left huZ
            obtain ⟨c, hc⟩ := exists_reflTransGen_bayesBall_of_reflTransGen huw huZ true
            exact Or.inr ⟨w, hw, fun hwZ => huZ ⟨w, hwZ, huw⟩, c, ih.trans hc⟩
      · obtain ⟨huv, hu⟩ := bayesBall_adj_true.1 h₁₂
        exact Or.inl (ih.tail (bayesBall_adj_true.2 ⟨huv, fun h => hu (Or.inl h)⟩))
    · exact Or.inr ih

/-- Weak union: if `X` is d-separated from `Y ∪ W` by `Z`, then `X` is d-separated from `Y` by
`Z ∪ W`. -/
theorem DSep.weak_union (h : G.DSep X (Y ∪ W) Z) : G.DSep X Y (Z ∪ W) := by
  rintro ⟨x, hx, y, hy, hxZ, hyZ, b, hxy⟩
  rcases reflTransGen_bayesBall_union_or hxy with hxy' | ⟨w, hw, hwZ, c, hxw⟩
  · exact h ⟨x, hx, y, Or.inl hy, fun h => hxZ (Or.inl h), fun h => hyZ (Or.inl h), b, hxy'⟩
  · exact h ⟨x, hx, w, Or.inr hw, fun h => hxZ (Or.inl h), hwZ, c, hxw⟩

/-- The core of contraction: if no active trail given `Z` from `(x, false)` reaches a vertex of
`Y \ Z`, then every active trail given `Z` from `(x, false)` is also active given `Z ∪ Y`. -/
theorem reflTransGen_bayesBall_union_of_forall {x : V} {t : V × Bool}
    (hY : ∀ s : V × Bool, ReflTransGen (G.bayesBall Z).Adj (x, false) s → s.1 ∉ Z → s.1 ∉ Y)
    (h : ReflTransGen (G.bayesBall Z).Adj (x, false) t) :
    ReflTransGen (G.bayesBall (Z ∪ Y)).Adj (x, false) t := by
  induction h with
  | refl => exact ReflTransGen.refl
  | @tail t₁ t₂ h₀₁ h₁₂ ih =>
    obtain ⟨u, f⟩ := t₁
    obtain ⟨v, d⟩ := t₂
    have key : u ∉ Z → u ∉ Z ∪ Y := fun huZ h => h.elim huZ (hY _ h₀₁ huZ)
    cases d
    · cases f
      · obtain ⟨hvu, hu⟩ := bayesBall_adj_false_false.1 h₁₂
        exact ih.tail (bayesBall_adj_false_false.2 ⟨hvu, key hu⟩)
      · obtain ⟨hvu, hu⟩ := bayesBall_adj_true_false.1 h₁₂
        exact ih.tail (bayesBall_adj_true_false.2
          ⟨hvu, ancestorsOf_mono Set.subset_union_left hu⟩)
    · obtain ⟨huv, hu⟩ := bayesBall_adj_true.1 h₁₂
      exact ih.tail (bayesBall_adj_true.2 ⟨huv, key hu⟩)

/-- Contraction: if `X` is d-separated from `Y` by `Z` and from `W` by `Z ∪ Y`, then `X` is
d-separated from `Y ∪ W` by `Z`. -/
theorem DSep.contraction (hY : G.DSep X Y Z) (hW : G.DSep X W (Z ∪ Y)) :
    G.DSep X (Y ∪ W) Z := by
  rintro ⟨x, hx, t, ht, hxZ, htZ, b, hxt⟩
  have hsep : ∀ s : V × Bool, ReflTransGen (G.bayesBall Z).Adj (x, false) s → s.1 ∉ Z →
      s.1 ∉ Y :=
    fun ⟨y, c⟩ hs hyZ hyY => hY ⟨x, hx, y, hyY, hxZ, hyZ, c, hs⟩
  rcases ht with htY | htW
  · exact hY ⟨x, hx, t, htY, hxZ, htZ, b, hxt⟩
  · have hxY := hsep _ ReflTransGen.refl hxZ
    have htY := hsep _ hxt htZ
    exact hW ⟨x, hx, t, htW, fun h => h.elim hxZ hxY, fun h => h.elim htZ htY, b,
      reflTransGen_bayesBall_union_of_forall hsep hxt⟩

/-! ### Three-vertex configurations -/

/-- Two adjacent vertices outside `Z` are d-connected given `Z`. -/
theorem dConn_of_adj (h : G.Adj u v) (hu : u ∉ Z) (hv : v ∉ Z) : G.DConn {u} {v} Z :=
  ⟨u, rfl, v, rfl, hu, hv, true, ReflTransGen.single (bayesBall_adj_true.2 ⟨h, hu⟩)⟩

/-- A chain `u → m → v` is open when `m` is not conditioned on. -/
theorem dConn_of_chain (hum : G.Adj u m) (hmv : G.Adj m v) (hu : u ∉ Z) (hm : m ∉ Z)
    (hv : v ∉ Z) : G.DConn {u} {v} Z :=
  ⟨u, rfl, v, rfl, hu, hv, true, ReflTransGen.head (bayesBall_adj_true.2 ⟨hum, hu⟩)
    (ReflTransGen.single (bayesBall_adj_true.2 ⟨hmv, hm⟩))⟩

/-- A fork `u ← m → v` is open when `m` is not conditioned on. -/
theorem dConn_of_fork (hmu : G.Adj m u) (hmv : G.Adj m v) (hu : u ∉ Z) (hm : m ∉ Z)
    (hv : v ∉ Z) : G.DConn {u} {v} Z :=
  ⟨u, rfl, v, rfl, hu, hv, true, ReflTransGen.head (bayesBall_adj_false_false.2 ⟨hmu, hu⟩)
    (ReflTransGen.single (bayesBall_adj_true.2 ⟨hmv, hm⟩))⟩

/-- A collider `u → m ← v` is opened by conditioning on `m` or on a descendant of `m`, that is,
when `m ∈ G.ancestorsOf Z`. -/
theorem dConn_of_collider (hum : G.Adj u m) (hvm : G.Adj v m) (hu : u ∉ Z)
    (hm : m ∈ G.ancestorsOf Z) (hv : v ∉ Z) : G.DConn {u} {v} Z :=
  ⟨u, rfl, v, rfl, hu, hv, false, ReflTransGen.head (bayesBall_adj_true.2 ⟨hum, hu⟩)
    (ReflTransGen.single (bayesBall_adj_true_false.2 ⟨hvm, hm⟩))⟩

/-- Blocking at a conditioned vertex with no other connection. Suppose the only neighbor of `u`
(in either direction) is `m`, the only possible parent of `m` is `u`, and `m ∈ Z`. Then `u` is
d-separated given `Z` from every set not containing `u`. This covers the chain `u → m → v` and
the fork `u ← m → v` when no other edge touches `u` or enters `m`: conditioning on the middle
vertex blocks. -/
theorem dSep_of_block (hu : ∀ w, G.Adj u w ∨ G.Adj w u → w = m)
    (hpar : ∀ w, G.Adj w m → w = u) (hm : m ∈ Z) (huY : u ∉ Y) : G.DSep {u} Y Z := by
  have inv : ∀ s : V × Bool, ReflTransGen (G.bayesBall Z).Adj (u, false) s →
      s.1 = u ∨ s.1 = m := by
    intro s hs
    induction hs with
    | refl => exact Or.inl rfl
    | @tail t₁ t₂ _ h₁₂ ih =>
      obtain ⟨x, f⟩ := t₁
      obtain ⟨y, d⟩ := t₂
      obtain ⟨hedge, hpass⟩ := h₁₂
      rcases ih with rfl | rfl
      · right
        cases d
        · exact hu y (Or.inr hedge)
        · exact hu y (Or.inl hedge)
      · left
        cases d
        · cases f
          · exact absurd hm (by simpa [Passes] using hpass)
          · exact hpar y hedge
        · exact absurd hm (by simpa [Passes] using hpass)
  rintro ⟨x, rfl, y, hy, -, hyZ, b, hxy⟩
  rcases inv _ hxy with rfl | rfl
  · exact huY hy
  · exact hyZ hm

/-- An unconditioned collider with no descendants blocks. Suppose the only neighbor of `u` (in
either direction) is `m`, the vertex `m` has no children and `m ∉ Z`. Then `u` is d-separated
given `Z` from every set containing neither `u` nor `m`. This covers the collider `u → m ← v`
with no other edge touching `u` or leaving `m`: without conditioning on `m` (or a descendant),
`u` and `v` are d-separated. -/
theorem dSep_of_collider (hu : ∀ w, G.Adj u w ∨ G.Adj w u → w = m) (hch : ∀ w, ¬ G.Adj m w)
    (hm : m ∉ Z) (huY : u ∉ Y) (hmY : m ∉ Y) : G.DSep {u} Y Z := by
  have hmA : m ∉ G.ancestorsOf Z := by
    rintro ⟨s, hs, hms⟩
    rcases hms.cases_head with rfl | ⟨c, hmc, _⟩
    · exact hm hs
    · exact hch c hmc
  have inv : ∀ s : V × Bool, ReflTransGen (G.bayesBall Z).Adj (u, false) s →
      s.1 = u ∨ (s.1 = m ∧ s.2 = true) := by
    intro s hs
    induction hs with
    | refl => exact Or.inl rfl
    | @tail t₁ t₂ _ h₁₂ ih =>
      obtain ⟨x, f⟩ := t₁
      obtain ⟨y, d⟩ := t₂
      rcases ih with rfl | ⟨rfl, rfl⟩
      · cases d
        · obtain ⟨hyx, -⟩ := h₁₂
          have hym : y = m := hu y (Or.inr (by simpa using hyx))
          subst hym
          exact absurd (by simpa using hyx) (hch x)
        · obtain ⟨hxy, -⟩ := h₁₂
          exact Or.inr ⟨hu y (Or.inl (by simpa using hxy)), rfl⟩
      · cases d
        · exact absurd (bayesBall_adj_true_false.1 h₁₂).2 hmA
        · exact absurd (bayesBall_adj_true.1 h₁₂).1 (hch y)
  rintro ⟨x, rfl, y, hy, -, -, b, hxy⟩
  rcases inv _ hxy with h | ⟨h, -⟩
  · exact huY (h ▸ hy)
  · exact hmY (h ▸ hy)

/-! ### The local Markov statement -/

/-- In an acyclic graph, a vertex is d-separated from its non-descendants given its parents.
Since parents are in the conditioning set and endpoints in the conditioning set are blocked,
this is equivalent to the textbook form with the non-descendants that are not parents. -/
theorem IsAcyclic.dSep_nondescendants_parents (hG : G.IsAcyclic) (v : V) :
    G.DSep {v} (G.descendantsOf {v})ᶜ (G.parents v) := by
  have inv : ∀ s : V × Bool, ReflTransGen (G.bayesBall (G.parents v)).Adj (v, false) s →
      s = (v, false) ∨ (s.1 ∈ G.parents v ∧ s.2 = false) ∨
        (G.IsAncestor v s.1 ∧ s.2 = true) := by
    intro s hs
    induction hs with
    | refl => exact Or.inl rfl
    | @tail t₁ t₂ _ h₁₂ ih =>
      obtain ⟨x, f⟩ := t₁
      obtain ⟨y, d⟩ := t₂
      rcases ih with h | ⟨hx, rfl⟩ | ⟨hx, rfl⟩
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        cases d
        · exact Or.inr (Or.inl ⟨(bayesBall_adj_false_false.1 h₁₂).1, rfl⟩)
        · exact Or.inr (Or.inr ⟨isAncestor_of_adj (bayesBall_adj_true.1 h₁₂).1, rfl⟩)
      · exact absurd hx (notMem_of_bayesBall_adj_false h₁₂)
      · cases d
        · obtain ⟨-, p, hp, hxp⟩ := bayesBall_adj_true_false.1 h₁₂
          exact absurd ((TransGen.trans_left hx hxp).tail hp) (hG v)
        · exact Or.inr (Or.inr ⟨hx.tail (bayesBall_adj_true.1 h₁₂).1, rfl⟩)
  rintro ⟨x, rfl, y, hy, -, hyZ, b, hxy⟩
  rcases inv _ hxy with h | ⟨h, -⟩ | ⟨h, -⟩
  · obtain ⟨rfl, -⟩ := Prod.mk.inj h
    exact hy (subset_descendantsOf _ rfl)
  · exact hyZ h
  · exact hy ⟨x, rfl, h.reflTransGen⟩

end Digraph
