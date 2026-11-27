/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Graphical.Closure
public import CausalInference.Graphical.DSeparation
public import CausalInference.Graphical.DSeparationDecide
public import CausalInference.Graphical.Induce
public import CausalInference.Graphical.Criteria.Moralization
public import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Further d-separation lemmas

Lemmas on d-separation (`Digraph.DSep`, defined in `CausalInference.Graphical.DSeparation`) that
use the active-trail formulation of `CausalInference.Graphical.DSeparationDecide`.

## Main definitions

* `Digraph.skeleton G`: the underlying undirected graph of `G`, as a Mathlib `SimpleGraph`.

## Main results

* `Digraph.IsAcyclic.dSep_singleton_nonDescendants_parents`,
  `Digraph.IsAcyclic.dSep_nonDescendants_diff_parents`: the local Markov statement stated with
  `Digraph.nonDescendants`, with and without the parents in the second set.
* `Digraph.dSep_of_parent_block`: a conditioned fork blocks, with no restriction on the other
  parents and children of the middle vertex.
* `Digraph.dSep_of_unique_path_of_mem`, `Digraph.dSep_of_unique_path_of_notMem_ancestorsOf`:
  if `[u, m, v]` is the unique path between `u` and `v` in the skeleton, conditioning on `m`
  blocks a chain or a fork, and `m ∉ G.ancestorsOf Z` blocks a collider; the acyclic chain,
  fork and collider forms follow.
* `Digraph.ActiveTrail.mem_ancestorsOf_pair`: every vertex of an active trail from `x` to `y`
  given `Z` lies in `G.ancestorsOf ({x, y} ∪ Z)`.
* `Digraph.dSep_restrict_iff_of_isAncestral`, `Digraph.dSep_induce_iff_of_isAncestral`: for an
  ancestral set `S` containing `X ∪ Y ∪ Z`, d-separation in `G` is d-separation in the
  restriction `G.restrict S` and in the induced subgraph `G.induce S`.
* `Digraph.DSep.intersection`: the intersection property, under `Y ∩ W ⊆ Z`; the hypothesis is
  needed under the total convention for overlapping sets
  (`CausalInference.DSeparationLemmasExamples.dSep_intersection_needs_disjoint`).

None of the results uses finiteness; only the local Markov statements and the chain, fork and
collider forms use acyclicity.

## References

* J. Pearl (1988), *Probabilistic Reasoning in Intelligent Systems*.
* S. L. Lauritzen, A. P. Dawid, B. N. Larsen, H.-G. Leimer (1990), *Independence properties of
  directed Markov fields*, Networks 20.
* J. Pearl (2009), *Causality: Models, Reasoning, and Inference*, 2nd edition, section 1.2.3.
-/

@[expose] public section

namespace Digraph

open Relation

variable {V : Type*}

variable {G : Digraph V} {X Y Z W S : Set V} {u v w m x y : V} {a : Bool} {l : List V}

/-! ### The local Markov statement with non-descendants -/

/-- In an acyclic graph a vertex is d-separated from its non-descendants given its parents,
stated with `Digraph.nonDescendants`. -/
theorem IsAcyclic.dSep_singleton_nonDescendants_parents (hG : G.IsAcyclic) (v : V) :
    G.DSep {v} (G.nonDescendants v) (G.parents v) :=
  hG.dSep_nondescendants_parents v

/-- The textbook form of the local Markov statement: in an acyclic graph a vertex is
d-separated from its non-descendants other than its parents, given its parents. -/
theorem IsAcyclic.dSep_nonDescendants_diff_parents (hG : G.IsAcyclic) (v : V) :
    G.DSep {v} (G.nonDescendants v \ G.parents v) (G.parents v) :=
  (hG.dSep_singleton_nonDescendants_parents v).mono_right Set.sdiff_subset

/-! ### Blocking at a fork -/

/-- Blocking at a conditioned fork. Suppose the only neighbor of `u` (in either direction) is
`m`, the edge `u → m` is absent (so `m` is a parent of `u`), and `m ∈ Z`. Then `u` is
d-separated given `Z` from every set not containing `u`. Unlike `Digraph.dSep_of_block`, the
middle vertex may have any further parents and children: a trail from `u` reaches `m` along
`u ← m`, so `m` is a non-collider, and conditioning on it blocks. -/
theorem dSep_of_parent_block (hu : ∀ w, G.Adj u w ∨ G.Adj w u → w = m) (hum : ¬ G.Adj u m)
    (hm : m ∈ Z) (huY : u ∉ Y) : G.DSep {u} Y Z := by
  have inv : ∀ s : V × Bool, ReflTransGen (G.bayesBall Z).Adj (u, false) s →
      s = (u, false) ∨ s = (m, false) := by
    intro s hs
    induction hs with
    | refl => exact Or.inl rfl
    | @tail t₁ t₂ _ h₁₂ ih =>
      obtain ⟨y, d⟩ := t₂
      rcases ih with rfl | rfl
      · cases d
        · obtain ⟨hyu, -⟩ := bayesBall_adj_false_false.1 h₁₂
          exact Or.inr (by rw [hu y (Or.inr hyu)])
        · obtain ⟨huy, -⟩ := bayesBall_adj_true.1 h₁₂
          exact absurd (hu y (Or.inl huy) ▸ huy) hum
      · exact absurd hm (notMem_of_bayesBall_adj_false h₁₂)
  rintro ⟨x, rfl, y, hy, -, hyZ, b, hxy⟩
  rcases inv _ hxy with h | h
  · exact huY ((Prod.mk.inj h).1 ▸ hy)
  · exact hyZ ((Prod.mk.inj h).1 ▸ hm)

/-! ### Three-vertex configurations with a unique skeleton path -/

/-- The skeleton of `G`: the undirected graph in which two distinct vertices are adjacent when
they are joined by an edge of `G` in either direction. -/
def skeleton (G : Digraph V) : SimpleGraph V := SimpleGraph.fromRel G.Adj

theorem skeleton_adj : G.skeleton.Adj u v ↔ u ≠ v ∧ (G.Adj u v ∨ G.Adj v u) :=
  SimpleGraph.fromRel_adj _ _ _

/-- The vertex list of an active trail with no repeated vertex is the support of a walk of the
skeleton (a path, by `SimpleGraph.Walk.isPath_def`). -/
theorem ActiveTrail.exists_walk (p : G.ActiveTrail Z a u w l) (hl : l.Nodup) :
    ∃ q : G.skeleton.Walk u w, q.support = l := by
  induction p with
  | nil _ => exact ⟨.nil, rfl⟩
  | @fwd a u v w l h _ q ih =>
    obtain ⟨r, hr⟩ := ih (List.nodup_cons.1 hl).2
    have hne : u ≠ v := fun e => (List.nodup_cons.1 hl).1 (e ▸ q.head_mem)
    exact ⟨.cons (skeleton_adj.2 ⟨hne, Or.inl h⟩) r, by simp [hr]⟩
  | @bwd u v w l h _ q ih =>
    obtain ⟨r, hr⟩ := ih (List.nodup_cons.1 hl).2
    have hne : u ≠ v := fun e => (List.nodup_cons.1 hl).1 (e ▸ q.head_mem)
    exact ⟨.cons (skeleton_adj.2 ⟨hne, Or.inr h⟩) r, by simp [hr]⟩
  | @collider u v w l h _ q ih =>
    obtain ⟨r, hr⟩ := ih (List.nodup_cons.1 hl).2
    have hne : u ≠ v := fun e => (List.nodup_cons.1 hl).1 (e ▸ q.head_mem)
    exact ⟨.cons (skeleton_adj.2 ⟨hne, Or.inr h⟩) r, by simp [hr]⟩

/-- A one-vertex active trail starts at its end. -/
theorem ActiveTrail.eq_of_singleton {t : V} (p : G.ActiveTrail Z a u w [t]) : u = w := by
  cases p with
  | nil _ => rfl
  | fwd _ _ q => simpa using q.head_mem
  | bwd _ _ q => simpa using q.head_mem
  | collider _ _ q => simpa using q.head_mem

/-- If `[u, m, v]` is the unique path of the skeleton from `u` to `v` and `u` and `v` are
d-connected given `Z`, then the trail `u, m, v` itself is active given `Z`. -/
theorem activeTrail_of_unique_path
    (huniq : ∀ q : G.skeleton.Walk u v, q.IsPath → q.support = [u, m, v])
    (h : G.DConn {u} {v} Z) : G.ActiveTrail Z false u v [u, m, v] := by
  obtain ⟨x, rfl, y, rfl, l, hl, hnd⟩ := dConn_iff_dConnPath.1 h
  obtain ⟨q, hq⟩ := hl.exists_walk hnd
  have hpath : q.IsPath := (SimpleGraph.Walk.isPath_def q).2 (hq ▸ hnd)
  rw [← hq, huniq q hpath] at hl
  exact hl

/-- **A chain or fork with a unique skeleton path is blocked by its middle vertex.** If
`[u, m, v]` is the unique path between `u` and `v` in the skeleton of `G`, the vertex `m` is
not a common child of `u` and `v`, and `m ∈ Z`, then `u` and `v` are d-separated given `Z`.
Other edges may touch `u`, `m` and `v`, as long as they create no second path. Neither
finiteness nor acyclicity is needed; `Digraph.IsAcyclic.dSep_of_unique_path_chain` and
`Digraph.IsAcyclic.dSep_of_unique_path_fork` are the chain and fork forms. -/
theorem dSep_of_unique_path_of_mem
    (huniq : ∀ q : G.skeleton.Walk u v, q.IsPath → q.support = [u, m, v])
    (hcol : ¬ (G.Adj u m ∧ G.Adj v m)) (hm : m ∈ Z) : G.DSep {u} {v} Z := by
  intro h
  cases activeTrail_of_unique_path huniq h with
  | fwd hum _ q =>
    cases q with
    | fwd _ hmZ _ => exact hmZ hm
    | collider hvm _ r =>
      cases r.eq_of_singleton
      exact hcol ⟨hum, hvm⟩
  | bwd _ _ q =>
    cases q with
    | fwd _ hmZ _ => exact hmZ hm
    | bwd _ hmZ _ => exact hmZ hm

/-- **A collider with a unique skeleton path is blocked unless it is an ancestor of `Z`.** If
`[u, m, v]` is the unique path between `u` and `v` in the skeleton of `G`, neither `m → u` nor
`m → v` is an edge, and `m ∉ G.ancestorsOf Z` (neither `m` nor a descendant of `m` is in `Z`),
then `u` and `v` are d-separated given `Z`. Neither finiteness nor acyclicity is needed;
`Digraph.IsAcyclic.dSep_of_unique_path_collider` is the collider form. -/
theorem dSep_of_unique_path_of_notMem_ancestorsOf
    (huniq : ∀ q : G.skeleton.Walk u v, q.IsPath → q.support = [u, m, v])
    (hmu : ¬ G.Adj m u) (hmv : ¬ G.Adj m v) (hm : m ∉ G.ancestorsOf Z) :
    G.DSep {u} {v} Z := by
  intro h
  cases activeTrail_of_unique_path huniq h with
  | fwd _ _ q =>
    cases q with
    | fwd hmw _ r =>
      cases r.eq_of_singleton
      exact hmv hmw
    | collider _ hmA _ => exact hm hmA
  | bwd hmu' _ q => cases q <;> exact hmu hmu'

/-- The chain `u → m → v` in an acyclic graph, when it is the unique skeleton path between
`u` and `v`, is blocked by conditioning on `m`. -/
theorem IsAcyclic.dSep_of_unique_path_chain (hG : G.IsAcyclic)
    (huniq : ∀ q : G.skeleton.Walk u v, q.IsPath → q.support = [u, m, v])
    (hmv : G.Adj m v) (hm : m ∈ Z) : G.DSep {u} {v} Z :=
  dSep_of_unique_path_of_mem huniq (fun h => hG.asymm hmv h.2) hm

/-- The fork `u ← m → v` in an acyclic graph, when it is the unique skeleton path between `u`
and `v`, is blocked by conditioning on `m`. -/
theorem IsAcyclic.dSep_of_unique_path_fork (hG : G.IsAcyclic)
    (huniq : ∀ q : G.skeleton.Walk u v, q.IsPath → q.support = [u, m, v])
    (hmu : G.Adj m u) (hm : m ∈ Z) : G.DSep {u} {v} Z :=
  dSep_of_unique_path_of_mem huniq (fun h => hG.asymm hmu h.1) hm

/-- The collider `u → m ← v` in an acyclic graph, when it is the unique skeleton path between
`u` and `v`, is blocked when neither `m` nor any descendant of `m` is conditioned on. -/
theorem IsAcyclic.dSep_of_unique_path_collider (hG : G.IsAcyclic)
    (huniq : ∀ q : G.skeleton.Walk u v, q.IsPath → q.support = [u, m, v])
    (hum : G.Adj u m) (hvm : G.Adj v m) (hm : m ∉ G.ancestorsOf Z) : G.DSep {u} {v} Z :=
  dSep_of_unique_path_of_notMem_ancestorsOf huniq (hG.asymm hum) (hG.asymm hvm) hm

/-! ### Ancestral reduction -/

/-- Every vertex of an active trail from `x` to `y` given `Z` is an ancestor of `x`, of `y`, or
of a member of `Z`. -/
theorem ActiveTrail.mem_ancestorsOf_pair (p : G.ActiveTrail Z a x y l) :
    ∀ t ∈ l, t ∈ G.ancestorsOf ({x, y} ∪ Z) := by
  intro t ht
  rcases p.mem_ancestorsOf t ht with h | ⟨-, h⟩
  · refine ancestorsOf_mono ?_ h
    rintro s (hs | hs)
    · exact Or.inl (Or.inr hs)
    · exact Or.inr hs
  · refine ancestorsOf_mono ?_ h
    intro s hs
    exact Or.inl (Or.inl hs)

/-- An active trail of `G` all of whose vertices lie in `S` is an active trail of
`G.restrict S`, provided restricting to `S` does not shrink the ancestral closure of `Z`. -/
theorem ActiveTrail.restrict (p : G.ActiveTrail Z a u w l) (hl : ∀ t ∈ l, t ∈ S)
    (hZ : G.ancestorsOf Z ⊆ (G.restrict S).ancestorsOf Z) :
    (G.restrict S).ActiveTrail Z a u w l := by
  induction p with
  | nil hv => exact .nil hv
  | fwd h hu q ih =>
    exact .fwd ⟨h, hl _ List.mem_cons_self, hl _ (List.mem_cons_of_mem _ q.head_mem)⟩ hu
      (ih fun t ht => hl t (List.mem_cons_of_mem _ ht))
  | bwd h hu q ih =>
    exact .bwd ⟨h, hl _ (List.mem_cons_of_mem _ q.head_mem), hl _ List.mem_cons_self⟩ hu
      (ih fun t ht => hl t (List.mem_cons_of_mem _ ht))
  | collider h hu q ih =>
    exact .collider ⟨h, hl _ (List.mem_cons_of_mem _ q.head_mem), hl _ List.mem_cons_self⟩
      (hZ hu) (ih fun t ht => hl t (List.mem_cons_of_mem _ ht))

/-- **Ancestral reduction.** If `S` is ancestral and contains `X ∪ Y ∪ Z`, then d-separation of
`X` and `Y` by `Z` is the same in `G` and in the subgraph `G.restrict S` that keeps only the
edges inside `S`. The direction from `G` is `Digraph.DSep.restrict`; for the converse, every
vertex of an active trail is an ancestor of an endpoint or of `Z`, hence lies in `S`, and the
ancestral closure of `Z` is the same in both graphs. Acyclicity is not needed. -/
theorem dSep_restrict_iff_of_isAncestral (hS : G.IsAncestral S) (h : X ∪ Y ∪ Z ⊆ S) :
    (G.restrict S).DSep X Y Z ↔ G.DSep X Y Z := by
  refine ⟨fun hsep hconn => hsep ?_, DSep.restrict⟩
  obtain ⟨x, hx, y, hy, l, hl⟩ := dConn_iff_dConnTrail.1 hconn
  have hlS : ∀ t ∈ l, t ∈ S := by
    intro t ht
    refine hS.ancestorsOf_subset ?_ (hl.mem_ancestorsOf_pair t ht)
    rintro s ((rfl | rfl) | hs)
    · exact h (Or.inl (Or.inl hx))
    · exact h (Or.inl (Or.inr hy))
    · exact h (Or.inr hs)
  have hZ : G.ancestorsOf Z ⊆ (G.restrict S).ancestorsOf Z :=
    (ancestorsOf_restrict_of_subset
      (hS.ancestorsOf_subset fun z hz => h (Or.inr hz))).ge
  exact dConn_iff_dConnTrail.2 ⟨x, hx, y, hy, l, hl.restrict hlS hZ⟩

/-- Reachability in `G.restrict S` from a vertex of `S` stays in `S`. -/
theorem mem_of_reflTransGen_restrict (h : ReflTransGen (G.restrict S).Adj u w) (hu : u ∈ S) :
    w ∈ S := by
  rcases h.cases_tail with rfl | ⟨c, -, hcw⟩
  · exact hu
  · exact hcw.2.2

/-- The ancestral closure in the induced subgraph corresponds to the ancestral closure in the
restricted graph. -/
theorem mem_induce_ancestorsOf_iff {v : S} :
    v ∈ (G.induce S).ancestorsOf (Subtype.val ⁻¹' Z) ↔ v.val ∈ (G.restrict S).ancestorsOf Z := by
  constructor
  · rintro ⟨z, hz, hvz⟩
    exact ⟨z.val, hz, induce_reflTransGen_iff.1 hvz⟩
  · rintro ⟨z, hz, hvz⟩
    have hzS := mem_of_reflTransGen_restrict hvz v.2
    exact ⟨⟨z, hzS⟩, hz, induce_reflTransGen_iff.2 hvz⟩

/-- The Bayes-ball state graph of the induced subgraph is the Bayes-ball state graph of the
restricted graph on the states with vertex in `S`. -/
theorem induce_bayesBall_adj_iff {s t : S × Bool} :
    ((G.induce S).bayesBall (Subtype.val ⁻¹' Z)).Adj s t ↔
      ((G.restrict S).bayesBall Z).Adj (s.1.val, s.2) (t.1.val, t.2) := by
  obtain ⟨⟨v, hv⟩, b⟩ := s
  obtain ⟨⟨w, hw⟩, c⟩ := t
  cases c
  · cases b
    · simp [hv, hw]
    · simp only [bayesBall_adj_true_false, induce_adj, restrict_adj, hv, hw, and_true,
        mem_induce_ancestorsOf_iff]
  · simp [hv, hw]

/-- A path of the restricted Bayes-ball state graph that starts in `S` stays in `S` and is a
path of the induced Bayes-ball state graph. -/
theorem exists_reflTransGen_induce_bayesBall {s t : V × Bool}
    (h : ReflTransGen ((G.restrict S).bayesBall Z).Adj s t) (hs : s.1 ∈ S) :
    ∃ ht : t.1 ∈ S, ReflTransGen ((G.induce S).bayesBall (Subtype.val ⁻¹' Z)).Adj
      (⟨s.1, hs⟩, s.2) (⟨t.1, ht⟩, t.2) := by
  induction h with
  | refl => exact ⟨hs, ReflTransGen.refl⟩
  | @tail t₁ t₂ _ h₁₂ ih =>
    obtain ⟨h₁, ih⟩ := ih
    have h₂ : t₂.1 ∈ S := by
      obtain ⟨hedge, -⟩ := h₁₂
      split at hedge
      · exact hedge.2.2
      · exact hedge.2.1
    exact ⟨h₂, ih.tail (induce_bayesBall_adj_iff.2 h₁₂)⟩

/-- d-separation in the induced subgraph `G.induce S`, for the subtype preimages of `X`, `Y`,
`Z`, is d-separation in `G.restrict S`, when `X` lies in `S`. Nothing is assumed of `Y` and
`Z`: a trail of `G.restrict S` from a vertex of `S` stays in `S`. The hypothesis on `X` is
needed: a vertex of `X ∩ Y` outside `S ∪ Z` connects `X` and `Y` in `G.restrict S` by the
trivial trail, but is not a vertex of `G.induce S`. -/
theorem dSep_induce_iff_restrict (hX : X ⊆ S) :
    (G.induce S).DSep (Subtype.val ⁻¹' X) (Subtype.val ⁻¹' Y) (Subtype.val ⁻¹' Z) ↔
      (G.restrict S).DSep X Y Z := by
  refine not_congr ⟨?_, ?_⟩
  · rintro ⟨x, hx, y, hy, hxZ, hyZ, b, hxy⟩
    exact ⟨x.val, hx, y.val, hy, hxZ, hyZ, b, hxy.lift
      (fun s : S × Bool => (s.1.val, s.2)) (fun _ _ h => induce_bayesBall_adj_iff.1 h)⟩
  · rintro ⟨x, hx, y, hy, hxZ, hyZ, b, hxy⟩
    obtain ⟨hyS, h⟩ := exists_reflTransGen_induce_bayesBall hxy (hX hx)
    exact ⟨⟨x, hX hx⟩, hx, ⟨y, hyS⟩, hy, hxZ, hyZ, b, h⟩

/-- **Ancestral reduction to the induced subgraph.** If `S` is ancestral and contains
`X ∪ Y ∪ Z`, then `X` and `Y` are d-separated by `Z` in `G` exactly when their subtype
preimages are d-separated in the induced subgraph `G.induce S`. -/
theorem dSep_induce_iff_of_isAncestral (hS : G.IsAncestral S) (h : X ∪ Y ∪ Z ⊆ S) :
    (G.induce S).DSep (Subtype.val ⁻¹' X) (Subtype.val ⁻¹' Y) (Subtype.val ⁻¹' Z) ↔
      G.DSep X Y Z :=
  (dSep_induce_iff_restrict fun _ hx => h (Or.inl (Or.inl hx))).trans
    (dSep_restrict_iff_of_isAncestral hS h)

/-! ### The intersection property -/

/-- One step of the state graph given `Z` is a step given `Z ∪ U`, when the vertex it leaves
is in `U` only if it is in `Z`. -/
theorem bayesBall_adj_union_of {U : Set V} {s t : V × Bool} (hs : s.1 ∈ U → s.1 ∈ Z)
    (h : (G.bayesBall Z).Adj s t) : (G.bayesBall (Z ∪ U)).Adj s t := by
  obtain ⟨hedge, hpass⟩ := h
  refine ⟨hedge, ?_⟩
  unfold Passes at hpass ⊢
  split_ifs at hpass ⊢
  · exact ancestorsOf_mono Set.subset_union_left hpass
  · exact fun h => h.elim hpass fun hU => hpass (hs hU)

/-- The core of the intersection property: an active trail given `Z` from `(x, false)` is
active given both `Z ∪ W` and `Z ∪ Y`, unless it passes through a vertex of `Y \ Z` or of
`W \ Z`; the part of the trail before the first such vertex is active given `Z ∪ W` and given
`Z ∪ Y`. -/
theorem reflTransGen_bayesBall_intersection {x : V} {t : V × Bool}
    (h : ReflTransGen (G.bayesBall Z).Adj (x, false) t) :
    (ReflTransGen (G.bayesBall (Z ∪ W)).Adj (x, false) t ∧
      ReflTransGen (G.bayesBall (Z ∪ Y)).Adj (x, false) t) ∨
    (∃ y ∈ Y, y ∉ Z ∧ ∃ c, ReflTransGen (G.bayesBall (Z ∪ W)).Adj (x, false) (y, c)) ∨
    (∃ w ∈ W, w ∉ Z ∧ ∃ c, ReflTransGen (G.bayesBall (Z ∪ Y)).Adj (x, false) (w, c)) := by
  induction h with
  | refl => exact Or.inl ⟨ReflTransGen.refl, ReflTransGen.refl⟩
  | @tail t₁ t₂ _ h₁₂ ih =>
    rcases ih with ⟨hW, hY⟩ | ih | ih
    · obtain ⟨u, f⟩ := t₁
      by_cases huY : u ∈ Y ∧ u ∉ Z
      · exact Or.inr (Or.inl ⟨u, huY.1, huY.2, f, hW⟩)
      by_cases huW : u ∈ W ∧ u ∉ Z
      · exact Or.inr (Or.inr ⟨u, huW.1, huW.2, f, hY⟩)
      exact Or.inl ⟨hW.tail (bayesBall_adj_union_of
          (fun hu => by_contra fun hz => huW ⟨hu, hz⟩) h₁₂),
        hY.tail (bayesBall_adj_union_of (fun hu => by_contra fun hz => huY ⟨hu, hz⟩) h₁₂)⟩
    · exact Or.inr (Or.inl ih)
    · exact Or.inr (Or.inr ih)

/-- **The intersection property** of d-separation: if `X` is d-separated from `Y` by `Z ∪ W`
and from `W` by `Z ∪ Y`, then `X` is d-separated from `Y ∪ W` by `Z`. With weak union and
contraction (`Digraph.DSep.weak_union`, `Digraph.DSep.contraction`) it makes d-separation a
graphoid. The hypothesis `Y ∩ W ⊆ Z` replaces the disjointness of the textbook statement and
cannot be dropped under the total convention for overlapping sets
(`CausalInference.DSeparationLemmasExamples.dSep_intersection_needs_disjoint`). Acyclicity is
not needed. -/
theorem DSep.intersection (hYW : Y ∩ W ⊆ Z) (h₁ : G.DSep X Y (Z ∪ W))
    (h₂ : G.DSep X W (Z ∪ Y)) : G.DSep X (Y ∪ W) Z := by
  rintro ⟨x, hx, t, ht, hxZ, htZ, b, hxt⟩
  have hnW : ∀ y ∈ Y, y ∉ Z → y ∉ Z ∪ W := fun y hy hyZ h =>
    h.elim hyZ fun hyW => hyZ (hYW ⟨hy, hyW⟩)
  have hnY : ∀ w ∈ W, w ∉ Z → w ∉ Z ∪ Y := fun w hw hwZ h =>
    h.elim hwZ fun hwY => hwZ (hYW ⟨hwY, hw⟩)
  by_cases hxY : x ∈ Y
  · exact h₁ (dConn_of_mem_inter hx hxY (hnW x hxY hxZ))
  by_cases hxW : x ∈ W
  · exact h₂ (dConn_of_mem_inter hx hxW (hnY x hxW hxZ))
  have hxZW : x ∉ Z ∪ W := fun h => h.elim hxZ hxW
  have hxZY : x ∉ Z ∪ Y := fun h => h.elim hxZ hxY
  rcases reflTransGen_bayesBall_intersection (Y := Y) (W := W) hxt with
    ⟨hW, hY⟩ | ⟨y, hy, hyZ, c, hxy⟩ | ⟨w, hw, hwZ, c, hxw⟩
  · rcases ht with htY | htW
    · exact h₁ ⟨x, hx, t, htY, hxZW, hnW t htY htZ, b, hW⟩
    · exact h₂ ⟨x, hx, t, htW, hxZY, hnY t htW htZ, b, hY⟩
  · exact h₁ ⟨x, hx, y, hy, hxZW, hnW y hy hyZ, c, hxy⟩
  · exact h₂ ⟨x, hx, w, hw, hxZY, hnY w hw hwZ, c, hxw⟩

end Digraph

namespace CausalInference.DSeparationLemmasExamples

open GraphExamples

/-- The intersection property needs `Y ∩ W ⊆ Z`. In the chain `0 → 1 → 2`, take `X = {0}`,
`Y = W = {1}` and `Z = ∅`. Both premises hold because the endpoint `1` lies in the conditioning
set `{1}`, but `0` and `1` are adjacent, hence d-connected given `∅`. -/
theorem dSep_intersection_needs_disjoint :
    ∃ X Y W Z : Set (Fin 3), chain.DSep X Y (Z ∪ W) ∧ chain.DSep X W (Z ∪ Y) ∧
      ¬ chain.DSep X (Y ∪ W) Z :=
  ⟨{0}, {1}, {1}, ∅, by decide, by decide, by decide⟩

end CausalInference.DSeparationLemmasExamples
