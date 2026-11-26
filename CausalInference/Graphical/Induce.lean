/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Graphical.TopologicalOrder

/-!
# Induced subgraphs on a subtype

`Digraph.restrict G S` keeps the vertex type, so every vertex outside `S` survives as an isolated
vertex. The induced subgraph `Digraph.induce G S : Digraph S` instead has exactly the vertices of
`S`, with the edges of `G` between them. The pinned Mathlib has no `Digraph.induce` or
`Digraph.comap`, so it is defined here.

## Main definitions

* `Digraph.induce G S`: the subgraph of `G` induced on `S`, on the vertex type `S`.

## Main results

* `Digraph.IsAcyclic.induce`: induced subgraphs of acyclic graphs are acyclic.
* `Digraph.induce_isAncestor_iff`: directed paths in `G.induce S` are the directed paths in
  `G.restrict S` between vertices of `S`.
* Parents and children in `G.induce S` are those in `G` that lie in `S`.
* `Digraph.induce_parents_eq_empty_iff`, `Digraph.induce_children_eq_empty_iff`: the sources and
  sinks of `G.induce S` are the relative sources and sinks of `S`, and
  `Digraph.IsAcyclic.exists_induce_parents_eq_empty`,
  `Digraph.IsAcyclic.exists_induce_children_eq_empty` give their existence for finite nonempty
  `S`.
-/

@[expose] public section

namespace Digraph

open Relation

variable {V : Type*}

/-- The subgraph of `G` induced on `S`: its vertices are the elements of `S`, and `u → v` is an
edge exactly when it is an edge of `G`. -/
def induce (G : Digraph V) (S : Set V) : Digraph S where
  Adj u v := G.Adj u.val v.val

variable {G : Digraph V} {S : Set V}

@[simp] theorem induce_adj {u v : S} : (G.induce S).Adj u v ↔ G.Adj u.val v.val := Iff.rfl

instance decidableRelInduce [DecidableRel G.Adj] : DecidableRel (G.induce S).Adj :=
  fun u v => inferInstanceAs (Decidable (G.Adj u.val v.val))

/-! ### Directed paths -/

/-- A directed path in the induced subgraph is a directed path in `G`. -/
theorem IsAncestor.of_induce {u v : S} (h : (G.induce S).IsAncestor u v) :
    G.IsAncestor u.val v.val :=
  TransGen.lift Subtype.val (fun _ _ h => h) _ _ h

/-- Directed paths in `G.induce S` are the directed paths in `G.restrict S` between vertices of
`S`. -/
theorem induce_isAncestor_iff {u v : S} :
    (G.induce S).IsAncestor u v ↔ (G.restrict S).IsAncestor u.val v.val := by
  constructor
  · intro h
    exact TransGen.lift Subtype.val (fun a b h => ⟨h, a.2, b.2⟩) _ _ h
  · intro h
    have key : ∀ {a b : V}, TransGen (G.restrict S).Adj a b →
        ∀ (ha : a ∈ S) (hb : b ∈ S), (G.induce S).IsAncestor ⟨a, ha⟩ ⟨b, hb⟩ := by
      intro a b hab
      induction hab with
      | single h => exact fun _ _ => TransGen.single h.1
      | tail _ hbc ih => exact fun ha _ => TransGen.tail (ih ha hbc.2.1) hbc.1
    exact key h u.2 v.2

/-- Reachability in `G.induce S` is reachability in `G.restrict S` between vertices of `S`. -/
theorem induce_reflTransGen_iff {u v : S} :
    ReflTransGen (G.induce S).Adj u v ↔ ReflTransGen (G.restrict S).Adj u.val v.val := by
  rw [reflTransGen_iff_eq_or_transGen, reflTransGen_iff_eq_or_transGen, Subtype.ext_iff]
  exact or_congr Iff.rfl induce_isAncestor_iff

/-- The induced subgraph of an acyclic graph is acyclic. -/
theorem IsAcyclic.induce (hG : G.IsAcyclic) : (G.induce S).IsAcyclic :=
  fun v h => hG v.val (IsAncestor.of_induce h)

/-! ### Parents and children -/

@[simp] theorem mem_induce_parents {u v : S} : u ∈ (G.induce S).parents v ↔ u.val ∈ G.parents v :=
  Iff.rfl

@[simp] theorem mem_induce_children {v w : S} :
    w ∈ (G.induce S).children v ↔ w.val ∈ G.children v :=
  Iff.rfl

/-- The parents of `v` in `G.induce S`, viewed in `V`, are its parents in `G` that lie in `S`;
these are also its parents in `G.restrict S`. -/
theorem image_induce_parents (v : S) :
    Subtype.val '' (G.induce S).parents v = G.parents v ∩ S := by
  ext u
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨hu, u.2⟩
  · rintro ⟨hu, huS⟩
    exact ⟨⟨u, huS⟩, hu, rfl⟩

/-- The children of `v` in `G.induce S`, viewed in `V`, are its children in `G` that lie in `S`;
these are also its children in `G.restrict S`. -/
theorem image_induce_children (v : S) :
    Subtype.val '' (G.induce S).children v = G.children v ∩ S := by
  ext w
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨hw, w.2⟩
  · rintro ⟨hw, hwS⟩
    exact ⟨⟨w, hwS⟩, hw, rfl⟩

theorem image_induce_parents_eq_restrict (v : S) :
    Subtype.val '' (G.induce S).parents v = (G.restrict S).parents v.val := by
  rw [image_induce_parents, parents_restrict_of_mem v.2]

theorem image_induce_children_eq_restrict (v : S) :
    Subtype.val '' (G.induce S).children v = (G.restrict S).children v.val := by
  rw [image_induce_children, children_restrict_of_mem v.2]

/-! ### Sources and sinks -/

/-- A vertex is a source of `G.induce S` exactly when none of its parents in `G` lies in `S`. -/
theorem induce_parents_eq_empty_iff (v : S) :
    (G.induce S).parents v = ∅ ↔ Disjoint (G.parents v.val) S := by
  rw [← Set.image_eq_empty (f := Subtype.val), image_induce_parents,
    Set.disjoint_iff_inter_eq_empty]

/-- A vertex is a sink of `G.induce S` exactly when none of its children in `G` lies in `S`. -/
theorem induce_children_eq_empty_iff (v : S) :
    (G.induce S).children v = ∅ ↔ Disjoint (G.children v.val) S := by
  rw [← Set.image_eq_empty (f := Subtype.val), image_induce_children,
    Set.disjoint_iff_inter_eq_empty]

/-- The subgraph of an acyclic graph induced on a finite nonempty set has a source. -/
theorem IsAcyclic.exists_induce_parents_eq_empty (hG : G.IsAcyclic) (hS : S.Finite)
    (hne : S.Nonempty) : ∃ v : S, (G.induce S).parents v = ∅ := by
  obtain ⟨v, hv, hdisj⟩ := hG.exists_mem_disjoint_parents hS hne
  exact ⟨⟨v, hv⟩, (induce_parents_eq_empty_iff _).2 hdisj⟩

/-- The subgraph of an acyclic graph induced on a finite nonempty set has a sink. -/
theorem IsAcyclic.exists_induce_children_eq_empty (hG : G.IsAcyclic) (hS : S.Finite)
    (hne : S.Nonempty) : ∃ v : S, (G.induce S).children v = ∅ := by
  obtain ⟨v, hv, hdisj⟩ := hG.exists_mem_disjoint_children hS hne
  exact ⟨⟨v, hv⟩, (induce_children_eq_empty_iff _).2 hdisj⟩

end Digraph

/-! ### Concrete examples checked by `decide` -/

namespace CausalInference.GraphExamples

/-- The vertex set `{0, 2}` of the chain `0 → 1 → 2`. -/
abbrev chainEnds : Set (Fin 3) := {0, 2}

example : (chain.induce chainEnds).IsAcyclic := by decide
example : ¬ (chain.induce chainEnds).IsAncestor ⟨0, by decide⟩ ⟨2, by decide⟩ := by decide
example : (cycle.induce chainEnds).parentsFinset ⟨0, by decide⟩ = {⟨2, by decide⟩} := by decide

end CausalInference.GraphExamples
