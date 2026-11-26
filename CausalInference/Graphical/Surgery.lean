/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Graphical.Closure

/-!
# Further properties of graph surgery

Complements to the edge deletions `Digraph.deleteIncoming`, `Digraph.deleteOutgoing`, and
`Digraph.restrict`.

## Main results

* Descendant closures under each operation, dual to the ancestral statements, for example
  `Digraph.descendantsOf_deleteIncoming_of_disjoint`.
* `Digraph.ancestorsOf_deleteOutgoing_self`: deleting the outgoing edges of `X` does not change
  the ancestral closure of `X`; dually `Digraph.descendantsOf_deleteIncoming_self`.
* `Digraph.restrict_eq_deleteIncoming_deleteOutgoing`: restriction to `S` deletes the incoming
  and the outgoing edges of the complement of `S`; restriction commutes with both deletions.
* `Digraph.IsAncestral.parents_restrict`: restricting to an ancestral set does not change the
  parents of its members.
* `parentsFinset` and `childrenFinset` after each operation, for example
  `Digraph.parentsFinset_deleteIncoming`.

See Pearl (2009), *Causality: Models, Reasoning, and Inference*, 2nd edition.
-/

@[expose] public section

namespace Digraph

open Relation

variable {V : Type*} {G : Digraph V} {X S T : Set V} {u v w : V}

/-! ### Descendant closures -/

theorem descendantsOf_deleteIncoming_subset (S : Set V) :
    (G.deleteIncoming X).descendantsOf S ⊆ G.descendantsOf S :=
  descendantsOf_mono_graph deleteIncoming_le S

theorem descendantsOf_deleteOutgoing_subset (S : Set V) :
    (G.deleteOutgoing X).descendantsOf S ⊆ G.descendantsOf S :=
  descendantsOf_mono_graph deleteOutgoing_le S

theorem descendantsOf_restrict_subset (S : Set V) :
    (G.restrict T).descendantsOf S ⊆ G.descendantsOf S :=
  descendantsOf_mono_graph restrict_le S

/-- After deleting the incoming edges of `X`, a vertex of `X` outside `S` is not a descendant
of `S`. -/
theorem notMem_descendantsOf_deleteIncoming (hw : w ∈ X) (hwS : w ∉ S) :
    w ∉ (G.deleteIncoming X).descendantsOf S := by
  rintro ⟨s, hs, hsw⟩
  rcases hsw.cases_tail with rfl | ⟨c, _, hcw⟩
  · exact hwS hs
  · exact hcw.2 hw

/-- Deleting the incoming edges of a set `X` that avoids the descendant closure of `S` does not
change that closure. -/
theorem descendantsOf_deleteIncoming_of_disjoint (h : Disjoint X (G.descendantsOf S)) :
    (G.deleteIncoming X).descendantsOf S = G.descendantsOf S :=
  Set.Subset.antisymm (descendantsOf_deleteIncoming_subset S)
    (descendantsOf_subset_descendantsOf_of_adj fun _ _ huw hu =>
      ⟨huw, fun hwX => Set.disjoint_left.1 h hwX (mem_descendantsOf_of_adj huw hu)⟩)

/-- Deleting the outgoing edges of a set `X` that avoids the descendant closure of `S` does not
change that closure. -/
theorem descendantsOf_deleteOutgoing_of_disjoint (h : Disjoint X (G.descendantsOf S)) :
    (G.deleteOutgoing X).descendantsOf S = G.descendantsOf S :=
  Set.Subset.antisymm (descendantsOf_deleteOutgoing_subset S)
    (descendantsOf_subset_descendantsOf_of_adj fun _ _ huw hu =>
      ⟨huw, fun huX => Set.disjoint_left.1 h huX hu⟩)

/-- Restricting to a set `T` that contains the descendant closure of `S` does not change that
closure. -/
theorem descendantsOf_restrict_of_subset (h : G.descendantsOf S ⊆ T) :
    (G.restrict T).descendantsOf S = G.descendantsOf S :=
  Set.Subset.antisymm (descendantsOf_restrict_subset S)
    (descendantsOf_subset_descendantsOf_of_adj fun _ _ huw hu =>
      ⟨huw, h hu, h (mem_descendantsOf_of_adj huw hu)⟩)

/-- Deleting the outgoing edges of `X` does not change the ancestral closure of `X`: a directed
path into `X` can be cut at its first vertex in `X`. -/
theorem ancestorsOf_deleteOutgoing_self (X : Set V) :
    (G.deleteOutgoing X).ancestorsOf X = G.ancestorsOf X := by
  refine Set.Subset.antisymm (ancestorsOf_deleteOutgoing_subset X) ?_
  rintro u ⟨s, hs, hus⟩
  induction hus using ReflTransGen.head_induction_on with
  | refl => exact subset_ancestorsOf X hs
  | @head a c hac _ ih =>
    by_cases ha : a ∈ X
    · exact subset_ancestorsOf X ha
    · exact mem_ancestorsOf_of_adj ⟨hac, ha⟩ ih

/-- Deleting the incoming edges of `X` does not change the descendant closure of `X`: a directed
path out of `X` can be started at its last vertex in `X`. -/
theorem descendantsOf_deleteIncoming_self (X : Set V) :
    (G.deleteIncoming X).descendantsOf X = G.descendantsOf X := by
  refine Set.Subset.antisymm (descendantsOf_deleteIncoming_subset X) ?_
  rintro w ⟨s, hs, hsw⟩
  induction hsw with
  | refl => exact subset_descendantsOf X hs
  | @tail b c _ hbc ih =>
    by_cases hc : c ∈ X
    · exact subset_descendantsOf X hc
    · exact mem_descendantsOf_of_adj ⟨hbc, hc⟩ ih

/-- After deleting the incoming edges of `X`, the set `X` is ancestral. -/
theorem isAncestral_deleteIncoming_self (X : Set V) : (G.deleteIncoming X).IsAncestral X :=
  ancestorsOf_deleteIncoming_self X

/-- After deleting the outgoing edges of `X`, the set `X` is descendant closed. -/
theorem isDescendantClosed_deleteOutgoing_self (X : Set V) :
    (G.deleteOutgoing X).IsDescendantClosed X :=
  descendantsOf_deleteOutgoing_of_subset subset_rfl

/-! ### Restriction and the two deletions -/

/-- Restricting to `S` is deleting the incoming and the outgoing edges of the complement of
`S`. -/
theorem restrict_eq_deleteIncoming_deleteOutgoing (S : Set V) :
    G.restrict S = (G.deleteIncoming Sᶜ).deleteOutgoing Sᶜ := by
  ext u v
  simp only [restrict_adj, deleteOutgoing_adj, deleteIncoming_adj, Set.mem_compl_iff, not_not]
  tauto

/-- Restriction commutes with deleting incoming edges. -/
theorem restrict_deleteIncoming :
    (G.deleteIncoming X).restrict S = (G.restrict S).deleteIncoming X := by
  ext u v
  simp only [restrict_adj, deleteIncoming_adj]
  tauto

/-- Restriction commutes with deleting outgoing edges. -/
theorem restrict_deleteOutgoing :
    (G.deleteOutgoing X).restrict S = (G.restrict S).deleteOutgoing X := by
  ext u v
  simp only [restrict_adj, deleteOutgoing_adj]
  tauto

/-- Restricting to an ancestral set does not change the parents of its members. -/
theorem IsAncestral.parents_restrict (hS : G.IsAncestral S) (hv : v ∈ S) :
    (G.restrict S).parents v = G.parents v := by
  rw [parents_restrict_of_mem hv, Set.inter_eq_left]
  exact fun _ hu => hS.mem_of_adj hu hv

/-- Restricting to a descendant closed set does not change the children of its members. -/
theorem IsDescendantClosed.children_restrict (hS : G.IsDescendantClosed S) (hv : v ∈ S) :
    (G.restrict S).children v = G.children v := by
  rw [children_restrict_of_mem hv, Set.inter_eq_left]
  exact fun _ hw => hS.mem_of_adj hw hv

/-- Restricting to an ancestral set `S` keeps the ancestral closure of every subset of `S`. -/
theorem IsAncestral.ancestorsOf_restrict (hS : G.IsAncestral S) (hT : T ⊆ S) :
    (G.restrict S).ancestorsOf T = G.ancestorsOf T :=
  ancestorsOf_restrict_of_subset (hS.ancestorsOf_subset hT)

/-! ### Finite parents and children after surgery -/

section Finset

variable [Fintype V] [DecidableRel G.Adj]

/-- In `G.deleteIncoming X` a vertex of `X` has no parents and any other vertex keeps its
parents. -/
theorem parentsFinset_deleteIncoming [DecidablePred (· ∈ X)] (v : V) :
    (G.deleteIncoming X).parentsFinset v = if v ∈ X then ∅ else G.parentsFinset v := by
  ext u
  split_ifs with hv <;> simp [hv]

theorem childrenFinset_deleteIncoming [DecidablePred (· ∈ X)] (v : V) :
    (G.deleteIncoming X).childrenFinset v = (G.childrenFinset v).filter (· ∉ X) := by
  ext w
  simp

theorem parentsFinset_deleteOutgoing [DecidablePred (· ∈ X)] (v : V) :
    (G.deleteOutgoing X).parentsFinset v = (G.parentsFinset v).filter (· ∉ X) := by
  ext u
  simp

/-- In `G.deleteOutgoing X` a vertex of `X` has no children and any other vertex keeps its
children. -/
theorem childrenFinset_deleteOutgoing [DecidablePred (· ∈ X)] (v : V) :
    (G.deleteOutgoing X).childrenFinset v = if v ∈ X then ∅ else G.childrenFinset v := by
  ext w
  split_ifs with hv <;> simp [hv]

/-- In `G.restrict S` a vertex of `S` keeps its parents in `S`; a vertex outside `S` has
none. -/
theorem parentsFinset_restrict [DecidablePred (· ∈ S)] (v : V) :
    (G.restrict S).parentsFinset v =
      if v ∈ S then (G.parentsFinset v).filter (· ∈ S) else ∅ := by
  ext u
  split_ifs with hv <;> simp [hv, and_comm]

/-- In `G.restrict S` a vertex of `S` keeps its children in `S`; a vertex outside `S` has
none. -/
theorem childrenFinset_restrict [DecidablePred (· ∈ S)] (v : V) :
    (G.restrict S).childrenFinset v =
      if v ∈ S then (G.childrenFinset v).filter (· ∈ S) else ∅ := by
  ext w
  split_ifs with hv <;> simp [hv]

end Finset

end Digraph

/-! ### Concrete examples checked by `decide` -/

namespace CausalInference.GraphExamples

example : (chain.deleteIncoming {2}).descendantsOfFinset {0} = {0, 1} := by decide
example : (chain.deleteOutgoing {1}).ancestorsOfFinset {1} = chain.ancestorsOfFinset {1} := by
  decide
example : (collider.restrict {0, 2}).parentsFinset 2 = {0} := by decide

end CausalInference.GraphExamples
