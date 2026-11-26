/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Graphical.Mutilation

/-!
# Ancestral closures of sets, ancestral sets, and non-descendants

This file develops the inclusive closures `Digraph.ancestorsOf` and `Digraph.descendantsOf` of a
set of vertices.

## Main definitions

* `Digraph.ancestorsOfFinset G S`, `Digraph.descendantsOfFinset G S`: the closures of a finset,
  for a finite vertex type with decidable adjacency.
* `Digraph.IsAncestral G S`: `S` equals its ancestral closure.
* `Digraph.IsDescendantClosed G S`: `S` equals its descendant closure.
* `Digraph.nonDescendants G v`: the complement of the inclusive descendant closure of `v`.
* `Digraph.nonDescendantsFinset G v`: its finite version.

## Main results

* Decidable membership in `G.ancestorsOf S` and `G.descendantsOf S` for a finite vertex type,
  decidable adjacency, and decidable `S`, usable by `decide`.
* `Digraph.ancestorsOf_eq_union_iUnion_ancestors`: `G.ancestorsOf S = S ∪ ⋃ s ∈ S, G.ancestors s`,
  and `Digraph.ancestorsOf_eq_iUnion_singleton`; likewise for descendants.
* `Digraph.isAncestral_iff_forall_adj`: a set is ancestral exactly when it contains every parent
  of each of its members. Ancestral sets are closed under unions and intersections, and a set is
  ancestral exactly when its complement is descendant closed.
* `Digraph.IsAcyclic.parents_subset_nonDescendants`: in an acyclic graph the parents of `v` are
  non-descendants of `v`.

The non-descendants of a vertex appear in the local Markov property; see Pearl (2009),
*Causality: Models, Reasoning, and Inference*, 2nd edition, and Lauritzen (1996),
*Graphical Models*.
-/

@[expose] public section

namespace Digraph

open Relation

variable {V : Type*}

/-! ### Closures of a set as unions -/

section Sets

variable {G : Digraph V} {S T : Set V} {u v w : V}

/-- The ancestral closure of `S` is `S` together with the strict ancestors of its members. -/
theorem ancestorsOf_eq_union_iUnion_ancestors (S : Set V) :
    G.ancestorsOf S = S ∪ ⋃ s ∈ S, G.ancestors s := by
  ext u
  simp only [mem_ancestorsOf, Set.mem_union, Set.mem_iUnion, mem_ancestors, IsAncestor,
    exists_prop]
  constructor
  · rintro ⟨s, hs, hus⟩
    rcases reflTransGen_iff_eq_or_transGen.1 hus with rfl | h
    · exact Or.inl hs
    · exact Or.inr ⟨s, hs, h⟩
  · rintro (hu | ⟨s, hs, h⟩)
    · exact ⟨u, hu, ReflTransGen.refl⟩
    · exact ⟨s, hs, h.to_reflTransGen⟩

/-- The descendant closure of `S` is `S` together with the strict descendants of its members. -/
theorem descendantsOf_eq_union_iUnion_descendants (S : Set V) :
    G.descendantsOf S = S ∪ ⋃ s ∈ S, G.descendants s := by
  ext w
  simp only [mem_descendantsOf, Set.mem_union, Set.mem_iUnion, mem_descendants, IsAncestor,
    exists_prop]
  constructor
  · rintro ⟨s, hs, hsw⟩
    rcases reflTransGen_iff_eq_or_transGen.1 hsw with rfl | h
    · exact Or.inl hs
    · exact Or.inr ⟨s, hs, h⟩
  · rintro (hw | ⟨s, hs, h⟩)
    · exact ⟨w, hw, ReflTransGen.refl⟩
    · exact ⟨s, hs, h.to_reflTransGen⟩

/-- The ancestral closure of `S` is the union of the ancestral closures of its members. -/
theorem ancestorsOf_eq_iUnion_singleton (S : Set V) :
    G.ancestorsOf S = ⋃ s ∈ S, G.ancestorsOf {s} := by
  ext u
  simp

/-- The descendant closure of `S` is the union of the descendant closures of its members. -/
theorem descendantsOf_eq_iUnion_singleton (S : Set V) :
    G.descendantsOf S = ⋃ s ∈ S, G.descendantsOf {s} := by
  ext w
  simp

end Sets

/-! ### Ancestral and descendant closed sets -/

/-- A set `S` is ancestral in `G` when it equals its ancestral closure: every ancestor of a member
of `S` lies in `S`. -/
def IsAncestral (G : Digraph V) (S : Set V) : Prop := G.ancestorsOf S = S

/-- A set `S` is descendant closed in `G` when it equals its descendant closure: every descendant
of a member of `S` lies in `S`. -/
def IsDescendantClosed (G : Digraph V) (S : Set V) : Prop := G.descendantsOf S = S

section Ancestral

variable {G : Digraph V} {S T : Set V} {u v : V}

theorem isAncestral_iff : G.IsAncestral S ↔ G.ancestorsOf S = S := Iff.rfl

theorem isDescendantClosed_iff : G.IsDescendantClosed S ↔ G.descendantsOf S = S := Iff.rfl

/-- A set is ancestral exactly when its ancestral closure is contained in it. -/
theorem isAncestral_iff_subset : G.IsAncestral S ↔ G.ancestorsOf S ⊆ S :=
  ⟨fun h => h.le, fun h => h.antisymm (subset_ancestorsOf S)⟩

/-- A set is descendant closed exactly when its descendant closure is contained in it. -/
theorem isDescendantClosed_iff_subset : G.IsDescendantClosed S ↔ G.descendantsOf S ⊆ S :=
  ⟨fun h => h.le, fun h => h.antisymm (subset_descendantsOf S)⟩

/-- The closure test for ancestral sets: `S` is ancestral exactly when every parent of a member
of `S` lies in `S`. -/
theorem isAncestral_iff_forall_adj :
    G.IsAncestral S ↔ ∀ ⦃u v⦄, G.Adj u v → v ∈ S → u ∈ S := by
  rw [isAncestral_iff_subset]
  refine ⟨fun h u v huv hv => h (mem_ancestorsOf_of_adj huv (subset_ancestorsOf S hv)), ?_⟩
  rintro h u ⟨s, hs, hus⟩
  induction hus using ReflTransGen.head_induction_on with
  | refl => exact hs
  | head huc _ ih => exact h huc ih

/-- The closure test for descendant closed sets: `S` is descendant closed exactly when every
child of a member of `S` lies in `S`. -/
theorem isDescendantClosed_iff_forall_adj :
    G.IsDescendantClosed S ↔ ∀ ⦃u v⦄, G.Adj u v → u ∈ S → v ∈ S := by
  rw [isDescendantClosed_iff_subset]
  refine ⟨fun h u v huv hu => h (mem_descendantsOf_of_adj huv (subset_descendantsOf S hu)), ?_⟩
  rintro h w ⟨s, hs, hsw⟩
  induction hsw with
  | refl => exact hs
  | tail _ hbc ih => exact h hbc ih

/-- An ancestral set contains the parents of its members. -/
theorem IsAncestral.mem_of_adj (hS : G.IsAncestral S) (huv : G.Adj u v) (hv : v ∈ S) : u ∈ S :=
  isAncestral_iff_forall_adj.1 hS huv hv

/-- A descendant closed set contains the children of its members. -/
theorem IsDescendantClosed.mem_of_adj (hS : G.IsDescendantClosed S) (huv : G.Adj u v)
    (hu : u ∈ S) : v ∈ S :=
  isDescendantClosed_iff_forall_adj.1 hS huv hu

/-- An ancestral set contains the reachability predecessors of its members. -/
theorem IsAncestral.mem_of_reflTransGen (hS : G.IsAncestral S) (huv : ReflTransGen G.Adj u v)
    (hv : v ∈ S) : u ∈ S :=
  hS.le ⟨v, hv, huv⟩

/-- A descendant closed set contains the vertices reachable from its members. -/
theorem IsDescendantClosed.mem_of_reflTransGen (hS : G.IsDescendantClosed S)
    (huv : ReflTransGen G.Adj u v) (hu : u ∈ S) : v ∈ S :=
  hS.le ⟨u, hu, huv⟩

/-- The ancestral closure of any set is ancestral. -/
theorem isAncestral_ancestorsOf (S : Set V) : G.IsAncestral (G.ancestorsOf S) :=
  ancestorsOf_ancestorsOf S

/-- The descendant closure of any set is descendant closed. -/
theorem isDescendantClosed_descendantsOf (S : Set V) :
    G.IsDescendantClosed (G.descendantsOf S) :=
  descendantsOf_descendantsOf S

theorem isAncestral_empty : G.IsAncestral ∅ := ancestorsOf_empty

theorem isDescendantClosed_empty : G.IsDescendantClosed ∅ := descendantsOf_empty

theorem isAncestral_univ : G.IsAncestral Set.univ :=
  isAncestral_iff_subset.2 (Set.subset_univ _)

theorem isDescendantClosed_univ : G.IsDescendantClosed Set.univ :=
  isDescendantClosed_iff_subset.2 (Set.subset_univ _)

/-- A set is ancestral exactly when its complement is descendant closed. -/
theorem isAncestral_compl_iff : G.IsAncestral Sᶜ ↔ G.IsDescendantClosed S := by
  rw [isAncestral_iff_forall_adj, isDescendantClosed_iff_forall_adj]
  exact ⟨fun h u v huv hu => by_contra fun hv => h huv hv hu,
    fun h _ _ huv hv hu => hv (h huv hu)⟩

/-- A set is descendant closed exactly when its complement is ancestral. -/
theorem isDescendantClosed_compl_iff : G.IsDescendantClosed Sᶜ ↔ G.IsAncestral S := by
  rw [← isAncestral_compl_iff, compl_compl]

/-- The union of two ancestral sets is ancestral. -/
theorem IsAncestral.union (hS : G.IsAncestral S) (hT : G.IsAncestral T) :
    G.IsAncestral (S ∪ T) := by
  rw [IsAncestral, ancestorsOf_union, hS, hT]

/-- The intersection of two ancestral sets is ancestral. -/
theorem IsAncestral.inter (hS : G.IsAncestral S) (hT : G.IsAncestral T) :
    G.IsAncestral (S ∩ T) :=
  isAncestral_iff_forall_adj.2 fun _ _ huv hv => ⟨hS.mem_of_adj huv hv.1, hT.mem_of_adj huv hv.2⟩

/-- An indexed union of ancestral sets is ancestral. -/
theorem isAncestral_iUnion {ι : Sort*} {S : ι → Set V} (h : ∀ i, G.IsAncestral (S i)) :
    G.IsAncestral (⋃ i, S i) :=
  isAncestral_iff_forall_adj.2 fun _ _ huv hv =>
    let ⟨i, hi⟩ := Set.mem_iUnion.1 hv
    Set.mem_iUnion.2 ⟨i, (h i).mem_of_adj huv hi⟩

/-- An indexed intersection of ancestral sets is ancestral. -/
theorem isAncestral_iInter {ι : Sort*} {S : ι → Set V} (h : ∀ i, G.IsAncestral (S i)) :
    G.IsAncestral (⋂ i, S i) :=
  isAncestral_iff_forall_adj.2 fun _ _ huv hv =>
    Set.mem_iInter.2 fun i => (h i).mem_of_adj huv (Set.mem_iInter.1 hv i)

/-- The union of two descendant closed sets is descendant closed. -/
theorem IsDescendantClosed.union (hS : G.IsDescendantClosed S) (hT : G.IsDescendantClosed T) :
    G.IsDescendantClosed (S ∪ T) := by
  rw [IsDescendantClosed, descendantsOf_union, hS, hT]

/-- The intersection of two descendant closed sets is descendant closed. -/
theorem IsDescendantClosed.inter (hS : G.IsDescendantClosed S) (hT : G.IsDescendantClosed T) :
    G.IsDescendantClosed (S ∩ T) :=
  isDescendantClosed_iff_forall_adj.2 fun _ _ huv hu =>
    ⟨hS.mem_of_adj huv hu.1, hT.mem_of_adj huv hu.2⟩

/-- An indexed union of descendant closed sets is descendant closed. -/
theorem isDescendantClosed_iUnion {ι : Sort*} {S : ι → Set V}
    (h : ∀ i, G.IsDescendantClosed (S i)) : G.IsDescendantClosed (⋃ i, S i) :=
  isDescendantClosed_iff_forall_adj.2 fun _ _ huv hu =>
    let ⟨i, hi⟩ := Set.mem_iUnion.1 hu
    Set.mem_iUnion.2 ⟨i, (h i).mem_of_adj huv hi⟩

/-- An indexed intersection of descendant closed sets is descendant closed. -/
theorem isDescendantClosed_iInter {ι : Sort*} {S : ι → Set V}
    (h : ∀ i, G.IsDescendantClosed (S i)) : G.IsDescendantClosed (⋂ i, S i) :=
  isDescendantClosed_iff_forall_adj.2 fun _ _ huv hu =>
    Set.mem_iInter.2 fun i => (h i).mem_of_adj huv (Set.mem_iInter.1 hu i)

/-- The ancestral closure of `S` is contained in every ancestral set containing `S`; with
`isAncestral_ancestorsOf` this makes it the smallest ancestral superset of `S`. -/
theorem IsAncestral.ancestorsOf_subset (hT : G.IsAncestral T) (h : S ⊆ T) :
    G.ancestorsOf S ⊆ T :=
  hT ▸ ancestorsOf_mono h

/-- The descendant closure of `S` is contained in every descendant closed set containing `S`. -/
theorem IsDescendantClosed.descendantsOf_subset (hT : G.IsDescendantClosed T) (h : S ⊆ T) :
    G.descendantsOf S ⊆ T :=
  hT ▸ descendantsOf_mono h

end Ancestral

/-! ### Non-descendants -/

/-- The non-descendants of `v`: the vertices not reachable from `v` by a directed path of length
at least zero. In particular `v` is not a non-descendant of itself. -/
def nonDescendants (G : Digraph V) (v : V) : Set V := (G.descendantsOf {v})ᶜ

section NonDescendants

variable {G : Digraph V} {u v : V}

@[simp] theorem mem_nonDescendants : u ∈ G.nonDescendants v ↔ ¬ ReflTransGen G.Adj v u := by
  simp [nonDescendants]

/-- A non-descendant of `v` is a vertex other than `v` that is not a strict descendant of `v`. -/
theorem mem_nonDescendants_iff_ne_and_not_isAncestor :
    u ∈ G.nonDescendants v ↔ u ≠ v ∧ ¬ G.IsAncestor v u := by
  rw [mem_nonDescendants, reflTransGen_iff_eq_or_transGen, not_or, IsAncestor]

/-- A vertex is not a non-descendant of itself. -/
theorem notMem_nonDescendants_self (v : V) : v ∉ G.nonDescendants v :=
  fun h => mem_nonDescendants.1 h ReflTransGen.refl

/-- The non-descendants of `v` form an ancestral set. -/
theorem isAncestral_nonDescendants (v : V) : G.IsAncestral (G.nonDescendants v) :=
  isAncestral_compl_iff.2 (isDescendantClosed_descendantsOf _)

/-- In an acyclic graph the strict ancestors of `v` are non-descendants of `v`. -/
theorem IsAcyclic.ancestors_subset_nonDescendants (hG : G.IsAcyclic) (v : V) :
    G.ancestors v ⊆ G.nonDescendants v := fun _ hu =>
  mem_nonDescendants_iff_ne_and_not_isAncestor.2 ⟨hG.ne_of_isAncestor hu, hG.isAncestor_asymm hu⟩

/-- In an acyclic graph the parents of `v` are non-descendants of `v`. -/
theorem IsAcyclic.parents_subset_nonDescendants (hG : G.IsAcyclic) (v : V) :
    G.parents v ⊆ G.nonDescendants v :=
  (parents_subset_ancestors v).trans (hG.ancestors_subset_nonDescendants v)

end NonDescendants

/-! ### Finite vertex types: decidability and finsets -/

section Finite

variable (G : Digraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Membership in the ancestral closure of a decidable set is decidable on a finite vertex type
with decidable adjacency; it is computed from the saturation `reachFinset`. -/
instance decidablePredMemAncestorsOf (S : Set V) [DecidablePred (· ∈ S)] :
    DecidablePred (· ∈ G.ancestorsOf S) := fun u =>
  decidable_of_iff (∃ s, s ∈ S ∧ s ∈ G.reachFinset u) (by simp)

/-- Membership in the descendant closure of a decidable set is decidable on a finite vertex type
with decidable adjacency; it is computed from the saturation `reachFinset`. -/
instance decidablePredMemDescendantsOf (S : Set V) [DecidablePred (· ∈ S)] :
    DecidablePred (· ∈ G.descendantsOf S) := fun w =>
  decidable_of_iff (∃ s, s ∈ S ∧ w ∈ G.reachFinset s) (by simp)

/-- Being ancestral is decidable, through the closure test `isAncestral_iff_forall_adj`. -/
instance decidableIsAncestral (S : Set V) [DecidablePred (· ∈ S)] :
    Decidable (G.IsAncestral S) :=
  decidable_of_iff _ isAncestral_iff_forall_adj.symm

/-- Being descendant closed is decidable, through `isDescendantClosed_iff_forall_adj`. -/
instance decidableIsDescendantClosed (S : Set V) [DecidablePred (· ∈ S)] :
    Decidable (G.IsDescendantClosed S) :=
  decidable_of_iff _ isDescendantClosed_iff_forall_adj.symm

/-- The inclusive ancestral closure of a finset: the vertices from which some member of `S` is
reachable by a directed path of length at least zero. -/
def ancestorsOfFinset (S : Finset V) : Finset V :=
  Finset.univ.filter fun u => ∃ s ∈ S, s ∈ G.reachFinset u

/-- The inclusive descendant closure of a finset: the vertices reachable from some member of `S`
by a directed path of length at least zero. -/
def descendantsOfFinset (S : Finset V) : Finset V := S.biUnion G.reachFinset

/-- The non-descendants of `v` as a finset. -/
def nonDescendantsFinset (v : V) : Finset V := (G.reachFinset v)ᶜ

variable {G}

@[simp] theorem mem_ancestorsOfFinset {S : Finset V} {u : V} :
    u ∈ G.ancestorsOfFinset S ↔ ∃ s ∈ S, ReflTransGen G.Adj u s := by
  simp [ancestorsOfFinset]

@[simp] theorem mem_descendantsOfFinset {S : Finset V} {w : V} :
    w ∈ G.descendantsOfFinset S ↔ ∃ s ∈ S, ReflTransGen G.Adj s w := by
  simp [descendantsOfFinset]

@[simp] theorem mem_nonDescendantsFinset {u v : V} :
    u ∈ G.nonDescendantsFinset v ↔ ¬ ReflTransGen G.Adj v u := by
  simp [nonDescendantsFinset]

@[simp, norm_cast] theorem coe_ancestorsOfFinset (S : Finset V) :
    (G.ancestorsOfFinset S : Set V) = G.ancestorsOf (S : Set V) := by
  ext; simp

@[simp, norm_cast] theorem coe_descendantsOfFinset (S : Finset V) :
    (G.descendantsOfFinset S : Set V) = G.descendantsOf (S : Set V) := by
  ext; simp

@[simp, norm_cast] theorem coe_nonDescendantsFinset (v : V) :
    (G.nonDescendantsFinset v : Set V) = G.nonDescendants v := by
  ext; simp

end Finite

end Digraph

/-! ### Concrete examples checked by `decide` -/

namespace CausalInference.GraphExamples

example : (0 : Fin 3) ∈ chain.ancestorsOf {2} := by decide
example : (2 : Fin 3) ∉ chain.ancestorsOf {1} := by decide
example : (1 : Fin 3) ∈ fork.descendantsOf {0} := by decide
example : (1 : Fin 3) ∉ collider.descendantsOf {0} := by decide
example : chain.ancestorsOfFinset {1} = {0, 1} := by decide
example : collider.ancestorsOfFinset {2} = {0, 1, 2} := by decide
example : fork.descendantsOfFinset {1, 2} = {1, 2} := by decide
example : chain.descendantsOfFinset {1} = {1, 2} := by decide
example : chain.nonDescendantsFinset 1 = {0} := by decide
example : fork.nonDescendantsFinset 1 = {0, 2} := by decide
example : collider.IsAncestral {0, 1} := by decide
example : ¬ chain.IsAncestral {1, 2} := by decide
example : chain.IsDescendantClosed {1, 2} := by decide

end CausalInference.GraphExamples
