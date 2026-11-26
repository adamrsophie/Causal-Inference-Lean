/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Graphical.Acyclic

/-!
# Graph surgery

The edge deletions used by interventions and by the rules of the do-calculus. All operations
keep the vertex type and only remove edges.

## Main definitions

* `Digraph.deleteIncoming G X`: remove every edge whose head is in `X`. This is Pearl's graph
  with a bar over `X`, the graph of the intervention `do(X)`.
* `Digraph.deleteOutgoing G X`: remove every edge whose tail is in `X`. This is Pearl's graph
  with a bar under `X`.
* `Digraph.restrict G S`: keep only the edges with both endpoints in `S`.

## Main results

* Each operation gives a subgraph of `G`, hence preserves acyclicity.
* `deleteIncoming` and `deleteOutgoing` commute, compose by union of the deleted sets (so they
  are idempotent), and are antitone in the set.
* The parents and children after each operation, for example
  `Digraph.parents_deleteIncoming_of_mem`: a vertex of `X` has no parents in
  `G.deleteIncoming X`.
* Ancestral closures after each operation, for example
  `Digraph.ancestorsOf_deleteIncoming_of_subset` (cutting the incoming edges of a set `S` makes
  `S` ancestrally closed) and `Digraph.ancestorsOf_deleteIncoming_of_disjoint` (deleting the
  incoming edges of a set that avoids the ancestors of `S` does not change them).
* `DecidableRel` instances, so the finite decision procedures apply to the mutilated graphs.

See Pearl (2009), *Causality: Models, Reasoning, and Inference*, 2nd edition.
-/

@[expose] public section

namespace Digraph

open Relation

variable {V : Type*}

/-- Remove every edge whose head lies in `X`: `u → v` survives exactly when `v ∉ X`. This is
Pearl's graph with a bar over `X`. -/
def deleteIncoming (G : Digraph V) (X : Set V) : Digraph V where
  Adj u v := G.Adj u v ∧ v ∉ X

/-- Remove every edge whose tail lies in `X`: `u → v` survives exactly when `u ∉ X`. This is
Pearl's graph with a bar under `X`. -/
def deleteOutgoing (G : Digraph V) (X : Set V) : Digraph V where
  Adj u v := G.Adj u v ∧ u ∉ X

/-- Keep only the edges with both endpoints in `S`; the vertex type is unchanged. -/
def restrict (G : Digraph V) (S : Set V) : Digraph V where
  Adj u v := G.Adj u v ∧ u ∈ S ∧ v ∈ S

variable {G H : Digraph V} {X Y S T : Set V} {u v w : V}

@[simp] theorem deleteIncoming_adj : (G.deleteIncoming X).Adj u v ↔ G.Adj u v ∧ v ∉ X :=
  Iff.rfl

@[simp] theorem deleteOutgoing_adj : (G.deleteOutgoing X).Adj u v ↔ G.Adj u v ∧ u ∉ X :=
  Iff.rfl

@[simp] theorem restrict_adj : (G.restrict S).Adj u v ↔ G.Adj u v ∧ u ∈ S ∧ v ∈ S := Iff.rfl

/-! ### Subgraph and acyclicity -/

theorem deleteIncoming_le : G.deleteIncoming X ≤ G := fun _ _ h => h.1

theorem deleteOutgoing_le : G.deleteOutgoing X ≤ G := fun _ _ h => h.1

theorem restrict_le : G.restrict S ≤ G := fun _ _ h => h.1

theorem IsAcyclic.deleteIncoming (hG : G.IsAcyclic) : (G.deleteIncoming X).IsAcyclic :=
  hG.anti deleteIncoming_le

theorem IsAcyclic.deleteOutgoing (hG : G.IsAcyclic) : (G.deleteOutgoing X).IsAcyclic :=
  hG.anti deleteOutgoing_le

theorem IsAcyclic.restrict (hG : G.IsAcyclic) : (G.restrict S).IsAcyclic :=
  hG.anti restrict_le

/-! ### Algebra of the operations -/

/-- Deleting incoming and outgoing edges commute. -/
theorem deleteIncoming_deleteOutgoing :
    (G.deleteIncoming X).deleteOutgoing Y = (G.deleteOutgoing Y).deleteIncoming X := by
  ext u v
  simp only [deleteOutgoing_adj, deleteIncoming_adj]
  tauto

/-- Deleting incoming edges twice deletes those into the union. -/
@[simp] theorem deleteIncoming_deleteIncoming :
    (G.deleteIncoming X).deleteIncoming Y = G.deleteIncoming (X ∪ Y) := by
  ext u v
  simp [and_assoc]

/-- Deleting outgoing edges twice deletes those out of the union. -/
@[simp] theorem deleteOutgoing_deleteOutgoing :
    (G.deleteOutgoing X).deleteOutgoing Y = G.deleteOutgoing (X ∪ Y) := by
  ext u v
  simp [and_assoc]

theorem deleteIncoming_idem : (G.deleteIncoming X).deleteIncoming X = G.deleteIncoming X := by
  simp

theorem deleteOutgoing_idem : (G.deleteOutgoing X).deleteOutgoing X = G.deleteOutgoing X := by
  simp

/-- Restricting twice restricts to the intersection. -/
@[simp] theorem restrict_restrict : (G.restrict S).restrict T = G.restrict (S ∩ T) := by
  ext u v
  simp only [restrict_adj, Set.mem_inter_iff]
  tauto

@[simp] theorem deleteIncoming_empty : G.deleteIncoming ∅ = G := by
  ext; simp

@[simp] theorem deleteOutgoing_empty : G.deleteOutgoing ∅ = G := by
  ext; simp

@[simp] theorem restrict_univ : G.restrict Set.univ = G := by
  ext; simp

/-- Deleting the incoming edges of a larger set leaves fewer edges. -/
theorem deleteIncoming_anti (h : X ⊆ Y) : G.deleteIncoming Y ≤ G.deleteIncoming X :=
  fun _ _ huv => ⟨huv.1, fun hv => huv.2 (h hv)⟩

/-- Deleting the outgoing edges of a larger set leaves fewer edges. -/
theorem deleteOutgoing_anti (h : X ⊆ Y) : G.deleteOutgoing Y ≤ G.deleteOutgoing X :=
  fun _ _ huv => ⟨huv.1, fun hu => huv.2 (h hu)⟩

/-- Restricting to a larger set keeps more edges. -/
theorem restrict_mono (h : S ⊆ T) : G.restrict S ≤ G.restrict T :=
  fun _ _ huv => ⟨huv.1, h huv.2.1, h huv.2.2⟩

theorem deleteIncoming_mono_graph (h : G ≤ H) : G.deleteIncoming X ≤ H.deleteIncoming X :=
  fun _ _ huv => ⟨h huv.1, huv.2⟩

theorem deleteOutgoing_mono_graph (h : G ≤ H) : G.deleteOutgoing X ≤ H.deleteOutgoing X :=
  fun _ _ huv => ⟨h huv.1, huv.2⟩

theorem restrict_mono_graph (h : G ≤ H) : G.restrict S ≤ H.restrict S :=
  fun _ _ huv => ⟨h huv.1, huv.2⟩

/-! ### Parents and children -/

/-- A vertex of `X` has no parents in `G.deleteIncoming X`. -/
theorem parents_deleteIncoming_of_mem (hv : v ∈ X) : (G.deleteIncoming X).parents v = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ hu => hu.2 hv

theorem parents_deleteIncoming_of_notMem (hv : v ∉ X) :
    (G.deleteIncoming X).parents v = G.parents v := by
  ext; simp [hv]

theorem children_deleteIncoming (v : V) :
    (G.deleteIncoming X).children v = G.children v \ X := rfl

theorem parents_deleteOutgoing (v : V) :
    (G.deleteOutgoing X).parents v = G.parents v \ X := rfl

/-- A vertex of `X` has no children in `G.deleteOutgoing X`. -/
theorem children_deleteOutgoing_of_mem (hv : v ∈ X) : (G.deleteOutgoing X).children v = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ hw => hw.2 hv

theorem children_deleteOutgoing_of_notMem (hv : v ∉ X) :
    (G.deleteOutgoing X).children v = G.children v := by
  ext; simp [hv]

theorem parents_restrict_of_mem (hv : v ∈ S) : (G.restrict S).parents v = G.parents v ∩ S := by
  ext; simp [hv]

theorem parents_restrict_of_notMem (hv : v ∉ S) : (G.restrict S).parents v = ∅ := by
  ext; simp [hv]

theorem children_restrict_of_mem (hv : v ∈ S) :
    (G.restrict S).children v = G.children v ∩ S := by
  ext; simp [hv]

theorem children_restrict_of_notMem (hv : v ∉ S) : (G.restrict S).children v = ∅ := by
  ext; simp [hv]

/-! ### Ancestral closures -/

theorem ancestorsOf_deleteIncoming_subset (S : Set V) :
    (G.deleteIncoming X).ancestorsOf S ⊆ G.ancestorsOf S :=
  ancestorsOf_mono_graph deleteIncoming_le S

theorem ancestorsOf_deleteOutgoing_subset (S : Set V) :
    (G.deleteOutgoing X).ancestorsOf S ⊆ G.ancestorsOf S :=
  ancestorsOf_mono_graph deleteOutgoing_le S

theorem ancestorsOf_restrict_subset (S : Set V) :
    (G.restrict T).ancestorsOf S ⊆ G.ancestorsOf S :=
  ancestorsOf_mono_graph restrict_le S

/-- After deleting the incoming edges of `X`, a subset `S` of `X` is its own ancestral closure:
no vertex outside `S` has a directed path into `S`. -/
theorem ancestorsOf_deleteIncoming_of_subset (h : S ⊆ X) :
    (G.deleteIncoming X).ancestorsOf S = S := by
  refine Set.Subset.antisymm ?_ (subset_ancestorsOf S)
  rintro u ⟨s, hs, hus⟩
  rcases hus.cases_tail with rfl | ⟨c, _, hcs⟩
  · exact hs
  · exact absurd (h hs) hcs.2

/-- After deleting the incoming edges of `X`, the set `X` is its own ancestral closure. -/
theorem ancestorsOf_deleteIncoming_self (X : Set V) : (G.deleteIncoming X).ancestorsOf X = X :=
  ancestorsOf_deleteIncoming_of_subset subset_rfl

/-- Deleting the incoming edges of a set `X` that avoids the ancestral closure of `S` does not
change that closure. -/
theorem ancestorsOf_deleteIncoming_of_disjoint (h : Disjoint X (G.ancestorsOf S)) :
    (G.deleteIncoming X).ancestorsOf S = G.ancestorsOf S :=
  Set.Subset.antisymm (ancestorsOf_deleteIncoming_subset S)
    (ancestorsOf_subset_ancestorsOf_of_adj fun _ _ huw hw =>
      ⟨huw, fun hwX => Set.disjoint_left.1 h hwX hw⟩)

/-- Deleting the outgoing edges of a set `X` that avoids the ancestral closure of `S` does not
change that closure. -/
theorem ancestorsOf_deleteOutgoing_of_disjoint (h : Disjoint X (G.ancestorsOf S)) :
    (G.deleteOutgoing X).ancestorsOf S = G.ancestorsOf S :=
  Set.Subset.antisymm (ancestorsOf_deleteOutgoing_subset S)
    (ancestorsOf_subset_ancestorsOf_of_adj fun _ _ huw hw =>
      ⟨huw, fun huX => Set.disjoint_left.1 h huX (mem_ancestorsOf_of_adj huw hw)⟩)

/-- After deleting the outgoing edges of `X`, a vertex of `X` outside `S` is not an ancestor
of `S`. -/
theorem notMem_ancestorsOf_deleteOutgoing (hu : u ∈ X) (huS : u ∉ S) :
    u ∉ (G.deleteOutgoing X).ancestorsOf S := by
  rintro ⟨s, hs, hus⟩
  rcases hus.cases_head with rfl | ⟨c, huc, _⟩
  · exact huS hs
  · exact huc.2 hu

/-- After deleting the outgoing edges of `X`, a subset `S` of `X` is its own descendant
closure. -/
theorem descendantsOf_deleteOutgoing_of_subset (h : S ⊆ X) :
    (G.deleteOutgoing X).descendantsOf S = S := by
  refine Set.Subset.antisymm ?_ (subset_descendantsOf S)
  rintro w ⟨s, hs, hsw⟩
  rcases hsw.cases_head with rfl | ⟨c, hsc, _⟩
  · exact hs
  · exact absurd (h hs) hsc.2

/-- Restricting to a set `T` that contains the ancestral closure of `S` does not change that
closure. -/
theorem ancestorsOf_restrict_of_subset (h : G.ancestorsOf S ⊆ T) :
    (G.restrict T).ancestorsOf S = G.ancestorsOf S :=
  Set.Subset.antisymm (ancestorsOf_restrict_subset S)
    (ancestorsOf_subset_ancestorsOf_of_adj fun _ _ huw hw =>
      ⟨huw, h (mem_ancestorsOf_of_adj huw hw), h hw⟩)

/-! ### Decidability -/

instance decidableRelDeleteIncoming [DecidableRel G.Adj] [DecidablePred (· ∈ X)] :
    DecidableRel (G.deleteIncoming X).Adj :=
  fun u v => inferInstanceAs (Decidable (G.Adj u v ∧ v ∉ X))

instance decidableRelDeleteOutgoing [DecidableRel G.Adj] [DecidablePred (· ∈ X)] :
    DecidableRel (G.deleteOutgoing X).Adj :=
  fun u v => inferInstanceAs (Decidable (G.Adj u v ∧ u ∉ X))

instance decidableRelRestrict [DecidableRel G.Adj] [DecidablePred (· ∈ S)] :
    DecidableRel (G.restrict S).Adj :=
  fun u v => inferInstanceAs (Decidable (G.Adj u v ∧ u ∈ S ∧ v ∈ S))

end Digraph

/-! ### Concrete examples checked by `decide` -/

namespace CausalInference.GraphExamples

example : ¬ (chain.deleteIncoming {1}).IsAncestor 0 2 := by decide
example : (chain.deleteIncoming {1}).parentsFinset 1 = ∅ := by decide
example : (chain.deleteOutgoing {0}).ancestorsFinset 2 = {1} := by decide
example : (collider.deleteOutgoing {0}).parentsFinset 2 = {1} := by decide
example : (cycle.deleteIncoming {0}).IsAcyclic := by decide
example : (cycle.restrict {0, 1}).IsAcyclic := by decide
example : (fork.restrict {1, 2}).childrenFinset 0 = ∅ := by decide

end CausalInference.GraphExamples
