/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Graphical.Closure
public import CausalInference.Graphical.TopologicalOrder
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Acyclic directed mixed graphs

A directed mixed graph on a vertex type `V` has a directed part, a Mathlib `Digraph V` whose
edge `u → v` is `G.directed.Adj u v`, and a bidirected part, a Mathlib `SimpleGraph V` whose
edge `u ↔ v` is `G.bidirected.Adj u v`. Using `SimpleGraph` makes the bidirected part symmetric
and irreflexive by construction and gives access to Mathlib's connectivity API, which the
districts in `CausalInference.Graphical.Districts` reuse.

Acyclicity of the directed part is the separate predicate `ADMG.IsAcyclic`, not a field. The
graph operations (restriction, mutilation, latent projection) are then total functions with no
proof obligations, acyclicity is transported by separate lemmas, and on a finite vertex type it is
decidable, so `decide` can check it. An acyclic directed mixed graph (ADMG) is a value
`G : ADMG V` together with a proof of `G.IsAcyclic`.

## Main definitions

* `CausalInference.ADMG V`: the structure with fields `directed` and `bidirected`.
* `ADMG.IsAcyclic G`: the directed part has no directed cycle.
* `ADMG.ofDigraph D`: the DAG `D` seen as an ADMG with no bidirected edges.
* `ADMG.parents`, `ADMG.children`, `ADMG.IsAncestor`, `ADMG.ancestors`, `ADMG.descendants`,
  `ADMG.ancestorsOf`, `ADMG.descendantsOf`: the directed notions, read off the directed part.
* `ADMG.siblings G v`: the bidirected neighbors of `v`, and its finite version
  `ADMG.siblingsFinset G v`. (A spouse, in Pearl's usage, is a co-parent: a different notion.)
* `ADMG.restrict G S`: the induced sub-ADMG on `S`, on the same vertex type.
* `ADMG.deleteIncoming G X`, `ADMG.deleteOutgoing G X`: the mutilations of Pearl.
* `ADMG.IsAncestral G S`: `S` equals its ancestral closure.
* `ADMG.ancestorsOfFinset G S`: the ancestral closure of a finset, for a finite vertex type.

## Main results

* `ADMG.isAncestral_ancestorsOf`: the ancestral closure of any set is ancestral.
* `ADMG.isAncestral_iff_forall_adj`: a set is ancestral exactly when it contains every parent of
  each of its members.
* `ADMG.IsAcyclic.exists_adj_lt`, `ADMG.IsAcyclic.exists_injective_adj_lt`,
  `ADMG.IsAcyclic.exists_equiv_fin_adj_lt`: a finite acyclic ADMG has a topological order, and
  an enumeration `V ≃ Fin (Fintype.card V)` of its vertices along which every edge increases.
* Each operation preserves acyclicity, and `DecidableRel` instances make the finite decision
  procedures of the directed substrate apply; membership in `G.ancestorsOf S` and
  `G.IsAncestral S` are decidable on a finite vertex type.

Sources: Richardson (2003), *Markov properties for acyclic directed mixed graphs*; Pearl (2009),
*Causality: Models, Reasoning, and Inference*, 2nd edition.
-/

@[expose] public section

namespace CausalInference

/-- A directed mixed graph on `V`: a directed part `directed : Digraph V` (the edge `u → v` is
`directed.Adj u v`) and a bidirected part `bidirected : SimpleGraph V` (the edge `u ↔ v` is
`bidirected.Adj u v`, symmetric and irreflexive). Acyclicity of the directed part is the separate
predicate `ADMG.IsAcyclic`. -/
@[ext]
structure ADMG (V : Type*) where
  /-- The directed edges: `directed.Adj u v` is the edge `u → v`. -/
  directed : Digraph V
  /-- The bidirected edges: `bidirected.Adj u v` is the edge `u ↔ v`. -/
  bidirected : SimpleGraph V

namespace ADMG

open Relation

variable {V : Type*}

/-- An ADMG is acyclic when its directed part has no directed cycle. -/
def IsAcyclic (G : ADMG V) : Prop := G.directed.IsAcyclic

/-- A directed graph seen as a mixed graph with no bidirected edges. A DAG is the ADMG
`ofDigraph D` with `D` acyclic. -/
def ofDigraph (D : Digraph V) : ADMG V := ⟨D, ⊥⟩

/-! ### Directed notions, read off the directed part -/

/-- The parents of `v`: the vertices `u` with a directed edge `u → v`. -/
def parents (G : ADMG V) (v : V) : Set V := G.directed.parents v

/-- The children of `v`: the vertices `w` with a directed edge `v → w`. -/
def children (G : ADMG V) (v : V) : Set V := G.directed.children v

/-- `u` is a strict ancestor of `v`: a directed path with at least one edge from `u` to `v`. -/
def IsAncestor (G : ADMG V) (u v : V) : Prop := G.directed.IsAncestor u v

/-- The strict ancestors of `v` in the directed part. -/
def ancestors (G : ADMG V) (v : V) : Set V := G.directed.ancestors v

/-- The strict descendants of `v` in the directed part. -/
def descendants (G : ADMG V) (v : V) : Set V := G.directed.descendants v

/-- The inclusive ancestral closure of `S` in the directed part. -/
def ancestorsOf (G : ADMG V) (S : Set V) : Set V := G.directed.ancestorsOf S

/-- The inclusive descendant closure of `S` in the directed part. -/
def descendantsOf (G : ADMG V) (S : Set V) : Set V := G.directed.descendantsOf S

/-- The siblings of `v`: the vertices `w` with a bidirected edge `v ↔ w`. These are not the
spouses of `v`: in Pearl's usage a spouse is a co-parent, a vertex sharing a child with `v`. -/
def siblings (G : ADMG V) (v : V) : Set V := G.bidirected.neighborSet v

/-- A set `S` is ancestral when it equals its ancestral closure: every ancestor of a member of
`S` is in `S`. -/
def IsAncestral (G : ADMG V) (S : Set V) : Prop := G.ancestorsOf S = S

section Basic

variable {G : ADMG V} {D : Digraph V} {u v w : V} {S : Set V}

@[simp] theorem mem_parents : u ∈ G.parents v ↔ G.directed.Adj u v := Iff.rfl

@[simp] theorem mem_children : w ∈ G.children v ↔ G.directed.Adj v w := Iff.rfl

theorem isAncestor_iff : G.IsAncestor u v ↔ G.directed.IsAncestor u v := Iff.rfl

@[simp] theorem mem_ancestors : u ∈ G.ancestors v ↔ G.IsAncestor u v := Iff.rfl

@[simp] theorem mem_descendants : w ∈ G.descendants v ↔ G.IsAncestor v w := Iff.rfl

@[simp] theorem mem_ancestorsOf :
    u ∈ G.ancestorsOf S ↔ ∃ s ∈ S, ReflTransGen G.directed.Adj u s :=
  Iff.rfl

@[simp] theorem mem_descendantsOf :
    w ∈ G.descendantsOf S ↔ ∃ s ∈ S, ReflTransGen G.directed.Adj s w :=
  Iff.rfl

@[simp] theorem mem_siblings : w ∈ G.siblings v ↔ G.bidirected.Adj v w := Iff.rfl

/-- The sibling relation is symmetric. -/
theorem mem_siblings_comm : w ∈ G.siblings v ↔ v ∈ G.siblings w := G.bidirected.adj_comm v w

/-- No vertex is its own sibling. -/
theorem notMem_siblings_self (v : V) : v ∉ G.siblings v := G.bidirected.loopless.irrefl v

theorem subset_ancestorsOf (S : Set V) : S ⊆ G.ancestorsOf S :=
  Digraph.subset_ancestorsOf S

theorem isAncestral_iff : G.IsAncestral S ↔ G.ancestorsOf S = S := Iff.rfl

/-- An ADMG-ancestral set is an ancestral set of the directed part. -/
theorem isAncestral_iff_directed : G.IsAncestral S ↔ G.directed.IsAncestral S := Iff.rfl

/-- The closure test: `S` is ancestral exactly when every parent of a member of `S` lies in
`S`. -/
theorem isAncestral_iff_forall_adj :
    G.IsAncestral S ↔ ∀ ⦃u v⦄, G.directed.Adj u v → v ∈ S → u ∈ S :=
  Digraph.isAncestral_iff_forall_adj

/-- A set is ancestral exactly when it contains the ancestral closure of itself. -/
theorem isAncestral_iff_subset : G.IsAncestral S ↔ G.ancestorsOf S ⊆ S :=
  ⟨fun h => h.subset, fun h => h.antisymm (subset_ancestorsOf S)⟩

/-- The ancestral closure of any set is ancestral. -/
theorem isAncestral_ancestorsOf (S : Set V) : G.IsAncestral (G.ancestorsOf S) :=
  Digraph.ancestorsOf_ancestorsOf S

/-- An ancestral set contains every parent of each of its members. -/
theorem IsAncestral.mem_of_adj (hS : G.IsAncestral S) (huv : G.directed.Adj u v) (hv : v ∈ S) :
    u ∈ S :=
  hS.subset (Digraph.mem_ancestorsOf_of_adj huv (subset_ancestorsOf S hv))

@[simp] theorem ofDigraph_directed : (ofDigraph D).directed = D := rfl

@[simp] theorem ofDigraph_bidirected : (ofDigraph D).bidirected = ⊥ := rfl

@[simp] theorem isAcyclic_ofDigraph : (ofDigraph D).IsAcyclic ↔ D.IsAcyclic := Iff.rfl

@[simp] theorem siblings_ofDigraph (v : V) : (ofDigraph D).siblings v = ∅ := by
  ext; simp

@[simp] theorem ancestorsOf_ofDigraph (S : Set V) : (ofDigraph D).ancestorsOf S = D.ancestorsOf S :=
  rfl

/-- `ofDigraph` is injective: a mixed graph without bidirected edges determines its DAG. -/
theorem ofDigraph_injective : Function.Injective (ofDigraph : Digraph V → ADMG V) :=
  fun _ _ h => congrArg ADMG.directed h

/-- A mixed graph without bidirected edges is the embedding of its directed part. -/
theorem eq_ofDigraph_of_bidirected_eq_bot (h : G.bidirected = ⊥) : G = ofDigraph G.directed :=
  ADMG.ext rfl h

end Basic

/-! ### Induced sub-ADMG and mutilations -/

/-- The bidirected edges of `H` with both endpoints in `S`, on the same vertex type. -/
def bidirectedRestrict (H : SimpleGraph V) (S : Set V) : SimpleGraph V where
  Adj u v := H.Adj u v ∧ u ∈ S ∧ v ∈ S
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun v h => H.loopless.irrefl v h.1⟩

/-- The induced sub-ADMG on `S`: keep the directed and the bidirected edges with both endpoints
in `S`. The vertex type is unchanged, so vertices outside `S` become isolated. The directed part
is `Digraph.restrict`. -/
def restrict (G : ADMG V) (S : Set V) : ADMG V :=
  ⟨G.directed.restrict S, bidirectedRestrict G.bidirected S⟩

/-- Pearl's graph with a bar over `X`, the graph of the intervention `do(X)`: remove every
directed edge into `X`, and remove every bidirected edge with an endpoint in `X`. A bidirected
edge `u ↔ v` stands for a latent common cause, that is, for arrowheads at both `u` and `v`, so
cutting all arrows into `X` removes it as soon as one endpoint is in `X`. -/
def deleteIncoming (G : ADMG V) (X : Set V) : ADMG V :=
  ⟨G.directed.deleteIncoming X, bidirectedRestrict G.bidirected Xᶜ⟩

/-- Pearl's graph with a bar under `X`: remove every directed edge out of `X`. The bidirected
part is unchanged, since a bidirected edge has arrowheads at both endpoints and no tail. -/
def deleteOutgoing (G : ADMG V) (X : Set V) : ADMG V :=
  ⟨G.directed.deleteOutgoing X, G.bidirected⟩

section Operations

variable {G : ADMG V} {H : SimpleGraph V} {S T X : Set V} {u v : V}

@[simp] theorem bidirectedRestrict_adj :
    (bidirectedRestrict H S).Adj u v ↔ H.Adj u v ∧ u ∈ S ∧ v ∈ S := Iff.rfl

theorem bidirectedRestrict_le : bidirectedRestrict H S ≤ H := fun _ _ h => h.1

@[simp] theorem restrict_directed : (G.restrict S).directed = G.directed.restrict S := rfl

@[simp] theorem restrict_bidirected :
    (G.restrict S).bidirected = bidirectedRestrict G.bidirected S := rfl

@[simp] theorem deleteIncoming_directed :
    (G.deleteIncoming X).directed = G.directed.deleteIncoming X := rfl

@[simp] theorem deleteIncoming_bidirected :
    (G.deleteIncoming X).bidirected = bidirectedRestrict G.bidirected Xᶜ := rfl

@[simp] theorem deleteOutgoing_directed :
    (G.deleteOutgoing X).directed = G.directed.deleteOutgoing X := rfl

@[simp] theorem deleteOutgoing_bidirected : (G.deleteOutgoing X).bidirected = G.bidirected := rfl

/-- Restricting twice restricts to the intersection. -/
@[simp] theorem restrict_restrict : (G.restrict S).restrict T = G.restrict (S ∩ T) := by
  ext u v
  · simp
  · simp only [restrict_bidirected, bidirectedRestrict_adj, Set.mem_inter_iff]
    tauto

@[simp] theorem restrict_univ : G.restrict Set.univ = G := by
  ext <;> simp

@[simp] theorem deleteIncoming_empty : G.deleteIncoming ∅ = G := by
  ext <;> simp

@[simp] theorem deleteOutgoing_empty : G.deleteOutgoing ∅ = G := by
  ext <;> simp

/-- Restriction of a DAG is restriction of its directed part. -/
@[simp] theorem restrict_ofDigraph (D : Digraph V) :
    (ofDigraph D).restrict S = ofDigraph (D.restrict S) := by
  ext <;> simp

@[simp] theorem deleteIncoming_ofDigraph (D : Digraph V) :
    (ofDigraph D).deleteIncoming X = ofDigraph (D.deleteIncoming X) := by
  ext <;> simp

@[simp] theorem deleteOutgoing_ofDigraph (D : Digraph V) :
    (ofDigraph D).deleteOutgoing X = ofDigraph (D.deleteOutgoing X) := rfl

theorem IsAcyclic.restrict (hG : G.IsAcyclic) : (G.restrict S).IsAcyclic :=
  Digraph.IsAcyclic.restrict hG

theorem IsAcyclic.deleteIncoming (hG : G.IsAcyclic) : (G.deleteIncoming X).IsAcyclic :=
  Digraph.IsAcyclic.deleteIncoming hG

theorem IsAcyclic.deleteOutgoing (hG : G.IsAcyclic) : (G.deleteOutgoing X).IsAcyclic :=
  Digraph.IsAcyclic.deleteOutgoing hG

/-- Restricting to a set that contains the ancestral closure of `S` does not change that
closure. -/
theorem ancestorsOf_restrict_of_subset (h : G.ancestorsOf S ⊆ T) :
    (G.restrict T).ancestorsOf S = G.ancestorsOf S :=
  Digraph.ancestorsOf_restrict_of_subset h

/-- After `do(X)`, the set `X` is ancestral. -/
theorem isAncestral_deleteIncoming_self (X : Set V) : (G.deleteIncoming X).IsAncestral X :=
  Digraph.ancestorsOf_deleteIncoming_self X

/-- After `do(X)`, no vertex of `X` has a sibling. -/
theorem siblings_deleteIncoming_of_mem (hv : v ∈ X) : (G.deleteIncoming X).siblings v = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ h => h.2.1 hv

end Operations

/-! ### Topological order -/

/-- A finite acyclic ADMG has a topological order of its directed part. -/
theorem IsAcyclic.exists_adj_lt [Finite V] {G : ADMG V} (hG : G.IsAcyclic) :
    ∃ f : V → ℕ, ∀ ⦃u v⦄, G.directed.Adj u v → f u < f v :=
  Digraph.IsAcyclic.exists_adj_lt hG

/-- A finite acyclic ADMG has an injective topological order of its directed part. -/
theorem IsAcyclic.exists_injective_adj_lt [Finite V] {G : ADMG V} (hG : G.IsAcyclic) :
    ∃ f : V → ℕ, Function.Injective f ∧ ∀ ⦃u v⦄, G.directed.Adj u v → f u < f v :=
  Digraph.IsAcyclic.exists_injective_adj_lt hG

/-- A finite acyclic ADMG has an enumeration `e : V ≃ Fin (Fintype.card V)` of its vertices
along which every directed edge increases. -/
theorem IsAcyclic.exists_equiv_fin_adj_lt [Fintype V] {G : ADMG V} (hG : G.IsAcyclic) :
    ∃ e : V ≃ Fin (Fintype.card V), ∀ ⦃u v⦄, G.directed.Adj u v → e u < e v :=
  Digraph.IsAcyclic.exists_equiv_fin_adj_lt hG

/-! ### Decidability -/

section Decidable

variable (G : ADMG V) (H : SimpleGraph V) (S : Set V)

instance decidableRelBidirectedRestrict [DecidableRel H.Adj] [DecidablePred (· ∈ S)] :
    DecidableRel (bidirectedRestrict H S).Adj :=
  fun u v => inferInstanceAs (Decidable (H.Adj u v ∧ u ∈ S ∧ v ∈ S))

instance decidableRelOfDigraphDirected (D : Digraph V) [DecidableRel D.Adj] :
    DecidableRel (ofDigraph D).directed.Adj :=
  inferInstanceAs (DecidableRel D.Adj)

instance decidableRelOfDigraphBidirected (D : Digraph V) :
    DecidableRel (ofDigraph D).bidirected.Adj :=
  fun _ _ => inferInstanceAs (Decidable False)

instance decidableRelRestrictDirected [DecidableRel G.directed.Adj]
    [DecidablePred (· ∈ S)] : DecidableRel (G.restrict S).directed.Adj :=
  inferInstanceAs (DecidableRel (G.directed.restrict S).Adj)

instance decidableRelRestrictBidirected [DecidableRel G.bidirected.Adj]
    [DecidablePred (· ∈ S)] : DecidableRel (G.restrict S).bidirected.Adj :=
  inferInstanceAs (DecidableRel (bidirectedRestrict G.bidirected S).Adj)

instance decidableRelDeleteIncomingDirected [DecidableRel G.directed.Adj]
    [DecidablePred (· ∈ S)] : DecidableRel (G.deleteIncoming S).directed.Adj :=
  inferInstanceAs (DecidableRel (G.directed.deleteIncoming S).Adj)

instance decidableRelDeleteIncomingBidirected [DecidableRel G.bidirected.Adj]
    [DecidablePred (· ∈ S)] : DecidableRel (G.deleteIncoming S).bidirected.Adj :=
  inferInstanceAs (DecidableRel (bidirectedRestrict G.bidirected Sᶜ).Adj)

instance decidableRelDeleteOutgoingDirected [DecidableRel G.directed.Adj]
    [DecidablePred (· ∈ S)] : DecidableRel (G.deleteOutgoing S).directed.Adj :=
  inferInstanceAs (DecidableRel (G.directed.deleteOutgoing S).Adj)

instance decidableRelDeleteOutgoingBidirected [DecidableRel G.bidirected.Adj] :
    DecidableRel (G.deleteOutgoing S).bidirected.Adj :=
  inferInstanceAs (DecidableRel G.bidirected.Adj)

instance decidableIsAcyclic [Fintype V] [DecidableEq V] [DecidableRel G.directed.Adj] :
    Decidable G.IsAcyclic :=
  inferInstanceAs (Decidable G.directed.IsAcyclic)

instance decidableIsAncestor [Fintype V] [DecidableEq V] [DecidableRel G.directed.Adj]
    (u v : V) : Decidable (G.IsAncestor u v) :=
  inferInstanceAs (Decidable (G.directed.IsAncestor u v))

/-- Membership in the ancestral closure of a decidable set is decidable on a finite vertex
type. -/
instance decidablePredMemAncestorsOf [Fintype V] [DecidableEq V] [DecidableRel G.directed.Adj]
    [DecidablePred (· ∈ S)] : DecidablePred (· ∈ G.ancestorsOf S) :=
  inferInstanceAs (DecidablePred (· ∈ G.directed.ancestorsOf S))

/-- Being ancestral is decidable on a finite vertex type, through the closure test
`isAncestral_iff_forall_adj`. -/
instance decidableIsAncestral [Fintype V] [DecidableEq V] [DecidableRel G.directed.Adj]
    [DecidablePred (· ∈ S)] : Decidable (G.IsAncestral S) :=
  inferInstanceAs (Decidable (G.directed.IsAncestral S))

end Decidable

/-! ### Finite versions -/

section Finite

variable (G : ADMG V) [Fintype V]

/-- The siblings of `v` as a finset: the vertices `w` with a bidirected edge `v ↔ w`. -/
def siblingsFinset [DecidableRel G.bidirected.Adj] (v : V) : Finset V :=
  Finset.univ.filter (G.bidirected.Adj v)

/-- The inclusive ancestral closure of a finset `S` in the directed part. -/
def ancestorsOfFinset [DecidableEq V] [DecidableRel G.directed.Adj] (S : Finset V) : Finset V :=
  G.directed.ancestorsOfFinset S

variable {G}

@[simp] theorem mem_siblingsFinset [DecidableRel G.bidirected.Adj] {v w : V} :
    w ∈ G.siblingsFinset v ↔ G.bidirected.Adj v w := by
  simp [siblingsFinset]

@[simp, norm_cast] theorem coe_siblingsFinset [DecidableRel G.bidirected.Adj] (v : V) :
    (G.siblingsFinset v : Set V) = G.siblings v := by
  ext; simp

@[simp] theorem mem_ancestorsOfFinset [DecidableEq V] [DecidableRel G.directed.Adj]
    {S : Finset V} {u : V} :
    u ∈ G.ancestorsOfFinset S ↔ ∃ s ∈ S, ReflTransGen G.directed.Adj u s :=
  Digraph.mem_ancestorsOfFinset

@[simp, norm_cast] theorem coe_ancestorsOfFinset [DecidableEq V] [DecidableRel G.directed.Adj]
    (S : Finset V) : (G.ancestorsOfFinset S : Set V) = G.ancestorsOf (S : Set V) :=
  Digraph.coe_ancestorsOfFinset S

end Finite

end ADMG

end CausalInference
