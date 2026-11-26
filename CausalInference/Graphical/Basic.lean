/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Data.Fintype.Basic

/-!
# Parents and children in a directed graph

A causal graph is a Mathlib `Digraph V`, where `G.Adj u v` means that there is an edge `u → v`.
This file defines the parents and the children of a vertex, both as sets and, for a finite vertex
type with decidable adjacency, as finsets.

## Main definitions

* `Digraph.parents G v`: the vertices `u` with an edge `u → v`.
* `Digraph.children G v`: the vertices `w` with an edge `v → w`.
* `Digraph.parentsFinset G v`, `Digraph.childrenFinset G v`: the finite versions.

The terminology follows Pearl (2009), *Causality: Models, Reasoning, and Inference*, 2nd edition.
-/

@[expose] public section

namespace Digraph

variable {V : Type*}

/-- The parents of `v` in `G`: the vertices `u` with an edge `u → v`. -/
def parents (G : Digraph V) (v : V) : Set V := {u | G.Adj u v}

/-- The children of `v` in `G`: the vertices `w` with an edge `v → w`. -/
def children (G : Digraph V) (v : V) : Set V := {w | G.Adj v w}

section Sets

variable {G H : Digraph V} {u v w : V}

@[simp] theorem mem_parents : u ∈ G.parents v ↔ G.Adj u v := Iff.rfl

@[simp] theorem mem_children : w ∈ G.children v ↔ G.Adj v w := Iff.rfl

/-- `u` is a parent of `v` exactly when `v` is a child of `u`. -/
theorem mem_parents_iff_mem_children : u ∈ G.parents v ↔ v ∈ G.children u := Iff.rfl

/-- Parents are monotone in the graph. -/
theorem parents_mono (h : G ≤ H) (v : V) : G.parents v ⊆ H.parents v := fun _ hu => h hu

/-- Children are monotone in the graph. -/
theorem children_mono (h : G ≤ H) (v : V) : G.children v ⊆ H.children v := fun _ hw => h hw

end Sets

section Finset

variable (G : Digraph V) [Fintype V] [DecidableRel G.Adj]

/-- The parents of `v` as a finset, for a finite vertex type with decidable adjacency. -/
def parentsFinset (v : V) : Finset V := Finset.univ.filter (fun u => G.Adj u v)

/-- The children of `v` as a finset, for a finite vertex type with decidable adjacency. -/
def childrenFinset (v : V) : Finset V := Finset.univ.filter (fun w => G.Adj v w)

variable {G}

@[simp] theorem mem_parentsFinset {u v : V} : u ∈ G.parentsFinset v ↔ G.Adj u v := by
  simp [parentsFinset]

@[simp] theorem mem_childrenFinset {v w : V} : w ∈ G.childrenFinset v ↔ G.Adj v w := by
  simp [childrenFinset]

@[simp, norm_cast] theorem coe_parentsFinset (v : V) :
    (G.parentsFinset v : Set V) = G.parents v := by
  ext; simp

@[simp, norm_cast] theorem coe_childrenFinset (v : V) :
    (G.childrenFinset v : Set V) = G.children v := by
  ext; simp

end Finset

end Digraph
