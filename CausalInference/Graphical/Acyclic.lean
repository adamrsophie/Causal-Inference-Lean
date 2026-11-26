/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Graphical.Ancestry
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Fintype.Lattice

/-!
# Directed acyclic graphs

A digraph is acyclic when no vertex is a strict ancestor of itself, that is, when there is no
directed cycle (self-loops count as cycles of length one).

## Main definitions

* `Digraph.IsAcyclic G`: `∀ v, ¬ Relation.TransGen G.Adj v v`.

## Main results

* `Digraph.IsAcyclic.irrefl`, `Digraph.IsAcyclic.asymm`: an acyclic graph has no self-loops and
  no pair of opposite edges.
* `Digraph.IsAcyclic.anti`: a subgraph of an acyclic graph is acyclic.
* `Digraph.IsAcyclic.isStrictOrder`: in an acyclic graph the ancestor relation is a strict
  partial order.
* `Digraph.isAcyclic_iff_exists_adj_lt`: a graph on a finite vertex type is acyclic if and only
  if it has a topological order `f : V → ℕ`, meaning `G.Adj u v → f u < f v`.
* `Digraph.IsAcyclic.exists_parents_eq_empty`, `Digraph.IsAcyclic.exists_children_eq_empty`:
  a nonempty finite acyclic graph has a source and a sink.
* `Decidable G.IsAcyclic` on a finite vertex type, usable by `decide`.

See Pearl (2009), *Causality: Models, Reasoning, and Inference*, 2nd edition.
-/

@[expose] public section

namespace Digraph

open Relation

variable {V : Type*}

/-- A digraph is acyclic when it has no directed cycle: no vertex reaches itself by a directed
path with at least one edge. -/
def IsAcyclic (G : Digraph V) : Prop := ∀ v, ¬ TransGen G.Adj v v

variable {G H : Digraph V} {u v : V}

theorem isAcyclic_iff_forall_not_isAncestor : G.IsAcyclic ↔ ∀ v, ¬ G.IsAncestor v v := Iff.rfl

/-- In an acyclic graph no vertex is a strict ancestor of itself. -/
theorem IsAcyclic.not_isAncestor_self (hG : G.IsAcyclic) (v : V) : ¬ G.IsAncestor v v := hG v

/-- In an acyclic graph no vertex belongs to its own strict ancestors. -/
theorem IsAcyclic.notMem_ancestors_self (hG : G.IsAcyclic) (v : V) : v ∉ G.ancestors v := hG v

/-- In an acyclic graph no vertex belongs to its own strict descendants. -/
theorem IsAcyclic.notMem_descendants_self (hG : G.IsAcyclic) (v : V) : v ∉ G.descendants v :=
  hG v

/-- An acyclic graph has no self-loops. -/
theorem IsAcyclic.irrefl (hG : G.IsAcyclic) (v : V) : ¬ G.Adj v v :=
  fun h => hG v (TransGen.single h)

/-- An acyclic graph has no pair of opposite edges. -/
theorem IsAcyclic.asymm (hG : G.IsAcyclic) (huv : G.Adj u v) : ¬ G.Adj v u :=
  fun hvu => hG u (TransGen.head huv (TransGen.single hvu))

/-- The two endpoints of an edge in an acyclic graph are distinct. -/
theorem IsAcyclic.ne_of_adj (hG : G.IsAcyclic) (huv : G.Adj u v) : u ≠ v := by
  rintro rfl
  exact hG.irrefl u huv

/-- A strict ancestor in an acyclic graph is a different vertex. -/
theorem IsAcyclic.ne_of_isAncestor (hG : G.IsAcyclic) (huv : G.IsAncestor u v) : u ≠ v := by
  rintro rfl
  exact hG u huv

/-- The ancestor relation of an acyclic graph is asymmetric. -/
theorem IsAcyclic.isAncestor_asymm (hG : G.IsAcyclic) (huv : G.IsAncestor u v) :
    ¬ G.IsAncestor v u :=
  fun hvu => hG u (huv.trans hvu)

/-- A subgraph of an acyclic graph is acyclic. -/
theorem IsAcyclic.anti (hHG : H ≤ G) (hG : G.IsAcyclic) : H.IsAcyclic :=
  fun v h => hG v (IsAncestor.mono hHG h)

/-- In an acyclic graph the ancestor relation is a strict partial order (irreflexive and
transitive, hence asymmetric). -/
theorem IsAcyclic.isStrictOrder (hG : G.IsAcyclic) : IsStrictOrder V G.IsAncestor where
  irrefl := hG
  trans _ _ _ := IsAncestor.trans

/-- A graph that admits a strictly increasing labeling along its edges, into any preorder, is
acyclic. No finiteness is needed for this direction. -/
theorem isAcyclic_of_adj_lt {α : Type*} [Preorder α] (f : V → α)
    (hf : ∀ ⦃u v⦄, G.Adj u v → f u < f v) : G.IsAcyclic := by
  have key : ∀ {u v}, TransGen G.Adj u v → f u < f v := by
    intro u v h
    induction h with
    | single h => exact hf h
    | tail _ hbc ih => exact ih.trans (hf hbc)
  exact fun v h => lt_irrefl _ (key h)

/-- In an acyclic graph, an edge `u → v` makes the strict ancestors of `u` a proper subset of
those of `v`. -/
theorem IsAcyclic.ancestors_ssubset_of_adj (hG : G.IsAcyclic) (huv : G.Adj u v) :
    G.ancestors u ⊂ G.ancestors v :=
  Set.ssubset_iff_subset_ne.2
    ⟨fun _ hw => hw.tail huv, fun heq => hG u (heq ▸ isAncestor_of_adj huv : u ∈ G.ancestors u)⟩

section Finite

variable [Finite V]

/-- A finite acyclic graph has a topological order: counting strict ancestors gives
`f : V → ℕ` with `G.Adj u v → f u < f v`. -/
theorem IsAcyclic.exists_adj_lt (hG : G.IsAcyclic) :
    ∃ f : V → ℕ, ∀ ⦃u v⦄, G.Adj u v → f u < f v :=
  ⟨fun v => (G.ancestors v).ncard,
    fun _ _ huv => Set.ncard_lt_ncard (hG.ancestors_ssubset_of_adj huv)⟩

/-- A graph on a finite vertex type is acyclic if and only if it admits a topological order
`f : V → ℕ`, that is, `G.Adj u v → f u < f v`. -/
theorem isAcyclic_iff_exists_adj_lt :
    G.IsAcyclic ↔ ∃ f : V → ℕ, ∀ ⦃u v⦄, G.Adj u v → f u < f v :=
  ⟨IsAcyclic.exists_adj_lt, fun ⟨f, hf⟩ => isAcyclic_of_adj_lt f hf⟩

/-- A nonempty finite acyclic graph has a source: a vertex with no parents. -/
theorem IsAcyclic.exists_parents_eq_empty [Nonempty V] (hG : G.IsAcyclic) :
    ∃ v, G.parents v = ∅ := by
  obtain ⟨f, hf⟩ := hG.exists_adj_lt
  obtain ⟨v, hv⟩ := Finite.exists_min f
  exact ⟨v, Set.eq_empty_of_forall_notMem fun u hu => (hf hu).not_ge (hv u)⟩

/-- A nonempty finite acyclic graph has a sink: a vertex with no children. -/
theorem IsAcyclic.exists_children_eq_empty [Nonempty V] (hG : G.IsAcyclic) :
    ∃ v, G.children v = ∅ := by
  obtain ⟨f, hf⟩ := hG.exists_adj_lt
  obtain ⟨v, hv⟩ := Finite.exists_max f
  exact ⟨v, Set.eq_empty_of_forall_notMem fun w hw => (hf hw).not_ge (hv w)⟩

end Finite

instance decidableIsAcyclic [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :
    Decidable G.IsAcyclic :=
  decidable_of_iff (∀ v, ¬ G.IsAncestor v v) Iff.rfl

end Digraph

/-! ### Concrete examples checked by `decide` -/

namespace CausalInference.GraphExamples

/-- The chain `0 → 1 → 2`. -/
def chain : Digraph (Fin 3) where
  Adj i j := i.val + 1 = j.val

instance : DecidableRel chain.Adj := fun _ _ => inferInstanceAs (Decidable (_ = _))

/-- The fork `1 ← 0 → 2`. -/
def fork : Digraph (Fin 3) where
  Adj i j := i = 0 ∧ j ≠ 0

instance : DecidableRel fork.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

/-- The collider `0 → 2 ← 1`. -/
def collider : Digraph (Fin 3) where
  Adj i j := i ≠ 2 ∧ j = 2

instance : DecidableRel collider.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

/-- The directed cycle `0 → 1 → 2 → 0`. -/
def cycle : Digraph (Fin 3) where
  Adj i j := (i.val + 1) % 3 = j.val

instance : DecidableRel cycle.Adj := fun _ _ => inferInstanceAs (Decidable (_ = _))

example : chain.IsAncestor 0 2 := by decide
example : ¬ chain.IsAncestor 2 0 := by decide
example : chain.IsAcyclic := by decide
example : chain.ancestorsFinset 2 = {0, 1} := by decide
example : chain.descendantsFinset 0 = {1, 2} := by decide
example : chain.parentsFinset 1 = {0} := by decide

example : fork.IsAcyclic := by decide
example : ¬ fork.IsAncestor 1 2 := by decide
example : fork.childrenFinset 0 = {1, 2} := by decide

example : collider.IsAcyclic := by decide
example : collider.parentsFinset 2 = {0, 1} := by decide
example : collider.ancestorsFinset 2 = {0, 1} := by decide
example : ¬ collider.IsAncestor 0 1 := by decide

example : ¬ cycle.IsAcyclic := by decide
example : cycle.IsAncestor 2 2 := by decide
example : cycle.ancestorsFinset 0 = {0, 1, 2} := by decide

end CausalInference.GraphExamples
