/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Graphical.Mutilation
public import Mathlib.Order.WellFoundedSet
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Inv

/-!
# Topological orders, well-foundedness, and relative sources and sinks

## Main definitions

* `Digraph.topoKey G v`: for a finite vertex type with a linear order, the pair of the number of
  strict ancestors of `v` and `v` itself, in lexicographic order.
* `Digraph.topoIndex G v`: the position of `v` when the vertices are listed by `topoKey`; for an
  acyclic graph this is a computable enumeration of the vertices compatible with the edges.
* `Digraph.topoEquiv G`: that enumeration as an equivalence `V ≃ Fin (Fintype.card V)`.

## Main results

* `Digraph.IsAcyclic.wellFounded_adj`, `Digraph.IsAcyclic.wellFounded_flip_adj`: on a finite
  vertex type the edge relation of an acyclic graph and its reverse are well founded.
* `Digraph.lt_of_isAncestor`: a labeling strictly increasing along edges is strictly increasing
  along the ancestor relation.
* `Digraph.IsAcyclic.exists_injective_adj_lt`: a finite acyclic graph has an injective
  topological order `f : V → ℕ`.
* `Digraph.IsAcyclic.exists_equiv_fin_adj_lt`: a finite acyclic graph has an enumeration
  `e : V ≃ Fin (Fintype.card V)` with `G.Adj u v → e u < e v`.
* `Digraph.IsAcyclic.exists_mem_disjoint_children`,
  `Digraph.IsAcyclic.exists_mem_disjoint_parents`: a finite nonempty set of vertices of an
  acyclic graph contains a vertex with no child in the set and a vertex with no parent in the
  set. No finiteness of the vertex type is needed.

See Pearl (2009), *Causality: Models, Reasoning, and Inference*, 2nd edition.
-/

@[expose] public section

namespace Digraph

open Relation

variable {V : Type*} {G : Digraph V} {u v : V}

/-! ### Labelings increasing along edges -/

/-- A labeling strictly increasing along edges is strictly increasing along the ancestor
relation. -/
theorem lt_of_isAncestor {α : Type*} [Preorder α] {f : V → α}
    (hf : ∀ ⦃u v⦄, G.Adj u v → f u < f v) (h : G.IsAncestor u v) : f u < f v := by
  induction h with
  | single h => exact hf h
  | tail _ hbc ih => exact ih.trans (hf hbc)

/-- A labeling strictly increasing along edges is monotone along reachability. -/
theorem le_of_reflTransGen {α : Type*} [Preorder α] {f : V → α}
    (hf : ∀ ⦃u v⦄, G.Adj u v → f u < f v) (h : ReflTransGen G.Adj u v) : f u ≤ f v := by
  rcases reflTransGen_iff_eq_or_transGen.1 h with rfl | h
  · exact le_rfl
  · exact (lt_of_isAncestor hf h).le

/-! ### Well-foundedness -/

/-- On a finite vertex type the edge relation of an acyclic graph is well founded: there is no
infinite chain of parents `⋯ → v₂ → v₁ → v₀`. -/
theorem IsAcyclic.wellFounded_adj [Finite V] (hG : G.IsAcyclic) : WellFounded G.Adj := by
  obtain ⟨f, hf⟩ := hG.exists_adj_lt
  exact Subrelation.wf (fun h => hf h) (InvImage.wf f wellFounded_lt)

/-- On a finite vertex type the reversed edge relation of an acyclic graph is well founded:
there is no infinite chain of children `v₀ → v₁ → v₂ → ⋯`. -/
theorem IsAcyclic.wellFounded_flip_adj [Finite V] (hG : G.IsAcyclic) :
    WellFounded (flip G.Adj) := by
  have hR : (Digraph.mk (flip G.Adj)).IsAcyclic := fun v h => hG v h.swap
  exact hR.wellFounded_adj

/-- On a finite vertex type the ancestor relation of an acyclic graph is well founded. -/
theorem IsAcyclic.wellFounded_isAncestor [Finite V] (hG : G.IsAcyclic) :
    WellFounded G.IsAncestor :=
  hG.wellFounded_adj.transGen

/-! ### Relative sources and sinks -/

/-- A finite nonempty set `S` of vertices of an acyclic graph contains a vertex none of whose
parents lies in `S`: a source of the subgraph induced on `S`. The vertex type may be infinite. -/
theorem IsAcyclic.exists_mem_disjoint_parents (hG : G.IsAcyclic) {S : Set V} (hS : S.Finite)
    (hne : S.Nonempty) : ∃ v ∈ S, Disjoint (G.parents v) S := by
  have := hG.isStrictOrder
  obtain ⟨⟨m, hm⟩, -, hmin⟩ :=
    (hS.wellFoundedOn (r := G.IsAncestor)).has_min Set.univ ⟨⟨_, hne.some_mem⟩, trivial⟩
  exact ⟨m, hm, Set.disjoint_left.2 fun u hu huS =>
    hmin ⟨u, huS⟩ trivial (isAncestor_of_adj hu)⟩

/-- A finite nonempty set `S` of vertices of an acyclic graph contains a vertex none of whose
children lies in `S`: a sink of the subgraph induced on `S`. The vertex type may be infinite. -/
theorem IsAcyclic.exists_mem_disjoint_children (hG : G.IsAcyclic) {S : Set V} (hS : S.Finite)
    (hne : S.Nonempty) : ∃ v ∈ S, Disjoint (G.children v) S := by
  have : IsStrictOrder V (flip G.IsAncestor) :=
    { irrefl := fun a => hG a, trans := fun _ _ _ hab hbc => hbc.trans hab }
  obtain ⟨⟨m, hm⟩, -, hmin⟩ :=
    (hS.wellFoundedOn (r := flip G.IsAncestor)).has_min Set.univ ⟨⟨_, hne.some_mem⟩, trivial⟩
  exact ⟨m, hm, Set.disjoint_left.2 fun w hw hwS =>
    hmin ⟨w, hwS⟩ trivial (isAncestor_of_adj hw)⟩

/-! ### Enumerations compatible with the edges -/

section Enumeration

variable (G) [Fintype V] [LinearOrder V] [DecidableRel G.Adj]

/-- The sorting key of `v`: the number of strict ancestors of `v`, with ties broken by the linear
order on the vertices, in lexicographic order. -/
def topoKey (v : V) : ℕ ×ₗ V := toLex ((G.ancestorsFinset v).card, v)

/-- The position of `v` when the vertices are sorted by `topoKey`: the number of vertices with a
smaller key. For an acyclic graph it is an enumeration compatible with the edges
(`Digraph.IsAcyclic.topoIndex_lt_of_adj`). -/
def topoIndex (v : V) : Fin (Fintype.card V) :=
  ⟨(Finset.univ.filter fun u => G.topoKey u < G.topoKey v).card,
    Finset.card_lt_card (Finset.filter_ssubset.2 ⟨v, Finset.mem_univ _, lt_irrefl _⟩)⟩

variable {G}

theorem topoKey_injective : Function.Injective G.topoKey := fun _ _ h =>
  (Prod.ext_iff.1 (toLex.injective h)).2

/-- In an acyclic graph the sorting key strictly increases along every edge. -/
theorem IsAcyclic.topoKey_lt_of_adj (hG : G.IsAcyclic) (h : G.Adj u v) :
    G.topoKey u < G.topoKey v := by
  refine Prod.Lex.toLex_lt_toLex.2 (Or.inl ?_)
  refine Finset.card_lt_card ?_
  rw [← Finset.coe_ssubset, coe_ancestorsFinset, coe_ancestorsFinset]
  exact hG.ancestors_ssubset_of_adj h

theorem topoIndex_lt_topoIndex (h : G.topoKey u < G.topoKey v) : G.topoIndex u < G.topoIndex v := by
  refine Fin.mk_lt_mk.2 (Finset.card_lt_card ?_)
  refine (Finset.ssubset_iff_of_subset fun w hw => ?_).2 ⟨u, ?_, ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    exact hw.trans h
  · simpa using h
  · simp

theorem topoIndex_injective : Function.Injective G.topoIndex := by
  intro u v h
  by_contra hne
  rcases lt_or_gt_of_ne ((topoKey_injective (G := G)).ne hne) with hlt | hlt
  · exact (topoIndex_lt_topoIndex hlt).ne h
  · exact (topoIndex_lt_topoIndex hlt).ne h.symm

theorem topoIndex_bijective : Function.Bijective G.topoIndex :=
  (Fintype.bijective_iff_injective_and_card _).2 ⟨topoIndex_injective (G := G), by simp⟩

/-- In an acyclic graph the enumeration `topoIndex` strictly increases along every edge. -/
theorem IsAcyclic.topoIndex_lt_of_adj (hG : G.IsAcyclic) (h : G.Adj u v) :
    G.topoIndex u < G.topoIndex v :=
  topoIndex_lt_topoIndex (hG.topoKey_lt_of_adj h)

variable (G)

/-- The enumeration `topoIndex` as an equivalence `V ≃ Fin (Fintype.card V)`, with a computable
inverse. -/
def topoEquiv : V ≃ Fin (Fintype.card V) where
  toFun := G.topoIndex
  invFun := Fintype.bijInv (topoIndex_bijective (G := G))
  left_inv := Fintype.leftInverse_bijInv _
  right_inv := Fintype.rightInverse_bijInv _

variable {G}

@[simp] theorem topoEquiv_apply (v : V) : G.topoEquiv v = G.topoIndex v := rfl

/-- In an acyclic graph the equivalence `topoEquiv` strictly increases along every edge. -/
theorem IsAcyclic.topoEquiv_lt_of_adj (hG : G.IsAcyclic) (h : G.Adj u v) :
    G.topoEquiv u < G.topoEquiv v :=
  hG.topoIndex_lt_of_adj h

end Enumeration

/-- A finite acyclic graph has an enumeration of its vertices compatible with the edges:
`e : V ≃ Fin (Fintype.card V)` with `G.Adj u v → e u < e v`. -/
theorem IsAcyclic.exists_equiv_fin_adj_lt [Fintype V] (hG : G.IsAcyclic) :
    ∃ e : V ≃ Fin (Fintype.card V), ∀ ⦃u v⦄, G.Adj u v → e u < e v := by
  classical
  let _ : LinearOrder V := LinearOrder.lift' (Fintype.equivFin V) (Fintype.equivFin V).injective
  exact ⟨G.topoEquiv, fun _ _ h => hG.topoEquiv_lt_of_adj h⟩

/-- A finite acyclic graph has an injective topological order: `f : V → ℕ` injective with
`G.Adj u v → f u < f v`. -/
theorem IsAcyclic.exists_injective_adj_lt [Finite V] (hG : G.IsAcyclic) :
    ∃ f : V → ℕ, Function.Injective f ∧ ∀ ⦃u v⦄, G.Adj u v → f u < f v := by
  have := Fintype.ofFinite V
  obtain ⟨e, he⟩ := hG.exists_equiv_fin_adj_lt
  exact ⟨fun v => e v, fun _ _ h => e.injective (Fin.ext h), fun _ _ h => he h⟩

end Digraph

/-! ### Concrete examples checked by `decide` -/

namespace CausalInference.GraphExamples

example : chain.topoIndex 0 = 0 ∧ chain.topoIndex 1 = 1 ∧ chain.topoIndex 2 = 2 := by decide
example : collider.topoIndex 2 = 2 := by decide
example : fork.topoIndex 0 = 0 := by decide
example : (cycle.deleteIncoming {0}).topoEquiv.symm 0 = 0 := by decide

end CausalInference.GraphExamples
