/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Graphical.DSeparationLemmas
public import CausalInference.Graphical.TopologicalOrder

/-!
# Markov equivalence: definitions and the necessity of skeleton and v-structures

Two directed graphs on the same vertices are *Markov equivalent* when they have the same
d-separation relation. This file defines Markov equivalence, v-structures and unshielded triples,
and proves the graphical facts on which causal discovery rests:

* adjacent vertices are d-connected given every set that contains neither of them;
* nonadjacent vertices of an acyclic graph are d-separated by the parents of one of them (the
  later one in any topological order);
* for an unshielded triple `a, c, b`, the middle vertex `c` is a collider (`a → c ← b`) if and
  only if it lies in no separating set of `a` and `b`, if and only if it lies outside some
  separating set.

Consequently Markov equivalent acyclic graphs have the same skeleton and the same v-structures:
the "only if" half of the theorem of Verma and Pearl (1990); Pearl (2009), *Causality*, 2nd
edition, Theorem 1.2.8 (observational equivalence). The converse is
`Digraph.markovEquivalent_iff` in `CausalInference.Discovery.MarkovEquivalenceCharacterization`.

## Main definitions

* `Digraph.IsVStructure G a c b`: `a → c ← b` with `a ≠ b` and `a`, `b` nonadjacent.
* `Digraph.IsUnshielded G a c b`: `c` is adjacent to `a` and to `b` in the skeleton, `a ≠ b`,
  and `a`, `b` are nonadjacent.
* `Digraph.MarkovEquivalent G H`: `G.DSep X Y Z ↔ H.DSep X Y Z` for all sets `X`, `Y`, `Z`.

## Main results

* `Digraph.markovEquivalent_iff_forall_singleton`: the set form and the singleton form of
  Markov equivalence agree.
* `Digraph.not_dSep_of_skeleton_adj`: adjacent vertices are never d-separated by a set that
  contains neither of them.
* `Digraph.IsAcyclic.dSep_parents_of_not_reflTransGen`, `Digraph.dSep_parents_of_lt`:
  separation of a vertex from an earlier nonadjacent vertex by its parents.
* `Digraph.IsAcyclic.exists_dSep_of_not_adj`, `Digraph.IsAcyclic.skeleton_adj_iff`: adjacency in
  the skeleton is d-connection given every set avoiding both vertices.
* `Digraph.IsAcyclic.collider_iff_forall_dSep`, `Digraph.IsAcyclic.collider_iff_exists_dSep`:
  the separating set characterization of colliders in unshielded triples.
* `Digraph.MarkovEquivalent.skeleton_eq`, `Digraph.MarkovEquivalent.isVStructure_iff`.

## Conventions

`Digraph.DSep` is total: `G.DSep {u} {v} Z` holds whenever `u ∈ Z` or `v ∈ Z`. So every
statement about separating sets requires the two endpoints to lie outside the set.

## References

* T. Verma and J. Pearl (1990), *Equivalence and synthesis of causal models*.
* J. Pearl (2009), *Causality: Models, Reasoning, and Inference*, 2nd edition, section 1.2.3,
  Theorem 1.2.8.
-/

@[expose] public section

namespace Digraph

open Relation

variable {V : Type*}

/-- A v-structure (unshielded collider) `a → c ← b` of `G`: both `a` and `b` point into `c`,
`a ≠ b`, and `a` and `b` are not adjacent. -/
def IsVStructure (G : Digraph V) (a c b : V) : Prop :=
  G.Adj a c ∧ G.Adj b c ∧ a ≠ b ∧ ¬ G.Adj a b ∧ ¬ G.Adj b a

/-- An unshielded triple `a, c, b` of the skeleton of `G`: `a` and `c` are adjacent, `c` and
`b` are adjacent, `a ≠ b`, and `a` and `b` are not adjacent. -/
def IsUnshielded (G : Digraph V) (a c b : V) : Prop :=
  a ≠ b ∧ G.skeleton.Adj a c ∧ G.skeleton.Adj c b ∧ ¬ G.skeleton.Adj a b

/-- Two directed graphs on the same vertices are Markov equivalent when they have the same
d-separation relation: `G.DSep X Y Z ↔ H.DSep X Y Z` for all sets of vertices. -/
def MarkovEquivalent (G H : Digraph V) : Prop :=
  ∀ X Y Z : Set V, G.DSep X Y Z ↔ H.DSep X Y Z

variable {G H K : Digraph V} {X Y Z : Set V} {a b c u v : V}

/-! ### Markov equivalence as a relation -/

theorem MarkovEquivalent.refl (G : Digraph V) : MarkovEquivalent G G := fun _ _ _ => Iff.rfl

theorem MarkovEquivalent.symm (h : MarkovEquivalent G H) : MarkovEquivalent H G :=
  fun X Y Z => (h X Y Z).symm

theorem MarkovEquivalent.trans (h₁ : MarkovEquivalent G H) (h₂ : MarkovEquivalent H K) :
    MarkovEquivalent G K :=
  fun X Y Z => (h₁ X Y Z).trans (h₂ X Y Z)

/-- Markov equivalence in singleton form: it suffices that the two graphs agree on the
d-separation of single vertices. -/
theorem markovEquivalent_iff_forall_singleton :
    MarkovEquivalent G H ↔ ∀ (x y : V) (Z : Set V), G.DSep {x} {y} Z ↔ H.DSep {x} {y} Z := by
  refine ⟨fun h x y Z => h {x} {y} Z, fun h X Y Z => ?_⟩
  rw [dSep_iff_forall_singleton, dSep_iff_forall_singleton]
  exact forall₂_congr fun x _ => forall₂_congr fun y _ => h x y Z

/-! ### Adjacent vertices -/

/-- Adjacent vertices are d-connected given every set that contains neither of them. -/
theorem not_dSep_of_adj (h : G.Adj u v ∨ G.Adj v u) (hu : u ∉ Z) (hv : v ∉ Z) :
    ¬ G.DSep {u} {v} Z := by
  rcases h with h | h
  · exact fun hs => hs (dConn_of_adj h hu hv)
  · exact fun hs => hs (dConn_of_adj h hv hu).symm

/-- Vertices adjacent in the skeleton are never d-separated by a set containing neither of
them. -/
theorem not_dSep_of_skeleton_adj (h : G.skeleton.Adj u v) (hu : u ∉ Z) (hv : v ∉ Z) :
    ¬ G.DSep {u} {v} Z :=
  not_dSep_of_adj (skeleton_adj.1 h).2 hu hv

/-! ### Nonadjacent vertices -/

/-- In an acyclic graph a vertex `v` is d-separated from every vertex `u` that it does not
reach by a directed path, given the parents of `v`. If moreover `u` is not adjacent to `v`, the
parents of `v` form a separating set that contains neither vertex. -/
theorem IsAcyclic.dSep_parents_of_not_reflTransGen (hG : G.IsAcyclic)
    (hvu : ¬ ReflTransGen G.Adj v u) : G.DSep {v} {u} (G.parents v) :=
  (hG.dSep_nondescendants_parents v).mono_right (Set.singleton_subset_iff.2 fun hdesc => by
    obtain ⟨s, hs, hsw⟩ := hdesc
    rw [Set.mem_singleton_iff] at hs
    subst hs
    exact hvu hsw)

/-- With a topological order `f` of `G`, a vertex `v` is d-separated from every vertex `u`
with `f u < f v`, given the parents of `v`: nonadjacent vertices are separated by the parents
of the later one. -/
theorem dSep_parents_of_lt {f : V → ℕ} (hf : ∀ ⦃u v⦄, G.Adj u v → f u < f v)
    (hlt : f u < f v) : G.DSep {v} {u} (G.parents v) := by
  have hG : G.IsAcyclic := isAcyclic_of_adj_lt f hf
  exact hG.dSep_parents_of_not_reflTransGen fun h => (le_of_reflTransGen hf h).not_gt hlt

/-- Two distinct nonadjacent vertices of an acyclic graph are d-separated by some set containing
neither of them: the parents of whichever of the two is not an ancestor of the other. -/
theorem IsAcyclic.exists_dSep_of_not_adj (hG : G.IsAcyclic) (hne : u ≠ v)
    (hn : ¬ G.skeleton.Adj u v) : ∃ Z : Set V, u ∉ Z ∧ v ∉ Z ∧ G.DSep {u} {v} Z := by
  have hn' : ¬ G.Adj u v ∧ ¬ G.Adj v u := by
    rw [skeleton_adj] at hn
    push Not at hn
    exact ⟨fun h => (hn hne).1 h, fun h => (hn hne).2 h⟩
  by_cases hvu : ReflTransGen G.Adj v u
  · have huv : ¬ ReflTransGen G.Adj u v := by
      intro huv
      rcases reflTransGen_iff_eq_or_transGen.1 hvu with h | h
      · exact hne h
      · rcases reflTransGen_iff_eq_or_transGen.1 huv with h' | h'
        · exact hne h'.symm
        · exact hG u (h'.trans h)
    exact ⟨G.parents u, hG.irrefl u, hn'.2, hG.dSep_parents_of_not_reflTransGen huv⟩
  · exact ⟨G.parents v, hn'.1, hG.irrefl v, (hG.dSep_parents_of_not_reflTransGen hvu).symm⟩

/-- **Adjacency is d-connection.** In an acyclic graph two vertices are adjacent in the skeleton
if and only if they are distinct and d-connected given every set containing neither of them. -/
theorem IsAcyclic.skeleton_adj_iff (hG : G.IsAcyclic) :
    G.skeleton.Adj u v ↔ u ≠ v ∧ ∀ Z : Set V, u ∉ Z → v ∉ Z → ¬ G.DSep {u} {v} Z := by
  refine ⟨fun h => ⟨h.ne, fun Z hu hv => not_dSep_of_skeleton_adj h hu hv⟩, ?_⟩
  rintro ⟨hne, h⟩
  by_contra hn
  obtain ⟨Z, hu, hv, hs⟩ := hG.exists_dSep_of_not_adj hne hn
  exact h Z hu hv hs

/-! ### Unshielded triples -/

/-- In an acyclic graph a v-structure is exactly an unshielded triple whose middle vertex is a
collider. -/
theorem IsAcyclic.isVStructure_iff (hG : G.IsAcyclic) :
    G.IsVStructure a c b ↔ G.IsUnshielded a c b ∧ G.Adj a c ∧ G.Adj b c := by
  constructor
  · rintro ⟨hac, hbc, hab, hnab, hnba⟩
    refine ⟨⟨hab, skeleton_adj.2 ⟨hG.ne_of_adj hac, Or.inl hac⟩,
      skeleton_adj.2 ⟨(hG.ne_of_adj hbc).symm, Or.inr hbc⟩, fun h => ?_⟩, hac, hbc⟩
    rcases (skeleton_adj.1 h).2 with h | h
    · exact hnab h
    · exact hnba h
  · rintro ⟨⟨hab, -, -, hn⟩, hac, hbc⟩
    exact ⟨hac, hbc, hab, fun h => hn (skeleton_adj.2 ⟨hab, Or.inl h⟩),
      fun h => hn (skeleton_adj.2 ⟨hab, Or.inr h⟩)⟩

/-- In an unshielded triple whose middle vertex is a collider, conditioning on the collider
d-connects the endpoints. So no separating set of the endpoints contains a collider. -/
theorem not_dSep_of_collider_mem (hac : G.Adj a c) (hbc : G.Adj b c) (hc : c ∈ Z)
    (ha : a ∉ Z) (hb : b ∉ Z) : ¬ G.DSep {a} {b} Z :=
  fun hs => hs (dConn_of_collider hac hbc ha (subset_ancestorsOf Z hc) hb)

/-- In an unshielded triple whose middle vertex is not a collider (a chain in either direction
or a fork), leaving the middle vertex unconditioned d-connects the endpoints. So every
separating set of the endpoints contains a non-collider. -/
theorem IsUnshielded.not_dSep_of_notMem (hs : G.IsUnshielded a c b)
    (hnc : ¬ (G.Adj a c ∧ G.Adj b c)) (hc : c ∉ Z) (ha : a ∉ Z) (hb : b ∉ Z) :
    ¬ G.DSep {a} {b} Z := by
  obtain ⟨-, hac, hcb, -⟩ := hs
  have hac' := (skeleton_adj.1 hac).2
  have hcb' := (skeleton_adj.1 hcb).2
  intro hsep
  apply hsep
  rcases hac' with hac' | hca'
  · rcases hcb' with hcb' | hbc'
    · exact dConn_of_chain hac' hcb' ha hc hb
    · exact absurd ⟨hac', hbc'⟩ hnc
  · rcases hcb' with hcb' | hbc'
    · exact dConn_of_fork hca' hcb' ha hc hb
    · exact (dConn_of_chain hbc' hca' hb hc ha).symm

/-- **Colliders and separating sets.** In an acyclic graph, the middle vertex `c` of an
unshielded triple `a, c, b` is a collider (`a → c ← b`) if and only if it belongs to no set
that separates `a` and `b` and contains neither of them. -/
theorem IsAcyclic.collider_iff_forall_dSep (hG : G.IsAcyclic) (hs : G.IsUnshielded a c b) :
    (G.Adj a c ∧ G.Adj b c) ↔
      ∀ Z : Set V, a ∉ Z → b ∉ Z → G.DSep {a} {b} Z → c ∉ Z := by
  refine ⟨fun ⟨hac, hbc⟩ Z ha hb hsep hc => not_dSep_of_collider_mem hac hbc hc ha hb hsep,
    fun h => ?_⟩
  by_contra hnc
  obtain ⟨Z, ha, hb, hsep⟩ := hG.exists_dSep_of_not_adj hs.1 hs.2.2.2
  exact hs.not_dSep_of_notMem hnc (h Z ha hb hsep) ha hb hsep

/-- **Colliders and separating sets, existential form.** In an acyclic graph, the middle vertex
`c` of an unshielded triple `a, c, b` is a collider if and only if some set separating `a` and
`b` and containing neither of them does not contain `c`. Since every separating set decides the
question in the same way, the PC algorithm may use any separating set it finds. -/
theorem IsAcyclic.collider_iff_exists_dSep (hG : G.IsAcyclic) (hs : G.IsUnshielded a c b) :
    (G.Adj a c ∧ G.Adj b c) ↔
      ∃ Z : Set V, a ∉ Z ∧ b ∉ Z ∧ G.DSep {a} {b} Z ∧ c ∉ Z := by
  refine ⟨fun h => ?_, fun ⟨Z, ha, hb, hsep, hc⟩ => ?_⟩
  · obtain ⟨Z, ha, hb, hsep⟩ := hG.exists_dSep_of_not_adj hs.1 hs.2.2.2
    exact ⟨Z, ha, hb, hsep, (hG.collider_iff_forall_dSep hs).1 h Z ha hb hsep⟩
  · by_contra hnc
    exact hs.not_dSep_of_notMem hnc hc ha hb hsep

/-! ### Markov equivalent graphs have the same skeleton and v-structures -/

/-- Markov equivalent acyclic graphs have the same skeleton. -/
theorem MarkovEquivalent.skeleton_eq (hG : G.IsAcyclic) (hH : H.IsAcyclic)
    (h : MarkovEquivalent G H) : G.skeleton = H.skeleton := by
  ext u v
  rw [hG.skeleton_adj_iff, hH.skeleton_adj_iff]
  exact and_congr Iff.rfl (forall_congr' fun Z => by rw [h])

theorem IsUnshielded.of_skeleton_eq (hs : G.IsUnshielded a c b) (h : G.skeleton = H.skeleton) :
    H.IsUnshielded a c b := by
  rwa [IsUnshielded, ← h]

/-- Markov equivalent acyclic graphs have the same v-structures. -/
theorem MarkovEquivalent.isVStructure_iff (hG : G.IsAcyclic) (hH : H.IsAcyclic)
    (h : MarkovEquivalent G H) : G.IsVStructure a c b ↔ H.IsVStructure a c b := by
  have hsk := h.skeleton_eq hG hH
  rw [hG.isVStructure_iff, hH.isVStructure_iff]
  constructor
  · rintro ⟨hs, hc⟩
    have hs' := hs.of_skeleton_eq hsk
    refine ⟨hs', (hH.collider_iff_forall_dSep hs').2 fun Z ha hb hsep => ?_⟩
    exact (hG.collider_iff_forall_dSep hs).1 hc Z ha hb ((h _ _ _).2 hsep)
  · rintro ⟨hs, hc⟩
    have hs' := hs.of_skeleton_eq hsk.symm
    refine ⟨hs', (hG.collider_iff_forall_dSep hs').2 fun Z ha hb hsep => ?_⟩
    exact (hH.collider_iff_forall_dSep hs).1 hc Z ha hb ((h _ _ _).1 hsep)

end Digraph
