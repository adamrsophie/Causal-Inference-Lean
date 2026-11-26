/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Graphical.Basic
public import Mathlib.Logic.Relation
public import Mathlib.Data.Fintype.Card

/-!
# Ancestors and descendants in a directed graph

Directed reachability in a `Digraph` is Mathlib's `Relation.TransGen G.Adj` (a directed path
with at least one edge) and `Relation.ReflTransGen G.Adj` (a directed path with zero or more
edges). This file names the ancestor relation and the ancestral closures built from them.

## Main definitions

* `Digraph.IsAncestor G u v`: there is a directed path with at least one edge from `u` to `v`.
  This is the strict ancestor relation.
* `Digraph.ancestors G v`, `Digraph.descendants G v`: the strict ancestors and descendants.
* `Digraph.ancestorsOf G S`: the inclusive ancestral closure of a set `S`, that is, every vertex
  with a directed path of length at least zero into `S`. Dually `Digraph.descendantsOf G S`.
* `Digraph.reachFinset G u`: for a finite vertex type, the finset of vertices reachable from `u`,
  computed by saturation; it underlies the decision procedures.
* `Digraph.ancestorsFinset G v`, `Digraph.descendantsFinset G v`: finite versions.

## Main results

* `Digraph.IsAncestor.trans`, monotonicity in the graph, `Digraph.subset_ancestorsOf`,
  `Digraph.ancestorsOf_ancestorsOf` (idempotence), `Digraph.ancestorsOf_mono`.
* `Digraph.mem_reachFinset`: correctness of the saturation procedure, which yields
  `Decidable (G.IsAncestor u v)` on a finite vertex type, usable by `decide`.

The terminology follows Pearl (2009), *Causality: Models, Reasoning, and Inference*, 2nd edition,
except that `ancestorsOf` and `descendantsOf` include the set itself, as is common in the
literature on d-separation and identification.
-/

@[expose] public section

namespace Digraph

open Relation

variable {V : Type*}

/-- `G.IsAncestor u v` means that there is a directed path with at least one edge from `u` to
`v` in `G`; this is the strict ancestor relation. -/
def IsAncestor (G : Digraph V) (u v : V) : Prop := TransGen G.Adj u v

/-- The strict ancestors of `v`: the vertices with a directed path of positive length to `v`. -/
def ancestors (G : Digraph V) (v : V) : Set V := {u | G.IsAncestor u v}

/-- The strict descendants of `v`: the vertices reached from `v` by a directed path of positive
length. -/
def descendants (G : Digraph V) (v : V) : Set V := {w | G.IsAncestor v w}

/-- The inclusive ancestral closure of `S`: every vertex with a directed path of length at least
zero into `S`. In particular `S ⊆ G.ancestorsOf S`. -/
def ancestorsOf (G : Digraph V) (S : Set V) : Set V := {u | ∃ s ∈ S, ReflTransGen G.Adj u s}

/-- The inclusive descendant closure of `S`: every vertex reached by a directed path of length at
least zero from `S`. In particular `S ⊆ G.descendantsOf S`. -/
def descendantsOf (G : Digraph V) (S : Set V) : Set V := {w | ∃ s ∈ S, ReflTransGen G.Adj s w}

section Sets

variable {G H : Digraph V} {u v w : V} {S T : Set V}

theorem isAncestor_iff : G.IsAncestor u v ↔ TransGen G.Adj u v := Iff.rfl

/-- Every edge is an ancestor relation. -/
theorem isAncestor_of_adj (h : G.Adj u v) : G.IsAncestor u v := TransGen.single h

/-- The ancestor relation is transitive. -/
theorem IsAncestor.trans (huv : G.IsAncestor u v) (hvw : G.IsAncestor v w) :
    G.IsAncestor u w :=
  TransGen.trans huv hvw

/-- Prepending an edge to a directed path. -/
theorem IsAncestor.head (huv : G.Adj u v) (hvw : G.IsAncestor v w) : G.IsAncestor u w :=
  TransGen.head huv hvw

/-- Appending an edge to a directed path. -/
theorem IsAncestor.tail (huv : G.IsAncestor u v) (hvw : G.Adj v w) : G.IsAncestor u w :=
  TransGen.tail huv hvw

/-- A strict ancestor is in particular reachable. -/
theorem IsAncestor.reflTransGen (h : G.IsAncestor u v) : ReflTransGen G.Adj u v :=
  TransGen.to_reflTransGen h

/-- The ancestor relation is monotone in the graph. -/
theorem IsAncestor.mono (hGH : G ≤ H) (h : G.IsAncestor u v) : H.IsAncestor u v :=
  TransGen.mono (fun _ _ h' => hGH h') _ _ h

/-- Reachability is monotone in the graph. -/
theorem reflTransGen_mono (hGH : G ≤ H) (h : ReflTransGen G.Adj u v) :
    ReflTransGen H.Adj u v :=
  ReflTransGen.mono (fun _ _ h' => hGH h') _ _ h

@[simp] theorem mem_ancestors : u ∈ G.ancestors v ↔ G.IsAncestor u v := Iff.rfl

@[simp] theorem mem_descendants : w ∈ G.descendants v ↔ G.IsAncestor v w := Iff.rfl

/-- `u` is an ancestor of `v` exactly when `v` is a descendant of `u`. -/
theorem mem_ancestors_iff_mem_descendants : u ∈ G.ancestors v ↔ v ∈ G.descendants u := Iff.rfl

/-- Parents are ancestors. -/
theorem parents_subset_ancestors (v : V) : G.parents v ⊆ G.ancestors v :=
  fun _ h => isAncestor_of_adj h

/-- Children are descendants. -/
theorem children_subset_descendants (v : V) : G.children v ⊆ G.descendants v :=
  fun _ h => isAncestor_of_adj h

theorem ancestors_mono (hGH : G ≤ H) (v : V) : G.ancestors v ⊆ H.ancestors v :=
  fun _ h => h.mono hGH

theorem descendants_mono (hGH : G ≤ H) (v : V) : G.descendants v ⊆ H.descendants v :=
  fun _ h => h.mono hGH

@[simp] theorem mem_ancestorsOf : u ∈ G.ancestorsOf S ↔ ∃ s ∈ S, ReflTransGen G.Adj u s :=
  Iff.rfl

@[simp] theorem mem_descendantsOf : w ∈ G.descendantsOf S ↔ ∃ s ∈ S, ReflTransGen G.Adj s w :=
  Iff.rfl

/-- A set is contained in its ancestral closure. -/
theorem subset_ancestorsOf (S : Set V) : S ⊆ G.ancestorsOf S :=
  fun s hs => ⟨s, hs, ReflTransGen.refl⟩

/-- A set is contained in its descendant closure. -/
theorem subset_descendantsOf (S : Set V) : S ⊆ G.descendantsOf S :=
  fun s hs => ⟨s, hs, ReflTransGen.refl⟩

/-- The ancestral closure is monotone in the set. -/
theorem ancestorsOf_mono (h : S ⊆ T) : G.ancestorsOf S ⊆ G.ancestorsOf T :=
  fun _ ⟨s, hs, hus⟩ => ⟨s, h hs, hus⟩

/-- The descendant closure is monotone in the set. -/
theorem descendantsOf_mono (h : S ⊆ T) : G.descendantsOf S ⊆ G.descendantsOf T :=
  fun _ ⟨s, hs, hsw⟩ => ⟨s, h hs, hsw⟩

/-- The ancestral closure is monotone in the graph. -/
theorem ancestorsOf_mono_graph (hGH : G ≤ H) (S : Set V) : G.ancestorsOf S ⊆ H.ancestorsOf S :=
  fun _ ⟨s, hs, hus⟩ => ⟨s, hs, reflTransGen_mono hGH hus⟩

/-- The descendant closure is monotone in the graph. -/
theorem descendantsOf_mono_graph (hGH : G ≤ H) (S : Set V) :
    G.descendantsOf S ⊆ H.descendantsOf S :=
  fun _ ⟨s, hs, hsw⟩ => ⟨s, hs, reflTransGen_mono hGH hsw⟩

/-- The ancestral closure is closed under reachability. -/
theorem mem_ancestorsOf_of_reflTransGen (huv : ReflTransGen G.Adj u v)
    (hv : v ∈ G.ancestorsOf S) : u ∈ G.ancestorsOf S :=
  let ⟨s, hs, hvs⟩ := hv
  ⟨s, hs, huv.trans hvs⟩

/-- The ancestral closure is closed under taking parents. -/
theorem mem_ancestorsOf_of_adj (huv : G.Adj u v) (hv : v ∈ G.ancestorsOf S) :
    u ∈ G.ancestorsOf S :=
  mem_ancestorsOf_of_reflTransGen (ReflTransGen.single huv) hv

/-- The descendant closure is closed under reachability. -/
theorem mem_descendantsOf_of_reflTransGen (huv : ReflTransGen G.Adj u v)
    (hu : u ∈ G.descendantsOf S) : v ∈ G.descendantsOf S :=
  let ⟨s, hs, hsu⟩ := hu
  ⟨s, hs, hsu.trans huv⟩

/-- The descendant closure is closed under taking children. -/
theorem mem_descendantsOf_of_adj (huv : G.Adj u v) (hu : u ∈ G.descendantsOf S) :
    v ∈ G.descendantsOf S :=
  mem_descendantsOf_of_reflTransGen (ReflTransGen.single huv) hu

/-- The ancestral closure is idempotent. -/
@[simp] theorem ancestorsOf_ancestorsOf (S : Set V) :
    G.ancestorsOf (G.ancestorsOf S) = G.ancestorsOf S := by
  refine Set.Subset.antisymm ?_ (subset_ancestorsOf _)
  rintro u ⟨v, hv, huv⟩
  exact mem_ancestorsOf_of_reflTransGen huv hv

/-- The descendant closure is idempotent. -/
@[simp] theorem descendantsOf_descendantsOf (S : Set V) :
    G.descendantsOf (G.descendantsOf S) = G.descendantsOf S := by
  refine Set.Subset.antisymm ?_ (subset_descendantsOf _)
  rintro w ⟨v, hv, hvw⟩
  exact mem_descendantsOf_of_reflTransGen hvw hv

@[simp] theorem ancestorsOf_empty : G.ancestorsOf ∅ = ∅ := by
  ext; simp

@[simp] theorem descendantsOf_empty : G.descendantsOf ∅ = ∅ := by
  ext; simp

theorem ancestorsOf_union (S T : Set V) :
    G.ancestorsOf (S ∪ T) = G.ancestorsOf S ∪ G.ancestorsOf T := by
  ext; simp [or_and_right, exists_or]

theorem descendantsOf_union (S T : Set V) :
    G.descendantsOf (S ∪ T) = G.descendantsOf S ∪ G.descendantsOf T := by
  ext; simp [or_and_right, exists_or]

/-- Membership in the ancestral closure of a single vertex is reachability. -/
theorem mem_ancestorsOf_singleton : u ∈ G.ancestorsOf {v} ↔ ReflTransGen G.Adj u v := by
  simp

/-- Membership in the descendant closure of a single vertex is reachability. -/
theorem mem_descendantsOf_singleton : w ∈ G.descendantsOf {v} ↔ ReflTransGen G.Adj v w := by
  simp

/-- `u` is in the ancestral closure of `v` exactly when `v` is in the descendant closure of `u`. -/
theorem mem_ancestorsOf_singleton_iff_mem_descendantsOf_singleton :
    u ∈ G.ancestorsOf {v} ↔ v ∈ G.descendantsOf {u} := by
  simp

/-- The ancestral closure of a vertex is the vertex together with its strict ancestors. -/
theorem ancestorsOf_singleton (v : V) : G.ancestorsOf {v} = insert v (G.ancestors v) := by
  ext u
  simp only [mem_ancestorsOf_singleton, Set.mem_insert_iff, mem_ancestors, IsAncestor]
  rw [reflTransGen_iff_eq_or_transGen, eq_comm]

/-- The descendant closure of a vertex is the vertex together with its strict descendants. -/
theorem descendantsOf_singleton (v : V) : G.descendantsOf {v} = insert v (G.descendants v) := by
  ext w
  simp only [mem_descendantsOf_singleton, Set.mem_insert_iff, mem_descendants, IsAncestor]
  rw [reflTransGen_iff_eq_or_transGen]

/-- The strict ancestors of a member of `S` lie in the ancestral closure of `S`. -/
theorem ancestors_subset_ancestorsOf (hv : v ∈ S) : G.ancestors v ⊆ G.ancestorsOf S :=
  fun _ hu => ⟨v, hv, hu.reflTransGen⟩

/-- The strict descendants of a member of `S` lie in the descendant closure of `S`. -/
theorem descendants_subset_descendantsOf (hv : v ∈ S) : G.descendants v ⊆ G.descendantsOf S :=
  fun _ hw => ⟨v, hv, hw.reflTransGen⟩

/-- Transfer of ancestral closures between graphs: if every edge of `G` that ends inside
`G.ancestorsOf S` is also an edge of `H`, then `G.ancestorsOf S ⊆ H.ancestorsOf S`. -/
theorem ancestorsOf_subset_ancestorsOf_of_adj
    (h : ∀ ⦃u w⦄, G.Adj u w → w ∈ G.ancestorsOf S → H.Adj u w) :
    G.ancestorsOf S ⊆ H.ancestorsOf S := by
  rintro u ⟨s, hs, hus⟩
  refine ⟨s, hs, ?_⟩
  induction hus using ReflTransGen.head_induction_on with
  | refl => exact ReflTransGen.refl
  | head huc hcs ih => exact ih.head (h huc ⟨s, hs, hcs⟩)

/-- Transfer of descendant closures between graphs: if every edge of `G` that starts inside
`G.descendantsOf S` is also an edge of `H`, then `G.descendantsOf S ⊆ H.descendantsOf S`. -/
theorem descendantsOf_subset_descendantsOf_of_adj
    (h : ∀ ⦃u w⦄, G.Adj u w → u ∈ G.descendantsOf S → H.Adj u w) :
    G.descendantsOf S ⊆ H.descendantsOf S := by
  rintro w ⟨s, hs, hsw⟩
  refine ⟨s, hs, ?_⟩
  induction hsw with
  | refl => exact ReflTransGen.refl
  | tail hsb hbc ih => exact ih.tail (h hbc ⟨s, hs, hsb⟩)

end Sets

/-! ### Finite vertex types: saturation and decidability -/

section Finite

variable (G : Digraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Saturation from `u`: stage `0` is `{u}`, and each stage adds the children of the previous
one. Stage `n` is the set of vertices reachable from `u` by a directed path of length at
most `n`. -/
def reachIter (u : V) : ℕ → Finset V
  | 0 => {u}
  | n + 1 => reachIter u n ∪ Finset.univ.filter (fun w => ∃ x ∈ reachIter u n, G.Adj x w)

/-- The finset of vertices reachable from `u` by a directed path of length at least zero,
computed as stage `Fintype.card V` of the saturation `reachIter`. -/
def reachFinset (u : V) : Finset V := G.reachIter u (Fintype.card V)

variable {G}

theorem reachIter_subset_succ (u : V) (n : ℕ) : G.reachIter u n ⊆ G.reachIter u (n + 1) :=
  Finset.subset_union_left

theorem reachIter_mono (u : V) {m n : ℕ} (h : m ≤ n) : G.reachIter u m ⊆ G.reachIter u n := by
  induction h with
  | refl => exact subset_rfl
  | step _ ih => exact ih.trans (reachIter_subset_succ u _)

theorem reflTransGen_of_mem_reachIter {u : V} :
    ∀ {n : ℕ} {w : V}, w ∈ G.reachIter u n → ReflTransGen G.Adj u w
  | 0, w, h => by
    rw [reachIter, Finset.mem_singleton] at h
    subst h
    exact ReflTransGen.refl
  | n + 1, w, h => by
    simp only [reachIter, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at h
    rcases h with h | ⟨x, hx, hxw⟩
    · exact reflTransGen_of_mem_reachIter h
    · exact (reflTransGen_of_mem_reachIter hx).tail hxw

theorem exists_mem_reachIter {u w : V} (h : ReflTransGen G.Adj u w) :
    ∃ n, w ∈ G.reachIter u n := by
  induction h with
  | refl => exact ⟨0, by simp [reachIter]⟩
  | tail _ hbc ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, by
      simp only [reachIter, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Or.inr ⟨_, hn, hbc⟩⟩

theorem reachIter_eq_of_succ_eq {u : V} {k : ℕ} (h : G.reachIter u (k + 1) = G.reachIter u k)
    {n : ℕ} (hn : k ≤ n) : G.reachIter u n = G.reachIter u k := by
  induction hn with
  | refl => rfl
  | step _ ih =>
    change G.reachIter u _ ∪ _ = _
    rw [ih]
    exact h

theorem card_reachIter_of_ne {u : V} :
    ∀ {n : ℕ}, (∀ k < n, G.reachIter u (k + 1) ≠ G.reachIter u k) →
      n + 1 ≤ (G.reachIter u n).card
  | 0, _ => by simp [reachIter]
  | n + 1, h => by
    have ih := card_reachIter_of_ne (n := n) (fun k hk => h k (Nat.lt_succ_of_lt hk))
    have hss : G.reachIter u n ⊂ G.reachIter u (n + 1) :=
      Finset.ssubset_iff_subset_ne.2 ⟨reachIter_subset_succ u n, (h n (Nat.lt_succ_self n)).symm⟩
    have := Finset.card_lt_card hss
    omega

theorem reachIter_subset_reachFinset (u : V) (n : ℕ) : G.reachIter u n ⊆ G.reachFinset u := by
  rcases le_total n (Fintype.card V) with hn | hn
  · exact reachIter_mono u hn
  · have hk : ∃ k < Fintype.card V, G.reachIter u (k + 1) = G.reachIter u k := by
      by_contra hcon
      push Not at hcon
      have h1 := card_reachIter_of_ne (G := G) (u := u) hcon
      have h2 := Finset.card_le_univ (G.reachIter u (Fintype.card V))
      omega
    obtain ⟨k, hk, hkeq⟩ := hk
    rw [reachIter_eq_of_succ_eq hkeq (hk.le.trans hn), reachFinset,
      reachIter_eq_of_succ_eq hkeq hk.le]

/-- Correctness of saturation: `w ∈ G.reachFinset u` exactly when `w` is reachable from `u`. -/
@[simp] theorem mem_reachFinset {u w : V} : w ∈ G.reachFinset u ↔ ReflTransGen G.Adj u w := by
  refine ⟨reflTransGen_of_mem_reachIter, fun h => ?_⟩
  obtain ⟨n, hn⟩ := exists_mem_reachIter h
  exact reachIter_subset_reachFinset u n hn

@[simp, norm_cast] theorem coe_reachFinset (u : V) :
    (G.reachFinset u : Set V) = G.descendantsOf {u} := by
  ext; simp

instance decidableReflTransGen (u v : V) : Decidable (ReflTransGen G.Adj u v) :=
  decidable_of_iff _ mem_reachFinset

instance decidableIsAncestor (u v : V) : Decidable (G.IsAncestor u v) :=
  decidable_of_iff (∃ x ∈ G.childrenFinset u, v ∈ G.reachFinset x) <| by
    simp [IsAncestor, TransGen.head'_iff]

variable (G)

/-- The strict ancestors of `v` as a finset, for a finite vertex type with decidable adjacency.
-/
def ancestorsFinset (v : V) : Finset V := Finset.univ.filter (fun u => G.IsAncestor u v)

/-- The strict descendants of `v` as a finset, for a finite vertex type with decidable
adjacency. -/
def descendantsFinset (v : V) : Finset V := Finset.univ.filter (fun w => G.IsAncestor v w)

variable {G}

@[simp] theorem mem_ancestorsFinset {u v : V} : u ∈ G.ancestorsFinset v ↔ G.IsAncestor u v := by
  simp [ancestorsFinset]

@[simp] theorem mem_descendantsFinset {v w : V} :
    w ∈ G.descendantsFinset v ↔ G.IsAncestor v w := by
  simp [descendantsFinset]

@[simp, norm_cast] theorem coe_ancestorsFinset (v : V) :
    (G.ancestorsFinset v : Set V) = G.ancestors v := by
  ext; simp

@[simp, norm_cast] theorem coe_descendantsFinset (v : V) :
    (G.descendantsFinset v : Set V) = G.descendants v := by
  ext; simp

end Finite

end Digraph
