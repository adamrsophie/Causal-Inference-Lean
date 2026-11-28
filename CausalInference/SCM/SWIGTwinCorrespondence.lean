/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.SCM.SWIGTwinGeneral

/-!
# The correspondence between the SWIG and the twin graph of one treatment

For one treatment `i`, the separation statements of the SWIG of `do(i)` are those of the graph
`G.deleteOutgoing {i}` of its random halves (`Digraph.swigSep_iff`). This file collects the
facts that relate that graph to the twin graph `twinGraph G {i}` and to the corrected
conditioning set `Digraph.twinCond G i C` of `CausalInference.SCM.SWIGTwinGeneral`; they are
used in `CausalInference.SCM.SWIGTwinSeparation` to prove that the two separations agree.

## Vertices

A vertex `v` of the SWIG is sent to `Digraph.twinVertex i v`: the factual copy of `i` for `i`,
the counterfactual copy `v*` otherwise. Three kinds of vertices play different roles:

* the treatment `i`, which lives in the factual layer;
* the proper descendants of `i` (`ReflTransGen G.Adj i v` and `v ≠ i`), which live in the
  counterfactual layer; their factual copies are never ancestors of the corrected
  conditioning set (`Digraph.fact_notMem_ancestorsOf_twinCond`), so a twin trail that enters
  them never comes back;
* the nondescendants of `i`, which have both copies, conditioned together
  (`Digraph.inr_inl_mem_twinCond`, `Digraph.inr_inr_mem_twinCond`), and joined through their
  shared noise vertex.

## Main results

* Adjacency of the twin graph for every pair of vertex kinds, the five impossible pairs
  included (`Digraph.twinGraph_not_adj_fact_noise` and the others).
* Edges: an edge `u → v` of the SWIG with `v ≠ i` is the edge `u* → v*` of the twin graph
  (`Digraph.deleteOutgoing_adj_iff_twinGraph_cf`); an edge `u → i` is the factual edge
  `u → i` (`Digraph.deleteOutgoing_adj_self_iff_twinGraph_fact`), and `u` is then a
  nondescendant of `i` (`Digraph.IsAcyclic.not_reflTransGen_of_adj_self`).
* Directed paths of the twin graph stay in their layer (`Digraph.reflTransGen_twinGraph_fact`,
  `Digraph.reflTransGen_twinGraph_cf`).
* Ancestors of the conditioning sets: `Digraph.mem_ancestorsOf_of_cf_mem_ancestorsOf_twinCond`,
  `Digraph.mem_ancestorsOf_of_fact_mem_ancestorsOf_twinCond` (from the twin graph to the SWIG)
  and `Digraph.cf_or_fact_mem_ancestorsOf_twinCond` (back), with
  `Digraph.mem_of_self_mem_ancestorsOf_deleteOutgoing` for the treatment itself.
* `Digraph.passes_of_passes_twin_cf`, `Digraph.passes_of_passes_twin_fact`: a twin trail that
  may pass a counterfactual copy, or the factual copy of a vertex that is not a proper
  descendant of `i`, may pass the vertex itself in the SWIG with the same flags.
-/

@[expose] public section

namespace Digraph

open Finset Relation CausalInference.SCM

variable {V : Type*}

/-! ### Adjacency in the twin graph -/

section Adjacency

variable {G : Digraph V} {X : Finset V} {u v : V}

theorem twinGraph_not_adj_noise_noise : ¬ (twinGraph G X).Adj (.inl u) (.inl v) := id

theorem twinGraph_not_adj_fact_noise : ¬ (twinGraph G X).Adj (.inr (.inl u)) (.inl v) := id

theorem twinGraph_not_adj_cf_noise : ¬ (twinGraph G X).Adj (.inr (.inr u)) (.inl v) := id

theorem twinGraph_not_adj_fact_cf : ¬ (twinGraph G X).Adj (.inr (.inl u)) (.inr (.inr v)) := id

theorem twinGraph_not_adj_cf_fact : ¬ (twinGraph G X).Adj (.inr (.inr u)) (.inr (.inl v)) := id

/-- A directed path of the twin graph from a factual copy stays in the factual layer, where it
is a directed path of `G`. -/
theorem reflTransGen_twinGraph_fact {z : V ⊕ V ⊕ V}
    (h : ReflTransGen (twinGraph G X).Adj (.inr (.inl v)) z) :
    ∃ w, z = .inr (.inl w) ∧ ReflTransGen G.Adj v w := by
  induction h with
  | refl => exact ⟨v, rfl, .refl⟩
  | @tail b c _ hbc ih =>
    obtain ⟨w, rfl, hw⟩ := ih
    rcases c with c | c | c
    · exact absurd hbc twinGraph_not_adj_fact_noise
    · exact ⟨c, rfl, hw.tail hbc⟩
    · exact absurd hbc twinGraph_not_adj_fact_cf

/-- A directed path of `G` is a directed path of the factual layer of the twin graph. -/
theorem reflTransGen_twinGraph_fact_of {w : V} (h : ReflTransGen G.Adj v w) :
    ReflTransGen (twinGraph G X).Adj (.inr (.inl v)) (.inr (.inl w)) :=
  h.lift (fun a : V => (Sum.inr (Sum.inl a) : V ⊕ V ⊕ V)) fun _ _ h => h

end Adjacency

/-! ### Edges of the SWIG -/

section Edges

variable {G : Digraph V} {i u v : V}

/-- **An edge of the SWIG into a vertex other than the treatment** is the edge between the
counterfactual copies. -/
theorem deleteOutgoing_adj_iff_twinGraph_cf (hv : v ≠ i) :
    (G.deleteOutgoing {i}).Adj u v ↔
      u ≠ i ∧ (twinGraph G {i}).Adj (.inr (.inr u)) (.inr (.inr v)) := by
  rw [deleteOutgoing_adj, twinGraph_adj_cf_cf]
  simp [hv, and_comm]

/-- **An edge of the SWIG into the treatment** is the edge between the factual copies. -/
theorem deleteOutgoing_adj_self_iff_twinGraph_fact :
    (G.deleteOutgoing {i}).Adj u i ↔
      u ≠ i ∧ (twinGraph G {i}).Adj (.inr (.inl u)) (.inr (.inl i)) := by
  rw [deleteOutgoing_adj, twinGraph_adj_fact_fact]
  simp [and_comm]

/-- In an acyclic graph a parent of the treatment is not a descendant of it. -/
theorem IsAcyclic.not_reflTransGen_of_adj_self (hG : G.IsAcyclic) (h : G.Adj u i) :
    ¬ ReflTransGen G.Adj i u := fun hiu => hG i (TransGen.tail' hiu h)

/-- The parents of a nondescendant of `i` are nondescendants of `i`. -/
theorem not_reflTransGen_of_adj (hv : ¬ ReflTransGen G.Adj i v) (h : G.Adj u v) :
    ¬ ReflTransGen G.Adj i u := fun hiu => hv (hiu.tail h)

/-- A proper descendant of `i` is not a parent of `i` when `G` is acyclic. -/
theorem IsAcyclic.ne_of_reflTransGen_of_adj (hG : G.IsAcyclic) (hd : ReflTransGen G.Adj i u)
    (h : G.Adj u v) : v ≠ i := by
  rintro rfl
  exact hG.not_reflTransGen_of_adj_self h hd

/-- A directed path of `G` ending at a vertex that is not a proper descendant of `i` does not
leave `i`, so it is a directed path of `G.deleteOutgoing {i}`. -/
theorem reflTransGen_deleteOutgoing_of {w : V} (h : ReflTransGen G.Adj u w)
    (hw : ¬ TransGen G.Adj i w) : ReflTransGen (G.deleteOutgoing {i}).Adj u w := by
  induction h with
  | refl => exact .refl
  | @tail x y _ hxy ih =>
    have hxi : x ≠ i := by
      rintro rfl
      exact hw (.single hxy)
    exact (ih fun h => hw (h.tail hxy)).tail (deleteOutgoing_adj.2 ⟨hxy, by simpa using hxi⟩)

/-- In `G.deleteOutgoing {i}` the treatment is an ancestor of a set only when it belongs to
the set. -/
theorem mem_of_self_mem_ancestorsOf_deleteOutgoing {C : Set V}
    (h : i ∈ (G.deleteOutgoing {i}).ancestorsOf C) : i ∈ C := by
  obtain ⟨c, hc, hp⟩ := h
  rcases hp.cases_head with rfl | ⟨x, hx, -⟩
  · exact hc
  · exact absurd (deleteOutgoing_adj.1 hx).2 (by simp)

/-- A directed path of the counterfactual layer of the twin graph from a vertex other than the
treatment stays in that layer, avoids `i*`, and is a directed path of `G.deleteOutgoing {i}`. -/
theorem reflTransGen_twinGraph_cf {z : V ⊕ V ⊕ V}
    (h : ReflTransGen (twinGraph G {i}).Adj (.inr (.inr v)) z) (hv : v ≠ i) :
    ∃ w, z = .inr (.inr w) ∧ w ≠ i ∧ ReflTransGen (G.deleteOutgoing {i}).Adj v w := by
  induction h with
  | refl => exact ⟨v, rfl, hv, .refl⟩
  | @tail b c _ hbc ih =>
    obtain ⟨w, rfl, hwi, hw⟩ := ih
    rcases c with c | c | c
    · exact absurd hbc twinGraph_not_adj_cf_noise
    · exact absurd hbc twinGraph_not_adj_cf_fact
    · obtain ⟨hwc, hci⟩ := twinGraph_adj_cf_cf.1 hbc
      have hci : c ≠ i := by simpa using hci
      exact ⟨c, rfl, hci, hw.tail (deleteOutgoing_adj.2 ⟨hwc, by simpa using hwi⟩)⟩

end Edges

/-! ### The corrected conditioning set -/

section Vertex

variable [DecidableEq V] {i v : V}

theorem twinVertex_self : twinVertex i i = .inr (.inl i) := by simp [twinVertex]

theorem twinVertex_of_ne (hv : v ≠ i) : twinVertex i v = .inr (.inr v) := by
  simp [twinVertex, hv]

theorem twinVertex_injective : Function.Injective (twinVertex i) := by
  intro u v h
  by_cases hu : u = i <;> by_cases hv : v = i <;>
    simp_all [twinVertex_self, twinVertex_of_ne]

end Vertex

section Cond

variable [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj] {i v : V}
  {C : Finset V}

/-- No noise vertex is conditioned on. -/
theorem inl_notMem_twinCond {u : V} : (.inl u : V ⊕ V ⊕ V) ∉ G.twinCond i C := by
  simp only [twinCond, mem_insert, mem_union, mem_image, mem_filter, reduceCtorEq, false_or,
    and_false, exists_false, or_false]
  rintro ⟨c, -, hc⟩
  by_cases hci : c = i
  · simp [hci, twinVertex_self] at hc
  · simp [twinVertex_of_ne hci] at hc

/-- **The factual copy of `v` is conditioned on** exactly when `v ∈ C` and `v` is the treatment
or a nondescendant of it. -/
theorem inr_inl_mem_twinCond :
    (.inr (.inl v) : V ⊕ V ⊕ V) ∈ G.twinCond i C ↔
      v ∈ C ∧ (v = i ∨ ¬ ReflTransGen G.Adj i v) := by
  simp only [twinCond, mem_insert, mem_union, mem_image, mem_filter, reduceCtorEq, false_or,
    Sum.inr.injEq, Sum.inl.injEq]
  constructor
  · rintro (⟨c, hc, he⟩ | ⟨c, ⟨hc, hci⟩, rfl⟩)
    · by_cases hci : c = i
      · subst hci
        rw [twinVertex_self] at he
        cases he
        exact ⟨hc, Or.inl rfl⟩
      · simp [twinVertex_of_ne hci] at he
    · exact ⟨hc, Or.inr hci⟩
  · rintro ⟨hv, rfl | hvi⟩
    · exact Or.inl ⟨v, hv, twinVertex_self⟩
    · exact Or.inr ⟨v, ⟨hv, hvi⟩, rfl⟩

/-- **The counterfactual copy of `v` is conditioned on** exactly when `v` is the treatment or
`v ∈ C`. -/
theorem inr_inr_mem_twinCond :
    (.inr (.inr v) : V ⊕ V ⊕ V) ∈ G.twinCond i C ↔ v = i ∨ v ∈ C := by
  simp only [twinCond, mem_insert, mem_union, mem_image, mem_filter, Sum.inr.injEq,
    reduceCtorEq, and_false, exists_false, or_false]
  constructor
  · rintro (rfl | ⟨c, hc, he⟩)
    · exact Or.inl rfl
    · by_cases hci : c = i
      · simp [hci, twinVertex_self] at he
      · rw [twinVertex_of_ne hci] at he
        cases he
        exact Or.inr hc
  · rintro (rfl | hv)
    · exact Or.inl rfl
    · by_cases hvi : v = i
      · exact Or.inl hvi
      · exact Or.inr ⟨v, hv, twinVertex_of_ne hvi⟩

/-- The twin vertex of `v` is conditioned on exactly when `v ∈ C`. -/
theorem twinVertex_mem_twinCond : twinVertex i v ∈ G.twinCond i C ↔ v ∈ C := by
  by_cases hvi : v = i
  · subst hvi
    rw [twinVertex_self, inr_inl_mem_twinCond]
    simp
  · rw [twinVertex_of_ne hvi, inr_inr_mem_twinCond]
    simp [hvi]

/-! ### Ancestors of the conditioning sets -/

/-- A counterfactual copy that is an ancestor of the corrected set is, for a vertex other than
the treatment, an ancestor of `C` in the SWIG. -/
theorem mem_ancestorsOf_of_cf_mem_ancestorsOf_twinCond (hv : v ≠ i)
    (h : (.inr (.inr v) : V ⊕ V ⊕ V) ∈ (twinGraph G {i}).ancestorsOf ↑(G.twinCond i C)) :
    v ∈ (G.deleteOutgoing {i}).ancestorsOf ↑C := by
  obtain ⟨z, hz, hp⟩ := h
  obtain ⟨w, rfl, hwi, hw⟩ := reflTransGen_twinGraph_cf hp hv
  exact ⟨w, (inr_inr_mem_twinCond.1 hz).resolve_left hwi, hw⟩

/-- A factual copy that is an ancestor of the corrected set comes from an ancestor of `C` in
the SWIG. -/
theorem mem_ancestorsOf_of_fact_mem_ancestorsOf_twinCond (hG : G.IsAcyclic)
    (h : (.inr (.inl v) : V ⊕ V ⊕ V) ∈ (twinGraph G {i}).ancestorsOf ↑(G.twinCond i C)) :
    v ∈ (G.deleteOutgoing {i}).ancestorsOf ↑C := by
  obtain ⟨z, hz, hp⟩ := h
  obtain ⟨w, rfl, hw⟩ := reflTransGen_twinGraph_fact hp
  obtain ⟨hwC, hwi⟩ := inr_inl_mem_twinCond.1 hz
  refine ⟨w, hwC, reflTransGen_deleteOutgoing_of hw fun hiw => ?_⟩
  rcases hwi with rfl | hwi
  · exact hG w hiw
  · exact hwi hiw.to_reflTransGen

/-- **The factual copy of a proper descendant of `i` is never an ancestor of the corrected
set**: its factual descendants are descendants of `i`, of which only `i` could be
conditioned, and `i` is not below it. -/
theorem fact_notMem_ancestorsOf_twinCond (hG : G.IsAcyclic) (hd : ReflTransGen G.Adj i v)
    (hvi : v ≠ i) :
    (.inr (.inl v) : V ⊕ V ⊕ V) ∉ (twinGraph G {i}).ancestorsOf ↑(G.twinCond i C) := by
  rintro ⟨z, hz, hp⟩
  obtain ⟨w, rfl, hw⟩ := reflTransGen_twinGraph_fact hp
  obtain ⟨-, hwi⟩ := inr_inl_mem_twinCond.1 hz
  rcases hwi with rfl | hwi
  · obtain hiv := (reflTransGen_iff_eq_or_transGen.1 hd).resolve_left hvi
    exact hG w (hiv.trans_left hw)
  · exact hwi (hd.trans hw)

/-- **An ancestor of `C` in the SWIG**, other than the treatment, has a copy that is an ancestor
of the corrected set: the counterfactual one when the directed path to `C` avoids `i`, the
factual one when it ends at `i`. -/
theorem cf_or_fact_mem_ancestorsOf_twinCond (hv : v ≠ i)
    (h : v ∈ (G.deleteOutgoing {i}).ancestorsOf ↑C) :
    (.inr (.inr v) : V ⊕ V ⊕ V) ∈ (twinGraph G {i}).ancestorsOf ↑(G.twinCond i C) ∨
      (.inr (.inl v) : V ⊕ V ⊕ V) ∈ (twinGraph G {i}).ancestorsOf ↑(G.twinCond i C) := by
  obtain ⟨c, hc, hp⟩ := h
  have key : ∀ x, ReflTransGen (G.deleteOutgoing {i}).Adj v x →
      (x ≠ i ∧ ReflTransGen (twinGraph G {i}).Adj (.inr (.inr v)) (.inr (.inr x))) ∨
        (x = i ∧ ReflTransGen (twinGraph G {i}).Adj (.inr (.inl v)) (.inr (.inl i))) := by
    intro x hx
    induction hx with
    | refl => exact Or.inl ⟨hv, .refl⟩
    | @tail x y hvx hxy ih =>
      obtain ⟨hxy', hxi⟩ := deleteOutgoing_adj.1 hxy
      have hxi : x ≠ i := by simpa using hxi
      rcases ih with ⟨-, hcf⟩ | ⟨rfl, -⟩
      · by_cases hyi : y = i
        · subst hyi
          exact Or.inr ⟨rfl, reflTransGen_twinGraph_fact_of
            (reflTransGen_mono deleteOutgoing_le (hvx.tail hxy))⟩
        · exact Or.inl ⟨hyi, hcf.tail (twinGraph_adj_cf_cf.2 ⟨hxy', by simpa using hyi⟩)⟩
      · exact absurd rfl hxi
  rcases key c hp with ⟨hci, hcf⟩ | ⟨rfl, hf⟩
  · exact Or.inl ⟨_, inr_inr_mem_twinCond.2 (Or.inr hc), hcf⟩
  · exact Or.inr ⟨_, inr_inl_mem_twinCond.2 ⟨hc, Or.inl rfl⟩, hf⟩

/-! ### Passing a vertex -/

/-- A twin trail that may pass the counterfactual copy of a vertex other than the treatment may
pass the vertex in the SWIG with the same flags. -/
theorem passes_of_passes_twin_cf (hv : v ≠ i) {b c : Bool}
    (h : (twinGraph G {i}).Passes ↑(G.twinCond i C) (.inr (.inr v)) b c) :
    (G.deleteOutgoing {i}).Passes ↑C v b c := by
  unfold Passes at h ⊢
  split_ifs at h ⊢
  · exact mem_ancestorsOf_of_cf_mem_ancestorsOf_twinCond hv h
  · exact fun hC => h (mem_coe.2 (inr_inr_mem_twinCond.2 (Or.inr hC)))

/-- A twin trail that may pass the factual copy of a vertex that is not a proper descendant of
the treatment may pass the vertex in the SWIG with the same flags. -/
theorem passes_of_passes_twin_fact (hG : G.IsAcyclic) (hv : v = i ∨ ¬ ReflTransGen G.Adj i v)
    {b c : Bool} (h : (twinGraph G {i}).Passes ↑(G.twinCond i C) (.inr (.inl v)) b c) :
    (G.deleteOutgoing {i}).Passes ↑C v b c := by
  unfold Passes at h ⊢
  split_ifs at h ⊢
  · exact mem_ancestorsOf_of_fact_mem_ancestorsOf_twinCond hG h
  · exact fun hC => h (mem_coe.2 (inr_inl_mem_twinCond.2 ⟨hC, hv⟩))

end Cond

end Digraph
