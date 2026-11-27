/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Graphical.Criteria.FrontDoor
public import CausalInference.Graphical.DSeparationExamples

/-!
# Common ancestors and marginal d-separation

The graph core of Pearl's common-cause principle (Theorem 6.4.3): with no adjustment, the
back-door criterion for `(x, y)` holds exactly when `x` and `y` have no common ancestor, where,
as footnote 19 of Pearl (2009) asks, ancestors that reach `y` only through `x` do not count.

## Main results

* `Digraph.dConn_singleton_empty_iff`: in any digraph, `x` and `y` are d-connected given the
  empty set exactly when they have a common ancestor in the reflexive sense: a vertex `a` with
  directed paths (of length zero or more) to `x` and to `y`. An active trail given the empty
  set has no collider, so it is a pair of directed paths out of its top vertex.
* `Digraph.deleteOutgoing_dSep_empty_iff`: `x` and `y` are d-separated by the empty set in
  `G.deleteOutgoing {x}` exactly when no vertex `a` has a directed path to `x` in `G` and a
  directed path to `y` in `G` that does not leave `x`. The treatment of `x` itself: `x` counts
  as such a common ancestor only when `y = x` (`Digraph.reflTransGen_deleteOutgoing_self_iff`),
  and an ancestor of `y` counts only through a directed path that avoids `x` (as an
  intermediate vertex).
* `Digraph.backDoor_empty_iff`: the same statement for the back-door criterion with the empty
  adjustment set.
* Examples by `decide`.

No acyclicity is needed for these graph statements, although Pearl states the principle for
acyclic diagrams.

## References

* J. Pearl (2009), *Causality: Models, Reasoning, and Inference*, 2nd edition, section 6.4.2,
  Theorem 6.4.3 (Common-Cause Principle) and footnote 19.
-/

@[expose] public section

namespace Digraph

open Relation

variable {V : Type*} {G : Digraph V} {Y : Set V} {x y a : V}

/-- A directed path into `x` read backward is an active trail given the empty set. -/
theorem reflTransGen_bayesBall_empty_of_reflTransGen (h : ReflTransGen G.Adj a x) :
    ReflTransGen (G.bayesBall ∅).Adj (x, false) (a, false) := by
  induction h using ReflTransGen.head_induction_on with
  | refl => exact ReflTransGen.refl
  | @head a b hab _ ih => exact ih.tail (bayesBall_adj_false_false.2 ⟨hab, Set.notMem_empty b⟩)

/-- In any digraph, `x` and `y` are d-connected given the empty set exactly when some vertex has
directed paths (of length zero or more) to both. -/
theorem dConn_singleton_empty_iff :
    G.DConn {x} {y} ∅ ↔ ∃ a, ReflTransGen G.Adj a x ∧ ReflTransGen G.Adj a y := by
  constructor
  · have inv : ∀ s : V × Bool, ReflTransGen (G.bayesBall ∅).Adj (x, false) s →
        (s.2 = false → ReflTransGen G.Adj s.1 x) ∧
          (s.2 = true → ∃ a, ReflTransGen G.Adj a x ∧ ReflTransGen G.Adj a s.1) := by
      intro s hs
      induction hs with
      | refl => exact ⟨fun _ => ReflTransGen.refl, fun h => Bool.noConfusion h⟩
      | @tail t₁ t₂ _ h₁₂ ih =>
        obtain ⟨u, f⟩ := t₁
        obtain ⟨w, c⟩ := t₂
        cases c
        · cases f
          · have hwu := (bayesBall_adj_false_false.1 h₁₂).1
            exact ⟨fun _ => ReflTransGen.head hwu (ih.1 rfl),
              fun h => Bool.noConfusion h⟩
          · have := (bayesBall_adj_true_false.1 h₁₂).2
            rw [ancestorsOf_empty] at this
            exact this.elim
        · have huw := (bayesBall_adj_true.1 h₁₂).1
          refine ⟨fun h => Bool.noConfusion h, fun _ => ?_⟩
          cases f
          · exact ⟨u, ih.1 rfl, ReflTransGen.single huw⟩
          · obtain ⟨a, hax, hau⟩ := ih.2 rfl
            exact ⟨a, hax, hau.tail huw⟩
    rintro ⟨x', hx', y', hy', -, -, b, h⟩
    rw [Set.mem_singleton_iff] at hx' hy'
    rw [hx', hy'] at h
    cases b
    · exact ⟨y, (inv _ h).1 rfl, ReflTransGen.refl⟩
    · exact (inv _ h).2 rfl
  · rintro ⟨a, hax, hay⟩
    obtain ⟨c, hc⟩ := exists_reflTransGen_bayesBall_of_reflTransGen hay
      (by simp : a ∉ G.ancestorsOf ∅) false
    exact ⟨x, rfl, y, rfl, Set.notMem_empty x, Set.notMem_empty y, c,
      (reflTransGen_bayesBall_empty_of_reflTransGen hax).trans hc⟩

/-- After deleting the edges out of `x`, the vertices reachable from `x` are `x` alone. -/
theorem reflTransGen_deleteOutgoing_self_iff :
    ReflTransGen (G.deleteOutgoing {x}).Adj x y ↔ y = x := by
  constructor
  · intro h
    rcases h.cases_head with h | ⟨c, hxc, -⟩
    · exact h.symm
    · exact absurd rfl hxc.2
  · rintro rfl
    exact ReflTransGen.refl

/-- A directed path into `x` can be cut at its first visit to `x`, so the paths into `x` are
the same in `G` and in `G.deleteOutgoing {x}`. -/
theorem reflTransGen_deleteOutgoing_iff_into :
    ReflTransGen (G.deleteOutgoing {x}).Adj a x ↔ ReflTransGen G.Adj a x := by
  constructor
  · exact reflTransGen_mono deleteOutgoing_le
  · intro h
    obtain ⟨s, hs, hp⟩ := exists_reflTransGen_deleteOutgoing h (Set.mem_singleton x)
    rw [Set.mem_singleton_iff] at hs
    exact hs ▸ hp

/-- The graph lemma behind the common-cause principle (Pearl 2009, section 6.4.2): `x` and `y`
are d-separated by the empty set in `G.deleteOutgoing {x}` exactly when no vertex `a` has a
directed path to `x` in `G` and a directed path to `y` that does not leave `x`. -/
theorem deleteOutgoing_dSep_empty_iff :
    (G.deleteOutgoing {x}).DSep {x} {y} ∅ ↔
      ¬ ∃ a, ReflTransGen G.Adj a x ∧ ReflTransGen (G.deleteOutgoing {x}).Adj a y := by
  rw [DSep, dConn_singleton_empty_iff]
  simp only [reflTransGen_deleteOutgoing_iff_into]

/-- The back-door criterion with the empty adjustment set holds for `(x, y)` exactly when `x`
and `y` have no common ancestor in the sense of `Digraph.deleteOutgoing_dSep_empty_iff`. -/
theorem backDoor_empty_iff :
    G.BackDoor {x} {y} ∅ ↔
      ¬ ∃ a, ReflTransGen G.Adj a x ∧ ReflTransGen (G.deleteOutgoing {x}).Adj a y := by
  rw [← deleteOutgoing_dSep_empty_iff]
  exact ⟨fun h => h.2, fun h => ⟨fun _ hz => hz.elim, h⟩⟩

end Digraph

namespace CausalInference.CommonAncestorExamples

open DSeparationExamples Criteria

-- The back-door graph `Z → X`, `Z → Y`, `X → Y`: `Z` is a common ancestor of `X` and `Y`.
example : ¬ (backdoor.deleteOutgoing {1}).DSep {1} {2} ∅ := by decide +kernel
-- The M-structure: `X` and `Y` have no common ancestor.
example : (mStructure.deleteOutgoing {0}).DSep {0} {4} ∅ := by decide +kernel

/-- An ancestor that reaches `y` only through `x` does not count (footnote 19, node `E` of
Figure 6.3): `E → X → Y` with `E = 0`, `X = 1`, `Y = 2`. -/
abbrev throughTreatment : Digraph (Fin 3) := ofEdges [(0, 1), (1, 2)]

example : (throughTreatment.deleteOutgoing {1}).DSep {1} {2} ∅ := by decide +kernel

end CausalInference.CommonAncestorExamples
