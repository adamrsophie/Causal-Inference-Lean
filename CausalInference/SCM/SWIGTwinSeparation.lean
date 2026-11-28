/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.SCM.SWIGTwinCorrespondence

/-!
# SWIG separation is twin graph separation given the corrected set

For an acyclic graph `G`, one treatment `i` and arbitrary finite sets `S`, `T`, `C`, the SWIG of
`do(i)` separates `S` from `T` given `C` exactly when the twin graph separates their twin
vertices given the corrected conditioning set `Digraph.twinCond G i C`
(`Digraph.swigSep_iff_twinSep`). No disjointness is needed, and `i` may belong to any of the
sets. Acyclicity cannot be dropped (`SWIGTwinSeparation.cycle_swigSep_not_twinSep`).

## Proof

Both directions simulate the Bayes-ball state graph of one graph in the other, by induction on
its paths, with the SWIG replaced by the graph `G.deleteOutgoing {i}` of its random halves
(`Digraph.swigSep_iff`).

* From the twin graph to the SWIG (`Digraph.TwinToSWIG`): a twin state at a counterfactual copy,
  or at the factual copy of a vertex that is not a proper descendant of `i`, is matched by a
  SWIG state at the same vertex that may leave in every direction the twin state may leave. A
  twin state at a noise vertex `U_v` is matched by a SWIG state at `v` that may leave upward.
  The other twin states are dead ends: `i*` is conditioned and has no parent, and the factual
  copies of proper descendants of `i` are entered through an arrowhead and are never ancestors
  of the corrected set.
* From the SWIG to the twin graph (`Digraph.SWIGToTwin`): a SWIG state at `i` is matched at the
  factual copy, a state at a proper descendant of `i` at the counterfactual copy, and a state at
  a nondescendant `v` at one copy; when `v ∉ C` the other copy is also reached, entered through
  an arrowhead from the shared noise vertex, so that the trail can go on in the layer that the
  next step needs (the factual one into `i`, the counterfactual one into a proper descendant,
  the one with a conditioned descendant at a collider).

## Main results

* `Digraph.exists_reflTransGen_swig_of_twin`, `Digraph.exists_reflTransGen_twin_of_swig`: the
  two simulations.
* `Digraph.swigSep_iff_twinSep`: the equivalence.
* `Digraph.twinSep_iff_backDoor`: for a set `L` of nondescendants of `i`, the twin graph
  separates the factual `i` from the counterfactual outcomes given the corrected set of `L`
  exactly when `L` satisfies the back-door criterion.
* `SWIGTwinSeparation`: the examples of `CausalInference.SCM.SWIGTwinGeneral` as corollaries,
  and a cyclic countermodel.
-/

@[expose] public section

namespace Digraph

open Finset Relation CausalInference.SCM

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj] {i : V}
  {C : Finset V}

/-! ### Passing helpers -/

omit [Fintype V] [DecidableEq V] in
theorem passes_true_iff {H : Digraph V} {Z : Set V} {v : V} {b : Bool} :
    H.Passes Z v b true ↔ v ∉ Z := by
  cases b <;> simp [Passes]

omit [Fintype V] [DecidableEq V] in
/-- A state that may leave upward and another that may leave downward at the same vertex give a
state that may leave in every direction the second one may. -/
theorem passes_of_passes_up {H : Digraph V} {Z : Set V} {v : V} {b c : Bool}
    (hup : H.Passes Z v b false) (h : H.Passes Z v true c) : H.Passes Z v b c := by
  cases c
  · exact hup
  · exact passes_true_iff.2 (passes_true_iff.1 h)

omit [Fintype V] [DecidableEq V] in
theorem bayesBall_adj_false_iff {H : Digraph V} {Z : Set V} {v w : V} {b : Bool} :
    (H.bayesBall Z).Adj (v, b) (w, false) ↔ H.Adj w v ∧ H.Passes Z v b false := by
  simp [bayesBall]

/-! ### From the twin graph to the SWIG -/

/-- **The invariant of the simulation of the twin graph in the SWIG**, for trails from the
twin vertex of `x`. A state at a noise vertex `U_v` is entered from a child, and some SWIG state
at `v`, reached from `x`, may leave `v` upward. A state at the factual copy of a proper
descendant of `i` is entered through an arrowhead. A state at `i*` is entered from a child. At
any other vertex some SWIG state at the same vertex, reached from `x`, may leave in every
direction the twin state may leave. -/
def TwinToSWIG (G : Digraph V) [DecidableRel G.Adj] (i : V) (C : Finset V) (x : V) :
    (V ⊕ V ⊕ V) × Bool → Prop
  | (.inl v, b) => b = false ∧ ∃ b', ReflTransGen ((G.deleteOutgoing {i}).bayesBall ↑C).Adj
      (x, false) (v, b') ∧ (G.deleteOutgoing {i}).Passes ↑C v b' false
  | (.inr (.inl v), b) => (ReflTransGen G.Adj i v ∧ v ≠ i ∧ b = true) ∨
      ((v = i ∨ ¬ ReflTransGen G.Adj i v) ∧ ∃ b',
        ReflTransGen ((G.deleteOutgoing {i}).bayesBall ↑C).Adj (x, false) (v, b') ∧
        ∀ c, (twinGraph G {i}).Passes ↑(G.twinCond i C) (.inr (.inl v)) b c →
          (G.deleteOutgoing {i}).Passes ↑C v b' c)
  | (.inr (.inr v), b) => (v = i ∧ b = false) ∨ (v ≠ i ∧ ∃ b',
        ReflTransGen ((G.deleteOutgoing {i}).bayesBall ↑C).Adj (x, false) (v, b') ∧
        ∀ c, (twinGraph G {i}).Passes ↑(G.twinCond i C) (.inr (.inr v)) b c →
          (G.deleteOutgoing {i}).Passes ↑C v b' c)

variable {x : V}

/-- A SWIG state at a vertex that is not a proper descendant of `i` matches the twin state at
its factual copy with the same flag. -/
theorem twinToSWIG_fact (hG : G.IsAcyclic) {v : V} {b : Bool}
    (hv : v = i ∨ ¬ ReflTransGen G.Adj i v)
    (h : ReflTransGen ((G.deleteOutgoing {i}).bayesBall ↑C).Adj (x, false) (v, b)) :
    TwinToSWIG G i C x (.inr (.inl v), b) :=
  Or.inr ⟨hv, b, h, fun _ hc => passes_of_passes_twin_fact hG hv hc⟩

/-- A SWIG state at a vertex entered through an arrowhead matches the twin state at its factual
copy entered through an arrowhead. -/
theorem twinToSWIG_fact_true (hG : G.IsAcyclic) {v : V}
    (h : ReflTransGen ((G.deleteOutgoing {i}).bayesBall ↑C).Adj (x, false) (v, true)) :
    TwinToSWIG G i C x (.inr (.inl v), true) := by
  by_cases hd : ReflTransGen G.Adj i v ∧ v ≠ i
  · exact Or.inl ⟨hd.1, hd.2, rfl⟩
  · refine twinToSWIG_fact hG ?_ h
    by_cases hvi : v = i
    · exact Or.inl hvi
    · exact Or.inr fun hiv => hd ⟨hiv, hvi⟩

/-- A SWIG state at a vertex other than `i` matches the twin state at its counterfactual copy
with the same flag. -/
theorem twinToSWIG_cf {v : V} {b : Bool} (hv : v ≠ i)
    (h : ReflTransGen ((G.deleteOutgoing {i}).bayesBall ↑C).Adj (x, false) (v, b)) :
    TwinToSWIG G i C x (.inr (.inr v), b) :=
  Or.inr ⟨hv, b, h, fun _ hc => passes_of_passes_twin_cf hv hc⟩

/-- **One step of the simulation of the twin graph in the SWIG.** -/
theorem TwinToSWIG.step (hG : G.IsAcyclic) {s t : (V ⊕ V ⊕ V) × Bool}
    (hs : TwinToSWIG G i C x s)
    (hst : ((twinGraph G {i}).bayesBall ↑(G.twinCond i C)).Adj s t) :
    TwinToSWIG G i C x t := by
  obtain ⟨a, b⟩ := s
  obtain ⟨a', c⟩ := t
  obtain ⟨hedge, hpass⟩ := hst
  rcases a with v | v | v
  · -- a noise vertex: the trail leaves downward, to the factual or the counterfactual copy
    obtain ⟨rfl, b', hR, hup⟩ := hs
    rcases a' with w | w | w <;> cases c <;>
      simp only [Bool.false_eq_true, ↓reduceIte, twinGraph_not_adj_noise_noise,
        twinGraph_not_adj_fact_noise, twinGraph_not_adj_cf_noise, twinGraph_adj_noise_fact,
        twinGraph_adj_noise_cf] at hedge
    · subst hedge
      by_cases hd : ReflTransGen G.Adj i v ∧ v ≠ i
      · exact Or.inl ⟨hd.1, hd.2, rfl⟩
      · have hv : v = i ∨ ¬ ReflTransGen G.Adj i v := by
          by_cases hvi : v = i
          · exact Or.inl hvi
          · exact Or.inr fun hiv => hd ⟨hiv, hvi⟩
        exact Or.inr ⟨hv, b', hR, fun _ hc =>
          passes_of_passes_up hup (passes_of_passes_twin_fact hG hv hc)⟩
    · obtain ⟨rfl, hwi⟩ := hedge
      have hwi : v ≠ i := by simpa using hwi
      exact Or.inr ⟨hwi, b', hR, fun _ hc =>
        passes_of_passes_up hup (passes_of_passes_twin_cf hwi hc)⟩
  · -- a factual copy
    rcases hs with ⟨hd, hvi, rfl⟩ | ⟨hv, b', hR, himp⟩
    · -- a proper descendant of `i`: only downward steps are possible
      cases c
      · exfalso
        simp only [Passes, ↓reduceIte, and_self] at hpass
        exact fact_notMem_ancestorsOf_twinCond hG hd hvi (by simpa using hpass)
      · rcases a' with w | w | w <;>
          simp only [↓reduceIte, twinGraph_not_adj_fact_noise, twinGraph_not_adj_fact_cf,
            twinGraph_adj_fact_fact] at hedge
        exact Or.inl ⟨hd.tail hedge, hG.ne_of_reflTransGen_of_adj hd hedge, rfl⟩
    · have hP := himp c hpass
      rcases a' with w | w | w <;> cases c <;>
        simp only [Bool.false_eq_true, ↓reduceIte, twinGraph_not_adj_fact_noise,
          twinGraph_not_adj_fact_cf, twinGraph_not_adj_cf_fact, twinGraph_adj_noise_fact,
          twinGraph_adj_fact_fact] at hedge
      · -- up to the noise vertex
        subst hedge
        exact ⟨rfl, b', hR, hP⟩
      · -- up to a factual parent, a nondescendant of `i`
        have hw : ¬ ReflTransGen G.Adj i w := by
          rcases hv with rfl | hv
          · exact hG.not_reflTransGen_of_adj_self hedge
          · exact not_reflTransGen_of_adj hv hedge
        have hwi : w ≠ i := fun h => hw (h ▸ .refl)
        refine twinToSWIG_fact hG (Or.inr hw) (hR.tail ?_)
        exact bayesBall_adj_false_iff.2
          ⟨deleteOutgoing_adj.2 ⟨hedge, by simpa using hwi⟩, hP⟩
      · -- down to a factual child
        rcases hv with rfl | hv
        · exact Or.inl ⟨.single hedge, (hG.ne_of_adj hedge).symm, rfl⟩
        · have hvi : v ≠ i := fun h => hv (h ▸ .refl)
          refine twinToSWIG_fact_true hG (hR.tail ?_)
          exact bayesBall_adj_true.2 ⟨deleteOutgoing_adj.2 ⟨hedge, by simpa using hvi⟩,
            passes_true_iff.1 hP⟩
  · -- a counterfactual copy
    rcases hs with ⟨hvi, rfl⟩ | ⟨hvi, b', hR, himp⟩
    · exfalso
      have hmem : (.inr (.inr v) : V ⊕ V ⊕ V) ∈ G.twinCond i C :=
        inr_inr_mem_twinCond.2 (Or.inl hvi)
      cases c <;> simp [Passes, hmem] at hpass
    · have hP := himp c hpass
      rcases a' with w | w | w <;> cases c <;>
        simp only [Bool.false_eq_true, ↓reduceIte, twinGraph_not_adj_cf_noise,
          twinGraph_not_adj_fact_cf, twinGraph_not_adj_cf_fact, twinGraph_adj_noise_cf,
          twinGraph_adj_cf_cf] at hedge
      · -- up to the noise vertex
        obtain ⟨rfl, -⟩ := hedge
        exact ⟨rfl, b', hR, hP⟩
      · -- up to a counterfactual parent
        obtain ⟨hwv, -⟩ := hedge
        by_cases hwi : w = i
        · exact Or.inl ⟨hwi, rfl⟩
        · refine twinToSWIG_cf hwi (hR.tail ?_)
          exact bayesBall_adj_false_iff.2
            ⟨deleteOutgoing_adj.2 ⟨hwv, by simpa using hwi⟩, hP⟩
      · -- down to a counterfactual child
        obtain ⟨hvw, hwi⟩ := hedge
        refine twinToSWIG_cf (by simpa using hwi) (hR.tail ?_)
        exact bayesBall_adj_true.2 ⟨deleteOutgoing_adj.2 ⟨hvw, by simpa using hvi⟩,
          passes_true_iff.1 hP⟩

/-- **From an active twin trail to an active SWIG trail.** A path of the Bayes-ball state graph
of the twin graph, given the corrected set, from the twin vertex of `x` to the twin vertex of
`y` gives a path of the state graph of the SWIG, given `C`, from `x` to `y`. -/
theorem exists_reflTransGen_swig_of_twin (hG : G.IsAcyclic) {y : V} {b : Bool}
    (h : ReflTransGen ((twinGraph G {i}).bayesBall ↑(G.twinCond i C)).Adj
      (twinVertex i x, false) (twinVertex i y, b)) :
    ∃ b', ReflTransGen ((G.deleteOutgoing {i}).bayesBall ↑C).Adj (x, false) (y, b') := by
  have start : TwinToSWIG G i C x (twinVertex i x, false) := by
    by_cases hxi : x = i
    · subst hxi
      rw [twinVertex_self]
      exact twinToSWIG_fact hG (Or.inl rfl) .refl
    · rw [twinVertex_of_ne hxi]
      exact twinToSWIG_cf hxi .refl
  have key : ∀ t, ReflTransGen ((twinGraph G {i}).bayesBall ↑(G.twinCond i C)).Adj
      (twinVertex i x, false) t → TwinToSWIG G i C x t := by
    intro t ht
    induction ht with
    | refl => exact start
    | tail _ hst ih => exact ih.step hG hst
  have hy := key _ h
  by_cases hyi : y = i
  · subst hyi
    rw [twinVertex_self] at hy
    rcases hy with ⟨-, hne, -⟩ | ⟨-, b', hR, -⟩
    · exact absurd rfl hne
    · exact ⟨b', hR⟩
  · rw [twinVertex_of_ne hyi] at hy
    rcases hy with ⟨hne, -⟩ | ⟨-, b', hR, -⟩
    · exact absurd hne hyi
    · exact ⟨b', hR⟩

/-! ### From the SWIG to the twin graph -/

/-- Reachability in the Bayes-ball state graph of the twin graph, given the corrected set, from
the twin vertex of `x` entered without an arrowhead. -/
abbrev TwinReach (G : Digraph V) [DecidableRel G.Adj] (i : V) (C : Finset V) (x : V)
    (s : (V ⊕ V ⊕ V) × Bool) : Prop :=
  ReflTransGen ((twinGraph G {i}).bayesBall ↑(G.twinCond i C)).Adj (twinVertex i x, false) s

/-- **The invariant of the simulation of the SWIG in the twin graph**, for trails from `x`. A
SWIG state at `i` is matched at the factual copy of `i`, a state at a proper descendant of `i`
at its counterfactual copy, and a state at a nondescendant `v` at one of its copies; when
`v ∉ C`, the other copy is reached too, through an arrowhead. -/
def SWIGToTwin (G : Digraph V) [DecidableRel G.Adj] (i : V) (C : Finset V) (x : V) :
    V × Bool → Prop
  | (v, b) => (v = i ∧ TwinReach G i C x (.inr (.inl i), b)) ∨
      (ReflTransGen G.Adj i v ∧ v ≠ i ∧ TwinReach G i C x (.inr (.inr v), b)) ∨
      (¬ ReflTransGen G.Adj i v ∧
        ((TwinReach G i C x (.inr (.inl v), b) ∧
            (v ∉ C → TwinReach G i C x (.inr (.inr v), true))) ∨
          (TwinReach G i C x (.inr (.inr v), b) ∧
            (v ∉ C → TwinReach G i C x (.inr (.inl v), true)))))

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A nondescendant of `i` is not `i`. -/
theorem ne_of_not_reflTransGen {v : V} (hv : ¬ ReflTransGen G.Adj i v) : v ≠ i :=
  fun h => hv (h ▸ .refl)

/-- From the factual copy of an unconditioned nondescendant, entered without an arrowhead, the
trail reaches its counterfactual copy through the noise vertex. -/
theorem twinReach_cf_of_fact {w : V} (hw : ¬ ReflTransGen G.Adj i w) (hwC : w ∉ C)
    (h : TwinReach G i C x (.inr (.inl w), false)) :
    TwinReach G i C x (.inr (.inr w), true) := by
  refine (ReflTransGen.tail h
    (bayesBall_adj_false_iff.2 ⟨twinGraph_adj_noise_fact.2 rfl, ?_⟩)).tail
    (bayesBall_adj_true.2 ⟨twinGraph_adj_noise_cf.2 ⟨rfl, ?_⟩, inl_notMem_twinCond⟩)
  · simp [Passes, inr_inl_mem_twinCond, hwC]
  · simpa using ne_of_not_reflTransGen hw

/-- From the counterfactual copy of an unconditioned vertex other than `i`, entered without an
arrowhead, the trail reaches its factual copy through the noise vertex. -/
theorem twinReach_fact_of_cf {w : V} (hwi : w ≠ i) (hwC : w ∉ C)
    (h : TwinReach G i C x (.inr (.inr w), false)) :
    TwinReach G i C x (.inr (.inl w), true) := by
  refine (ReflTransGen.tail h (bayesBall_adj_false_iff.2
    ⟨twinGraph_adj_noise_cf.2 ⟨rfl, by simpa using hwi⟩, ?_⟩)).tail
    (bayesBall_adj_true.2 ⟨twinGraph_adj_noise_fact.2 rfl, inl_notMem_twinCond⟩)
  simp [Passes, inr_inr_mem_twinCond, hwC, hwi]

theorem swigToTwin_of_fact {w : V} (hw : ¬ ReflTransGen G.Adj i w)
    (h : TwinReach G i C x (.inr (.inl w), false)) : SWIGToTwin G i C x (w, false) :=
  Or.inr (Or.inr ⟨hw, Or.inl ⟨h, fun hwC => twinReach_cf_of_fact hw hwC h⟩⟩)

theorem swigToTwin_of_cf {w : V} (hw : ¬ ReflTransGen G.Adj i w)
    (h : TwinReach G i C x (.inr (.inr w), false)) : SWIGToTwin G i C x (w, false) :=
  Or.inr (Or.inr ⟨hw, Or.inr ⟨h, fun hwC =>
    twinReach_fact_of_cf (ne_of_not_reflTransGen hw) hwC h⟩⟩)

/-- Moving down from an unconditioned factual copy. -/
theorem twinReach_fact_down {v w : V} {e : Bool} (hvC : v ∉ C) (hvw : G.Adj v w)
    (h : TwinReach G i C x (.inr (.inl v), e)) : TwinReach G i C x (.inr (.inl w), true) :=
  h.tail (bayesBall_adj_true.2 ⟨twinGraph_adj_fact_fact.2 hvw, by
    simp [inr_inl_mem_twinCond, hvC]⟩)

/-- Moving down from an unconditioned counterfactual copy. -/
theorem twinReach_cf_down {v w : V} {e : Bool} (hvi : v ≠ i) (hvC : v ∉ C) (hvw : G.Adj v w)
    (hwi : w ≠ i) (h : TwinReach G i C x (.inr (.inr v), e)) :
    TwinReach G i C x (.inr (.inr w), true) :=
  h.tail (bayesBall_adj_true.2 ⟨twinGraph_adj_cf_cf.2 ⟨hvw, by simpa using hwi⟩, by
    simp [inr_inr_mem_twinCond, hvC, hvi]⟩)

/-- A nondescendant is matched in at least one layer. -/
theorem SWIGToTwin.one_layer {v : V} {b : Bool} (hv : ¬ ReflTransGen G.Adj i v)
    (hs : SWIGToTwin G i C x (v, b)) :
    TwinReach G i C x (.inr (.inl v), b) ∨ TwinReach G i C x (.inr (.inr v), b) := by
  rcases hs with ⟨hvi, -⟩ | ⟨hd, -⟩ | ⟨-, ⟨h, -⟩ | ⟨h, -⟩⟩
  · exact absurd (hvi ▸ .refl) hv
  · exact absurd hd hv
  · exact Or.inl h
  · exact Or.inr h

/-- An unconditioned nondescendant entered through an arrowhead is matched in both layers. -/
theorem SWIGToTwin.both_true {v : V} (hv : ¬ ReflTransGen G.Adj i v) (hvC : v ∉ C)
    (hs : SWIGToTwin G i C x (v, true)) :
    TwinReach G i C x (.inr (.inl v), true) ∧ TwinReach G i C x (.inr (.inr v), true) := by
  rcases hs with ⟨hvi, -⟩ | ⟨hd, -⟩ | ⟨-, ⟨h, h'⟩ | ⟨h, h'⟩⟩
  · exact absurd (hvi ▸ .refl) hv
  · exact absurd hd hv
  · exact ⟨h, h' hvC⟩
  · exact ⟨h' hvC, h⟩

/-- An unconditioned nondescendant is matched in both layers, with some flags. -/
theorem SWIGToTwin.both {v : V} {b : Bool} (hv : ¬ ReflTransGen G.Adj i v) (hvC : v ∉ C)
    (hs : SWIGToTwin G i C x (v, b)) :
    (∃ e, TwinReach G i C x (.inr (.inl v), e)) ∧
      ∃ e, TwinReach G i C x (.inr (.inr v), e) := by
  rcases hs with ⟨hvi, -⟩ | ⟨hd, -⟩ | ⟨-, ⟨h, h'⟩ | ⟨h, h'⟩⟩
  · exact absurd (hvi ▸ .refl) hv
  · exact absurd hd hv
  · exact ⟨⟨b, h⟩, true, h' hvC⟩
  · exact ⟨⟨true, h' hvC⟩, b, h⟩

/-- The twin trail may leave the factual copy of `i` upward whenever the SWIG trail may leave
`i` upward. -/
theorem passes_twin_fact_self {b : Bool} (hP : (G.deleteOutgoing {i}).Passes ↑C i b false) :
    (twinGraph G {i}).Passes ↑(G.twinCond i C) (.inr (.inl i)) b false := by
  cases b
  · simp only [Passes, Bool.false_eq_true, false_and, ↓reduceIte, mem_coe] at hP ⊢
    simpa [inr_inl_mem_twinCond] using hP
  · simp only [Passes, and_self, ↓reduceIte] at hP ⊢
    exact subset_ancestorsOf _ (mem_coe.2 (inr_inl_mem_twinCond.2
      ⟨mem_coe.1 (mem_of_self_mem_ancestorsOf_deleteOutgoing hP), Or.inl rfl⟩))

/-- The twin trail may leave the counterfactual copy of a proper descendant of `i` upward
whenever the SWIG trail may leave the vertex upward. -/
theorem passes_twin_cf_of_dead (hG : G.IsAcyclic) {v : V} {b : Bool}
    (hd : ReflTransGen G.Adj i v) (hvi : v ≠ i)
    (hP : (G.deleteOutgoing {i}).Passes ↑C v b false) :
    (twinGraph G {i}).Passes ↑(G.twinCond i C) (.inr (.inr v)) b false := by
  cases b
  · simp only [Passes, Bool.false_eq_true, false_and, ↓reduceIte, mem_coe] at hP ⊢
    simpa [inr_inr_mem_twinCond, hvi] using hP
  · simp only [Passes, and_self, ↓reduceIte] at hP ⊢
    exact (cf_or_fact_mem_ancestorsOf_twinCond hvi hP).resolve_right
      (fact_notMem_ancestorsOf_twinCond hG hd hvi)

/-- **One step of the simulation of the SWIG in the twin graph.** -/
theorem SWIGToTwin.step (hG : G.IsAcyclic) {s t : V × Bool} (hs : SWIGToTwin G i C x s)
    (hst : ((G.deleteOutgoing {i}).bayesBall ↑C).Adj s t) : SWIGToTwin G i C x t := by
  obtain ⟨v, b⟩ := s
  obtain ⟨w, c⟩ := t
  cases c
  · -- up to a parent `w`
    obtain ⟨hadj, hP⟩ := bayesBall_adj_false_iff.1 hst
    obtain ⟨hwv, hwi⟩ := deleteOutgoing_adj.1 hadj
    have hwi : w ≠ i := by simpa using hwi
    rcases hs with ⟨hvi, hR⟩ | ⟨hd, hvi, hR⟩ | ⟨hv, hR⟩
    · rw [hvi] at hwv hP
      exact swigToTwin_of_fact (hG.not_reflTransGen_of_adj_self hwv) (hR.tail
        (bayesBall_adj_false_iff.2 ⟨twinGraph_adj_fact_fact.2 hwv, passes_twin_fact_self hP⟩))
    · have h' : TwinReach G i C x (.inr (.inr w), false) :=
        hR.tail (bayesBall_adj_false_iff.2 ⟨twinGraph_adj_cf_cf.2 ⟨hwv, by simpa using hvi⟩,
          passes_twin_cf_of_dead hG hd hvi hP⟩)
      by_cases hdw : ReflTransGen G.Adj i w
      · exact Or.inr (Or.inl ⟨hdw, hwi, h'⟩)
      · exact swigToTwin_of_cf hdw h'
    · have hw := not_reflTransGen_of_adj hv hwv
      have hvi := ne_of_not_reflTransGen hv
      have hfact : ∀ {e}, TwinReach G i C x (.inr (.inl v), e) →
          (twinGraph G {i}).Passes ↑(G.twinCond i C) (.inr (.inl v)) e false →
          SWIGToTwin G i C x (w, false) := fun h hp => swigToTwin_of_fact hw
        (h.tail (bayesBall_adj_false_iff.2 ⟨twinGraph_adj_fact_fact.2 hwv, hp⟩))
      have hcf : ∀ {e}, TwinReach G i C x (.inr (.inr v), e) →
          (twinGraph G {i}).Passes ↑(G.twinCond i C) (.inr (.inr v)) e false →
          SWIGToTwin G i C x (w, false) := fun h hp => swigToTwin_of_cf hw
        (h.tail (bayesBall_adj_false_iff.2
          ⟨twinGraph_adj_cf_cf.2 ⟨hwv, by simpa using hvi⟩, hp⟩))
      have hs : SWIGToTwin G i C x (v, b) := Or.inr (Or.inr ⟨hv, hR⟩)
      cases b
      · have hvC : v ∉ C := by simpa [Passes] using hP
        rcases hs.one_layer hv with h | h
        · exact hfact h (by simp [Passes, inr_inl_mem_twinCond, hvC])
        · exact hcf h (by simp [Passes, inr_inr_mem_twinCond, hvC, hvi])
      · have hanc : v ∈ (G.deleteOutgoing {i}).ancestorsOf ↑C := by simpa [Passes] using hP
        by_cases hvC : v ∈ C
        · rcases hs.one_layer hv with h | h
          · exact hfact h (by
              simpa [Passes] using subset_ancestorsOf _ (mem_coe.2 (inr_inl_mem_twinCond.2
                ⟨hvC, Or.inr hv⟩)))
          · exact hcf h (by
              simpa [Passes] using subset_ancestorsOf _ (mem_coe.2 (inr_inr_mem_twinCond.2
                (Or.inr hvC))))
        · obtain ⟨hf, hc⟩ := hs.both_true hv hvC
          rcases cf_or_fact_mem_ancestorsOf_twinCond hvi hanc with h | h
          · exact hcf hc (by simpa [Passes] using h)
          · exact hfact hf (by simpa [Passes] using h)
  · -- down to a child `w`
    obtain ⟨hadj, hvC⟩ := bayesBall_adj_true.1 hst
    obtain ⟨hvw, hvi⟩ := deleteOutgoing_adj.1 hadj
    have hvi : v ≠ i := by simpa using hvi
    have hvC : v ∉ C := by simpa using hvC
    rcases hs with ⟨hvi', -⟩ | ⟨hd, -, hR⟩ | ⟨hv, hR⟩
    · exact absurd hvi' hvi
    · have hwi := hG.ne_of_reflTransGen_of_adj hd hvw
      exact Or.inr (Or.inl ⟨hd.tail hvw, hwi, twinReach_cf_down hvi hvC hvw hwi hR⟩)
    · obtain ⟨⟨e, hf⟩, e', hc⟩ :=
        SWIGToTwin.both (b := b) hv hvC (Or.inr (Or.inr ⟨hv, hR⟩))
      have hf' := twinReach_fact_down hvC hvw hf
      by_cases hwi : w = i
      · rw [hwi] at hf'
        exact Or.inl ⟨hwi, hf'⟩
      · have hc' := twinReach_cf_down hvi hvC hvw hwi hc
        by_cases hdw : ReflTransGen G.Adj i w
        · exact Or.inr (Or.inl ⟨hdw, hwi, hc'⟩)
        · exact Or.inr (Or.inr ⟨hdw, Or.inl ⟨hf', fun _ => hc'⟩⟩)

/-- **From an active SWIG trail to an active twin trail.** A path of the Bayes-ball state graph
of the SWIG, given `C`, from `x` to a vertex `y` outside `C` gives a path of the state graph of
the twin graph, given the corrected set, from the twin vertex of `x` to the twin vertex of
`y`. -/
theorem exists_reflTransGen_twin_of_swig (hG : G.IsAcyclic) {y : V} {b : Bool} (hyC : y ∉ C)
    (h : ReflTransGen ((G.deleteOutgoing {i}).bayesBall ↑C).Adj (x, false) (y, b)) :
    ∃ b', ReflTransGen ((twinGraph G {i}).bayesBall ↑(G.twinCond i C)).Adj
      (twinVertex i x, false) (twinVertex i y, b') := by
  have h0 : TwinReach G i C x (twinVertex i x, false) := ReflTransGen.refl
  have start : SWIGToTwin G i C x (x, false) := by
    by_cases hxi : x = i
    · rw [hxi, twinVertex_self] at h0
      exact Or.inl ⟨hxi, hxi ▸ h0⟩
    · rw [twinVertex_of_ne hxi] at h0
      by_cases hd : ReflTransGen G.Adj i x
      · exact Or.inr (Or.inl ⟨hd, hxi, h0⟩)
      · exact swigToTwin_of_cf hd h0
  have key : ∀ t, ReflTransGen ((G.deleteOutgoing {i}).bayesBall ↑C).Adj (x, false) t →
      SWIGToTwin G i C x t := by
    intro t ht
    induction ht with
    | refl => exact start
    | tail _ hst ih => exact ih.step hG hst
  rcases key _ h with ⟨hyi, hR⟩ | ⟨-, hyi, hR⟩ | ⟨hy, ⟨-, hR⟩ | ⟨hR, -⟩⟩
  · exact ⟨b, by rw [hyi, twinVertex_self]; exact hR⟩
  · exact ⟨b, by rw [twinVertex_of_ne hyi]; exact hR⟩
  · exact ⟨true, by rw [twinVertex_of_ne (ne_of_not_reflTransGen hy)]; exact hR hyC⟩
  · exact ⟨b, by rw [twinVertex_of_ne (ne_of_not_reflTransGen hy)]; exact hR⟩

/-! ### The equivalence -/

/-- **SWIG separation is twin graph separation given the corrected set.** For an acyclic graph
`G`, a treatment `i` and arbitrary finite sets `S`, `T`, `C`, the SWIG of `do(i)` separates
`S` from `T` given `C` (with the fixed half of `i` conditioned on) exactly when the twin graph
separates the twin vertices of `S` and `T` given the twin vertices of `C`, the counterfactual
copy `i*` and the factual copies of the vertices of `C` that are not descendants of `i`. -/
theorem swigSep_iff_twinSep (hG : G.IsAcyclic) {S T : Finset V} :
    G.SWIGSep {i} S T C ↔ G.TwinSep i S T C := by
  rw [swigSep_iff, TwinSep, coe_singleton, coe_image, coe_image]
  refine not_congr ⟨?_, ?_⟩
  · rintro ⟨x, hx, y, hy, hxC, hyC, b, h⟩
    have hxC : x ∉ C := by simpa using hxC
    have hyC : y ∉ C := by simpa using hyC
    obtain ⟨b', h'⟩ := exists_reflTransGen_twin_of_swig hG hyC h
    exact ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, by simpa [twinVertex_mem_twinCond] using hxC,
      by simpa [twinVertex_mem_twinCond] using hyC, b', h'⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, hxC, hyC, b, h⟩
    obtain ⟨b', h'⟩ := exists_reflTransGen_swig_of_twin hG h
    exact ⟨x, hx, y, hy, by simpa [twinVertex_mem_twinCond] using hxC,
      by simpa [twinVertex_mem_twinCond] using hyC, b', h'⟩

/-- **The back-door criterion read off the twin graph.** For an acyclic graph and a set `L` of
vertices that are not descendants of the treatment `i`, the twin graph separates the factual
`i` from the counterfactual outcomes `Y*` given `i*` and both copies of every vertex of `L`
exactly when `L` satisfies the back-door criterion relative to `({i}, Y)`. -/
theorem twinSep_iff_backDoor (hG : G.IsAcyclic) {Y L : Finset V}
    (hL : ∀ l ∈ L, l ∉ G.descendantsOf {i}) :
    G.TwinSep i {i} Y L ↔ G.BackDoor {i} ↑Y ↑L :=
  (swigSep_iff_twinSep hG).symm.trans (swigSep_singleton_iff_backDoor hL)

end Digraph

namespace CausalInference

namespace SWIGTwinSeparation

open Criteria Digraph SCM

theorem fork_isAcyclic : SWIGTwinGeneral.fork.IsAcyclic := by decide +kernel

theorem collider_isAcyclic : SWIGTwinGeneral.collider.IsAcyclic := by decide +kernel

theorem forkChain_isAcyclic : SWIGTwinExamples.forkChain.IsAcyclic := by decide +kernel

theorem confounded_isAcyclic : SWIGTwinExamples.confounded.IsAcyclic := by decide +kernel

/-- On the fork `a ← i → b`, the corrected set separates `a*` from `b*`, read off the SWIG
(`SWIGTwinGeneral.fixedHalf_corrected`). -/
theorem fork_twinSep : SWIGTwinGeneral.fork.TwinSep 0 {1} {2} ∅ :=
  (swigSep_iff_twinSep fork_isAcyclic).1 SWIGTwinGeneral.fixedHalf_needed.1

/-- On the collider `i → c ← y`, the corrected set separates the factual `i` from `y*`, read
off the SWIG (`SWIGTwinGeneral.factualDescendant_corrected`). -/
theorem collider_twinSep : SWIGTwinGeneral.collider.TwinSep 0 {0} {2} {1} :=
  (swigSep_iff_twinSep collider_isAcyclic).1 SWIGTwinGeneral.factualDescendant_opens.1

/-- On `X ← W → Z → Y` the two separations agree for all sets, which contains
`SWIGTwinGeneral.forkChain_corrected`. -/
theorem forkChain_swigSep_iff_twinSep (S T C : Finset (Fin 4)) :
    SWIGTwinExamples.forkChain.SWIGSep {0} S T C ↔
      SWIGTwinExamples.forkChain.TwinSep 0 S T C :=
  swigSep_iff_twinSep forkChain_isAcyclic

/-- On `W → L → X → Y` with `W → Y` the two separations agree for all sets, which contains
`SWIGTwinGeneral.confounded_corrected`. -/
theorem confounded_swigSep_iff_twinSep (S T C : Finset (Fin 4)) :
    SWIGTwinExamples.confounded.SWIGSep {0} S T C ↔
      SWIGTwinExamples.confounded.TwinSep 0 S T C :=
  swigSep_iff_twinSep confounded_isAcyclic

/-- On `X ← W → Z → Y`, the separation of `X` from `Y_x` by `Z` in the SWIG
(`SWIGTwinExamples.factualCopy_differs`) is the separation of the factual `X` from `Y*` by
`Z`, `Z*` and `X*` in the twin graph. -/
theorem forkChain_twinSep : SWIGTwinExamples.forkChain.TwinSep 0 {0} {3} {2} :=
  (forkChain_swigSep_iff_twinSep _ _ _).1 SWIGTwinExamples.factualCopy_differs.1

/-- On `W → L → X → Y` with `W → Y`, the back-door separation of `X` from `Y_x` by `L` in
the SWIG (`SWIGTwinExamples.counterfactualCopy_differs`) is the separation of the factual
`X` from `Y*` by `L`, `L*` and `X*` in the twin graph. -/
theorem confounded_twinSep : SWIGTwinExamples.confounded.TwinSep 0 {0} {1} {2} :=
  (confounded_swigSep_iff_twinSep _ _ _).1 SWIGTwinExamples.counterfactualCopy_differs.2.1

/-- The cycle `0 → 1 → 2 → 0`. -/
abbrev cycle : Digraph (Fin 3) := ofEdges [(0, 1), (1, 2), (2, 0)]

/-- **Acyclicity is needed.** On the cycle `0 → 1 → 2 → 0` with treatment `0`, the SWIG
separates `0` from `1` given `2`, but the twin graph does not separate the factual `0` from
`1*` given the corrected set. -/
theorem cycle_swigSep_not_twinSep :
    cycle.SWIGSep {0} {0} {1} {2} ∧ ¬ cycle.TwinSep 0 {0} {1} {2} :=
  ⟨by decide +kernel, by decide +kernel⟩

end SWIGTwinSeparation

end CausalInference
