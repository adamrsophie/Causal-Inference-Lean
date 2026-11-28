/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.SCM.SWIGTwin

/-!
# SWIG separation against twin graph separation, in general

For one treatment `i`, `CausalInference.SCM.SWIGTwin` matches the vertices of the SWIG of
`do(i := x)` with those of the twin graph: the random half of `i` is the factual copy of `i`,
the random half of every other `v` is the counterfactual copy `v*` (`Digraph.twinVertex`).
This file compares the two separations for arbitrary sets `S`, `T`, `C`.

## The naive statement is false

"If the SWIG separates `S` from `T` given `C`, the twin graph separates their twin vertices
given both copies of every vertex of `C`" fails for two reasons.

* The fixed half of `i` is conditioned in the SWIG, while its counterfactual copy `i*` is a
  free vertex of the twin graph: on `a ← i → b`, the SWIG separates `a` from `b` given nothing,
  the twin graph does not separate `a*` from `b*` given nothing (`a* ← i* → b*`)
  (`SWIGTwinGeneral.fixedHalf_needed`).
* The factual copy of a descendant of `i` is a collider of the twin graph that the SWIG does
  not have: on `i → c ← y`, the SWIG separates `i` from `y` given `c`, but the twin graph does
  not separate the factual `i` from `y*` given `c`, `c*` and `i*`
  (`i → c ← y ← U_y → y*`, `SWIGTwinGeneral.factualDescendant_opens`).

## The corrected statement

The corrected conditioning set `Digraph.twinCond G i C` is the set of twin vertices of `C`,
the counterfactual copy `i*` of the fixed half, and the factual copies of the vertices of `C`
that are not descendants of `i` (both copies of a nondescendant, one copy of a descendant).
`Digraph.TwinSep G i S T C` is twin separation given that set. The conjecture
`Digraph.SWIGSep {i} S T C ↔ Digraph.TwinSep G i S T C` holds in every instance checked here
by the kernel: on the two graphs above it repairs both failures
(`SWIGTwinGeneral.fixedHalf_corrected`, `SWIGTwinGeneral.factualDescendant_corrected`), and it
gives the right answer on the graphs of `SWIGTwinExamples` (`SWIGTwinGeneral.forkChain_corrected`,
`SWIGTwinGeneral.confounded_corrected`). No general proof in either direction is given here;
both directions need surgery on active trails across the two layers of the twin graph.

## One copy of a nondescendant

For a nondescendant `v` of `i` (`¬ ReflTransGen G.Adj i v`), the factual and the counterfactual
copies carry the same value in every twin model (`SCM.twinConfig_fact_eq_cf`), which is why the
SWIG has one vertex for `v`. The twin graph keeps two vertices, and d-separation does not see
that their values agree: conditioning on one copy only can differ from the SWIG in both ways
(`SWIGTwinExamples.factualCopy_differs`, `SWIGTwinExamples.counterfactualCopy_differs`), so the
corrected set conditions on both.
-/

@[expose] public section

namespace Digraph

open Finset Relation CausalInference.SCM

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The twin vertex of a vertex `v` of the SWIG of `do(i)`: the factual copy of `i` for the
random half of `i`, the counterfactual copy `v*` for every other `v`. -/
def twinVertex (i v : V) : V ⊕ V ⊕ V := if v = i then .inr (.inl v) else .inr (.inr v)

/-- **The corrected conditioning set** of the twin graph for the SWIG conditioning set `C`:
the twin vertices of `C`, the counterfactual copy `i*` of the fixed half of `i`, and the factual
copies of the vertices of `C` that are not descendants of `i`. -/
def twinCond (G : Digraph V) [DecidableRel G.Adj] (i : V) (C : Finset V) :
    Finset (V ⊕ V ⊕ V) :=
  insert (.inr (.inr i)) (C.image (twinVertex i) ∪
    (C.filter fun c => ¬ ReflTransGen G.Adj i c).image fun c => .inr (.inl c))

/-- Twin separation of the twin vertices of `S` and `T` given the corrected conditioning set
of `C`. -/
def TwinSep (G : Digraph V) [DecidableRel G.Adj] (i : V) (S T C : Finset V) : Prop :=
  (twinGraph G {i}).DSep ↑(S.image (twinVertex i)) ↑(T.image (twinVertex i)) ↑(G.twinCond i C)

instance (G : Digraph V) [DecidableRel G.Adj] (i : V) (S T C : Finset V) :
    Decidable (G.TwinSep i S T C) := by
  unfold TwinSep
  infer_instance

end Digraph

namespace CausalInference

open Finset Relation

namespace SCM

universe u

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
  {α ε : V → Type u} [∀ v, Fintype (ε v)] (M : SCM G α ε)

/-- **Both copies of a nondescendant carry the same value**: in the twin model of `do(i := x)`,
the factual and the counterfactual copies of a vertex that is not a descendant of `i` are
equal at every noise value. -/
theorem twinConfig_fact_eq_cf (i : V) (x : ∀ v, α v) (w : ∀ v, ε v) {v : V}
    (hv : ¬ ReflTransGen G.Adj i v) :
    twinConfig M {i} x w (.inr (.inl v)) = twinConfig M {i} x w (.inr (.inr v)) := by
  refine (M.solve_intervene_of_notMem_descendantsOf w ?_).symm
  simpa [Digraph.descendantsOf] using hv

end SCM

namespace SWIGTwinGeneral

open Criteria Digraph SCM

/-- The fork `a ← i → b` with `i = 0`, `a = 1`, `b = 2`. -/
abbrev fork : Digraph (Fin 3) := ofEdges [(0, 1), (0, 2)]

/-- **The fixed half must be conditioned.** On `a ← i → b`, the SWIG separates `a` from `b`
given nothing, the twin graph does not separate `a*` from `b*` given nothing. -/
theorem fixedHalf_needed :
    fork.SWIGSep {0} {1} {2} ∅ ∧
      ¬ (twinGraph fork {0}).DSep {.inr (.inr 1)} {.inr (.inr 2)} ∅ := by
  refine ⟨by decide +kernel, by decide +kernel⟩

/-- With the corrected set (here `{i*}`) the twin graph separates `a*` from `b*`. -/
theorem fixedHalf_corrected : fork.SWIGSep {0} {1} {2} ∅ ∧ fork.TwinSep 0 {1} {2} ∅ := by
  refine ⟨by decide +kernel, by decide +kernel⟩

/-- The collider `i → c ← y` with `i = 0`, `c = 1`, `y = 2`. -/
abbrev collider : Digraph (Fin 3) := ofEdges [(0, 1), (2, 1)]

/-- **The factual copy of a descendant opens a collider.** On `i → c ← y`, the SWIG separates
`i` from `y` given `c`, but the twin graph does not separate the factual `i` from `y*` given
both copies of `c` and `i*`. -/
theorem factualDescendant_opens :
    collider.SWIGSep {0} {0} {2} {1} ∧
      ¬ (twinGraph collider {0}).DSep {.inr (.inl 0)} {.inr (.inr 2)}
        {.inr (.inl 1), .inr (.inr 1), .inr (.inr 0)} := by
  refine ⟨by decide +kernel, by decide +kernel⟩

/-- With the corrected set (here `{c*, i*}`, `c` being a descendant of `i`) the twin graph
separates the factual `i` from `y*`. -/
theorem factualDescendant_corrected :
    collider.SWIGSep {0} {0} {2} {1} ∧ collider.TwinSep 0 {0} {2} {1} := by
  refine ⟨by decide +kernel, by decide +kernel⟩

/-- On `X ← W → Z → Y` (`SWIGTwinExamples.forkChain`) the corrected set agrees with the SWIG
for the separation of `X` from `Y` given `Z`, given nothing and given `W`. -/
theorem forkChain_corrected :
    (SWIGTwinExamples.forkChain.SWIGSep {0} {0} {3} {2} ↔
        SWIGTwinExamples.forkChain.TwinSep 0 {0} {3} {2}) ∧
      (SWIGTwinExamples.forkChain.SWIGSep {0} {0} {3} ∅ ↔
        SWIGTwinExamples.forkChain.TwinSep 0 {0} {3} ∅) ∧
      (SWIGTwinExamples.forkChain.SWIGSep {0} {0} {3} {1} ↔
        SWIGTwinExamples.forkChain.TwinSep 0 {0} {3} {1}) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- On `W → L → X → Y` with `W → Y` (`SWIGTwinExamples.confounded`) the corrected set agrees
with the SWIG for the separation of `X` from `Y` given `L`, given nothing and given `W`. -/
theorem confounded_corrected :
    (SWIGTwinExamples.confounded.SWIGSep {0} {0} {1} {2} ↔
        SWIGTwinExamples.confounded.TwinSep 0 {0} {1} {2}) ∧
      (SWIGTwinExamples.confounded.SWIGSep {0} {0} {1} ∅ ↔
        SWIGTwinExamples.confounded.TwinSep 0 {0} {1} ∅) ∧
      (SWIGTwinExamples.confounded.SWIGSep {0} {0} {1} {3} ↔
        SWIGTwinExamples.confounded.TwinSep 0 {0} {1} {3}) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

end SWIGTwinGeneral

end CausalInference
