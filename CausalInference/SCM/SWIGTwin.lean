/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.SCM.SWIG

/-!
# Single world intervention graphs and twin networks

For one treatment vertex `i`, the SWIG of `do(i := x)` and the twin graph of
`CausalInference.SCM.TwinNetwork` share their variables: the random half of `i` carries the
factual treatment, the copy of `i` in the factual layer of the twin graph; the fixed half
carries the constant `x i`, the counterfactual copy `i*`; and the random half of every `v ≠ i`
carries the potential response `V_x`, the counterfactual copy `v*`
(`SCM.swigConfig_inl_self_eq_twinConfig`, `SCM.swigConfig_inl_eq_twinConfig`,
`SCM.swigConfig_inr_eq_twinConfig`). The edges agree accordingly, except that the random half
of `i` reads its parents in the counterfactual layer of the SWIG and in the factual layer of
the twin graph (`Digraph.swigGraph_adj_inl_inl_iff_twinGraph`,
`Digraph.swigGraph_adj_inr_inl_iff_twinGraph`,
`Digraph.swigGraph_adj_inl_self_iff_twinGraph`). For the parents, which are not descendants of
`i`, both copies carry the same value, but they are different vertices of the twin graph, and
the twin graph also has the shared noise vertices.

## The d-separations differ

The twin graph keeps two vertices for every nondescendant of the treatment, a factual one and
a counterfactual one, with equal values. A statement of the SWIG conditioning on a
nondescendant translates into the twin graph in several ways, and none of the two single-copy
translations reproduces the SWIG:

* `SWIGTwinExamples.factualCopy_differs`: on `X ← W → Z → Y` with treatment `X`, the SWIG
  separates `X` from `Y_x` given `Z`, the twin graph separates the factual `X` from `Y*` given
  `Z*`, but not given the factual `Z` (the path `X ← W → Z ← U_Z → Z* → Y*` is open, the
  factual `Z` being a collider).
* `SWIGTwinExamples.counterfactualCopy_differs`: on `W → L → X → Y` with `W → Y`, the SWIG
  separates `X` from `Y_x` given `L` (a back-door set), the twin graph separates the factual
  `X` from `Y*` given the factual `L`, but not given `L*` (the path
  `X ← L ← W ← U_W → W* → Y*` is open).
* In both examples, conditioning on both copies of the covariate separates in the twin graph.

The general comparison of the two families of d-separations, with the conditioning set it
needs, is `Digraph.swigSep_iff_twinSep` in `CausalInference.SCM.SWIGTwinSeparation`.
-/

@[expose] public section

namespace Digraph

open Finset CausalInference.SCM

variable {V : Type*} {G : Digraph V} {i : V}

/-- Between random halves of vertices other than the treatment, the SWIG has the edges of the
counterfactual layer of the twin graph. -/
theorem swigGraph_adj_inl_inl_iff_twinGraph {u v : V} (hu : u ≠ i) (hv : v ≠ i) :
    (G.swigGraph {i}).Adj (.inl u) (.inl v) ↔
      (twinGraph G {i}).Adj (.inr (.inr u)) (.inr (.inr v)) := by
  rw [swigGraph_adj_inl_inl, twinGraph_adj_cf_cf]
  simp [hu, hv]

/-- The edges out of the fixed half of the treatment are the edges out of its counterfactual
copy in the twin graph. -/
theorem swigGraph_adj_inr_inl_iff_twinGraph {v : V} (hv : v ≠ i) :
    (G.swigGraph {i}).Adj (.inr ⟨i, mem_singleton_self i⟩) (.inl v) ↔
      (twinGraph G {i}).Adj (.inr (.inr i)) (.inr (.inr v)) := by
  rw [swigGraph_adj_inr_inl, twinGraph_adj_cf_cf]
  simp [hv]

/-- The edges into the random half of the treatment are the edges into its factual copy in
the twin graph, from the factual copies of the parents (in the SWIG they come from the random
halves of the parents, which correspond to their counterfactual copies). -/
theorem swigGraph_adj_inl_self_iff_twinGraph {u : V} (hu : u ≠ i) :
    (G.swigGraph {i}).Adj (.inl u) (.inl i) ↔
      (twinGraph G {i}).Adj (.inr (.inl u)) (.inr (.inl i)) := by
  rw [swigGraph_adj_inl_inl, twinGraph_adj_fact_fact]
  simp [hu]

end Digraph

namespace CausalInference

open Finset

namespace SCM

universe u

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
  {α ε : V → Type u} [∀ v, Fintype (ε v)] (M : SCM G α ε)

/-- The random half of the treatment carries the variable of its factual copy in the twin
network. -/
theorem swigConfig_inl_self_eq_twinConfig (i : V) (x : ∀ v, α v) (w : ∀ v, ε v) :
    M.swigConfig {i} x w (.inl i) = twinConfig M {i} x w (.inr (.inl i)) :=
  M.world_singleton_self i x w

/-- The random half of a vertex other than the treatment carries the variable of its
counterfactual copy in the twin network. -/
theorem swigConfig_inl_eq_twinConfig {i v : V} (hv : v ≠ i) (x : ∀ v, α v) (w : ∀ v, ε v) :
    M.swigConfig {i} x w (.inl v) = twinConfig M {i} x w (.inr (.inr v)) :=
  M.world_of_notMem x w (by simpa using hv)

/-- The fixed half of the treatment carries the variable of its counterfactual copy in the twin
network, the constant `x i`. -/
theorem swigConfig_inr_eq_twinConfig (i : V) (x : ∀ v, α v) (w : ∀ v, ε v) :
    M.swigConfig {i} x w (.inr ⟨i, mem_singleton_self i⟩) =
      twinConfig M {i} x w (.inr (.inr i)) :=
  (M.solve_intervene_of_mem w (mem_singleton_self i)).symm

end SCM

namespace SWIGTwinExamples

open Criteria SCM

/-- The graph `X ← W → Z → Y` with `X = 0`, `W = 1`, `Z = 2`, `Y = 3`. -/
abbrev forkChain : Digraph (Fin 4) := ofEdges [(1, 0), (1, 2), (2, 3)]

/-- **The factual copy of a covariate does not reproduce the SWIG.** On `X ← W → Z → Y` with
treatment `X`: the SWIG separates the random half of `X` from `Y_x` given `Z`; the twin graph
separates the factual `X` from `Y*` given `Z*` and given both copies of `Z`, but not given the
factual `Z`. -/
theorem factualCopy_differs :
    forkChain.SWIGSep {0} {0} {3} {2} ∧
      (twinGraph forkChain {0}).DSep {.inr (.inl 0)} {.inr (.inr 3)} {.inr (.inr 2)} ∧
      (twinGraph forkChain {0}).DSep {.inr (.inl 0)} {.inr (.inr 3)}
        {.inr (.inl 2), .inr (.inr 2)} ∧
      ¬ (twinGraph forkChain {0}).DSep {.inr (.inl 0)} {.inr (.inr 3)} {.inr (.inl 2)} := by
  refine ⟨by decide +kernel, ?_, ?_, ?_⟩ <;> decide +kernel

/-- The graph `W → L → X → Y` with `W → Y`, with `X = 0`, `Y = 1`, `L = 2`, `W = 3`. -/
abbrev confounded : Digraph (Fin 4) := ofEdges [(3, 2), (2, 0), (0, 1), (3, 1)]

/-- **The counterfactual copy of a covariate does not reproduce the SWIG.** On `W → L → X → Y`
with `W → Y` and treatment `X`: the back-door set `L` separates the random half of `X` from
`Y_x` in the SWIG; the twin graph separates the factual `X` from `Y*` given the factual `L` and
given both copies of `L`, but not given `L*`. -/
theorem counterfactualCopy_differs :
    confounded.BackDoor {0} {1} {2} ∧ confounded.SWIGSep {0} {0} {1} {2} ∧
      (twinGraph confounded {0}).DSep {.inr (.inl 0)} {.inr (.inr 1)} {.inr (.inl 2)} ∧
      (twinGraph confounded {0}).DSep {.inr (.inl 0)} {.inr (.inr 1)}
        {.inr (.inl 2), .inr (.inr 2)} ∧
      ¬ (twinGraph confounded {0}).DSep {.inr (.inl 0)} {.inr (.inr 1)} {.inr (.inr 2)} := by
  refine ⟨by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩ <;> decide +kernel

end SWIGTwinExamples

end CausalInference
