/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Graphical.Districts
public import CausalInference.Graphical.LatentProjection
public import CausalInference.Graphical.DSeparationDecide

/-!
# Examples of acyclic directed mixed graphs

Concrete ADMGs on `Fin n`, with their acyclicity, ancestors and districts checked by `decide`:

* the bow graph `X → Y`, `X ↔ Y`;
* the front-door graph `X → M → Y` with a latent confounder `X ↔ Y`;
* the instrumental-variable graph `Z → X → Y`, `X ↔ Y`;
* the graph `verma` of Verma and Pearl (1990), Figure 2(a): the chain `A → B → C → D` with a
  latent common cause of `B` and `D`, that is, `B ↔ D`; and the graph `vermaAC` with the extra
  edge `A → C`, as in Richardson, Evans, Robins and Shpitser (2023), Figure 1(i);
* latent projections of explicit DAGs with one and two latent vertices, which reproduce the
  front-door, the instrumental-variable, `verma`, and `vermaAC` graphs, and a two-stage
  projection checked as a graph equality;
* the d-separation of `A` and `C` given `B` in the DAG behind `verma`, which fails with the
  edge `A → C`;
* finite sibling sets, ancestral sets, and the districts inside a vertex set;
* a strict inclusion between the district of a vertex in an induced sub-ADMG and its district
  in the whole graph.

## References

* T. Verma and J. Pearl (1990), *Equivalence and synthesis of causal models*, Proceedings of
  the Sixth Conference on Uncertainty in Artificial Intelligence, Figure 2(a).
* T. S. Richardson, R. J. Evans, J. M. Robins, I. Shpitser (2023), *Nested Markov properties
  for acyclic directed mixed graphs*, Annals of Statistics, Figure 1(i).
-/

@[expose] public section

namespace CausalInference.ADMGExamples

open ADMG

/-- The mixed graph on `Fin n` with the listed directed edges `d` (a pair `(i, j)` is `i → j`)
and the listed bidirected edges `b` (a pair `(i, j)` with `i ≠ j` is `i ↔ j`). -/
def ofLists {n : ℕ} (d b : List (Fin n × Fin n)) : ADMG (Fin n) where
  directed := { Adj := fun i j => (i, j) ∈ d }
  bidirected := SimpleGraph.fromRel fun i j => (i, j) ∈ b

instance {n : ℕ} (d b : List (Fin n × Fin n)) : DecidableRel (ofLists d b).directed.Adj :=
  fun i j => inferInstanceAs (Decidable ((i, j) ∈ d))

instance {n : ℕ} (d b : List (Fin n × Fin n)) : DecidableRel (ofLists d b).bidirected.Adj :=
  fun i j => inferInstanceAs (Decidable (i ≠ j ∧ ((i, j) ∈ b ∨ (j, i) ∈ b)))

/-- The directed graph on `Fin n` with the listed edges. -/
def digraphOfList {n : ℕ} (d : List (Fin n × Fin n)) : Digraph (Fin n) where
  Adj i j := (i, j) ∈ d

instance {n : ℕ} (d : List (Fin n × Fin n)) : DecidableRel (digraphOfList d).Adj :=
  fun i j => inferInstanceAs (Decidable ((i, j) ∈ d))

/-! ### The bow graph: `X = 0`, `Y = 1` -/

/-- The bow graph `X → Y`, `X ↔ Y`, with `X = 0` and `Y = 1`. -/
abbrev bow : ADMG (Fin 2) := ofLists [(0, 1)] [(0, 1)]

example : bow.IsAcyclic := by decide
example : bow.IsAncestor 0 1 := by decide
example : bow.SameDistrict 0 1 := by decide
example : bow.districtFinset 0 = {0, 1} := by decide
example : bow.districts = {{0, 1}} := by decide

/-! ### The front-door graph: `X = 0`, `M = 1`, `Y = 2` -/

/-- The front-door graph `X → M → Y` with a latent confounder `X ↔ Y`. -/
abbrev frontDoor : ADMG (Fin 3) := ofLists [(0, 1), (1, 2)] [(0, 2)]

example : frontDoor.IsAcyclic := by decide
example : frontDoor.IsAncestor 0 2 := by decide
example : frontDoor.districtFinset 0 = {0, 2} := by decide
example : frontDoor.districtFinset 1 = {1} := by decide
example : frontDoor.districts = {{0, 2}, {1}} := by decide
example : frontDoor.siblingsFinset 0 = {2} := by decide
example : frontDoor.siblings 0 = {2} := by
  rw [← coe_siblingsFinset, show frontDoor.siblingsFinset 0 = {2} by decide, Finset.coe_singleton]
example : frontDoor.ancestorsOfFinset {2} = {0, 1, 2} := by decide
example : frontDoor.IsAncestral ({0, 1} : Finset (Fin 3)) := by decide
example : ¬ frontDoor.IsAncestral ({1, 2} : Finset (Fin 3)) := by decide

/-! ### The instrumental-variable graph: `Z = 0`, `X = 1`, `Y = 2` -/

/-- The instrumental-variable graph `Z → X → Y`, `X ↔ Y`. -/
abbrev instrument : ADMG (Fin 3) := ofLists [(0, 1), (1, 2)] [(1, 2)]

example : instrument.IsAcyclic := by decide
example : instrument.districtFinset 0 = {0} := by decide
example : instrument.districtFinset 2 = {1, 2} := by decide
example : instrument.districts = {{0}, {1, 2}} := by decide
example : ¬ instrument.SameDistrict 0 1 := by decide

/-! ### The `verma` graph: `A = 0`, `B = 1`, `C = 2`, `D = 3` -/

/-- The graph of Verma and Pearl (1990), Figure 2(a): the directed edges `A → B`, `B → C`,
`C → D` and the bidirected edge `B ↔ D`, which stands for a latent common cause of `B` and `D`.
It is the graph on which the Verma constraint is stated. -/
abbrev verma : ADMG (Fin 4) := ofLists [(0, 1), (1, 2), (2, 3)] [(1, 3)]

example : verma.IsAcyclic := by decide
example : verma.IsAncestor 0 3 := by decide
example : verma.districtFinset 1 = {1, 3} := by decide
example : verma.districts = {{0}, {1, 3}, {2}} := by decide

/-- The `verma` graph with the extra edge `A → C`: the graph of Richardson, Evans, Robins and
Shpitser (2023), Figure 1(i). The Verma constraint holds in it as well, and it implies no
conditional independence among the observed vertices. Its districts are those of `verma`. -/
abbrev vermaAC : ADMG (Fin 4) := ofLists [(0, 1), (1, 2), (2, 3), (0, 2)] [(1, 3)]

example : vermaAC.IsAcyclic := by decide
example : vermaAC.districts = {{0}, {1, 3}, {2}} := by decide

/-! ### Districts of an induced sub-ADMG can be strictly smaller -/

/-- The bidirected path `0 ↔ 1 ↔ 2` with no directed edges. -/
abbrev biPath : ADMG (Fin 3) := ofLists [] [(0, 1), (1, 2)]

example : biPath.districtFinset 0 = {0, 1, 2} := by decide
example : (biPath.restrict {0, 2}).districtFinset 0 = {0} := by decide

/-- `(biPath.restrict {0, 2}).districts` also lists the removed vertex `1`; `districtsOn`
lists only the districts inside `{0, 2}`. -/
example : (biPath.restrict {0, 2}).districts = {{0}, {1}, {2}} := by decide
example : biPath.districtsOn {0, 2} = {{0}, {2}} := by decide
example : biPath.districtsOn {0, 1} = {{0, 1}} := by decide

/-- The district of `0` in the sub-ADMG of `0 ↔ 1 ↔ 2` induced on `{0, 2}` is `{0}`, a strict
subset of its district `{0, 1, 2}` in the whole graph: removing `1` disconnects `0` from `2`. -/
theorem district_restrict_ssubset : (biPath.restrict {0, 2}).district 0 ⊂ biPath.district 0 := by
  rw [← coe_districtFinset, ← coe_districtFinset, Finset.coe_ssubset]
  decide

/-! ### Mutilation -/

example : (frontDoor.deleteIncoming {0}).districts = {{0}, {1}, {2}} := by decide
example : (instrument.deleteOutgoing {1}).districtFinset 1 = {1, 2} := by decide
example : ¬ (instrument.deleteOutgoing {1}).IsAncestor 1 2 := by decide

/-! ### Latent projection with one latent vertex

The DAG `X → M → Y` with a latent `U → X`, `U → Y`, where `X = 0`, `M = 1`, `Y = 2`, `U = 3`.
Projecting out `U` gives the front-door graph, with `U` isolated. -/

/-- The front-door DAG with its latent confounder `U = 3` made explicit. -/
abbrev frontDoorDAG : Digraph (Fin 4) := digraphOfList [(0, 1), (1, 2), (3, 0), (3, 2)]

example : frontDoorDAG.IsAcyclic := by decide

/-- Projecting `U` out of the front-door DAG gives `X → M → Y`, `X ↔ Y`, and `U` isolated. -/
theorem latentProjection_frontDoorDAG :
    latentProjection frontDoorDAG {3} = ofLists [(0, 1), (1, 2)] [(0, 2)] := by
  ext u v <;> revert u v <;> decide

example : (latentProjection frontDoorDAG {3}).districts = {{0, 2}, {1}, {3}} := by decide

/-! ### Latent projection with two latent vertices

The DAG `Z → X`, `X → W → Y` and `U → X`, `U → Y`, with `Z = 0`, `X = 1`, `Y = 2`, `U = 3`,
`W = 4`. The latent mediator `W` becomes the directed edge `X → Y` and the latent confounder `U`
becomes `X ↔ Y`: the projection is the instrumental-variable graph. Projecting `U` and `W` in
two stages gives the same graph. -/

/-- A DAG with a latent confounder `U = 3` and a latent mediator `W = 4`. -/
abbrev ivDAG : Digraph (Fin 5) := digraphOfList [(0, 1), (1, 4), (4, 2), (3, 1), (3, 2)]

example : ivDAG.IsAcyclic := by decide

/-- Projecting `{U, W}` out of `ivDAG` gives `Z → X → Y`, `X ↔ Y`, with `U` and `W` isolated. -/
theorem latentProjection_ivDAG :
    latentProjection ivDAG {3, 4} = ofLists [(0, 1), (1, 2)] [(1, 2)] := by
  ext u v <;> revert u v <;> decide

example : (latentProjection ivDAG {3, 4}).districts = {{0}, {1, 2}, {3}, {4}} := by decide

/-- Projecting `W` and then `U` agrees with projecting both at once, checked as an equality of
graphs (both adjacency relations) by `decide`; `latentProjection_project` proves this in
general. -/
example : (latentProjection ivDAG {4}).project {3} = latentProjection ivDAG {3, 4} := by
  ext u v <;> revert u v <;> decide

example : ((latentProjection ivDAG {4}).project {3}).districts = {{0}, {1, 2}, {3}, {4}} := by
  decide

/-- The observed vertices of the projection, as the vertex set for `districtsOn`: the latent
`U` and `W` no longer appear. -/
example : (latentProjection ivDAG {3, 4}).districtsOn {0, 1, 2} = {{0}, {1, 2}} := by decide

/-- Cutting the edges into `X` commutes with the projection: `(latentProjection ivDAG {3, 4})`
with the edges into `X` removed is the projection of `ivDAG` with those edges removed. -/
example : (latentProjection ivDAG {3, 4}).deleteIncoming {1} =
    latentProjection (ivDAG.deleteIncoming {1}) {3, 4} :=
  latentProjection_deleteIncoming _ (Set.disjoint_singleton_left.2 (by decide))

/-- Ancestors among observed vertices are preserved: `Z` is an ancestor of `Y` in the
projection, as in the DAG. -/
example : (latentProjection ivDAG {3, 4}).IsAncestor 0 2 := by decide

/-! ### The `verma` graph as a latent projection

The DAG `A → B → C → D` with a latent `U → B`, `U → D`, where `A = 0`, `B = 1`, `C = 2`,
`D = 3`, `U = 4`. Projecting out `U` gives the edges of `verma`, with `U` isolated. -/

/-- The `verma` graph with its latent confounder `U = 4` made explicit. -/
abbrev vermaDAG : Digraph (Fin 5) :=
  digraphOfList [(0, 1), (1, 2), (2, 3), (4, 1), (4, 3)]

example : vermaDAG.IsAcyclic := by decide

/-- Projecting `U` out of `vermaDAG` gives `A → B → C → D`, `B ↔ D`, and `U` isolated: the
edges of `verma` on `Fin 5`. -/
theorem latentProjection_vermaDAG :
    latentProjection vermaDAG {4} = ofLists [(0, 1), (1, 2), (2, 3)] [(1, 3)] := by
  ext u v <;> revert u v <;> decide

/-- The independence `A ⫫ C | B` implied by the graph of Verma and Pearl (1990): in `vermaDAG`,
`B` d-separates `A` and `C`. Conditioning on `B` opens `A → B ← U`, but the path continues
through the collider `D`, which is not conditioned on. -/
theorem vermaDAG_dSep : vermaDAG.DSep {0} {2} {1} := by decide

/-- The `vermaAC` graph with its latent confounder `U = 4` made explicit. -/
abbrev vermaACDAG : Digraph (Fin 5) :=
  digraphOfList [(0, 1), (1, 2), (2, 3), (0, 2), (4, 1), (4, 3)]

example : vermaACDAG.IsAcyclic := by decide

/-- Projecting `U` out of `vermaACDAG` gives `A → B → C → D`, `A → C`, `B ↔ D`, and `U`
isolated: the edges of `vermaAC` on `Fin 5`. -/
theorem latentProjection_vermaACDAG :
    latentProjection vermaACDAG {4} = ofLists [(0, 1), (1, 2), (2, 3), (0, 2)] [(1, 3)] := by
  ext u v <;> revert u v <;> decide

/-- With the edge `A → C`, the independence `A ⫫ C | B` fails, which distinguishes `verma` from
`vermaAC` although they have the same districts. -/
theorem not_vermaACDAG_dSep : ¬ vermaACDAG.DSep {0} {2} {1} := by decide

end CausalInference.ADMGExamples
