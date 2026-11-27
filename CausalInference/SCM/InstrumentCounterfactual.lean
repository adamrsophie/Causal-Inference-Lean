/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.SCM.TwinNetwork
public import CausalInference.Graphical.Criteria.Instrument

/-!
# The counterfactual instrument condition from the graphical criterion

Pearl (2009), Definition 7.4.1, states two criteria for an instrument `Z` relative to the effect
of `X` on `Y` given measurements `S` unaffected by `X`: the counterfactual criterion,
(i) `Z ⫫ Y_x | S` and (ii) `Z` and `X` dependent given `S`, and the graphical criterion,
(i) `Z` and `Y` d-separated by `S` in the graph with the edges into `X` removed and (ii) `Z` and
`X` d-connected given `S`. This file derives condition (i) of the counterfactual criterion from
condition (i) of the graphical one, for an instrument that is not a descendant of `X`.

## Main results

* `SCM.condIndepFun_potentialResponse_of_dSep`: if no member of `Z` or `S` is a descendant of
  `X` and `Z`, `Y` are d-separated by `S` in the graph with the edges into `X` removed, then,
  under the noise law, the factual `Z` and the potential response `Y_x` are conditionally
  independent given the factual `S`, for every value `x`. This is the cross-world statement
  `Z ⫫ Y_x | S`.
* `SCM.condIndepFun_potentialResponse_of_isPretreatmentInstrument`: the same conclusion for a
  pretreatment instrument (`Digraph.IsPretreatmentInstrument`).

## Proof

The law of the solution of the model under `do(X := x)` factorizes according to the graph with
the edges into `X` removed, so its global Markov property gives `Z_x ⫫ Y_x | S_x`. Vertices that
are not descendants of `X` take the same value with and without the intervention at every noise
value, so `Z_x = Z` and `S_x = S` pointwise, which turns the statement about the interventional
law into the cross-world statement.

## Notes

Condition (ii) of the counterfactual criterion, the dependence of `Z` and `X` given `S`, does
not follow from d-connection: a law that factorizes according to the graph need not be faithful
to it, so dependence in a given model is a separate hypothesis. Without the requirement that `Z`
is not a descendant of `X` the conclusion can fail: see
`CausalInference.InstrumentExamples.descendantInstrument` and the linear model
`CausalInference.LinearSEM.DescendantInstrumentModel.counterexample`.

## References

* J. Pearl (2009), *Causality: Models, Reasoning, and Inference*, 2nd edition, section 7.4.5,
  Definition 7.4.1.
-/

@[expose] public section

namespace CausalInference

open Finset

namespace SCM

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
  {α : V → Type*} {ε : V → Type*} [∀ v, Fintype (ε v)] [∀ v, Finite (α v)]
  [∀ v, DecidableEq (α v)] (M : SCM G α ε)

/-- **The counterfactual independence of an instrument.** If no member of `Z` or of `S` is a
descendant of `X`, and `Z` and `Y` are d-separated by `S` in the graph with the edges into `X`
removed, then for every value `x`, under the noise law, the factual values of `Z` and the
potential responses `Y_x` are conditionally independent given the factual values of `S`:
`Z ⫫ Y_x | S`. -/
theorem condIndepFun_potentialResponse_of_dSep {X Z Y S : Finset V} (x : ∀ v, α v)
    (hZ : ∀ z ∈ Z, z ∉ G.descendantsOf ↑X) (hS : ∀ s ∈ S, s ∉ G.descendantsOf ↑X)
    (hsep : (G.deleteIncoming ↑X).DSep ↑Z ↑Y ↑S) :
    M.noiseDist.CondIndepFun (fun u => Z.restrict (M.solve u))
      (fun u => Y.restrict ((M.intervene X x).solve u)) (fun u => S.restrict (M.solve u)) := by
  have : ∀ v, Fintype (α v) := fun _ => Fintype.ofFinite _
  have h := (FiniteDist.condIndepFun_map_iff (M.intervene X x).noiseDist
    (M.intervene X x).solve (Z.restrict (π := α)) (Y.restrict (π := α))
    (S.restrict (π := α))).1
    (M.factorizes_intervene.condIndep_of_dSep (M.intervene X x).acyclic hsep)
  have eZ : (fun u => Z.restrict (M.solve u)) =
      fun u => Z.restrict ((M.intervene X x).solve u) :=
    funext fun u => funext fun z => (M.solve_intervene_of_notMem_descendantsOf u (hZ z z.2)).symm
  have eS : (fun u => S.restrict (M.solve u)) =
      fun u => S.restrict ((M.intervene X x).solve u) :=
    funext fun u => funext fun s => (M.solve_intervene_of_notMem_descendantsOf u (hS s s.2)).symm
  rw [eZ, eS]
  exact h

/-- **Condition (i) of the counterfactual instrument criterion** (Pearl 2009, Definition 7.4.1)
for a pretreatment instrument: if `Z` is a pretreatment instrument for `X` on `Y` given `S`
(`Digraph.IsPretreatmentInstrument`), then `Z ⫫ Y_x | S` under the noise law, for every value
`x`, with `Z` and `S` factual. -/
theorem condIndepFun_potentialResponse_of_isPretreatmentInstrument {X Z Y S : Finset V}
    (x : ∀ v, α v) (h : G.IsPretreatmentInstrument ↑Z ↑X ↑Y ↑S) :
    M.noiseDist.CondIndepFun (fun u => Z.restrict (M.solve u))
      (fun u => Y.restrict ((M.intervene X x).solve u)) (fun u => S.restrict (M.solve u)) :=
  M.condIndepFun_potentialResponse_of_dSep x (fun z hz => h.2 z hz) (fun s hs => h.1.2.1 s hs)
    h.1.2.2.1

end SCM

end CausalInference
