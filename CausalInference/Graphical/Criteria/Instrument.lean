/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Graphical.Criteria.BackDoor

/-!
# Graphical instruments

## Main definitions

* `Digraph.IsInstrument G Z X Y S`: the graphical criterion of Pearl's Definition 7.4.1 for `Z`
  to be an instrument relative to the total effect of `X` on `Y`, given the measured covariates
  `S`: no member of `S` is a descendant of `X` ("measurements unaffected by `X`"), `Z` and `Y`
  are d-separated by `S` in the graph with the edges out of `X` removed, and `Z` and `X` are
  d-connected given `S` in `G`.

## Main results

* `Digraph.not_isInstrument_of_adj`: a direct edge from `z` to `y` (outside `X ∪ S`) rules out
  `z` as an instrument; this is the exclusion restriction.
* `Digraph.IsInstrument.notMem`: an instrument lies outside the covariate set.
* Decidability, and examples: graphs with the properties stated for Figure 7.8 (a) to (d), the
  conditional instrument obtained in (d) by measuring `W`, and non-examples.

## Notes on the source

The extract prints condition (i) as `(Z ⫫ Y | S)` in `G` with a lost bar over or under `X`. The
definition uses the graph with the edges out of `X` removed (Pearl's `G` with a bar under `X`),
which is the standard reading of Definition 7.4.1 and agrees with the counterfactual criterion
`Z ⫫ Y_x | S`. The covariate condition follows the text: the measurements `S` are unaffected by
`X`, that is, they are nondescendants of `X` (not of `Y`). This condition matters: without it,
conditioning on `Y` itself would make any vertex d-connected to `X` an instrument, because an
endpoint in the conditioning set is d-separated from everything (see the examples).

One consequence of the surgery form: a child `z` of `x` whose only other connection to `y`
runs through `x` (edges `x → z`, `x → y`) passes the test, since removing the edges out of `x`
isolates `z`. The heuristic sentence before Definition 7.4.1 ("every unblocked path connecting
`Z` and `Y` must contain an arrow pointing into `X`") would reject it. The example
`childOfTreatment` records this.

The figures are not in the extract; the examples are graphs with the properties stated in the
caption and in footnote 29 (`Z` is randomized in (a) but not in (b) and (c), and `Z` does not
affect `X` in (c)).

## References

* J. Pearl (2009), *Causality: Models, Reasoning, and Inference*, 2nd edition, section 7.4.5,
  Definition 7.4.1 (Instrument) and Figure 7.8.
-/

@[expose] public section

namespace Digraph

variable {V : Type*}

/-- The graphical instrument criterion (Pearl 2009, Definition 7.4.1, graphical criterion):
`Z` is an instrument relative to the total effect of `X` on `Y` given the covariates `S` when
no member of `S` is a descendant of `X` (the measurements are unaffected by `X`; inclusive
descendants, so also `S ∩ X = ∅`), (i) `Z` and `Y` are d-separated by `S` in the graph with the
edges out of `X` removed, and (ii) `Z` and `X` are d-connected given `S` in `G`. -/
def IsInstrument (G : Digraph V) (Z X Y S : Set V) : Prop :=
  (∀ s ∈ S, s ∉ G.descendantsOf X) ∧ (G.deleteOutgoing X).DSep Z Y S ∧ G.DConn Z X S

variable {G : Digraph V} {Z X Y S : Set V} {z y : V}

/-- The exclusion restriction: a direct edge `z → y`, with `z ∉ X` and both endpoints outside
`S`, rules out `z` as an instrument for the effect of `X` on `y`, because the edge survives the
removal of the edges out of `X`. -/
theorem not_isInstrument_of_adj (h : G.Adj z y) (hzX : z ∉ X) (hzS : z ∉ S) (hyS : y ∉ S) :
    ¬ G.IsInstrument {z} X {y} S :=
  fun hI => hI.2.1 (dConn_of_adj (G := G.deleteOutgoing X) ⟨h, hzX⟩ hzS hyS)

/-- A single instrument is never in the covariate set: a vertex of `S` is blocked as an
endpoint, so it cannot be d-connected to `X` given `S`. -/
theorem IsInstrument.notMem (hI : G.IsInstrument {z} X Y S) : z ∉ S := by
  obtain ⟨z', hz', -, -, hz'S, -⟩ := hI.2.2
  rw [Set.mem_singleton_iff] at hz'
  exact hz' ▸ hz'S

section Decidable

variable (G : Digraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

instance decidableIsInstrument (Z X Y S : Set V) [DecidablePred (· ∈ Z)]
    [DecidablePred (· ∈ X)] [DecidablePred (· ∈ Y)] [DecidablePred (· ∈ S)] :
    Decidable (G.IsInstrument Z X Y S) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end Decidable

end Digraph

namespace CausalInference.InstrumentExamples

open Criteria

/-- Figure 7.8 (a) style: `Z → X → Y` with a latent confounder `U → X`, `U → Y`; `Z = 0`,
`X = 1`, `Y = 2`, `U = 3`. -/
abbrev ivA : Digraph (Fin 4) := ofEdges [(0, 1), (1, 2), (3, 1), (3, 2)]

example : ivA.IsInstrument {0} {1} {2} ∅ := by decide +kernel

/-- Figure 7.8 (b) style: (a) with `Z` and `X` also confounded by a latent `V = 4`, so `Z` is not
randomized. -/
abbrev ivB : Digraph (Fin 5) := ofEdges [(0, 1), (1, 2), (3, 1), (3, 2), (4, 0), (4, 1)]

example : ivB.IsInstrument {0} {1} {2} ∅ := by decide +kernel

/-- Figure 7.8 (c) style: `Z` does not affect `X`; `Z` and `X` share the latent cause `V = 4`. -/
abbrev ivC : Digraph (Fin 5) := ofEdges [(1, 2), (3, 1), (3, 2), (4, 0), (4, 1)]

example : ivC.IsInstrument {0} {1} {2} ∅ := by decide +kernel

/-- Figure 7.8 (d) style: (a) together with `Z ← V → W → Y`, where `V = 4` is latent and
`W = 5` is measured. -/
abbrev ivD : Digraph (Fin 6) :=
  ofEdges [(0, 1), (1, 2), (3, 1), (3, 2), (4, 0), (4, 5), (5, 2)]

-- `Z` is not an instrument, being correlated with `W`, which influences `Y`.
example : ¬ ivD.IsInstrument {0} {1} {2} ∅ := by decide +kernel
-- Measuring `W`, a nondescendant of `X`, makes `Z` a conditional instrument.
example : ivD.IsInstrument {0} {1} {2} {5} := by decide +kernel

/-- Non-example: (a) with a direct edge `Z → Y`, violating the exclusion restriction. -/
abbrev ivDirect : Digraph (Fin 4) := ofEdges [(0, 1), (1, 2), (3, 1), (3, 2), (0, 2)]

example : ¬ ivDirect.IsInstrument {0} {1} {2} ∅ := by decide +kernel

/-- Non-example: the instrument is disconnected from the treatment. -/
abbrev ivIrrelevant : Digraph (Fin 4) := ofEdges [(1, 2), (3, 1), (3, 2)]

example : ¬ ivIrrelevant.IsInstrument {0} {1} {2} ∅ := by decide +kernel

-- The covariate condition is needed: conditioning on the outcome `Y` passes both d-separation
-- tests in (a), since an endpoint in the conditioning set is blocked, but `Y` is a descendant
-- of `X`.
example : (ivA.deleteOutgoing {1}).DSep {0} {2} {2} ∧ ivA.DConn {0} {1} {2} := by decide +kernel
example : ¬ ivA.IsInstrument {0} {1} {2} {2} := by decide +kernel

/-- A child of the treatment: `X → Z`, `X → Y`, with `X = 0`, `Z = 1`, `Y = 2`. The surgery form
of the criterion accepts `Z`. -/
abbrev childOfTreatment : Digraph (Fin 3) := ofEdges [(0, 1), (0, 2)]

example : childOfTreatment.IsInstrument {1} {0} {2} ∅ := by decide +kernel

end CausalInference.InstrumentExamples
