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
  are d-separated by `S` in the graph with the edges into `X` removed, and `Z` and `X` are
  d-connected given `S` in `G`.
* `Digraph.InstrumentRoles Z X Y S`: the setting of the definition: instrument, treatment, and
  outcome pairwise disjoint, and the covariates disjoint from all three.
* `Digraph.IsInstrumentIn G Z X Y S`: the criterion within that setting; this is the reading of
  Definition 7.4.1 to use for a single instrument, treatment, and outcome.
* `Digraph.IsPretreatmentInstrument G Z X Y S`: `IsInstrumentIn` together with the requirement
  that no member of `Z` is a descendant of `X`, the setting in which the graphical test speaks
  about the factual instrument.

## Main results

* `Digraph.not_isInstrument_of_adj`: a direct edge from `z` to `y`, with `y` outside `X` and
  both endpoints outside `S`, rules out `z` as an instrument; this is the exclusion restriction.
* `Digraph.IsInstrument.notMem`: an instrument lies outside the covariate set.
* Decidability, and examples: graphs with the properties stated for Figure 7.8 (a) to (c), the
  printed Figure 7.8 (d), a variant of (d) in which measuring `W` makes `Z` a conditional
  instrument, and non-examples; `CausalInference.InstrumentExamples.descendantInstrument_test`:
  the graph `U → X → Z`, `U → Y`, in which an instrument affected by the treatment passes the
  graphical test.

## Notes on the source

The printed condition (i) is `(Z ⫫ Y | S)` in `G` with a bar over `X`, the graph with the edges
into `X` removed; the sentence before the definition says the same in words: "every unblocked
path connecting `Z` and `Y` must contain an arrow pointing into `X`". The text extract loses the
bar, and the same graph is meant in both places.

The graphical test is a statement about the model under the intervention on `X`: in the graph
with the edges into `X` removed, d-separation gives the independence of the instrument and the
outcome under that intervention, `Z_x ⫫ Y_x | S_x`. It gives the counterfactual criterion
`Z ⫫ Y_x | S` of the definition only when `Z` and `S` are unaffected by `X`, so that `Z_x = Z`
and `S_x = S`. The covariates are nondescendants of `X` by definition; the instrument is not
required to be. With `U → X → Z` and `U → Y` the graphical test passes, while the factual `Z`
depends on `Y_x` through `U` (the example `descendantInstrument`). The predicate
`Digraph.IsPretreatmentInstrument` adds the requirement that no member of `Z` is a descendant
of `X`. This file proves only graphical statements; the counterfactual implication is not
proved here.

Condition (ii) is d-connection in `G`. That `Z` and `X` are dependent in a particular law, and
the nonzero first stage that an instrumental ratio needs, are separate hypotheses: a law that
factorizes according to `G` need not be faithful to it, so d-connection does not supply them.

The graphical criterion is not necessary for the counterfactual criterion. A child `z` of `x`
whose only other connection to `y` runs through `x` (edges `x → z`, `x → y`) is rejected, since
the fork `z ← x → y` survives the removal of the edges into `x`; without confounding of `x` and
`y` it still satisfies the counterfactual criterion (the example `childOfTreatment`). The graph
with the edges out of `X` removed (a bar under `X`) would accept that child even when `x` and
`y` are confounded, and then `z` is not an instrument: the example `confoundedChild` records the
computation.

The covariate condition follows the text: the measurements `S` are unaffected by `X`, that is,
they are nondescendants of `X` (not of `Y`). It does not exclude every degenerate case: an
endpoint in the conditioning set is d-separated from everything, so a covariate set containing
an outcome that is not a descendant of `X` makes condition (i) automatic (the example
`outcomeAsCovariate`). The setting `Digraph.InstrumentRoles` excludes such overlaps of roles.

The drawings of Figure 7.8 (a) to (c) are recorded as graphs with the properties stated in the
caption and in footnote 29 (`Z` is randomized in (a) but not in (b) and (c), and `Z` does not
affect `X` in (c)). Figure 7.8 (d) is recorded with its printed edges, including `X → W`.

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
edges into `X` removed (Pearl's `G` with a bar over `X`), and (ii) `Z` and `X` are d-connected
given `S` in `G`. The roles are not required to be disjoint here; see `IsInstrumentIn`. The
instrument is not required to be unaffected by `X`; see `IsPretreatmentInstrument`. -/
def IsInstrument (G : Digraph V) (Z X Y S : Set V) : Prop :=
  (∀ s ∈ S, s ∉ G.descendantsOf X) ∧ (G.deleteIncoming X).DSep Z Y S ∧ G.DConn Z X S

/-- The setting of Definition 7.4.1: the instrument `Z`, the treatment `X`, and the outcome `Y`
are pairwise disjoint, and the covariates `S` are disjoint from all three. -/
def InstrumentRoles (Z X Y S : Set V) : Prop :=
  Disjoint Z X ∧ Disjoint Z Y ∧ Disjoint X Y ∧ Disjoint S Z ∧ Disjoint S X ∧ Disjoint S Y

/-- The graphical instrument criterion within the setting of Definition 7.4.1
(`InstrumentRoles`). Outside that setting the criterion can hold for degenerate reasons, for
instance when the outcome is a covariate (the example `outcomeAsCovariate`). -/
def IsInstrumentIn (G : Digraph V) (Z X Y S : Set V) : Prop :=
  InstrumentRoles Z X Y S ∧ G.IsInstrument Z X Y S

/-- The graphical instrument criterion within the setting of Definition 7.4.1, for an
instrument unaffected by the treatment: `IsInstrumentIn G Z X Y S`, and no member of `Z` is a
descendant of `X` (inclusive descendants). Then the instrument, like the covariates, takes the
same value under every intervention on `X`, which is what lets the independence read off the
graph with the edges into `X` removed speak about the factual `Z`. Without this requirement the
test can pass for an instrument that is a child of the treatment (the example
`descendantInstrument`). -/
def IsPretreatmentInstrument (G : Digraph V) (Z X Y S : Set V) : Prop :=
  G.IsInstrumentIn Z X Y S ∧ ∀ z ∈ Z, z ∉ G.descendantsOf X

variable {G : Digraph V} {Z X Y S : Set V} {z y : V}

/-- The exclusion restriction: a direct edge `z → y`, with `y ∉ X` and both endpoints outside
`S`, rules out `z` as an instrument for the effect of `X` on `y`, because the edge survives the
removal of the edges into `X`. -/
theorem not_isInstrument_of_adj (h : G.Adj z y) (hyX : y ∉ X) (hzS : z ∉ S) (hyS : y ∉ S) :
    ¬ G.IsInstrument {z} X {y} S :=
  fun hI => hI.2.1 (dConn_of_adj (G := G.deleteIncoming X) ⟨h, hyX⟩ hzS hyS)

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

instance decidableInstrumentRoles (Z X Y S : Set V) [DecidablePred (· ∈ Z)]
    [DecidablePred (· ∈ X)] [DecidablePred (· ∈ Y)] [DecidablePred (· ∈ S)] :
    Decidable (InstrumentRoles Z X Y S) :=
  have (A B : Set V) [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)] :
      Decidable (Disjoint A B) :=
    decidable_of_iff _ Set.disjoint_left.symm
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

instance decidableIsInstrumentIn (Z X Y S : Set V) [DecidablePred (· ∈ Z)]
    [DecidablePred (· ∈ X)] [DecidablePred (· ∈ Y)] [DecidablePred (· ∈ S)] :
    Decidable (G.IsInstrumentIn Z X Y S) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance decidableIsPretreatmentInstrument (Z X Y S : Set V) [DecidablePred (· ∈ Z)]
    [DecidablePred (· ∈ X)] [DecidablePred (· ∈ Y)] [DecidablePred (· ∈ S)] :
    Decidable (G.IsPretreatmentInstrument Z X Y S) :=
  inferInstanceAs (Decidable (_ ∧ _))

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

/-- Figure 7.8 (d) as printed: (a) together with `Z ← U_W → W → Y` and `X → W`, where
`U_W = 4` is latent and `W = 5` is measured. -/
abbrev ivD : Digraph (Fin 6) :=
  ofEdges [(0, 1), (1, 2), (3, 1), (3, 2), (4, 0), (4, 5), (5, 2), (1, 5)]

example : ivD.IsAcyclic := by decide +kernel
-- `Z` is not an instrument, being correlated with `W`, which influences `Y`.
example : ¬ ivD.IsInstrument {0} {1} {2} ∅ := by decide +kernel

/-- In the printed Figure 7.8 (d), measuring `W` does not make `Z` an instrument: `W` is a
descendant of `X`, and conditioning on the collider `W` of `U_W → W ← X` opens the path
`Z ← U_W → W ← X → Y`, which survives the removal of the edges into `X`. -/
theorem ivD_not_isInstrument_W :
    ¬ ivD.IsInstrument {0} {1} {2} {5} ∧ 5 ∈ ivD.descendantsOf {1} ∧
      ¬ (ivD.deleteIncoming {1}).DSep {0} {2} {5} := by
  refine ⟨by decide +kernel, ⟨1, rfl, .single (by decide)⟩, by decide +kernel⟩

/-- A variant of Figure 7.8 (d) without the edge `X → W`, so that `W` is not affected by `X`. -/
abbrev ivDNoXW : Digraph (Fin 6) :=
  ofEdges [(0, 1), (1, 2), (3, 1), (3, 2), (4, 0), (4, 5), (5, 2)]

-- Unconditionally `Z` is not an instrument; measuring `W`, a nondescendant of `X`, makes `Z` a
-- conditional instrument.
example : ¬ ivDNoXW.IsInstrument {0} {1} {2} ∅ := by decide +kernel
example : ivDNoXW.IsInstrumentIn {0} {1} {2} {5} := by decide +kernel

/-- Non-example: (a) with a direct edge `Z → Y`, violating the exclusion restriction. -/
abbrev ivDirect : Digraph (Fin 4) := ofEdges [(0, 1), (1, 2), (3, 1), (3, 2), (0, 2)]

example : ¬ ivDirect.IsInstrument {0} {1} {2} ∅ := by decide +kernel

/-- Non-example: the instrument is disconnected from the treatment. -/
abbrev ivIrrelevant : Digraph (Fin 4) := ofEdges [(1, 2), (3, 1), (3, 2)]

example : ¬ ivIrrelevant.IsInstrument {0} {1} {2} ∅ := by decide +kernel

-- The covariate condition matters: conditioning on the outcome `Y` passes both d-separation
-- tests in (a), since an endpoint in the conditioning set is blocked, but `Y` is a descendant
-- of `X`.
example : (ivA.deleteIncoming {1}).DSep {0} {2} {2} ∧ ivA.DConn {0} {1} {2} := by decide +kernel
example : ¬ ivA.IsInstrument {0} {1} {2} {2} := by decide +kernel

/-- The outcome as a covariate when it is not a descendant of the treatment: `Z → X`, `Z → Y`,
with `Z = 0`, `X = 1`, `Y = 2`. Here `Z` violates the exclusion restriction, yet the criterion
holds with `S = {Y}`, because the endpoint `Y` is blocked by conditioning on it. The setting
`InstrumentRoles` excludes this. -/
abbrev outcomeAsCovariate : Digraph (Fin 3) := ofEdges [(0, 1), (0, 2)]

example : outcomeAsCovariate.IsInstrument {0} {1} {2} {2} := by decide +kernel
example : ¬ outcomeAsCovariate.IsInstrumentIn {0} {1} {2} {2} := by decide +kernel
example : ¬ outcomeAsCovariate.IsInstrument {0} {1} {2} ∅ := by decide +kernel

/-- A child of the treatment: `X → Z`, `X → Y`, with `X = 0`, `Z = 1`, `Y = 2`. The graphical
criterion rejects `Z`, since the fork `Z ← X → Y` survives the removal of the edges into `X`.
Without confounding of `X` and `Y`, `Z` satisfies the counterfactual criterion `Z ⫫ Y_x`, so the
graphical criterion is not necessary. -/
abbrev childOfTreatment : Digraph (Fin 3) := ofEdges [(0, 1), (0, 2)]

example : ¬ childOfTreatment.IsInstrument {1} {0} {2} ∅ := by decide +kernel

/-- A confounded child of the treatment: `U → X`, `U → Y`, `X → Z`, `X → Y`, with `X = 0`,
`Z = 1`, `Y = 2`, `U = 3`. Removing the edges out of `X` (a bar under `X`) would isolate `Z` and
accept it, but `Z` is not an instrument. In the linear model `X = U + e_X`, `Z = X + e_Z`,
`Y = b X + U + e_Y` with independent disturbances of unit variance, `Var(X) = 2`,
`Cov(Z, X) = 2`, and `Cov(Z, Y) = 2 b + 1`, so the instrumental ratio `Cov(Z, Y) / Cov(Z, X)`
is `b + 1/2`, not `b`. The criterion with the edges into `X` removed rejects `Z`. -/
abbrev confoundedChild : Digraph (Fin 4) := ofEdges [(3, 0), (3, 2), (0, 1), (0, 2)]

example : (confoundedChild.deleteOutgoing {0}).DSep {1} {2} ∅ ∧
    confoundedChild.DConn {1} {0} ∅ := by decide +kernel
example : ¬ confoundedChild.IsInstrument {1} {0} {2} ∅ := by decide +kernel

/-- An instrument affected by the treatment: `U → X`, `X → Z`, `U → Y`, with `X = 0`, `Z = 1`,
`Y = 2`, `U = 3`. Removing the edges into `X` cuts `U → X`, so `Z` and `Y` are d-separated there,
and `Z` is a child of `X`; the graphical test passes with disjoint roles and `S = ∅`. Yet `Z` is
not an instrument in the factual sense: in the linear model `X = U + e_X`, `Z = X + e_Z`,
`Y = U + e_Y` with independent disturbances of unit variance, `X` has no effect on `Y`, so
`Y_x = Y`, while `Cov(Z, Y) = 1` and `Cov(Z, X) = 2`: the instrumental ratio is `1/2` for a zero
effect. -/
abbrev descendantInstrument : Digraph (Fin 4) := ofEdges [(3, 0), (0, 1), (3, 2)]

/-- In `descendantInstrument` the graphical test passes within the setting of Definition 7.4.1,
the instrument is a descendant of the treatment, and `IsPretreatmentInstrument` fails. -/
theorem descendantInstrument_test :
    descendantInstrument.IsInstrumentIn {1} {0} {2} ∅ ∧
      1 ∈ descendantInstrument.descendantsOf {0} ∧
      ¬ descendantInstrument.IsPretreatmentInstrument {1} {0} {2} ∅ :=
  ⟨by decide +kernel, ⟨0, rfl, .single (by decide)⟩, by decide +kernel⟩

-- The covariances of the linear model of `descendantInstrument`, as inner products of the
-- coefficient vectors on the independent unit-variance disturbances `(U, e_X, e_Z, e_Y)`:
-- `Z = (1, 1, 1, 0)`, `X = (1, 1, 0, 0)`, `Y = (1, 0, 0, 1)`; `Cov(Z, Y) = 1`, `Cov(Z, X) = 2`.
example : (List.zipWith (· * ·) [1, 1, 1, 0] [1, 0, 0, 1]).sum = (1 : ℤ) ∧
    (List.zipWith (· * ·) [1, 1, 1, 0] [1, 1, 0, 0]).sum = (2 : ℤ) := by decide

-- A pretreatment instrument: Figure 7.8 (a) style.
example : ivA.IsPretreatmentInstrument {0} {1} {2} ∅ := by decide +kernel

end CausalInference.InstrumentExamples
