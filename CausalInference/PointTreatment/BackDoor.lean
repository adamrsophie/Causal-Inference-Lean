/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PointTreatment.Assumptions
public import CausalInference.SCM.TwinBackDoor

/-!
# Point treatment: ignorability from the back-door criterion

A structural causal model on finitely many vertices with finite value and noise spaces gives a
point treatment problem on the noise space: the treatment is a binary coding `t` of the value
of a vertex `i`, the conditioning variable is the factual value of a set `Z` of vertices, and
the potential outcome of the arm `a` is a real function `g` of the potential response of a set
`Y` of vertices under the intervention `do(X_i := x_a)`. If `Z` satisfies the back-door
criterion relative to `({i}, Y)`, this point treatment problem satisfies ignorability in the
sense of `PointTreatment.Ignorable`, under the law of the noises.

The finite conditional independence of
`SCM.condIndepFun_potentialResponse_pair_of_backDoor_singleton` passes to the binary coding
and to the real outcome, and then to Mathlib's conditional independence through
`FiniteDist.condIndepFun_iff_condIndepFun_toMeasure`. The noise space and the space of values
of `Z` carry no measurable structure in the structural model; the statement takes one as
instance arguments (measurable singletons and standard Borel on the noise space, a discrete
σ-algebra on the values of `Z`).

## Main results

* `ignorable_of_backDoor`: the back-door criterion implies ignorability.

## References

* J. Pearl, *Causality: Models, Reasoning, and Inference*, 2nd edition, Cambridge University
  Press (2009).
-/

@[expose] public section

namespace CausalInference

namespace PointTreatment

open MeasureTheory ProbabilityTheory

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
  {α : V → Type*} {ε : V → Type*} [∀ v, Fintype (ε v)] [∀ v, Finite (α v)]

/-- **Ignorability from the back-door criterion.** Let `M` be a structural causal model, `i` a
vertex, and `Z` a set of vertices satisfying the back-door criterion relative to `({i}, Y)`.
Code the treatment as `A = t(X_i)` for a map `t` into `Bool`, take the factual value of `Z` as
the conditioning variable and, for configurations `x₀`, `x₁`, the potential outcomes
`Y(0) = g(Y_{x₀})` and `Y(1) = g(Y_{x₁})` for a real function `g` of the potential response of
`Y`. Then `A ⫫ (Y(0), Y(1)) | Z` under the law of the noises. -/
theorem ignorable_of_backDoor (M : SCM G α ε) {i : V} {Y Z : Finset V}
    (hbd : G.BackDoor {i} ↑Y ↑Z) (x₀ x₁ : ∀ v, α v) (t : α i → Bool)
    (g : ((v : Y) → α v) → ℝ) [MeasurableSpace (∀ v, ε v)]
    [MeasurableSingletonClass (∀ v, ε v)] [StandardBorelSpace (∀ v, ε v)]
    [MeasurableSpace ((v : Z) → α v)] [DiscreteMeasurableSpace ((v : Z) → α v)] :
    Ignorable M.noiseDist.toMeasure (fun u => t (M.solve u i))
      (FiniteDist.measurable_of_fintype fun u => Z.restrict (M.solve u))
      (fun a u => g (Y.restrict ((M.intervene {i} (if a then x₁ else x₀)).solve u))) := by
  classical
  have h := (M.condIndepFun_potentialResponse_pair_of_backDoor_singleton hbd x₀ x₁).of_left t
    (X' := fun u => t (M.solve u i)) (fun _ => rfl)
  have h' := h.of_right (fun p => (g p.1, g p.2))
    (Y' := potentialPair fun a u =>
      g (Y.restrict ((M.intervene {i} (if a then x₁ else x₀)).solve u))) (fun _ => rfl)
  exact (FiniteDist.condIndepFun_iff_condIndepFun_toMeasure _ _ _ _).1 h'

end PointTreatment

end CausalInference
