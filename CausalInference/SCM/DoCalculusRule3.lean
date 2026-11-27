/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.SCM.DoCalculus

/-!
# Rule 3 of do-calculus: examples

Concrete checks for `SCM.rule3` and `SCM.rule3_div` (Pearl 2009, *Causality*, 2nd edition,
Theorem 3.4.1, equation (3.33)).

* `Digraph.rule3SetFinset` evaluated by `decide`, and a Rule 3 premise with nonempty `W` checked
  by `decide`.
* `SCM.Rule3PositivityExample.premises_hold_joint_mass_zero`: a model in which the hypotheses of
  `SCM.rule3` and `SCM.rule3_div` hold while the joint mass `P(z', w | do(x))` of `Z \ Z(W)` and
  `W` is zero. The positivity of that mass (the hypothesis of `SCM.rule3_pos`) is therefore
  strictly stronger than the positivity of the two denominators of the ratio form.
-/

@[expose] public section

/-! ### Examples -/

namespace CausalInference

open Finset GraphExamples

/-- `Z(W)` evaluated by `decide`: in the chain `0 → 1 → 2`, the vertex `0` is an ancestor of
`1`, so `Z(W) = ∅` for `Z = {0}`, `W = {1}`. -/
example : chain.rule3SetFinset ∅ {0} {1} = ∅ := by decide

/-- In the fork `1 ← 0 → 2`, the vertex `1` is not an ancestor of `2`, so `Z(W) = Z` for
`Z = {1}`, `W = {2}`. -/
example : fork.rule3SetFinset ∅ {1} {2} = {1} := by decide

namespace SCM.Rule3PositivityExample

/-- The model on the chain `Z = 0 → W = 1 → Y = 2` with fair noise bits: `Z := false`,
`W := Z || U₁`, `Y := W`. -/
noncomputable def model : SCM chain (fun _ => Bool) (fun _ => Bool) where
  acyclic := by decide
  f v z e := if h1 : v = 1 then (z ⟨0, by subst h1; decide⟩ || e) else
    if h2 : v = 2 then z ⟨1, by subst h2; decide⟩ else false
  noise _ := FiniteDist.uniform

/-- The all-`true` configuration. -/
def allTrue : Fin 3 → Bool := fun _ => true

theorem model_solve (u : Fin 3 → Bool) : model.solve u = ![false, u 1, u 1] := by
  refine (model.isSolution_iff.1 fun v => ?_).symm
  fin_cases v <;> simp [model, Finset.restrict]

theorem model_intervene_solve (u : Fin 3 → Bool) :
    (model.intervene {0} allTrue).solve u = allTrue := by
  refine ((model.intervene {0} allTrue).eq_solve_of_isSolution
    (model.isSolution_intervene_iff.2 ⟨fun v _ => rfl, fun v hv => ?_⟩)).symm
  fin_cases v
  · exact absurd (mem_singleton_self 0) hv
  · simp [model, allTrue, Finset.restrict]
  · simp [model, allTrue, Finset.restrict]

/-- **The joint positivity hypothesis of `SCM.rule3_pos` is strictly stronger than needed.**
In `SCM.Rule3PositivityExample.model`, with `X = ∅`, `Z = {0}`, `W = {1}`, `Y = {2}` and
all values `true`, the disjointness and graphical hypotheses of `SCM.rule3` hold
(the graphical one checked by `decide` through `Digraph.rule3SetFinset_eq`), and both
denominators of `SCM.rule3_div` are positive, `P(w) = 1/2` and `P(w | do(z)) = 1`, but the joint
mass `P(z', w)` of `Z \ Z(W)` and `W` is `0`, because `Z = false` observationally. -/
theorem premises_hold_joint_mass_zero :
    Disjoint (∅ : Finset (Fin 3)) {0} ∧ Disjoint ({1} : Finset (Fin 3)) {0} ∧
      (chain.deleteIncoming ↑((∅ : Finset (Fin 3)) ∪ chain.rule3Set ∅ {0} {1})).DSep
        ↑({2} : Finset (Fin 3)) ↑({0} : Finset (Fin 3)) ↑((∅ : Finset (Fin 3)) ∪ {1}) ∧
      0 < (model.intervene ∅ allTrue).dist.margAt {1} allTrue ∧
      0 < (model.intervene (∅ ∪ {0}) allTrue).dist.margAt {1} allTrue ∧
      (model.intervene ∅ allTrue).dist.margAt
        (({0} \ chain.rule3Set ∅ {0} {1}) ∪ {1}) allTrue = 0 := by
  refine ⟨by decide, by decide, by rw [← Digraph.rule3SetFinset_eq]; decide, ?_, ?_, ?_⟩
  · rw [dist_intervene_empty, margAt_dist]
    simp only [mem_singleton, forall_eq, model_solve]
    rw [FiniteDist.probOf_congr _ (Q := fun u : Fin 3 → Bool => u 1 = true) fun u => by
      simp [allTrue]]
    change 0 < (FiniteDist.pi fun _ => FiniteDist.uniform).probOf _
    rw [FiniteDist.probOf_pi_eval (κ := fun _ : Fin 3 => Bool) (fun _ => FiniteDist.uniform) 1
      (fun b : Bool => b = true)]
    simp only [FiniteDist.probOf, FiniteDist.prob, FiniteDist.uniform_apply]
    exact sum_pos (fun _ _ => by simp [Fintype.card_bool]) ⟨true, by simp⟩
  · rw [empty_union, margAt_dist, FiniteDist.probOf]
    simp only [model_intervene_solve]
    rw [filter_true_of_mem fun _ _ _ _ => trivial, FiniteDist.prob_univ]
    exact one_pos
  · rw [← Digraph.rule3SetFinset_eq,
      show ({0} \ chain.rule3SetFinset ∅ {0} {1} ∪ {1} : Finset (Fin 3)) = {0, 1} by decide,
      dist_intervene_empty, margAt_dist]
    convert FiniteDist.probOf_eq_zero (p := model.noiseDist)
      (P := fun u => ∀ v ∈ ({0, 1} : Finset (Fin 3)), model.solve u v = allTrue v) ?_
    intro u h
    have h0 := h 0 (by simp)
    simp [model_solve, allTrue] at h0

end SCM.Rule3PositivityExample

end CausalInference
