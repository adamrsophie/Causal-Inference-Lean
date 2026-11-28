/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.ReductionLikelihood

/-!
# Instances of the reductions of the multilevel model

A network of two studies, `A` (treatment `0`) against `C` (treatment `2`) and `B` (treatment
`1`) against `C`, with the common comparator `C` as baseline and reference, and a multilevel
model without covariate effects: study baselines `μ = (1/4, 1/4)` and relative effects
`γ = (γ_A, γ_B, γ_C) = (1/4, 1/2, 0)`, with one covariate whose law is the point mass at `0` in
both studies.

* **The arm means** (`reductionExample_armMeans`): on the identity link the arm means are
  `1/2` and `1/4` in the first study and `3/4` and `1/4` in the second, and each is the arm
  design applied to `nmaCoef`.
* **The indirect comparison** (`reductionExample_indirect`): `d_AC - d_BC = (-1/4) - (-1/2) =
  1/4 = d_AB`, in any covariate laws.
* **The likelihood** (`reductionExample_likelihood`): with a Bernoulli summary density and one
  success on the arm `A` of the first study and one failure on the arm `B` of the second, the
  likelihood is `1/2 · 1/4 = 1/8`, and it equals the arm based network likelihood at
  `nmaCoef`.

## Main definitions

* `reductionArms`, `reductionModel`, `bernoulliDensity`.

## Main results

* `reductionExample_armMeans`, `reductionExample_indirect`, `reductionExample_likelihood`.
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaRegression

open MeasureTheory ProbabilityTheory EffectMeasure IndirectComparison NetworkMetaAnalysis Matrix
open scoped ENNReal

/-- The arms of the network: `{A, C}` in the first study and `{B, C}` in the second. -/
def reductionArms : Fin 2 → Finset (Fin 3) := ![{0, 2}, {1, 2}]

/-- The model of the instance: baselines `1/4`, `γ = (1/4, 1/2, 0)`, no covariate effects. -/
noncomputable def reductionModel : MultilevelModel (Fin 2) (Fin 3) 1 :=
  ⟨fun _ => 1 / 4, 0, ![1 / 4, 1 / 2, 0], fun _ => 0⟩

/-- The arm `A` of the first study. -/
def armA : ArmIndex reductionArms := ⟨(0, 0), by decide⟩

/-- The arm `B` of the second study. -/
def armB : ArmIndex reductionArms := ⟨(1, 1), by decide⟩

/-- The Bernoulli density of a summary `y ∈ {0, 1}` with mean `θ`. -/
noncomputable def bernoulliDensity (θ y : ℝ) : ℝ := if y = 1 then θ else 1 - θ

theorem reductionModel_armMean (j : Fin 2) (k : Fin 3) :
    reductionModel.armMean id (reductionModel.μ j) (Measure.dirac 0) k =
      1 / 4 + ![1 / 4, 1 / 2, 0] k := by
  rw [((reductionModel.armMean_of_no_covariate_effects (g := id) (ginv := id) (fun _ => rfl)
    rfl (fun _ => rfl) _ (Measure.dirac 0)).2.1 k)]
  rfl

/-- **The arm means of the instance and the reduction**: on the identity link the arm means of
`A` in the first study and of `B` in the second are `1/2` and `3/4`, and each is the arm design
of the network applied to `nmaCoef`. -/
theorem reductionExample_armMeans :
    reductionModel.armMean id (reductionModel.μ 0) (Measure.dirac 0) 0 = 1 / 2 ∧
      reductionModel.armMean id (reductionModel.μ 1) (Measure.dirac 0) 1 = 3 / 4 ∧
      (armDesign reductionArms (fun _ => 2) 2 *ᵥ reductionModel.nmaCoef (fun _ => 2) 2) armA =
        1 / 2 ∧
      (armDesign reductionArms (fun _ => 2) 2 *ᵥ reductionModel.nmaCoef (fun _ => 2) 2) armB =
        3 / 4 := by
  have hA := reductionModel.link_armMean_eq_armDesign_mulVec (g := id) (ginv := id)
    (fun _ => rfl) rfl (fun _ => rfl) (fun _ => Measure.dirac 0) (fun _ => 2) 2 armA
  have hB := reductionModel.link_armMean_eq_armDesign_mulVec (g := id) (ginv := id)
    (fun _ => rfl) rfl (fun _ => rfl) (fun _ => Measure.dirac 0) (fun _ => 2) 2 armB
  have e0 : reductionModel.armMean id (reductionModel.μ 0) (Measure.dirac 0) 0 = 1 / 2 := by
    rw [reductionModel_armMean]; norm_num
  have e1 : reductionModel.armMean id (reductionModel.μ 1) (Measure.dirac 0) 1 = 3 / 4 := by
    rw [reductionModel_armMean]; norm_num
  refine ⟨e0, e1, ?_, ?_⟩
  · rw [← hA]; exact e0
  · rw [← hB]; exact e1

/-- **The indirect comparison of the instance**: with any covariate laws `F_k`, `F_l`, `F_j` and
the identity link, `d_AC - d_BC = (-1/4) - (-1/2) = 1/4`, which is the direct effect
`d_AB = γ_B - γ_A`. -/
theorem reductionExample_indirect (Fk Fl Fj : Measure (Fin 1 → ℝ)) [IsProbabilityMeasure Fk]
    [IsProbabilityMeasure Fl] [IsProbabilityMeasure Fj] :
    indirectEstimate
        (fun _ => linkMarginal id Fk (reductionModel.surface id (1 / 4) 0)
          (reductionModel.surface id (1 / 4) 2))
        (fun _ => linkMarginal id Fl (reductionModel.surface id (1 / 4) 1)
          (reductionModel.surface id (1 / 4) 2)) () = 1 / 4 ∧
      linkMarginal id Fj (reductionModel.surface id (1 / 4) 0)
        (reductionModel.surface id (1 / 4) 1) = 1 / 4 := by
  have h := reductionModel.indirectEstimate_linkMarginal_of_no_covariate_effects (g := id)
    (ginv := id) (fun _ => rfl) rfl (fun _ => rfl) (1 / 4) (1 / 4) (1 / 4) Fk Fl Fj 0 1 2 ()
  have hd : linkMarginal id Fj (reductionModel.surface id (1 / 4) 0)
      (reductionModel.surface id (1 / 4) 1) = 1 / 4 := by
    rw [(reductionModel.armMean_of_no_covariate_effects (g := id) (ginv := id) (fun _ => rfl) rfl
      (fun _ => rfl) (1 / 4) Fj).2.2]
    simp [reductionModel]
    norm_num
  exact ⟨h.trans hd, hd⟩

/-- **The likelihood of the instance**: with the Bernoulli summary density, the identity link,
the point mass covariate laws and the aggregate data `y = 1` on the arm `A` of the first study and
`y = 0` on the arm `B` of the second, the likelihood is `1/2 · (1 - 3/4) = 1/8` and equals the arm
based network likelihood at `nmaCoef`, for any individual density. -/
theorem reductionExample_likelihood (f : ℝ → ℝ → ℝ) :
    reductionModel.likelihood f bernoulliDensity id (fun _ => Measure.dirac 0) []
        [(armA, 1), (armB, 0)] = ENNReal.ofReal (1 / 8) ∧
      armLikelihood f bernoulliDensity id (fun _ => 2) 2 (reductionModel.nmaCoef (fun _ => 2) 2)
        [] [(armA, 1), (armB, 0)] = ENNReal.ofReal (1 / 8) := by
  have hl : reductionModel.likelihood f bernoulliDensity id (fun _ => Measure.dirac 0) []
      [(armA, 1), (armB, 0)] = ENNReal.ofReal (1 / 8) := by
    simp only [MultilevelModel.likelihood, List.map_nil, List.prod_nil, one_mul, List.map_cons,
      List.prod_cons, mul_one]
    change ENNReal.ofReal (bernoulliDensity
        (reductionModel.armMean id (reductionModel.μ 0) (Measure.dirac 0) 0) 1) *
      ENNReal.ofReal (bernoulliDensity
        (reductionModel.armMean id (reductionModel.μ 1) (Measure.dirac 0) 1) 0) = _
    rw [reductionModel_armMean, reductionModel_armMean, ← ENNReal.ofReal_mul (by
      norm_num [bernoulliDensity])]
    norm_num [bernoulliDensity]
  refine ⟨hl, ?_⟩
  rw [← hl, MultilevelModel.likelihood_eq_armLikelihood f bernoulliDensity id reductionModel rfl
    (fun _ => rfl) (fun _ => Measure.dirac 0) (fun _ => 2) 2]
  rfl

end NetworkMetaRegression

end CausalInference
