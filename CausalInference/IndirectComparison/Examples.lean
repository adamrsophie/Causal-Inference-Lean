/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.IndirectComparison.TrialSummary
public import CausalInference.IndirectComparison.AnchoredBias
public import CausalInference.IndirectComparison.AnchoredPredictor

/-!
# A worked smallest anchored network

Three treatments: the common comparator `c = 0` and the active treatments `a = 1`, `b = 2`. The
outcome follows the anchored model `sharedExampleModel` on the identity scale, with one
covariate `x`: conditional means `m_0(x) = x`, `m_1(x) = 1 + 3x`, `m_2(x) = 3 + 3x` (relative
effects `γ = (0, 1, 3)`, interactions `β₂ = (0, 2, 2)`), so `1` and `2` share their effect
modifier `x`, while `x` modifies their effects against `0`.

Two randomized trials (`productTrial`, assignment independent of the covariates):

* the trial of `a` against `c` (`exTrialAC`): covariate law `signLaw` (`x = ±1`, mean `0`), fair
  assignment to `0` and `1`; aggregate data `E[Y | A = 0] = 0`, `E[Y | A = 1] = 1`, so the
  aggregate contrast of `c` relative to `a` is `-1`;
* the trial of `b` against `c` (`exTrialBC`): covariates concentrated at `x = 1`, fair assignment
  to `0` and `2`; aggregate data `1` and `6`, so the aggregate contrast of `c` relative to `b` is
  `-5`.

The unadjusted indirect comparison of `b` against `a` is `-1 - (-5) = 4`
(`smallestNetwork_example`). The target effect of `b` relative to `a` is `γ_b - γ_a = 2` in each
trial population (shared effect modifiers). Taking the population of the first trial as the
target, the bias of the unadjusted comparison is `2`, the term
`(∫ τ_ac dP_ac - ∫ τ_ac dP_*) - (∫ τ_bc dP_bc - ∫ τ_bc dP_*) = 0 - (-5 - (-3))` of the bias
decomposition `anchoredEstimand_sub_linkConditional`: the imbalance of the effect modifier `x`
between the trials. When the second trial has the covariate law of the first
(`exTrialBCBalanced`), the indirect comparison is `2`, the target effect
(`smallestNetwork_balanced_example`).

## Main definitions

* `twoArmLaw`, `exTrialAC`, `exTrialBC`, `exTrialBCBalanced`.

## Main results

* `smallestNetwork_example`, `smallestNetwork_balanced_example`.

## References

* D. M. Phillippo, A. E. Ades, S. Dias, S. Palmer, K. R. Abrams and N. J. Welton, *Methods for
  population-adjusted indirect comparisons in health technology appraisal*, Medical Decision
  Making 38 (2018).
-/

@[expose] public section

namespace CausalInference

namespace IndirectComparison

open MeasureTheory ProbabilityTheory EffectMeasure

/-- Fair assignment to the two treatments `s ≠ t` of `Fin 3`. -/
noncomputable def twoArmLaw (s t : Fin 3) : Measure (Fin 3) :=
  stratumLaw fun v => if v = s ∨ v = t then 1 / 2 else 0

theorem isWeights_twoArm {s t : Fin 3} (hst : s ≠ t) :
    IsWeights fun v : Fin 3 => if v = s ∨ v = t then (1 / 2 : ℝ) else 0 := by
  refine ⟨fun v => by dsimp only; split_ifs <;> norm_num, ?_⟩
  fin_cases s <;> fin_cases t <;> simp at hst ⊢ <;> norm_num [Fin.sum_univ_three]

/-- The two assigned arms have positive probability. -/
theorem twoArmLaw_singleton_ne_zero (s t : Fin 3) {v : Fin 3} (hv : v = s ∨ v = t) :
    twoArmLaw s t {v} ≠ 0 := fun h => by
  have := (ae_stratumLaw_iff _).1 (measure_eq_zero_iff_ae_notMem.1 h) v (by simp [hv])
  exact this rfl

/-- The conditional means `m_t = η_t` of `sharedExampleModel`. -/
abbrev exMean : Fin 3 → (Fin 1 → ℝ) → ℝ := sharedExampleModel.predictor

theorem exMean_apply (x : Fin 1 → ℝ) :
    exMean 0 x = x 0 ∧ exMean 1 x = 1 + 3 * x 0 ∧ exMean 2 x = 3 + 3 * x 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [exMean, sharedExampleModel, AnchoredModel.predictor, anchoredPredictor] <;> ring

theorem measurable_exMean (t : Fin 3) : Measurable (exMean t) := by
  unfold exMean AnchoredModel.predictor anchoredPredictor; fun_prop

theorem integrable_exMean_signLaw (t : Fin 3) : Integrable (exMean t) signLaw :=
  (integrable_map_measure (measurable_exMean t).aestronglyMeasurable
    (measurable_of_finite signCov).aemeasurable).2 Integrable.of_finite

/-- The point `x = 1` of the covariate space. -/
def exPoint : Fin 1 → ℝ := fun _ => 1

instance (s t : Fin 3) [Fact (s ≠ t)] : IsProbabilityMeasure (twoArmLaw s t) :=
  isProbabilityMeasure_stratumLaw (isWeights_twoArm Fact.out)

local instance : Fact ((0 : Fin 3) ≠ 1) := ⟨by decide⟩
local instance : Fact ((0 : Fin 3) ≠ 2) := ⟨by decide⟩

/-- The trial of `1` against `0`: covariate law `signLaw`, fair assignment to `0` and `1`. -/
noncomputable def exTrialAC : Trial ((Fin 1 → ℝ) × Fin 3) (Fin 1 → ℝ) (Fin 3) :=
  productTrial signLaw (twoArmLaw 0 1) exMean

/-- The trial of `2` against `0`: covariates at `x = 1`, fair assignment to `0` and `2`. -/
noncomputable def exTrialBC : Trial ((Fin 1 → ℝ) × Fin 3) (Fin 1 → ℝ) (Fin 3) :=
  productTrial (Measure.dirac exPoint) (twoArmLaw 0 2) exMean

/-- The trial of `2` against `0` with the covariate law `signLaw` of the first trial. -/
noncomputable def exTrialBCBalanced : Trial ((Fin 1 → ℝ) × Fin 3) (Fin 1 → ℝ) (Fin 3) :=
  productTrial signLaw (twoArmLaw 0 2) exMean

/-- The mean of `exMean t` under `signLaw`. -/
theorem integral_exMean_signLaw (t : Fin 3) :
    ∫ x, exMean t x ∂signLaw = (exMean t (signCov true) + exMean t (signCov false)) / 2 :=
  integral_signLaw (measurable_exMean t)

/-- The aggregate data of the three trials. -/
theorem exTrial_armSummary :
    exTrialAC.armSummary 0 = 0 ∧ exTrialAC.armSummary 1 = 1 ∧
      exTrialBC.armSummary 0 = 1 ∧ exTrialBC.armSummary 2 = 6 ∧
      exTrialBCBalanced.armSummary 0 = 0 ∧ exTrialBCBalanced.armSummary 2 = 3 := by
  have hS : ∀ (s t v : Fin 3) [Fact (s ≠ t)], (v = s ∨ v = t) →
      (productTrial signLaw (twoArmLaw s t) exMean).armSummary v =
        (exMean v (signCov true) + exMean v (signCov false)) / 2 := fun s t v _ hv => by
    rw [productTrial_armSummary (measurable_exMean v) (integrable_exMean_signLaw v)
      (twoArmLaw_singleton_ne_zero s t hv), integral_exMean_signLaw]
  have hD : ∀ (v : Fin 3), (v = 0 ∨ v = 2) →
      (productTrial (Measure.dirac exPoint) (twoArmLaw 0 2) exMean).armSummary v =
        exMean v exPoint := fun v hv => by
    rw [productTrial_armSummary (measurable_exMean v) (integrable_dirac (by simp))
      (twoArmLaw_singleton_ne_zero 0 2 hv), integral_dirac]
  obtain ⟨e0, e1, e2⟩ := exMean_apply (signCov true)
  obtain ⟨f0, f1, f2⟩ := exMean_apply (signCov false)
  obtain ⟨g0, -, g2⟩ := exMean_apply exPoint
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [exTrialAC, hS 0 1 0 (by simp), e0, f0]; norm_num [signCov]
  · rw [exTrialAC, hS 0 1 1 (by simp), e1, f1]; norm_num [signCov]
  · rw [exTrialBC, hD 0 (by simp), g0]; norm_num [exPoint]
  · rw [exTrialBC, hD 2 (by simp), g2]; norm_num [exPoint]
  · rw [exTrialBCBalanced, hS 0 2 0 (by simp), e0, f0]; norm_num [signCov]
  · rw [exTrialBCBalanced, hS 0 2 2 (by simp), e2, f2]; norm_num [signCov]

/-- The conditional effects `τ_ac = m_0 - m_1` and `τ_bc = m_0 - m_2` of `0` relative to the
active treatments, on the identity scale. -/
theorem exContrast_apply (x : Fin 1 → ℝ) :
    linkContrast id (exMean 1) (exMean 0) x = -1 - 2 * x 0 ∧
      linkContrast id (exMean 2) (exMean 0) x = -3 - 2 * x 0 := by
  obtain ⟨h0, h1, h2⟩ := exMean_apply x
  simp only [linkContrast, id, h0, h1, h2]
  constructor <;> ring

theorem measurable_exContrast (t : Fin 3) : Measurable (linkContrast id (exMean t) (exMean 0)) :=
  (measurable_exMean 0).sub (measurable_exMean t)

/-- **The smallest anchored network with an imbalanced effect modifier.** The aggregate
contrasts of `0` relative to `1` in the first trial and relative to `2` in the second are `-1`
and `-5`, and the unadjusted indirect comparison of `2` against `1` is `4`. The effect of `2`
relative to `1` in each trial population is `2 = γ_2 - γ_1`. Taking the first trial population
as the target, the bias of the indirect comparison is `2`, and it is the term
`(∫ τ_ac dP_ac - ∫ τ_ac dP_*) - (∫ τ_bc dP_bc - ∫ τ_bc dP_*)` of the bias decomposition, with
`P_ac = P_* = signLaw` and `P_bc` the point mass at `x = 1`. -/
theorem smallestNetwork_example :
    exTrialAC.aggregateContrast id 1 0 = -1 ∧ exTrialBC.aggregateContrast id 2 0 = -5 ∧
      indirectAggregate id exTrialAC exTrialBC 1 2 0 = 4 ∧
      exTrialAC.toPopulation.marginalEffect id 1 2 = 2 ∧
      exTrialBC.toPopulation.marginalEffect id 1 2 = 2 ∧
      sharedExampleModel.γ 2 - sharedExampleModel.γ 1 = 2 ∧
      indirectAggregate id exTrialAC exTrialBC 1 2 0 -
          exTrialAC.toPopulation.marginalEffect id 1 2 =
        (∫ x, linkContrast id (exMean 1) (exMean 0) x ∂signLaw -
            ∫ x, linkContrast id (exMean 1) (exMean 0) x ∂signLaw) -
          (∫ x, linkContrast id (exMean 2) (exMean 0) x ∂Measure.dirac exPoint -
            ∫ x, linkContrast id (exMean 2) (exMean 0) x ∂signLaw) ∧
      (∫ x, linkContrast id (exMean 1) (exMean 0) x ∂signLaw -
            ∫ x, linkContrast id (exMean 1) (exMean 0) x ∂signLaw) -
          (∫ x, linkContrast id (exMean 2) (exMean 0) x ∂Measure.dirac exPoint -
            ∫ x, linkContrast id (exMean 2) (exMean 0) x ∂signLaw) = 2 := by
  obtain ⟨s0, s1, b0, b2, -, -⟩ := exTrial_armSummary
  have hac : exTrialAC.aggregateContrast id 1 0 = -1 := by
    rw [Trial.aggregateContrast, s0, s1]; norm_num
  have hbc : exTrialBC.aggregateContrast id 2 0 = -5 := by
    rw [Trial.aggregateContrast, b0, b2]; norm_num
  have hind : indirectAggregate id exTrialAC exTrialBC 1 2 0 = 4 := by
    rw [indirectAggregate, hac, hbc]; norm_num
  -- the arm means of the populations, from the conditional means
  have hmS : ∀ t, exTrialAC.toPopulation.armMean t =
      (exMean t (signCov true) + exMean t (signCov false)) / 2 := fun t => by
    rw [exTrialAC, ← (productTrial_isCondMean (measurable_exMean t)
      (integrable_exMean_signLaw t)).integral_eq measurable_fst
      (productTrial_integrable (measurable_exMean t) (integrable_exMean_signLaw t)),
      productTrial_covLaw, integral_exMean_signLaw]
  have hmD : ∀ t, exTrialBC.toPopulation.armMean t = exMean t exPoint := fun t => by
    have hi : Integrable (exMean t) (Measure.dirac exPoint) := integrable_dirac (by simp)
    rw [exTrialBC, ← (productTrial_isCondMean (measurable_exMean t) hi).integral_eq measurable_fst
      (productTrial_integrable (measurable_exMean t) hi), productTrial_covLaw, integral_dirac]
  obtain ⟨-, e1, e2⟩ := exMean_apply (signCov true)
  obtain ⟨-, f1, f2⟩ := exMean_apply (signCov false)
  obtain ⟨-, g1, g2⟩ := exMean_apply exPoint
  have hT1 : exTrialAC.toPopulation.marginalEffect id 1 2 = 2 := by
    rw [Population.marginalEffect, hmS, hmS, e1, e2, f1, f2]; norm_num [signCov]
  have hT2 : exTrialBC.toPopulation.marginalEffect id 1 2 = 2 := by
    rw [Population.marginalEffect, hmD, hmD, g1, g2]; norm_num [exPoint]
  have hterm : (∫ x, linkContrast id (exMean 1) (exMean 0) x ∂signLaw -
            ∫ x, linkContrast id (exMean 1) (exMean 0) x ∂signLaw) -
          (∫ x, linkContrast id (exMean 2) (exMean 0) x ∂Measure.dirac exPoint -
            ∫ x, linkContrast id (exMean 2) (exMean 0) x ∂signLaw) = 2 := by
    rw [sub_self, integral_dirac, integral_signLaw (measurable_exContrast 2),
      (exContrast_apply _).2, (exContrast_apply _).2, (exContrast_apply _).2]
    norm_num [exPoint, signCov]
  refine ⟨hac, hbc, hind, hT1, hT2, by norm_num [sharedExampleModel], ?_, hterm⟩
  rw [hterm, hind, hT1]; norm_num

/-- **The same network with balanced effect modifiers.** When the trial of `2` against `0` has
the covariate law `signLaw` of the first trial, its aggregate contrast of `0` relative to `2` is
`-3`, and the indirect comparison `-1 - (-3) = 2` is the target effect `γ_2 - γ_1`. -/
theorem smallestNetwork_balanced_example :
    exTrialBCBalanced.aggregateContrast id 2 0 = -3 ∧
      indirectAggregate id exTrialAC exTrialBCBalanced 1 2 0 = 2 ∧
      indirectAggregate id exTrialAC exTrialBCBalanced 1 2 0 =
        exTrialAC.toPopulation.marginalEffect id 1 2 := by
  obtain ⟨s0, s1, -, -, c0, c2⟩ := exTrial_armSummary
  have hbc : exTrialBCBalanced.aggregateContrast id 2 0 = -3 := by
    rw [Trial.aggregateContrast, c0, c2]; norm_num
  have hind : indirectAggregate id exTrialAC exTrialBCBalanced 1 2 0 = 2 := by
    rw [indirectAggregate, Trial.aggregateContrast, s0, s1, hbc]; norm_num
  refine ⟨hbc, hind, ?_⟩
  rw [hind, (smallestNetwork_example).2.2.2.1]

end IndirectComparison

end CausalInference
