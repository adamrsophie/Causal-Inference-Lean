/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.SharedModifiersNecessary
public import CausalInference.Measures.LinkScaleExamples

/-!
# On the logit link the marginal effect depends on more than the covariate mean

On the identity link the target estimands of multilevel network meta-regression depend on the
target covariate law only through its mean (`MultilevelModel.linkMarginal_surface_id`). On the
logit link this fails for the marginal effect, even without effect modification. This file gives
one triangle model with exact numbers.

The model `logitTriangle` (one covariate, treatments `0 = a`, `1 = b`, `2 = c`) has prognostic
effect `log 6`, effects `γ_a = 0`, `γ_b = log 2` and no interactions, so `a` and `b` share their
effect modifiers and the conditional log odds ratio of `b` against `a` is `log 2` at every
covariate value and in every target (`logitTriangle_linkConditional`). At the baseline
`log (1/4)` the risks of `a` at `x = 0, 1` are `1/5, 3/5` and those of `b` are `1/3, 3/4`.

## Main results

* `logitTriangle_marginal`: under the binary law with `P(X = 1) = 1/2` and baseline `log (1/4)`
  the marginal log odds ratio of `b` against `a` is `log (39/22)`, not the conditional `log 2`.
* `logitTriangle_marginal_dirac`: the point mass at `x = 1/2` has the same covariate mean `1/2`
  and the marginal log odds ratio `log 2`: the marginal effect is not a function of the covariate
  mean.
* `logitTriangle_marginal_shift`: with the baseline raised by `log 2` (risks `1/3, 3/4` and
  `1/2, 6/7`) and the same binary law, the marginal log odds ratio is `log (209/117)`: it depends
  on the target baseline as well.
* `logitTriangle_counterexample`: the three facts together.

Another logit model with the same conclusion for the covariate law, with strata `x = ±1`, is
`IndirectComparison.logit_marginal_not_transported`.

## References

* D. M. Phillippo, S. Dias, A. E. Ades, M. Belger, A. Brnabic, A. Schacht, D. Saure, Z. Kadziola
  and N. J. Welton, *Multilevel network meta-regression for population-adjusted treatment
  comparisons*, Journal of the Royal Statistical Society Series A 183 (2020).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaRegression

open MeasureTheory ProbabilityTheory EffectMeasure IndirectComparison NetworkMetaAnalysis
  MultilevelModel

/-- The logit triangle model: one covariate, prognostic effect `log 6`, effects `γ_a = 0` and
`γ_b = log 2`, no interactions, intercepts `0`. -/
noncomputable def logitTriangle : MultilevelModel (Fin 2) (Fin 3) 1 :=
  triangleModel 0 0 (Real.log 6) 0 (Real.log 2) 0 0

/-- The logit triangle model shares the effect modifiers of `a` and `b`. -/
theorem logitTriangle_shared : logitTriangle.SharedEffectModifiers {0, 1} :=
  (triangleModel_shared_iff _ _ _ _ _ _ _).2 rfl

/-- The predictor of the logit triangle model at a scalar covariate `x`. -/
theorem logitTriangle_eta (α : ℝ) (t : Fin 3) (x : ℝ) :
    logitTriangle.eta α t (fun _ => x) = α + logitTriangle.γ t + x * Real.log 6 := by
  rw [eta_eq_affine]
  fin_cases t <;> simp [logitTriangle, triangleModel, dotProduct]

/-- **The conditional log odds ratio is `log 2`** at every covariate value, at every baseline,
and its average under every probability law of the covariate with an integrable coordinate. -/
theorem logitTriangle_linkConditional (α : ℝ) :
    (∀ x, linkContrast logit (logitTriangle.surface Real.sigmoid α 0)
      (logitTriangle.surface Real.sigmoid α 1) x = Real.log 2) ∧
    ∀ (F : Measure (Fin 1 → ℝ)) [IsProbabilityMeasure F],
      (∀ i, Integrable (fun x : Fin 1 → ℝ => x i) F) →
      linkConditional logit F (logitTriangle.surface Real.sigmoid α 0)
        (logitTriangle.surface Real.sigmoid α 1) = Real.log 2 := by
  have hg : ∀ y, logit (Real.sigmoid y) = y := EffectMeasure.logit_sigmoid
  refine ⟨fun x => ?_, fun F _ hF => ?_⟩
  · rw [linkContrast_surface hg]
    simp [logitTriangle, triangleModel]
  · rw [linkConditional_surface hg _ α hF]
    simp [logitTriangle, triangleModel]

/-- If `exp t = r` then `σ(t) = r / (1 + r)`: the risk with odds `r`. -/
theorem sigmoid_eq_div_of_exp_eq {t r : ℝ} (h : Real.exp t = r) :
    Real.sigmoid t = r / (1 + r) := by
  rw [sigmoid_eq_exp_div, h]

/-- The marginal log odds ratio of `b` against `a` under the binary law `binaryLaw (1/2)`, at the
baseline `α`, in terms of the four risks. -/
theorem logitTriangle_marginal_binary (α : ℝ) :
    linkMarginal logit (binaryLaw (1 / 2)) (logitTriangle.surface Real.sigmoid α 0)
        (logitTriangle.surface Real.sigmoid α 1) =
      logit ((1 - 1 / 2) * Real.sigmoid (α + Real.log 2) +
          1 / 2 * Real.sigmoid (α + Real.log 2 + Real.log 6)) -
        logit ((1 - 1 / 2) * Real.sigmoid α + 1 / 2 * Real.sigmoid (α + Real.log 6)) := by
  have hI : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  change logit (∫ x, _ ∂_) - logit (∫ x, _ ∂_) = _
  rw [integral_binaryLaw hI, integral_binaryLaw hI]
  simp only [surface, logitTriangle_eta]
  simp [logitTriangle, triangleModel]

/-- **Under the binary law the marginal log odds ratio is `log (39/22)`**: risks `1/5, 3/5` of
`a` and `1/3, 3/4` of `b`, arm means `2/5` and `13/24`. -/
theorem logitTriangle_marginal :
    linkMarginal logit (binaryLaw (1 / 2)) (logitTriangle.surface Real.sigmoid (Real.log (1 / 4)) 0)
        (logitTriangle.surface Real.sigmoid (Real.log (1 / 4)) 1) = Real.log (39 / 22) := by
  rw [logitTriangle_marginal_binary]
  have e1 : Real.exp (Real.log (1 / 4) + Real.log 2) = 1 / 2 := by
    rw [Real.exp_add, Real.exp_log (by norm_num), Real.exp_log (by norm_num)]; norm_num
  have e2 : Real.exp (Real.log (1 / 4) + Real.log 2 + Real.log 6) = 3 := by
    rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num), Real.exp_log (by norm_num),
      Real.exp_log (by norm_num)]; norm_num
  have e3 : Real.exp (Real.log (1 / 4)) = 1 / 4 := Real.exp_log (by norm_num)
  have e4 : Real.exp (Real.log (1 / 4) + Real.log 6) = 3 / 2 := by
    rw [Real.exp_add, Real.exp_log (by norm_num), Real.exp_log (by norm_num)]; norm_num
  rw [sigmoid_eq_div_of_exp_eq e1, sigmoid_eq_div_of_exp_eq e2, sigmoid_eq_div_of_exp_eq e3,
    sigmoid_eq_div_of_exp_eq e4, logit_eq_log_div, logit_eq_log_div,
    ← Real.log_div (by norm_num) (by norm_num)]
  norm_num

/-- **The point mass at `1/2`**: it has the covariate mean `1/2` of `binaryLaw (1/2)`, and the
marginal log odds ratio under it is the conditional one, `log 2`, at every baseline. -/
theorem logitTriangle_marginal_dirac (α : ℝ) :
    covMean (Measure.dirac fun _ : Fin 1 => (1 / 2 : ℝ)) = covMean (binaryLaw (1 / 2)) ∧
      linkMarginal logit (Measure.dirac fun _ : Fin 1 => (1 / 2 : ℝ))
        (logitTriangle.surface Real.sigmoid α 0) (logitTriangle.surface Real.sigmoid α 1) =
        Real.log 2 := by
  have hI : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  refine ⟨funext fun i => ?_, ?_⟩
  · simp only [covMean]
    rw [integral_dirac, integral_binaryLaw hI]
    norm_num
  · have h := (logitTriangle_linkConditional α).1 fun _ => 1 / 2
    simpa [linkMarginal, linkContrast, integral_dirac] using h

/-- **The marginal effect depends on the baseline**: at the baseline `log (1/4) + log 2` the risks
are `1/3, 3/4` of `a` and `1/2, 6/7` of `b`, and the marginal log odds ratio under the binary law
is `log (209/117)`. -/
theorem logitTriangle_marginal_shift :
    linkMarginal logit (binaryLaw (1 / 2))
        (logitTriangle.surface Real.sigmoid (Real.log (1 / 4) + Real.log 2) 0)
        (logitTriangle.surface Real.sigmoid (Real.log (1 / 4) + Real.log 2) 1) =
      Real.log (209 / 117) := by
  rw [logitTriangle_marginal_binary]
  have e1 : Real.exp (Real.log (1 / 4) + Real.log 2 + Real.log 2) = 1 := by
    rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num), Real.exp_log (by norm_num)]
    norm_num
  have e2 : Real.exp (Real.log (1 / 4) + Real.log 2 + Real.log 2 + Real.log 6) = 6 := by
    rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log (by norm_num),
      Real.exp_log (by norm_num), Real.exp_log (by norm_num)]
    norm_num
  have e3 : Real.exp (Real.log (1 / 4) + Real.log 2) = 1 / 2 := by
    rw [Real.exp_add, Real.exp_log (by norm_num), Real.exp_log (by norm_num)]; norm_num
  have e4 : Real.exp (Real.log (1 / 4) + Real.log 2 + Real.log 6) = 3 := by
    rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num), Real.exp_log (by norm_num),
      Real.exp_log (by norm_num)]; norm_num
  rw [sigmoid_eq_div_of_exp_eq e1, sigmoid_eq_div_of_exp_eq e2, sigmoid_eq_div_of_exp_eq e3,
    sigmoid_eq_div_of_exp_eq e4, logit_eq_log_div, logit_eq_log_div,
    ← Real.log_div (by norm_num) (by norm_num)]
  norm_num

/-- **The logit counterexample.** In the logit triangle model, where `a` and `b` share their
effect modifiers and the conditional log odds ratio is `log 2` in every target:
1. under `binaryLaw (1/2)` at baseline `log (1/4)` the marginal log odds ratio is `log (39/22)`,
   which differs from `log 2`;
2. the point mass at `1/2` has the same covariate mean and the marginal log odds ratio `log 2`;
3. at the baseline `log (1/4) + log 2` under the same binary law it is `log (209/117)`, which
   differs from `log (39/22)`. -/
theorem logitTriangle_counterexample :
    linkMarginal logit (binaryLaw (1 / 2))
        (logitTriangle.surface Real.sigmoid (Real.log (1 / 4)) 0)
        (logitTriangle.surface Real.sigmoid (Real.log (1 / 4)) 1) = Real.log (39 / 22) ∧
      linkConditional logit (binaryLaw (1 / 2))
        (logitTriangle.surface Real.sigmoid (Real.log (1 / 4)) 0)
        (logitTriangle.surface Real.sigmoid (Real.log (1 / 4)) 1) = Real.log 2 ∧
      Real.log (39 / 22) ≠ Real.log 2 ∧
      covMean (Measure.dirac fun _ : Fin 1 => (1 / 2 : ℝ)) = covMean (binaryLaw (1 / 2)) ∧
      linkMarginal logit (Measure.dirac fun _ : Fin 1 => (1 / 2 : ℝ))
        (logitTriangle.surface Real.sigmoid (Real.log (1 / 4)) 0)
        (logitTriangle.surface Real.sigmoid (Real.log (1 / 4)) 1) = Real.log 2 ∧
      linkMarginal logit (binaryLaw (1 / 2))
        (logitTriangle.surface Real.sigmoid (Real.log (1 / 4) + Real.log 2) 0)
        (logitTriangle.surface Real.sigmoid (Real.log (1 / 4) + Real.log 2) 1) =
        Real.log (209 / 117) ∧
      Real.log (209 / 117) ≠ Real.log (39 / 22) := by
  have hI : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hlog : ∀ u v : ℝ, 0 < u → 0 < v → u ≠ v → Real.log u ≠ Real.log v :=
    fun u v hu hv h e => h (Real.log_injOn_pos hu hv e)
  have := isProbabilityMeasure_binaryLaw hI
  exact ⟨logitTriangle_marginal, (logitTriangle_linkConditional _).2 _
      fun _ => integrable_binaryLaw _ _,
    hlog _ _ (by norm_num) (by norm_num) (by norm_num), (logitTriangle_marginal_dirac 0).1,
    (logitTriangle_marginal_dirac _).2, logitTriangle_marginal_shift,
    hlog _ _ (by norm_num) (by norm_num) (by norm_num)⟩

end NetworkMetaRegression

end CausalInference
