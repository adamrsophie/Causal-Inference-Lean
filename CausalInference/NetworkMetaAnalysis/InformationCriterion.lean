/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaAnalysis.GaussMarkov
public import CausalInference.Estimation.ChiSquared

/-!
# The deviance information criterion

For a posterior `π` on the parameter space `ℝ^ι` and a deviance `D`, the posterior mean deviance
is `D̄ = E_π D`, the effective number of parameters is `p_D = D̄ - D(θ̄)` with `θ̄` the posterior
mean, and the deviance information criterion is `DIC = D̄ + p_D`
(Spiegelhalter, Best, Carlin and van der Linde 2002).

* `devianceInformationCriterion_eq`: `DIC = D(θ̄) + 2 p_D = 2 D̄ - D(θ̄)`.
* **A quadratic deviance** (`effectiveParameters_eq_trace`): if `D(θ) = (θ - θ̂)ᵀ I (θ - θ̂) + c`
  almost surely under `π`, then `p_D = tr(I Σ_π)`, with `Σ_π` the posterior covariance matrix.
  No positive definiteness of `I` is needed; the posterior needs second moments.
* **The normal linear model** (`effectiveParameters_glsObjective`): with the deviance
  `D(β) = (y - X β)ᵀ V⁻¹ (y - X β) + c` (minus twice the Gaussian log likelihood with known `V`),
  `p_D = tr(Xᵀ V⁻¹ X Σ_π)` for every posterior with second moments.
* **The flat prior** (`effectiveParameters_multivariateGaussian`,
  `effectiveParameters_glsObjective_flat`): if the posterior is `N(β̂, (Xᵀ V⁻¹ X)⁻¹)`, then
  `p_D = p`, the number of parameters. Under a flat prior on `ℝ^p` this Gaussian is the posterior
  of the normal linear model with known `V`; here the Gaussian form of the posterior is the
  hypothesis, not derived from Bayes' theorem.

## Main definitions

* `posteriorMeanDeviance`, `posteriorMean`, `effectiveParameters`,
  `devianceInformationCriterion`.

## Main results

* `devianceInformationCriterion_eq`, `integral_sub_mul_sub_eq`, `effectiveParameters_eq_trace`,
  `effectiveParameters_glsObjective`, `effectiveParameters_multivariateGaussian`,
  `effectiveParameters_glsObjective_flat`.

## References

* D. J. Spiegelhalter, N. G. Best, B. P. Carlin and A. van der Linde, *Bayesian measures of
  model complexity and fit*, Journal of the Royal Statistical Society B 64 (2002).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaAnalysis

open Matrix MeasureTheory ProbabilityTheory

variable {ι : Type*} [Fintype ι]

/-- The **posterior mean deviance** `D̄ = E_π D`. -/
noncomputable def posteriorMeanDeviance (π : Measure (EuclideanSpace ℝ ι))
    (D : EuclideanSpace ℝ ι → ℝ) : ℝ :=
  ∫ θ, D θ ∂π

/-- The **posterior mean** `θ̄`, coordinatewise. -/
noncomputable def posteriorMean (π : Measure (EuclideanSpace ℝ ι)) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 fun i => ∫ θ, θ i ∂π

/-- The **effective number of parameters** `p_D = D̄ - D(θ̄)`. -/
noncomputable def effectiveParameters (π : Measure (EuclideanSpace ℝ ι))
    (D : EuclideanSpace ℝ ι → ℝ) : ℝ :=
  posteriorMeanDeviance π D - D (posteriorMean π)

/-- The **deviance information criterion** `DIC = D̄ + p_D`. -/
noncomputable def devianceInformationCriterion (π : Measure (EuclideanSpace ℝ ι))
    (D : EuclideanSpace ℝ ι → ℝ) : ℝ :=
  posteriorMeanDeviance π D + effectiveParameters π D

omit [Fintype ι] in
/-- `DIC = D(θ̄) + 2 p_D = 2 D̄ - D(θ̄)`. -/
theorem devianceInformationCriterion_eq (π : Measure (EuclideanSpace ℝ ι))
    (D : EuclideanSpace ℝ ι → ℝ) :
    devianceInformationCriterion π D = D (posteriorMean π) + 2 * effectiveParameters π D ∧
      devianceInformationCriterion π D = 2 * posteriorMeanDeviance π D - D (posteriorMean π) := by
  simp only [devianceInformationCriterion, effectiveParameters]
  constructor <;> ring

/-- `E[(X - a)(Y - b)] = cov[X, Y] + (E X - a)(E Y - b)`. -/
theorem integral_sub_mul_sub_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X Y : Ω → ℝ} (hX : MemLp X 2 P) (hY : MemLp Y 2 P) (a b : ℝ) :
    ∫ ω, (X ω - a) * (Y ω - b) ∂P = cov[X, Y; P] + ((∫ ω, X ω ∂P) - a) * ((∫ ω, Y ω ∂P) - b) := by
  have hXY : Integrable (fun ω => X ω * Y ω) P := hX.integrable_mul hY
  have iX := hX.integrable one_le_two
  have iY := hY.integrable one_le_two
  have e : ∀ ω, (X ω - a) * (Y ω - b) = X ω * Y ω - b * X ω - a * Y ω + a * b := fun ω => by ring
  simp_rw [e]
  have i1 : Integrable (fun ω => X ω * Y ω - b * X ω) P := hXY.sub (iX.const_mul b)
  have i2 : Integrable (fun ω => X ω * Y ω - b * X ω - a * Y ω) P := i1.sub (iY.const_mul a)
  rw [integral_add i2 (integrable_const _), integral_sub i1 (iY.const_mul a),
    integral_sub hXY (iX.const_mul b),
    integral_const_mul, integral_const_mul, integral_const, covariance_eq_sub hX hY]
  simp only [probReal_univ, smul_eq_mul, one_mul, Pi.mul_apply]
  ring

/-- **The effective number of parameters of a quadratic deviance is a trace.** If
`D(θ) = (θ - θ̂)ᵀ I (θ - θ̂) + c` almost surely under a posterior `π` with second moments, and also
at the posterior mean, then `p_D = tr(I Σ_π)` with `Σ_π` the posterior covariance matrix. -/
theorem effectiveParameters_eq_trace {π : Measure (EuclideanSpace ℝ ι)}
    [IsProbabilityMeasure π] (h2 : ∀ i, MemLp (fun θ : EuclideanSpace ℝ ι => θ i) 2 π)
    (I : Matrix ι ι ℝ) (θhat : EuclideanSpace ℝ ι) (c : ℝ) {D : EuclideanSpace ℝ ι → ℝ}
    (hD : ∀ᵐ θ ∂π, D θ = quadForm I (θ - θhat) + c)
    (hDbar : D (posteriorMean π) = quadForm I (posteriorMean π - θhat) + c) :
    effectiveParameters π D =
      (I * Matrix.of fun i j => cov[fun θ => θ i, fun θ => θ j; π]).trace := by
  classical
  have hexp : ∀ v : EuclideanSpace ℝ ι,
      quadForm I (v - θhat) = ∑ i, ∑ j, I i j * ((v i - θhat i) * (v j - θhat j)) := by
    intro v
    simp only [quadForm, dotProduct, mulVec, Finset.mul_sum, WithLp.ofLp_sub, Pi.sub_apply]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hpi : ∀ i j, Integrable
      (fun θ : EuclideanSpace ℝ ι => (θ i - θhat i) * (θ j - θhat j)) π := fun i j =>
    ((h2 i).sub (memLp_const (θhat i))).integrable_mul ((h2 j).sub (memLp_const (θhat j)))
  have hQint : Integrable (fun θ : EuclideanSpace ℝ ι => quadForm I (θ - θhat)) π := by
    simp_rw [hexp]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hpi i j).const_mul (I i j)
  have hQ : ∫ θ, quadForm I (θ - θhat) ∂π = ∑ i, ∑ j, I i j *
      (cov[fun θ => θ i, fun θ => θ j; π] +
        ((∫ θ, θ i ∂π) - θhat i) * ((∫ θ, θ j ∂π) - θhat j)) := by
    simp_rw [hexp]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hpi i j).const_mul (I i j)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => (hpi i j).const_mul (I i j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, integral_sub_mul_sub_eq (h2 i) (h2 j)]
  have htr : (I * Matrix.of fun i j => cov[fun θ => θ i, fun θ => θ j; π]).trace =
      ∑ i, ∑ j, I i j * cov[fun θ => θ i, fun θ => θ j; π] := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [covariance_comm]
  rw [effectiveParameters, posteriorMeanDeviance, integral_congr_ae hD,
    integral_add hQint (integrable_const c), hQ, hDbar, hexp, htr]
  simp only [posteriorMean, PiLp.toLp_apply, integral_const, probReal_univ, smul_eq_mul, one_mul,
    mul_add, Finset.sum_add_distrib]
  ring

/-- **Under a Gaussian posterior with covariance `I⁻¹`, `p_D` is the number of parameters.** If
the posterior is `N(θ̂, I⁻¹)` with `I` positive definite and the deviance is
`(θ - θ̂)ᵀ I (θ - θ̂) + c`, then `p_D = tr(I I⁻¹) = card ι`. -/
theorem effectiveParameters_multivariateGaussian [DecidableEq ι] {I : Matrix ι ι ℝ}
    (hI : I.PosDef) (θhat : EuclideanSpace ℝ ι) (c : ℝ) {D : EuclideanSpace ℝ ι → ℝ}
    (hD : ∀ θ, D θ = quadForm I (θ - θhat) + c) :
    effectiveParameters (multivariateGaussian θhat I⁻¹) D = Fintype.card ι := by
  have hS : I⁻¹.PosSemidef := hI.inv.posSemidef
  have hm : ∀ i, MemLp (fun x : EuclideanSpace ℝ ι => x i) 2 (multivariateGaussian θhat I⁻¹) :=
    fun i => (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => ℝ) i).comp_memLp'
      (IsGaussian.memLp_two_id (μ := multivariateGaussian θhat I⁻¹))
  rw [effectiveParameters_eq_trace hm I θhat c (Filter.Eventually.of_forall hD) (hD _)]
  have hcov : (Matrix.of fun i j => cov[fun θ : EuclideanSpace ℝ ι => θ i, fun θ => θ j;
      multivariateGaussian θhat I⁻¹]) = I⁻¹ :=
    Matrix.ext fun i j => by rw [Matrix.of_apply, covariance_eval_multivariateGaussian hS]
  rw [hcov, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hI.isUnit), trace_one]

/-! ### The normal linear model -/

section Linear

variable {n : Type*} [Fintype n] [DecidableEq n] [DecidableEq ι]

/-- The generalized least squares objective is quadratic around the estimate, in the form of the
`quadForm`. -/
theorem glsObjective_eq_quadForm {X : Matrix n ι ℝ} {V : Matrix n n ℝ} (hV : V.PosDef)
    (hX : Function.Injective X.mulVec) (y : n → ℝ) (θ : EuclideanSpace ℝ ι) :
    glsObjective X V y (WithLp.ofLp θ) =
      quadForm (Xᵀ * V⁻¹ * X) (θ - WithLp.toLp 2 (glsEstimate X V y)) +
        glsObjective X V y (glsEstimate X V y) := by
  rw [glsObjective_eq_add hV hX, quadForm, add_comm]
  rfl

omit [DecidableEq ι] in
/-- **The effective number of parameters in the normal linear model.** With the deviance
`D(β) = (y - X β)ᵀ V⁻¹ (y - X β) + c` and any posterior with second moments,
`p_D = tr(Xᵀ V⁻¹ X Σ_π)`. -/
theorem effectiveParameters_glsObjective {X : Matrix n ι ℝ} {V : Matrix n n ℝ} (hV : V.PosDef)
    (hX : Function.Injective X.mulVec) (y : n → ℝ) (c : ℝ) {π : Measure (EuclideanSpace ℝ ι)}
    [IsProbabilityMeasure π] (h2 : ∀ i, MemLp (fun θ : EuclideanSpace ℝ ι => θ i) 2 π) :
    effectiveParameters π (fun θ => glsObjective X V y (WithLp.ofLp θ) + c) =
      ((Xᵀ * V⁻¹ * X) * Matrix.of fun i j => cov[fun θ => θ i, fun θ => θ j; π]).trace := by
  classical
  refine effectiveParameters_eq_trace h2 _ (WithLp.toLp 2 (glsEstimate X V y))
    (glsObjective X V y (glsEstimate X V y) + c) (Filter.Eventually.of_forall fun θ => ?_) ?_
  · rw [glsObjective_eq_quadForm hV hX]
    ring
  · rw [glsObjective_eq_quadForm hV hX]
    ring

/-- **The flat prior: `p_D = p`.** In the normal linear model with known positive definite `V`
and full column rank `X`, if the posterior is the Gaussian `N(β̂, (Xᵀ V⁻¹ X)⁻¹)` (the posterior
under a flat prior, taken here as the hypothesis on `π`), then the effective number of
parameters is the number `p` of columns of `X`. -/
theorem effectiveParameters_glsObjective_flat {X : Matrix n ι ℝ} {V : Matrix n n ℝ}
    (hV : V.PosDef) (hX : Function.Injective X.mulVec) (y : n → ℝ) (c : ℝ) :
    effectiveParameters
        (multivariateGaussian (WithLp.toLp 2 (glsEstimate X V y)) (Xᵀ * V⁻¹ * X)⁻¹)
        (fun θ => glsObjective X V y (WithLp.ofLp θ) + c) = Fintype.card ι := by
  refine effectiveParameters_multivariateGaussian ((posDef_transpose_mul_mul_iff hV.inv).2 hX)
    _ (glsObjective X V y (glsEstimate X V y) + c) fun θ => ?_
  rw [glsObjective_eq_quadForm hV hX]
  ring

end Linear

end NetworkMetaAnalysis

end CausalInference
