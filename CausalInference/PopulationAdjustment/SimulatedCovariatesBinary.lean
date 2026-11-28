/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.SimulatedCovariatesConstruction
public import CausalInference.Measures.LinkScale

/-!
# Simulated binary covariates: the product moment

For two binary covariates the standardized mean of an outcome surface with an interaction
depends on the covariate law through the margins and the product moment `E[X₀X₁]`. Under the
normal to anything construction with fair coin margins the simulated covariates are the signs of
a Gaussian pair, so the simulated product moment is a bivariate normal orthant probability
(`integral_mul_nortaLaw_fairCoin`). Matching the correlation of the Gaussian vector to the
reported (Pearson) correlation of the covariates does not reproduce the product moment.

**The numbers.** Two fair coins with Pearson correlation `1/2` have `P(X₀ = X₁ = 1) = 3/8`
(the law `dependentCoinLaw`). Simulating them with Gaussian correlation `1/2` gives
`P(X₀ = X₁ = 1) = 1/3` (`bivariateNormal_half_orthant`) and Pearson correlation `1/3`
(`dependentCoin_vs_simulated`).

## Main definitions

* `coinCode`, `dependentCoinWeight`, `dependentCoinLaw`: two fair coins with Pearson
  correlation `1/2`.
* `binaryInteraction f`: `f(1,1) - f(1,0) - f(0,1) + f(0,0)`.

## Main results

* `integral_mul_nortaLaw_fairCoin`: the simulated product moment is the orthant probability
  `P(Z_j > 0, Z_k > 0)` of the bivariate normal law with correlation `R_{jk}`.
* `integral_binary_expand`: for any law concentrated on `{0, 1}²` the integral of a surface is
  `f(0,0) + (f(1,0) - f(0,0)) E X₀ + (f(0,1) - f(0,0)) E X₁ + I(f) E[X₀X₁]`.
* `map_eval_dependentCoinLaw`, `integral_mul_dependentCoinLaw`,
  `covariance_dependentCoinLaw`, `variance_dependentCoinLaw`: the target law.
* `integral_mul_nortaLaw_half`, `covariance_nortaLaw_half`: the simulated law with Gaussian
  correlation `1/2`.
* `dependentCoin_vs_simulated`: same margins, same reported correlation of the Gaussian
  vector and the covariates, different product moments `3/8` and `1/3`.
* `binaryInteraction_logistic_ne_zero`: the logistic surface `σ(x₀ + x₁)` has a nonzero
  interaction `(e⁻¹ - 1)³ / (2 (1 + e⁻¹)(1 + e⁻²))`.

## References

* M. C. Cario and B. L. Nelson (1997), *Modeling and generating random vectors with arbitrary
  marginal distributions and correlation matrix*, Northwestern University.
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open MeasureTheory ProbabilityTheory Set BiasAnalysis.Distributions EffectMeasure

/-! ### The simulated product moment -/

section Simulated

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Matrix ι ι ℝ}

/-- **The simulated product moment of two fair coins is an orthant probability.** With fair coin
margins, `E[X_j X_k] = P(Z₀ > 0, Z₁ > 0)` for `Z` standard bivariate normal with correlation
`R_{jk}`. -/
theorem integral_mul_nortaLaw_fairCoin (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1) (j k : ι) :
    ∫ x, x j * x k ∂nortaLaw R (fun _ => fairCoin) =
      (bivariateNormal (R j k)).real {z | 0 < z 0 ∧ 0 < z 1} := by
  have h := map_pair_nortaLaw (μ := fun _ => fairCoin) hR hdiag (j := j) (k := k)
  have e1 : ∫ x, x j * x k ∂nortaLaw R (fun _ => fairCoin) =
      ∫ p, p.1 * p.2 ∂((nortaLaw R (fun _ => fairCoin)).map fun x => (x j, x k)) := by
    rw [integral_map (by fun_prop) (by fun_prop)]
  have hq : Measurable fun z : EuclideanSpace ℝ (Fin 2) =>
      (quantile fairCoin (cdf (gaussianReal 0 1) (z 0)),
        quantile fairCoin (cdf (gaussianReal 0 1) (z 1))) :=
    ((measurable_quantile _).comp ((cdf _).mono.measurable.comp (by fun_prop))).prodMk
      ((measurable_quantile _).comp ((cdf _).mono.measurable.comp (by fun_prop)))
  have hS : MeasurableSet {z : EuclideanSpace ℝ (Fin 2) | 0 < z 0 ∧ 0 < z 1} := by
    have h0 := measurableSet_lt (f := fun _ : EuclideanSpace ℝ (Fin 2) => (0 : ℝ))
      measurable_const (show Measurable fun z : EuclideanSpace ℝ (Fin 2) => z 0 by fun_prop)
    have h1 := measurableSet_lt (f := fun _ : EuclideanSpace ℝ (Fin 2) => (0 : ℝ))
      measurable_const (show Measurable fun z : EuclideanSpace ℝ (Fin 2) => z 1 by fun_prop)
    exact h0.inter h1
  rw [e1, h, integral_map hq.aemeasurable (by fun_prop), ← integral_indicator_one hS]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only [quantile_fairCoin_cdf_stdNormal, indicator_apply, mem_Ioi, mem_ofPred_eq,
    Pi.one_apply]
  split_ifs <;> simp_all

end Simulated

/-! ### Laws on `{0, 1}²` -/

/-- The interaction contrast `f(1,1) - f(1,0) - f(0,1) + f(0,0)` of a surface on `{0, 1}²`. -/
noncomputable def binaryInteraction (f : (Fin 2 → ℝ) → ℝ) : ℝ :=
  f ![1, 1] - f ![1, 0] - f ![0, 1] + f ![0, 0]

/-- On `{0, 1}²` a surface is `f(0,0) + (f(1,0) - f(0,0)) x₀ + (f(0,1) - f(0,0)) x₁ + I x₀ x₁`. -/
theorem binary_expand (f : (Fin 2 → ℝ) → ℝ) {x : Fin 2 → ℝ} (h0 : x 0 = 0 ∨ x 0 = 1)
    (h1 : x 1 = 0 ∨ x 1 = 1) :
    f x = f ![0, 0] + (f ![1, 0] - f ![0, 0]) * x 0 + (f ![0, 1] - f ![0, 0]) * x 1 +
      binaryInteraction f * (x 0 * x 1) := by
  have hx : x = ![x 0, x 1] := by ext i; fin_cases i <;> rfl
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
    · rw [hx, h0, h1, binaryInteraction]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      ring

/-- **Integrals over a law concentrated on `{0, 1}²`.** For a probability law `κ` with both
coordinates in `{0, 1}` almost surely, every surface `f` is integrable and
`∫ f dκ = f(0,0) + (f(1,0) - f(0,0)) E X₀ + (f(0,1) - f(0,0)) E X₁ + I(f) E[X₀X₁]`. -/
theorem integral_binary_expand {κ : Measure (Fin 2 → ℝ)} [IsProbabilityMeasure κ]
    (hκ : ∀ᵐ x ∂κ, (x 0 = 0 ∨ x 0 = 1) ∧ (x 1 = 0 ∨ x 1 = 1)) (f : (Fin 2 → ℝ) → ℝ) :
    Integrable f κ ∧ ∫ x, f x ∂κ = f ![0, 0] + (f ![1, 0] - f ![0, 0]) * ∫ x, x 0 ∂κ +
      (f ![0, 1] - f ![0, 0]) * ∫ x, x 1 ∂κ + binaryInteraction f * ∫ x, x 0 * x 1 ∂κ := by
  have hb : ∀ i : Fin 2, Integrable (fun x : Fin 2 → ℝ => x i) κ := fun i =>
    Integrable.of_bound (measurable_pi_apply i).aestronglyMeasurable 1 (hκ.mono fun x hx => by
      fin_cases i <;> rcases hx with ⟨h0 | h0, h1 | h1⟩ <;> simp [h0, h1])
  have hp : Integrable (fun x : Fin 2 → ℝ => x 0 * x 1) κ :=
    Integrable.of_bound ((measurable_pi_apply 0).mul (measurable_pi_apply 1)).aestronglyMeasurable
      1 (hκ.mono fun x hx => by
      rcases hx with ⟨h0 | h0, h1 | h1⟩ <;> simp [h0, h1])
  set g : (Fin 2 → ℝ) → ℝ := fun x => f ![0, 0] + (f ![1, 0] - f ![0, 0]) * x 0 +
    (f ![0, 1] - f ![0, 0]) * x 1 + binaryInteraction f * (x 0 * x 1)
  have hfg : f =ᵐ[κ] g := hκ.mono fun x hx => binary_expand f hx.1 hx.2
  have hg : Integrable g κ :=
    (((integrable_const _).add ((hb 0).const_mul _)).add ((hb 1).const_mul _)).add
      (hp.const_mul _)
  refine ⟨hg.congr hfg.symm, ?_⟩
  rw [integral_congr_ae hfg]
  simp only [g]
  rw [integral_add ?_ ?_, integral_add ?_ ?_, integral_add ?_ ?_, integral_const,
    integral_const_mul, integral_const_mul, integral_const_mul]
  · simp
  all_goals first
    | exact integrable_const _
    | exact (hb 0).const_mul _
    | exact (hb 1).const_mul _
    | exact hp.const_mul _
    | exact (integrable_const _).add ((hb 0).const_mul _)
    | exact ((integrable_const _).add ((hb 0).const_mul _)).add ((hb 1).const_mul _)

/-- The simulated fair coin law is concentrated on `{0, 1}^ι`. -/
theorem ae_nortaLaw_fairCoin_binary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Matrix ι ι ℝ) (j : ι) :
    ∀ᵐ x ∂nortaLaw R (fun _ => fairCoin), x j = 0 ∨ x j = 1 := by
  have hS : MeasurableSet {x : ι → ℝ | x j = 0 ∨ x j = 1} :=
    (measurableSet_eq_fun (measurable_pi_apply j) measurable_const).union
      (measurableSet_eq_fun (measurable_pi_apply j) measurable_const)
  rw [nortaLaw, ae_map_iff (measurable_nortaMap _).aemeasurable hS]
  refine ae_of_all _ fun z => ?_
  simp only [nortaMap_fairCoin, indicator_apply, mem_Ioi, Pi.one_apply]
  split_ifs <;> simp

/-! ### Two fair coins with Pearson correlation `1/2` -/

/-- The code `(b₀, b₁) ↦ (1[b₀], 1[b₁])` of a pair of binary covariates. -/
noncomputable def coinCode (b : Bool × Bool) : Fin 2 → ℝ :=
  ![if b.1 then 1 else 0, if b.2 then 1 else 0]

/-- The weights `P(1,1) = P(0,0) = 3/8`, `P(1,0) = P(0,1) = 1/8`. -/
noncomputable def dependentCoinWeight (b : Bool × Bool) : ℝ := if b.1 = b.2 then 3 / 8 else 1 / 8

/-- **Two fair coins with Pearson correlation `1/2`**: the law of `coinCode` under
`dependentCoinWeight`. -/
noncomputable def dependentCoinLaw : Measure (Fin 2 → ℝ) :=
  (stratumLaw dependentCoinWeight).map coinCode

theorem measurable_coinCode : Measurable coinCode := measurable_of_finite _

theorem dependentCoinWeight_nonneg (b : Bool × Bool) : 0 ≤ dependentCoinWeight b := by
  unfold dependentCoinWeight; split_ifs <;> norm_num

instance : IsProbabilityMeasure (stratumLaw dependentCoinWeight) :=
  isProbabilityMeasure_stratumLaw ⟨dependentCoinWeight_nonneg, by
    simp [Fintype.sum_prod_type, dependentCoinWeight]; norm_num⟩

instance : IsProbabilityMeasure dependentCoinLaw :=
  (Measure.isProbabilityMeasure_map_iff measurable_coinCode.aemeasurable).2 inferInstance

/-- Integrals against `dependentCoinLaw` are weighted sums over the four points. -/
theorem integral_dependentCoinLaw {f : (Fin 2 → ℝ) → ℝ} (hf : Measurable f) :
    ∫ x, f x ∂dependentCoinLaw =
      3 / 8 * f ![1, 1] + 1 / 8 * f ![1, 0] + 1 / 8 * f ![0, 1] + 3 / 8 * f ![0, 0] := by
  rw [dependentCoinLaw, integral_map measurable_coinCode.aemeasurable hf.aestronglyMeasurable,
    integral_stratumLaw dependentCoinWeight_nonneg, standardizedRisk]
  simp [Fintype.sum_prod_type, dependentCoinWeight, coinCode]
  ring

/-- **The margins of `dependentCoinLaw` are fair coins.** -/
theorem map_eval_dependentCoinLaw (j : Fin 2) : dependentCoinLaw.map (fun x => x j) = fairCoin := by
  have : IsProbabilityMeasure (dependentCoinLaw.map fun x => x j) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_pi_apply j).aemeasurable).2 inferInstance
  refine Measure.eq_of_cdf _ _ (StieltjesFunction.ext fun t => ?_)
  rw [cdf_eq_real, cdf_fairCoin, map_measureReal_apply (measurable_pi_apply j) measurableSet_Iic,
    ← integral_indicator_one ((measurable_pi_apply j) measurableSet_Iic),
    integral_dependentCoinLaw ((measurable_one.indicator
      ((measurable_pi_apply j) measurableSet_Iic)))]
  have key : ∀ i : Fin 2, ∀ v : Fin 2 → ℝ, ((fun f : Fin 2 → ℝ => f i) ⁻¹' Iic t).indicator 1 v =
      if v i ≤ t then (1 : ℝ) else 0 := fun i v => by
    simp only [Set.indicator, Set.mem_preimage, Set.mem_Iic, Pi.one_apply]
  fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, key, Matrix.cons_val_zero,
    Matrix.cons_val_one] <;> by_cases h0 : (0 : ℝ) ≤ t <;> by_cases h1 : (1 : ℝ) ≤ t <;>
    simp only [h0, h1, ite_true, ite_false] <;> first | (exfalso; linarith) | norm_num

theorem ae_dependentCoinLaw_binary :
    ∀ᵐ x ∂dependentCoinLaw, (x 0 = 0 ∨ x 0 = 1) ∧ (x 1 = 0 ∨ x 1 = 1) := by
  have hS : MeasurableSet {x : Fin 2 → ℝ | (x 0 = 0 ∨ x 0 = 1) ∧ (x 1 = 0 ∨ x 1 = 1)} := by
    have h : ∀ i : Fin 2, MeasurableSet {x : Fin 2 → ℝ | x i = 0 ∨ x i = 1} := fun i =>
      (measurableSet_eq_fun (measurable_pi_apply i) measurable_const).union
        (measurableSet_eq_fun (measurable_pi_apply i) measurable_const)
    exact (h 0).inter (h 1)
  rw [dependentCoinLaw, ae_map_iff measurable_coinCode.aemeasurable hS]
  refine ae_of_all _ fun b => ?_
  rcases b with ⟨_ | _, _ | _⟩ <;> simp [coinCode]

theorem integral_eval_dependentCoinLaw (j : Fin 2) : ∫ x, x j ∂dependentCoinLaw = 1 / 2 := by
  rw [integral_dependentCoinLaw (measurable_pi_apply j)]
  fin_cases j <;> simp <;> norm_num

/-- **The product moment of the target**: `E[X₀X₁] = P(X₀ = X₁ = 1) = 3/8`. -/
theorem integral_mul_dependentCoinLaw : ∫ x, x 0 * x 1 ∂dependentCoinLaw = 3 / 8 := by
  rw [integral_dependentCoinLaw (by fun_prop)]
  simp

/-- The covariance of the target coins is `3/8 - 1/4 = 1/8`. -/
theorem covariance_dependentCoinLaw :
    cov[fun x => x 0, fun x => x 1; dependentCoinLaw] = 1 / 8 := by
  rw [covariance, integral_eval_dependentCoinLaw 0, integral_eval_dependentCoinLaw 1,
    integral_dependentCoinLaw (by fun_prop)]
  simp
  norm_num

/-- Each target coin has variance `1/4`. -/
theorem variance_dependentCoinLaw (j : Fin 2) :
    Var[fun x => x j; dependentCoinLaw] = 1 / 4 := by
  rw [variance_eq_integral (measurable_pi_apply j).aemeasurable, integral_eval_dependentCoinLaw j,
    integral_dependentCoinLaw (by fun_prop)]
  fin_cases j <;> simp <;> norm_num

/-- **The target coins have Pearson correlation `1/2`.** -/
theorem correlation_dependentCoinLaw :
    cov[fun x => x 0, fun x => x 1; dependentCoinLaw] /
      (√Var[fun x => x 0; dependentCoinLaw] * √Var[fun x => x 1; dependentCoinLaw]) = 1 / 2 := by
  rw [covariance_dependentCoinLaw, variance_dependentCoinLaw, variance_dependentCoinLaw,
    show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

/-! ### The simulated coins with Gaussian correlation `1/2` -/

theorem corrMatrix_diag (ρ : ℝ) (i : Fin 2) : corrMatrix ρ i i = 1 := by
  fin_cases i <;> rfl

/-- The simulated fair coins with Gaussian correlation `1/2` have product moment `1/3`. -/
theorem integral_mul_nortaLaw_half :
    ∫ x, x 0 * x 1 ∂nortaLaw (corrMatrix (1 / 2)) (fun _ => fairCoin) = 1 / 3 := by
  rw [integral_mul_nortaLaw_fairCoin (corrMatrix_posSemidef (by norm_num)) (corrMatrix_diag _)]
  exact bivariateNormal_half_orthant

theorem integral_eval_nortaLaw_fairCoin {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Matrix ι ι ℝ} (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1) (j : ι) :
    ∫ x, x j ∂nortaLaw R (fun _ => fairCoin) = 1 / 2 := by
  rw [show ∫ x, x j ∂nortaLaw R (fun _ => fairCoin) = ∫ t, t ∂fairCoin from
    integral_nortaLaw_eval (f := fun t => t) hR hdiag j aestronglyMeasurable_id]
  rw [fairCoin, integral_smul_measure, integral_add_measure (integrable_dirac (by simp))
    (integrable_dirac (by simp)), integral_dirac, integral_dirac]
  norm_num

/-- The simulated coins with Gaussian correlation `1/2` have covariance `1/3 - 1/4 = 1/12`. -/
theorem covariance_nortaLaw_half :
    cov[fun x => x 0, fun x => x 1; nortaLaw (corrMatrix (1 / 2)) (fun _ => fairCoin)] =
      1 / 12 := by
  have hR := corrMatrix_posSemidef (ρ := 1 / 2) (by norm_num)
  obtain ⟨-, h⟩ := integral_binary_expand
    (Filter.eventually_and.2 ⟨ae_nortaLaw_fairCoin_binary _ 0, ae_nortaLaw_fairCoin_binary _ 1⟩)
    (fun x => (x 0 - 1 / 2) * (x 1 - 1 / 2))
  rw [covariance, integral_eval_nortaLaw_fairCoin hR (corrMatrix_diag _),
    integral_eval_nortaLaw_fairCoin hR (corrMatrix_diag _), h,
    integral_eval_nortaLaw_fairCoin hR (corrMatrix_diag _),
    integral_eval_nortaLaw_fairCoin hR (corrMatrix_diag _), integral_mul_nortaLaw_half,
    binaryInteraction]
  simp
  norm_num

/-- **Matching the Gaussian correlation to the reported correlation gives the wrong product
moment.** The target `dependentCoinLaw` and the simulated law with Gaussian correlation `1/2`
have the same fair coin margins, the target coins have Pearson correlation `1/2`, the Gaussian
vector has correlation `1/2`, and yet the product moments are `3/8` and `1/3`; the simulated
coins have covariance `1/12`, Pearson correlation `1/3`. -/
theorem dependentCoin_vs_simulated :
    (∀ j, dependentCoinLaw.map (fun x => x j) = fairCoin) ∧
      (∀ j, (nortaLaw (corrMatrix (1 / 2)) (fun _ => fairCoin)).map (fun x => x j) =
        fairCoin) ∧
      cov[fun x => x 0, fun x => x 1; dependentCoinLaw] /
        (√Var[fun x => x 0; dependentCoinLaw] * √Var[fun x => x 1; dependentCoinLaw]) = 1 / 2 ∧
      cov[fun x : EuclideanSpace ℝ (Fin 2) => x 0, fun x => x 1; bivariateNormal (1 / 2)] =
        1 / 2 ∧
      ∫ x, x 0 * x 1 ∂dependentCoinLaw = 3 / 8 ∧
      ∫ x, x 0 * x 1 ∂nortaLaw (corrMatrix (1 / 2)) (fun _ => fairCoin) = 1 / 3 ∧
      cov[fun x => x 0, fun x => x 1; nortaLaw (corrMatrix (1 / 2)) (fun _ => fairCoin)] =
        1 / 12 :=
  ⟨map_eval_dependentCoinLaw, map_eval_nortaLaw (corrMatrix_posSemidef (by norm_num))
    (corrMatrix_diag _), correlation_dependentCoinLaw,
    covariance_bivariateNormal (by norm_num), integral_mul_dependentCoinLaw,
    integral_mul_nortaLaw_half, covariance_nortaLaw_half⟩

/-! ### A logistic surface with an interaction -/

/-- **The logistic surface `σ(x₀ + x₁)` has a nonzero interaction**: with `u = e⁻¹`,
`σ(2) - 2σ(1) + σ(0) = (u - 1)³ / (2 (1 + u)(1 + u²)) < 0`. -/
theorem binaryInteraction_logistic :
    binaryInteraction (fun x => Real.sigmoid (x 0 + x 1)) =
      (Real.exp (-1) - 1) ^ 3 / (2 * (1 + Real.exp (-1)) * (1 + Real.exp (-1) ^ 2)) := by
  have hu := Real.exp_pos (-1)
  have h2 : Real.exp (-2) = Real.exp (-1) ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  simp only [binaryInteraction, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num [Real.sigmoid_def, h2]
  field_simp
  ring

theorem binaryInteraction_logistic_ne_zero :
    binaryInteraction (fun x => Real.sigmoid (x 0 + x 1)) ≠ 0 := by
  rw [binaryInteraction_logistic]
  have hu := Real.exp_pos (-1)
  have hu1 : Real.exp (-1) < 1 := Real.exp_lt_one_iff.2 (by norm_num)
  refine div_ne_zero (pow_ne_zero _ (by linarith)) (by positivity)

end PopulationAdjustment

end CausalInference
