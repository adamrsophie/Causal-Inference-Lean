/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.SimulatedCovariatesBinary
public import CausalInference.BiasAnalysis.IndirectComparisonArcsine

/-!
# Simulated binary covariates at every correlation; attenuation

The standard bivariate normal law with correlation `ρ` is the law of `(V, ρV + √(1 - ρ²)W)` for
independent standard normals `V, W` (`bivariateNormal_eq_map`). With the orthant probability of
that pair, `1/4 + arcsin(ρ)/(2π)`, the simulated fair coins `X_j = 1{Z_j > 0}`, `Z ∼ N(0, R)`,
have

* product moment `E[X_j X_k] = 1/4 + arcsin(R_{jk})/(2π)` (`integral_mul_nortaLaw_fairCoin_eq`);
* variance `1/4` and Pearson correlation `(2/π) arcsin(R_{jk})`
  (`correlation_nortaLaw_fairCoin`);
* **attenuation**: `|(2/π) arcsin(R_{jk})| ≤ |R_{jk}|` (`abs_correlation_nortaLaw_fairCoin_le`);
  at `R_{jk} = 1/2` the simulated correlation is `1/3` (`correlation_nortaLaw_half`).

For a surface `f` of two binary covariates with nonzero interaction contrast `I(f)`, distinct
Gaussian correlations give distinct simulated standardized means
(`integral_nortaLaw_fairCoin_injOn`): the target of the simulated comparison is not determined
by the margins, and it changes with the correlation parameter chosen.

## Main results

* `bivariateNormal_eq_map`, `bivariateNormal_orthant`.
* `integral_mul_nortaLaw_fairCoin_eq`, `variance_nortaLaw_fairCoin`,
  `covariance_nortaLaw_fairCoin`, `correlation_nortaLaw_fairCoin`.
* `abs_two_div_pi_mul_arcsin_le`, `abs_correlation_nortaLaw_fairCoin_le`.
* `integral_nortaLaw_fairCoin_pair`, `integral_nortaLaw_fairCoin_injOn`.
* `correlation_nortaLaw_half`, `correlation_nortaLaw_half_lt`.
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open MeasureTheory ProbabilityTheory Set Complex BiasAnalysis.Distributions
  BiasAnalysis.IndirectComparisonBias
open scoped Real

/-! ### The bivariate normal law as a linear image of two independent normals -/

/-- The linear map `(v, w) ↦ (v, ρv + sw)`. -/
noncomputable def gaussPairMap (ρ s : ℝ) : ℝ × ℝ →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p => !₂[p.1, ρ * p.1 + s * p.2]
      map_add' := fun p q => by ext i; fin_cases i <;> simp; ring
      map_smul' := fun c p => by ext i; fin_cases i <;> simp; ring }

theorem gaussPairMap_apply (ρ s : ℝ) (p : ℝ × ℝ) :
    gaussPairMap ρ s p = !₂[p.1, ρ * p.1 + s * p.2] :=
  rfl

/-- **The standard bivariate normal law is the law of `(V, ρV + √(1 - ρ²)W)`** for independent
standard normals `V, W`. -/
theorem bivariateNormal_eq_map {ρ : ℝ} (hρ : ρ ^ 2 ≤ 1) :
    bivariateNormal ρ = stdNormalPair.map (gaussPairMap ρ √(1 - ρ ^ 2)) := by
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_bivariateNormal hρ, charFun_eq_charFunDual_toDualMap, charFunDual_map,
    charFunDual_stdNormalPair]
  simp only [ContinuousLinearMap.comp_apply, gaussPairMap_apply]
  have hs : √(1 - ρ ^ 2) ^ 2 = 1 - ρ ^ 2 := Real.sq_sqrt (by linarith)
  rw [← Complex.exp_add]
  congr 1
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]
  have hsC : ((√(1 - ρ ^ 2) : ℝ) : ℂ) ^ 2 = 1 - (ρ : ℂ) ^ 2 := by exact_mod_cast hs
  linear_combination ((t 1 : ℂ) ^ 2 / 2) * hsC

/-- **The orthant probability of the standard bivariate normal law**:
`P(Z₀ > 0, Z₁ > 0) = 1/4 + arcsin(ρ)/(2π)` for `ρ ∈ [-1, 1]`. -/
theorem bivariateNormal_orthant {ρ : ℝ} (hρ : ρ ∈ Icc (-1 : ℝ) 1) :
    (bivariateNormal ρ).real {z | 0 < z 0 ∧ 0 < z 1} = 1 / 4 + Real.arcsin ρ / (2 * π) := by
  have hρ2 : ρ ^ 2 ≤ 1 := by nlinarith [hρ.1, hρ.2]
  have hS : MeasurableSet {z : EuclideanSpace ℝ (Fin 2) | 0 < z 0 ∧ 0 < z 1} := by
    have h0 := measurableSet_lt (f := fun _ : EuclideanSpace ℝ (Fin 2) => (0 : ℝ))
      measurable_const (show Measurable fun z : EuclideanSpace ℝ (Fin 2) => z 0 by fun_prop)
    have h1 := measurableSet_lt (f := fun _ : EuclideanSpace ℝ (Fin 2) => (0 : ℝ))
      measurable_const (show Measurable fun z : EuclideanSpace ℝ (Fin 2) => z 1 by fun_prop)
    exact h0.inter h1
  rw [bivariateNormal_eq_map hρ2, map_measureReal_apply (gaussPairMap _ _).continuous.measurable hS,
    ← measureReal_orthant_pair hρ]
  rfl

/-! ### Simulated fair coins -/

section Coins

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Matrix ι ι ℝ}

omit [Fintype ι] [DecidableEq ι] in
theorem mem_Icc_of_posSemidef [Finite ι] (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1) (j k : ι) :
    R j k ∈ Icc (-1 : ℝ) 1 := by
  have h := sq_le_one_of_posSemidef hR hdiag j k
  constructor <;> nlinarith [sq_nonneg (R j k + 1), sq_nonneg (R j k - 1)]

/-- **The product moment of simulated fair coins**:
`E[X_j X_k] = 1/4 + arcsin(R_{jk})/(2π)`. -/
theorem integral_mul_nortaLaw_fairCoin_eq (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1)
    (j k : ι) :
    ∫ x, x j * x k ∂nortaLaw R (fun _ => fairCoin) = 1 / 4 + Real.arcsin (R j k) / (2 * π) := by
  rw [integral_mul_nortaLaw_fairCoin hR hdiag, bivariateNormal_orthant
    (mem_Icc_of_posSemidef hR hdiag j k)]

theorem memLp_eval_nortaLaw_fairCoin (R : Matrix ι ι ℝ) (j : ι) :
    MemLp (fun x : ι → ℝ => x j) 2 (nortaLaw R (fun _ => fairCoin)) :=
  MemLp.of_bound (measurable_pi_apply j).aestronglyMeasurable 1
    ((ae_nortaLaw_fairCoin_binary R j).mono fun x hx => by rcases hx with h | h <;> simp [h])

/-- Each simulated fair coin has variance `1/4`. -/
theorem variance_nortaLaw_fairCoin (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1) (j : ι) :
    Var[fun x => x j; nortaLaw R (fun _ => fairCoin)] = 1 / 4 := by
  rw [variance_eq_integral (measurable_pi_apply j).aemeasurable,
    integral_eval_nortaLaw_fairCoin hR hdiag j]
  rw [integral_congr_ae ((ae_nortaLaw_fairCoin_binary R j).mono fun x hx =>
    show (x j - 1 / 2) ^ 2 = (fun _ => (1 / 4 : ℝ)) x by rcases hx with h | h <;> simp [h] <;>
      norm_num)]
  simp

/-- The simulated fair coins have covariance `arcsin(R_{jk})/(2π)`. -/
theorem covariance_nortaLaw_fairCoin (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1) (j k : ι) :
    cov[fun x => x j, fun x => x k; nortaLaw R (fun _ => fairCoin)] =
      Real.arcsin (R j k) / (2 * π) := by
  rw [covariance_eq_sub (memLp_eval_nortaLaw_fairCoin R j) (memLp_eval_nortaLaw_fairCoin R k)]
  change ∫ x : ι → ℝ, x j * x k ∂nortaLaw R (fun _ => fairCoin) -
    (∫ x : ι → ℝ, x j ∂nortaLaw R (fun _ => fairCoin)) *
      ∫ x : ι → ℝ, x k ∂nortaLaw R (fun _ => fairCoin) = _
  rw [integral_mul_nortaLaw_fairCoin_eq hR hdiag, integral_eval_nortaLaw_fairCoin hR hdiag,
    integral_eval_nortaLaw_fairCoin hR hdiag]
  ring

/-- **The Pearson correlation of simulated fair coins is `(2/π) arcsin(R_{jk})`.** -/
theorem correlation_nortaLaw_fairCoin (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1) (j k : ι) :
    cov[fun x => x j, fun x => x k; nortaLaw R (fun _ => fairCoin)] /
      (√Var[fun x => x j; nortaLaw R (fun _ => fairCoin)] *
        √Var[fun x => x k; nortaLaw R (fun _ => fairCoin)]) = 2 / π * Real.arcsin (R j k) := by
  rw [covariance_nortaLaw_fairCoin hR hdiag, variance_nortaLaw_fairCoin hR hdiag,
    variance_nortaLaw_fairCoin hR hdiag, show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]
  field_simp

/-- `|(2/π) arcsin ρ| ≤ |ρ|` on `[-1, 1]`, from Jordan's inequality `(2/π) x ≤ sin x` on
`[0, π/2]`. -/
theorem abs_two_div_pi_mul_arcsin_le {ρ : ℝ} (hρ : ρ ∈ Icc (-1 : ℝ) 1) :
    |2 / π * Real.arcsin ρ| ≤ |ρ| := by
  have key : ∀ r ∈ Icc (0 : ℝ) 1, 2 / π * Real.arcsin r ≤ r := fun r hr => by
    have h := Real.mul_le_sin (Real.arcsin_nonneg.2 hr.1) (Real.arcsin_le_pi_div_two r)
    rwa [Real.sin_arcsin (by linarith [hr.1]) hr.2] at h
  have hpi := Real.pi_pos
  rcases le_total 0 ρ with h | h
  · have h1 := key ρ ⟨h, hρ.2⟩
    have h2 : 0 ≤ 2 / π * Real.arcsin ρ := by
      have := Real.arcsin_nonneg.2 h; positivity
    rw [abs_of_nonneg h2, abs_of_nonneg h]; exact h1
  · have h1 := key (-ρ) ⟨by linarith, by linarith [hρ.1]⟩
    rw [Real.arcsin_neg] at h1
    have h2 : 2 / π * Real.arcsin ρ ≤ 0 := by
      have := Real.arcsin_nonpos.2 h
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) this
    rw [abs_of_nonpos h2, abs_of_nonpos h]; linarith

/-- **Attenuation for simulated fair coins**: the Pearson correlation of the simulated coins is
at most the Gaussian correlation in absolute value, `|Corr(X_j, X_k)| ≤ |R_{jk}|`. -/
theorem abs_correlation_nortaLaw_fairCoin_le (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1)
    (j k : ι) :
    |cov[fun x => x j, fun x => x k; nortaLaw R (fun _ => fairCoin)] /
      (√Var[fun x => x j; nortaLaw R (fun _ => fairCoin)] *
        √Var[fun x => x k; nortaLaw R (fun _ => fairCoin)])| ≤ |R j k| := by
  rw [correlation_nortaLaw_fairCoin hR hdiag]
  exact abs_two_div_pi_mul_arcsin_le (mem_Icc_of_posSemidef hR hdiag j k)

end Coins

/-! ### The simulated standardized mean depends on the correlation -/

/-- **The simulated standardized mean of a surface of two binary covariates**: for fair coin
margins and Gaussian correlation `ρ`,
`∫ f = f(0,0) + (f(1,0) - f(0,0))/2 + (f(0,1) - f(0,0))/2 + I(f)(1/4 + arcsin(ρ)/(2π))`. -/
theorem integral_nortaLaw_fairCoin_pair {ρ : ℝ} (hρ : ρ ∈ Icc (-1 : ℝ) 1)
    (f : (Fin 2 → ℝ) → ℝ) :
    ∫ x, f x ∂nortaLaw (corrMatrix ρ) (fun _ => fairCoin) =
      f ![0, 0] + (f ![1, 0] - f ![0, 0]) / 2 + (f ![0, 1] - f ![0, 0]) / 2 +
        binaryInteraction f * (1 / 4 + Real.arcsin ρ / (2 * π)) := by
  have hR := corrMatrix_posSemidef (ρ := ρ) (by nlinarith [hρ.1, hρ.2])
  obtain ⟨-, h⟩ := integral_binary_expand
    (Filter.eventually_and.2 ⟨ae_nortaLaw_fairCoin_binary _ 0, ae_nortaLaw_fairCoin_binary _ 1⟩) f
  rw [h, integral_eval_nortaLaw_fairCoin hR (corrMatrix_diag _),
    integral_eval_nortaLaw_fairCoin hR (corrMatrix_diag _),
    integral_mul_nortaLaw_fairCoin_eq hR (corrMatrix_diag _)]
  simp only [corrMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

/-- **Different correlation parameters give different simulated means.** For a surface `f` of
two binary covariates with nonzero interaction contrast and fair coin margins, two distinct
Gaussian correlations in `[-1, 1]` give different simulated standardized means. -/
theorem integral_nortaLaw_fairCoin_injOn {f : (Fin 2 → ℝ) → ℝ} (hf : binaryInteraction f ≠ 0)
    {ρ ρ' : ℝ} (hρ : ρ ∈ Icc (-1 : ℝ) 1) (hρ' : ρ' ∈ Icc (-1 : ℝ) 1) (hne : ρ ≠ ρ') :
    ∫ x, f x ∂nortaLaw (corrMatrix ρ) (fun _ => fairCoin) ≠
      ∫ x, f x ∂nortaLaw (corrMatrix ρ') (fun _ => fairCoin) := by
  rw [integral_nortaLaw_fairCoin_pair hρ, integral_nortaLaw_fairCoin_pair hρ']
  intro h
  have hpi := Real.pi_pos
  have h1 : binaryInteraction f * Real.arcsin ρ = binaryInteraction f * Real.arcsin ρ' := by
    field_simp at h
    linarith
  exact hne (Real.injOn_arcsin hρ hρ' (mul_left_cancel₀ hf h1))

/-! ### The case `ρ = 1/2` -/

/-- Each simulated fair coin at Gaussian correlation `1/2` has variance `1/4`. -/
theorem variance_nortaLaw_half (j : Fin 2) :
    Var[fun x => x j; nortaLaw (corrMatrix (1 / 2)) (fun _ => fairCoin)] = 1 / 4 :=
  variance_nortaLaw_fairCoin (corrMatrix_posSemidef (by norm_num)) (corrMatrix_diag _) j

/-- **The simulated coins have Pearson correlation `1/3`**, while the Gaussian correlation is
`1/2`. -/
theorem correlation_nortaLaw_half :
    cov[fun x => x 0, fun x => x 1; nortaLaw (corrMatrix (1 / 2)) (fun _ => fairCoin)] /
      (√Var[fun x => x 0; nortaLaw (corrMatrix (1 / 2)) (fun _ => fairCoin)] *
        √Var[fun x => x 1; nortaLaw (corrMatrix (1 / 2)) (fun _ => fairCoin)]) = 1 / 3 := by
  rw [covariance_nortaLaw_half, variance_nortaLaw_half, variance_nortaLaw_half,
    show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

/-- **Attenuation at `ρ = 1/2`.** The Pearson correlation `1/3` of the simulated coins is
strictly smaller than the Gaussian correlation `corrMatrix (1/2) 0 1 = 1/2` and than the Pearson
correlation `1/2` of the target coins, although the margins agree. -/
theorem correlation_nortaLaw_half_lt :
    cov[fun x => x 0, fun x => x 1; nortaLaw (corrMatrix (1 / 2)) (fun _ => fairCoin)] /
        (√Var[fun x => x 0; nortaLaw (corrMatrix (1 / 2)) (fun _ => fairCoin)] *
          √Var[fun x => x 1; nortaLaw (corrMatrix (1 / 2)) (fun _ => fairCoin)]) <
      corrMatrix (1 / 2) 0 1 ∧
    cov[fun x => x 0, fun x => x 1; nortaLaw (corrMatrix (1 / 2)) (fun _ => fairCoin)] /
        (√Var[fun x => x 0; nortaLaw (corrMatrix (1 / 2)) (fun _ => fairCoin)] *
          √Var[fun x => x 1; nortaLaw (corrMatrix (1 / 2)) (fun _ => fairCoin)]) <
      cov[fun x => x 0, fun x => x 1; dependentCoinLaw] /
        (√Var[fun x => x 0; dependentCoinLaw] * √Var[fun x => x 1; dependentCoinLaw]) := by
  rw [correlation_nortaLaw_half, correlation_dependentCoinLaw]
  refine ⟨?_, by norm_num⟩
  change (1 / 3 : ℝ) < 1 / 2
  norm_num

end PopulationAdjustment

end CausalInference
