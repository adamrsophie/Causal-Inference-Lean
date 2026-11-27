/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import Mathlib.Probability.Distributions.Beta
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Probability.CDF
public import Mathlib.Order.Monotone.Union
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.SpecialFunctions.Sigmoid
public import CausalInference.Estimation.ConfidenceInterval

/-!
# Distributions for bias parameters

Facts about the probability distributions assigned to bias parameters in probabilistic bias
analysis. Source: Matthew P. Fox, Richard F. MacLehose and Timothy L. Lash (2021), *Applying
Quantitative Bias Analysis to Epidemiologic Data*, second edition, Chapter 7 ("Preparing for
Probabilistic Bias Analysis"). Mathlib supplies the beta density `betaPDFReal`, the beta measure
`betaMeasure`, the uniform law `pdf.IsUniform`, the Gaussian law `gaussianReal`, the binomial
law and the distribution function `cdf`; this file adds what the chapter uses on top of them.

## Main results

* Beta distribution: `integral_id_betaMeasure` (mean `α/(α + β)`, Equation 7.5),
  `integral_sq_betaMeasure`, `integral_sub_sq_betaMeasure` (variance
  `αβ/((α + β)²(α + β + 1))`, Equation 7.6), `betaPDFReal_le_mode` (mode `(α - 1)/(α + β - 2)`
  for `α, β > 1`), `betaPDFReal_le_mode_add_one` (`Beta(A + 1, B + 1)` has mode `A/(A + B)`),
  `betaMeasure_one_one` (`Beta(1, 1)` is uniform), `betaMeasure_method_of_moments` (choosing
  `α, β` from a mean and a standard deviation). The mode formula is not printed in the book.
* Uniform distribution: `uniformPDF_Icc` (density `1/(max - min)`), `map_affine_cond_Icc` and
  `IsUniform.affine` (the draw `min + u (max - min)`).
* Normal distribution: `hasLaw_normal_draw` (Equation 7.3), `se_eq_of_waldIntervalSE`
  (Equation 7.4, inverting a Wald interval built with `waldIntervalSE`) and
  `cdf_gaussianReal_affine` (standardization `F(m + s z) = Φ(z)`).
* Inverse distribution function sampling (Equations 7.1 and 7.2): the generalized inverse
  `quantile`, its Galois property `quantile_le_iff`, `map_quantile_uniform` and
  `IsUniform.hasLaw_quantile`; the probability integral transform `map_cdf_eq_uniform` for a
  continuous distribution function, with the counterexample `map_cdf_dirac_ne_uniform` for a
  point mass; `quantile_map` (quantiles commute with continuous strictly increasing maps such as
  the logit back transformation), `quantile_cdf_of_absolutelyContinuous` and
  `quantile_logitNormal` (the quantile of a logit normal law at level `Φ(z)` is
  `expit(m + s z)`).
* Correlated distributions (NORTA, Equation 7.7): the marginal step `hasLaw_quantile_cdf` and
  `hasLaw_quantile_cdf_gaussian`, and the joint law `measure_quantile_pair_le`,
  `measure_quantile_cdf_pair_le`, `measure_quantile_cdf_gaussian_pair_le`: the joint
  distribution function of the transformed pair is the copula of the inputs evaluated at the
  target marginal distribution functions, also for targets with atoms.
* Trapezoidal distribution: the distribution function `trapezoidCDF`, density `trapezoidPDF`,
  the printed sampling rule `trapezoidSample`, and the law `trapezoidMeasure` it produces from a
  standard uniform draw. `trapezoidSample_spec` and `quantile_trapezoidMeasure` show that the
  printed rule is exactly the quantile function, `cdf_trapezoidMeasure` identifies the
  distribution function, and `trapezoidMeasure_eq_withDensity` shows that the law has density
  `trapezoidPDF` for all ordered endpoints with `a < d`, collapsed ramps included
  (`integral_trapezoidPDF_eq_one`: the density integrates to one; `trapezoidPDF_le_mode`: the
  height `2/D` is the maximum). Special cases: `trapezoidMeasure_uniform` (`a = b`, `c = d` gives
  the uniform law), `trapezoidMeasure_eq_withDensity_triangularPDF` (`b = c` gives the triangular
  law) and `integral_id_trapezoidMeasure` (a symmetric trapezoid has mean `(b + c)/2`).
* `Examples`: the uniform density `4` on `[0.70, 0.95]`, `Beta(15, 2)` and `Beta(16, 3)`
  (means and standard deviations printed in the chapter), the choice `α ≈ 17.3`, `β ≈ 2.4` from
  the range `[0.70, 0.98]`, and certified bounds for the log normal and logit normal examples:
  `logNormal_sd_example` (`sd = 0.21`), `logitNormal_parameters_example` (`2.94` and `0.48`) and
  `logitNormal_quantiles_example` (the quantiles `0.88`, `0.95`, `0.98` at the levels `Φ(-1.96)`,
  `Φ(0)`, `Φ(1.96)`).

The size of the correlation induced by the NORTA construction is not formalized, and the
bivariate normal law is not defined here: the Gaussian copula enters only through the joint law
of `(Φ(Z₁), Φ(Z₂))`. The book's simulated quantiles are checked at the levels `Φ(±1.96)`, not at
exactly `0.025` and `0.975`. The beta mode for zero validation counts is not treated.
-/

@[expose] public section

namespace CausalInference

namespace BiasAnalysis

namespace Distributions

open MeasureTheory ProbabilityTheory Set

section Beta

/-- The beta density is nonnegative for positive shape parameters. -/
lemma betaPDFReal_nonneg {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (x : ℝ) : 0 ≤ betaPDFReal α β x := by
  unfold betaPDFReal
  split_ifs with h
  · have h1 : 0 < 1 - x := by linarith [h.2]
    have := Real.rpow_nonneg h.1.le (α - 1)
    have := Real.rpow_nonneg h1.le (β - 1)
    have := beta_pos hα hβ
    positivity
  · exact le_rfl

/-- The beta density integrates to one (real form of `lintegral_betaPDF_eq_one`). -/
lemma integral_betaPDFReal {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∫ x, betaPDFReal α β x = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (betaPDFReal_nonneg hα hβ))
    (measurable_betaPDFReal α β).aestronglyMeasurable]
  have := lintegral_betaPDF_eq_one hα hβ
  simp only [betaPDF] at this
  rw [this, ENNReal.toReal_one]

/-- The beta density is integrable. -/
lemma integrable_betaPDFReal {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    Integrable (betaPDFReal α β) := by
  refine ⟨(measurable_betaPDFReal α β).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (betaPDFReal_nonneg hα hβ))]
  have := lintegral_betaPDF_eq_one hα hβ
  simp only [betaPDF] at this
  rw [this]
  exact ENNReal.one_lt_top

/-- Integrals against the beta measure are integrals against its density. -/
lemma integral_betaMeasure {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (g : ℝ → ℝ) :
    ∫ x, g x ∂(betaMeasure α β) = ∫ x, betaPDFReal α β x * g x := by
  rw [betaMeasure, integral_withDensity_eq_integral_toReal_smul (f := betaPDF α β)
    (measurable_betaPDFReal α β).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [betaPDF, ENNReal.toReal_ofReal (betaPDFReal_nonneg hα hβ _), smul_eq_mul]

/-- The ratio `B(α + 1, β) / B(α, β) = α / (α + β)`, from `Γ(z + 1) = z Γ(z)`. -/
lemma beta_add_one_div {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    beta (α + 1) β / beta α β = α / (α + β) := by
  have hΓα := Real.Gamma_pos_of_pos hα
  have hΓβ := Real.Gamma_pos_of_pos hβ
  have hΓαβ := Real.Gamma_pos_of_pos (add_pos hα hβ)
  unfold beta
  rw [Real.Gamma_add_one hα.ne', show α + 1 + β = (α + β) + 1 by ring,
    Real.Gamma_add_one (add_pos hα hβ).ne']
  field_simp

/-- The moment identity behind Equation 7.5: `x` times the `Beta(α, β)` density is
`α / (α + β)` times the `Beta(α + 1, β)` density. -/
lemma mul_betaPDFReal {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (x : ℝ) :
    x * betaPDFReal α β x = α / (α + β) * betaPDFReal (α + 1) β x := by
  rw [← beta_add_one_div hα hβ]
  unfold betaPDFReal
  split_ifs with hx
  · obtain ⟨hx0, _⟩ := hx
    have hB := beta_pos hα hβ
    have hB' := beta_pos (by positivity : 0 < α + 1) hβ
    have e : x ^ (α + 1 - 1) = x ^ (α - 1) * x := by
      rw [show α + 1 - 1 = (α - 1) + 1 by ring, Real.rpow_add hx0, Real.rpow_one]
    rw [e]
    field_simp
  · simp

/-- Mean of the beta distribution (Fox, MacLehose and Lash 2021, Equation 7.5):
`E X = α / (α + β)`. -/
theorem integral_id_betaMeasure {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∫ x, x ∂(betaMeasure α β) = α / (α + β) := by
  rw [integral_betaMeasure hα hβ]
  simp_rw [mul_comm (betaPDFReal α β _), mul_betaPDFReal hα hβ]
  rw [integral_const_mul, integral_betaPDFReal (by positivity) hβ, mul_one]

/-- Second moment of the beta distribution: `E X² = α (α + 1) / ((α + β)(α + β + 1))`. -/
theorem integral_sq_betaMeasure {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∫ x, x ^ 2 ∂(betaMeasure α β) = α / (α + β) * ((α + 1) / (α + 1 + β)) := by
  rw [integral_betaMeasure hα hβ]
  have h : ∀ x, betaPDFReal α β x * x ^ 2 =
      α / (α + β) * ((α + 1) / (α + 1 + β)) * betaPDFReal (α + 1 + 1) β x := by
    intro x
    rw [show betaPDFReal α β x * x ^ 2 = x * (x * betaPDFReal α β x) by ring,
      mul_betaPDFReal hα hβ, mul_left_comm, mul_betaPDFReal (by positivity) hβ]
    ring
  simp_rw [h]
  rw [integral_const_mul, integral_betaPDFReal (by positivity) hβ, mul_one]

/-- Variance of the beta distribution (Equation 7.6):
`E (X - E X)² = α β / ((α + β)² (α + β + 1))`. -/
theorem integral_sub_sq_betaMeasure {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∫ x, (x - α / (α + β)) ^ 2 ∂(betaMeasure α β) =
      α * β / ((α + β) ^ 2 * (α + β + 1)) := by
  set m := α / (α + β) with hm
  rw [integral_betaMeasure hα hβ]
  have h : ∀ x, betaPDFReal α β x * (x - m) ^ 2 =
      (m * ((α + 1) / (α + 1 + β))) * betaPDFReal (α + 1 + 1) β x -
        2 * m * (m * betaPDFReal (α + 1) β x) + m ^ 2 * betaPDFReal α β x := by
    intro x
    have h1 := mul_betaPDFReal hα hβ x
    have h2 := mul_betaPDFReal (by positivity : 0 < α + 1) hβ x
    rw [← hm] at h1
    rw [show α + 1 + β = α + β + 1 by ring] at h2 ⊢
    have : betaPDFReal α β x * (x - m) ^ 2 =
        x * (x * betaPDFReal α β x) - 2 * m * (x * betaPDFReal α β x) +
          m ^ 2 * betaPDFReal α β x := by ring
    rw [this, h1, mul_left_comm, h2]
    ring
  simp_rw [h]
  have i0 := integrable_betaPDFReal hα hβ
  have i1 := integrable_betaPDFReal (by positivity : 0 < α + 1) hβ
  have i2 := integrable_betaPDFReal (by positivity : 0 < α + 1 + 1) hβ
  rw [integral_add _ (i0.const_mul _),
    integral_sub (i2.const_mul _) ((i1.const_mul _).const_mul _), integral_const_mul,
    integral_const_mul, integral_const_mul, integral_const_mul,
    integral_betaPDFReal hα hβ, integral_betaPDFReal (by positivity) hβ,
    integral_betaPDFReal (by positivity) hβ, hm]
  · have : 0 < α + β := by positivity
    have : 0 < α + 1 + β := by positivity
    field_simp
    ring
  · exact (i2.const_mul _).sub ((i1.const_mul _).const_mul _)

/-- The kernel inequality behind the beta mode: for `α, β > 1` and `x ∈ (0, 1)`,
`x^(α - 1) (1 - x)^(β - 1) ≤ m^(α - 1) (1 - m)^(β - 1)` with `m = (α - 1)/(α + β - 2)`. It is the
weighted arithmetic and geometric mean inequality with weights `m` and `1 - m`. -/
lemma rpow_mul_rpow_le_mode {α β : ℝ} (hα : 1 < α) (hβ : 1 < β) {x : ℝ} (hx0 : 0 < x)
    (hx1 : x < 1) :
    x ^ (α - 1) * (1 - x) ^ (β - 1) ≤
      ((α - 1) / (α + β - 2)) ^ (α - 1) * (1 - (α - 1) / (α + β - 2)) ^ (β - 1) := by
  set s := α + β - 2 with hs
  have hs0 : 0 < s := by rw [hs]; linarith
  set m := (α - 1) / s with hm
  have hm0 : 0 < m := div_pos (by linarith) hs0
  have h1m : 1 - m = (β - 1) / s := by rw [hm]; field_simp; ring
  have hm1 : 0 < 1 - m := by rw [h1m]; exact div_pos (by linarith) hs0
  have hx1' : 0 < 1 - x := by linarith
  have amgm := Real.geom_mean_le_arith_mean2_weighted hm0.le hm1.le (div_pos hx0 hm0).le
    (div_pos hx1' hm1).le (by ring)
  have hsum : m * (x / m) + (1 - m) * ((1 - x) / (1 - m)) = 1 := by field_simp; ring
  rw [hsum] at amgm
  have hpow := Real.rpow_le_rpow (by positivity) amgm hs0.le
  rw [Real.one_rpow, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by positivity),
    ← Real.rpow_mul (by positivity), show m * s = α - 1 by rw [hm]; field_simp,
    show (1 - m) * s = β - 1 by rw [h1m]; field_simp, Real.div_rpow hx0.le hm0.le,
    Real.div_rpow hx1'.le hm1.le] at hpow
  have hd : 0 < m ^ (α - 1) * (1 - m) ^ (β - 1) := by positivity
  rw [div_mul_div_comm, div_le_one hd] at hpow
  exact hpow

/-- For `α, β > 1` the point `(α - 1)/(α + β - 2)` lies in `(0, 1)`. -/
lemma mode_mem_Ioo {α β : ℝ} (hα : 1 < α) (hβ : 1 < β) :
    (α - 1) / (α + β - 2) ∈ Ioo (0 : ℝ) 1 := by
  have hs0 : 0 < α + β - 2 := by linarith
  exact ⟨div_pos (by linarith) hs0, by rw [div_lt_one hs0]; linarith⟩

/-- Mode of the beta distribution: for `α, β > 1` the density is maximized at
`(α - 1)/(α + β - 2)` (in `(0, 1)` by `mode_mem_Ioo`). The book (Chapter 7, "Beta
Distribution") discusses the mode without printing this formula; it is the standard one. -/
theorem betaPDFReal_le_mode {α β : ℝ} (hα : 1 < α) (hβ : 1 < β) (x : ℝ) :
    betaPDFReal α β x ≤ betaPDFReal α β ((α - 1) / (α + β - 2)) := by
  have hα0 : 0 < α := by linarith
  have hβ0 : 0 < β := by linarith
  have hs0 : 0 < α + β - 2 := by linarith
  have hm0 : 0 < (α - 1) / (α + β - 2) := div_pos (by linarith) hs0
  have hm1 : (α - 1) / (α + β - 2) < 1 := by rw [div_lt_one hs0]; linarith
  by_cases hx : 0 < x ∧ x < 1
  · have hB := beta_pos hα0 hβ0
    rw [betaPDFReal, ite_eq_left hx, betaPDFReal, ite_eq_left ⟨hm0, hm1⟩, mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left (rpow_mul_rpow_le_mode hα hβ hx.1 hx.2) (by positivity)
  · rw [betaPDFReal, ite_eq_right hx]
    exact betaPDFReal_nonneg hα0 hβ0 _

/-- The mode of `Beta(A + 1, B + 1)` is `A / (A + B)` (Chapter 7: adding one to the validation
counts centers the mode at the observed proportion). -/
theorem betaPDFReal_le_mode_add_one {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (x : ℝ) :
    betaPDFReal (A + 1) (B + 1) x ≤ betaPDFReal (A + 1) (B + 1) (A / (A + B)) := by
  have h := betaPDFReal_le_mode (by linarith : 1 < A + 1) (by linarith : 1 < B + 1) x
  rwa [show A + 1 - 1 = A by ring, show A + 1 + (B + 1) - 2 = A + B by ring] at h

/-- `Beta(1, 1)` is the uniform distribution on `(0, 1)` (Chapter 7 and Equation 11.5). -/
theorem betaMeasure_one_one : betaMeasure 1 1 = volume.restrict (Ioo 0 1) := by
  have hB : beta 1 1 = 1 := by simp [beta, show (1 : ℝ) + 1 = 2 by norm_num]
  have h : betaPDF 1 1 = (Ioo (0 : ℝ) 1).indicator 1 := by
    funext x
    simp only [betaPDF, betaPDFReal, hB, sub_self, Real.rpow_zero, indicator, mem_Ioo]
    split_ifs <;> simp
  rw [betaMeasure, h, withDensity_indicator measurableSet_Ioo, withDensity_one]

/-- Choosing the beta parameters from a mean and a standard deviation (Chapter 7, "Beta
Distribution"): with `k = m (1 - m) / sd² - 1 > 0`, `α = m k` and `β = (1 - m) k`, the
`Beta(α, β)` distribution has mean `m` and variance `sd²`. The condition `k > 0`, that is
`sd² < m (1 - m)`, is needed for `α, β > 0`. -/
theorem betaMeasure_method_of_moments {m sd : ℝ} (hm0 : 0 < m) (hm1 : m < 1) (hsd : sd ≠ 0)
    (hk : 0 < m * (1 - m) / sd ^ 2 - 1) :
    ∫ x, x ∂(betaMeasure (m * (m * (1 - m) / sd ^ 2 - 1)) ((1 - m) * (m * (1 - m) / sd ^ 2 - 1)))
        = m ∧
      ∫ x, (x - m) ^ 2 ∂(betaMeasure (m * (m * (1 - m) / sd ^ 2 - 1))
        ((1 - m) * (m * (1 - m) / sd ^ 2 - 1))) = sd ^ 2 := by
  set k := m * (1 - m) / sd ^ 2 - 1 with hkdef
  have hα : 0 < m * k := mul_pos hm0 hk
  have hβ : 0 < (1 - m) * k := mul_pos (by linarith) hk
  have hsum : m * k + (1 - m) * k = k := by ring
  have hmean : m * k / (m * k + (1 - m) * k) = m := by rw [hsum]; field_simp
  refine ⟨by rw [integral_id_betaMeasure hα hβ, hmean], ?_⟩
  have h := integral_sub_sq_betaMeasure hα hβ
  rw [hmean] at h
  rw [h, hsum]
  have hk1 : k + 1 = m * (1 - m) / sd ^ 2 := by rw [hkdef]; ring
  have hsd2 : 0 < sd ^ 2 := by positivity
  rw [hk1]
  field_simp

end Beta

section Uniform

/-- The uniform density on `[min, max]` is `1 / (max - min)` (Fox, MacLehose and Lash 2021,
Chapter 7, "Uniform Distribution"). -/
theorem uniformPDF_Icc {a b : ℝ} (hab : a < b) {x : ℝ} (hx : x ∈ Icc a b) :
    pdf.uniformPDF (Icc a b) x = ENNReal.ofReal (1 / (b - a)) := by
  rw [pdf.uniformPDF_ite, ite_eq_left hx, Real.volume_Icc, one_div,
    ENNReal.ofReal_inv_of_pos (sub_pos.2 hab)]

/-- The affine draw of Chapter 7: if `u` is a standard uniform draw then
`min + u (max - min)` is uniform on `[min, max]`, at the level of laws. -/
theorem map_affine_cond_Icc {a b : ℝ} (hab : a < b) :
    (volume[|Icc (0 : ℝ) 1]).map (fun u => a + u * (b - a)) = volume[|Icc a b] := by
  have hc : 0 < b - a := sub_pos.2 hab
  have hf : Measurable fun u : ℝ => a + u * (b - a) := by fun_prop
  ext t ht
  rw [Measure.map_apply hf ht, cond_apply measurableSet_Icc, cond_apply measurableSet_Icc,
    Real.volume_Icc, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, inv_one, one_mul]
  have hpre : Icc (0 : ℝ) 1 ∩ (fun u => a + u * (b - a)) ⁻¹' t =
      (fun u => u * (b - a)) ⁻¹' ((fun v => a + v) ⁻¹' (Icc a b ∩ t)) := by
    ext u
    simp only [mem_inter_iff, mem_preimage, mem_Icc]
    constructor
    · rintro ⟨⟨h0, h1⟩, h⟩
      exact ⟨⟨by nlinarith, by nlinarith⟩, h⟩
    · rintro ⟨⟨h0, h1⟩, h⟩
      refine ⟨⟨?_, ?_⟩, h⟩
      · by_contra hu; rw [not_le] at hu; nlinarith
      · by_contra hu; rw [not_le] at hu; nlinarith
  rw [hpre, Real.volume_preimage_mul_right hc.ne', measure_preimage_add,
    abs_of_pos (inv_pos.2 hc), ENNReal.ofReal_inv_of_pos hc]

/-- The affine draw for random variables: if `U` is uniform on `[0, 1]` then
`min + U (max - min)` is uniform on `[min, max]`. -/
theorem IsUniform.affine {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {U : Ω → ℝ}
    (hU : pdf.IsUniform U (Icc 0 1) P) {a b : ℝ} (hab : a < b) :
    pdf.IsUniform (fun ω => a + U ω * (b - a)) (Icc a b) P :=
  HasLaw.comp (X := U) (Y := fun u => a + u * (b - a))
    ⟨by fun_prop, map_affine_cond_Icc hab⟩ hU

end Uniform

section Normal

/-- Normal draws by location and scale (Fox, MacLehose and Lash 2021, Equation 7.3): if `Z` is
standard normal then `mean - Z sd` is normal with mean `mean` and variance `sd²`. -/
theorem hasLaw_normal_draw {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) P) (m sd : ℝ) :
    HasLaw (fun ω => m - Z ω * sd) (gaussianReal m ⟨sd ^ 2, sq_nonneg sd⟩) P := by
  have h := HasLaw.comp (X := fun ω => Z ω * sd) (Y := fun x => m - x)
    ⟨by fun_prop, gaussianReal_map_const_sub m⟩ (gaussianReal_mul_const hZ sd)
  simp only [mul_zero, sub_zero, mul_one] at h
  exact h

/-- Back calculation of a standard deviation from an interval (Equation 7.4): if `[L, U]` is the
Wald interval `[est - z se, est + z se]` with `z > 0` and `se ≥ 0`, then
`se = (U - L) / (2 z)` and `est = (L + U) / 2`. -/
theorem se_eq_of_waldIntervalSE {est se z L U : ℝ} (hz : 0 < z) (hse : 0 ≤ se)
    (h : waldIntervalSE est se z = Icc L U) : se = (U - L) / (2 * z) ∧ est = (L + U) / 2 := by
  have hle : est - z * se ≤ est + z * se := by nlinarith
  rw [waldIntervalSE, Icc_eq_Icc_iff hle] at h
  obtain ⟨hL, hU⟩ := h
  constructor
  · rw [← hL, ← hU]; field_simp; ring
  · rw [← hL, ← hU]; ring

end Normal

section Quantile

open Filter Topology

/-- The generalized inverse (quantile function) of the distribution function of a measure `μ`
on `ℝ`: `Q(u) = inf {x | u ≤ F(x)}` for `u ∈ (0, 1)` (Fox, MacLehose and Lash 2021, Equations
7.1 and 7.2, the inverse cumulative distribution function). Off `(0, 1)` it is set to `0`; that
value is never used, since `(0, 1)` carries all the mass of the standard uniform law. -/
noncomputable def quantile (μ : Measure ℝ) (u : ℝ) : ℝ :=
  if u ∈ Ioo (0 : ℝ) 1 then sInf {x | u ≤ cdf μ x} else 0

variable {μ : Measure ℝ}

lemma quantile_set_nonempty {u : ℝ} (hu : u < 1) : {x | u ≤ cdf μ x}.Nonempty := by
  obtain ⟨x, hx⟩ := ((tendsto_order.1 (tendsto_cdf_atTop μ)).1 u hu).exists
  exact ⟨x, hx.le⟩

lemma quantile_set_bddBelow {u : ℝ} (hu : 0 < u) : BddBelow {x | u ≤ cdf μ x} := by
  obtain ⟨x₀, hx₀⟩ := eventually_atBot.1 ((tendsto_order.1 (tendsto_cdf_atBot μ)).2 u hu)
  refine ⟨x₀, fun y hy => ?_⟩
  by_contra h
  exact absurd hy (not_le.2 (hx₀ y (not_le.1 h).le))

/-- The Galois property of the generalized inverse: for `u ∈ (0, 1)`,
`Q(u) ≤ x ↔ u ≤ F(x)`. It rests on the right continuity of `F`. -/
theorem quantile_le_iff {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (x : ℝ) :
    quantile μ u ≤ x ↔ u ≤ cdf μ x := by
  rw [quantile, ite_eq_left hu]
  have hne := quantile_set_nonempty (μ := μ) hu.2
  have hbdd := quantile_set_bddBelow (μ := μ) hu.1
  constructor
  · intro h
    refine le_trans ?_ ((cdf μ).mono h)
    rw [← (cdf μ).iInf_Ioi_eq]
    refine le_ciInf fun r => ?_
    obtain ⟨s, hs, hsr⟩ := exists_lt_of_csInf_lt hne r.2
    exact le_trans hs ((cdf μ).mono hsr.le)
  · exact fun h => csInf_le hbdd h

/-- `u ≤ F(Q(u))` for `u ∈ (0, 1)`. -/
lemma le_cdf_quantile {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : u ≤ cdf μ (quantile μ u) :=
  (quantile_le_iff hu _).1 le_rfl

/-- The quantile function is measurable. -/
theorem measurable_quantile (μ : Measure ℝ) : Measurable (quantile μ) := by
  refine measurable_of_Iic fun x => ?_
  have h : quantile μ ⁻¹' Iic x =
      (Ioo (0 : ℝ) 1 ∩ {u | u ≤ cdf μ x}) ∪ ((Ioo (0 : ℝ) 1)ᶜ ∩ {_u | (0 : ℝ) ≤ x}) := by
    ext u
    simp only [mem_preimage, mem_Iic, mem_union, mem_inter_iff, mem_compl_iff]
    by_cases hu : u ∈ Ioo (0 : ℝ) 1
    · rw [quantile_le_iff hu]; simp [hu]
    · rw [quantile, ite_eq_right hu]; simp [hu]
  rw [h]
  exact (measurableSet_Ioo.inter measurableSet_Iic).union
    (measurableSet_Ioo.compl.inter (MeasurableSet.const _))

/-- Inverse distribution function sampling (Fox, MacLehose and Lash 2021, Equations 7.1 and
7.2): pushing the uniform law on `(0, 1)` forward by the quantile function of a probability
measure `μ` on `ℝ` gives `μ`. -/
theorem map_quantile_uniform (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (volume.restrict (Ioo (0 : ℝ) 1)).map (quantile μ) = μ := by
  have : IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) 1)) :=
    isFiniteMeasure_restrict.2 (by simp)
  refine Measure.ext_of_Iic _ _ fun x => ?_
  rw [Measure.map_apply (measurable_quantile μ) measurableSet_Iic,
    Measure.restrict_apply (measurable_quantile μ measurableSet_Iic), ← ofReal_cdf]
  have h : quantile μ ⁻¹' Iic x ∩ Ioo 0 1 = Ioo 0 1 ∩ Iic (cdf μ x) := by
    ext u
    simp only [mem_inter_iff, mem_preimage, mem_Iic]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2, (quantile_le_iff h2 x).1 h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨(quantile_le_iff h1 x).2 h2, h1⟩
  rw [h]
  rcases (cdf_le_one μ x).lt_or_eq with hlt | heq
  · have : Ioo (0 : ℝ) 1 ∩ Iic (cdf μ x) = Ioc 0 (cdf μ x) := by
      ext u
      simp only [mem_inter_iff, mem_Ioo, mem_Iic, mem_Ioc]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by linarith⟩, h3⟩
    rw [this, Real.volume_Ioc, sub_zero]
  · rw [heq, inter_eq_left.2 (fun u (hu : u ∈ Ioo (0 : ℝ) 1) => (le_of_lt hu.2 : u ≤ 1)),
      Real.volume_Ioo, sub_zero]

/-- The uniform law on `[0, 1]` (the law of a standard uniform draw `u`) equals the Lebesgue
measure restricted to `(0, 1)`. -/
lemma cond_Icc_zero_one : volume[|Icc (0 : ℝ) 1] = volume.restrict (Ioo (0 : ℝ) 1) := by
  rw [ProbabilityTheory.cond, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, inv_one, one_smul]
  exact Measure.restrict_congr_set Ioo_ae_eq_Icc.symm

/-- Inverse distribution function sampling for random variables: if `U` is uniform on `[0, 1]`
then `Q(U)` has law `μ`, that is, distribution function `F = cdf μ`. -/
theorem IsUniform.hasLaw_quantile {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {U : Ω → ℝ}
    (hU : pdf.IsUniform U (Icc 0 1) P) (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    HasLaw (fun ω => quantile μ (U ω)) μ P :=
  HasLaw.comp (X := U) (Y := quantile μ)
    ⟨(measurable_quantile μ).aemeasurable, by rw [cond_Icc_zero_one, map_quantile_uniform]⟩ hU

/-- For a continuous distribution function, `F(Q(u)) = u` for `u ∈ (0, 1)`. -/
theorem cdf_quantile {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (hF : Continuous (cdf μ)) :
    cdf μ (quantile μ u) = u := by
  refine le_antisymm ?_ (le_cdf_quantile hu)
  have hlt : ∀ y < quantile μ u, cdf μ y ≤ u := fun y hy =>
    le_of_lt (not_le.1 fun h => absurd ((quantile_le_iff hu y).2 h) (not_le.2 hy))
  exact le_of_tendsto ((hF.tendsto _).mono_left nhdsWithin_le_nhds)
    (eventually_nhdsWithin_of_forall (s := Iio (quantile μ u)) fun y hy => hlt y hy)

/-- Probability integral transform (Chapter 7, "Generalized Method for Sampling from
Distributions" and "Correlated Distributions"): if `μ` has a continuous distribution function
`F`, then `F` pushes `μ` forward to the uniform law on `(0, 1)`. -/
theorem map_cdf_eq_uniform (μ : Measure ℝ) [IsProbabilityMeasure μ] (hF : Continuous (cdf μ)) :
    μ.map (cdf μ) = volume.restrict (Ioo (0 : ℝ) 1) := by
  rw [show μ.map (cdf μ) = ((volume.restrict (Ioo (0 : ℝ) 1)).map (quantile μ)).map (cdf μ) from
    congrArg (Measure.map (cdf μ)) (map_quantile_uniform μ).symm]
  rw [Measure.map_map (cdf μ).mono.measurable (measurable_quantile μ)]
  have h : (cdf μ ∘ quantile μ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] id :=
    (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun u hu =>
      cdf_quantile hu hF)
  rw [Measure.map_congr h, Measure.map_id]

/-- A probability measure on `ℝ` without atoms has a continuous distribution function. -/
theorem continuous_cdf_of_measure_singleton (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : ∀ x, μ {x} = 0) : Continuous (cdf μ) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  rw [Monotone.continuousAt_iff_leftLim_eq_rightLim (cdf μ).mono, (cdf μ).rightLim_eq]
  have hs := (cdf μ).measure_singleton x
  rw [measure_cdf, h x] at hs
  have h1 : cdf μ x - Function.leftLim (cdf μ) x ≤ 0 := ENNReal.ofReal_eq_zero.1 hs.symm
  have h2 : Function.leftLim (cdf μ) x ≤ cdf μ x := (cdf μ).mono.leftLim_le le_rfl
  linarith

/-- The marginal step of the NORTA construction (Chapter 7, "Correlated Distributions",
Equation 7.7): if `Z` has a law `ν` with continuous distribution function `G` (for instance a
coordinate of a bivariate normal vector, whose marginal is standard normal), then
`X = Q_μ(G(Z))` has law `μ`. Applied to each coordinate of a correlated pair, it shows that the
transformed pair has the target marginals whatever the dependence of `(Z₁, Z₂)`; the joint law is
`measure_quantile_cdf_pair_le`. The size of the induced correlation is not a theorem here. -/
theorem hasLaw_quantile_cdf {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → ℝ}
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (hZ : HasLaw Z ν P) (hG : Continuous (cdf ν))
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    HasLaw (fun ω => quantile μ (cdf ν (Z ω))) μ P := by
  have hU : HasLaw (fun ω => cdf ν (Z ω)) (volume.restrict (Ioo (0 : ℝ) 1)) P :=
    HasLaw.comp (X := Z) (Y := cdf ν) ⟨(cdf ν).mono.measurable.aemeasurable,
      map_cdf_eq_uniform ν hG⟩ hZ
  exact HasLaw.comp (X := fun ω => cdf ν (Z ω)) (Y := quantile μ)
    ⟨(measurable_quantile μ).aemeasurable, map_quantile_uniform μ⟩ hU

/-- NORTA for a standard normal coordinate: if `Z ~ N(0, 1)` then `Q_μ(Φ(Z))` has law `μ`, where
`Φ` is the standard normal distribution function. -/
theorem hasLaw_quantile_cdf_gaussian {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Z : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P) (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    HasLaw (fun ω => quantile μ (cdf (gaussianReal 0 1) (Z ω))) μ P := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  exact hasLaw_quantile_cdf hZ
    (continuous_cdf_of_measure_singleton _ fun x => measure_singleton x) μ

/-- Quantiles commute with continuous strictly increasing transformations (Chapter 7, the logit
and log transformations of "Normal Distribution"): for `u ∈ (0, 1)`, the `u` quantile of the law
of `g(X)` is `g` applied to the `u` quantile of the law of `X`. -/
theorem quantile_map {g : ℝ → ℝ} (hg : StrictMono g) (hgc : Continuous g)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    quantile (μ.map g) u = g (quantile μ u) := by
  have hmeas : Measurable g := hgc.measurable
  have hprob : IsProbabilityMeasure (μ.map g) := inferInstance
  have hcdf : ∀ y, cdf (μ.map g) y = μ.real (g ⁻¹' Iic y) := fun y => by
    rw [cdf_eq_real, map_measureReal_apply hmeas measurableSet_Iic]
  set q := quantile μ u with hq
  apply le_antisymm
  · rw [quantile_le_iff hu, hcdf]
    have : g ⁻¹' Iic (g q) = Iic q := by
      ext x; simp only [mem_preimage, mem_Iic, hg.le_iff_le]
    rw [this, ← cdf_eq_real]
    exact le_cdf_quantile hu
  · by_contra hlt
    rw [not_le] at hlt
    set y := quantile (μ.map g) u
    have hy := le_cdf_quantile (μ := μ.map g) hu
    rw [hcdf] at hy
    set D := g ⁻¹' Iic y with hD
    have hDq : ∀ x ∈ D, x < q := fun x hx => hg.lt_iff_lt.1 (lt_of_le_of_lt hx hlt)
    rcases D.eq_empty_or_nonempty with hE | hne
    · rw [hE, measureReal_empty] at hy
      exact absurd hu.1 (not_lt.2 hy)
    · have hclosed : IsClosed D := isClosed_le hgc continuous_const
      have hbdd : BddAbove D := ⟨q, fun x hx => (hDq x hx).le⟩
      set d := sSup D
      have hdD : d ∈ D := hclosed.csSup_mem hne hbdd
      have hsub : D ⊆ Iic d := fun x hx => le_csSup hbdd hx
      have h1 : μ.real D ≤ cdf μ d := by
        rw [cdf_eq_real]; exact measureReal_mono hsub
      have h2 : cdf μ d < u :=
        not_le.1 fun h => absurd ((quantile_le_iff hu d).2 h) (not_le.2 (hDq d hdD))
      linarith

/-- A random variable with the uniform law on `(0, 1)` lies in `(0, 1)` almost surely. -/
lemma ae_mem_Ioo_of_hasLaw_uniform {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {U : Ω → ℝ}
    (hU : HasLaw U (volume.restrict (Ioo (0 : ℝ) 1)) P) : ∀ᵐ ω ∂P, U ω ∈ Ioo (0 : ℝ) 1 := by
  have h : ∀ᵐ x ∂(P.map U), x ∈ Ioo (0 : ℝ) 1 := by
    rw [hU.map_eq]; exact ae_restrict_mem measurableSet_Ioo
  exact ae_of_ae_map hU.aemeasurable h

/-- The probability integral transform for random variables: if `Z` has a law `ν` with
continuous distribution function `G`, then `G(Z)` is uniform on `(0, 1)`. -/
theorem hasLaw_cdf_uniform {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → ℝ}
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (hZ : HasLaw Z ν P) (hG : Continuous (cdf ν)) :
    HasLaw (fun ω => cdf ν (Z ω)) (volume.restrict (Ioo (0 : ℝ) 1)) P :=
  HasLaw.comp (X := Z) (Y := cdf ν) ⟨(cdf ν).mono.measurable.aemeasurable,
    map_cdf_eq_uniform ν hG⟩ hZ

/-- Joint law of two quantile transformed uniforms (Chapter 7, "Correlated Distributions"): if
`U₁` and `U₂` each have the uniform law on `(0, 1)`, with any dependence between them, then
`P(Q₁(U₁) ≤ x, Q₂(U₂) ≤ y) = P(U₁ ≤ F₁(x), U₂ ≤ F₂(y))`, where `Qᵢ` and `Fᵢ` are the quantile
and distribution functions of the target laws `μᵢ`. The right side is the copula of `(U₁, U₂)`
(their joint distribution function) evaluated at `(F₁(x), F₂(y))`, so the dependence of the
transformed pair is that copula, also when a target law has atoms. -/
theorem measure_quantile_pair_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {U₁ U₂ : Ω → ℝ} (hU₁ : HasLaw U₁ (volume.restrict (Ioo (0 : ℝ) 1)) P)
    (hU₂ : HasLaw U₂ (volume.restrict (Ioo (0 : ℝ) 1)) P) (μ₁ μ₂ : Measure ℝ) (x y : ℝ) :
    P {ω | quantile μ₁ (U₁ ω) ≤ x ∧ quantile μ₂ (U₂ ω) ≤ y} =
      P {ω | U₁ ω ≤ cdf μ₁ x ∧ U₂ ω ≤ cdf μ₂ y} := by
  refine measure_congr ?_
  filter_upwards [ae_mem_Ioo_of_hasLaw_uniform hU₁, ae_mem_Ioo_of_hasLaw_uniform hU₂]
    with ω h1 h2
  rw [quantile_le_iff h1, quantile_le_iff h2]

/-- The joint distribution function of the NORTA pair (Chapter 7, "Correlated Distributions",
Equation 7.7): if `Zᵢ` has a law `νᵢ` with continuous distribution function `Gᵢ` and
`Xᵢ = Q_{μᵢ}(Gᵢ(Zᵢ))`, then `P(X₁ ≤ x, X₂ ≤ y) = P(G₁(Z₁) ≤ F₁(x), G₂(Z₂) ≤ F₂(y))`: the copula
of `(Z₁, Z₂)` at the target marginal distribution functions. -/
theorem measure_quantile_cdf_pair_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Z₁ Z₂ : Ω → ℝ} {ν₁ ν₂ : Measure ℝ} [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    (hZ₁ : HasLaw Z₁ ν₁ P) (hZ₂ : HasLaw Z₂ ν₂ P) (hG₁ : Continuous (cdf ν₁))
    (hG₂ : Continuous (cdf ν₂)) (μ₁ μ₂ : Measure ℝ) (x y : ℝ) :
    P {ω | quantile μ₁ (cdf ν₁ (Z₁ ω)) ≤ x ∧ quantile μ₂ (cdf ν₂ (Z₂ ω)) ≤ y} =
      P {ω | cdf ν₁ (Z₁ ω) ≤ cdf μ₁ x ∧ cdf ν₂ (Z₂ ω) ≤ cdf μ₂ y} :=
  measure_quantile_pair_le (hasLaw_cdf_uniform hZ₁ hG₁) (hasLaw_cdf_uniform hZ₂ hG₂) μ₁ μ₂ x y

/-- The standard normal distribution function `Φ` is continuous. -/
lemma continuous_cdf_gaussianReal_zero_one : Continuous (cdf (gaussianReal 0 1)) := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  exact continuous_cdf_of_measure_singleton _ fun x => measure_singleton x

/-- The NORTA pair with standard normal coordinates: if `Z₁, Z₂ ~ N(0, 1)` (any joint law) then
`P(Q₁(Φ(Z₁)) ≤ x, Q₂(Φ(Z₂)) ≤ y) = P(Φ(Z₁) ≤ F₁(x), Φ(Z₂) ≤ F₂(y))`. When `(Z₁, Z₂)` is
standard bivariate normal with correlation `ρ`, the right side is by definition the Gaussian
copula `C_ρ(F₁(x), F₂(y))`; the bivariate normal law itself is not formalized here. -/
theorem measure_quantile_cdf_gaussian_pair_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Z₁ Z₂ : Ω → ℝ} (hZ₁ : HasLaw Z₁ (gaussianReal 0 1) P) (hZ₂ : HasLaw Z₂ (gaussianReal 0 1) P)
    (μ₁ μ₂ : Measure ℝ) (x y : ℝ) :
    P {ω | quantile μ₁ (cdf (gaussianReal 0 1) (Z₁ ω)) ≤ x ∧
        quantile μ₂ (cdf (gaussianReal 0 1) (Z₂ ω)) ≤ y} =
      P {ω | cdf (gaussianReal 0 1) (Z₁ ω) ≤ cdf μ₁ x ∧
        cdf (gaussianReal 0 1) (Z₂ ω) ≤ cdf μ₂ y} :=
  measure_quantile_cdf_pair_le hZ₁ hZ₂ continuous_cdf_gaussianReal_zero_one
    continuous_cdf_gaussianReal_zero_one μ₁ μ₂ x y

/-- If Lebesgue measure is absolutely continuous with respect to a probability measure `μ`
(every interval has positive `μ` mass), then `0 < F(x) < 1` for every `x`. -/
lemma cdf_mem_Ioo_of_absolutelyContinuous [IsProbabilityMeasure μ] (hμ : volume ≪ μ) (x : ℝ) :
    cdf μ x ∈ Ioo (0 : ℝ) 1 := by
  constructor
  · by_contra h
    rw [not_lt] at h
    have h0 : μ (Iic x) = 0 := by rw [← ofReal_cdf]; exact ENNReal.ofReal_eq_zero.2 h
    have := hμ h0
    simp at this
  · by_contra h
    rw [not_lt] at h
    have h1 : μ (Ioi x) = 0 := by
      rw [← compl_Iic, measure_compl measurableSet_Iic (measure_ne_top _ _), measure_univ,
        ← ofReal_cdf]
      exact tsub_eq_zero_of_le (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal h)
    have := hμ h1
    simp at this

/-- If Lebesgue measure is absolutely continuous with respect to `μ`, the quantile function
inverts the distribution function: `Q(F(x)) = x`. -/
theorem quantile_cdf_of_absolutelyContinuous [IsProbabilityMeasure μ] (hμ : volume ≪ μ)
    (x : ℝ) : quantile μ (cdf μ x) = x := by
  have hx := cdf_mem_Ioo_of_absolutelyContinuous hμ x
  refine le_antisymm ((quantile_le_iff hx x).2 le_rfl) (not_lt.1 fun hlt => ?_)
  set q := quantile μ (cdf μ x) with hq
  have h1 : cdf μ x ≤ cdf μ q := le_cdf_quantile hx
  have h2 := (cdf μ).measure_Ioc q x
  rw [measure_cdf, ENNReal.ofReal_eq_zero.2 (by linarith)] at h2
  have := hμ h2
  rw [Real.volume_Ioc, ENNReal.ofReal_eq_zero] at this
  linarith

/-- Standardizing the normal distribution function: for `s > 0` and variance `v = s²`, the
`N(m, v)` distribution function at `m + s z` is the standard normal distribution function
`Φ(z)`. -/
theorem cdf_gaussianReal_affine (m : ℝ) {s : ℝ} (hs : 0 < s) {v : NNReal} (hv : (v : ℝ) = s ^ 2)
    (z : ℝ) : cdf (gaussianReal m v) (m + s * z) = cdf (gaussianReal 0 1) z := by
  have hlaw := hasLaw_normal_draw (P := gaussianReal 0 1) (Z := id) (HasLaw.id) m (-s)
  have hv' : (⟨(-s) ^ 2, sq_nonneg (-s)⟩ : NNReal) = v := NNReal.eq (by
    change (-s) ^ 2 = (v : ℝ); rw [hv, neg_sq])
  rw [hv'] at hlaw
  have hf : Measurable fun ω : ℝ => m - id ω * -s := by fun_prop
  rw [cdf_eq_real, cdf_eq_real, ← hlaw.map_eq, map_measureReal_apply hf measurableSet_Iic]
  congr 1
  ext w
  simp only [mem_preimage, mem_Iic, id]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- Quantiles of the logit normal law (Chapter 7, "Normal Distribution"): if `logit(p)` has law
`N(m, v)` with `v = s²`, `s > 0`, the quantile of `p = expit(logit(p))` at level `Φ(z)` is
`expit(m + s z)`. Here `Real.sigmoid` is the expit function. -/
theorem quantile_logitNormal (m : ℝ) {s : ℝ} (hs : 0 < s) {v : NNReal} (hv : (v : ℝ) = s ^ 2)
    (z : ℝ) :
    quantile ((gaussianReal m v).map Real.sigmoid) (cdf (gaussianReal 0 1) z) =
      Real.sigmoid (m + s * z) := by
  have hv0 : v ≠ 0 := fun h => by
    rw [h, NNReal.coe_zero] at hv
    exact (pow_pos hs 2).ne' hv.symm
  have hac := gaussianReal_absolutelyContinuous' m hv0
  rw [← cdf_gaussianReal_affine m hs hv z,
    quantile_map Real.sigmoid_strictMono continuous_sigmoid _
      (cdf_mem_Ioo_of_absolutelyContinuous hac _),
    quantile_cdf_of_absolutelyContinuous hac]

/-- Continuity of the distribution function cannot be dropped from `map_cdf_eq_uniform`: for
the point mass at `0`, `F` pushes the law to the point mass at `F(0)`, which charges the point
`F(0)` while the uniform law does not. -/
theorem map_cdf_dirac_ne_uniform :
    (Measure.dirac (0 : ℝ)).map (cdf (Measure.dirac 0)) ≠ volume.restrict (Ioo (0 : ℝ) 1) := by
  intro h
  have hm : Measurable (cdf (Measure.dirac (0 : ℝ))) := (cdf _).mono.measurable
  have h1 := congrArg (fun ν : Measure ℝ => ν {cdf (Measure.dirac (0 : ℝ)) 0}) h
  simp only [Measure.map_dirac' hm, Measure.dirac_apply_of_mem (mem_singleton _)] at h1
  have h2 : volume.restrict (Ioo (0 : ℝ) 1) {cdf (Measure.dirac (0 : ℝ)) 0} = 0 :=
    le_antisymm ((Measure.restrict_apply_le _ _).trans (by simp)) zero_le
  rw [h2] at h1
  exact one_ne_zero h1

end Quantile

section Trapezoid

/-! ### The trapezoidal distribution

Minimum `a`, lower mode `b`, upper mode `c`, maximum `d`, with `a ≤ b ≤ c ≤ d` and `a < d`
(Fox, MacLehose and Lash 2021, Chapter 7, "Trapezoidal Distribution"). The normalizing length is
`D = d + c - a - b`, so the height of the density is `2 / D`. When `a = b` (or `c = d`) the
rising (or falling) ramp is a single point; the ramp formulas are stated only for positive
width, and the endpoint values `F(a) = 0`, `F(d) = 1` hold for all admissible parameters. -/

/-- The trapezoidal distribution function, piecewise: `0` up to `a`, `(x - a)²/((b - a) D)` on
`[a, b]`, `(2x - a - b)/D` on `[b, c]`, `1 - (d - x)²/((d - c) D)` on `[c, d]`, and `1` after
`d`. -/
noncomputable def trapezoidCDF (a b c d x : ℝ) : ℝ :=
  if x ≤ a then 0
  else if x ≤ b then (x - a) ^ 2 / ((b - a) * (d + c - a - b))
  else if x ≤ c then (2 * x - a - b) / (d + c - a - b)
  else if x ≤ d then 1 - (d - x) ^ 2 / ((d - c) * (d + c - a - b))
  else 1

/-- The trapezoidal density: height `h = 2 / D` between the modes, rising linearly from `a` to
`b` and falling linearly from `c` to `d`, and `0` off `[a, d]`. The value on `[b, c]` is the
height also at the endpoints, so that the mode is attained when a ramp is collapsed
(`trapezoidPDF_le_mode`). -/
noncomputable def trapezoidPDF (a b c d x : ℝ) : ℝ :=
  if x < a then 0
  else if x < b then 2 / (d + c - a - b) * ((x - a) / (b - a))
  else if x ≤ c then 2 / (d + c - a - b)
  else if x < d then 2 / (d + c - a - b) * ((d - x) / (d - c))
  else 0

/-- The sampling rule printed in Chapter 7: with `s = (a + b + u (d + c - a - b)) / 2`, return
`a + √((b - a)(2s - a - b))` if `s < b`, `s` if `b ≤ s < c`, and `d - √((d - c)(-2s + d + c))`
if `s ≥ c`. -/
noncomputable def trapezoidSample (a b c d u : ℝ) : ℝ :=
  if (a + b + u * (d + c - a - b)) / 2 < b then
    a + Real.sqrt ((b - a) * (2 * ((a + b + u * (d + c - a - b)) / 2) - a - b))
  else if (a + b + u * (d + c - a - b)) / 2 < c then (a + b + u * (d + c - a - b)) / 2
  else d - Real.sqrt ((d - c) * (-2 * ((a + b + u * (d + c - a - b)) / 2) + d + c))

variable {a b c d : ℝ}

/-- The rising ramp of the distribution function: on `[a, b]` with `a < b`,
`F(x) = (x - a)²/((b - a) D)`. The positive width `b - a` keeps the quotient meaningful; at a
collapsed ramp `a = b` the only point is `a`, where `F(a) = 0` (`trapezoidCDF_left`). -/
lemma trapezoidCDF_lower (_hab : a < b) {x : ℝ} (hx : x ∈ Icc a b) :
    trapezoidCDF a b c d x = (x - a) ^ 2 / ((b - a) * (d + c - a - b)) := by
  obtain ⟨h1, h2⟩ := hx
  unfold trapezoidCDF
  by_cases hxa : x ≤ a
  · have : x = a := le_antisymm hxa h1
    subst this; simp
  · rw [ite_eq_right hxa, ite_eq_left h2]

/-- The flat part of the distribution function: on `[b, c]`, `F(x) = (2x - a - b)/D`. -/
lemma trapezoidCDF_mid (hab : a ≤ b) (hbc : b ≤ c) (had : a < d) {x : ℝ}
    (hx : x ∈ Icc b c) :
    trapezoidCDF a b c d x = (2 * x - a - b) / (d + c - a - b) := by
  obtain ⟨h1, h2⟩ := hx
  have hD : 0 < d + c - a - b := by linarith
  unfold trapezoidCDF
  by_cases hxa : x ≤ a
  · have hxa' : x = a := by linarith
    have hba : b = a := by linarith
    subst hxa' hba; simp only [le_refl, ite_true]
    rw [show (2 : ℝ) * b - b - b = 0 by ring, zero_div]
  · rw [ite_eq_right hxa]
    by_cases hxb : x ≤ b
    · have hxb' : x = b := le_antisymm hxb h1
      have hab' : 0 < b - a := by
        subst hxb'; exact sub_pos.2 (not_le.1 hxa)
      rw [ite_eq_left hxb, hxb']
      field_simp
      ring
    · rw [ite_eq_right hxb, ite_eq_left h2]

/-- The falling ramp of the distribution function: on `[c, d]` with `c < d`,
`F(x) = 1 - (d - x)²/((d - c) D)`. At a collapsed ramp `c = d`, `F(d) = 1`
(`trapezoidCDF_right`). -/
lemma trapezoidCDF_upper (hab : a ≤ b) (hbc : b ≤ c) (hcd : c < d) {x : ℝ}
    (hx : x ∈ Icc c d) :
    trapezoidCDF a b c d x = 1 - (d - x) ^ 2 / ((d - c) * (d + c - a - b)) := by
  obtain ⟨h1, h2⟩ := hx
  have had : a < d := by linarith
  have hD : 0 < d + c - a - b := by linarith
  by_cases hxc : x ≤ c
  · have hxc' : x = c := le_antisymm hxc h1
    subst hxc'
    rw [trapezoidCDF_mid hab hbc had ⟨hbc, le_rfl⟩]
    have : 0 < d - x := sub_pos.2 hcd
    field_simp
    ring
  · unfold trapezoidCDF
    rw [ite_eq_right (by linarith : ¬ x ≤ a), ite_eq_right (by linarith : ¬ x ≤ b),
      ite_eq_right hxc, ite_eq_left h2]

lemma trapezoidCDF_of_le {x : ℝ} (hx : x ≤ a) : trapezoidCDF a b c d x = 0 := by
  rw [trapezoidCDF, ite_eq_left hx]

lemma trapezoidCDF_of_ge (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (had : a < d) {x : ℝ}
    (hx : d ≤ x) : trapezoidCDF a b c d x = 1 := by
  rcases hx.lt_or_eq with hlt | heq
  · unfold trapezoidCDF
    rw [ite_eq_right (by linarith : ¬ x ≤ a), ite_eq_right (by linarith : ¬ x ≤ b),
      ite_eq_right (by linarith : ¬ x ≤ c), ite_eq_right (by linarith : ¬ x ≤ d)]
  · subst heq
    rcases hcd.lt_or_eq with hlt | hce
    · rw [trapezoidCDF_upper hab hbc hlt ⟨hlt.le, le_rfl⟩]; simp
    · subst hce
      rw [trapezoidCDF_mid hab hbc had ⟨hbc, le_rfl⟩, div_eq_one_iff_eq (by linarith)]
      ring

/-- The trapezoidal distribution function vanishes at the minimum, for all parameters. -/
lemma trapezoidCDF_left : trapezoidCDF a b c d a = 0 := trapezoidCDF_of_le le_rfl

/-- The trapezoidal distribution function equals one at the maximum, for all admissible
parameters, collapsed ramps included. -/
lemma trapezoidCDF_right (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (had : a < d) :
    trapezoidCDF a b c d d = 1 := trapezoidCDF_of_ge hab hbc hcd had le_rfl

/-- The trapezoidal distribution function is strictly increasing on `[a, d]`. -/
theorem trapezoidCDF_strictMonoOn (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (had : a < d) :
    StrictMonoOn (trapezoidCDF a b c d) (Icc a d) := by
  have hD : 0 < d + c - a - b := by linarith
  have h1 : StrictMonoOn (trapezoidCDF a b c d) (Icc a b) := by
    intro x hx y hy hxy
    have hba : 0 < b - a := by linarith [hx.1, hy.2]
    rw [trapezoidCDF_lower (sub_pos.1 hba) hx, trapezoidCDF_lower (sub_pos.1 hba) hy]
    apply div_lt_div_of_pos_right _ (by positivity)
    nlinarith [hx.1]
  have h2 : StrictMonoOn (trapezoidCDF a b c d) (Icc b c) := by
    intro x hx y hy hxy
    rw [trapezoidCDF_mid hab hbc had hx, trapezoidCDF_mid hab hbc had hy]
    apply div_lt_div_of_pos_right _ hD
    linarith
  have h3 : StrictMonoOn (trapezoidCDF a b c d) (Icc c d) := by
    intro x hx y hy hxy
    have hdc : 0 < d - c := by linarith [hx.1, hy.2]
    rw [trapezoidCDF_upper hab hbc (sub_pos.1 hdc) hx,
      trapezoidCDF_upper hab hbc (sub_pos.1 hdc) hy]
    have : (d - y) ^ 2 / ((d - c) * (d + c - a - b)) <
        (d - x) ^ 2 / ((d - c) * (d + c - a - b)) := by
      apply div_lt_div_of_pos_right _ (by positivity)
      nlinarith [hy.2]
    linarith
  have h12 := StrictMonoOn.union h1 h2 (isGreatest_Icc hab) (isLeast_Icc hbc)
  rw [Icc_union_Icc_eq_Icc hab hbc] at h12
  have h123 := StrictMonoOn.union h12 h3 (isGreatest_Icc (hab.trans hbc)) (isLeast_Icc hcd)
  rwa [Icc_union_Icc_eq_Icc (hab.trans hbc) hcd] at h123

/-- The trapezoidal distribution function is monotone, with values in `[0, 1]`. -/
theorem trapezoidCDF_monotone (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (had : a < d) :
    Monotone (trapezoidCDF a b c d) := by
  have hsm := trapezoidCDF_strictMonoOn hab hbc hcd had
  have hmem : ∀ x ∈ Icc a d, 0 ≤ trapezoidCDF a b c d x ∧ trapezoidCDF a b c d x ≤ 1 := by
    intro x hx
    have h0 := hsm.monotoneOn ⟨le_rfl, had.le⟩ hx hx.1
    have h1 := hsm.monotoneOn hx ⟨had.le, le_rfl⟩ hx.2
    rw [trapezoidCDF_of_le le_rfl] at h0
    rw [trapezoidCDF_of_ge hab hbc hcd had le_rfl] at h1
    exact ⟨h0, h1⟩
  intro x y hxy
  by_cases hxa : x ≤ a
  · rw [trapezoidCDF_of_le hxa]
    by_cases hya : y ≤ a
    · rw [trapezoidCDF_of_le hya]
    by_cases hyd : y ≤ d
    · exact (hmem y ⟨(not_le.1 hya).le, hyd⟩).1
    · rw [trapezoidCDF_of_ge hab hbc hcd had (not_le.1 hyd).le]; norm_num
  by_cases hxd : x ≤ d
  · by_cases hyd : y ≤ d
    · exact hsm.monotoneOn ⟨(not_le.1 hxa).le, hxd⟩ ⟨by linarith [not_le.1 hxa], hyd⟩ hxy
    · rw [trapezoidCDF_of_ge hab hbc hcd had (not_le.1 hyd).le]
      exact (hmem x ⟨(not_le.1 hxa).le, hxd⟩).2
  · rw [trapezoidCDF_of_ge hab hbc hcd had (not_le.1 hxd).le,
      trapezoidCDF_of_ge hab hbc hcd had (by linarith [not_le.1 hxd])]

/-- The printed sampling rule inverts the distribution function: for `u ∈ [0, 1]` the draw lies
in `[a, d]` and `F(trap(u)) = u`. -/
theorem trapezoidSample_spec (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (had : a < d) {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) :
    trapezoidSample a b c d u ∈ Icc a d ∧
      trapezoidCDF a b c d (trapezoidSample a b c d u) = u := by
  obtain ⟨hu0, hu1⟩ := hu
  set D := d + c - a - b with hDdef
  have hD : 0 < D := by rw [hDdef]; linarith
  set s := (a + b + u * D) / 2 with hs
  have hs1 : a + b ≤ 2 * s := by rw [hs]; nlinarith
  have hs2 : 2 * s ≤ c + d := by rw [hs, hDdef]; nlinarith
  have h2s : 2 * s - a - b = u * D := by rw [hs]; ring
  unfold trapezoidSample
  rw [← hDdef, ← hs]
  by_cases h1 : s < b
  · rw [ite_eq_left h1]
    have hba : 0 < b - a := by linarith
    set r := (b - a) * (2 * s - a - b) with hr
    have hr0 : 0 ≤ r := by rw [hr]; nlinarith
    have hrle : Real.sqrt r ≤ b - a := by
      rw [Real.sqrt_le_left hba.le]; rw [hr]; nlinarith
    have hmem : a + Real.sqrt r ∈ Icc a b := ⟨by linarith [Real.sqrt_nonneg r], by linarith⟩
    refine ⟨⟨hmem.1, by linarith [hmem.2]⟩, ?_⟩
    rw [trapezoidCDF_lower (sub_pos.1 hba) hmem, add_sub_cancel_left, Real.sq_sqrt hr0, hr,
      ← hDdef, h2s]
    field_simp
  · rw [ite_eq_right h1]
    by_cases h2 : s < c
    · rw [ite_eq_left h2]
      refine ⟨⟨by linarith, by linarith⟩, ?_⟩
      rw [trapezoidCDF_mid hab hbc had ⟨not_lt.1 h1, h2.le⟩, ← hDdef, h2s]
      field_simp
    · rw [ite_eq_right h2]
      set r := (d - c) * (-2 * s + d + c) with hr
      have hr0 : 0 ≤ r := by rw [hr]; nlinarith
      have hrle : Real.sqrt r ≤ d - c := by
        rw [Real.sqrt_le_left (by linarith)]; rw [hr]; nlinarith
      have hmem : d - Real.sqrt r ∈ Icc c d :=
        ⟨by linarith, by linarith [Real.sqrt_nonneg r]⟩
      refine ⟨⟨by linarith [hmem.1], hmem.2⟩, ?_⟩
      rcases hcd.lt_or_eq with hlt | heq
      · rw [trapezoidCDF_upper hab hbc hlt hmem, sub_sub_cancel, Real.sq_sqrt hr0, hr, ← hDdef]
        have : 0 < d - c := sub_pos.2 hlt
        field_simp
        linear_combination (-1 : ℝ) * h2s
      · have hsd : 2 * s = c + d := by linarith [not_lt.1 h2]
        have : u * D = D := by rw [← h2s, hDdef]; linarith
        have hu' : u = 1 := by
          have := mul_right_cancel₀ hD.ne' (this.trans (one_mul D).symm); exact this
        have hr' : Real.sqrt r = 0 := by rw [hr, heq, sub_self, zero_mul, Real.sqrt_zero]
        rw [hu', hr', sub_zero]
        exact trapezoidCDF_right hab hbc hcd had

/-- The Galois property of the sampling rule: for `u ∈ (0, 1)`,
`trap(u) ≤ x ↔ u ≤ F(x)`. -/
theorem trapezoidSample_le_iff (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (had : a < d) {u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) (x : ℝ) :
    trapezoidSample a b c d u ≤ x ↔ u ≤ trapezoidCDF a b c d x := by
  obtain ⟨hmem, hF⟩ := trapezoidSample_spec hab hbc hcd had ⟨hu.1.le, hu.2.le⟩
  constructor
  · intro h
    rw [← hF]; exact trapezoidCDF_monotone hab hbc hcd had h
  · intro h
    by_contra hlt
    rw [not_le] at hlt
    by_cases hxa : x < a
    · rw [trapezoidCDF_of_le hxa.le] at h; linarith [hu.1]
    · have := trapezoidCDF_strictMonoOn hab hbc hcd had ⟨not_lt.1 hxa, by linarith [hmem.2]⟩
        hmem hlt
      linarith

lemma measurable_trapezoidSample (a b c d : ℝ) : Measurable (trapezoidSample a b c d) := by
  unfold trapezoidSample
  refine Measurable.ite (measurableSet_lt (by fun_prop) measurable_const) (by fun_prop)
    (Measurable.ite (measurableSet_lt (by fun_prop) measurable_const) (by fun_prop)
      (by fun_prop))

/-- The trapezoidal distribution, defined as the law of the printed sampling rule applied to a
standard uniform draw. Its distribution function is `trapezoidCDF` (`cdf_trapezoidMeasure`), and
it is Lebesgue measure with density `trapezoidPDF` (`trapezoidMeasure_eq_withDensity`). -/
noncomputable def trapezoidMeasure (a b c d : ℝ) : Measure ℝ :=
  (volume.restrict (Ioo (0 : ℝ) 1)).map (trapezoidSample a b c d)

/-- The law produced by the printed sampling rule has distribution function `trapezoidCDF`
(Chapter 7: the rule is the inverse distribution function method of Equations 7.1 and 7.2 for
the trapezoid). -/
theorem trapezoidMeasure_Iic (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (had : a < d)
    (x : ℝ) :
    trapezoidMeasure a b c d (Iic x) = ENNReal.ofReal (trapezoidCDF a b c d x) := by
  have hm := measurable_trapezoidSample a b c d
  rw [trapezoidMeasure, Measure.map_apply hm measurableSet_Iic,
    Measure.restrict_apply (hm measurableSet_Iic)]
  have hF1 : trapezoidCDF a b c d x ≤ 1 := by
    rcases le_or_gt x d with h | h
    · rw [← trapezoidCDF_of_ge hab hbc hcd had (le_refl d)]
      exact trapezoidCDF_monotone hab hbc hcd had h
    · rw [trapezoidCDF_of_ge hab hbc hcd had h.le]
  have h : trapezoidSample a b c d ⁻¹' Iic x ∩ Ioo 0 1 =
      Ioo 0 1 ∩ Iic (trapezoidCDF a b c d x) := by
    ext u
    simp only [mem_inter_iff, mem_preimage, mem_Iic]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2, (trapezoidSample_le_iff hab hbc hcd had h2 x).1 h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨(trapezoidSample_le_iff hab hbc hcd had h1 x).2 h2, h1⟩
  rw [h]
  rcases hF1.lt_or_eq with hlt | heq
  · have : Ioo (0 : ℝ) 1 ∩ Iic (trapezoidCDF a b c d x) = Ioc 0 (trapezoidCDF a b c d x) := by
      ext u
      simp only [mem_inter_iff, mem_Ioo, mem_Iic, mem_Ioc]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by linarith⟩, h3⟩
    rw [this, Real.volume_Ioc, sub_zero]
  · rw [heq, inter_eq_left.2 (fun u (hu : u ∈ Ioo (0 : ℝ) 1) => (le_of_lt hu.2 : u ≤ 1)),
      Real.volume_Ioo, sub_zero]

instance (a b c d : ℝ) : IsProbabilityMeasure (trapezoidMeasure a b c d) := by
  have : IsProbabilityMeasure (volume.restrict (Ioo (0 : ℝ) 1)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioo, sub_zero,
      ENNReal.ofReal_one]⟩
  unfold trapezoidMeasure
  infer_instance

/-- The distribution function of the trapezoidal law is `trapezoidCDF`. -/
theorem cdf_trapezoidMeasure (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (had : a < d) :
    (cdf (trapezoidMeasure a b c d) : ℝ → ℝ) = trapezoidCDF a b c d := by
  funext x
  have h0 : 0 ≤ trapezoidCDF a b c d x := by
    rcases le_or_gt x a with h | h
    · rw [trapezoidCDF_of_le h]
    · rw [← trapezoidCDF_of_le (b := b) (c := c) (d := d) (le_refl a)]
      exact trapezoidCDF_monotone hab hbc hcd had h.le
  rw [cdf_eq_real, measureReal_def, trapezoidMeasure_Iic hab hbc hcd had,
    ENNReal.toReal_ofReal h0]

/-- The printed sampling rule is exactly the quantile function of the trapezoidal law on
`(0, 1)`. -/
theorem quantile_trapezoidMeasure (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (had : a < d)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    quantile (trapezoidMeasure a b c d) u = trapezoidSample a b c d u := by
  have key : ∀ x, quantile (trapezoidMeasure a b c d) u ≤ x ↔ trapezoidSample a b c d u ≤ x :=
    fun x => by
      rw [quantile_le_iff hu, trapezoidSample_le_iff hab hbc hcd had hu,
        cdf_trapezoidMeasure hab hbc hcd had]
  exact le_antisymm ((key _).2 le_rfl) ((key _).1 le_rfl)

/-- The trapezoidal density is the derivative of the trapezoidal distribution function on each
open piece `(a, b)`, `(b, c)`, `(c, d)`. -/
theorem hasDerivAt_trapezoidCDF (hab : a ≤ b) (hbc : b ≤ c) (_hcd : c ≤ d) (had : a < d)
    {x : ℝ} (hx : x ∈ Ioo a b ∪ Ioo b c ∪ Ioo c d) :
    HasDerivAt (trapezoidCDF a b c d) (trapezoidPDF a b c d x) x := by
  have hD : 0 < d + c - a - b := by linarith
  rcases hx with (hx | hx) | hx
  · have hba : 0 < b - a := by linarith [hx.1, hx.2]
    have hg : HasDerivAt (fun y => (y - a) ^ 2 / ((b - a) * (d + c - a - b)))
        ((2 : ℕ) * (x - a) ^ (2 - 1) * 1 / ((b - a) * (d + c - a - b))) x :=
      (((hasDerivAt_id x).sub_const a).pow 2).div_const _
    have hpdf : trapezoidPDF a b c d x = (2 : ℕ) * (x - a) ^ (2 - 1) * 1 /
        ((b - a) * (d + c - a - b)) := by
      rw [trapezoidPDF, ite_eq_right (not_lt.2 hx.1.le), ite_eq_left hx.2]
      field_simp; ring
    rw [hpdf]
    exact hg.congr_of_eventuallyEq (Filter.eventually_of_mem (Ioo_mem_nhds hx.1 hx.2)
      fun y hy => trapezoidCDF_lower (sub_pos.1 hba) ⟨hy.1.le, hy.2.le⟩)
  · have hg : HasDerivAt (fun y => (2 * y - a - b) / (d + c - a - b))
        (2 * 1 / (d + c - a - b)) x :=
      ((((hasDerivAt_id x).const_mul 2).sub_const a).sub_const b).div_const _
    have hpdf : trapezoidPDF a b c d x = 2 * 1 / (d + c - a - b) := by
      rw [trapezoidPDF, ite_eq_right (by linarith [hx.1] : ¬ x < a),
        ite_eq_right (not_lt.2 hx.1.le), ite_eq_left hx.2.le]
      ring
    rw [hpdf]
    exact hg.congr_of_eventuallyEq (Filter.eventually_of_mem (Ioo_mem_nhds hx.1 hx.2)
      fun y hy => trapezoidCDF_mid hab hbc had ⟨hy.1.le, hy.2.le⟩)
  · have hdc : 0 < d - c := by linarith [hx.1, hx.2]
    have hg : HasDerivAt (fun y => 1 - (d - y) ^ 2 / ((d - c) * (d + c - a - b)))
        (-((2 : ℕ) * (d - x) ^ (2 - 1) * (-1) / ((d - c) * (d + c - a - b)))) x :=
      (((((hasDerivAt_id x).const_sub d).pow 2).div_const _).const_sub 1)
    have hpdf : trapezoidPDF a b c d x =
        -((2 : ℕ) * (d - x) ^ (2 - 1) * (-1) / ((d - c) * (d + c - a - b))) := by
      rw [trapezoidPDF, ite_eq_right (by linarith [hx.1] : ¬ x < a),
        ite_eq_right (by linarith [hx.1] : ¬ x < b), ite_eq_right (not_le.2 hx.1),
        ite_eq_left hx.2]
      field_simp; ring
    rw [hpdf]
    exact hg.congr_of_eventuallyEq (Filter.eventually_of_mem (Ioo_mem_nhds hx.1 hx.2)
      fun y hy => trapezoidCDF_upper hab hbc (sub_pos.1 hdc) ⟨hy.1.le, hy.2.le⟩)

/-- The trapezoidal density is nonnegative for admissible parameters. -/
lemma trapezoidPDF_nonneg (hbc : b ≤ c) (had : a < d) (x : ℝ) :
    0 ≤ trapezoidPDF a b c d x := by
  have hh : 0 < 2 / (d + c - a - b) := div_pos two_pos (by linarith)
  unfold trapezoidPDF
  split_ifs with h1 h2 h3 h4
  · exact le_rfl
  · exact mul_nonneg hh.le (div_nonneg (by linarith) (by linarith))
  · exact hh.le
  · exact mul_nonneg hh.le (div_nonneg (by linarith) (by linarith))
  · exact le_rfl

/-- The trapezoidal density is bounded by its height `2 / D`. -/
lemma trapezoidPDF_le (hbc : b ≤ c) (had : a < d) (x : ℝ) :
    trapezoidPDF a b c d x ≤ 2 / (d + c - a - b) := by
  have hh : 0 < 2 / (d + c - a - b) := div_pos two_pos (by linarith)
  unfold trapezoidPDF
  split_ifs with h1 h2 h3 h4
  · exact hh.le
  · exact mul_le_of_le_one_right hh.le ((div_le_one (by linarith)).2 (by linarith))
  · exact le_rfl
  · exact mul_le_of_le_one_right hh.le ((div_le_one (by linarith)).2 (by linarith))
  · exact hh.le

/-- Between the modes the trapezoidal density equals its height `2 / D`, endpoints included. -/
lemma trapezoidPDF_of_mem_Icc (hab : a ≤ b) {x : ℝ} (hx : x ∈ Icc b c) :
    trapezoidPDF a b c d x = 2 / (d + c - a - b) := by
  rw [trapezoidPDF, ite_eq_right (by linarith [hx.1] : ¬ x < a), ite_eq_right (not_lt.2 hx.1),
    ite_eq_left hx.2]

/-- The maximum of the trapezoidal density is attained at every point of `[b, c]`, collapsed ramps
included: with `a = b = c` the mode `a` is attained. -/
theorem trapezoidPDF_le_mode (hab : a ≤ b) (hbc : b ≤ c) (had : a < d) (x : ℝ)
    {y : ℝ} (hy : y ∈ Icc b c) : trapezoidPDF a b c d x ≤ trapezoidPDF a b c d y := by
  rw [trapezoidPDF_of_mem_Icc hab hy]
  exact trapezoidPDF_le hbc had x

lemma measurable_trapezoidPDF (a b c d : ℝ) : Measurable (trapezoidPDF a b c d) := by
  unfold trapezoidPDF
  refine Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
    (Measurable.ite (measurableSet_lt measurable_id measurable_const) (by fun_prop)
      (Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const
        (Measurable.ite (measurableSet_lt measurable_id measurable_const) (by fun_prop)
          measurable_const)))

/-- The trapezoidal density is integrable on every bounded interval `(s, t]`. -/
lemma integrableOn_trapezoidPDF (hbc : b ≤ c) (had : a < d)
    (s t : ℝ) : IntegrableOn (trapezoidPDF a b c d) (Ioc s t) :=
  IntegrableOn.of_bound (by simp) (measurable_trapezoidPDF a b c d).aestronglyMeasurable
    (2 / (d + c - a - b)) (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (trapezoidPDF_nonneg hbc had x)]
      exact trapezoidPDF_le hbc had x)

/-- The trapezoidal distribution function is continuous, collapsed ramps included: the law has no
atoms, since the sampling rule meets each value at most at one level `u = F(x)`. -/
theorem continuous_trapezoidCDF (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (had : a < d) :
    Continuous (trapezoidCDF a b c d) := by
  rw [← cdf_trapezoidMeasure hab hbc hcd had]
  refine continuous_cdf_of_measure_singleton _ fun x => ?_
  have hm := measurable_trapezoidSample a b c d
  rw [trapezoidMeasure, Measure.map_apply hm (measurableSet_singleton x),
    Measure.restrict_apply (hm (measurableSet_singleton x))]
  refine measure_mono_null (t := {trapezoidCDF a b c d x}) ?_ (measure_singleton _)
  rintro u ⟨hu1, hu2⟩
  have h := (trapezoidSample_spec hab hbc hcd had ⟨hu2.1.le, hu2.2.le⟩).2
  rw [mem_preimage, mem_singleton_iff] at hu1
  rw [hu1] at h
  exact mem_singleton_iff.2 h.symm

/-- Away from the four break points the trapezoidal density is the derivative of the
distribution function (it is `0` outside `[a, d]`). -/
lemma hasDerivAt_trapezoidCDF_of_ne (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (had : a < d)
    {x : ℝ} (ha : x ≠ a) (hb : x ≠ b) (hc : x ≠ c) (hd : x ≠ d) :
    HasDerivAt (trapezoidCDF a b c d) (trapezoidPDF a b c d x) x := by
  rcases lt_or_gt_of_ne ha with hxa | hxa
  · have hp : trapezoidPDF a b c d x = 0 := by rw [trapezoidPDF, ite_eq_left hxa]
    rw [hp]
    exact (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
      (Filter.eventually_of_mem (Iio_mem_nhds hxa) fun y hy => trapezoidCDF_of_le (le_of_lt hy))
  rcases lt_or_gt_of_ne hd with hxd | hxd
  · apply hasDerivAt_trapezoidCDF hab hbc hcd had
    rcases lt_or_gt_of_ne hb with hxb | hxb
    · exact Or.inl (Or.inl ⟨hxa, hxb⟩)
    rcases lt_or_gt_of_ne hc with hxc | hxc
    · exact Or.inl (Or.inr ⟨hxb, hxc⟩)
    · exact Or.inr ⟨hxc, hxd⟩
  · have hp : trapezoidPDF a b c d x = 0 := by
      rw [trapezoidPDF, ite_eq_right (by linarith : ¬ x < a), ite_eq_right (by linarith : ¬ x < b),
        ite_eq_right (by linarith : ¬ x ≤ c), ite_eq_right (by linarith : ¬ x < d)]
    rw [hp]
    exact (hasDerivAt_const x (1 : ℝ)).congr_of_eventuallyEq
      (Filter.eventually_of_mem (Ioi_mem_nhds hxd) fun y hy =>
        trapezoidCDF_of_ge hab hbc hcd had (le_of_lt hy))

/-- The trapezoidal density integrates to the increments of the distribution function:
`∫_s^t f = F(t) - F(s)` for `s ≤ t`. -/
theorem integral_trapezoidPDF (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (had : a < d)
    {s t : ℝ} (hst : s ≤ t) :
    ∫ x in s..t, trapezoidPDF a b c d x = trapezoidCDF a b c d t - trapezoidCDF a b c d s := by
  refine integral_eq_of_hasDerivAt_off_countable_of_le _ _ hst (s := {a, b, c, d})
    ((((countable_singleton d).insert c).insert b).insert a)
    (continuous_trapezoidCDF hab hbc hcd had).continuousOn (fun x hx => ?_)
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hst).2
      (integrableOn_trapezoidPDF hbc had s t))
  have h := hx.2
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at h
  exact hasDerivAt_trapezoidCDF_of_ne hab hbc hcd had h.1 h.2.1 h.2.2.1 h.2.2.2

/-- The trapezoidal density integrates to one. -/
theorem integral_trapezoidPDF_eq_one (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (had : a < d) :
    ∫ x in a..d, trapezoidPDF a b c d x = 1 := by
  rw [integral_trapezoidPDF hab hbc hcd had had.le, trapezoidCDF_right hab hbc hcd had,
    trapezoidCDF_left, sub_zero]

/-- The law produced by the printed sampling rule is Lebesgue measure with density `trapezoidPDF`
(Chapter 7, "Trapezoidal Distribution"), for all ordered endpoints with `a < d`, collapsed ramps
included. -/
theorem trapezoidMeasure_eq_withDensity (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (had : a < d) :
    trapezoidMeasure a b c d =
      volume.withDensity (fun x => ENNReal.ofReal (trapezoidPDF a b c d x)) := by
  refine Measure.ext_of_Ioc _ _ fun s t hst => ?_
  rw [← measure_cdf (trapezoidMeasure a b c d), StieltjesFunction.measure_Ioc,
    cdf_trapezoidMeasure hab hbc hcd had, withDensity_apply _ measurableSet_Ioc,
    ← ofReal_integral_eq_lintegral_ofReal (integrableOn_trapezoidPDF hbc had s t)
      (ae_of_all _ fun x => trapezoidPDF_nonneg hbc had x),
    ← intervalIntegral.integral_of_le hst.le, integral_trapezoidPDF hab hbc hcd had hst.le]

/-- Special case (Chapter 7): with `a = b` and `c = d` the printed rule is the affine draw
`a + u (d - a)` of the uniform distribution. -/
lemma trapezoidSample_uniform (had : a < d) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    trapezoidSample a a d d u = a + u * (d - a) := by
  obtain ⟨hu0, hu1⟩ := hu
  have hs : (a + a + u * (d + d - a - a)) / 2 = a + u * (d - a) := by ring
  unfold trapezoidSample
  rw [hs, ite_eq_right (by nlinarith : ¬ a + u * (d - a) < a)]
  by_cases h : a + u * (d - a) < d
  · rw [ite_eq_left h]
  · rw [ite_eq_right h]
    have : a + u * (d - a) = d := by nlinarith
    rw [this]; simp

/-- Special case (Chapter 7): the trapezoid with `a = b` and `c = d` is the uniform
distribution on `[a, d]`. -/
theorem trapezoidMeasure_uniform (had : a < d) : trapezoidMeasure a a d d = volume[|Icc a d] := by
  rw [← map_affine_cond_Icc had, cond_Icc_zero_one, trapezoidMeasure]
  refine Measure.map_congr ((ae_restrict_iff' measurableSet_Ioo).2
    (Filter.Eventually.of_forall fun u hu => trapezoidSample_uniform had ⟨hu.1.le, hu.2.le⟩))

/-- The triangular density with minimum `a`, mode `m` and maximum `d` (Chapter 7, "Triangular
Distribution"): rising linearly from `0` at `a` to the peak `2 / (d - a)` at `m`, then falling
linearly to `0` at `d`; the peak value is taken at `m` also when `m = a` or `m = d`. -/
noncomputable def triangularPDF (a m d x : ℝ) : ℝ :=
  if x < a then 0
  else if x < m then 2 * (x - a) / ((d - a) * (m - a))
  else if x ≤ m then 2 / (d - a)
  else if x < d then 2 * (d - x) / ((d - a) * (d - m))
  else 0

/-- Special case (Chapter 7): the trapezoid with equal modes `b = c = m` is the triangular
distribution. -/
theorem trapezoidPDF_eq_triangularPDF (a m d x : ℝ) :
    trapezoidPDF a m m d x = triangularPDF a m d x := by
  have hD : d + m - a - m = d - a := by ring
  unfold trapezoidPDF triangularPDF
  rw [hD]
  split_ifs <;> first | rfl | rw [div_mul_div_comm]

/-- The triangular law (Chapter 7, "Triangular Distribution"): for `a ≤ m ≤ d` with `a < d`, the
trapezoidal law with equal modes `b = c = m` is Lebesgue measure with the triangular density,
including the right triangles `m = a` and `m = d`. -/
theorem trapezoidMeasure_eq_withDensity_triangularPDF {m : ℝ} (ham : a ≤ m) (hmd : m ≤ d)
    (had : a < d) :
    trapezoidMeasure a m m d =
      volume.withDensity (fun x => ENNReal.ofReal (triangularPDF a m d x)) := by
  rw [trapezoidMeasure_eq_withDensity ham le_rfl hmd had]
  simp_rw [trapezoidPDF_eq_triangularPDF]

/-- Symmetry of the trapezoidal distribution function when `b - a = d - c`:
`F(a + d - x) = 1 - F(x)` on `[a, d]`. -/
lemma trapezoidCDF_symm (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (had : a < d)
    (hsym : b - a = d - c) {x : ℝ} (hx : x ∈ Icc a d) :
    trapezoidCDF a b c d (a + d - x) = 1 - trapezoidCDF a b c d x := by
  have hD : 0 < d + c - a - b := by linarith
  obtain ⟨h1, h2⟩ := hx
  by_cases hxb : x ≤ b
  · rcases hab.lt_or_eq with hlt | hab'
    · rw [trapezoidCDF_upper hab hbc (by linarith) ⟨by linarith, by linarith⟩,
        trapezoidCDF_lower hlt ⟨h1, hxb⟩, show d - (a + d - x) = x - a by ring, ← hsym]
    · have hxa : x = a := by linarith
      rw [hxa, show a + d - a = d by ring, trapezoidCDF_right hab hbc hcd had,
        trapezoidCDF_left]
      ring
  by_cases hxc : x ≤ c
  · rw [trapezoidCDF_mid hab hbc had ⟨by linarith, by linarith⟩,
      trapezoidCDF_mid hab hbc had ⟨by linarith, hxc⟩]
    field_simp
    linarith
  · rw [trapezoidCDF_lower (by linarith) ⟨by linarith, by linarith⟩,
      trapezoidCDF_upper hab hbc (by linarith) ⟨by linarith, h2⟩,
      show a + d - x - a = d - x by ring,
      hsym]
    ring

/-- Mean of a symmetric trapezoid (Chapter 7, used for the participation priors of Chapter 12):
if `b - a = d - c`, the trapezoidal law has mean `(b + c) / 2`. -/
theorem integral_id_trapezoidMeasure (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (had : a < d)
    (hsym : b - a = d - c) :
    ∫ x, x ∂(trapezoidMeasure a b c d) = (b + c) / 2 := by
  set Q := trapezoidSample a b c d with hQ
  have hm : Measurable Q := measurable_trapezoidSample a b c d
  have hspec := fun u (hu : u ∈ Icc (0 : ℝ) 1) => trapezoidSample_spec hab hbc hcd had hu
  -- Reflection: `Q (1 - u) = a + d - Q u` on `[0, 1]`.
  have hrefl : ∀ u ∈ Icc (0 : ℝ) 1, Q (1 - u) = a + d - Q u := by
    intro u hu
    have hu' : 1 - u ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hu.2], by linarith [hu.1]⟩
    obtain ⟨hmem, hF⟩ := hspec u hu
    obtain ⟨hmem', hF'⟩ := hspec (1 - u) hu'
    have hmem'' : a + d - Q u ∈ Icc a d := ⟨by linarith [hmem.2], by linarith [hmem.1]⟩
    apply (trapezoidCDF_strictMonoOn hab hbc hcd had).injOn hmem' hmem''
    rw [hF', trapezoidCDF_symm hab hbc hcd had hsym hmem, hF]
  have hint : IntervalIntegrable Q volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    refine IntegrableOn.of_bound (by simp) hm.aestronglyMeasurable (max |a| |d|)
      ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun u hu => ?_))
    obtain ⟨h1, h2⟩ := (hspec u ⟨hu.1.le, hu.2⟩).1
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · linarith [le_max_left |a| |d|, neg_abs_le a]
    · linarith [le_max_right |a| |d|, le_abs_self d]
  have hint' : IntervalIntegrable (fun u => Q (1 - u)) volume 0 1 := by
    simpa using (hint.comp_sub_left 1).symm
  have hI : ∫ x, x ∂(trapezoidMeasure a b c d) = ∫ u in (0 : ℝ)..1, Q u := by
    rw [trapezoidMeasure, ← hQ,
      integral_map (f := fun x : ℝ => x) hm.aemeasurable (by fun_prop),
      intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  have hsum : ∫ u in (0 : ℝ)..1, (Q u + Q (1 - u)) = a + d := by
    rw [intervalIntegral.integral_congr (g := fun _ => a + d) fun u hu => by
      rw [uIcc_of_le zero_le_one] at hu
      simp only [hrefl u hu]; ring]
    simp
  rw [intervalIntegral.integral_add hint hint', intervalIntegral.integral_comp_sub_left Q 1,
    sub_self, sub_zero] at hsum
  rw [hI]
  linarith

end Trapezoid

section Examples

/-- Chapter 7, "Uniform Distribution": the uniform density for sensitivity between `0.70` and
`0.95` is `1/(0.95 - 0.70) = 4`. -/
theorem uniform_example {x : ℝ} (hx : x ∈ Icc (0.70 : ℝ) 0.95) :
    pdf.uniformPDF (Icc (0.70 : ℝ) 0.95) x = 4 := by
  rw [uniformPDF_Icc (by norm_num) hx]
  norm_num

/-- Chapter 7, "Beta Distribution": the validation counts `15` and `2` give `Beta(15, 2)`, with
mean `15/17 ≈ 0.88` and variance `5/867`, so standard deviation `√(5/867) ≈ 0.076`, printed as
`0.08`. -/
theorem beta_15_2 :
    ∫ x, x ∂(betaMeasure 15 2) = 15 / 17 ∧
      ∫ x, (x - 15 / 17) ^ 2 ∂(betaMeasure 15 2) = 5 / 867 ∧
      0.075 < Real.sqrt (5 / 867) ∧ Real.sqrt (5 / 867) < 0.077 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [integral_id_betaMeasure (by norm_num) (by norm_num)]; norm_num
  · have h := integral_sub_sq_betaMeasure (α := 15) (β := 2) (by norm_num) (by norm_num)
    norm_num at h ⊢; exact h
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- Chapter 7: adding one to each count gives `Beta(16, 3)`, with mean `16/19 ≈ 0.84` and
variance `12/1805`, so standard deviation about `0.082`, printed as `0.08`. -/
theorem beta_16_3 :
    ∫ x, x ∂(betaMeasure 16 3) = 16 / 19 ∧
      ∫ x, (x - 16 / 19) ^ 2 ∂(betaMeasure 16 3) = 12 / 1805 ∧
      0.081 < Real.sqrt (12 / 1805) ∧ Real.sqrt (12 / 1805) < 0.082 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [integral_id_betaMeasure (by norm_num) (by norm_num)]; norm_num
  · have h := integral_sub_sq_betaMeasure (α := 16) (β := 3) (by norm_num) (by norm_num)
    norm_num at h ⊢; exact h
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- Chapter 7, choosing `α` and `β` from the range `[0.70, 0.98]` and mean `0.88`: Equation 7.4
gives `sd = (0.98 - 0.70)/(2 · 1.96) = 1/14`, printed as `0.07`. With the unrounded `1/14` the
formulas give `α ≈ 17.33` and `β ≈ 2.36`, the printed `17.3` and `2.4`. With the rounded `0.07`
they would give `α ≈ 18.08` and `β ≈ 2.47` instead, so the printed values use the unrounded
standard deviation. -/
theorem beta_parameters_example :
    (0.98 - 0.70) / (2 * 1.96) = (1 / 14 : ℝ) ∧
      (17.3 : ℝ) < 0.88 * (0.88 * (1 - 0.88) / (1 / 14) ^ 2 - 1) ∧
      0.88 * (0.88 * (1 - 0.88) / (1 / 14) ^ 2 - 1) < (17.35 : ℝ) ∧
      (2.35 : ℝ) < (1 - 0.88) * (0.88 * (1 - 0.88) / (1 / 14) ^ 2 - 1) ∧
      (1 - 0.88) * (0.88 * (1 - 0.88) / (1 / 14) ^ 2 - 1) < (2.45 : ℝ) ∧
      (18 : ℝ) < 0.88 * (0.88 * (1 - 0.88) / 0.07 ^ 2 - 1) ∧
      2.45 < (1 - 0.88) * (0.88 * (1 - 0.88) / 0.07 ^ 2 - (1 : ℝ)) := by
  norm_num

/-- The partial sum `∑_{m < 10} y^m / m!` of the exponential series, used for certified bounds. -/
noncomputable def expPartialSum (y : ℝ) : ℝ := ∑ m ∈ Finset.range 10, y ^ m / m.factorial

lemma expPartialSum_le_exp {y : ℝ} (hy : 0 ≤ y) : expPartialSum y ≤ Real.exp y :=
  Real.sum_le_exp_of_nonneg hy 10

lemma exp_le_expPartialSum_add {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) :
    Real.exp y ≤ expPartialSum y + y ^ 10 * (10 + 1) / (Nat.factorial 10 * 10) := by
  have h := Real.exp_bound' h0 h1 (n := 10) (by norm_num)
  simpa [expPartialSum] using h

lemma expPartialSum_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ expPartialSum y :=
  Finset.sum_nonneg fun _ _ => by positivity

lemma exp_four_mul_le {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) :
    Real.exp (4 * y) ≤ (expPartialSum y + y ^ 10 * (10 + 1) / (Nat.factorial 10 * 10)) ^ 4 := by
  rw [show (4 : ℝ) * y = ((4 : ℕ) : ℝ) * y by norm_num, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Real.exp_pos y).le (exp_le_expPartialSum_add h0 h1) 4

lemma expPartialSum_pow_le {y : ℝ} (h0 : 0 ≤ y) : expPartialSum y ^ 4 ≤ Real.exp (4 * y) := by
  rw [show (4 : ℝ) * y = ((4 : ℕ) : ℝ) * y by norm_num, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (expPartialSum_nonneg h0) (expPartialSum_le_exp h0) 4

/-- `t < expit(x)` as soon as `t / (1 - t) < exp x`. -/
lemma lt_sigmoid_of_lt_exp {x t : ℝ} (ht1 : t < 1) (h : t / (1 - t) < Real.exp x) :
    t < Real.sigmoid x := by
  have hE := Real.exp_pos x
  rw [div_lt_iff₀ (by linarith)] at h
  rw [Real.sigmoid_def, Real.exp_neg,
    show (1 + (Real.exp x)⁻¹) = (Real.exp x + 1) / Real.exp x by
      rw [add_div, div_self hE.ne', one_div],
    inv_div, lt_div_iff₀ (by positivity)]
  nlinarith

/-- `expit(x) < t` as soon as `exp x < t / (1 - t)`. -/
lemma sigmoid_lt_of_exp_lt {x t : ℝ} (ht1 : t < 1) (h : Real.exp x < t / (1 - t)) :
    Real.sigmoid x < t := by
  have hE := Real.exp_pos x
  rw [lt_div_iff₀ (by linarith)] at h
  rw [Real.sigmoid_def, Real.exp_neg,
    show (1 + (Real.exp x)⁻¹) = (Real.exp x + 1) / Real.exp x by
      rw [add_div, div_self hE.ne', one_div],
    inv_div, div_lt_iff₀ (by positivity)]
  nlinarith

/-- Chapter 7, "Normal Distribution": the odds ratio `0.61` with 95% interval `[0.40, 0.92]`
gives, by Equation 7.4 on the log scale, `sd = (ln 0.92 - ln 0.40)/(2 · 1.96)`, with value in
`(0.21247, 0.21248)`, printed as `0.21`. -/
theorem logNormal_sd_example :
    0.21247 < (Real.log 0.92 - Real.log 0.40) / (2 * 1.96) ∧
      (Real.log 0.92 - Real.log 0.40) / (2 * 1.96) < 0.21248 := by
  have hlog : Real.log 0.92 - Real.log 0.40 = Real.log 2.3 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
  rw [hlog, lt_div_iff₀ (by norm_num), div_lt_iff₀ (by norm_num),
    Real.lt_log_iff_exp_lt (by norm_num), Real.log_lt_iff_lt_exp (by norm_num)]
  constructor
  · refine lt_of_le_of_lt (exp_le_expPartialSum_add (by norm_num) (by norm_num)) ?_
    norm_num [expPartialSum, Finset.sum_range_succ, Nat.factorial]
  · refine lt_of_lt_of_le ?_ (expPartialSum_le_exp (by norm_num))
    norm_num [expPartialSum, Finset.sum_range_succ, Nat.factorial]

/-- Chapter 7, "Normal Distribution": the positive predictive value `0.95` with 95% interval
`[0.88, 0.98]` gives the logit scale mean `logit(0.95) = ln 19`, printed as `2.94`, and by
Equation 7.4 `sd = (logit(0.98) - logit(0.88))/(2 · 1.96)`, printed as `0.48`. -/
theorem logitNormal_parameters_example :
    2.94 < Real.log (0.95 / (1 - 0.95)) ∧ Real.log (0.95 / (1 - 0.95)) < 2.95 ∧
      0.48 < (Real.log (0.98 / (1 - 0.98)) - Real.log (0.88 / (1 - 0.88))) / (2 * 1.96) ∧
      (Real.log (0.98 / (1 - 0.98)) - Real.log (0.88 / (1 - 0.88))) / (2 * 1.96) < 0.49 := by
  have hsd : Real.log (0.98 / (1 - 0.98)) - Real.log (0.88 / (1 - 0.88)) =
      Real.log (147 / 22) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
  rw [hsd, lt_div_iff₀ (by norm_num), div_lt_iff₀ (by norm_num),
    Real.lt_log_iff_exp_lt (by norm_num), Real.log_lt_iff_lt_exp (by norm_num),
    Real.lt_log_iff_exp_lt (by norm_num), Real.log_lt_iff_lt_exp (by norm_num)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show (2.94 : ℝ) = 4 * 0.735 by norm_num]
    refine lt_of_le_of_lt (exp_four_mul_le (by norm_num) (by norm_num)) ?_
    norm_num [expPartialSum, Finset.sum_range_succ, Nat.factorial]
  · rw [show (2.95 : ℝ) = 4 * 0.7375 by norm_num]
    refine lt_of_lt_of_le ?_ (expPartialSum_pow_le (by norm_num))
    norm_num [expPartialSum, Finset.sum_range_succ, Nat.factorial]
  · rw [show (0.48 : ℝ) * (2 * 1.96) = 4 * 0.47040 by norm_num]
    refine lt_of_le_of_lt (exp_four_mul_le (by norm_num) (by norm_num)) ?_
    norm_num [expPartialSum, Finset.sum_range_succ, Nat.factorial]
  · rw [show (0.49 : ℝ) * (2 * 1.96) = 4 * 0.48020 by norm_num]
    refine lt_of_lt_of_le ?_ (expPartialSum_pow_le (by norm_num))
    norm_num [expPartialSum, Finset.sum_range_succ, Nat.factorial]

/-- Chapter 7, "Normal Distribution": for `logit(PPV) ~ N(2.94, 0.48²)` the quantiles of the
positive predictive value at the levels `Φ(-1.96)`, `Φ(0)` and `Φ(1.96)` (about 2.5%, 50% and
97.5%) are `expit(2.94 + 0.48 z)`, in `(0.8807, 0.8808)`, `(0.9497, 0.9498)` and
`(0.9797, 0.9798)`; the book prints `0.88`, `0.95` and `0.98` from simulation. The levels are the
exact values `Φ(±1.96)`, not `0.025` and `0.975`. -/
theorem logitNormal_quantiles_example :
    let μ := (gaussianReal 2.94 (Real.toNNReal (0.48 ^ 2))).map Real.sigmoid
    (0.8807 < quantile μ (cdf (gaussianReal 0 1) (-1.96)) ∧
      quantile μ (cdf (gaussianReal 0 1) (-1.96)) < 0.8808) ∧
    (0.9497 < quantile μ (cdf (gaussianReal 0 1) 0) ∧
      quantile μ (cdf (gaussianReal 0 1) 0) < 0.9498) ∧
    (0.9797 < quantile μ (cdf (gaussianReal 0 1) 1.96) ∧
      quantile μ (cdf (gaussianReal 0 1) 1.96) < 0.9798) := by
  intro μ
  simp only [μ, quantile_logitNormal 2.94 (by norm_num : (0 : ℝ) < 0.48)
    (Real.coe_toNNReal _ (by positivity))]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · refine lt_sigmoid_of_lt_exp (by norm_num) (lt_of_lt_of_le ?_
      ((show (2.94 : ℝ) + 0.48 * -1.96 = 4 * 0.4998 by norm_num) ▸
        expPartialSum_pow_le (by norm_num)))
    norm_num [expPartialSum, Finset.sum_range_succ, Nat.factorial]
  · refine sigmoid_lt_of_exp_lt (by norm_num) (lt_of_le_of_lt
      ((show (2.94 : ℝ) + 0.48 * -1.96 = 4 * 0.4998 by norm_num) ▸
        exp_four_mul_le (by norm_num) (by norm_num)) ?_)
    norm_num [expPartialSum, Finset.sum_range_succ, Nat.factorial]
  · refine lt_sigmoid_of_lt_exp (by norm_num) (lt_of_lt_of_le ?_
      ((show (2.94 : ℝ) + 0.48 * 0 = 4 * 0.735 by norm_num) ▸
        expPartialSum_pow_le (by norm_num)))
    norm_num [expPartialSum, Finset.sum_range_succ, Nat.factorial]
  · refine sigmoid_lt_of_exp_lt (by norm_num) (lt_of_le_of_lt
      ((show (2.94 : ℝ) + 0.48 * 0 = 4 * 0.735 by norm_num) ▸
        exp_four_mul_le (by norm_num) (by norm_num)) ?_)
    norm_num [expPartialSum, Finset.sum_range_succ, Nat.factorial]
  · refine lt_sigmoid_of_lt_exp (by norm_num) (lt_of_lt_of_le ?_
      ((show (2.94 : ℝ) + 0.48 * 1.96 = 4 * 0.9702 by norm_num) ▸
        expPartialSum_pow_le (by norm_num)))
    norm_num [expPartialSum, Finset.sum_range_succ, Nat.factorial]
  · refine sigmoid_lt_of_exp_lt (by norm_num) (lt_of_le_of_lt
      ((show (2.94 : ℝ) + 0.48 * 1.96 = 4 * 0.9702 by norm_num) ▸
        exp_four_mul_le (by norm_num) (by norm_num)) ?_)
    norm_num [expPartialSum, Finset.sum_range_succ, Nat.factorial]

end Examples

end Distributions

end BiasAnalysis

end CausalInference
