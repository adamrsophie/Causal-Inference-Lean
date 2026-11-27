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
* Normal distribution: `hasLaw_normal_draw` (Equation 7.3) and `se_eq_of_waldIntervalSE`
  (Equation 7.4, inverting a Wald interval built with `waldIntervalSE`).
* Inverse distribution function sampling (Equations 7.1 and 7.2): the generalized inverse
  `quantile`, its Galois property `quantile_le_iff`, `map_quantile_uniform` and
  `IsUniform.hasLaw_quantile`; the probability integral transform `map_cdf_eq_uniform` for a
  continuous distribution function, with the counterexample `map_cdf_dirac_ne_uniform` for a
  point mass; `quantile_map` (quantiles commute with continuous strictly
  increasing maps such as the logit back transformation); `hasLaw_quantile_cdf` and
  `hasLaw_quantile_cdf_gaussian`, the marginal step of the NORTA construction of "Correlated
  Distributions" (Equation 7.7).
* Trapezoidal distribution: the distribution function `trapezoidCDF`, density `trapezoidPDF`
  (`hasDerivAt_trapezoidCDF`), the printed sampling rule `trapezoidSample`, and the law
  `trapezoidMeasure` it produces from a standard uniform draw. `trapezoidSample_spec` and
  `quantile_trapezoidMeasure` show that the printed rule is exactly the quantile function, and
  `cdf_trapezoidMeasure` identifies the distribution function; that the law has density
  `trapezoidPDF` is shown only through the derivative on the open pieces. Special cases:
  `trapezoidMeasure_uniform` (`a = b`, `c = d` gives the uniform law),
  `trapezoidPDF_eq_triangularPDF` (`b = c` gives the triangular density) and
  `integral_id_trapezoidMeasure` (a symmetric trapezoid has mean `(b + c)/2`).
* `Examples`: the uniform density `4` on `[0.70, 0.95]`, `Beta(15, 2)` and `Beta(16, 3)`
  (means and standard deviations printed in the chapter) and the choice `α ≈ 17.3`,
  `β ≈ 2.4` from the range `[0.70, 0.98]`.

The bivariate normal correlation of the NORTA construction only enters through the marginals;
the size of the induced correlation is not formalized. The printed numerical quantiles of the
logit normal and log normal examples (for instance `logit(0.95) = 2.94`, `sd = 0.21`) involve
logarithms and are not checked here.
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
transformed pair has the target marginals whatever the dependence of `(Z₁, Z₂)`. The size of the
induced correlation is not a theorem here. -/
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
rising (or falling) ramp is empty and its formula is never evaluated. -/

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
`b` and falling linearly from `c` to `d`. -/
noncomputable def trapezoidPDF (a b c d x : ℝ) : ℝ :=
  if x ≤ a then 0
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

lemma trapezoidCDF_lower {x : ℝ} (hx : x ∈ Icc a b) :
    trapezoidCDF a b c d x = (x - a) ^ 2 / ((b - a) * (d + c - a - b)) := by
  obtain ⟨h1, h2⟩ := hx
  unfold trapezoidCDF
  by_cases hxa : x ≤ a
  · have : x = a := le_antisymm hxa h1
    subst this; simp
  · rw [ite_eq_right hxa, ite_eq_left h2]

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

lemma trapezoidCDF_upper (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (had : a < d) {x : ℝ}
    (hx : x ∈ Icc c d) :
    trapezoidCDF a b c d x = 1 - (d - x) ^ 2 / ((d - c) * (d + c - a - b)) := by
  obtain ⟨h1, h2⟩ := hx
  have hD : 0 < d + c - a - b := by linarith
  by_cases hxc : x ≤ c
  · have hxc' : x = c := le_antisymm hxc h1
    subst hxc'
    rw [trapezoidCDF_mid hab hbc had ⟨hbc, le_rfl⟩]
    rcases hcd.lt_or_eq with hlt | heq
    · have : 0 < d - x := sub_pos.2 hlt
      field_simp
      ring
    · subst heq
      have : (2 * x - a - b) / (x + x - a - b) = 1 := by rw [div_eq_one_iff_eq hD.ne']; ring
      rw [this]; simp
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
  · rw [trapezoidCDF_upper hab hbc hcd had ⟨by linarith, heq.ge⟩, heq]; simp

/-- The trapezoidal distribution function is strictly increasing on `[a, d]`. -/
theorem trapezoidCDF_strictMonoOn (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (had : a < d) :
    StrictMonoOn (trapezoidCDF a b c d) (Icc a d) := by
  have hD : 0 < d + c - a - b := by linarith
  have h1 : StrictMonoOn (trapezoidCDF a b c d) (Icc a b) := by
    intro x hx y hy hxy
    rw [trapezoidCDF_lower hx, trapezoidCDF_lower hy]
    have hba : 0 < b - a := by linarith [hx.1, hy.2]
    apply div_lt_div_of_pos_right _ (by positivity)
    nlinarith [hx.1]
  have h2 : StrictMonoOn (trapezoidCDF a b c d) (Icc b c) := by
    intro x hx y hy hxy
    rw [trapezoidCDF_mid hab hbc had hx, trapezoidCDF_mid hab hbc had hy]
    apply div_lt_div_of_pos_right _ hD
    linarith
  have h3 : StrictMonoOn (trapezoidCDF a b c d) (Icc c d) := by
    intro x hx y hy hxy
    rw [trapezoidCDF_upper hab hbc hcd had hx, trapezoidCDF_upper hab hbc hcd had hy]
    have hdc : 0 < d - c := by linarith [hx.1, hy.2]
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
    rw [trapezoidCDF_lower hmem, add_sub_cancel_left, Real.sq_sqrt hr0, hr, ← hDdef, h2s]
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
      rw [trapezoidCDF_upper hab hbc hcd had hmem, sub_sub_cancel, Real.sq_sqrt hr0, hr, ← hDdef]
      rcases hcd.lt_or_eq with hlt | heq
      · have : 0 < d - c := sub_pos.2 hlt
        field_simp
        linear_combination (-1 : ℝ) * h2s
      · have hsd : 2 * s = c + d := by linarith [not_lt.1 h2]
        have : u * D = D := by rw [← h2s, hDdef]; linarith
        have hu' : u = 1 := by
          have := mul_right_cancel₀ hD.ne' (this.trans (one_mul D).symm); exact this
        rw [hu', ← heq]; simp

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
standard uniform draw. Its distribution function is `trapezoidCDF` (`cdf_trapezoidMeasure`),
whose derivative on the open pieces is `trapezoidPDF` (`hasDerivAt_trapezoidCDF`); that the
measure equals Lebesgue measure with density `trapezoidPDF` is not stated here. -/
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
theorem hasDerivAt_trapezoidCDF (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (had : a < d)
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
      rw [trapezoidPDF, ite_eq_right (not_le.2 hx.1), ite_eq_left hx.2]
      field_simp; ring
    rw [hpdf]
    exact hg.congr_of_eventuallyEq (Filter.eventually_of_mem (Ioo_mem_nhds hx.1 hx.2)
      fun y hy => trapezoidCDF_lower ⟨hy.1.le, hy.2.le⟩)
  · have hg : HasDerivAt (fun y => (2 * y - a - b) / (d + c - a - b))
        (2 * 1 / (d + c - a - b)) x :=
      ((((hasDerivAt_id x).const_mul 2).sub_const a).sub_const b).div_const _
    have hpdf : trapezoidPDF a b c d x = 2 * 1 / (d + c - a - b) := by
      rw [trapezoidPDF, ite_eq_right (by linarith [hx.1] : ¬ x ≤ a),
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
      rw [trapezoidPDF, ite_eq_right (by linarith [hx.1] : ¬ x ≤ a),
        ite_eq_right (by linarith [hx.1] : ¬ x < b), ite_eq_right (not_le.2 hx.1),
        ite_eq_left hx.2]
      field_simp; ring
    rw [hpdf]
    exact hg.congr_of_eventuallyEq (Filter.eventually_of_mem (Ioo_mem_nhds hx.1 hx.2)
      fun y hy => trapezoidCDF_upper hab hbc hcd had ⟨hy.1.le, hy.2.le⟩)

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
linearly to `0` at `d`. -/
noncomputable def triangularPDF (a m d x : ℝ) : ℝ :=
  if x ≤ a then 0
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

/-- Symmetry of the trapezoidal distribution function when `b - a = d - c`:
`F(a + d - x) = 1 - F(x)` on `[a, d]`. -/
lemma trapezoidCDF_symm (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (had : a < d)
    (hsym : b - a = d - c) {x : ℝ} (hx : x ∈ Icc a d) :
    trapezoidCDF a b c d (a + d - x) = 1 - trapezoidCDF a b c d x := by
  have hD : 0 < d + c - a - b := by linarith
  obtain ⟨h1, h2⟩ := hx
  by_cases hxb : x ≤ b
  · rw [trapezoidCDF_upper hab hbc hcd had ⟨by linarith, by linarith⟩,
      trapezoidCDF_lower ⟨h1, hxb⟩, show d - (a + d - x) = x - a by ring, ← hsym]
  by_cases hxc : x ≤ c
  · rw [trapezoidCDF_mid hab hbc had ⟨by linarith, by linarith⟩,
      trapezoidCDF_mid hab hbc had ⟨by linarith, hxc⟩]
    field_simp
    linarith
  · rw [trapezoidCDF_lower ⟨by linarith, by linarith⟩,
      trapezoidCDF_upper hab hbc hcd had ⟨by linarith, h2⟩, show a + d - x - a = d - x by ring,
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

end Examples

end Distributions

end BiasAnalysis

end CausalInference
