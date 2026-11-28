/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.BiasAnalysis.Distributions
public import CausalInference.Measures.LinkScale
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Aggregation on the probit scale with a Gaussian covariate

Write `Φ = cdf (gaussianReal 0 1)` for the standard normal distribution function and
`probit = quantile (gaussianReal 0 1)` for its inverse, the probit link.

* **The Gaussian probit integral** (`integral_cdf_gaussianReal`, `HasLaw.integral_cdf_affine`):
  if `X ∼ N(m, s)` then `E Φ(a + b X) = Φ((a + b m) / √(1 + b² s))`. The proof writes
  `E Φ(W)` with `W ∼ N(μ, τ)` as the probability that `U ≤ W` for an independent standard normal
  `U`, a convolution of two Gaussians.
* **The probit link inverts `Φ`** (`probit_cdf`), and `Φ` is strictly increasing
  (`strictMono_cdf_gaussianReal`), with values in `(0, 1)`.
* **The aggregate probit contrast** (`linkMarginal_probit_gaussian`): with arm risks
  `Φ(a_t + ρ_t x)` and `X ∼ N(m, s)`, the marginal probit contrast is `c + b₂ m` with the
  ecological slope `b₂ = h(ρ₁) - h(ρ₀)`, `h(ρ) = ρ / √(1 + ρ² s)`.
* **Attenuation.** The factor `1 / √(1 + b² s)` lies in `(0, 1]` and equals one iff `b = 0` or
  `s = 0` (`probitAttenuation_eq_one_iff`); the slope of a single arm on the probit scale of the
  aggregate is `b / √(1 + b² s)`, strictly smaller in absolute value than `b` unless `b = 0` or
  `s = 0` (`abs_probitShrink_lt`, `probitShrink_eq_self_iff`). The ecological slope is strictly
  attenuated toward zero relative to the individual slope difference `β₂ = ρ₁ - ρ₀` when
  `s > 0` (`probitEcoSlope_attenuation`), with equality iff `s = 0` or `ρ₀ = ρ₁`
  (`probitEcoSlope_eq_iff`).
* **Non collapsibility** (`not_linkCollapsible_probit`): with a common slope `b ≠ 0` and
  `s > 0`, the conditional probit contrast is the constant `a₁ - a₀` but the marginal one is
  `(a₁ - a₀) / √(1 + b² s)`; in particular the effect measure on the probit scale is not
  collapsible.

## Main definitions

* `probit`, `probitShrink`, `probitAttenuation`, `probitEcoIntercept`, `probitEcoSlope`.

## Main results

* `integral_cdf_gaussianReal`, `HasLaw.integral_cdf_affine`, `strictMono_cdf_gaussianReal`,
  `cdf_gaussianReal_mem_Ioo`, `probit_cdf`.
* `linkMarginal_probit_gaussian`, `linkMarginal_probit_gaussian_common_slope`.
* `probitAttenuation_pos`, `probitAttenuation_le_one`, `probitAttenuation_eq_one_iff`,
  `abs_probitShrink_lt`, `probitShrink_eq_self_iff`.
* `probitShrink_strictMono`, `sub_probitShrink_strictMono`, `probitEcoSlope_attenuation`,
  `probitEcoSlope_eq_iff`.
* `not_linkCollapsible_probit`, `linkMarginal_sub_linkConditional_probit`.

## References

* S. L. Zeger, K.-Y. Liang and P. S. Albert, *Models for longitudinal data: a generalized
  estimating equation approach*, Biometrics 44 (1988).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaAnalysis

open MeasureTheory ProbabilityTheory Set EffectMeasure BiasAnalysis.Distributions
open scoped NNReal ENNReal

/-! ### The standard normal distribution function and the probit link -/

/-- The **probit link** `Φ⁻¹`, the quantile function of the standard normal law. -/
noncomputable def probit : ℝ → ℝ := quantile (gaussianReal 0 1)

theorem volume_absolutelyContinuous_gaussianReal : volume ≪ gaussianReal 0 1 :=
  gaussianReal_absolutelyContinuous' 0 one_ne_zero

/-- `0 < Φ(x) < 1`. -/
theorem cdf_gaussianReal_mem_Ioo (x : ℝ) : cdf (gaussianReal 0 1) x ∈ Ioo (0 : ℝ) 1 :=
  cdf_mem_Ioo_of_absolutelyContinuous volume_absolutelyContinuous_gaussianReal x

/-- **The probit link inverts `Φ`**: `probit (Φ x) = x`. -/
theorem probit_cdf (x : ℝ) : probit (cdf (gaussianReal 0 1) x) = x :=
  quantile_cdf_of_absolutelyContinuous volume_absolutelyContinuous_gaussianReal x

/-- `Φ` is strictly increasing. -/
theorem strictMono_cdf_gaussianReal : StrictMono (cdf (gaussianReal 0 1)) := by
  intro x y hxy
  have hpos : 0 < (gaussianReal 0 1) (Ioc x y) := by
    refine pos_iff_ne_zero.2 fun h0 => ?_
    have h := volume_absolutelyContinuous_gaussianReal h0
    rw [Real.volume_Ioc] at h
    exact (ENNReal.ofReal_pos.2 (sub_pos.2 hxy)).ne' h
  have h2 := (cdf (gaussianReal 0 1)).measure_Ioc x y
  rw [measure_cdf] at h2
  rw [h2] at hpos
  exact sub_pos.1 (ENNReal.ofReal_pos.1 hpos)

/-! ### The Gaussian probit integral -/

/-- **The Gaussian probit integral**: `∫ Φ dN(μ, τ) = Φ(μ / √(1 + τ))`. -/
theorem integral_cdf_gaussianReal (μ : ℝ) (τ : ℝ≥0) :
    ∫ w, cdf (gaussianReal 0 1) w ∂gaussianReal μ τ =
      cdf (gaussianReal 0 1) (μ / √(1 + τ)) := by
  set N := gaussianReal (0 : ℝ) 1 with hNdef
  have hmono : Measurable fun w : ℝ => N (Iic w) :=
    Monotone.measurable fun x y hxy => measure_mono (Iic_subset_Iic.2 hxy)
  have h1 : ∫ w, cdf N w ∂gaussianReal μ τ = (∫⁻ w, N (Iic w) ∂gaussianReal μ τ).toReal := by
    rw [← integral_toReal hmono.aemeasurable (ae_of_all _ fun _ => measure_lt_top _ _)]
    simp [cdf_eq_real, measureReal_def]
  have h2 : ∫⁻ w, N (Iic w) ∂gaussianReal μ τ = (gaussianReal (-μ) τ ∗ N) (Iic 0) := by
    rw [← lintegral_indicator_one measurableSet_Iic,
      Measure.lintegral_conv (measurable_one.indicator measurableSet_Iic),
      ← gaussianReal_map_neg, lintegral_map _ measurable_neg]
    · refine lintegral_congr fun w => ?_
      rw [← lintegral_indicator_one measurableSet_Iic]
      congr 1
      funext y
      simp only [indicator, mem_Iic]
      congr 1
      simp only [eq_iff_iff]
      constructor <;> intro h <;> linarith
    · have e : (fun x : ℝ => ∫⁻ y, (Iic (0 : ℝ)).indicator 1 (x + y) ∂N) =
          fun x => N (Iic (-x)) := by
        funext x
        rw [← lintegral_indicator_one measurableSet_Iic]
        congr 1
        funext y
        simp only [indicator, mem_Iic]
        congr 1
        simp only [eq_iff_iff]
        constructor <;> intro h <;> linarith
      rw [e]
      exact Antitone.measurable fun x y hxy => measure_mono (Iic_subset_Iic.2 (neg_le_neg hxy))
  rw [h1, h2, gaussianReal_conv_gaussianReal, add_zero]
  set c := √(1 + (τ : ℝ)) with hc
  have hc0 : 0 < c := Real.sqrt_pos.2 (by positivity)
  have hN : gaussianReal (-μ) (τ + 1) = (N.map (c * ·)).map (· + -μ) := by
    rw [gaussianReal_map_const_mul, gaussianReal_map_add_const]
    congr 1
    · simp
    · ext
      simp [hc, add_comm, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (τ : ℝ) + 1)]
  rw [hN, Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_apply (by fun_prop) measurableSet_Iic]
  have hpre : (fun x => x + -μ) ∘ (c * ·) ⁻¹' Iic 0 = Iic (μ / c) := by
    ext x
    simp only [mem_preimage, Function.comp, mem_Iic]
    rw [le_div_iff₀ hc0]
    constructor <;> intro h <;> linarith
  rw [hpre, cdf_eq_real, measureReal_def]

/-- **The probit integral against a Gaussian covariate**: if `X ∼ N(m, s)` then
`E Φ(a + b X) = Φ((a + b m) / √(1 + b² s))`. -/
theorem _root_.ProbabilityTheory.HasLaw.integral_cdf_affine {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {m : ℝ} {s : ℝ≥0} (hX : HasLaw X (gaussianReal m s) P)
    (a b : ℝ) :
    ∫ ω, cdf (gaussianReal 0 1) (a + b * X ω) ∂P =
      cdf (gaussianReal 0 1) ((a + b * m) / √(1 + b ^ 2 * s)) := by
  have hY : HasLaw (fun ω => a + b * X ω)
      (gaussianReal (a + b * m) (⟨b ^ 2, sq_nonneg _⟩ * s)) P := by
    have h1 := gaussianReal_mul_const hX b
    have h2 : HasLaw (fun ω => a + b * X ω) ((gaussianReal (b * m) (⟨b ^ 2, sq_nonneg _⟩ * s)).map
        (a + ·)) P := by
      refine HasLaw.comp (X := fun ω => b * X ω) (Y := (a + ·)) ⟨by fun_prop, rfl⟩ ?_
      convert h1 using 2
      · ring
      · rfl
    rw [gaussianReal_map_const_add] at h2
    convert h2 using 2
    ring
  have h := hY.integral_comp (f := fun x => cdf (gaussianReal 0 1) x)
    (cdf (gaussianReal 0 1)).mono.measurable.aestronglyMeasurable
  rw [integral_cdf_gaussianReal] at h
  simp only [Function.comp_def] at h
  rw [h]
  rfl

/-! ### Attenuation of a single slope -/

/-- The **probit attenuation factor** `1 / √(1 + b² s)` of a slope `b` under a covariate of
variance `s`. -/
noncomputable def probitAttenuation (s b : ℝ) : ℝ := 1 / √(1 + b ^ 2 * s)

/-- The **probit shrinkage map** `h(ρ) = ρ / √(1 + ρ² s)`: the slope of the aggregate probit in
the covariate mean, for an individual slope `ρ`. -/
noncomputable def probitShrink (s ρ : ℝ) : ℝ := ρ / √(1 + ρ ^ 2 * s)

theorem probitShrink_eq_mul (s ρ : ℝ) : probitShrink s ρ = ρ * probitAttenuation s ρ := by
  rw [probitShrink, probitAttenuation, mul_one_div]

theorem probitAttenuation_pos {s : ℝ} (hs : 0 ≤ s) (b : ℝ) : 0 < probitAttenuation s b := by
  have : 0 < 1 + b ^ 2 * s := by positivity
  rw [probitAttenuation]
  exact one_div_pos.2 (Real.sqrt_pos.2 this)

theorem probitAttenuation_le_one {s : ℝ} (hs : 0 ≤ s) (b : ℝ) : probitAttenuation s b ≤ 1 := by
  have h1 : 1 ≤ √(1 + b ^ 2 * s) := by
    calc (1 : ℝ) = √1 := Real.sqrt_one.symm
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [mul_nonneg (sq_nonneg b) hs])
  rw [probitAttenuation, div_le_one (by linarith)]
  exact h1

/-- **No attenuation exactly without slope or without covariate variation**: the factor is one
iff `b = 0` or `s = 0`. -/
theorem probitAttenuation_eq_one_iff {s : ℝ} (hs : 0 ≤ s) (b : ℝ) :
    probitAttenuation s b = 1 ↔ b = 0 ∨ s = 0 := by
  have hq : 0 ≤ 1 + b ^ 2 * s := by positivity
  rw [probitAttenuation, div_eq_one_iff_eq (Real.sqrt_pos.2 (by positivity)).ne', eq_comm,
    Real.sqrt_eq_one, add_eq_left, mul_eq_zero, pow_eq_zero_iff two_ne_zero]

/-- **Strict attenuation of a single slope**: for `b ≠ 0` and `s > 0`, `|h(b)| < |b|`. -/
theorem abs_probitShrink_lt {s : ℝ} (hs : 0 < s) {b : ℝ} (hb : b ≠ 0) :
    |probitShrink s b| < |b| := by
  have h1 := probitAttenuation_le_one hs.le b
  have h2 : probitAttenuation s b ≠ 1 := fun h =>
    ((probitAttenuation_eq_one_iff hs.le b).1 h).elim hb hs.ne'
  have h0 := probitAttenuation_pos hs.le b
  rw [probitShrink_eq_mul, abs_mul, abs_of_pos h0]
  exact mul_lt_of_lt_one_right (abs_pos.2 hb) (lt_of_le_of_ne h1 h2)

/-- The aggregate slope equals the individual slope iff `b = 0` or `s = 0`. -/
theorem probitShrink_eq_self_iff {s : ℝ} (hs : 0 ≤ s) (b : ℝ) :
    probitShrink s b = b ↔ b = 0 ∨ s = 0 := by
  rw [probitShrink_eq_mul]
  constructor
  · intro h
    by_cases hb : b = 0
    · exact Or.inl hb
    · have : probitAttenuation s b = 1 := by
        have := congrArg (· / b) h
        simpa [mul_div_assoc, hb, mul_comm b] using this
      exact (probitAttenuation_eq_one_iff hs b).1 this
  · rintro (h | h)
    · rw [h, zero_mul]
    · rw [(probitAttenuation_eq_one_iff hs b).2 (Or.inr h), mul_one]

/-! ### The aggregate probit contrast -/

/-- The **ecological intercept** of the aggregate probit contrast of the arms `Φ(a_t + ρ_t x)`. -/
noncomputable def probitEcoIntercept (s a₀ a₁ ρ₀ ρ₁ : ℝ) : ℝ :=
  a₁ / √(1 + ρ₁ ^ 2 * s) - a₀ / √(1 + ρ₀ ^ 2 * s)

/-- The **ecological slope** `b₂ = h(ρ₁) - h(ρ₀)` of the aggregate probit contrast; the
individual slope difference is `β₂ = ρ₁ - ρ₀`. -/
noncomputable def probitEcoSlope (s ρ₀ ρ₁ : ℝ) : ℝ := probitShrink s ρ₁ - probitShrink s ρ₀

/-- `Φ(a + b X)` is integrable for every finite law. -/
theorem integrable_cdf_affine {𝒳 : Type*} [MeasurableSpace 𝒳] {ν : Measure 𝒳}
    [IsFiniteMeasure ν] {f : 𝒳 → ℝ} (hf : Measurable f) :
    Integrable (fun x => cdf (gaussianReal 0 1) (f x)) ν := by
  refine (integrable_const (1 : ℝ)).mono'
    ((cdf (gaussianReal 0 1)).mono.measurable.comp hf).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (cdf_nonneg _ _)]
  exact cdf_le_one _ _

/-- **The aggregate probit contrast is affine in the covariate mean**: with `X ∼ N(m, s)` and
arm risks `Φ(a_t + ρ_t x)`, the marginal probit contrast is `c + b₂ m`. -/
theorem linkMarginal_probit_gaussian (m : ℝ) (s : ℝ≥0) (a₀ a₁ ρ₀ ρ₁ : ℝ) :
    linkMarginal probit (gaussianReal m s) (fun x => cdf (gaussianReal 0 1) (a₀ + ρ₀ * x))
        (fun x => cdf (gaussianReal 0 1) (a₁ + ρ₁ * x)) =
      probitEcoIntercept s a₀ a₁ ρ₀ ρ₁ + probitEcoSlope s ρ₀ ρ₁ * m := by
  have hX : HasLaw (fun x : ℝ => x) (gaussianReal m s) (gaussianReal m s) :=
    ⟨aemeasurable_id, Measure.map_id⟩
  rw [linkMarginal, hX.integral_cdf_affine, hX.integral_cdf_affine, probit_cdf, probit_cdf,
    probitEcoIntercept, probitEcoSlope, probitShrink, probitShrink]
  ring

/-- **A common slope**: with `ρ₀ = ρ₁ = b` the conditional probit contrast is the constant
`a₁ - a₀` at every covariate value, while the marginal probit contrast under `X ∼ N(m, s)` is
the attenuated `(a₁ - a₀) / √(1 + b² s)`, whatever the mean `m`. -/
theorem linkMarginal_probit_gaussian_common_slope (m : ℝ) (s : ℝ≥0) (a₀ a₁ b : ℝ) :
    (∀ x, linkContrast probit (fun x => cdf (gaussianReal 0 1) (a₀ + b * x))
        (fun x => cdf (gaussianReal 0 1) (a₁ + b * x)) x = a₁ - a₀) ∧
      linkMarginal probit (gaussianReal m s) (fun x => cdf (gaussianReal 0 1) (a₀ + b * x))
          (fun x => cdf (gaussianReal 0 1) (a₁ + b * x)) =
        (a₁ - a₀) * probitAttenuation s b := by
  refine ⟨fun x => ?_, ?_⟩
  · rw [linkContrast, probit_cdf, probit_cdf]
    ring
  · rw [linkMarginal_probit_gaussian, probitEcoIntercept, probitEcoSlope, sub_self, zero_mul,
      add_zero, probitAttenuation]
    ring

/-- **The effect measure on the probit scale is not collapsible**: with arm risks `Φ(x)` and
`Φ(1 + x)` and `X ∼ N(0, 1)`, the conditional probit contrast is `1` at every `x` and the
marginal one is `1 / √2`. -/
theorem not_linkCollapsible_probit : ¬ LinkCollapsible (Ioo 0 1) probit := by
  intro h
  obtain ⟨hc, hm⟩ := linkMarginal_probit_gaussian_common_slope 0 1 0 1 1
  have hmeas : ∀ a : ℝ, Measurable fun x : ℝ => a + 1 * x := fun a => by fun_prop
  have := h ℝ (gaussianReal 0 1) _ _ (integrable_cdf_affine (hmeas 0))
    (integrable_cdf_affine (hmeas 1))
    (ae_of_all _ fun x => ⟨cdf_gaussianReal_mem_Ioo _, cdf_gaussianReal_mem_Ioo _⟩) 1
    (ae_of_all _ fun x => by rw [hc]; norm_num)
  rw [hm, probitAttenuation] at this
  have h2 : √(1 + (1 : ℝ) ^ 2 * ((1 : ℝ≥0) : ℝ)) = √2 := by norm_num
  rw [h2] at this
  have : √2 = 1 := by
    have h' : (1 : ℝ) / √2 = 1 := by linarith
    rwa [div_eq_one_iff_eq (by positivity), eq_comm] at h'
  have := Real.sqrt_eq_one.1 this
  norm_num at this

/-! ### Strict attenuation of the ecological slope -/

theorem hasDerivAt_probitShrink {s : ℝ} (hs : 0 ≤ s) (ρ : ℝ) :
    HasDerivAt (probitShrink s) (1 / ((1 + ρ ^ 2 * s) * √(1 + ρ ^ 2 * s))) ρ := by
  have hq : 0 < 1 + ρ ^ 2 * s := by positivity
  have hr : 0 < √(1 + ρ ^ 2 * s) := Real.sqrt_pos.2 hq
  have h1 : HasDerivAt (fun y : ℝ => 1 + y ^ 2 * s) (2 * ρ * s) ρ := by
    have := ((hasDerivAt_pow 2 ρ).mul_const s).const_add 1
    convert this using 1
    norm_num
  have h2 := (hasDerivAt_id ρ).div (h1.sqrt hq.ne') hr.ne'
  have hsq : √(1 + ρ ^ 2 * s) ^ 2 = 1 + ρ ^ 2 * s := Real.sq_sqrt hq.le
  convert h2 using 1
  · funext y
    rfl
  rw [hsq, id, eq_div_iff hq.ne']
  field_simp
  rw [hsq]
  ring

/-- The shrinkage map is strictly increasing. -/
theorem probitShrink_strictMono {s : ℝ} (hs : 0 ≤ s) : StrictMono (probitShrink s) :=
  strictMono_of_deriv_pos fun ρ => by
    rw [(hasDerivAt_probitShrink hs ρ).deriv]
    have hq : 0 < 1 + ρ ^ 2 * s := by positivity
    positivity

/-- For `s > 0`, `ρ ↦ ρ - h(ρ)` is strictly increasing: the shrinkage contracts differences. -/
theorem sub_probitShrink_strictMono {s : ℝ} (hs : 0 < s) :
    StrictMono fun ρ => ρ - probitShrink s ρ := by
  set k := fun ρ => ρ - probitShrink s ρ with hk
  have hd : ∀ ρ, HasDerivAt k (1 - 1 / ((1 + ρ ^ 2 * s) * √(1 + ρ ^ 2 * s))) ρ :=
    fun ρ => (hasDerivAt_id ρ).sub (hasDerivAt_probitShrink hs.le ρ)
  have hpos : ∀ ρ, ρ ≠ 0 → 0 < deriv k ρ := fun ρ hρ => by
    rw [(hd ρ).deriv, sub_pos]
    have hρ2 : 0 < ρ ^ 2 := by positivity
    have hq : 1 < 1 + ρ ^ 2 * s := by have := mul_pos hρ2 hs; linarith
    have hr : 1 < √(1 + ρ ^ 2 * s) := (Real.lt_sqrt zero_le_one).2 (by rw [one_pow]; exact hq)
    rw [div_lt_one (by positivity)]
    nlinarith
  have hc : Continuous k := continuous_iff_continuousAt.2 fun ρ => (hd ρ).continuousAt
  have hI : StrictMonoOn k (Ici 0) := strictMonoOn_of_deriv_pos (convex_Ici 0) hc.continuousOn
    fun ρ hρ => hpos ρ (by rw [interior_Ici] at hρ; exact (mem_Ioi.1 hρ).ne')
  have hJ : StrictMonoOn k (Iic 0) := strictMonoOn_of_deriv_pos (convex_Iic 0) hc.continuousOn
    fun ρ hρ => hpos ρ (by rw [interior_Iic] at hρ; exact (mem_Iio.1 hρ).ne)
  intro x y hxy
  rcases le_or_gt 0 x with hx | hx
  · exact hI hx (hx.trans hxy.le) hxy
  rcases le_or_gt y 0 with hy | hy
  · exact hJ hx.le hy hxy
  · exact (hJ hx.le le_rfl hx).trans (hI le_rfl hy.le hy)

/-- **Strict attenuation of the ecological slope**: for `s > 0`, `0 < b₂ < β₂` when
`β₂ = ρ₁ - ρ₀ > 0`, and `β₂ < b₂ < 0` when `β₂ < 0`. -/
theorem probitEcoSlope_attenuation {s : ℝ} (hs : 0 < s) (ρ₀ ρ₁ : ℝ) :
    (0 < ρ₁ - ρ₀ → 0 < probitEcoSlope s ρ₀ ρ₁ ∧ probitEcoSlope s ρ₀ ρ₁ < ρ₁ - ρ₀) ∧
      (ρ₁ - ρ₀ < 0 → ρ₁ - ρ₀ < probitEcoSlope s ρ₀ ρ₁ ∧ probitEcoSlope s ρ₀ ρ₁ < 0) := by
  have hm := probitShrink_strictMono hs.le
  have hk := sub_probitShrink_strictMono hs
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h1 := hm (show ρ₀ < ρ₁ by linarith)
    have h2 := hk (show ρ₀ < ρ₁ by linarith)
    simp only at h2
    exact ⟨by rw [probitEcoSlope]; linarith, by rw [probitEcoSlope]; linarith⟩
  · have h1 := hm (show ρ₁ < ρ₀ by linarith)
    have h2 := hk (show ρ₁ < ρ₀ by linarith)
    simp only at h2
    exact ⟨by rw [probitEcoSlope]; linarith, by rw [probitEcoSlope]; linarith⟩

/-- **The equality cases of the ecological slope**: `b₂ = β₂` iff `s = 0` or `ρ₀ = ρ₁`. -/
theorem probitEcoSlope_eq_iff {s : ℝ} (hs : 0 ≤ s) (ρ₀ ρ₁ : ℝ) :
    probitEcoSlope s ρ₀ ρ₁ = ρ₁ - ρ₀ ↔ s = 0 ∨ ρ₀ = ρ₁ := by
  constructor
  · intro h
    by_contra hne
    push Not at hne
    have hs' : 0 < s := lt_of_le_of_ne hs (Ne.symm hne.1)
    obtain ⟨h1, h2⟩ := probitEcoSlope_attenuation hs' ρ₀ ρ₁
    rcases lt_or_gt_of_ne hne.2 with hlt | hlt
    · linarith [(h1 (by linarith)).2]
    · linarith [(h2 (by linarith)).1]
  · rintro (h | h)
    · have e : ∀ ρ, probitShrink s ρ = ρ := fun ρ =>
        (probitShrink_eq_self_iff hs ρ).2 (Or.inr h)
      rw [probitEcoSlope, e, e]
    · rw [probitEcoSlope, h, sub_self, sub_self]

/-- **The conditional and the marginal probit contrasts under a Gaussian covariate.** With
`X ∼ N(m, s)` and arm risks `Φ(a_t + ρ_t x)`: the average conditional probit contrast is
`γ + β₂ m` with `γ = a₁ - a₀` and `β₂ = ρ₁ - ρ₀`; the marginal one is `c + b₂ m`; their
difference, the non collapsibility gap, is `(c - γ) + (b₂ - β₂) m`; and for `s > 0` and
`β₂ ≠ 0` the ecological slope `b₂` has the sign of `β₂` and strictly smaller magnitude. -/
theorem linkMarginal_sub_linkConditional_probit (m : ℝ) (s : ℝ≥0) (a₀ a₁ ρ₀ ρ₁ : ℝ) :
    linkConditional probit (gaussianReal m s) (fun x => cdf (gaussianReal 0 1) (a₀ + ρ₀ * x))
        (fun x => cdf (gaussianReal 0 1) (a₁ + ρ₁ * x)) = (a₁ - a₀) + (ρ₁ - ρ₀) * m ∧
      linkMarginal probit (gaussianReal m s) (fun x => cdf (gaussianReal 0 1) (a₀ + ρ₀ * x))
          (fun x => cdf (gaussianReal 0 1) (a₁ + ρ₁ * x)) -
        linkConditional probit (gaussianReal m s)
          (fun x => cdf (gaussianReal 0 1) (a₀ + ρ₀ * x))
          (fun x => cdf (gaussianReal 0 1) (a₁ + ρ₁ * x)) =
        (probitEcoIntercept s a₀ a₁ ρ₀ ρ₁ - (a₁ - a₀)) +
          (probitEcoSlope s ρ₀ ρ₁ - (ρ₁ - ρ₀)) * m ∧
      (0 < (s : ℝ) → ρ₁ - ρ₀ ≠ 0 →
        0 < probitEcoSlope s ρ₀ ρ₁ * (ρ₁ - ρ₀) ∧ |probitEcoSlope s ρ₀ ρ₁| < |ρ₁ - ρ₀|) := by
  have hcond : linkConditional probit (gaussianReal m s)
      (fun x => cdf (gaussianReal 0 1) (a₀ + ρ₀ * x))
      (fun x => cdf (gaussianReal 0 1) (a₁ + ρ₁ * x)) = (a₁ - a₀) + (ρ₁ - ρ₀) * m := by
    have hi : Integrable (fun x : ℝ => x) (gaussianReal m s) :=
      (memLp_id_gaussianReal 1).integrable le_rfl
    have e : linkContrast probit (fun x => cdf (gaussianReal 0 1) (a₀ + ρ₀ * x))
        (fun x => cdf (gaussianReal 0 1) (a₁ + ρ₁ * x)) = fun x => (a₁ - a₀) + (ρ₁ - ρ₀) * x := by
      funext x
      rw [linkContrast, probit_cdf, probit_cdf]
      ring
    rw [linkConditional, e, integral_add (integrable_const _) (hi.const_mul _), integral_const_mul,
      integral_id_gaussianReal]
    simp
  refine ⟨hcond, ?_, fun hs hne => ?_⟩
  · rw [linkMarginal_probit_gaussian, hcond]
    ring
  · obtain ⟨h1, h2⟩ := probitEcoSlope_attenuation hs ρ₀ ρ₁
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · obtain ⟨l, u⟩ := h2 hlt
      refine ⟨mul_pos_of_neg_of_neg u hlt, ?_⟩
      rw [abs_of_neg u, abs_of_neg hlt]
      linarith
    · obtain ⟨l, u⟩ := h1 hlt
      refine ⟨mul_pos l hlt, ?_⟩
      rw [abs_of_pos l, abs_of_pos hlt]
      exact u

end NetworkMetaAnalysis

end CausalInference
