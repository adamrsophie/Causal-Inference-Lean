/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.BiasAnalysis.IndirectComparisonRankCorrelation
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# The rank correlation of a Gaussian pair

Let `V`, `W` be independent standard normal variables, `ρ ∈ [-1, 1]` and
`Y = ρ V + √(1 - ρ²) W`, so that `(V, Y)` is a standard Gaussian pair with correlation `ρ`. This
file proves that the rank correlation of `(V, Y)` is `(6/π) arcsin(ρ/2)`.

The argument is the classical one. With independent standard normals `A`, `B`, independent of
`(V, W)`, `E[Φ(V) Φ(Y)] = P(A < V, B < Y)`. The differences `(V - A, Y - B)` have the law of
`√2 (U, r U + √(1 - r²) U')` with `r = ρ/2` and `U`, `U'` independent standard normals (by
characteristic functions), and in polar coordinates the event that both coordinates are positive
is an angular sector of length `π/2 + arcsin r`, whose probability is
`1/4 + arcsin(r) / (2π)` because the standard bivariate normal law is rotation invariant. The
probability integral transforms are uniform with mean `1/2` and variance `1/12`.

## Main results

* `measureReal_orthant_pair`: `P(V > 0, r V + √(1 - r²) W > 0) = 1/4 + arcsin(r) / (2π)` for
  `r ∈ [-1, 1]`; `measureReal_orthant_pair_half`: at `r = 1/2` it is `1/3`.
* `integral_cdf_mul_cdf_pair`: `E[Φ(V) Φ(ρ V + √(1 - ρ²) W)] = 1/4 + arcsin(ρ/2) / (2π)`.
* `map_pair_gaussian`: `ρ V + √(1 - ρ²) W` is standard normal.
* `rankCorrelation_gaussian_pair`: the rank correlation of `(V, ρ V + √(1 - ρ²) W)` is
  `(6/π) arcsin(ρ/2)`; `rankCorrelation_gaussian_pair_target`: for a target rank correlation
  `ρ_S ∈ [-1, 1]` the choice `ρ = 2 sin(π ρ_S / 6)` reproduces it exactly.
-/

@[expose] public section

namespace CausalInference

namespace BiasAnalysis

namespace IndirectComparisonBias

open MeasureTheory ProbabilityTheory Set Complex

open scoped Real

/-- The law of two independent standard normal variables. -/
noncomputable abbrev stdNormalPair : Measure (ℝ × ℝ) := (gaussianReal 0 1).prod (gaussianReal 0 1)

/-- The characteristic function of the standard normal law at a linear functional `ℓ` on `ℝ` is
`exp(-(ℓ 1)² / 2)`. -/
lemma charFunDual_stdNormal (ℓ : StrongDual ℝ ℝ) :
    charFunDual (gaussianReal 0 1) ℓ = cexp (-((ℓ 1 : ℝ) : ℂ) ^ 2 / 2) := by
  have h : ∀ x : ℝ, ℓ x = ℓ 1 * x := fun x => by
    rw [mul_comm, ← smul_eq_mul, ← ℓ.map_smul, smul_eq_mul, mul_one]
  rw [charFunDual_apply, show (fun v : ℝ => cexp (↑(ℓ v) * I)) =
      fun v : ℝ => cexp (↑(ℓ 1) * ↑v * I) from funext fun v => by rw [h v, ofReal_mul],
    ← charFun_apply_real, charFun_gaussianReal]
  simp [neg_div]

/-- The characteristic function of `stdNormalPair` at a linear functional `L` on `ℝ × ℝ`. -/
lemma charFunDual_stdNormalPair (L : StrongDual ℝ (ℝ × ℝ)) :
    charFunDual stdNormalPair L =
      cexp (-((L (1, 0) : ℝ) : ℂ) ^ 2 / 2) * cexp (-((L (0, 1) : ℝ) : ℂ) ^ 2 / 2) := by
  rw [charFunDual_prod, charFunDual_stdNormal, charFunDual_stdNormal]
  rfl

/-- A linear functional on `ℝ × ℝ` is determined by its values at the unit vectors. -/
lemma strongDual_prod_eq (L : StrongDual ℝ (ℝ × ℝ)) (p : ℝ × ℝ) :
    L p = p.1 * L (1, 0) + p.2 * L (0, 1) := by
  have hp : p = p.1 • ((1 : ℝ), (0 : ℝ)) + p.2 • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  conv_lhs => rw [hp]
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- The differences `((x, y), (a, b)) ↦ (x - a, ρ x + s y - b)`. -/
noncomputable def pairDifference (ρ s : ℝ) : (ℝ × ℝ) × (ℝ × ℝ) →L[ℝ] ℝ × ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun q => (q.1.1 - q.2.1, ρ * q.1.1 + s * q.1.2 - q.2.2)
      map_add' := fun q q' => by ext <;> simp <;> ring
      map_smul' := fun c q => by ext <;> simp <;> ring }

/-- `pairDifference` evaluates coordinatewise. -/
lemma pairDifference_apply (ρ s : ℝ) (q : (ℝ × ℝ) × (ℝ × ℝ)) :
    pairDifference ρ s q = (q.1.1 - q.2.1, ρ * q.1.1 + s * q.1.2 - q.2.2) := rfl

/-- The scaled correlated pair `(u, v) ↦ (√2 u, √2 (r u + c v))`. -/
noncomputable def scaledPair (r c : ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p => (√2 * p.1, √2 * (r * p.1 + c * p.2))
      map_add' := fun p p' => by ext <;> simp <;> ring
      map_smul' := fun a p => by ext <;> simp <;> ring }

/-- `scaledPair` evaluates coordinatewise. -/
lemma scaledPair_apply (r c : ℝ) (p : ℝ × ℝ) :
    scaledPair r c p = (√2 * p.1, √2 * (r * p.1 + c * p.2)) := rfl

/-- **The law of the differences.** For independent standard normals `x, y, a, b`,
`s² = 1 - ρ²` and `c² = 1 - (ρ/2)²`, the pair `(x - a, ρ x + s y - b)` has the law of
`(√2 u, √2 ((ρ/2) u + c v))` for independent standard normals `u, v`: both characteristic
functions are `exp(-(α² + ρ α β + β²))` at `(p, q) ↦ α p + β q`. -/
lemma map_pairDifference {ρ s c : ℝ} (hs : s ^ 2 = 1 - ρ ^ 2) (hc : c ^ 2 = 1 - (ρ / 2) ^ 2) :
    (stdNormalPair.prod stdNormalPair).map (pairDifference ρ s) =
      stdNormalPair.map (scaledPair (ρ / 2) c) := by
  refine Measure.ext_of_charFunDual (funext fun L => ?_)
  rw [charFunDual_map, charFunDual_map, charFunDual_prod, charFunDual_stdNormalPair,
    charFunDual_stdNormalPair, charFunDual_stdNormalPair]
  have key : (⇑L : ℝ × ℝ → ℝ) = fun p => p.1 * L (1, 0) + p.2 * L (0, 1) :=
    funext (strongDual_prod_eq L)
  generalize L (1, 0) = α at key
  generalize L (0, 1) = β at key
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.inr_apply, pairDifference_apply, scaledPair_apply, key, Prod.fst_zero,
    Prod.snd_zero]
  simp only [← Complex.exp_add]
  congr 1
  have H1 : (s : ℂ) ^ 2 = 1 - (ρ : ℂ) ^ 2 := by exact_mod_cast hs
  have H2 : (c : ℂ) ^ 2 = 1 - ((ρ : ℂ) / 2) ^ 2 := by exact_mod_cast hc
  have H3 : ((√2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  push_cast
  linear_combination (((α : ℂ) + ρ * β / 2) ^ 2 / 2 + (c : ℂ) ^ 2 * β ^ 2 / 2) * H3 +
    (-(β : ℂ) ^ 2 / 2) * H1 + (β : ℂ) ^ 2 * H2

/-- The product of two standard normal densities is radial:
`φ(x) φ(y) = exp(-(x² + y²) / 2) / (2π)`. -/
lemma gaussianPDFReal_zero_one_mul (x y : ℝ) :
    gaussianPDFReal 0 1 x * gaussianPDFReal 0 1 y = Real.exp (-(x ^ 2 + y ^ 2) / 2) / (2 * π) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [mul_mul_mul_comm, ← Real.exp_add, ← mul_inv, Real.mul_self_sqrt (by positivity)]
  ring_nf

/-- **Angular sets under `stdNormalPair`.** If membership of `(R cos θ, R sin θ)` in a measurable
set `S` depends only on whether `θ ∈ A`, for `R > 0` and `θ ∈ (-π, π)`, then the probability of
`S` is the radial integral times the length of `A ∩ (-π, π)`. -/
lemma measureReal_stdNormalPair_angular {S : Set (ℝ × ℝ)} {A : Set ℝ} (hS : MeasurableSet S)
    (hA : MeasurableSet A)
    (hSA : ∀ R θ, 0 < R → θ ∈ Ioo (-π) π → ((R * Real.cos θ, R * Real.sin θ) ∈ S ↔ θ ∈ A)) :
    stdNormalPair.real S =
      (∫ R in Ioi (0 : ℝ), R * (Real.exp (-R ^ 2 / 2) / (2 * π))) *
        volume.real (Ioo (-π) π ∩ A) := by
  have hγ : gaussianReal 0 1 = volume.withDensity (gaussianPDF 0 1) :=
    gaussianReal_of_var_ne_zero 0 one_ne_zero
  rw [← integral_indicator_one hS, stdNormalPair, hγ, prod_withDensity
    (measurable_gaussianPDF 0 1) (measurable_gaussianPDF 0 1), ← Measure.volume_eq_prod,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (ae_of_all _ fun _ => ENNReal.mul_lt_top gaussianPDF_lt_top gaussianPDF_lt_top),
    ← integral_comp_polarCoord_symm]
  have ht : polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-π) π := rfl
  have hang : volume.real (Ioo (-π) π ∩ A) = ∫ θ in Ioo (-π) π, A.indicator 1 θ := by
    rw [setIntegral_indicator hA]
    simp only [Pi.one_apply]
    rw [setIntegral_const, smul_eq_mul, mul_one]
  rw [ht, Measure.volume_eq_prod, hang, ← setIntegral_prod_mul]
  refine setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) fun p hp => ?_
  obtain ⟨hR, hθ⟩ := mem_prod.1 hp
  have hps : polarCoord.symm p = (p.1 * Real.cos p.2, p.1 * Real.sin p.2) := rfl
  have hr2 : (p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2 = p.1 ^ 2 := by
    linear_combination p.1 ^ 2 * Real.cos_sq_add_sin_sq p.2
  simp only [hps]
  rw [ENNReal.toReal_mul, toReal_gaussianPDF, toReal_gaussianPDF, gaussianPDFReal_zero_one_mul,
    hr2]
  by_cases h : p.2 ∈ A
  · rw [indicator_of_mem ((hSA _ _ hR hθ).2 h), indicator_of_mem h]
    simp [smul_eq_mul]
  · rw [indicator_of_notMem (mt (hSA _ _ hR hθ).1 h), indicator_of_notMem h]
    simp

/-- The radial integral of the standard bivariate normal density is `1 / (2π)`. -/
lemma integral_radial_stdNormalPair :
    ∫ R in Ioi (0 : ℝ), R * (Real.exp (-R ^ 2 / 2) / (2 * π)) = 1 / (2 * π) := by
  have h := measureReal_stdNormalPair_angular (S := univ) (A := univ) MeasurableSet.univ
    MeasurableSet.univ (fun _ _ _ _ => by simp)
  rw [probReal_univ, inter_univ, Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos])] at h
  have hpi := Real.pi_pos
  rw [show π - -π = 2 * π by ring] at h
  rw [eq_div_iff (by positivity)]
  linarith

/-- **The orthant probability of a correlated standard normal pair.** For independent standard
normals `V, W` and `r ∈ [-1, 1]`, `P(V > 0, r V + √(1 - r²) W > 0) = 1/4 + arcsin(r) / (2π)`. -/
theorem measureReal_orthant_pair {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) :
    stdNormalPair.real {p : ℝ × ℝ | 0 < p.1 ∧ 0 < r * p.1 + √(1 - r ^ 2) * p.2} =
      1 / 4 + Real.arcsin r / (2 * π) := by
  have hpi := Real.pi_pos
  set β := Real.arcsin r with hβdef
  have hβl : -(π / 2) ≤ β := Real.neg_pi_div_two_le_arcsin r
  have hβu : β ≤ π / 2 := Real.arcsin_le_pi_div_two r
  have hsin : Real.sin β = r := Real.sin_arcsin hr.1 hr.2
  have hcos : Real.cos β = √(1 - r ^ 2) := Real.cos_arcsin r
  have hS : MeasurableSet {p : ℝ × ℝ | 0 < p.1 ∧ 0 < r * p.1 + √(1 - r ^ 2) * p.2} :=
    (measurableSet_lt _root_.measurable_const measurable_fst).inter
      (measurableSet_lt _root_.measurable_const
        (show Measurable fun p : ℝ × ℝ => r * p.1 + √(1 - r ^ 2) * p.2 by fun_prop))
  rw [measureReal_stdNormalPair_angular (A := Ioo (-β) (π / 2)) hS measurableSet_Ioo,
    integral_radial_stdNormalPair, inter_eq_right.2 (Ioo_subset_Ioo (by linarith) (by linarith)),
    Real.volume_real_Ioo_of_le (by linarith)]
  · field_simp
    ring
  intro R θ hR hθ
  have hlin : r * (R * Real.cos θ) + √(1 - r ^ 2) * (R * Real.sin θ) =
      R * Real.sin (θ + β) := by
    rw [Real.sin_add, hsin, hcos]; ring
  simp only [mem_ofPred_eq, hlin, mem_Ioo]
  constructor
  · rintro ⟨h1, h2⟩
    have hc := pos_of_mul_pos_right h1 hR.le
    have hs := pos_of_mul_pos_right h2 hR.le
    have hθu : θ < π / 2 := by
      by_contra h
      have := Real.cos_nonpos_of_pi_div_two_le_of_le (not_lt.1 h) (by linarith [hθ.2])
      linarith
    have hθl : -(π / 2) < θ := by
      by_contra h
      have := Real.cos_nonpos_of_pi_div_two_le_of_le (x := -θ) (by linarith [not_lt.1 h])
        (by linarith [hθ.1])
      rw [Real.cos_neg] at this
      linarith
    refine ⟨?_, hθu⟩
    by_contra h
    have := Real.sin_nonpos_of_nonpos_of_neg_pi_le (x := θ + β) (by linarith [not_lt.1 h])
      (by linarith)
    linarith
  · rintro ⟨h1, h2⟩
    exact ⟨mul_pos hR (Real.cos_pos_of_mem_Ioo ⟨by linarith, h2⟩),
      mul_pos hR (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))⟩

/-- At `r = 1/2` the orthant probability is `1/3`. -/
theorem measureReal_orthant_pair_half :
    stdNormalPair.real {p : ℝ × ℝ | 0 < p.1 ∧ 0 < 1 / 2 * p.1 + √(1 - (1 / 2) ^ 2) * p.2} =
      1 / 3 := by
  rw [measureReal_orthant_pair ⟨by norm_num, by norm_num⟩,
    show (1 : ℝ) / 2 = Real.sin (π / 6) by rw [Real.sin_pi_div_six],
    Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]
  field_simp
  ring

/-- The standard normal distribution function is `x ↦ P(A < x)`, the law having no atoms. -/
lemma cdf_stdNormal_eq_measureReal_Iio (x : ℝ) :
    cdf (gaussianReal 0 1) x = (gaussianReal 0 1).real (Iio x) := by
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  rw [cdf_eq_real, measureReal_congr Iio_ae_eq_Iic]

/-- **The mixed moment of the probability integral transforms.** For independent standard normals
`V, W` and `ρ ∈ [-1, 1]`, `E[Φ(V) Φ(ρ V + √(1 - ρ²) W)] = 1/4 + arcsin(ρ/2) / (2π)`. -/
theorem integral_cdf_mul_cdf_pair {ρ : ℝ} (hρ : ρ ∈ Icc (-1 : ℝ) 1) :
    ∫ p, cdf (gaussianReal 0 1) p.1 * cdf (gaussianReal 0 1) (ρ * p.1 + √(1 - ρ ^ 2) * p.2)
        ∂stdNormalPair = 1 / 4 + Real.arcsin (ρ / 2) / (2 * π) := by
  set s := √(1 - ρ ^ 2) with hsdef
  have hρ2 : ρ ^ 2 ≤ 1 := by nlinarith [hρ.1, hρ.2]
  have hs : s ^ 2 = 1 - ρ ^ 2 := Real.sq_sqrt (by linarith)
  have hr : ρ / 2 ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hρ.1], by linarith [hρ.2]⟩
  have hc : √(1 - (ρ / 2) ^ 2) ^ 2 = 1 - (ρ / 2) ^ 2 := Real.sq_sqrt (by nlinarith)
  set E : Set ((ℝ × ℝ) × (ℝ × ℝ)) := pairDifference ρ s ⁻¹' (Ioi 0 ×ˢ Ioi 0) with hEdef
  have hE : MeasurableSet E :=
    (measurableSet_Ioi.prod measurableSet_Ioi).preimage (pairDifference ρ s).measurable
  have hslice : ∀ p : ℝ × ℝ, Prod.mk p ⁻¹' E = Iio p.1 ×ˢ Iio (ρ * p.1 + s * p.2) := by
    intro p
    ext q
    simp [hEdef, pairDifference_apply, sub_pos]
  have hint : ∀ p : ℝ × ℝ, cdf (gaussianReal 0 1) p.1 * cdf (gaussianReal 0 1)
      (ρ * p.1 + s * p.2) = (stdNormalPair (Prod.mk p ⁻¹' E)).toReal := by
    intro p
    rw [hslice, ← measureReal_def, stdNormalPair, measureReal_prod_prod,
      cdf_stdNormal_eq_measureReal_Iio, cdf_stdNormal_eq_measureReal_Iio]
  simp_rw [hint]
  rw [integral_toReal (measurable_measure_prodMk_left hE).aemeasurable
      (ae_of_all _ fun _ => measure_lt_top _ _), ← Measure.prod_apply hE, ← measureReal_def,
    ← map_measureReal_apply (pairDifference ρ s).measurable
      (measurableSet_Ioi.prod measurableSet_Ioi),
    map_pairDifference hs hc,
    map_measureReal_apply (scaledPair _ _).measurable (measurableSet_Ioi.prod measurableSet_Ioi),
    ← measureReal_orthant_pair hr]
  congr 1
  ext p
  have h2 : (0 : ℝ) < √2 := by positivity
  simp only [mem_preimage, scaledPair_apply, mem_prod, mem_Ioi, mem_ofPred_eq]
  rw [mul_pos_iff_of_pos_left h2, mul_pos_iff_of_pos_left h2]

/-- The linear combination `(x, y) ↦ ρ x + s y`. -/
noncomputable def pairCombination (ρ s : ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  ρ • ContinuousLinearMap.fst ℝ ℝ ℝ + s • ContinuousLinearMap.snd ℝ ℝ ℝ

/-- `pairCombination` evaluates as `ρ x + s y`. -/
lemma pairCombination_apply (ρ s : ℝ) (p : ℝ × ℝ) : pairCombination ρ s p = ρ * p.1 + s * p.2 :=
  rfl

/-- **The second coordinate of the pair is standard normal**: for `s² = 1 - ρ²`,
`ρ V + s W` is standard normal. -/
theorem map_pair_gaussian {ρ s : ℝ} (hs : s ^ 2 = 1 - ρ ^ 2) :
    stdNormalPair.map (fun p => ρ * p.1 + s * p.2) = gaussianReal 0 1 := by
  rw [show (fun p : ℝ × ℝ => ρ * p.1 + s * p.2) = pairCombination ρ s from rfl]
  refine Measure.ext_of_charFunDual (funext fun ℓ => ?_)
  rw [charFunDual_map, charFunDual_stdNormalPair, charFunDual_stdNormal]
  have h : ∀ x : ℝ, ℓ x = ℓ 1 * x := fun x => by
    rw [mul_comm, ← smul_eq_mul, ← ℓ.map_smul, smul_eq_mul, mul_one]
  have h1 : ℓ (pairCombination ρ s (1, 0)) = ℓ 1 * ρ := by
    rw [pairCombination_apply, h]; simp
  have h2 : ℓ (pairCombination ρ s (0, 1)) = ℓ 1 * s := by
    rw [pairCombination_apply, h]; simp
  simp only [ContinuousLinearMap.comp_apply, h1, h2]
  rw [← Complex.exp_add]
  congr 1
  have H : (s : ℂ) ^ 2 = 1 - (ρ : ℂ) ^ 2 := by exact_mod_cast hs
  push_cast
  linear_combination (-(ℓ 1 : ℂ) ^ 2 / 2) * H

/-- **The rank correlation of a standard Gaussian pair.** For independent standard normals `V`,
`W` and `ρ ∈ [-1, 1]`, the rank correlation of `V` and `ρ V + √(1 - ρ²) W` (a standard Gaussian
pair with correlation `ρ`) is `(6/π) arcsin(ρ/2)`. -/
theorem rankCorrelation_gaussian_pair {ρ : ℝ} (hρ : ρ ∈ Icc (-1 : ℝ) 1) :
    rankCorrelation (fun p : ℝ × ℝ => p.1) (fun p => ρ * p.1 + √(1 - ρ ^ 2) * p.2)
      stdNormalPair = gaussianRankCorrelation ρ := by
  set s := √(1 - ρ ^ 2) with hsdef
  have hρ2 : ρ ^ 2 ≤ 1 := by nlinarith [hρ.1, hρ.2]
  have hs : s ^ 2 = 1 - ρ ^ 2 := Real.sq_sqrt (by linarith)
  have hX : Measurable fun p : ℝ × ℝ => p.1 := measurable_fst
  have hY : Measurable fun p : ℝ × ℝ => ρ * p.1 + s * p.2 := by fun_prop
  have hmX : stdNormalPair.map (fun p : ℝ × ℝ => p.1) = gaussianReal 0 1 := by
    simp [stdNormalPair, Measure.map_fst_prod]
  have hmY := map_pair_gaussian hs
  have hc := Distributions.continuous_cdf_gaussianReal_zero_one
  have hcX : Continuous (cdf (stdNormalPair.map fun p : ℝ × ℝ => p.1)) := by rwa [hmX]
  have hcY : Continuous (cdf (stdNormalPair.map fun p : ℝ × ℝ => ρ * p.1 + s * p.2)) := by
    rwa [hmY]
  have hVX := variance_cdf_comp hX hcX
  have hVY := variance_cdf_comp hY hcY
  have hEX := integral_cdf_comp hX hcX
  have hEY := integral_cdf_comp hY hcY
  rw [rankCorrelation, LinearIV.correlation, hVX, hVY,
    covariance_eq_sub (memLp_cdf_comp _ hX) (memLp_cdf_comp _ hY), hEX, hEY]
  rw [hmX, hmY]
  simp only [Pi.mul_apply]
  rw [integral_cdf_mul_cdf_pair hρ, gaussianRankCorrelation,
    ← Real.sqrt_mul (by norm_num), Real.sqrt_mul_self (by norm_num)]
  field_simp
  ring

/-- **Matching a target rank correlation.** For `ρ_S ∈ [-1, 1]`, the Gaussian pair with
correlation `ρ = 2 sin(π ρ_S / 6)` has rank correlation exactly `ρ_S`. -/
theorem rankCorrelation_gaussian_pair_target {ρS : ℝ} (hρS : ρS ∈ Icc (-1 : ℝ) 1) :
    let ρ := 2 * Real.sin (π * ρS / 6)
    ρ ∈ Icc (-1 : ℝ) 1 ∧
      rankCorrelation (fun p : ℝ × ℝ => p.1) (fun p => ρ * p.1 + √(1 - ρ ^ 2) * p.2)
        stdNormalPair = ρS := by
  intro ρ
  have hpi := Real.pi_pos
  have hθ : π * ρS / 6 ∈ Icc (-(π / 6)) (π / 6) :=
    ⟨by nlinarith [hρS.1], by nlinarith [hρS.2]⟩
  have hθ' : π * ρS / 6 ∈ Icc (-(π / 2)) (π / 2) := ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have hmono := Real.strictMonoOn_sin.monotoneOn
  have hup : Real.sin (π * ρS / 6) ≤ 1 / 2 := by
    rw [← Real.sin_pi_div_six]
    exact hmono hθ' ⟨by linarith, by linarith⟩ hθ.2
  have hlo : -(1 / 2) ≤ Real.sin (π * ρS / 6) := by
    rw [← Real.sin_pi_div_six, ← Real.sin_neg]
    exact hmono ⟨by linarith, by linarith⟩ hθ' hθ.1
  have hρ : ρ ∈ Icc (-1 : ℝ) 1 := ⟨by simp only [ρ]; linarith, by simp only [ρ]; linarith⟩
  refine ⟨hρ, ?_⟩
  rw [rankCorrelation_gaussian_pair hρ, gaussianRankCorrelation,
    show ρ / 2 = Real.sin (π * ρS / 6) by simp only [ρ]; ring, Real.arcsin_sin hθ'.1 hθ'.2]
  field_simp

end IndirectComparisonBias

end BiasAnalysis

end CausalInference
