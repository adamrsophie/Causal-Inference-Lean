/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.BiasAnalysis.Distributions
public import CausalInference.InstrumentalVariables.InvalidInstrument
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Rank correlation

The **rank correlation** (Spearman's `ρ_S`) of two real random variables `X`, `Y` is the
correlation of their probability integral transforms `F_X(X)` and `F_Y(Y)`, with `F_X`, `F_Y` the
distribution functions of the laws of `X` and `Y`. In a bias analysis it is the dependence
parameter that survives arbitrary monotone changes of scale of the bias parameters, and for a
Gaussian copula with correlation `ρ` it equals `(6/π) arcsin(ρ/2)`
(`IndirectComparisonArcsine`).

## Main definitions

* `rankCorrelation X Y P`: the correlation of `F_X(X)` and `F_Y(Y)` under `P`.
* `gaussianRankCorrelation ρ = (6/π) arcsin(ρ/2)`.

## Main results

* `cdf_map_comp_of_strictMono`, `rankCorrelation_comp`: the probability integral transform, and
  hence the rank correlation, is unchanged by strictly increasing transformations of either
  variable. No continuity of the transformation or of the margins is needed.
* `abs_rankCorrelation_le_one`: `|ρ_S| ≤ 1` when both transforms have positive variance;
  `integral_cdf_comp`, `variance_cdf_comp` and `abs_rankCorrelation_le_one_of_continuous`: for
  continuous margins the transforms are uniform with mean `1/2` and variance `1/12`, and the
  bound needs no further hypothesis.
* `gaussianRankCorrelation_properties`: on `[-1, 1]` the map `ρ ↦ (6/π) arcsin(ρ/2)` is strictly
  increasing, fixes `-1`, `0`, `1`, has the sign of `ρ`, maps `[-1, 1]` into `[-1, 1]`, and is
  inverted by `ρ = 2 sin(π ρ_S / 6)`.
-/

@[expose] public section

namespace CausalInference

namespace BiasAnalysis

namespace IndirectComparisonBias

open MeasureTheory ProbabilityTheory Set Real

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The **rank correlation** of `X` and `Y` under `P`: the correlation of the probability
integral transforms `F_X(X)` and `F_Y(Y)`. -/
noncomputable def rankCorrelation (X Y : Ω → ℝ) (P : Measure Ω) : ℝ :=
  LinearIV.correlation (fun ω => cdf (P.map X) (X ω)) (fun ω => cdf (P.map Y) (Y ω)) P

/-- **The probability integral transform is invariant under strictly increasing maps.** For a
probability measure `P`, a measurable `X` and a strictly increasing `g`,
`F_{g(X)}(g(x)) = F_X(x)` for every `x`. -/
theorem cdf_map_comp_of_strictMono [IsProbabilityMeasure P] {X : Ω → ℝ} {g : ℝ → ℝ}
    (hX : Measurable X) (hg : StrictMono g) (x : ℝ) :
    cdf (P.map (g ∘ X)) (g x) = cdf (P.map X) x := by
  have hgX : Measurable (g ∘ X) := hg.monotone.measurable.comp hX
  rw [cdf_eq_real, cdf_eq_real, measureReal_def, measureReal_def,
    Measure.map_apply hgX measurableSet_Iic, Measure.map_apply hX measurableSet_Iic]
  congr 2
  ext ω
  simp [hg.le_iff_le]

/-- **The rank correlation is invariant under strictly increasing transformations** of either
variable, for measurable `X`, `Y` and a probability measure `P`. -/
theorem rankCorrelation_comp [IsProbabilityMeasure P] {X Y : Ω → ℝ} {g h : ℝ → ℝ}
    (hX : Measurable X) (hY : Measurable Y) (hg : StrictMono g) (hh : StrictMono h) :
    rankCorrelation (g ∘ X) (h ∘ Y) P = rankCorrelation X Y P := by
  have e₁ : (fun ω => cdf (P.map (g ∘ X)) ((g ∘ X) ω)) = fun ω => cdf (P.map X) (X ω) :=
    funext fun ω => cdf_map_comp_of_strictMono hX hg (X ω)
  have e₂ : (fun ω => cdf (P.map (h ∘ Y)) ((h ∘ Y) ω)) = fun ω => cdf (P.map Y) (Y ω) :=
    funext fun ω => cdf_map_comp_of_strictMono hY hh (Y ω)
  rw [rankCorrelation, rankCorrelation, e₁, e₂]

/-- A probability integral transform of a measurable variable is square integrable. -/
theorem memLp_cdf_comp [IsProbabilityMeasure P] (ν : Measure ℝ) {X : Ω → ℝ}
    (hX : Measurable X) : MemLp (fun ω => cdf ν (X ω)) 2 P :=
  MemLp.of_bound ((cdf ν).mono.measurable.comp hX).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [cdf_nonneg ν (X ω)], cdf_le_one ν (X ω)⟩)

/-- **The rank correlation lies in `[-1, 1]`** when both probability integral transforms have
nonzero variance. -/
theorem abs_rankCorrelation_le_one [IsProbabilityMeasure P] {X Y : Ω → ℝ} (hX : Measurable X)
    (hY : Measurable Y) (hVX : Var[fun ω => cdf (P.map X) (X ω); P] ≠ 0)
    (hVY : Var[fun ω => cdf (P.map Y) (Y ω); P] ≠ 0) :
    |rankCorrelation X Y P| ≤ 1 :=
  LinearIV.abs_correlation_le_one (memLp_cdf_comp _ hX) (memLp_cdf_comp _ hY) hVX hVY

/-- The uniform law on `(0, 1)` has mean `1/2`. -/
theorem integral_id_uniform : ∫ x, id x ∂(volume.restrict (Ioo (0 : ℝ) 1)) = 1 / 2 := by
  simp only [id]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    integral_id]
  norm_num

/-- The uniform law on `(0, 1)` has variance `1/12`. -/
theorem variance_id_uniform : Var[id; volume.restrict (Ioo (0 : ℝ) 1)] = 1 / 12 := by
  rw [variance_eq_integral measurable_id.aemeasurable, integral_id_uniform,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
  simp only [id]
  rw [intervalIntegral.integral_comp_sub_right (fun x => x ^ 2), integral_pow]
  norm_num

/-- **For a continuous margin the probability integral transform has mean `1/2`.** -/
theorem integral_cdf_comp [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : Measurable X)
    (hc : Continuous (cdf (P.map X))) : ∫ ω, cdf (P.map X) (X ω) ∂P = 1 / 2 := by
  have hlaw : HasLaw X (P.map X) P := ⟨hX.aemeasurable, rfl⟩
  rw [(Distributions.hasLaw_cdf_uniform hlaw hc).integral_eq, ← integral_id_uniform]
  rfl

/-- **For a continuous margin the probability integral transform has variance `1/12`.** -/
theorem variance_cdf_comp [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : Measurable X)
    (hc : Continuous (cdf (P.map X))) : Var[fun ω => cdf (P.map X) (X ω); P] = 1 / 12 := by
  have hlaw : HasLaw X (P.map X) P := ⟨hX.aemeasurable, rfl⟩
  rw [(Distributions.hasLaw_cdf_uniform hlaw hc).variance_eq, variance_id_uniform]

/-- **For continuous margins the rank correlation lies in `[-1, 1]`**, with no further
hypothesis. -/
theorem abs_rankCorrelation_le_one_of_continuous [IsProbabilityMeasure P] {X Y : Ω → ℝ}
    (hX : Measurable X) (hY : Measurable Y) (hcX : Continuous (cdf (P.map X)))
    (hcY : Continuous (cdf (P.map Y))) : |rankCorrelation X Y P| ≤ 1 :=
  abs_rankCorrelation_le_one hX hY (by rw [variance_cdf_comp hX hcX]; norm_num)
    (by rw [variance_cdf_comp hY hcY]; norm_num)

/-! ### The rank correlation of a Gaussian copula as a function of `ρ` -/

/-- The rank correlation `(6/π) arcsin(ρ/2)` of a Gaussian copula with correlation `ρ`. -/
noncomputable def gaussianRankCorrelation (ρ : ℝ) : ℝ := 6 / π * arcsin (ρ / 2)

/-- **Properties of `ρ ↦ (6/π) arcsin(ρ/2)`.** It is strictly increasing on `[-1, 1]`, takes the
values `-1`, `0`, `1` at `-1`, `0`, `1`, is positive exactly for positive `ρ ∈ [-1, 1]` and
negative exactly for negative `ρ`, maps `[-1, 1]` into `[-1, 1]`, and is inverted by
`ρ = 2 sin(π ρ_S / 6)`. -/
theorem gaussianRankCorrelation_properties :
    StrictMonoOn gaussianRankCorrelation (Icc (-1) 1) ∧
      gaussianRankCorrelation (-1) = -1 ∧ gaussianRankCorrelation 0 = 0 ∧
      gaussianRankCorrelation 1 = 1 ∧
      (∀ ρ ∈ Icc (-1 : ℝ) 1, 0 < gaussianRankCorrelation ρ ↔ 0 < ρ) ∧
      (∀ ρ ∈ Icc (-1 : ℝ) 1, gaussianRankCorrelation ρ < 0 ↔ ρ < 0) ∧
      (∀ ρ ∈ Icc (-1 : ℝ) 1, gaussianRankCorrelation ρ ∈ Icc (-1) 1) ∧
      (∀ ρ ∈ Icc (-1 : ℝ) 1, 2 * sin (π * gaussianRankCorrelation ρ / 6) = ρ) := by
  have hk : 0 < 6 / π := div_pos (by norm_num) pi_pos
  have hmem : ∀ ρ ∈ Icc (-1 : ℝ) 1, ρ / 2 ∈ Icc (-1 : ℝ) 1 := fun ρ hρ =>
    ⟨by linarith [hρ.1], by linarith [hρ.2]⟩
  have hmono : StrictMonoOn gaussianRankCorrelation (Icc (-1) 1) := fun a ha b hb hab =>
    mul_lt_mul_of_pos_left (strictMonoOn_arcsin (hmem a ha) (hmem b hb) (by linarith)) hk
  have h1 : gaussianRankCorrelation 1 = 1 := by
    rw [gaussianRankCorrelation, show (1 : ℝ) / 2 = sin (π / 6) by rw [sin_pi_div_six],
      arcsin_sin (by linarith [pi_pos]) (by linarith [pi_pos])]
    field_simp
  have hm1 : gaussianRankCorrelation (-1) = -1 := by
    rw [gaussianRankCorrelation, neg_div, arcsin_neg, mul_neg, ← gaussianRankCorrelation, h1]
  have h0 : gaussianRankCorrelation 0 = 0 := by simp [gaussianRankCorrelation]
  have h0m : (0 : ℝ) ∈ Icc (-1) 1 := ⟨by norm_num, by norm_num⟩
  refine ⟨hmono, hm1, h0, h1, fun ρ hρ => ?_, fun ρ hρ => ?_, fun ρ hρ => ?_, fun ρ hρ => ?_⟩
  · have := hmono.lt_iff_lt h0m hρ; rwa [h0] at this
  · have := hmono.lt_iff_lt hρ h0m; rwa [h0] at this
  · rw [mem_Icc]
    nth_rw 1 [← hm1]; nth_rw 2 [← h1]
    exact ⟨hmono.monotoneOn ⟨le_rfl, by norm_num⟩ hρ hρ.1,
      hmono.monotoneOn hρ ⟨by norm_num, le_rfl⟩ hρ.2⟩
  · rw [gaussianRankCorrelation, show π * (6 / π * arcsin (ρ / 2)) / 6 = arcsin (ρ / 2) by
      field_simp, sin_arcsin (hmem ρ hρ).1 (hmem ρ hρ).2]
    ring

end IndirectComparisonBias

end BiasAnalysis

end CausalInference
