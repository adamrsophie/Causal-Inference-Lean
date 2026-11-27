/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.InstrumentalVariables.Heterogeneity
public import CausalInference.InstrumentalVariables.LinearIV
public import Mathlib.Algebra.QuadraticDiscriminant

/-!
# Invalid instruments against least squares

When an instrument violates exogeneity, its IV estimand is biased, and it can be more biased than
the least squares slope that ignores the endogeneity of the treatment. This file makes the
comparison exact in the linear structural model `Y = α + β D + U` of
`CausalInference.LinearIVModel` (a general probability space, finite second moments, population
covariances). Source: NICE Decision Support Unit Technical Support Document 17 (Faria, Hernandez
Alava, Manca and Wailoo, 2015), Section 2.4.1 ("even moderate levels of endogeneity of the
instrument can lead to estimate parameters that are more inconsistent than those obtained from
methods which wrongly assume selection on observables") and Questions 17 and 18 of its
checklist (overidentifying restrictions; weak instruments). The document states these facts in
words; the statements below are their formalization.

## Main definitions

* `CausalInference.LinearIV.correlation`: `Cov(X, Y) / (sd(X) sd(Y))`.

## Main results

* `LinearIV.covariance_sq_le`, `LinearIV.abs_correlation_le_one`: the inequality of Cauchy and
  Schwarz for covariances.
* `LinearIVModel.ivBias_gt_olsBias_iff`: the IV estimand is strictly farther from `β` than the
  OLS slope iff `|Cov(Z, D)| |Cov(D, U)| < |Cov(Z, U)| Var(D)`;
  `LinearIVModel.ivBias_gt_olsBias_iff_correlation`: equivalently, when `Var(U) ≠ 0`,
  `|ρ(Z, D)| |ρ(D, U)| < |ρ(Z, U)|`.
* `LinearIVModel.ivBias_eq_correlation`, `LinearIVModel.olsBias_eq_correlation`: the two biases
  in correlation form; `LinearIVModel.abs_ivBias_ge`: with `sd(U) / sd(D) ≥ c > 0`, the IV
  bias is at least `c |ρ(Z, U)| / |ρ(Z, D)|`, so it grows without bound as `ρ(Z, D) → 0`
  (without the bound on the scale ratio it need not).
* `LinearIVModel.ivBias_gt_olsBias_of_abs_correlation_lt`: if `|ρ(Z, D)| < |ρ(Z, U)|`, the
  invalid instrument is worse than least squares, whatever the endogeneity of the treatment.
* `LinearIVModel.covRatio_eq_covRatio_of_exogenous`: two valid instruments in the linear
  (constant effect) model give the same IV estimand.
* `IVModel.covRatio_eq_of_homogeneous`: in a binary IV model with a constant effect `β`, the
  covariance ratio is `β` under exclusion, independence and relevance, without monotonicity.
* `InvalidInstrumentExample.worse_iv_ols`: a concrete model where the IV bias (`1`) exceeds the
  OLS bias (`1 / 2`).
* `InvalidInstrumentExample.weakFamily_bias`: a family with `ρ(Z, U) = 1` and squared
  first-stage correlation `1 / (1 + t²)`, in which the IV bias is `1` for every `t`.

## Implementation notes

`Var(Z) ≠ 0` and `Var(D) ≠ 0` are not hypotheses: they follow from relevance
`Cov(Z, D) ≠ 0` (`LinearIVModel.variances_ne_zero`). `Var(U) ≠ 0` is assumed in the correlation
statements so that `ρ(Z, U)` and `ρ(D, U)` are genuine quotients.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace CausalInference

namespace LinearIV

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Cauchy and Schwarz for covariances.** For square integrable `X` and `Y` under a
probability measure, `Cov(X, Y)² ≤ Var(X) Var(Y)`. -/
theorem covariance_sq_le [IsProbabilityMeasure μ] {X Y : Ω → ℝ} (hX : MemLp X 2 μ)
    (hY : MemLp Y 2 μ) : cov[X, Y; μ] ^ 2 ≤ Var[X; μ] * Var[Y; μ] := by
  have h : ∀ t : ℝ, 0 ≤ Var[X; μ] * (t * t) + 2 * cov[X, Y; μ] * t + Var[Y; μ] := by
    intro t
    have := variance_nonneg (fun ω ↦ t * X ω + Y ω) μ
    rw [variance_fun_add (hX.const_mul t) hY, variance_const_mul,
      covariance_const_mul_left] at this
    linarith
  have := discrim_le_zero h
  rw [discrim] at this
  linarith

/-- The correlation `Cov(X, Y) / (sd(X) sd(Y))` of two real random variables. The theorems
below assume both variances nonzero, so that it is a genuine quotient. -/
noncomputable def correlation (X Y : Ω → ℝ) (μ : Measure Ω) : ℝ :=
  cov[X, Y; μ] / (Real.sqrt Var[X; μ] * Real.sqrt Var[Y; μ])

/-- A correlation lies in `[-1, 1]` in absolute value (for square integrable variables with
nonzero variances, so that the correlation is a genuine quotient). -/
theorem abs_correlation_le_one [IsProbabilityMeasure μ] {X Y : Ω → ℝ} (hX : MemLp X 2 μ)
    (hY : MemLp Y 2 μ) (hVX : Var[X; μ] ≠ 0) (hVY : Var[Y; μ] ≠ 0) :
    |correlation X Y μ| ≤ 1 := by
  have h : 0 < Real.sqrt (Var[X; μ] * Var[Y; μ]) :=
    Real.sqrt_pos.2 (mul_pos (lt_of_le_of_ne (variance_nonneg _ _) (Ne.symm hVX))
      (lt_of_le_of_ne (variance_nonneg _ _) (Ne.symm hVY)))
  rw [correlation, abs_div,
    abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)),
    ← Real.sqrt_mul (variance_nonneg _ _), div_le_one h, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (covariance_sq_le hX hY)

end LinearIV

namespace LinearIVModel

open LinearIV

variable {Ω : Type*} [MeasurableSpace Ω] {L : LinearIVModel Ω} {μ : Measure Ω}

/-- A relevant instrument (`Cov(Z, D) ≠ 0`) forces `Var(Z) ≠ 0` and `Var(D) ≠ 0`, by the
inequality of Cauchy and Schwarz. -/
theorem variances_ne_zero [IsProbabilityMeasure μ] (h : L.SecondMoments μ)
    (hR : L.Relevance μ) : Var[L.Z; μ] ≠ 0 ∧ Var[L.D; μ] ≠ 0 := by
  have hcs := covariance_sq_le h.memLp_Z h.memLp_D
  have hpos : 0 < cov[L.Z, L.D; μ] ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hR))
  refine ⟨fun h0 ↦ ?_, fun h0 ↦ ?_⟩
  · rw [h0, zero_mul] at hcs; linarith
  · rw [h0, mul_zero] at hcs; linarith

/-- **Bias of an invalid instrument against bias of least squares, covariance form.** With
finite second moments and a relevant instrument, the IV estimand
`Cov(Z, Y) / Cov(Z, D)` is strictly farther from `β` than the OLS slope `Cov(D, Y) / Var(D)` if
and only if `|Cov(Z, D)| |Cov(D, U)| < |Cov(Z, U)| Var(D)`. -/
theorem ivBias_gt_olsBias_iff [IsProbabilityMeasure μ] (h : L.SecondMoments μ)
    (hR : L.Relevance μ) :
    |cov[L.Z, L.Y; μ] / cov[L.Z, L.D; μ] - L.β| > |cov[L.D, L.Y; μ] / Var[L.D; μ] - L.β| ↔
      |cov[L.Z, L.D; μ]| * |cov[L.D, L.U; μ]| < |cov[L.Z, L.U; μ]| * Var[L.D; μ] := by
  have hVD := (variances_ne_zero h hR).2
  have hVpos : 0 < Var[L.D; μ] := lt_of_le_of_ne (variance_nonneg _ _) (Ne.symm hVD)
  rw [covRatio_eq h hR, olsSlope_eq h.memLp_D h.memLp_U hVD, add_sub_cancel_left,
    add_sub_cancel_left, abs_div, abs_div, abs_of_pos hVpos, gt_iff_lt,
    div_lt_div_iff₀ hVpos (abs_pos.2 hR), mul_comm |cov[L.D, L.U; μ]|]

/-- **Bias of an invalid instrument against bias of least squares, correlation form** (NICE DSU
TSD 17, Section 2.4.1: "even moderate levels of endogeneity of the instrument can lead to
estimate parameters that are more inconsistent than those obtained from methods which wrongly
assume selection on observables"). With finite second moments, a relevant instrument and
`Var(U) ≠ 0` (so that the three correlations are genuine quotients), the IV estimand is strictly
farther from `β` than the OLS slope if and only if `|ρ(Z, D)| |ρ(D, U)| < |ρ(Z, U)|`. -/
theorem ivBias_gt_olsBias_iff_correlation [IsProbabilityMeasure μ] (h : L.SecondMoments μ)
    (hR : L.Relevance μ) (hU : Var[L.U; μ] ≠ 0) :
    |cov[L.Z, L.Y; μ] / cov[L.Z, L.D; μ] - L.β| > |cov[L.D, L.Y; μ] / Var[L.D; μ] - L.β| ↔
      |correlation L.Z L.D μ| * |correlation L.D L.U μ| < |correlation L.Z L.U μ| := by
  rw [ivBias_gt_olsBias_iff h hR]
  obtain ⟨hVZ, hVD⟩ := variances_ne_zero h hR
  have hsZ : 0 < Real.sqrt Var[L.Z; μ] :=
    Real.sqrt_pos.2 (lt_of_le_of_ne (variance_nonneg _ _) (Ne.symm hVZ))
  have hsD : 0 < Real.sqrt Var[L.D; μ] :=
    Real.sqrt_pos.2 (lt_of_le_of_ne (variance_nonneg _ _) (Ne.symm hVD))
  have hsU : 0 < Real.sqrt Var[L.U; μ] :=
    Real.sqrt_pos.2 (lt_of_le_of_ne (variance_nonneg _ _) (Ne.symm hU))
  have hD2 : Real.sqrt Var[L.D; μ] * Real.sqrt Var[L.D; μ] = Var[L.D; μ] :=
    Real.mul_self_sqrt (variance_nonneg _ _)
  simp only [correlation, abs_div, abs_mul, abs_of_pos hsZ, abs_of_pos hsD, abs_of_pos hsU]
  rw [div_mul_div_comm, div_lt_div_iff₀ (by positivity) (by positivity),
    show Real.sqrt Var[L.Z; μ] * Real.sqrt Var[L.D; μ] *
        (Real.sqrt Var[L.D; μ] * Real.sqrt Var[L.U; μ]) =
      Var[L.D; μ] * (Real.sqrt Var[L.Z; μ] * Real.sqrt Var[L.U; μ]) by
        linear_combination (Real.sqrt Var[L.Z; μ] * Real.sqrt Var[L.U; μ]) * hD2,
    ← mul_assoc |cov[L.Z, L.U; μ]|]
  exact (mul_lt_mul_iff_of_pos_right
    (show 0 < Real.sqrt Var[L.Z; μ] * Real.sqrt Var[L.U; μ] by positivity)).symm

/-- **The IV bias in correlation form.** With finite second moments, a relevant instrument and
`Var(U) ≠ 0`, `Cov(Z, Y) / Cov(Z, D) - β = (ρ(Z, U) / ρ(Z, D)) (sd(U) / sd(D))`. The bias is
inversely proportional to the first-stage correlation `ρ(Z, D)` only when the scale factor
`sd(U) / sd(D)` is held fixed. A fixed violation `ρ(Z, U)` of exogeneity together with
`ρ(Z, D) → 0` does not force the bias to grow: for independent fair coins `Z`, `V`, `U = Z`
and `D = Z + t V`, one has `ρ(Z, U) = 1` and `ρ(Z, D)² = 1 / (1 + t²) → 0` as `t` grows, while
the bias stays `1`, because `sd(U) / sd(D) → 0` at the same rate
(`InvalidInstrumentExample.weakFamily_bias`). With `sd(U) / sd(D)` bounded away from
`0`, the bias does grow without bound (`LinearIVModel.abs_ivBias_ge`), which is the sense in
which a weak instrument amplifies the bias (NICE DSU TSD 17, Section 2.4.1 and Question 18). -/
theorem ivBias_eq_correlation [IsProbabilityMeasure μ] (h : L.SecondMoments μ)
    (hR : L.Relevance μ) (hU : Var[L.U; μ] ≠ 0) :
    cov[L.Z, L.Y; μ] / cov[L.Z, L.D; μ] - L.β =
      correlation L.Z L.U μ / correlation L.Z L.D μ *
        (Real.sqrt Var[L.U; μ] / Real.sqrt Var[L.D; μ]) := by
  obtain ⟨hVZ, hVD⟩ := variances_ne_zero h hR
  have hsZ : Real.sqrt Var[L.Z; μ] ≠ 0 :=
    (Real.sqrt_pos.2 (lt_of_le_of_ne (variance_nonneg _ _) (Ne.symm hVZ))).ne'
  have hsD : Real.sqrt Var[L.D; μ] ≠ 0 :=
    (Real.sqrt_pos.2 (lt_of_le_of_ne (variance_nonneg _ _) (Ne.symm hVD))).ne'
  have hsU : Real.sqrt Var[L.U; μ] ≠ 0 :=
    (Real.sqrt_pos.2 (lt_of_le_of_ne (variance_nonneg _ _) (Ne.symm hU))).ne'
  rw [covRatio_eq h hR, add_sub_cancel_left, correlation, correlation]
  field_simp

/-- **A weak instrument amplifies the bias, at a bounded scale ratio.** With finite second
moments, a relevant instrument and `Var(U) ≠ 0`, if `0 ≤ c ≤ sd(U) / sd(D)`, then the absolute
IV bias is at least `c |ρ(Z, U)| / |ρ(Z, D)|`. So for a fixed violation `ρ(Z, U) ≠ 0` and a
scale ratio bounded below by `c > 0`, the bias grows without bound as `ρ(Z, D) → 0`. -/
theorem abs_ivBias_ge [IsProbabilityMeasure μ] (h : L.SecondMoments μ) (hR : L.Relevance μ)
    (hU : Var[L.U; μ] ≠ 0) {c : ℝ} (hc : 0 ≤ c)
    (hcr : c ≤ Real.sqrt Var[L.U; μ] / Real.sqrt Var[L.D; μ]) :
    c * |correlation L.Z L.U μ| / |correlation L.Z L.D μ| ≤
      |cov[L.Z, L.Y; μ] / cov[L.Z, L.D; μ] - L.β| := by
  rw [ivBias_eq_correlation h hR hU, abs_mul, abs_div,
    abs_of_nonneg (le_trans hc hcr), mul_comm c, mul_div_right_comm]
  exact mul_le_mul_of_nonneg_left hcr (by positivity)

/-- **The OLS bias in correlation form.** With finite second moments of `D` and `U` and
nonzero variances, `Cov(D, Y) / Var(D) - β = ρ(D, U) (sd(U) / sd(D))`. -/
theorem olsBias_eq_correlation [IsProbabilityMeasure μ] (hD : MemLp L.D 2 μ)
    (hUm : MemLp L.U 2 μ) (hVD : Var[L.D; μ] ≠ 0) (hU : Var[L.U; μ] ≠ 0) :
    cov[L.D, L.Y; μ] / Var[L.D; μ] - L.β =
      correlation L.D L.U μ * (Real.sqrt Var[L.U; μ] / Real.sqrt Var[L.D; μ]) := by
  have hsD : Real.sqrt Var[L.D; μ] ≠ 0 :=
    (Real.sqrt_pos.2 (lt_of_le_of_ne (variance_nonneg _ _) (Ne.symm hVD))).ne'
  have hsU : Real.sqrt Var[L.U; μ] ≠ 0 :=
    (Real.sqrt_pos.2 (lt_of_le_of_ne (variance_nonneg _ _) (Ne.symm hU))).ne'
  have hD2 : Real.sqrt Var[L.D; μ] * Real.sqrt Var[L.D; μ] = Var[L.D; μ] :=
    Real.mul_self_sqrt (variance_nonneg _ _)
  rw [olsSlope_eq hD hUm hVD, add_sub_cancel_left, correlation]
  field_simp
  linear_combination cov[L.D, L.U; μ] * hD2

/-- **A weak first stage makes an invalid instrument worse than least squares.** With finite
second moments, a relevant instrument and `Var(U) ≠ 0`: if the first-stage correlation is
smaller in absolute value than the correlation of the instrument with the error,
`|ρ(Z, D)| < |ρ(Z, U)|`, then the IV estimand is strictly farther from `β` than the OLS slope,
whatever the endogeneity `ρ(D, U)` of the treatment (because `|ρ(D, U)| ≤ 1`). -/
theorem ivBias_gt_olsBias_of_abs_correlation_lt [IsProbabilityMeasure μ]
    (h : L.SecondMoments μ) (hR : L.Relevance μ) (hU : Var[L.U; μ] ≠ 0)
    (hlt : |correlation L.Z L.D μ| < |correlation L.Z L.U μ|) :
    |cov[L.Z, L.Y; μ] / cov[L.Z, L.D; μ] - L.β| > |cov[L.D, L.Y; μ] / Var[L.D; μ] - L.β| :=
  (ivBias_gt_olsBias_iff_correlation h hR hU).2 (lt_of_le_of_lt
    (mul_le_of_le_one_right (abs_nonneg _) (abs_correlation_le_one h.memLp_D h.memLp_U
      (variances_ne_zero h hR).2 hU)) hlt)

/-- **Overidentification in the linear model under a constant effect** (NICE DSU TSD 17,
Question 17). If `Z` is a valid instrument (finite second moments, exogeneity, relevance) and
`W` is a second square integrable instrument with `Cov(W, U) = 0` and `Cov(W, D) ≠ 0`, the two
IV estimands agree: `Cov(W, Y) / Cov(W, D) = Cov(Z, Y) / Cov(Z, D)` (both equal `β`). -/
theorem covRatio_eq_covRatio_of_exogenous [IsProbabilityMeasure μ] (h : L.SecondMoments μ)
    (hE : L.Exogeneity μ) (hR : L.Relevance μ) {W : Ω → ℝ} (hW : MemLp W 2 μ)
    (hWU : cov[W, L.U; μ] = 0) (hWD : cov[W, L.D; μ] ≠ 0) :
    cov[W, L.Y; μ] / cov[W, L.D; μ] = cov[L.Z, L.Y; μ] / cov[L.Z, L.D; μ] := by
  rw [← beta_eq_covRatio h hE hR, covariance_Y hW h.memLp_D h.memLp_U, hWU, add_zero,
    mul_div_assoc, div_self hWD, mul_one]

end LinearIVModel

namespace IVModel

variable {Ω : Type*} [MeasurableSpace Ω] (M : IVModel Ω) {μ : Measure Ω}

/-- **The linear IV estimand under a homogeneous effect, without monotonicity.** Under the
exclusion restriction, instrument independence, relevance and integrable responses `Y z (D z)`,
if the unit-level effect equals `β` almost surely, the covariance ratio
`Cov(Z, Yobs) / Cov(Z, Dobs)` equals `β`. Unlike
`IVModel.LATEAssumptions.covRatio_eq_of_homogeneous`, monotonicity is not assumed. -/
theorem covRatio_eq_of_homogeneous [IsProbabilityMeasure μ] (hE : M.Exclusion μ)
    (hI : M.InstrumentIndependence μ) (hR : M.Relevance μ) (hY : ∀ z, Integrable (M.YD z) μ)
    {z : Bool} {β : ℝ} (hβ : ∀ᵐ ω ∂μ, M.effect z ω = β) :
    cov[fun ω ↦ boolToReal (M.Z ω), M.Yobs; μ] / cov[fun ω ↦ boolToReal (M.Z ω), M.DobsReal; μ] =
      β := by
  rw [M.covRatio_eq_wald hY hR, M.wald_eq_of_homogeneous hE hI hR hY hβ]

end IVModel

namespace InvalidInstrumentExample

open LinearIVExample IVModel

/-- An invalid instrument that is worse than least squares: `Z` and `V` are independent fair
coins (coded `0`/`1`), the treatment is `D = Z + V`, the structural error is `U = Z` (so the
instrument violates exogeneity), and `Y = U` (`α = 0`, `β = 0`). -/
noncomputable def worse : LinearIVModel (Bool × Bool) where
  α := 0
  β := 0
  Z x := boolToReal x.1
  D x := boolToReal x.1 + boolToReal x.2
  U x := boolToReal x.1

theorem worse_secondMoments : worse.SecondMoments coins where
  memLp_D := memLp_coins fun ⟨a, b⟩ ↦ by cases a <;> cases b <;> norm_num [worse]
  memLp_Z := memLp_coins fun ⟨a, b⟩ ↦ by cases a <;> norm_num [worse]
  memLp_U := memLp_coins fun ⟨a, b⟩ ↦ by cases a <;> norm_num [worse]

/-- **An invalid instrument strictly worse than least squares.** In `worse` the instrument is
relevant but not exogenous; the IV estimand is `1` and the OLS slope is `1 / 2`, while `β = 0`,
so the IV bias strictly exceeds the OLS bias, as `LinearIVModel.ivBias_gt_olsBias_iff`
predicts (`|Cov(Z, D)| |Cov(D, U)| = 1 / 16 < 1 / 8 = |Cov(Z, U)| Var(D)`). With a valid
instrument the comparison goes the other way: see `LinearIVExample.endogenous_iv_ols`. -/
theorem worse_iv_ols :
    ¬ worse.Exogeneity coins ∧ worse.Relevance coins ∧
      cov[worse.Z, worse.Y; coins] / cov[worse.Z, worse.D; coins] = 1 ∧
      cov[worse.D, worse.Y; coins] / Var[worse.D; coins] = 1 / 2 ∧
      |cov[worse.Z, worse.Y; coins] / cov[worse.Z, worse.D; coins] - worse.β| >
        |cov[worse.D, worse.Y; coins] / Var[worse.D; coins] - worse.β| := by
  have hZU : cov[worse.Z, worse.U; coins] = 1 / 4 := by
    simp only [covariance, integral_coins, worse]; norm_num
  have hZD : cov[worse.Z, worse.D; coins] = 1 / 4 := by
    simp only [covariance, integral_coins, worse]; norm_num
  have hDU : cov[worse.D, worse.U; coins] = 1 / 4 := by
    simp only [covariance, integral_coins, worse]; norm_num
  have hV : Var[worse.D; coins] = 1 / 2 := by
    rw [← covariance_self (measurable_of_countable _).aemeasurable]
    simp only [covariance, integral_coins, worse]; norm_num
  have hR : worse.Relevance coins := by rw [LinearIVModel.Relevance, hZD]; norm_num
  have hiv : cov[worse.Z, worse.Y; coins] / cov[worse.Z, worse.D; coins] = 1 := by
    rw [LinearIVModel.covRatio_eq worse_secondMoments hR, hZU, hZD]; norm_num [worse]
  have hols : cov[worse.D, worse.Y; coins] / Var[worse.D; coins] = 1 / 2 := by
    rw [LinearIVModel.olsSlope_eq worse_secondMoments.memLp_D worse_secondMoments.memLp_U
      (by rw [hV]; norm_num), hDU, hV]; norm_num [worse]
  refine ⟨fun h ↦ ?_, hR, hiv, hols, ?_⟩
  · rw [LinearIVModel.Exogeneity, hZU] at h; norm_num at h
  · rw [hiv, hols]; norm_num [worse]

/-- A family in which the first-stage correlation tends to `0` while the IV bias does not grow:
`Z` and `V` are independent fair coins (coded `0`/`1`), the structural error is `U = Z`, the
treatment is `D = Z + t V`, and `Y = U` (`α = 0`, `β = 0`). -/
noncomputable def weakFamily (t : ℝ) : LinearIVModel (Bool × Bool) where
  α := 0
  β := 0
  Z x := boolToReal x.1
  D x := boolToReal x.1 + t * boolToReal x.2
  U x := boolToReal x.1

/-- **A vanishing first-stage correlation does not by itself make the IV bias grow.** In
`weakFamily t` the instrument is relevant for every `t`, `ρ(Z, U) = 1`, and the squared
first-stage correlation is `Cov(Z, D)² / (Var(Z) Var(D)) = 1 / (1 + t²)`, which tends to `0`
as `t` grows; yet the IV bias `Cov(Z, Y) / Cov(Z, D) - β` equals `1` for every `t`. The scale
factor `sd(U) / sd(D)` of `LinearIVModel.ivBias_eq_correlation` shrinks at the same rate, so a
bound on it from below is needed in `LinearIVModel.abs_ivBias_ge`. -/
theorem weakFamily_bias (t : ℝ) :
    (weakFamily t).Relevance coins ∧
      LinearIV.correlation (weakFamily t).Z (weakFamily t).U coins = 1 ∧
      cov[(weakFamily t).Z, (weakFamily t).D; coins] ^ 2 /
          (Var[(weakFamily t).Z; coins] * Var[(weakFamily t).D; coins]) = 1 / (1 + t ^ 2) ∧
      cov[(weakFamily t).Z, (weakFamily t).Y; coins] /
          cov[(weakFamily t).Z, (weakFamily t).D; coins] - (weakFamily t).β = 1 := by
  have hZD : cov[(weakFamily t).Z, (weakFamily t).D; coins] = 1 / 4 := by
    simp only [covariance, integral_coins, weakFamily]; norm_num; ring
  have hZY : cov[(weakFamily t).Z, (weakFamily t).Y; coins] = 1 / 4 := by
    simp only [covariance, integral_coins, weakFamily, LinearIVModel.Y]; norm_num
  have hZU : cov[(weakFamily t).Z, (weakFamily t).U; coins] = 1 / 4 := by
    simp only [covariance, integral_coins, weakFamily]; norm_num
  have hVZ : Var[(weakFamily t).Z; coins] = 1 / 4 := by
    rw [← covariance_self (measurable_of_countable _).aemeasurable]
    simp only [covariance, integral_coins, weakFamily]; norm_num
  have hVU : Var[(weakFamily t).U; coins] = 1 / 4 := by
    rw [← covariance_self (measurable_of_countable _).aemeasurable]
    simp only [covariance, integral_coins, weakFamily]; norm_num
  have hVD : Var[(weakFamily t).D; coins] = (1 + t ^ 2) / 4 := by
    rw [← covariance_self (measurable_of_countable _).aemeasurable]
    simp only [covariance, integral_coins, weakFamily]; norm_num; ring
  have hs : Real.sqrt (1 / 4 : ℝ) * Real.sqrt (1 / 4) = 1 / 4 :=
    Real.mul_self_sqrt (by norm_num)
  refine ⟨by rw [LinearIVModel.Relevance, hZD]; norm_num, ?_, ?_, ?_⟩
  · rw [LinearIV.correlation, hZU, hVZ, hVU, hs]; norm_num
  · rw [hZD, hVZ, hVD]; field_simp
  · rw [hZY, hZD]; norm_num [weakFamily]

end InvalidInstrumentExample

end CausalInference
