/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.InstrumentalVariables.Bounds
public import Mathlib.Probability.Moments.Variance

/-!
# Linear instrumental variables

The linear structural model `Y = α + β D + U` with real treatment, instrument and error, as in
Wooldridge (*Econometric Analysis of Cross Section and Panel Data*), and its relation to the Wald
ratio (Wald 1940) and to the local average treatment effect of Angrist, Imbens and Rubin (1996).
This model is separate from the binary potential outcomes model `CausalInference.IVModel`; the
two meet only through the covariance ratio.

## Main definitions

* `CausalInference.LinearIVModel`: intercept `α`, slope `β`, treatment `D`, instrument `Z` and
  error `U`; the outcome `LinearIVModel.Y` is `α + β D + U`.
* `LinearIVModel.SecondMoments`, `LinearIVModel.Exogeneity` (`Cov(Z, U) = 0`),
  `LinearIVModel.Relevance` (`Cov(Z, D) ≠ 0`), each a separate `Prop`.

## Main results

* `LinearIVModel.beta_eq_covRatio`: `β = Cov(Z, Y) / Cov(Z, D)` under finite second moments,
  exogeneity and relevance; `LinearIVModel.covRatio_eq`: in general the ratio is
  `β + Cov(Z, U) / Cov(Z, D)`.
* `LinearIVModel.olsSlope_eq`, `LinearIVModel.olsSlope_ne_beta`: the OLS slope is
  `β + Cov(D, U) / Var(D)`, biased under endogeneity.
* `LinearIV.covariance_boolToReal`, `LinearIV.covRatio_eq_waldRatio`: for a binary instrument
  the covariance ratio is the Wald ratio.
* `IVModel.covRatio_eq_wald`, `IVModel.LATEAssumptions.covRatio_eq_complierEffect`: in a binary
  IV model the covariance ratio is the Wald ratio, hence under the LATE assumptions the complier
  average causal effect; `IVModel.LATEAssumptions.covRatio_eq_of_homogeneous`: it equals a
  constant effect `β` when unit-level effects are homogeneous.
* `LinearIVExample.endogenous_iv_ols`: a valid instrument where IV recovers `β = 1` and OLS gives
  `3 / 2`; `LinearIVExample.invalid_iv_biased`: an instrument violating exogeneity, where the IV
  ratio is `1` while `β = 0`, matching the bias `Cov(Z, U) / Cov(Z, D)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace CausalInference

/-- A linear structural model `Y = α + β D + U` with a real treatment `D`, a real instrument `Z`
and a real structural error `U` on a sample space `Ω`. The parameter of interest is the slope
`β`, the effect of a unit change of `D` on `Y`, the same for every unit. -/
structure LinearIVModel (Ω : Type*) where
  /-- The intercept. -/
  α : ℝ
  /-- The structural slope, the constant causal effect of the treatment. -/
  β : ℝ
  /-- The treatment. -/
  D : Ω → ℝ
  /-- The instrument. -/
  Z : Ω → ℝ
  /-- The structural error. -/
  U : Ω → ℝ

namespace LinearIVModel

variable {Ω : Type*} [MeasurableSpace Ω] (L : LinearIVModel Ω) (μ : Measure Ω)

/-- The outcome, given by the structural equation `Y = α + β D + U`. -/
def Y (ω : Ω) : ℝ := L.α + L.β * L.D ω + L.U ω

/-- Finite second moments of the treatment, the instrument and the error. -/
structure SecondMoments : Prop where
  memLp_D : MemLp L.D 2 μ
  memLp_Z : MemLp L.Z 2 μ
  memLp_U : MemLp L.U 2 μ

/-- Exogeneity of the instrument: `Cov(Z, U) = 0`. -/
def Exogeneity : Prop := cov[L.Z, L.U; μ] = 0

/-- Relevance of the instrument: `Cov(Z, D) ≠ 0`. -/
def Relevance : Prop := cov[L.Z, L.D; μ] ≠ 0

variable {L μ}

/-- Covariance of any square integrable `W` with the outcome:
`Cov(W, Y) = β Cov(W, D) + Cov(W, U)`. -/
theorem covariance_Y [IsProbabilityMeasure μ] {W : Ω → ℝ} (hW : MemLp W 2 μ)
    (hD : MemLp L.D 2 μ) (hU : MemLp L.U 2 μ) :
    cov[W, L.Y; μ] = L.β * cov[W, L.D; μ] + cov[W, L.U; μ] := by
  have hY : L.Y = fun ω ↦ L.α + ((fun ω ↦ L.β * L.D ω) + L.U) ω := by
    funext ω; simp only [Y, Pi.add_apply]; ring
  rw [hY, covariance_const_add_right (((hD.const_mul L.β).add hU).integrable one_le_two),
    covariance_add_right hW (hD.const_mul L.β) hU, covariance_const_mul_right]

/-- **The IV estimand with its bias.** With finite second moments and a relevant instrument,
`Cov(Z, Y) / Cov(Z, D) = β + Cov(Z, U) / Cov(Z, D)`. -/
theorem covRatio_eq [IsProbabilityMeasure μ] (h : L.SecondMoments μ) (hR : L.Relevance μ) :
    cov[L.Z, L.Y; μ] / cov[L.Z, L.D; μ] = L.β + cov[L.Z, L.U; μ] / cov[L.Z, L.D; μ] := by
  rw [covariance_Y h.memLp_Z h.memLp_D h.memLp_U, add_div, mul_div_assoc, div_self hR, mul_one]

/-- **Identification of the structural slope by linear IV** (see Wooldridge, *Econometric
Analysis of Cross Section and Panel Data*). With finite second moments, exogeneity
`Cov(Z, U) = 0` and relevance `Cov(Z, D) ≠ 0`, `β = Cov(Z, Y) / Cov(Z, D)`. -/
theorem beta_eq_covRatio [IsProbabilityMeasure μ] (h : L.SecondMoments μ)
    (hE : L.Exogeneity μ) (hR : L.Relevance μ) :
    L.β = cov[L.Z, L.Y; μ] / cov[L.Z, L.D; μ] := by
  rw [covRatio_eq h hR, show cov[L.Z, L.U; μ] = 0 from hE, zero_div, add_zero]

/-- If exogeneity fails (`Cov(Z, U) ≠ 0`) but the instrument is relevant, the IV ratio differs
from `β`, by exactly `Cov(Z, U) / Cov(Z, D)`. -/
theorem covRatio_ne_beta [IsProbabilityMeasure μ] (h : L.SecondMoments μ) (hR : L.Relevance μ)
    (hU : cov[L.Z, L.U; μ] ≠ 0) : cov[L.Z, L.Y; μ] / cov[L.Z, L.D; μ] ≠ L.β := by
  rw [covRatio_eq h hR]
  intro h'
  exact div_ne_zero hU hR (by linarith)

/-- **Ordinary least squares under endogeneity.** With finite second moments of `D` and `U` and
`Var(D) ≠ 0`, the OLS slope is `Cov(D, Y) / Var(D) = β + Cov(D, U) / Var(D)`. -/
theorem olsSlope_eq [IsProbabilityMeasure μ] (hD : MemLp L.D 2 μ) (hU : MemLp L.U 2 μ)
    (hV : Var[L.D; μ] ≠ 0) :
    cov[L.D, L.Y; μ] / Var[L.D; μ] = L.β + cov[L.D, L.U; μ] / Var[L.D; μ] := by
  rw [covariance_Y hD hD hU, covariance_self hD.aemeasurable, add_div, mul_div_assoc,
    div_self hV, mul_one]

/-- OLS is biased when the treatment is correlated with the error: if `Cov(D, U) ≠ 0` and
`Var(D) ≠ 0`, the OLS slope differs from `β`. -/
theorem olsSlope_ne_beta [IsProbabilityMeasure μ] (hD : MemLp L.D 2 μ) (hU : MemLp L.U 2 μ)
    (hV : Var[L.D; μ] ≠ 0) (hDU : cov[L.D, L.U; μ] ≠ 0) :
    cov[L.D, L.Y; μ] / Var[L.D; μ] ≠ L.β := by
  rw [olsSlope_eq hD hU hV]
  intro h'
  exact div_ne_zero hDU hV (by linarith)

end LinearIVModel

/-! ### Binary instrument: the Wald ratio -/

namespace LinearIV

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Covariance with a binary instrument: for `Zb : Ω → Bool` measurable, coded as `0`/`1`, and
`X` integrable, `Cov(Z, X) = P(Z = 1) P(Z = 0) (E[X | Z = 1] - E[X | Z = 0])`, with conditional
means taken against `μ[|Z = z]`. Only integrability of `X` is needed, since `Z` is bounded. -/
theorem covariance_boolToReal [IsProbabilityMeasure μ] {Zb : Ω → Bool} (hZ : Measurable Zb)
    {X : Ω → ℝ} (hX : Integrable X μ) :
    cov[fun ω ↦ IVModel.boolToReal (Zb ω), X; μ] =
      μ.real (Zb ⁻¹' {true}) * μ.real (Zb ⁻¹' {false}) *
        (∫ ω, X ω ∂μ[|Zb ⁻¹' {true}] - ∫ ω, X ω ∂μ[|Zb ⁻¹' {false}]) := by
  set S := Zb ⁻¹' {true} with hSdef
  have hS : MeasurableSet S := hZ (measurableSet_singleton true)
  have hc : Zb ⁻¹' {false} = Sᶜ := by ext ω; simp [S]
  rw [hc]
  have hind : (fun ω ↦ IVModel.boolToReal (Zb ω)) = S.indicator 1 := by
    funext ω; by_cases h : Zb ω = true <;> simp [S, Set.indicator, h, IVModel.boolToReal]
  have hp : ∫ ω, S.indicator (1 : Ω → ℝ) ω ∂μ = μ.real S := integral_indicator_one hS
  have hq : μ.real Sᶜ = 1 - μ.real S := probReal_compl_eq_one_sub hS
  have e1 := measureReal_mul_integral_cond (μ := μ) S X
  have e2 := measureReal_mul_integral_cond (μ := μ) Sᶜ X
  have hsplit := integral_add_compl hS hX
  have hpt : ∀ ω, (S.indicator (1 : Ω → ℝ) ω - μ.real S) * (X ω - ∫ x, X x ∂μ) =
      S.indicator X ω - μ.real S * X ω - (∫ x, X x ∂μ) * S.indicator (1 : Ω → ℝ) ω +
        μ.real S * ∫ x, X x ∂μ := by
    intro ω; by_cases h : ω ∈ S <;> simp [Set.indicator, h] <;> ring
  have i1 : Integrable (S.indicator (1 : Ω → ℝ)) μ := (integrable_const 1).indicator hS
  rw [hind, covariance, hp, integral_congr_ae (ae_of_all _ hpt), integral_add, integral_sub,
    integral_sub, integral_indicator hS, integral_const_mul, integral_const_mul, hp,
    integral_const, probReal_univ, one_smul]
  · linear_combination μ.real S * hsplit - μ.real Sᶜ * e1 + μ.real S * e2 -
      (∫ ω in S, X ω ∂μ) * hq
  all_goals first
    | exact hX.indicator hS | exact hX.const_mul _ | exact i1.const_mul _
    | exact integrable_const _ | exact (hX.indicator hS).sub (hX.const_mul _)
    | exact ((hX.indicator hS).sub (hX.const_mul _)).sub (i1.const_mul _)

/-- **Covariance ratio equals the Wald ratio** for a binary instrument (Wald 1940). If both
instrument values have positive probability and the first stage
`E[D | Z = 1] - E[D | Z = 0]` is nonzero, then for integrable `X` and `D`,
`Cov(Z, X) / Cov(Z, D) = (E[X | Z = 1] - E[X | Z = 0]) / (E[D | Z = 1] - E[D | Z = 0])`. -/
theorem covRatio_eq_waldRatio [IsProbabilityMeasure μ] {Zb : Ω → Bool} (hZ : Measurable Zb)
    {X D : Ω → ℝ} (hX : Integrable X μ) (hD : Integrable D μ) (h₁ : μ (Zb ⁻¹' {true}) ≠ 0)
    (h₀ : μ (Zb ⁻¹' {false}) ≠ 0)
    (hR : ∫ ω, D ω ∂μ[|Zb ⁻¹' {true}] - ∫ ω, D ω ∂μ[|Zb ⁻¹' {false}] ≠ 0) :
    cov[fun ω ↦ IVModel.boolToReal (Zb ω), X; μ] / cov[fun ω ↦ IVModel.boolToReal (Zb ω), D; μ] =
      (∫ ω, X ω ∂μ[|Zb ⁻¹' {true}] - ∫ ω, X ω ∂μ[|Zb ⁻¹' {false}]) /
        (∫ ω, D ω ∂μ[|Zb ⁻¹' {true}] - ∫ ω, D ω ∂μ[|Zb ⁻¹' {false}]) := by
  have hp : μ.real (Zb ⁻¹' {true}) ≠ 0 := fun h ↦ h₁ ((measureReal_eq_zero_iff).1 h)
  have hq : μ.real (Zb ⁻¹' {false}) ≠ 0 := fun h ↦ h₀ ((measureReal_eq_zero_iff).1 h)
  rw [covariance_boolToReal hZ hX, covariance_boolToReal hZ hD,
    div_eq_div_iff (mul_ne_zero (mul_ne_zero hp hq) hR) hR]
  ring

end LinearIV

namespace IVModel

variable {Ω : Type*} [MeasurableSpace Ω] (M : IVModel Ω) {μ : Measure Ω}

/-- With integrable potential outcomes the observed outcome is integrable. -/
theorem integrable_Yobs (hY : ∀ z d, Integrable (M.Y z d) μ) : Integrable M.Yobs μ := by
  refine (((hY true true).norm.add (hY true false).norm).add
    ((hY false true).norm.add (hY false false).norm)).mono'
    M.measurable_Yobs.aestronglyMeasurable (ae_of_all _ fun ω ↦ ?_)
  have := norm_nonneg (M.Y true true ω)
  have := norm_nonneg (M.Y true false ω)
  have := norm_nonneg (M.Y false true ω)
  have := norm_nonneg (M.Y false false ω)
  simp only [Yobs, Dobs, Pi.add_apply]
  cases M.Z ω <;> cases M.D _ ω <;> linarith

/-- The observed treatment, coded as a real number, is integrable for a finite measure. -/
theorem integrable_DobsReal [IsFiniteMeasure μ] : Integrable M.DobsReal μ := by
  refine Integrable.of_bound
    (measurable_boolToReal.comp M.measurable_Dobs).aestronglyMeasurable 1
    (ae_of_all _ fun ω ↦ ?_)
  simp only [DobsReal, boolToReal]
  split_ifs <;> simp

/-- **The linear IV estimand of a binary IV model is the Wald ratio.** With integrable potential
outcomes, `P(Z = z) ≠ 0` for both `z` and relevance, the covariance ratio
`Cov(Z, Yobs) / Cov(Z, Dobs)` (with `Z` and `Dobs` coded as `0`/`1`) equals `M.wald μ`. -/
theorem covRatio_eq_wald [IsProbabilityMeasure μ] (hY : ∀ z d, Integrable (M.Y z d) μ)
    (h₁ : μ (M.instrumentEq true) ≠ 0) (h₀ : μ (M.instrumentEq false) ≠ 0)
    (hR : M.Relevance μ) :
    cov[fun ω ↦ boolToReal (M.Z ω), M.Yobs; μ] / cov[fun ω ↦ boolToReal (M.Z ω), M.DobsReal; μ] =
      M.wald μ :=
  LinearIV.covRatio_eq_waldRatio M.measurable_Z (M.integrable_Yobs hY) M.integrable_DobsReal h₁ h₀
    hR

/-- **The linear IV estimand under the LATE assumptions is the complier effect.** Under
exclusion, instrument independence, monotonicity, relevance, `0 < P(Z = 1) < 1` and integrable
potential outcomes, the covariance ratio `Cov(Z, Yobs) / Cov(Z, Dobs)` equals the complier
average causal effect `E[Y z 1 - Y z 0 | compliers]`, which in general differs from the average
treatment effect (see `IVCounterexample.ate_not_identified`). -/
theorem LATEAssumptions.covRatio_eq_complierEffect [IsProbabilityMeasure μ] {M : IVModel Ω}
    (h : M.LATEAssumptions μ) (z : Bool) :
    cov[fun ω ↦ boolToReal (M.Z ω), M.Yobs; μ] / cov[fun ω ↦ boolToReal (M.Z ω), M.DobsReal; μ] =
      M.complierEffect μ z := by
  have h₀ : μ (M.instrumentEq false) ≠ 0 := by
    have hc : M.instrumentEq false = (M.instrumentEq true)ᶜ := by
      ext ω; simp [instrumentEq]
    rw [hc, prob_compl_eq_one_sub (M.measurableSet_instrumentEq true)]
    exact (tsub_pos_of_lt h.instrument_lt_one).ne'
  rw [M.covRatio_eq_wald h.integrable h.instrument_pos.ne' h₀ h.relevance, h.wald_eq z]

/-- **Homogeneous effects.** If, in addition to the LATE assumptions, the unit-level effect
`Y z 1 - Y z 0` equals a constant `β` almost surely, then the linear IV estimand
`Cov(Z, Yobs) / Cov(Z, Dobs)` equals `β`. Without homogeneity it is only the complier effect
(`LATEAssumptions.covRatio_eq_complierEffect`). -/
theorem LATEAssumptions.covRatio_eq_of_homogeneous [IsProbabilityMeasure μ] {M : IVModel Ω}
    (h : M.LATEAssumptions μ) {z : Bool} {β : ℝ} (hβ : ∀ᵐ ω ∂μ, M.effect z ω = β) :
    cov[fun ω ↦ boolToReal (M.Z ω), M.Yobs; μ] / cov[fun ω ↦ boolToReal (M.Z ω), M.DobsReal; μ] =
      β := by
  have h₀ : μ (M.instrumentEq false) ≠ 0 := by
    have hc : M.instrumentEq false = (M.instrumentEq true)ᶜ := by
      ext ω; simp [instrumentEq]
    rw [hc, prob_compl_eq_one_sub (M.measurableSet_instrumentEq true)]
    exact (tsub_pos_of_lt h.instrument_lt_one).ne'
  have hCpos := (M.relevance_iff h.independence h.monotonicity h.instrument_pos.ne' h₀).1
    h.relevance
  have hC : μ M.compliers ≠ 0 := fun h0 ↦ by
    rw [measureReal_def, h0, ENNReal.toReal_zero] at hCpos; exact lt_irrefl _ hCpos
  have := cond_isProbabilityMeasure (μ := μ) hC
  rw [h.covRatio_eq_complierEffect z, complierEffect,
    integral_congr_ae (cond_absolutelyContinuous.ae_le hβ), integral_const, probReal_univ,
    one_smul]

end IVModel

/-! ### Concrete examples -/

namespace LinearIVExample

open IVModel

/-- Two independent fair coins: the uniform distribution on `Bool × Bool`. -/
noncomputable def coins : Measure (Bool × Bool) := uniformOn univ

instance : IsProbabilityMeasure coins := by unfold coins; infer_instance

/-- The mean of any function of two fair coins is its average over the four outcomes. -/
theorem integral_coins (f : Bool × Bool → ℝ) :
    ∫ x, f x ∂coins =
      (f (true, true) + f (true, false) + f (false, true) + f (false, false)) / 4 := by
  rw [coins, integral_fintype .of_finite]
  simp [uniformOn_univ, measureReal_def, Fintype.sum_prod_type]
  ring

theorem memLp_coins {f : Bool × Bool → ℝ} (hf : ∀ x, |f x| ≤ 2) : MemLp f 2 coins :=
  MemLp.of_bound (measurable_of_countable f).aestronglyMeasurable 2
    (ae_of_all _ fun x ↦ by simpa [Real.norm_eq_abs] using hf x)

/-- A valid instrument with an endogenous treatment: `Z` and `V` are independent fair coins
(coded `0`/`1`), the treatment is `D = Z + V`, the structural error is `U = V`, and
`Y = D + U` (`α = 0`, `β = 1`). Then `Cov(Z, U) = 0` but `Cov(D, U) ≠ 0`. -/
noncomputable def endogenous : LinearIVModel (Bool × Bool) where
  α := 0
  β := 1
  Z x := boolToReal x.1
  D x := boolToReal x.1 + boolToReal x.2
  U x := boolToReal x.2

theorem endogenous_secondMoments : endogenous.SecondMoments coins where
  memLp_D := memLp_coins fun ⟨a, b⟩ ↦ by cases a <;> cases b <;> norm_num [endogenous]
  memLp_Z := memLp_coins fun ⟨a, b⟩ ↦ by cases a <;> cases b <;> norm_num [endogenous]
  memLp_U := memLp_coins fun ⟨a, b⟩ ↦ by cases a <;> cases b <;> norm_num [endogenous]

/-- **IV recovers `β` while OLS does not.** In `endogenous` the instrument is exogenous and
relevant, so `Cov(Z, Y) / Cov(Z, D) = β = 1`, while the OLS slope is
`Cov(D, Y) / Var(D) = 3 / 2 ≠ β`. -/
theorem endogenous_iv_ols :
    endogenous.Exogeneity coins ∧ endogenous.Relevance coins ∧
      cov[endogenous.Z, endogenous.Y; coins] / cov[endogenous.Z, endogenous.D; coins] =
        endogenous.β ∧
      cov[endogenous.D, endogenous.Y; coins] / Var[endogenous.D; coins] = 3 / 2 ∧
      cov[endogenous.D, endogenous.Y; coins] / Var[endogenous.D; coins] ≠ endogenous.β := by
  have hE : endogenous.Exogeneity coins := by
    simp only [LinearIVModel.Exogeneity, covariance, integral_coins, endogenous]
    norm_num
  have hR : endogenous.Relevance coins := by
    simp only [LinearIVModel.Relevance, covariance, integral_coins, endogenous]
    norm_num
  have hV : Var[endogenous.D; coins] = 1 / 2 := by
    rw [← covariance_self (measurable_of_countable _).aemeasurable]
    simp only [covariance, integral_coins, endogenous]
    norm_num
  have hDU : cov[endogenous.D, endogenous.U; coins] = 1 / 4 := by
    simp only [covariance, integral_coins, endogenous]
    norm_num
  have hols := LinearIVModel.olsSlope_eq endogenous_secondMoments.memLp_D
    endogenous_secondMoments.memLp_U (by rw [hV]; norm_num)
  have h32 : cov[endogenous.D, endogenous.Y; coins] / Var[endogenous.D; coins] = 3 / 2 := by
    rw [hols, hV, hDU]; norm_num [endogenous]
  refine ⟨hE, hR, (LinearIVModel.beta_eq_covRatio endogenous_secondMoments hE hR).symm, h32, ?_⟩
  rw [h32]; norm_num [endogenous]

/-- An instrument violating exogeneity: `Z` is a fair coin (coded `0`/`1`) and
`D = U = Z`, with `Y = U` (`α = 0`, `β = 0`). Then `Cov(Z, U) ≠ 0`. -/
noncomputable def invalid : LinearIVModel (Bool × Bool) where
  α := 0
  β := 0
  Z x := boolToReal x.1
  D x := boolToReal x.1
  U x := boolToReal x.1

theorem invalid_secondMoments : invalid.SecondMoments coins where
  memLp_D := memLp_coins fun ⟨a, b⟩ ↦ by cases a <;> norm_num [invalid]
  memLp_Z := memLp_coins fun ⟨a, b⟩ ↦ by cases a <;> norm_num [invalid]
  memLp_U := memLp_coins fun ⟨a, b⟩ ↦ by cases a <;> norm_num [invalid]

/-- **Counterexample: exogeneity fails.** In `invalid` the instrument is relevant but
`Cov(Z, U) = 1 / 4 ≠ 0`; the IV ratio equals `β + Cov(Z, U) / Cov(Z, D) = 1`, which differs from
`β = 0`. -/
theorem invalid_iv_biased :
    ¬ invalid.Exogeneity coins ∧ invalid.Relevance coins ∧
      cov[invalid.Z, invalid.Y; coins] / cov[invalid.Z, invalid.D; coins] =
        invalid.β + cov[invalid.Z, invalid.U; coins] / cov[invalid.Z, invalid.D; coins] ∧
      cov[invalid.Z, invalid.Y; coins] / cov[invalid.Z, invalid.D; coins] = 1 ∧
      cov[invalid.Z, invalid.Y; coins] / cov[invalid.Z, invalid.D; coins] ≠ invalid.β := by
  have hZU : cov[invalid.Z, invalid.U; coins] = 1 / 4 := by
    simp only [covariance, integral_coins, invalid]
    norm_num
  have hZD : cov[invalid.Z, invalid.D; coins] = 1 / 4 := by
    simp only [covariance, integral_coins, invalid]
    norm_num
  have hR : invalid.Relevance coins := by
    rw [LinearIVModel.Relevance, hZD]; norm_num
  have hbias := LinearIVModel.covRatio_eq invalid_secondMoments hR
  have h1 : cov[invalid.Z, invalid.Y; coins] / cov[invalid.Z, invalid.D; coins] = 1 := by
    rw [hbias, hZU, hZD]; norm_num [invalid]
  refine ⟨fun h ↦ ?_, hR, hbias, h1, ?_⟩
  · rw [LinearIVModel.Exogeneity, hZU] at h; norm_num at h
  · rw [h1]; norm_num [invalid]

end LinearIVExample

end CausalInference
