/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.Probability.UniformOn
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Analysis.Real.Sqrt

/-!
# Linear panel models: fixed effects, first differences, pooled and random effects slopes

The linear panel model `Y t = δ t + α + β D t + ε t` with a time-invariant unit effect `α`
(unobserved heterogeneity), deterministic period effects `δ t`, a common causal slope `β` and
idiosyncratic errors `ε t`, for a balanced panel. Units are the points of a probability space
`(Ω, μ)` (one unit drawn from the population); periods are the elements of a type `τ`, finite
where a sum over periods appears. Every estimator is formalized by its population estimand, a
ratio of covariances; sampling and consistency are not treated here.

## Main definitions

* `CausalInference.LinearPanel`, `LinearPanel.Y`, `LinearPanel.SecondMoments`.
* `LinearPanel.StrictExogeneity` (`Cov(D s, ε t) = 0` for all periods `s, t`) and
  `LinearPanel.ContemporaneousExogeneity` (`Cov(D t, ε t) = 0`). Strict exogeneity is used in
  moment form; `LinearPanel.strictExogeneity_of_condExp` derives it from the textbook conditional
  mean form `E[ε t | D, α] = 0`.
* `LinearPanel.fdSlope` (first differences over any finite set of period pairs),
  `LinearPanel.quasiSlope` (quasi-demeaning `X t - θ X̄`), `LinearPanel.withinSlope` (`θ = 1`),
  `LinearPanel.pooledSlope` (`θ = 0`). These slopes are pooled over periods with period dummies.
* `LinearPanel.ordinarySlope`: the ordinary pooled least squares slope of the stacked data with
  a single intercept (no period dummies), `LinearPanel.stackedCov`, `LinearPanel.grandMean`.
* `LinearPanel.compoundSymmetric` (the composite error covariance `σε² I + σα² 1 1ᵀ`),
  `LinearPanel.periodAverage` (the matrix `1 1ᵀ / T`), `LinearPanel.reTheta` (the random
  effects parameter `1 - √(σε² / (σε² + T σα²))`).
* `LinearPanel.lsObjective`, `LinearPanel.quasiObjective` (population least squares objectives
  with period intercepts), `LinearPanel.glsObjective` (`E[rᵀ V⁻¹ r]`).

## Main results

* `LinearPanel.fdSlope_eq`, `LinearPanel.fdSlope_eq_beta`, `LinearPanel.fdSlope_pair_eq_beta`:
  the first-difference slope is `β` plus a term in `Cov(ΔD, Δε)` only, so under strict
  exogeneity it equals `β` for every joint law of the unit effect and the treatment.
* `LinearPanel.quasiSlope_eq`: under strict exogeneity the quasi-demeaned slope is
  `β + (1 - θ)² ∑ₜ Cov(D t, α) / ∑ₜ Var(D t - θ D̄)`. Corollaries:
  `LinearPanel.withinSlope_eq_beta` (fixed effects identify `β`),
  `LinearPanel.quasiSlope_eq_beta_of_uncorrelated` (quasi-demeaned slopes identify `β` when
  `∑ₜ Cov(D t, α) = 0`), `LinearPanel.quasiSlope_ne_beta` (they differ from `β` when `θ ≠ 1` and
  `∑ₜ Cov(D t, α) ≠ 0`). The condition is on the sum over periods: correlations of opposite
  sign in different periods can cancel, and then every quasi-demeaned slope equals `β`.
* `LinearPanel.quasi_mul_quasi_mul_compoundSymmetric`, `LinearPanel.inv_compoundSymmetric`,
  `LinearPanel.gls_quadForm_eq`, `LinearPanel.quasiDemean_eq_mulVec`: under compound symmetry
  with `σε² > 0` and `σα² ≥ 0`, and with `(1 - θ)² (σε² + T σα²) = σε²` (solved by `reTheta`,
  which lies in `[0, 1)`), the inverse covariance is `σε⁻² (I - θ 1 1ᵀ / T)²`, so the generalized
  least squares quadratic form of a unit's residual vector is `σε⁻²` times the squared norm of
  its quasi-demeaned residual vector. `LinearPanel.gls_quadForm_of_compoundSymmetry` states
  this for the model under the hypothesis `LinearPanel.CompoundSymmetry` on the composite errors.
* `LinearPanel.lsSlope_isMin`, `LinearPanel.quasiSlope_isLeastSquares`,
  `LinearPanel.withinSlope_isLeastSquares`, `LinearPanel.pooledSlope_isLeastSquares`: under
  second moments and a positive pooled treatment variance, each covariance ratio slope is the
  unique minimizer of its population least squares objective with period intercepts, and the
  intercepts profile out to the period means. `LinearPanel.glsObjective_eq`,
  `LinearPanel.gls_isLeastSquares_reTheta`: under compound symmetry the generalized least
  squares objective is `σε⁻²` times the quasi-demeaned objective at `θ = reTheta`, so its
  unique minimizing slope is `quasiSlope reTheta`.
* `LinearPanel.ordinarySlope_eq`: under contemporaneous exogeneity the ordinary pooled slope is
  `β` plus `∑ₜ Cov(D t, α)` plus the covariation over periods of the mean treatment with the
  period effects and the mean errors, over the stacked treatment variance.
* `LinearPanel.pooledSlope_eq`, `LinearPanel.pooledSlope_ne_beta`: the pooled slope is
  `β + ∑ₜ Cov(D t, α) / ∑ₜ Var(D t)` under contemporaneous exogeneity alone.
* `LinearPanel.withinSlope_eq_fdSlope`: with two periods the within and first-difference slopes
  coincide.
* `LinearPanel.Counterexample.correlated_slopes`: strict exogeneity holds and the heterogeneity
  is correlated with the treatment; first differences and within recover `β = 0`, the pooled
  slope is `1`, and every quasi-demeaned slope with `θ ≠ 1` differs from `β`.
* `LinearPanel.Counterexample.feedback_slopes`: no unit effect and contemporaneous exogeneity,
  but the treatment responds to a past shock; the first-difference slope is `-1 ≠ β = 0`.
* `LinearPanel.Counterexample.timeVarying_slopes`: strict exogeneity holds but the unit effect
  enters the outcome with a loading that changes over time; the first-difference slope is
  `1 ≠ β = 0`, while with a constant loading it is `β`.
* `LinearPanel.Counterexample.timing_slopes`: treatment switched on for everybody in the second
  period; the period-dummy denominator `∑ₜ Var(D t)` is zero, while the ordinary pooled slope is
  `β + c` for a period effect `c`.

The random effects estimator is generalized least squares. Its link to quasi-demeaning holds
under compound symmetry of the composite error only: then the weight matrix is proportional to
the square of `I - θ 1 1ᵀ / T` with `θ = reTheta`. With a general error covariance (for example
independent period errors of unequal variances) no scalar `θ` reproduces the generalized least
squares weights, since every such square has equal diagonal entries. The bias formula of
`quasiSlope_eq` holds for every fixed `θ`. The covariance ratio `quasiSlope θ` is the unique
minimizer of the quasi-demeaned least squares objective with period dummies
(`LinearPanel.quasiSlope_isLeastSquares`), and under compound symmetry the generalized least
squares objective is `σε⁻²` times that objective at `θ = reTheta`
(`LinearPanel.glsObjective_eq`), so the random effects slope minimizes it
(`LinearPanel.gls_isLeastSquares_reTheta`). No optimality property of any `θ` in the sampling
sense is claimed.

Source: NICE Decision Support Unit, Technical Support Document 17 (Faria, Hernandez Alava,
Manca and Wailoo, 2015), Section 2.4.2 (panel data models) and Section 2.5.1 (difference in
differences as first differences); the model and the estimators are those of Wooldridge,
*Econometric Analysis of Cross Section and Panel Data*, cited there. TSD 17 prints no formula
for these models; the statements are formalizations of its verbal claims.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace CausalInference

/-- A linear panel model with a time-invariant unit effect. Units are the points `ω` of a
probability space `(Ω, μ)` (a unit drawn at random from the population) and periods are the
elements of `τ`. The outcome of unit `ω` in period `t` is
`Y t ω = δ t + α ω + β D t ω + ε t ω`: a deterministic period effect `δ t`, a unit effect `α ω`
that does not depend on the period, a common causal slope `β` of the treatment `D t ω`, and an
idiosyncratic error `ε t ω`. No assumption links `α` to `D`. -/
structure LinearPanel (Ω τ : Type*) where
  /-- The common causal slope of the treatment. -/
  β : ℝ
  /-- The deterministic period effects. -/
  δ : τ → ℝ
  /-- The time-invariant unit effect (unobserved heterogeneity). -/
  α : Ω → ℝ
  /-- The treatment of each unit in each period. -/
  D : τ → Ω → ℝ
  /-- The idiosyncratic error of each unit in each period. -/
  ε : τ → Ω → ℝ

namespace LinearPanel

variable {Ω τ : Type*} {mΩ : MeasurableSpace Ω} (P : LinearPanel Ω τ) (μ : Measure Ω)

/-- The outcome, given by the structural equation `Y t = δ t + α + β D t + ε t`. -/
def Y (t : τ) (ω : Ω) : ℝ := P.δ t + P.α ω + P.β * P.D t ω + P.ε t ω

/-- Finite second moments of the unit effect, the treatment and the error in every period. -/
structure SecondMoments : Prop where
  memLp_α : MemLp P.α 2 μ
  memLp_D : ∀ t, MemLp (P.D t) 2 μ
  memLp_ε : ∀ t, MemLp (P.ε t) 2 μ

/-- **Strict exogeneity, moment form:** the treatment in every period is uncorrelated with the
error in every period, `Cov(D s, ε t) = 0` for all `s, t`. Nothing is assumed about the unit
effect `α`. The textbook conditional mean form `E[ε t | D, α] = 0` implies it
(`strictExogeneity_of_condExp`). -/
def StrictExogeneity : Prop := ∀ s t, cov[P.D s, P.ε t; μ] = 0

/-- **Contemporaneous exogeneity:** `Cov(D t, ε t) = 0` for every period `t`. It is implied by
strict exogeneity and is strictly weaker (`Counterexample.feedback`). -/
def ContemporaneousExogeneity : Prop := ∀ t, cov[P.D t, P.ε t; μ] = 0

variable {P μ}

theorem StrictExogeneity.contemporaneous (h : P.StrictExogeneity μ) :
    P.ContemporaneousExogeneity μ := fun t ↦ h t t

/-- With finite second moments the outcome has finite second moments in every period. -/
theorem SecondMoments.memLp_Y [IsFiniteMeasure μ] (h : P.SecondMoments μ) (t : τ) :
    MemLp (P.Y t) 2 μ :=
  (((memLp_const (P.δ t)).add h.memLp_α).add ((h.memLp_D t).const_mul P.β)).add (h.memLp_ε t)

/-- **The first difference removes the unit effect.** For any two periods `s, t` and every
unit, `Y t - Y s = (δ t - δ s) + β (D t - D s) + (ε t - ε s)`. -/
theorem Y_sub_Y (s t : τ) (ω : Ω) :
    P.Y t ω - P.Y s ω = (P.δ t - P.δ s) + (P.β * (P.D t ω - P.D s ω) + (P.ε t ω - P.ε s ω)) := by
  simp only [Y]; ring

/-- Covariance of a first-differenced treatment with the first-differenced outcome:
`Cov(ΔD, ΔY) = β Var(ΔD) + Cov(ΔD, Δε)`. -/
theorem cov_sub_Y_sub [IsProbabilityMeasure μ] (h : P.SecondMoments μ) (s t : τ) :
    cov[fun ω ↦ P.D t ω - P.D s ω, fun ω ↦ P.Y t ω - P.Y s ω; μ] =
      P.β * Var[fun ω ↦ P.D t ω - P.D s ω; μ] +
        cov[fun ω ↦ P.D t ω - P.D s ω, fun ω ↦ P.ε t ω - P.ε s ω; μ] := by
  have hΔD : MemLp (fun ω ↦ P.D t ω - P.D s ω) 2 μ := (h.memLp_D t).sub (h.memLp_D s)
  have hΔε : MemLp (fun ω ↦ P.ε t ω - P.ε s ω) 2 μ := (h.memLp_ε t).sub (h.memLp_ε s)
  have e : (fun ω ↦ P.Y t ω - P.Y s ω) = fun ω ↦ (P.δ t - P.δ s) +
      ((fun ω ↦ P.β * (P.D t ω - P.D s ω)) + fun ω ↦ P.ε t ω - P.ε s ω) ω := by
    funext ω; rw [Y_sub_Y]; rfl
  rw [e, covariance_const_add_right (((hΔD.const_mul P.β).add hΔε).integrable one_le_two),
    covariance_add_right hΔD (hΔD.const_mul P.β) hΔε, covariance_const_mul_right,
    covariance_self hΔD.aemeasurable]

/-- Under strict exogeneity the first-differenced treatment is uncorrelated with the
first-differenced error: `Cov(D t - D s, ε t - ε s) = 0`. -/
theorem cov_sub_ε_sub_eq_zero [IsProbabilityMeasure μ] (h : P.SecondMoments μ)
    (hE : P.StrictExogeneity μ) (s t : τ) :
    cov[fun ω ↦ P.D t ω - P.D s ω, fun ω ↦ P.ε t ω - P.ε s ω; μ] = 0 := by
  rw [covariance_fun_sub_fun_sub (h.memLp_D t) (h.memLp_D s) (h.memLp_ε t) (h.memLp_ε s),
    hE, hE, hE, hE]
  ring

variable (P μ) in
/-- The **population first-difference slope** over a finite set `K` of period pairs `(s, t)`:
the least squares slope of `Y t - Y s` on `D t - D s` pooled over the pairs in `K`, with a
separate intercept for each pair, `∑ Cov(ΔD, ΔY) / ∑ Var(ΔD)`. With two periods `K` is the
single pair (before, after); with `T` periods the usual first-difference estimand takes the
consecutive pairs. -/
noncomputable def fdSlope (K : Finset (τ × τ)) : ℝ :=
  (∑ p ∈ K, cov[fun ω ↦ P.D p.2 ω - P.D p.1 ω, fun ω ↦ P.Y p.2 ω - P.Y p.1 ω; μ]) /
    ∑ p ∈ K, Var[fun ω ↦ P.D p.2 ω - P.D p.1 ω; μ]

/-- **The first-difference slope with its bias.** With finite second moments and a nonzero
pooled variance of the differenced treatment, the first-difference slope is
`β + ∑ Cov(ΔD, Δε) / ∑ Var(ΔD)`, whatever the joint law of the unit effect `α` and the
treatment. -/
theorem fdSlope_eq [IsProbabilityMeasure μ] (h : P.SecondMoments μ) (K : Finset (τ × τ))
    (hV : ∑ p ∈ K, Var[fun ω ↦ P.D p.2 ω - P.D p.1 ω; μ] ≠ 0) :
    P.fdSlope μ K = P.β + (∑ p ∈ K,
      cov[fun ω ↦ P.D p.2 ω - P.D p.1 ω, fun ω ↦ P.ε p.2 ω - P.ε p.1 ω; μ]) /
        ∑ p ∈ K, Var[fun ω ↦ P.D p.2 ω - P.D p.1 ω; μ] := by
  simp_rw [fdSlope, cov_sub_Y_sub h]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, add_div, mul_div_assoc, div_self hV, mul_one]

/-- **Identification by first differences** (TSD 17, Sections 2.4.2 and 2.5.1). Under finite
second moments and strict exogeneity, and with a nonzero pooled variance of the differenced
treatment, the first-difference slope equals the causal slope `β`. No assumption restricts the
correlation between the unit effect `α` and the treatment. -/
theorem fdSlope_eq_beta [IsProbabilityMeasure μ] (h : P.SecondMoments μ)
    (hE : P.StrictExogeneity μ) (K : Finset (τ × τ))
    (hV : ∑ p ∈ K, Var[fun ω ↦ P.D p.2 ω - P.D p.1 ω; μ] ≠ 0) :
    P.fdSlope μ K = P.β := by
  rw [fdSlope_eq h K hV]
  simp [cov_sub_ε_sub_eq_zero h hE]

/-- **First differences with two periods.** For two periods `s, t` with
`Var(D t - D s) ≠ 0`, under finite second moments and strict exogeneity,
`Cov(D t - D s, Y t - Y s) / Var(D t - D s) = β`. -/
theorem fdSlope_pair_eq_beta [IsProbabilityMeasure μ] (h : P.SecondMoments μ)
    (hE : P.StrictExogeneity μ) (s t : τ) (hV : Var[fun ω ↦ P.D t ω - P.D s ω; μ] ≠ 0) :
    cov[fun ω ↦ P.D t ω - P.D s ω, fun ω ↦ P.Y t ω - P.Y s ω; μ] /
      Var[fun ω ↦ P.D t ω - P.D s ω; μ] = P.β := by
  rw [cov_sub_Y_sub h, cov_sub_ε_sub_eq_zero h hE, add_zero, mul_div_assoc, div_self hV,
    mul_one]

/-- **Strict exogeneity in conditional mean form implies the moment form.** Let `m` be a
sub-σ-algebra for which every treatment `D s` is measurable (for example the σ-algebra generated
by the whole treatment path and the unit effect). If `E[ε t | m] = 0` almost surely for every
period `t`, then `Cov(D s, ε t) = 0` for all `s, t`. -/
theorem strictExogeneity_of_condExp [IsProbabilityMeasure μ] {m : MeasurableSpace Ω}
    (hm : m ≤ mΩ) (h : P.SecondMoments μ)
    (hD : ∀ s, StronglyMeasurable[m] (P.D s)) (hε : ∀ t, μ[P.ε t | m] =ᵐ[μ] 0) :
    P.StrictExogeneity μ := by
  intro s t
  have hint : ∫ ω, P.ε t ω ∂μ = 0 := by
    rw [← integral_condExp hm, integral_congr_ae (hε t)]
    simp
  have hprod : ∫ ω, (P.D s * P.ε t) ω ∂μ = 0 := by
    rw [← integral_condExp hm, integral_congr_ae (condExp_mul_of_stronglyMeasurable_left (hD s)
      ((h.memLp_D s).integrable_mul (h.memLp_ε t)) ((h.memLp_ε t).integrable one_le_two))]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hε t] with ω hω
    simp [hω]
  rw [covariance_eq_sub (h.memLp_D s) (h.memLp_ε t), hprod, hint, mul_zero, sub_zero]

/-! ### Within, pooled and random effects slopes -/

section Quasi

variable [Fintype τ]

/-- The mean over periods of a unit's trajectory, `X̄ ω = (1 / T) ∑ₛ X s ω` with `T` the number of
periods. -/
noncomputable def unitMean (X : τ → Ω → ℝ) (ω : Ω) : ℝ :=
  (Fintype.card τ : ℝ)⁻¹ * ∑ s, X s ω

/-- Quasi-demeaning with parameter `θ`: `X t ω - θ X̄ ω`. The value `θ = 1` is the within
(fixed effects) transformation and `θ = 0` leaves the data unchanged (pooled least squares).
Under compound symmetry of the composite error the random effects (generalized least squares)
transformation is the value `θ = reTheta T σε² σα² ∈ [0, 1)` (`gls_quadForm_eq`); without
compound symmetry no single `θ` gives generalized least squares. -/
noncomputable def quasiDemean (θ : ℝ) (X : τ → Ω → ℝ) (t : τ) (ω : Ω) : ℝ :=
  X t ω - θ * unitMean X ω

variable (P μ) in
/-- The population slope after quasi-demeaning with parameter `θ`, pooled over periods with a
separate intercept for each period (period dummies), written as the covariance ratio
`∑ₜ Cov(D t - θ D̄, Y t - θ Ȳ) / ∑ₜ Var(D t - θ D̄)`. It is defined for every fixed `θ`; its
reading as the random effects estimand needs compound symmetry and `θ = reTheta`
(`gls_quadForm_eq`). -/
noncomputable def quasiSlope (θ : ℝ) : ℝ :=
  (∑ t, cov[quasiDemean θ P.D t, quasiDemean θ P.Y t; μ]) /
    ∑ t, Var[quasiDemean θ P.D t; μ]

variable (P μ) in
/-- The population **within (fixed effects) slope** with period effects: the slope after
subtracting each unit's mean over periods, `∑ₜ Cov(D t - D̄, Y t - Ȳ) / ∑ₜ Var(D t - D̄)`. It is
the two-way fixed effects estimand of the regression of `Y` on `D` with unit and period
dummies. -/
noncomputable def withinSlope : ℝ := P.quasiSlope μ 1

variable (P μ) in
/-- The population **pooled least squares slope** with period dummies:
`∑ₜ Cov(D t, Y t) / ∑ₜ Var(D t)`. -/
noncomputable def pooledSlope : ℝ :=
  (∑ t, cov[P.D t, P.Y t; μ]) / ∑ t, Var[P.D t; μ]

theorem quasiDemean_zero (X : τ → Ω → ℝ) (t : τ) : quasiDemean 0 X t = X t := by
  funext ω; simp [quasiDemean]

theorem pooledSlope_eq_quasiSlope_zero : P.pooledSlope μ = P.quasiSlope μ 0 := by
  simp [pooledSlope, quasiSlope, quasiDemean_zero]

theorem quasiDemean_eq_sum [DecidableEq τ] (θ : ℝ) (X : τ → Ω → ℝ) (t : τ) (ω : Ω) :
    quasiDemean θ X t ω =
      ∑ s, ((if s = t then 1 else 0) - θ * (Fintype.card τ : ℝ)⁻¹) * X s ω := by
  simp [quasiDemean, unitMean, sub_mul, Finset.sum_sub_distrib, ite_mul, Finset.mul_sum,
    mul_assoc]

theorem memLp_unitMean {X : τ → Ω → ℝ} (hX : ∀ t, MemLp (X t) 2 μ) :
    MemLp (unitMean X) 2 μ :=
  (memLp_finsetSum Finset.univ fun s _ ↦ hX s).const_mul _

theorem memLp_quasiDemean (θ : ℝ) {X : τ → Ω → ℝ} (hX : ∀ t, MemLp (X t) 2 μ) (t : τ) :
    MemLp (quasiDemean θ X t) 2 μ :=
  (hX t).sub ((memLp_unitMean hX).const_mul θ)

/-- The quasi-demeaned outcome: `Y t - θ Ȳ = (δ t - θ δ̄) + (1 - θ) α + β (D t - θ D̄) +
(ε t - θ ε̄)`. The unit effect survives with weight `1 - θ`, and disappears exactly for the
within transformation `θ = 1`. -/
theorem quasiDemean_Y [Nonempty τ] (θ : ℝ) (t : τ) (ω : Ω) :
    quasiDemean θ P.Y t ω = (P.δ t - θ * ((Fintype.card τ : ℝ)⁻¹ * ∑ s, P.δ s)) +
      ((1 - θ) * P.α ω + P.β * quasiDemean θ P.D t ω + quasiDemean θ P.ε t ω) := by
  have hT : (Fintype.card τ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [quasiDemean, unitMean, Y, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
  field_simp
  ring

/-- Covariance of the quasi-demeaned treatment with the quasi-demeaned outcome:
`Cov(D̃ t, Ỹ t) = (1 - θ) Cov(D̃ t, α) + β Var(D̃ t) + Cov(D̃ t, ε̃ t)`. -/
theorem cov_quasiDemean_Y [Nonempty τ] [IsProbabilityMeasure μ] (h : P.SecondMoments μ)
    (θ : ℝ) (t : τ) :
    cov[quasiDemean θ P.D t, quasiDemean θ P.Y t; μ] =
      (1 - θ) * cov[quasiDemean θ P.D t, P.α; μ] + P.β * Var[quasiDemean θ P.D t; μ] +
        cov[quasiDemean θ P.D t, quasiDemean θ P.ε t; μ] := by
  have hD := memLp_quasiDemean θ h.memLp_D t
  have hε := memLp_quasiDemean θ h.memLp_ε t
  have hα : MemLp (fun ω ↦ (1 - θ) * P.α ω) 2 μ := h.memLp_α.const_mul _
  have hβ : MemLp (fun ω ↦ P.β * quasiDemean θ P.D t ω) 2 μ := hD.const_mul _
  have e : quasiDemean θ P.Y t = fun ω ↦ (P.δ t - θ * ((Fintype.card τ : ℝ)⁻¹ * ∑ s, P.δ s)) +
      ((fun ω ↦ (1 - θ) * P.α ω) + (fun ω ↦ P.β * quasiDemean θ P.D t ω) +
        quasiDemean θ P.ε t) ω := by
    funext ω; rw [quasiDemean_Y]; rfl
  rw [e, covariance_const_add_right (((hα.add hβ).add hε).integrable one_le_two),
    covariance_add_right hD (hα.add hβ) hε, covariance_add_right hD hα hβ,
    covariance_const_mul_right, covariance_const_mul_right, covariance_self hD.aemeasurable]

/-- Under strict exogeneity the quasi-demeaned treatment and error are uncorrelated. -/
theorem cov_quasiDemean_ε_eq_zero [IsProbabilityMeasure μ] (h : P.SecondMoments μ)
    (hE : P.StrictExogeneity μ) (θ θ' : ℝ) (t t' : τ) :
    cov[quasiDemean θ P.D t, quasiDemean θ' P.ε t'; μ] = 0 := by
  classical
  have e1 : quasiDemean θ P.D t = fun ω ↦ ∑ s,
      ((if s = t then 1 else 0) - θ * (Fintype.card τ : ℝ)⁻¹) * P.D s ω :=
    funext (quasiDemean_eq_sum θ P.D t)
  have e2 : quasiDemean θ' P.ε t' = fun ω ↦ ∑ s,
      ((if s = t' then 1 else 0) - θ' * (Fintype.card τ : ℝ)⁻¹) * P.ε s ω :=
    funext (quasiDemean_eq_sum θ' P.ε t')
  rw [e1, e2, covariance_fun_sum_fun_sum (fun s ↦ (h.memLp_D s).const_mul _)
    (fun s ↦ (h.memLp_ε s).const_mul _)]
  have hE' : ∀ s t, cov[P.D s, P.ε t; μ] = 0 := hE
  simp [covariance_const_mul_left, covariance_const_mul_right, hE']

/-- The covariances of the quasi-demeaned treatment with the unit effect, summed over periods:
`∑ₜ Cov(D t - θ D̄, α) = (1 - θ) ∑ₜ Cov(D t, α)`. -/
theorem sum_cov_quasiDemean_α [Nonempty τ] [IsProbabilityMeasure μ] (h : P.SecondMoments μ)
    (θ : ℝ) :
    ∑ t, cov[quasiDemean θ P.D t, P.α; μ] = (1 - θ) * ∑ t, cov[P.D t, P.α; μ] := by
  have hT : (Fintype.card τ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have e : ∀ t, cov[quasiDemean θ P.D t, P.α; μ] =
      cov[P.D t, P.α; μ] - θ * ((Fintype.card τ : ℝ)⁻¹ * ∑ s, cov[P.D s, P.α; μ]) := by
    intro t
    have hm := memLp_unitMean (μ := μ) h.memLp_D
    change cov[fun ω ↦ P.D t ω - θ * unitMean P.D ω, P.α; μ] = _
    rw [covariance_fun_sub_left (h.memLp_D t) (hm.const_mul θ) h.memLp_α,
      covariance_const_mul_left]
    rw [show unitMean P.D = fun ω ↦ (Fintype.card τ : ℝ)⁻¹ * ∑ s, P.D s ω from rfl,
      covariance_const_mul_left, covariance_fun_sum_left h.memLp_D h.memLp_α]
  simp only [e, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- **The quasi-demeaned slope with its bias.** With finite second moments, strict exogeneity
and a nonzero denominator, the slope after quasi-demeaning with parameter `θ` is
`β + (1 - θ)² ∑ₜ Cov(D t, α) / ∑ₜ Var(D t - θ D̄)`. -/
theorem quasiSlope_eq [Nonempty τ] [IsProbabilityMeasure μ] (h : P.SecondMoments μ)
    (hE : P.StrictExogeneity μ) (θ : ℝ) (hV : ∑ t, Var[quasiDemean θ P.D t; μ] ≠ 0) :
    P.quasiSlope μ θ = P.β + (1 - θ) ^ 2 * (∑ t, cov[P.D t, P.α; μ]) /
      ∑ t, Var[quasiDemean θ P.D t; μ] := by
  simp only [quasiSlope, cov_quasiDemean_Y h, cov_quasiDemean_ε_eq_zero h hE, add_zero,
    Finset.sum_add_distrib, ← Finset.mul_sum, sum_cov_quasiDemean_α h]
  field_simp
  ring

/-- **Identification by the within (fixed effects) transformation** (TSD 17, Section 2.4.2).
Under finite second moments and strict exogeneity, and with `∑ₜ Var(D t - D̄) ≠ 0`, the within
slope equals `β`, whatever the correlation between the unit effect and the treatment. -/
theorem withinSlope_eq_beta [Nonempty τ] [IsProbabilityMeasure μ] (h : P.SecondMoments μ)
    (hE : P.StrictExogeneity μ) (hV : ∑ t, Var[quasiDemean 1 P.D t; μ] ≠ 0) :
    P.withinSlope μ = P.β := by
  rw [withinSlope, quasiSlope_eq h hE 1 hV]
  simp

/-- **Random effects and pooled slopes equal `β` when heterogeneity is uncorrelated.** If
`∑ₜ Cov(D t, α) = 0` then, under finite second moments and strict exogeneity, the
quasi-demeaned slope equals `β` for every `θ`. -/
theorem quasiSlope_eq_beta_of_uncorrelated [Nonempty τ] [IsProbabilityMeasure μ]
    (h : P.SecondMoments μ) (hE : P.StrictExogeneity μ) (θ : ℝ)
    (hV : ∑ t, Var[quasiDemean θ P.D t; μ] ≠ 0) (hα : ∑ t, cov[P.D t, P.α; μ] = 0) :
    P.quasiSlope μ θ = P.β := by
  rw [quasiSlope_eq h hE θ hV, hα]
  simp

/-- **Random effects slopes differ from `β` under correlated heterogeneity** (TSD 17,
Section 2.4.2: the random effects estimator "assumes that the unobserved determinants of
heterogeneity in the outcomes do not have an effect on selection"). If `θ ≠ 1` and
`∑ₜ Cov(D t, α) ≠ 0`, then under finite second moments and strict exogeneity the quasi-demeaned
slope differs from `β`. -/
theorem quasiSlope_ne_beta [Nonempty τ] [IsProbabilityMeasure μ] (h : P.SecondMoments μ)
    (hE : P.StrictExogeneity μ) {θ : ℝ} (hθ : θ ≠ 1)
    (hV : ∑ t, Var[quasiDemean θ P.D t; μ] ≠ 0) (hα : ∑ t, cov[P.D t, P.α; μ] ≠ 0) :
    P.quasiSlope μ θ ≠ P.β := by
  rw [quasiSlope_eq h hE θ hV]
  intro h'
  have : (1 - θ) ^ 2 * (∑ t, cov[P.D t, P.α; μ]) / ∑ t, Var[quasiDemean θ P.D t; μ] = 0 := by
    linarith
  exact div_ne_zero (mul_ne_zero (pow_ne_zero 2 (sub_ne_zero.mpr hθ.symm)) hα) hV this

omit [Fintype τ] in
/-- Covariance of the treatment with the outcome in the same period:
`Cov(D t, Y t) = Cov(D t, α) + β Var(D t) + Cov(D t, ε t)`. -/
theorem cov_D_Y [IsProbabilityMeasure μ] (h : P.SecondMoments μ) (t : τ) :
    cov[P.D t, P.Y t; μ] =
      cov[P.D t, P.α; μ] + P.β * Var[P.D t; μ] + cov[P.D t, P.ε t; μ] := by
  have hβ : MemLp (fun ω ↦ P.β * P.D t ω) 2 μ := (h.memLp_D t).const_mul _
  have e : P.Y t = fun ω ↦ P.δ t + (P.α + (fun ω ↦ P.β * P.D t ω) + P.ε t) ω := by
    funext ω; simp only [Y, Pi.add_apply]; ring
  rw [e, covariance_const_add_right (((h.memLp_α.add hβ).add (h.memLp_ε t)).integrable
      one_le_two), covariance_add_right (h.memLp_D t) (h.memLp_α.add hβ) (h.memLp_ε t),
    covariance_add_right (h.memLp_D t) h.memLp_α hβ, covariance_const_mul_right,
    covariance_self (h.memLp_D t).aemeasurable]

/-- **The pooled slope with its bias** (TSD 17, Section 2.4.2). Under finite second moments and
contemporaneous exogeneity only, with `∑ₜ Var(D t) ≠ 0`, the pooled slope with period dummies
is `β + ∑ₜ Cov(D t, α) / ∑ₜ Var(D t)`: it is biased by the correlation between the unit effect
and the treatment. -/
theorem pooledSlope_eq [IsProbabilityMeasure μ] (h : P.SecondMoments μ)
    (hE : P.ContemporaneousExogeneity μ) (hV : ∑ t, Var[P.D t; μ] ≠ 0) :
    P.pooledSlope μ = P.β + (∑ t, cov[P.D t, P.α; μ]) / ∑ t, Var[P.D t; μ] := by
  simp only [pooledSlope, cov_D_Y h, hE _, add_zero, Finset.sum_add_distrib, ← Finset.mul_sum]
  field_simp
  ring

/-- **The pooled slope differs from `β` under correlated heterogeneity.** If
`∑ₜ Cov(D t, α) ≠ 0`, under finite second moments, contemporaneous exogeneity and
`∑ₜ Var(D t) ≠ 0`, the pooled slope differs from `β`. -/
theorem pooledSlope_ne_beta [IsProbabilityMeasure μ] (h : P.SecondMoments μ)
    (hE : P.ContemporaneousExogeneity μ) (hV : ∑ t, Var[P.D t; μ] ≠ 0)
    (hα : ∑ t, cov[P.D t, P.α; μ] ≠ 0) : P.pooledSlope μ ≠ P.β := by
  rw [pooledSlope_eq h hE hV]
  intro h'
  exact div_ne_zero hα hV (by linarith)

/-- With exactly two periods `s ≠ t`, the within transformation is half the first difference:
`X t - X̄ = (X t - X s) / 2`. -/
theorem quasiDemean_one_of_two [DecidableEq τ] {s t : τ} (hst : s ≠ t)
    (huniv : (Finset.univ : Finset τ) = {s, t})
    (X : τ → Ω → ℝ) :
    quasiDemean 1 X t = (fun ω ↦ (1 / 2 : ℝ) * (X t ω - X s ω)) ∧
      quasiDemean 1 X s = (fun ω ↦ (-1 / 2 : ℝ) * (X t ω - X s ω)) := by
  have hT : (Fintype.card τ : ℝ) = 2 := by
    rw [← Finset.card_univ, huniv, Finset.card_pair hst]; norm_num
  constructor <;> funext ω <;>
    simp only [quasiDemean, unitMean, hT, huniv, Finset.sum_pair hst] <;> ring

/-- **Within equals first differences with two periods** (TSD 17, Section 2.5.1: with
longitudinal data the two-period estimand is the first-difference estimand, equivalently the
two-way fixed effects coefficient). If the periods are exactly `s ≠ t`, then under finite second
moments and `Var(D t - D s) ≠ 0` the within slope equals the first-difference slope of the pair
`(s, t)`. -/
theorem withinSlope_eq_fdSlope [DecidableEq τ] [IsProbabilityMeasure μ]
    (h : P.SecondMoments μ) {s t : τ} (hst : s ≠ t)
    (huniv : (Finset.univ : Finset τ) = {s, t})
    (hV : Var[fun ω ↦ P.D t ω - P.D s ω; μ] ≠ 0) :
    P.withinSlope μ = P.fdSlope μ {(s, t)} := by
  obtain ⟨hDt, hDs⟩ := quasiDemean_one_of_two hst huniv P.D
  obtain ⟨hYt, hYs⟩ := quasiDemean_one_of_two hst huniv P.Y
  have hΔD : MemLp (fun ω ↦ P.D t ω - P.D s ω) 2 μ := (h.memLp_D t).sub (h.memLp_D s)
  have hv : ∀ c : ℝ, Var[fun ω ↦ c * (P.D t ω - P.D s ω); μ] =
      c * (c * Var[fun ω ↦ P.D t ω - P.D s ω; μ]) := by
    intro c
    rw [← covariance_self (hΔD.const_mul c).aemeasurable, ← covariance_self hΔD.aemeasurable,
      covariance_const_mul_left, covariance_const_mul_right]
  simp only [withinSlope, quasiSlope, fdSlope, huniv, Finset.sum_pair hst, Finset.sum_singleton,
    hDt, hDs, hYt, hYs, covariance_const_mul_left, covariance_const_mul_right, hv]
  field_simp

end Quasi

/-! ### Random effects as generalized least squares under compound symmetry -/

section GLS

open Matrix

variable [Fintype τ] [DecidableEq τ]

/-- The period-averaging matrix `1 1ᵀ / T` on the periods, `T` the number of periods. -/
noncomputable def periodAverage : Matrix τ τ ℝ := (Fintype.card τ : ℝ)⁻¹ • Matrix.of fun _ _ => 1

omit [DecidableEq τ] in
/-- The period-averaging matrix is idempotent. -/
theorem periodAverage_mul_self [Nonempty τ] :
    (periodAverage : Matrix τ τ ℝ) * periodAverage = periodAverage := by
  ext i j
  simp [periodAverage, Matrix.mul_apply, Finset.sum_const, Finset.card_univ]

/-- The **compound symmetric** covariance `s I + a 1 1ᵀ` of the composite errors
`α + ε t` of one unit over the periods, with `s = σε²` (variance of the idiosyncratic errors,
assumed uncorrelated over periods with a common variance) and `a = σα²` (variance of the unit
effect, uncorrelated with the idiosyncratic errors). -/
noncomputable def compoundSymmetric (s a : ℝ) : Matrix τ τ ℝ :=
  s • (1 : Matrix τ τ ℝ) + a • Matrix.of fun _ _ => 1

/-- The **random effects parameter** `θ = 1 - √(s / (s + T a))` for `T` periods,
idiosyncratic variance `s` and unit effect variance `a`. -/
noncomputable def reTheta (T s a : ℝ) : ℝ := 1 - Real.sqrt (s / (s + T * a))

omit [Fintype τ] [DecidableEq τ] in
/-- The random effects parameter solves `(1 - θ)² (s + T a) = s` when `s > 0`, `T ≥ 0` and
`a ≥ 0`. -/
theorem one_sub_reTheta_sq {T s a : ℝ} (hs : 0 < s) (hT : 0 ≤ T) (ha : 0 ≤ a) :
    (1 - reTheta T s a) ^ 2 * (s + T * a) = s := by
  have h : 0 < s + T * a := by positivity
  rw [reTheta, sub_sub_cancel, Real.sq_sqrt (by positivity)]
  field_simp

omit [Fintype τ] [DecidableEq τ] in
/-- The random effects parameter lies in `[0, 1)` when `s > 0`, `T ≥ 0` and `a ≥ 0`; it is
`0` (pooled least squares) when `a = 0`. -/
theorem reTheta_mem {T s a : ℝ} (hs : 0 < s) (hT : 0 ≤ T) (ha : 0 ≤ a) :
    0 ≤ reTheta T s a ∧ reTheta T s a < 1 := by
  have h : 0 < s + T * a := by positivity
  refine ⟨?_, ?_⟩
  · rw [reTheta, sub_nonneg, Real.sqrt_le_one]
    rw [div_le_one h]; nlinarith [mul_nonneg hT ha]
  · rw [reTheta, sub_lt_self_iff]; positivity

/-- **Quasi-demeaning whitens a compound symmetric covariance.** If
`(1 - θ)² (s + T a) = s`, then `(I - θ 1 1ᵀ / T)² (s I + a 1 1ᵀ) = s I`. -/
theorem quasi_mul_quasi_mul_compoundSymmetric [Nonempty τ] {s a θ : ℝ}
    (hθ : (1 - θ) ^ 2 * (s + Fintype.card τ * a) = s) :
    (1 - θ • periodAverage) * (1 - θ • periodAverage) * compoundSymmetric s a =
      s • (1 : Matrix τ τ ℝ) := by
  have hT : (Fintype.card τ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hJ : (Matrix.of fun _ _ => (1 : ℝ) : Matrix τ τ ℝ) =
      (Fintype.card τ : ℝ) • periodAverage := by
    rw [periodAverage, smul_smul, mul_inv_cancel₀ hT, one_smul]
  have hP := periodAverage_mul_self (τ := τ)
  rw [compoundSymmetric, hJ, smul_smul]
  simp only [sub_mul, mul_sub, mul_add, one_mul, mul_one, smul_mul_assoc,
    mul_smul_comm, hP, smul_sub]
  linear_combination (norm := module) hθ • (periodAverage : Matrix τ τ ℝ)

/-- Quasi-demeaning is multiplication of a unit's trajectory by `I - θ 1 1ᵀ / T`. -/
theorem quasiDemean_eq_mulVec (θ : ℝ) (X : τ → Ω → ℝ) (t : τ) (ω : Ω) :
    quasiDemean θ X t ω = ((1 - θ • periodAverage) *ᵥ fun s => X s ω) t := by
  rw [quasiDemean_eq_sum]
  simp [Matrix.mulVec, dotProduct, periodAverage, Matrix.one_apply, eq_comm]

/-- **The inverse of a compound symmetric covariance.** If `s ≠ 0` and
`(1 - θ)² (s + T a) = s`, then `(s I + a 1 1ᵀ)⁻¹ = s⁻¹ (I - θ 1 1ᵀ / T)²`. -/
theorem inv_compoundSymmetric [Nonempty τ] {s a θ : ℝ} (hs : s ≠ 0)
    (hθ : (1 - θ) ^ 2 * (s + Fintype.card τ * a) = s) :
    (compoundSymmetric s a : Matrix τ τ ℝ)⁻¹ =
      s⁻¹ • ((1 - θ • periodAverage) * (1 - θ • periodAverage)) := by
  refine Matrix.inv_eq_left_inv ?_
  rw [smul_mul_assoc, quasi_mul_quasi_mul_compoundSymmetric hθ, smul_smul, inv_mul_cancel₀ hs,
    one_smul]

/-- **Random effects is least squares on quasi-demeaned data, under compound symmetry**
(TSD 17, Section 2.4.2). If the composite errors of a unit have the compound symmetric
covariance `V = s I + a 1 1ᵀ` with `s ≠ 0` and `θ` solves `(1 - θ)² (s + T a) = s` (for
`s > 0`, `a ≥ 0` the solution `reTheta` lies in `[0, 1)`), then for every residual vector `r`
of a unit the generalized least squares quadratic form `rᵀ V⁻¹ r` equals `s⁻¹` times the squared
norm of the quasi-demeaned residual vector `(I - θ 1 1ᵀ / T) r`. So the generalized least
squares objective is a constant multiple of the least squares objective of the data
quasi-demeaned with this `θ`. -/
theorem gls_quadForm_eq [Nonempty τ] {s a θ : ℝ} (hs : s ≠ 0)
    (hθ : (1 - θ) ^ 2 * (s + Fintype.card τ * a) = s) (r : τ → ℝ) :
    r ⬝ᵥ ((compoundSymmetric s a : Matrix τ τ ℝ)⁻¹ *ᵥ r) =
      s⁻¹ * ((1 - θ • periodAverage) *ᵥ r) ⬝ᵥ ((1 - θ • periodAverage) *ᵥ r) := by
  have hQ : (1 - θ • (periodAverage : Matrix τ τ ℝ))ᵀ = 1 - θ • periodAverage := by
    ext i j; simp [periodAverage, Matrix.one_apply, eq_comm]
  rw [inv_compoundSymmetric hs hθ, Matrix.smul_mulVec, dotProduct_smul, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hQ, smul_eq_mul]
/-- `gls_quadForm_eq` at the random effects parameter: for `s > 0` and `a ≥ 0`, with
`θ = reTheta T s a ∈ [0, 1)`, the quadratic form of `(s I + a 1 1ᵀ)⁻¹` is `s⁻¹` times the
squared norm of the quasi-demeaned vector. -/
theorem gls_quadForm_reTheta [Nonempty τ] {s a : ℝ} (hs : 0 < s) (ha : 0 ≤ a) (r : τ → ℝ) :
    r ⬝ᵥ ((compoundSymmetric s a : Matrix τ τ ℝ)⁻¹ *ᵥ r) =
      s⁻¹ * ((1 - reTheta (Fintype.card τ) s a • periodAverage) *ᵥ r) ⬝ᵥ
        ((1 - reTheta (Fintype.card τ) s a • periodAverage) *ᵥ r) :=
  gls_quadForm_eq hs.ne' (one_sub_reTheta_sq hs (Nat.cast_nonneg _) ha) r

variable (P μ) in
/-- The covariance matrix over periods of a unit's composite errors `α + ε t`. -/
noncomputable def compositeCov : Matrix τ τ ℝ :=
  Matrix.of fun u v => cov[fun ω ↦ P.α ω + P.ε u ω, fun ω ↦ P.α ω + P.ε v ω; μ]

variable (P μ) in
/-- **Compound symmetry** of the composite errors, the random effects variance assumption:
the covariance matrix of `(α + ε t)ₜ` is `s I + a 1 1ᵀ`, that is every composite error has
variance `s + a` and any two periods have covariance `a`. -/
def CompoundSymmetry (s a : ℝ) : Prop := P.compositeCov μ = compoundSymmetric s a

/-- **Random effects is generalized least squares on quasi-demeaned data, model form.** If the
composite errors of the panel satisfy compound symmetry with `s > 0` and `a ≥ 0`, then for every
residual vector `r` the generalized least squares quadratic form with the composite error
covariance equals `s⁻¹` times the squared norm of `(I - θ 1 1ᵀ / T) r` with
`θ = reTheta T s a`. -/
theorem gls_quadForm_of_compoundSymmetry [Nonempty τ] {s a : ℝ}
    (hCS : P.CompoundSymmetry μ s a) (hs : 0 < s) (ha : 0 ≤ a) (r : τ → ℝ) :
    r ⬝ᵥ ((P.compositeCov μ)⁻¹ *ᵥ r) =
      s⁻¹ * ((1 - reTheta (Fintype.card τ) s a • periodAverage) *ᵥ r) ⬝ᵥ
        ((1 - reTheta (Fintype.card τ) s a • periodAverage) *ᵥ r) := by
  rw [show P.compositeCov μ = compoundSymmetric s a from hCS]
  exact gls_quadForm_reTheta hs ha r

end GLS

/-- A second moment about arbitrary centers:
`E[(X - a)(Z - b)] = Cov(X, Z) + (E X - a)(E Z - b)`. -/
theorem integral_sub_mul_sub [IsProbabilityMeasure μ] {X Z : Ω → ℝ} (hX : MemLp X 2 μ)
    (hZ : MemLp Z 2 μ) (a b : ℝ) :
    ∫ ω, (X ω - a) * (Z ω - b) ∂μ = cov[X, Z; μ] + (μ[X] - a) * (μ[Z] - b) := by
  have hXi := hX.integrable one_le_two
  have hZi := hZ.integrable one_le_two
  have hXZ : Integrable (fun ω => X ω * Z ω) μ := hX.integrable_mul hZ
  have e : (fun ω => (X ω - a) * (Z ω - b)) =
      fun ω => X ω * Z ω - b * X ω - a * Z ω + a * b := by funext ω; ring
  have h1 : Integrable (fun ω => X ω * Z ω - b * X ω) μ := hXZ.sub (hXi.const_mul b)
  have h2 : Integrable (fun ω => X ω * Z ω - b * X ω - a * Z ω) μ := h1.sub (hZi.const_mul a)
  rw [e, integral_add h2 (integrable_const _), integral_sub h1 (hZi.const_mul a),
    integral_sub hXZ (hXi.const_mul b), integral_const_mul, integral_const_mul, integral_const,
    covariance_eq_sub hX hZ]
  simp only [probReal_univ, smul_eq_mul, one_mul, Pi.mul_apply]
  ring

section Ordinary

variable [Fintype τ]

variable (μ) in
/-- The grand mean of a panel variable over the stacked data, each period with weight `1 / T`:
`(1 / T) ∑ₜ E[X t]`. -/
noncomputable def grandMean (X : τ → Ω → ℝ) : ℝ :=
  (Fintype.card τ : ℝ)⁻¹ * ∑ t, ∫ ω, X t ω ∂μ

variable (μ) in
/-- The covariation of two panel variables in the stacked data around their grand means,
`∑ₜ E[(X t - X̄̄)(Z t - Z̄̄)]`: `T` times the covariance of `X J` and `Z J` for a period `J`
drawn uniformly and independently of the unit. -/
noncomputable def stackedCov (X Z : τ → Ω → ℝ) : ℝ :=
  ∑ t, ∫ ω, (X t ω - grandMean μ X) * (Z t ω - grandMean μ Z) ∂μ

variable (P μ) in
/-- The population **ordinary pooled least squares slope** of the stacked data with a single
intercept and no period dummies: `stackedCov D Y / stackedCov D D`, the covariance ratio of
`Y J` on `D J` for a uniformly drawn period `J`. -/
noncomputable def ordinarySlope : ℝ := stackedCov μ P.D P.Y / stackedCov μ P.D P.D

/-- The stacked covariation splits into the within-period covariances and the covariation of
the period means: `stackedCov X Z = ∑ₜ Cov(X t, Z t) + ∑ₜ (E X t - X̄̄)(E Z t - Z̄̄)`. -/
theorem stackedCov_eq [IsProbabilityMeasure μ] {X Z : τ → Ω → ℝ} (hX : ∀ t, MemLp (X t) 2 μ)
    (hZ : ∀ t, MemLp (Z t) 2 μ) :
    stackedCov μ X Z = ∑ t, cov[X t, Z t; μ] +
      ∑ t, (μ[X t] - grandMean μ X) * (μ[Z t] - grandMean μ Z) := by
  simp only [stackedCov, integral_sub_mul_sub (hX _) (hZ _), Finset.sum_add_distrib]

omit [Fintype τ] in
/-- The mean outcome in a period: `E[Y t] = δ t + E[α] + β E[D t] + E[ε t]`. -/
theorem integral_Y [IsProbabilityMeasure μ] (h : P.SecondMoments μ) (t : τ) :
    μ[P.Y t] = P.δ t + μ[P.α] + P.β * μ[P.D t] + μ[P.ε t] := by
  have hα := h.memLp_α.integrable one_le_two
  have hD := (h.memLp_D t).integrable one_le_two
  have hε := (h.memLp_ε t).integrable one_le_two
  change ∫ ω, (P.δ t + P.α ω + P.β * P.D t ω + P.ε t ω) ∂μ = _
  have h1 : Integrable (fun ω => P.δ t + P.α ω) μ := (integrable_const _).add hα
  have h2 : Integrable (fun ω => P.δ t + P.α ω + P.β * P.D t ω) μ := h1.add (hD.const_mul _)
  rw [integral_add h2 hε, integral_add h1 (hD.const_mul _),
    integral_add (integrable_const _) hα, integral_const_mul, integral_const]
  simp

/-- The deviation of a period mean outcome from the grand mean: the unit effect cancels, and
`E[Y t] - Ȳ̄ = (δ t - δ̄) + β (E[D t] - D̄̄) + (E[ε t] - ε̄̄)`. -/
theorem integral_Y_sub_grandMean [Nonempty τ] [IsProbabilityMeasure μ] (h : P.SecondMoments μ)
    (t : τ) :
    μ[P.Y t] - grandMean μ P.Y = (P.δ t - (Fintype.card τ : ℝ)⁻¹ * ∑ s, P.δ s) +
      P.β * (μ[P.D t] - grandMean μ P.D) + (μ[P.ε t] - grandMean μ P.ε) := by
  have hT : (Fintype.card τ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have e : ∀ s, ∫ ω, P.Y s ω ∂μ = P.δ s + μ[P.α] + P.β * μ[P.D s] + μ[P.ε s] :=
    integral_Y h
  simp only [grandMean, e, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
  field_simp
  ring

/-- **The ordinary pooled slope with its bias.** Under finite second moments and
contemporaneous exogeneity, with a nonzero stacked treatment variation, the ordinary pooled
slope (no period dummies) is `β` plus
`[∑ₜ Cov(D t, α) + ∑ₜ (E[D t] - D̄̄)((δ t - δ̄) + (E[ε t] - ε̄̄))] / stackedCov D D`. Dividing
numerator and denominator by `T`, this is
`β + [Cov(D_J, α) + Cov(E[D_J | J], δ_J + E[ε_J | J])] / Var(D_J)` for a uniform period `J`.
Besides the correlation of the unit effect with the treatment, period effects (and mean errors)
that move with the mean treatment over periods bias it (`Counterexample.timing_slopes`). -/
theorem ordinarySlope_eq [Nonempty τ] [IsProbabilityMeasure μ] (h : P.SecondMoments μ)
    (hE : P.ContemporaneousExogeneity μ) (hV : stackedCov μ P.D P.D ≠ 0) :
    P.ordinarySlope μ = P.β + (∑ t, cov[P.D t, P.α; μ] + ∑ t, (μ[P.D t] - grandMean μ P.D) *
      ((P.δ t - (Fintype.card τ : ℝ)⁻¹ * ∑ s, P.δ s) + (μ[P.ε t] - grandMean μ P.ε))) /
        stackedCov μ P.D P.D := by
  have key : ∀ t, cov[P.D t, P.Y t; μ] + (μ[P.D t] - grandMean μ P.D) *
      (μ[P.Y t] - grandMean μ P.Y) = P.β * (cov[P.D t, P.D t; μ] +
        (μ[P.D t] - grandMean μ P.D) * (μ[P.D t] - grandMean μ P.D)) +
      (cov[P.D t, P.α; μ] + (μ[P.D t] - grandMean μ P.D) *
        ((P.δ t - (Fintype.card τ : ℝ)⁻¹ * ∑ s, P.δ s) + (μ[P.ε t] - grandMean μ P.ε))) := by
    intro t
    rw [cov_D_Y h, hE t, integral_Y_sub_grandMean h,
      covariance_self (h.memLp_D t).aemeasurable]
    ring
  have hnum : stackedCov μ P.D P.Y = P.β * stackedCov μ P.D P.D +
      (∑ t, cov[P.D t, P.α; μ] + ∑ t, (μ[P.D t] - grandMean μ P.D) *
        ((P.δ t - (Fintype.card τ : ℝ)⁻¹ * ∑ s, P.δ s) + (μ[P.ε t] - grandMean μ P.ε))) := by
    rw [stackedCov_eq h.memLp_D h.memLp_Y, stackedCov_eq h.memLp_D h.memLp_D,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun t _ => key t
  rw [ordinarySlope, hnum, add_div, mul_div_assoc, div_self hV, mul_one]
end Ordinary

/-! ### Least squares readings of the slopes -/

section LeastSquares

variable {ι : Type*} [Fintype ι]

variable (μ) in
/-- The population least squares objective of a pooled regression with group specific
intercepts: `∑ᵢ E[(Z i - a i - b X i)²]` for regressors `X i`, outcomes `Z i`, slope `b` and
intercepts `a i`, one for each index `i` of a finite type (periods, in the panel use). -/
noncomputable def lsObjective (X Z : ι → Ω → ℝ) (b : ℝ) (a : ι → ℝ) : ℝ :=
  ∑ i, ∫ ω, (Z i ω - a i - b * X i ω) ^ 2 ∂μ

variable (μ) in
/-- The intercepts profiled out for a given slope `b`: `E[Z i] - b E[X i]`. -/
noncomputable def lsIntercept (X Z : ι → Ω → ℝ) (b : ℝ) (i : ι) : ℝ :=
  μ[Z i] - b * μ[X i]

variable (μ) in
/-- The covariance ratio `∑ᵢ Cov(X i, Z i) / ∑ᵢ Var(X i)` of a pooled regression with group
specific intercepts. -/
noncomputable def lsSlope (X Z : ι → Ω → ℝ) : ℝ :=
  (∑ i, cov[X i, Z i; μ]) / ∑ i, Var[X i; μ]

omit [Fintype ι] in
/-- The mean squared error of one regression: for square integrable `X` and `Z`,
`E[(Z - a - b X)²] = Var Z - 2 b Cov(X, Z) + b² Var X + (E Z - b E X - a)²`. -/
theorem integral_sub_sub_mul_sq [IsProbabilityMeasure μ] {X Z : Ω → ℝ} (hX : MemLp X 2 μ)
    (hZ : MemLp Z 2 μ) (a b : ℝ) :
    ∫ ω, (Z ω - a - b * X ω) ^ 2 ∂μ = cov[Z, Z; μ] - 2 * b * cov[X, Z; μ] +
      b ^ 2 * cov[X, X; μ] + (μ[Z] - b * μ[X] - a) ^ 2 := by
  have hbX : MemLp (fun ω => b * X ω) 2 μ := hX.const_mul b
  have hu : MemLp (fun ω => Z ω - b * X ω) 2 μ := hZ.sub hbX
  have e : (fun ω => (Z ω - a - b * X ω) ^ 2) =
      fun ω => ((Z ω - b * X ω) - a) * ((Z ω - b * X ω) - a) := by
    funext ω; ring
  rw [e, integral_sub_mul_sub hu hu a a,
    integral_sub (hZ.integrable one_le_two) (hbX.integrable one_le_two), integral_const_mul,
    covariance_fun_sub_fun_sub hZ hbX hZ hbX, covariance_const_mul_left,
    covariance_const_mul_right, covariance_const_mul_left, covariance_const_mul_right,
    covariance_comm Z X]
  ring

/-- **Decomposition of the least squares objective.** Under second moments,
`lsObjective = ∑ Var(Z i) - 2 b ∑ Cov(X i, Z i) + b² ∑ Var(X i) + ∑ (E[Z i] - b E[X i] - a i)²`.
For a fixed slope the intercepts therefore enter only through the last sum, which vanishes
exactly at `lsIntercept`. -/
theorem lsObjective_eq [IsProbabilityMeasure μ] {X Z : ι → Ω → ℝ} (hX : ∀ i, MemLp (X i) 2 μ)
    (hZ : ∀ i, MemLp (Z i) 2 μ) (b : ℝ) (a : ι → ℝ) :
    lsObjective μ X Z b a = ∑ i, cov[Z i, Z i; μ] - 2 * b * ∑ i, cov[X i, Z i; μ] +
      b ^ 2 * ∑ i, Var[X i; μ] + ∑ i, (lsIntercept μ X Z b i - a i) ^ 2 := by
  simp only [lsObjective, lsIntercept, integral_sub_sub_mul_sq (hX _) (hZ _),
    covariance_self (hX _).aemeasurable, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.mul_sum]

/-- **The covariance ratio is the unique least squares slope.** Under second moments and a
positive pooled regressor variance `∑ᵢ Var(X i) > 0`, the slope `lsSlope` with the profiled
intercepts `lsIntercept` minimizes `lsObjective`, and any slope and intercepts attaining the
minimum are these. -/
theorem lsSlope_isMin [IsProbabilityMeasure μ] {X Z : ι → Ω → ℝ} (hX : ∀ i, MemLp (X i) 2 μ)
    (hZ : ∀ i, MemLp (Z i) 2 μ) (hV : 0 < ∑ i, Var[X i; μ]) :
    (∀ b a, lsObjective μ X Z (lsSlope μ X Z) (lsIntercept μ X Z (lsSlope μ X Z)) ≤
        lsObjective μ X Z b a) ∧
      ∀ b a, lsObjective μ X Z b a =
          lsObjective μ X Z (lsSlope μ X Z) (lsIntercept μ X Z (lsSlope μ X Z)) →
        b = lsSlope μ X Z ∧ a = lsIntercept μ X Z (lsSlope μ X Z) := by
  have hC : ∑ i, cov[X i, Z i; μ] = lsSlope μ X Z * ∑ i, Var[X i; μ] := by
    rw [lsSlope, div_mul_cancel₀ _ hV.ne']
  have hmin : lsObjective μ X Z (lsSlope μ X Z) (lsIntercept μ X Z (lsSlope μ X Z)) =
      ∑ i, cov[Z i, Z i; μ] - 2 * lsSlope μ X Z * ∑ i, cov[X i, Z i; μ] +
        lsSlope μ X Z ^ 2 * ∑ i, Var[X i; μ] := by
    rw [lsObjective_eq hX hZ]; simp
  have key : ∀ (b : ℝ) (a : ι → ℝ), lsObjective μ X Z b a =
      lsObjective μ X Z (lsSlope μ X Z) (lsIntercept μ X Z (lsSlope μ X Z)) +
        ((∑ i, Var[X i; μ]) * (b - lsSlope μ X Z) ^ 2 +
          ∑ i, (lsIntercept μ X Z b i - a i) ^ 2) := by
    intro b a
    rw [lsObjective_eq hX hZ, hmin, hC]
    ring
  have hS : ∀ (b : ℝ) (a : ι → ℝ), 0 ≤ ∑ i, (lsIntercept μ X Z b i - a i) ^ 2 := fun b a =>
    Finset.sum_nonneg fun i _ => sq_nonneg _
  refine ⟨fun b a => ?_, fun b a h => ?_⟩
  · rw [key b a]
    nlinarith [hS b a, mul_nonneg hV.le (sq_nonneg (b - lsSlope μ X Z))]
  · rw [key b a] at h
    have h1 : (∑ i, Var[X i; μ]) * (b - lsSlope μ X Z) ^ 2 = 0 := by
      nlinarith [hS b a, mul_nonneg hV.le (sq_nonneg (b - lsSlope μ X Z))]
    have hb : b = lsSlope μ X Z := by
      have := (mul_eq_zero.mp h1).resolve_left hV.ne'
      exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
    refine ⟨hb, ?_⟩
    have h2 : ∑ i, (lsIntercept μ X Z b i - a i) ^ 2 = 0 := by linarith
    funext i
    have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg
      (lsIntercept μ X Z b i - a i)).mp h2 i (Finset.mem_univ i)
    rw [← hb]
    exact (sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)).symm

end LeastSquares

section QuasiLeastSquares

variable [Fintype τ]

variable (P μ) in
/-- The population least squares objective of the quasi-demeaned regression with period
effects: `∑ₜ E[(Ỹ t - a t - b D̃ t)²]` with `Ỹ = quasiDemean θ Y`, `D̃ = quasiDemean θ D` and
one intercept `a t` per period. -/
noncomputable def quasiObjective (θ b : ℝ) (a : τ → ℝ) : ℝ :=
  lsObjective μ (quasiDemean θ P.D) (quasiDemean θ P.Y) b a

variable (P μ) in
/-- The period intercepts of the quasi-demeaned regression profiled out for the slope `b`:
the period means `E[Ỹ t] - b E[D̃ t]`. -/
noncomputable def quasiIntercept (θ b : ℝ) : τ → ℝ :=
  lsIntercept μ (quasiDemean θ P.D) (quasiDemean θ P.Y) b

/-- **The quasi-demeaned slope is the least squares slope with period effects.** Under second
moments and `∑ₜ Var(D t - θ D̄) > 0`, the covariance ratio `quasiSlope θ` with the period
intercepts `quasiIntercept θ` minimizes `quasiObjective θ`, and it is the unique minimizer:
any slope and period intercepts attaining the minimum are these. -/
theorem quasiSlope_isLeastSquares [IsProbabilityMeasure μ] (h : P.SecondMoments μ) (θ : ℝ)
    (hV : 0 < ∑ t, Var[quasiDemean θ P.D t; μ]) :
    (∀ b a, P.quasiObjective μ θ (P.quasiSlope μ θ) (P.quasiIntercept μ θ (P.quasiSlope μ θ)) ≤
        P.quasiObjective μ θ b a) ∧
      ∀ b a, P.quasiObjective μ θ b a =
          P.quasiObjective μ θ (P.quasiSlope μ θ) (P.quasiIntercept μ θ (P.quasiSlope μ θ)) →
        b = P.quasiSlope μ θ ∧ a = P.quasiIntercept μ θ (P.quasiSlope μ θ) :=
  lsSlope_isMin (memLp_quasiDemean θ h.memLp_D) (memLp_quasiDemean θ fun t => h.memLp_Y t) hV

/-- **The within slope is the least squares slope of the demeaned data with period effects**
(`θ = 1`): under second moments and `∑ₜ Var(D t - D̄) > 0` it is the unique minimizer of
`quasiObjective 1`. -/
theorem withinSlope_isLeastSquares [IsProbabilityMeasure μ] (h : P.SecondMoments μ)
    (hV : 0 < ∑ t, Var[quasiDemean 1 P.D t; μ]) :
    (∀ b a, P.quasiObjective μ 1 (P.withinSlope μ) (P.quasiIntercept μ 1 (P.withinSlope μ)) ≤
        P.quasiObjective μ 1 b a) ∧
      ∀ b a, P.quasiObjective μ 1 b a =
          P.quasiObjective μ 1 (P.withinSlope μ) (P.quasiIntercept μ 1 (P.withinSlope μ)) →
        b = P.withinSlope μ ∧ a = P.quasiIntercept μ 1 (P.withinSlope μ) :=
  quasiSlope_isLeastSquares h 1 hV

/-- **The pooled slope is the least squares slope with period effects** of the untransformed
data (`θ = 0`): under second moments and `∑ₜ Var(D t) > 0` it is the unique minimizer of
`∑ₜ E[(Y t - a t - b D t)²]`. -/
theorem pooledSlope_isLeastSquares [IsProbabilityMeasure μ] (h : P.SecondMoments μ)
    (hV : 0 < ∑ t, Var[P.D t; μ]) :
    (∀ b a, lsObjective μ P.D P.Y (P.pooledSlope μ) (lsIntercept μ P.D P.Y (P.pooledSlope μ)) ≤
        lsObjective μ P.D P.Y b a) ∧
      ∀ b a, lsObjective μ P.D P.Y b a =
          lsObjective μ P.D P.Y (P.pooledSlope μ) (lsIntercept μ P.D P.Y (P.pooledSlope μ)) →
        b = P.pooledSlope μ ∧ a = lsIntercept μ P.D P.Y (P.pooledSlope μ) :=
  lsSlope_isMin h.memLp_D (fun t => h.memLp_Y t) hV

end QuasiLeastSquares

section GLSLeastSquares

open Matrix

variable [Fintype τ] [DecidableEq τ]

variable (P μ) in
/-- The population generalized least squares objective with weight matrix `V⁻¹` and period
intercepts `c`: `E[rᵀ V⁻¹ r]` for the residual vector `r t = Y t - c t - b D t` of a unit. -/
noncomputable def glsObjective (V : Matrix τ τ ℝ) (b : ℝ) (c : τ → ℝ) : ℝ :=
  ∫ ω, (fun t => P.Y t ω - c t - b * P.D t ω) ⬝ᵥ
    (V⁻¹ *ᵥ fun t => P.Y t ω - c t - b * P.D t ω) ∂μ

/-- Quasi-demeaning the residual vector of a unit quasi-demeans the outcome, the treatment
and the intercept vector. -/
theorem quasi_mulVec_residual (θ b : ℝ) (c : τ → ℝ) (ω : Ω) (t : τ) :
    ((1 - θ • periodAverage) *ᵥ fun s => P.Y s ω - c s - b * P.D s ω) t =
      quasiDemean θ P.Y t ω - ((1 - θ • periodAverage) *ᵥ c) t - b * quasiDemean θ P.D t ω := by
  have e : (fun s => P.Y s ω - c s - b * P.D s ω) =
      (fun s => P.Y s ω) - c - b • fun s => P.D s ω := by
    funext s; simp
  rw [e, mulVec_sub, mulVec_sub, mulVec_smul, quasiDemean_eq_mulVec, quasiDemean_eq_mulVec]
  simp

/-- **The generalized least squares objective is a scaled quasi-demeaned objective.** Under
second moments and compound symmetry of the composite errors with `σε² = s ≠ 0`, and for `θ`
with `(1 - θ)² (s + T a) = s`, the objective `E[rᵀ V⁻¹ r]` with `V = compositeCov` equals
`s⁻¹` times the quasi-demeaned objective at the quasi-demeaned intercepts
`(I - θ 1 1ᵀ / T) c`. -/
theorem glsObjective_eq [Nonempty τ] [IsProbabilityMeasure μ] (h : P.SecondMoments μ)
    {s a θ : ℝ} (hCS : P.CompoundSymmetry μ s a) (hs : s ≠ 0)
    (hθ : (1 - θ) ^ 2 * (s + Fintype.card τ * a) = s) (b : ℝ) (c : τ → ℝ) :
    P.glsObjective μ (P.compositeCov μ) b c =
      s⁻¹ * P.quasiObjective μ θ b ((1 - θ • periodAverage) *ᵥ c) := by
  have hpt : ∀ ω, (fun t => P.Y t ω - c t - b * P.D t ω) ⬝ᵥ
      ((P.compositeCov μ)⁻¹ *ᵥ fun t => P.Y t ω - c t - b * P.D t ω) =
      s⁻¹ * ∑ t, (quasiDemean θ P.Y t ω - ((1 - θ • periodAverage) *ᵥ c) t -
        b * quasiDemean θ P.D t ω) ^ 2 := by
    intro ω
    rw [show P.compositeCov μ = compoundSymmetric s a from hCS, gls_quadForm_eq hs hθ]
    congr 1
    simp only [dotProduct, quasi_mulVec_residual, sq]
  have hint : ∀ t, Integrable (fun ω => (quasiDemean θ P.Y t ω -
      ((1 - θ • periodAverage) *ᵥ c) t - b * quasiDemean θ P.D t ω) ^ 2) μ := fun t =>
    (((memLp_quasiDemean θ (fun t => h.memLp_Y t) t).sub (memLp_const _)).sub
      ((memLp_quasiDemean θ h.memLp_D t).const_mul b)).integrable_sq
  rw [glsObjective, integral_congr_ae (ae_of_all _ hpt), integral_const_mul,
    integral_finsetSum _ fun t _ => hint t]
  rfl

/-- The inverse `I + θ / (1 - θ) 1 1ᵀ / T` of the quasi-demeaning matrix, for `θ ≠ 1`. -/
noncomputable def quasiInverse (θ : ℝ) : Matrix τ τ ℝ := 1 + (θ / (1 - θ)) • periodAverage

/-- `quasiInverse θ` is a right inverse of `I - θ 1 1ᵀ / T` for `θ ≠ 1`, so quasi-demeaning
is a bijection on intercept vectors. -/
theorem quasi_mul_quasiInverse [Nonempty τ] {θ : ℝ} (hθ : θ ≠ 1) :
    (1 - θ • periodAverage) * quasiInverse θ = (1 : Matrix τ τ ℝ) := by
  have h1 : (1 : ℝ) - θ ≠ 0 := sub_ne_zero.mpr (Ne.symm hθ)
  have hκ : θ / (1 - θ) * (1 - θ) = θ := div_mul_cancel₀ _ h1
  have hP := periodAverage_mul_self (τ := τ)
  simp only [quasiInverse, sub_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
    hP]
  linear_combination (norm := module) hκ • (periodAverage : Matrix τ τ ℝ)

/-- **Generalized least squares and the quasi-demeaned slope.** Under second moments,
compound symmetry with `σε² = s > 0`, a `θ ≠ 1` with `(1 - θ)² (s + T a) = s` and
`∑ₜ Var(D t - θ D̄) > 0`, the slope `quasiSlope θ` with the intercepts `quasiInverse θ`
applied to `quasiIntercept θ` minimizes the generalized least squares objective `E[rᵀ V⁻¹ r]`,
and every minimizing slope is `quasiSlope θ`. -/
theorem gls_isLeastSquares [Nonempty τ] [IsProbabilityMeasure μ] (h : P.SecondMoments μ)
    {s a θ : ℝ} (hCS : P.CompoundSymmetry μ s a) (hs : 0 < s)
    (hθ : (1 - θ) ^ 2 * (s + Fintype.card τ * a) = s) (hθ1 : θ ≠ 1)
    (hV : 0 < ∑ t, Var[quasiDemean θ P.D t; μ]) :
    (∀ b c, P.glsObjective μ (P.compositeCov μ) (P.quasiSlope μ θ)
        (quasiInverse θ *ᵥ P.quasiIntercept μ θ (P.quasiSlope μ θ)) ≤
        P.glsObjective μ (P.compositeCov μ) b c) ∧
      ∀ b c, P.glsObjective μ (P.compositeCov μ) b c =
          P.glsObjective μ (P.compositeCov μ) (P.quasiSlope μ θ)
            (quasiInverse θ *ᵥ P.quasiIntercept μ θ (P.quasiSlope μ θ)) →
        b = P.quasiSlope μ θ := by
  have hinv : ∀ v : τ → ℝ, (1 - θ • periodAverage) *ᵥ (quasiInverse θ *ᵥ v) = v := fun v => by
    rw [mulVec_mulVec, quasi_mul_quasiInverse hθ1, one_mulVec]
  obtain ⟨hmin, huniq⟩ := quasiSlope_isLeastSquares h θ hV
  have hsi : 0 < s⁻¹ := inv_pos.mpr hs
  refine ⟨fun b c => ?_, fun b c hbc => ?_⟩
  · rw [glsObjective_eq h hCS hs.ne' hθ, glsObjective_eq h hCS hs.ne' hθ, hinv]
    exact mul_le_mul_of_nonneg_left (hmin _ _) hsi.le
  · rw [glsObjective_eq h hCS hs.ne' hθ, glsObjective_eq h hCS hs.ne' hθ, hinv] at hbc
    exact (huniq _ _ (mul_left_cancel₀ hsi.ne' hbc)).1

/-- **The random effects slope is the generalized least squares slope** (TSD 17,
Section 2.4.2). Under second moments, compound symmetry of the composite errors with
`σε² = s > 0` and `σα² = a ≥ 0`, and `∑ₜ Var(D t - θ D̄) > 0` at `θ = reTheta`, the
quasi-demeaned slope at `reTheta` is the unique slope minimizing `E[rᵀ V⁻¹ r]`. -/
theorem gls_isLeastSquares_reTheta [Nonempty τ] [IsProbabilityMeasure μ]
    (h : P.SecondMoments μ) {s a : ℝ} (hCS : P.CompoundSymmetry μ s a) (hs : 0 < s)
    (ha : 0 ≤ a)
    (hV : 0 < ∑ t, Var[quasiDemean (reTheta (Fintype.card τ) s a) P.D t; μ]) :
    (∀ b c, P.glsObjective μ (P.compositeCov μ) (P.quasiSlope μ (reTheta (Fintype.card τ) s a))
        (quasiInverse (reTheta (Fintype.card τ) s a) *ᵥ P.quasiIntercept μ
          (reTheta (Fintype.card τ) s a) (P.quasiSlope μ (reTheta (Fintype.card τ) s a))) ≤
        P.glsObjective μ (P.compositeCov μ) b c) ∧
      ∀ b c, P.glsObjective μ (P.compositeCov μ) b c =
          P.glsObjective μ (P.compositeCov μ) (P.quasiSlope μ (reTheta (Fintype.card τ) s a))
            (quasiInverse (reTheta (Fintype.card τ) s a) *ᵥ P.quasiIntercept μ
              (reTheta (Fintype.card τ) s a) (P.quasiSlope μ (reTheta (Fintype.card τ) s a))) →
        b = P.quasiSlope μ (reTheta (Fintype.card τ) s a) :=
  gls_isLeastSquares h hCS hs (one_sub_reTheta_sq hs (Nat.cast_nonneg _) ha)
    (reTheta_mem hs (Nat.cast_nonneg _) ha).2.ne hV

end GLSLeastSquares

variable (P) in
/-- The outcome of a panel model with **time-varying heterogeneity**: the unit effect enters
period `t` with loading `lam t`, `Y t = δ t + lam t α + β D t + ε t`. The linear panel model is
the case of a constant loading `1` (`Counterexample.loadedY_one`). -/
def loadedY (lam : τ → ℝ) (t : τ) (ω : Ω) : ℝ :=
  P.δ t + lam t * P.α ω + P.β * P.D t ω + P.ε t ω

/-! ### Countermodels -/

namespace Counterexample

/-- A fair coin: the uniform distribution on `Bool`, the population of units. -/
noncomputable def coin : Measure Bool := uniformOn Set.univ

instance : IsProbabilityMeasure coin := by unfold coin; infer_instance

/-- The indicator of `true`, coded as a real number. -/
def ind (b : Bool) : ℝ := if b then 1 else 0

theorem integral_coin (f : Bool → ℝ) : ∫ x, f x ∂coin = (f true + f false) / 2 := by
  rw [coin, integral_fintype .of_finite, Fintype.sum_bool]
  simp only [measureReal_def, uniformOn_univ]
  simp
  ring

theorem memLp_coin (f : Bool → ℝ) : MemLp f 2 coin :=
  MemLp.of_bound (measurable_of_countable f).aestronglyMeasurable (|f true| + |f false|)
    (ae_of_all _ fun b ↦ by cases b <;> simp [abs_nonneg])

theorem cov_coin (f g : Bool → ℝ) : cov[f, g; coin] =
    ((f true - (f true + f false) / 2) * (g true - (g true + g false) / 2) +
      (f false - (f true + f false) / 2) * (g false - (g true + g false) / 2)) / 2 := by
  rw [covariance, integral_coin, integral_coin, integral_coin]

theorem var_coin (f : Bool → ℝ) : Var[f; coin] =
    ((f true - (f true + f false) / 2) ^ 2 + (f false - (f true + f false) / 2) ^ 2) / 2 := by
  rw [variance_eq_integral (measurable_of_countable f).aemeasurable, integral_coin, integral_coin]

/-- **Correlated heterogeneity.** Two periods (`false`, then `true`) and two equally likely
units. The unit effect is `α = ind`, nobody is treated in the first period, and in the second
period exactly the units with `α = 1` are treated (`D true = ind`). The causal slope is `β = 0`
and there is no error, so strict exogeneity holds. -/
noncomputable def correlated : LinearPanel Bool Bool where
  β := 0
  δ := fun _ ↦ 0
  α := ind
  D := fun t ω ↦ if t then ind ω else 0
  ε := fun _ _ ↦ 0

/-- **Countermodel: correlated heterogeneity defeats pooled and random effects slopes.** In
`correlated` strict exogeneity holds, and the first-difference and within slopes recover
`β = 0`, but the pooled slope is `1` and every quasi-demeaned (random effects) slope with
`θ ≠ 1` differs from `β`: the only failing assumption of these estimands is
`∑ₜ Cov(D t, α) = 0`. -/
theorem correlated_slopes :
    correlated.StrictExogeneity coin ∧
      correlated.fdSlope coin {(false, true)} = correlated.β ∧
      correlated.withinSlope coin = correlated.β ∧
      correlated.pooledSlope coin = 1 ∧ correlated.pooledSlope coin ≠ correlated.β ∧
      ∀ θ : ℝ, θ ≠ 1 → correlated.quasiSlope coin θ ≠ correlated.β := by
  have hSM : correlated.SecondMoments coin :=
    ⟨memLp_coin _, fun _ ↦ memLp_coin _, fun _ ↦ memLp_coin _⟩
  have hE : correlated.StrictExogeneity coin := by
    intro s t
    simp [correlated]
  have hΔ : Var[fun ω ↦ correlated.D true ω - correlated.D false ω; coin] ≠ 0 := by
    simp [var_coin, correlated, ind]
    norm_num
  have hfd : correlated.fdSlope coin {(false, true)} = correlated.β :=
    fdSlope_eq_beta hSM hE _ (by simpa using hΔ)
  have hpool : correlated.pooledSlope coin = 1 := by
    simp [pooledSlope, cov_coin, var_coin, Y, correlated, ind]
    norm_num
  refine ⟨hE, hfd, ?_, hpool, ?_, fun θ hθ ↦ quasiSlope_ne_beta hSM hE hθ ?_ ?_⟩
  · rw [withinSlope_eq_fdSlope hSM (s := false) (t := true) (by decide) (by decide) hΔ, hfd]
  · rw [hpool]; simp [correlated]
  · have e : ∑ t, Var[quasiDemean θ correlated.D t; coin] =
        ((1 - θ / 2) ^ 2 + (θ / 2) ^ 2) / 4 := by
      simp [quasiDemean, unitMean, var_coin, correlated, ind]
      ring
    rw [e]
    have : 0 < (1 - θ / 2) ^ 2 + (θ / 2) ^ 2 := by
      nlinarith [sq_nonneg (1 - θ / 2), sq_nonneg (θ / 2)]
    positivity
  · simp [cov_coin, correlated, ind]
    norm_num

/-- **Feedback from past shocks.** Two periods and two equally likely units, no unit effect
(`α = 0`) and `β = 0`. The first-period error is `ε false = ind`, and the second-period
treatment responds to it: `D true = ind`, while `D false = 0` and `ε true = 0`. Each period's
treatment is uncorrelated with that period's error, but the second-period treatment is
correlated with the first-period error. -/
noncomputable def feedback : LinearPanel Bool Bool where
  β := 0
  δ := fun _ ↦ 0
  α := fun _ ↦ 0
  D := fun t ω ↦ if t then ind ω else 0
  ε := fun t ω ↦ if t then 0 else ind ω

/-- **Countermodel: strict exogeneity fails.** In `feedback` the unit effect is zero (so it is
uncorrelated with everything) and contemporaneous exogeneity holds, but strict exogeneity fails;
the first-difference slope is `-1 ≠ β = 0`, while the pooled slope, which needs only
contemporaneous exogeneity, recovers `β`. -/
theorem feedback_slopes :
    feedback.ContemporaneousExogeneity coin ∧ ¬ feedback.StrictExogeneity coin ∧
      feedback.fdSlope coin {(false, true)} = -1 ∧
      feedback.fdSlope coin {(false, true)} ≠ feedback.β ∧
      feedback.pooledSlope coin = feedback.β := by
  have hfd : feedback.fdSlope coin {(false, true)} = -1 := by
    simp [fdSlope, cov_coin, var_coin, Y, feedback, ind]
    norm_num
  refine ⟨?_, ?_, hfd, ?_, ?_⟩
  · intro t
    cases t <;> simp [feedback]
  · intro h
    have := h true false
    simp [feedback, cov_coin, ind] at this
    norm_num at this
  · rw [hfd]; simp [feedback]
  · simp [pooledSlope, cov_coin, var_coin, Y, feedback, ind]

/-- **Treatment timing confounded with a period effect.** Two periods and two equally likely
units, no unit effect and no error; nobody is treated in the first period and everybody in the
second (`D t = 1{t}` for every unit), with causal slope `β` and period effect `c` in the second
period. -/
noncomputable def timing (β c : ℝ) : LinearPanel Bool Bool where
  β := β
  δ := fun t ↦ if t then c else 0
  α := fun _ ↦ 0
  D := fun t _ ↦ if t then 1 else 0
  ε := fun _ _ ↦ 0

/-- **Countermodel: the ordinary pooled slope without period dummies.** In `timing β c`
strict exogeneity holds and the period-dummy denominator `∑ₜ Var(D t)` is zero (so the slopes
with period dummies are not defined by the data), while the stacked treatment variation is
`1 / 2` and the ordinary pooled slope is `β + c`: it recovers `β` when there is no period
effect and is biased by `c` otherwise. -/
theorem timing_slopes (β c : ℝ) :
    (timing β c).StrictExogeneity coin ∧ ∑ t, Var[(timing β c).D t; coin] = 0 ∧
      stackedCov coin (timing β c).D (timing β c).D = 1 / 2 ∧
      (timing β c).ordinarySlope coin = β + c := by
  have hb : ({false, true} : Set Bool) = Set.univ := by
    ext b; cases b <;> simp
  have hu : coin.real ({false, true} : Set Bool) = 1 := by
    simp only [hb, probReal_univ]
  refine ⟨fun s t ↦ by simp [timing], by simp [timing, var_coin], ?_, ?_⟩
  · simp [stackedCov, grandMean, timing, hu]
    norm_num
  · simp [ordinarySlope, stackedCov, grandMean, timing, Y, hu]
    ring

/-- With a constant loading `1` the loaded outcome is the outcome of the linear panel. -/
theorem loadedY_one (P : LinearPanel Ω τ) : P.loadedY (fun _ ↦ 1) = P.Y := by
  funext t ω; simp [loadedY, Y]

/-- **Countermodel: time-invariant heterogeneity fails** (TSD 17, Section 2.4.2, names time
invariance of the unobserved heterogeneity as the assumption first differences and fixed
effects require). In `correlated` strict exogeneity holds and the first-difference slope of the
outcome `Y` recovers `β = 0`. If instead the unit effect enters with the time-varying loading
`0` in the first period and `1` in the second (`loadedY`), with treatment, errors and `β`
unchanged, the first-difference slope `Cov(ΔD, ΔY) / Var(ΔD)` is `1 ≠ β`, with a positive
denominator. Only time invariance of the unit effect fails. -/
theorem timeVarying_slopes :
    correlated.StrictExogeneity coin ∧
      correlated.fdSlope coin {(false, true)} = correlated.β ∧
      cov[fun ω ↦ correlated.D true ω - correlated.D false ω,
        fun ω ↦ correlated.loadedY (fun t ↦ if t then 1 else 0) true ω -
          correlated.loadedY (fun t ↦ if t then 1 else 0) false ω; coin] /
        Var[fun ω ↦ correlated.D true ω - correlated.D false ω; coin] = 1 ∧
      Var[fun ω ↦ correlated.D true ω - correlated.D false ω; coin] ≠ 0 ∧
      (1 : ℝ) ≠ correlated.β := by
  have hE : correlated.StrictExogeneity coin := fun s t ↦ by simp [correlated]
  have hV : Var[fun ω ↦ correlated.D true ω - correlated.D false ω; coin] ≠ 0 := by
    simp [var_coin, correlated, ind]; norm_num
  have hSM : correlated.SecondMoments coin :=
    ⟨memLp_coin _, fun _ ↦ memLp_coin _, fun _ ↦ memLp_coin _⟩
  refine ⟨hE, fdSlope_eq_beta hSM hE _ (by simpa using hV), ?_, hV, by simp [correlated]⟩
  simp [cov_coin, var_coin, loadedY, correlated, ind]
  norm_num

end Counterexample

end LinearPanel

end CausalInference
