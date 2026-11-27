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
  `LinearPanel.pooledSlope` (`θ = 0`). All slopes are pooled over periods with period dummies.

## Main results

* `LinearPanel.fdSlope_eq`, `LinearPanel.fdSlope_eq_beta`, `LinearPanel.fdSlope_pair_eq_beta`:
  the first-difference slope is `β` plus a term in `Cov(ΔD, Δε)` only, so under strict
  exogeneity it equals `β` for every joint law of the unit effect and the treatment.
* `LinearPanel.quasiSlope_eq`: under strict exogeneity the quasi-demeaned slope is
  `β + (1 - θ)² ∑ₜ Cov(D t, α) / ∑ₜ Var(D t - θ D̄)`. Corollaries:
  `LinearPanel.withinSlope_eq_beta` (fixed effects identify `β`),
  `LinearPanel.quasiSlope_eq_beta_of_uncorrelated` (random effects slopes identify `β` when the
  heterogeneity is uncorrelated with the treatment), `LinearPanel.quasiSlope_ne_beta` (and do not
  when it is correlated).
* `LinearPanel.pooledSlope_eq`, `LinearPanel.pooledSlope_ne_beta`: the pooled slope is
  `β + ∑ₜ Cov(D t, α) / ∑ₜ Var(D t)` under contemporaneous exogeneity alone.
* `LinearPanel.withinSlope_eq_fdSlope`: with two periods the within and first-difference slopes
  coincide.
* `LinearPanel.Counterexample.correlated_slopes`: strict exogeneity holds and the heterogeneity
  is correlated with the treatment; first differences and within recover `β = 0`, the pooled
  slope is `1`, and every quasi-demeaned slope with `θ ≠ 1` differs from `β`.
* `LinearPanel.Counterexample.feedback_slopes`: no unit effect and contemporaneous exogeneity,
  but the treatment responds to a past shock; the first-difference slope is `-1 ≠ β = 0`.

The random effects estimator is generalized least squares, which in this model is the
quasi-demeaned slope for a `θ ∈ [0, 1)` fixed by the variance components; the bias formula
holds for every fixed `θ`, and no optimality property of any `θ` is claimed.

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
(fixed effects) transformation, `θ = 0` leaves the data unchanged (pooled least squares), and the
random effects (generalized least squares) transformation is `θ ∈ [0, 1)`, determined by the
variance components. -/
noncomputable def quasiDemean (θ : ℝ) (X : τ → Ω → ℝ) (t : τ) (ω : Ω) : ℝ :=
  X t ω - θ * unitMean X ω

variable (P μ) in
/-- The population slope after quasi-demeaning with parameter `θ`, pooled over periods with a
separate intercept for each period (period dummies):
`∑ₜ Cov(D t - θ D̄, Y t - θ Ȳ) / ∑ₜ Var(D t - θ D̄)`. -/
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

end Counterexample

end LinearPanel

end CausalInference
