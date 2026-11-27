/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Designs.Panel.FixedEffects
public import CausalInference.Designs.DifferenceInDifferences.TwoPeriod
public import CausalInference.InstrumentalVariables.LinearIV

/-!
# Difference in differences as first differences

TSD 17 (Section 2.5.1) states that with longitudinal data the difference in differences
estimator is the first-difference estimator of panel data models. This file proves the
population version on a probability space `(Ω, μ)` of units, with conditional means against
`ProbabilityTheory.cond` as in `CausalInference.Designs.DifferenceInDifferences.TwoPeriod`.

## Main results

* `LinearPanel.variance_boolToReal`: `Var(G) = P(G = 1) P(G = 0)` for a binary indicator.
* `LinearPanel.covRatio_fd_eq_did`: for any observed two-period outcomes and a binary group
  indicator `G` with both groups of positive probability, the least squares slope of
  `Yobs post - Yobs pre` on `G` is the observed difference in differences `TwoPeriod.did`. This
  is a statement about observed data only.
* `LinearPanel.fdSlope_eq_did`: in a linear panel model over the periods `pre, post` in which
  nobody is treated before and the group `G` is treated after, the first-difference slope equals
  `TwoPeriod.did`.
* `LinearPanel.withinSlope_eq_did`: the within (two-way fixed effects) slope also equals
  `TwoPeriod.did` in that model.
* `LinearPanel.did_eq_beta`: under finite second moments and strict exogeneity the difference in
  differences then equals the causal slope `β`, whatever the correlation between the unit effect
  and the group.

Source: NICE Decision Support Unit, Technical Support Document 17 (Faria, Hernandez Alava,
Manca and Wailoo, 2015), Sections 2.4.2 and 2.5.1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace CausalInference

namespace LinearPanel

open TwoPeriod TwoPeriod.Period IVModel

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The variance of a binary group indicator coded `0`/`1`: `Var(G) = P(G = 1) P(G = 0)`. -/
theorem variance_boolToReal [IsProbabilityMeasure μ] {G : Ω → Bool} (hG : Measurable G) :
    Var[fun ω ↦ boolToReal (G ω); μ] = μ.real (treated G) * μ.real (control G) := by
  have hGi : Integrable (fun ω ↦ boolToReal (G ω)) μ :=
    Integrable.of_bound (measurable_boolToReal.comp hG).aestronglyMeasurable 1
      (ae_of_all _ fun ω ↦ by cases G ω <;> simp [boolToReal])
  rw [← covariance_self hGi.aemeasurable, LinearIV.covariance_boolToReal hG hGi]
  by_cases h1 : μ (treated G) = 0
  · simp [measureReal_def, show μ (G ⁻¹' {true}) = 0 from h1, h1]
  by_cases h0 : μ (control G) = 0
  · simp [measureReal_def, show μ (G ⁻¹' {false}) = 0 from h0, h0]
  rw [DiD.integral_cond_eq_of_eqOn (hG (measurableSet_singleton true)) h1
      (k := 1) fun ω hω ↦ by simp [boolToReal, show G ω = true from hω],
    DiD.integral_cond_eq_of_eqOn (hG (measurableSet_singleton false)) h0
      (k := 0) fun ω hω ↦ by simp [boolToReal, show G ω = false from hω]]
  rw [show G ⁻¹' {true} = treated G from rfl, show G ⁻¹' {false} = TwoPeriod.control G from rfl]
  ring

/-- **The first-difference regression on a binary group is the difference in differences**
(TSD 17, Section 2.5.1). Let `G` be a measurable group indicator with both groups of positive
probability and `Yobs` integrable observed outcomes in the two periods. Then the least squares
slope of the change `Yobs post - Yobs pre` on `G` (coded `0`/`1`),
`Cov(G, ΔY) / Var(G)`, equals the observed difference in differences `TwoPeriod.did μ G Yobs`. -/
theorem covRatio_fd_eq_did [IsProbabilityMeasure μ] {G : Ω → Bool} (hG : Measurable G)
    {Yobs : Period → Ω → ℝ} (hY : ∀ t, Integrable (Yobs t) μ) (h1 : μ (treated G) ≠ 0)
    (h0 : μ (control G) ≠ 0) :
    cov[fun ω ↦ boolToReal (G ω), fun ω ↦ Yobs post ω - Yobs pre ω; μ] /
      Var[fun ω ↦ boolToReal (G ω); μ] = TwoPeriod.did μ G Yobs := by
  have hp : μ.real (treated G) ≠ 0 := fun h ↦ h1 ((measureReal_eq_zero_iff).1 h)
  have hq : μ.real (control G) ≠ 0 := fun h ↦ h0 ((measureReal_eq_zero_iff).1 h)
  have hΔ : Integrable (fun ω ↦ Yobs post ω - Yobs pre ω) μ := (hY post).sub (hY pre)
  rw [variance_boolToReal hG, LinearIV.covariance_boolToReal hG hΔ,
    show G ⁻¹' {true} = treated G from rfl, show G ⁻¹' {false} = TwoPeriod.control G from rfl,
    integral_sub (DiD.integrable_cond (hY post) _) (DiD.integrable_cond (hY pre) _),
    integral_sub (DiD.integrable_cond (hY post) _) (DiD.integrable_cond (hY pre) _), did]
  field_simp

/-- **The first-difference slope of a two-period panel is the difference in differences.** In a
linear panel model over the periods `pre, post` with finite second moments, in which nobody is
treated in the pre period (`D pre = 0`) and the units of group `G` are treated in the post
period (`D post = G`, coded `0`/`1`), with both groups of positive probability, the
first-difference slope equals the observed difference in differences of the outcome. -/
theorem fdSlope_eq_did [IsProbabilityMeasure μ] {P : LinearPanel Ω Period}
    (h : P.SecondMoments μ) {G : Ω → Bool} (hG : Measurable G) (hpre : ∀ ω, P.D pre ω = 0)
    (hpost : ∀ ω, P.D post ω = boolToReal (G ω)) (h1 : μ (treated G) ≠ 0)
    (h0 : μ (control G) ≠ 0) :
    P.fdSlope μ {(pre, post)} = TwoPeriod.did μ G P.Y := by
  have e : (fun ω ↦ P.D post ω - P.D pre ω) = fun ω ↦ boolToReal (G ω) := by
    funext ω; rw [hpre, hpost, sub_zero]
  rw [fdSlope, Finset.sum_singleton, Finset.sum_singleton, e]
  exact covRatio_fd_eq_did hG (fun t ↦ (h.memLp_Y t).integrable one_le_two) h1 h0

/-- **Difference in differences identifies the causal slope in a linear panel** (TSD 17,
Sections 2.4.2 and 2.5.1). Under the hypotheses of `fdSlope_eq_did` and strict exogeneity, the
observed difference in differences equals `β`. No assumption restricts the correlation between
the unit effect `α` and the group `G`; the period effects `δ` are arbitrary. -/
theorem did_eq_beta [IsProbabilityMeasure μ] {P : LinearPanel Ω Period}
    (h : P.SecondMoments μ) (hE : P.StrictExogeneity μ) {G : Ω → Bool} (hG : Measurable G)
    (hpre : ∀ ω, P.D pre ω = 0) (hpost : ∀ ω, P.D post ω = boolToReal (G ω))
    (h1 : μ (treated G) ≠ 0) (h0 : μ (control G) ≠ 0) :
    TwoPeriod.did μ G P.Y = P.β := by
  rw [← fdSlope_eq_did h hG hpre hpost h1 h0]
  refine fdSlope_eq_beta h hE _ ?_
  have e : (fun ω ↦ P.D post ω - P.D pre ω) = fun ω ↦ boolToReal (G ω) := by
    funext ω; rw [hpre, hpost, sub_zero]
  rw [Finset.sum_singleton, e, variance_boolToReal hG]
  exact mul_ne_zero (fun h ↦ h1 ((measureReal_eq_zero_iff).1 h))
    (fun h ↦ h0 ((measureReal_eq_zero_iff).1 h))

/-- The enumeration `pre, post` of the two periods. It is a local instance of this file only;
no global instance on `TwoPeriod.Period` is declared. -/
abbrev periodFintype : Fintype Period := ⟨{pre, post}, fun p ↦ by cases p <;> simp⟩

attribute [local instance] periodFintype

/-- **The two-period within (two-way fixed effects) slope is the difference in differences**
(TSD 17, Section 2.5.1). Under the hypotheses of `fdSlope_eq_did`, with the periods enumerated
as `pre, post`, the within slope equals the observed difference in differences. -/
theorem withinSlope_eq_did [IsProbabilityMeasure μ] {P : LinearPanel Ω Period}
    (h : P.SecondMoments μ) {G : Ω → Bool} (hG : Measurable G) (hpre : ∀ ω, P.D pre ω = 0)
    (hpost : ∀ ω, P.D post ω = boolToReal (G ω)) (h1 : μ (treated G) ≠ 0)
    (h0 : μ (TwoPeriod.control G) ≠ 0) :
    P.withinSlope μ = TwoPeriod.did μ G P.Y := by
  have e : (fun ω ↦ P.D post ω - P.D pre ω) = fun ω ↦ boolToReal (G ω) := by
    funext ω; rw [hpre, hpost, sub_zero]
  have hV : Var[fun ω ↦ P.D post ω - P.D pre ω; μ] ≠ 0 := by
    rw [e, variance_boolToReal hG]
    exact mul_ne_zero (fun h ↦ h1 ((measureReal_eq_zero_iff).1 h))
      (fun h ↦ h0 ((measureReal_eq_zero_iff).1 h))
  have huniv : (Finset.univ : Finset Period) = {pre, post} := rfl
  rw [withinSlope_eq_fdSlope h (by decide) huniv hV, fdSlope_eq_did h hG hpre hpost h1 h0]

end LinearPanel

end CausalInference
