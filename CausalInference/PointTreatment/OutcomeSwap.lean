/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PointTreatment.OutcomeRegression

/-!
# Point treatment: the conditional average effect and the outcome swap

The conditional average effect `cate μ W Y` is the conditional expectation
`E[Y(1) - Y(0) | W]`. Any pair of versions `m_a(W)` of the potential outcome regressions
`E[Y(a) | W]` gives a version `m_1(W) - m_0(W)` of it (`cate_ae_eq_of_regression`).

**The outcome swap.** By consistency the observed outcome equals `Y(a)` on the arm `{A = a}`, so
the observed regression `E[Y | W, A]` and the potential outcome regression `E[Y(a) | W, A]`,
evaluated at `A = a`, agree wherever the arm has positive conditional probability
`P(A = a | W) > 0`. No ignorability is used. Under mean ignorability for the arm, the observed
regression at `a` is then `E[Y(a) | W]` on that set. These are local forms of
`IsOutcomeRegression.ae_eq_condExp`, which assumes positivity almost everywhere; outside the set
`{P(A = a | W) > 0}` the observed regression at `a` is not determined by the law of the data.

## Main results

* `cate_ae_eq_of_regression`: `m_1(W) - m_0(W)` is a version of `E[Y(1) - Y(0) | W]`.
* `ae_eq_zero_of_respInd_arm_mul`: a `σ(W)`-measurable function that vanishes on the arm vanishes
  where the arm has positive conditional probability.
* `IsOutcomeRegression.ae_eq_of_pos`, `IsOutcomeRegression.ae_map_eq_of_pos`: the outcome swap
  `E[Y | W, A = a] = E[Y(a) | W, A = a]` on `{P(A = a | W) > 0}`, at almost every unit and at
  almost every covariate value.
* `IsOutcomeRegression.ae_eq_condExp_of_pos`: under mean ignorability for the arm,
  `E[Y | W, A = a] = E[Y(a) | W]` on `{P(A = a | W) > 0}`.

## References

* J. M. Robins, *A new approach to causal inference in mortality studies with a sustained
  exposure period*, Mathematical Modelling 7 (1986).
-/

@[expose] public section

namespace CausalInference

namespace PointTreatment

open MeasureTheory ProbabilityTheory MissingData

variable {Ω 𝒲 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒲] {μ : Measure Ω}
  {A : Ω → Bool} {W : Ω → 𝒲} {Y : Bool → Ω → ℝ} {e : 𝒲 → ℝ} {m : Bool → 𝒲 → ℝ}

/-- **The conditional average effect from the arm regressions.** If `m_a(W)` is a version of
`E[Y(a) | W]` for both arms and the potential outcomes are integrable, then
`m_1(W) - m_0(W)` is a version of `E[Y(1) - Y(0) | W] = cate μ W Y`. -/
theorem cate_ae_eq_of_regression (hYi : ∀ a, Integrable (Y a) μ)
    (hm : ∀ a, (fun ω => m a (W ω)) =ᵐ[μ] μ[Y a | MeasurableSpace.comap W inferInstance]) :
    (fun ω => m true (W ω) - m false (W ω)) =ᵐ[μ] cate μ W Y := by
  filter_upwards [hm true, hm false, cate_ae_eq_sub W hYi] with ω h1 h0 hc
  rw [hc, Pi.sub_apply, h1, h0]

/-- **Vanishing on an arm spreads to the positivity set.** Let `e(W)` be a version of the
propensity score and `D` a `σ(W)`-measurable function with `1{A = a} D = 0` almost everywhere.
Then `D = 0` at almost every unit with `P(A = a | W) > 0`. Conditioning `1{A = a} D` on `W`
gives `π_a(W) D = 0`. -/
theorem ae_eq_zero_of_respInd_arm_mul [IsFiniteMeasure μ] (hW : Measurable W)
    (hA : Measurable A) (hps : IsPropensityScore μ A W e) (a : Bool) {D : Ω → ℝ}
    (hD : StronglyMeasurable[MeasurableSpace.comap W inferInstance] D)
    (h0 : (fun ω => respInd (arm A a) ω * D ω) =ᵐ[μ] 0) :
    ∀ᵐ ω ∂μ, 0 < armProb e a (W ω) → D ω = 0 := by
  have hint : Integrable (fun ω => respInd (arm A a) ω * D ω) μ :=
    (integrable_zero Ω ℝ μ).congr h0.symm
  have c1 := condExp_mul_of_stronglyMeasurable_right hD hint
    (integrable_respInd (μ := μ) (measurable_arm hA a))
  have c2 := condExp_congr_ae (m := MeasurableSpace.comap W inferInstance) h0
  rw [condExp_zero] at c2
  filter_upwards [c1, c2, hps.condExp_arm hW hA a] with ω h1 h2 h3 hpos
  have h4 : armProb e a (W ω) * D ω = 0 := by
    rw [← h3]
    exact (h1.symm.trans h2 :)
  exact (mul_eq_zero.1 h4).resolve_left hpos.ne'

/-- On the arm `{A = a}` an observed regression at `a` is the conditional expectation of `Y(a)`
given `(W, A)`: `1{A = a} m(a, W) = 1{A = a} E[Y(a) | W, A]` almost everywhere. -/
theorem IsOutcomeRegression.respInd_arm_mul_ae_eq [IsFiniteMeasure μ] (hA : Measurable A)
    (hYo : Integrable (obsOutcome A Y) μ) (a : Bool) (hYa : Integrable (Y a) μ)
    (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m) :
    (fun ω => respInd (arm A a) ω * m a (W ω)) =ᵐ[μ] fun ω => respInd (arm A a) ω *
      μ[Y a | MeasurableSpace.comap (fun ω => (W ω, A ω)) inferInstance] ω := by
  have hbm : Measurable (respInd (arm A a)) := measurable_respInd (measurable_arm hA a)
  have hb : StronglyMeasurable[MeasurableSpace.comap (fun ω => (W ω, A ω)) inferInstance]
      (respInd (arm A a)) := (measurable_respInd_arm_comap W A a).stronglyMeasurable
  have hbd : ∀ᵐ ω ∂μ, ‖respInd (arm A a) ω‖ ≤ 1 := Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (respInd_nonneg _ ω)]; exact respInd_le_one _ ω
  have c1 := condExp_mul_of_stronglyMeasurable_left hb
    (hYo.bdd_mul hbm.aestronglyMeasurable hbd) hYo
  have c2 := condExp_mul_of_stronglyMeasurable_left hb
    (hYa.bdd_mul hbm.aestronglyMeasurable hbd) hYa
  have heq : respInd (arm A a) * obsOutcome A Y = respInd (arm A a) * Y a :=
    funext fun ω => respInd_arm_mul_obsOutcome A Y a ω
  filter_upwards [c1, c2, hreg.2] with ω h1 h2 h3
  rw [← respInd_arm_mul_apply A m a ω (W ω), ← h3, ← Pi.mul_apply, ← h1, heq, h2,
    Pi.mul_apply]

/-- **The outcome swap at almost every unit.** Let `r(A, W)` be a version of the observed
regression `E[Y | W, A]` and `v(A, W)` a version of the potential outcome regression
`E[Y(a) | W, A]`, with `Y` and `Y(a)` integrable, and `e(W)` a version of the propensity score.
Then `r(a, W) = v(a, W)` at almost every unit with `P(A = a | W) > 0`. No ignorability is
assumed. -/
theorem IsOutcomeRegression.ae_eq_of_pos [IsFiniteMeasure μ] (hW : Measurable W)
    (hA : Measurable A) (hYo : Integrable (obsOutcome A Y) μ) (a : Bool)
    (hYa : Integrable (Y a) μ) {r v : Bool → 𝒲 → ℝ}
    (hr : IsOutcomeRegression μ A W (obsOutcome A Y) r) (hv : IsOutcomeRegression μ A W (Y a) v)
    (hps : IsPropensityScore μ A W e) :
    ∀ᵐ ω ∂μ, 0 < armProb e a (W ω) → r a (W ω) = v a (W ω) := by
  have hD : StronglyMeasurable[MeasurableSpace.comap W inferInstance]
      (fun ω => r a (W ω) - v a (W ω)) :=
    (((hr.1 a).comp (comap_measurable W)).sub
      ((hv.1 a).comp (comap_measurable W))).stronglyMeasurable
  have h0 : (fun ω => respInd (arm A a) ω * (r a (W ω) - v a (W ω))) =ᵐ[μ] 0 := by
    filter_upwards [hr.respInd_arm_mul_ae_eq hA hYo a hYa, hv.2] with ω h1 h2
    rw [Pi.zero_apply, mul_sub, h1, h2, respInd_arm_mul_apply A v a ω (W ω), sub_self]
  filter_upwards [ae_eq_zero_of_respInd_arm_mul hW hA hps a hD h0] with ω h hpos
  exact sub_eq_zero.1 (h hpos)

/-- **The outcome swap as functions of the covariates.** Under the hypotheses of
`IsOutcomeRegression.ae_eq_of_pos`, `r(a, w) = v(a, w)` for almost every `w` under the law of
`W` at which `P(A = a | W = w) = π_a(w) > 0`. -/
theorem IsOutcomeRegression.ae_map_eq_of_pos [IsFiniteMeasure μ] (hW : Measurable W)
    (hA : Measurable A) (hYo : Integrable (obsOutcome A Y) μ) (a : Bool)
    (hYa : Integrable (Y a) μ) {r v : Bool → 𝒲 → ℝ}
    (hr : IsOutcomeRegression μ A W (obsOutcome A Y) r) (hv : IsOutcomeRegression μ A W (Y a) v)
    (hps : IsPropensityScore μ A W e) :
    ∀ᵐ w ∂(μ.map W), 0 < armProb e a w → r a w = v a w := by
  have hS : MeasurableSet {w | 0 < armProb e a w → r a w = v a w} := by
    have := (measurableSet_lt (measurable_const (a := (0 : ℝ)))
      (measurable_armProb hps.1 a)).compl.union
      (measurableSet_eq_fun (hr.1 a) (hv.1 a))
    convert this using 1
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff]
    tauto
  exact (ae_map_iff hW.aemeasurable hS).2 (hr.ae_eq_of_pos hW hA hYo a hYa hv hps)

/-- **The observed regression is the potential outcome regression on the positivity set.**
Under mean ignorability for the arm `a`, with `Y` and `Y(a)` integrable, the observed regression
at `a` is a version of `E[Y(a) | W]` at almost every unit with `P(A = a | W) > 0`. With
positivity almost everywhere this is `IsOutcomeRegression.ae_eq_condExp`. -/
theorem IsOutcomeRegression.ae_eq_condExp_of_pos [IsFiniteMeasure μ] (hW : Measurable W)
    (hA : Measurable A) (hYo : Integrable (obsOutcome A Y) μ) (a : Bool)
    (hYa : Integrable (Y a) μ) (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m)
    (hps : IsPropensityScore μ A W e) (hmi : MeanIgnorable μ A W Y a) :
    ∀ᵐ ω ∂μ, 0 < armProb e a (W ω) →
      m a (W ω) = μ[Y a | MeasurableSpace.comap W inferInstance] ω := by
  have hD : StronglyMeasurable[MeasurableSpace.comap W inferInstance]
      (fun ω => m a (W ω) - μ[Y a | MeasurableSpace.comap W inferInstance] ω) :=
    (((hreg.1 a).comp (comap_measurable W)).sub
      stronglyMeasurable_condExp.measurable).stronglyMeasurable
  have h0 : (fun ω => respInd (arm A a) ω *
      (m a (W ω) - μ[Y a | MeasurableSpace.comap W inferInstance] ω)) =ᵐ[μ] 0 := by
    filter_upwards [hreg.respInd_arm_mul_ae_eq hA hYo a hYa, hmi] with ω h1 h2
    rw [Pi.zero_apply, mul_sub, h1, h2, sub_self]
  filter_upwards [ae_eq_zero_of_respInd_arm_mul hW hA hps a hD h0] with ω h hpos
  exact sub_eq_zero.1 (h hpos)

end PointTreatment

end CausalInference
