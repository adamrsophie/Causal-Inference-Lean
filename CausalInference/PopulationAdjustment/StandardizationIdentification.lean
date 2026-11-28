/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.StandardizationEstimand
public import CausalInference.IndirectComparison.Constancy

/-!
# Identification by standardizing an outcome model

A source population `P` (the trial with individual data) and a target population `Q`, both with
covariates in `𝒳`. A **correct outcome model** for arm `t` in the source is a conditional mean
function `f` of `Y(t)` in `P` (`P.IsCondMean t f`). **Absolute constancy** of arm `t` is
`StructurallyInvariant`: one function is a conditional mean of `Y(t)` in both populations.
**Overlap** is `Q_X ≪ P_X`.

* **Transport of the surface** (`Population.IsCondMean.of_structurallyInvariant`): under absolute
  constancy and overlap a correct source surface is a conditional mean function in the target.
  The overlap carries the source almost sure equality of two versions to the target.
* **Arm identification** (`integral_covLaw_eq_armMean_of_structurallyInvariant`): the target
  mean of `Y(t)` is the standardized source surface `∫ f dQ_X`. With a correct model of the
  target itself no source and no overlap is needed: that is `Population.IsCondMean.integral_eq`.
* **Target effects.** On every scale the target marginal effect is the marginal estimand of the
  source surfaces under `Q_X`, also when the two arms come from two sources
  (`marginalEffect_eq_linkMarginal_of_structurallyInvariant`, the unanchored comparison
  `UnanchoredSetting.marginalEffect_target_eq`, and the form with the second arm observed in the
  target, `marginalEffect_eq_sub_linkPosition`). In the anchored comparison the effect of `b`
  against the common comparator `c` is read in the target
  (`marginalEffect_anchored_of_structurallyInvariant`). Under conditional constancy of the
  relative effect alone (`RelativeConstancy`) only the average conditional effect is identified
  (`linkConditional_anchored_of_relativeConstancy`); the marginal effect is not
  (`relativeConstancy_not_marginal_example`).
* **Standardization and weighting agree** (`integral_covLaw_eq_integral_densityRatio_mul`):
  for a correct source surface, overlap, and an integrable weighted outcome `w(X) Y(t)` with
  `w = Transport.densityRatio`, the standardized surface is integrable under `Q_X` and
  `∫ f dQ_X = E_P[w(X) f(X)] = E_P[w(X) Y(t)]`, with no constancy assumption. Under absolute
  constancy all three are the target mean (`armMean_eq_integral_densityRatio_mul`).
* **The surface from the observed trial regression** (`Trial.isCondMean_of_isOutcomeRegression`):
  in a trial with treatments `Bool`, a version of the observed regression `E[Y | X, A]` is a
  correct outcome model of each arm under mean ignorability and positivity of the arm.

## Main results

* `Population.IsCondMean.of_structurallyInvariant`,
  `integral_covLaw_eq_armMean_of_structurallyInvariant`.
* `marginalEffect_eq_linkMarginal_of_structurallyInvariant`,
  `UnanchoredSetting.marginalEffect_target_eq`, `marginalEffect_eq_sub_linkPosition`,
  `marginalEffect_anchored_of_structurallyInvariant`,
  `linkConditional_anchored_of_relativeConstancy`.
* `integral_covLaw_eq_integral_densityRatio_mul`, `armMean_eq_integral_densityRatio_mul`,
  `marginalEffect_eq_densityRatio_weighting`.
* `Trial.isCondMean_of_isOutcomeRegression`, `Trial.marginalEffect_eq_of_isOutcomeRegression`.

## References

* J. J. Caro and K. J. Ishak, *No head-to-head trial? Simulate the missing arms*,
  PharmacoEconomics 28 (2010).
* D. M. Phillippo, A. E. Ades, S. Dias, S. Palmer, K. R. Abrams and N. J. Welton, *Methods for
  population-adjusted indirect comparisons in health technology appraisal*, Medical Decision
  Making 38 (2018).
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open MeasureTheory ProbabilityTheory EffectMeasure IndirectComparison Transport

variable {Ω₁ Ω₂ 𝒳 ι : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace 𝒳]
  {P : Population Ω₁ 𝒳 ι} {Q : Population Ω₂ 𝒳 ι}

/-! ### Transport of a correct surface and arm identification -/

/-- **A correct source surface is a correct target surface** under absolute constancy of the arm
and overlap. If `f` is a conditional mean function of `Y(t)` in `P`, some function is a
conditional mean of `Y(t)` in both populations, and `Q_X ≪ P_X`, then `f` is a conditional mean
function of `Y(t)` in `Q`. -/
theorem _root_.CausalInference.IndirectComparison.Population.IsCondMean.of_structurallyInvariant
    {t : ι} {f : 𝒳 → ℝ} (hX₁ : Measurable P.X) (hX₂ : Measurable Q.X)
    (hf : P.IsCondMean t f) (hsi : StructurallyInvariant P.μ P.X (P.Y t) Q.μ Q.X (Q.Y t))
    (hov : Q.covLaw ≪ P.covLaw) : Q.IsCondMean t f := by
  obtain ⟨g, hg⟩ := hsi
  rw [Population.isCommonRegression_iff] at hg
  have h1 : ∀ᵐ x ∂Q.covLaw, f x = g x := hov.ae_le (hf.ae_eq hX₁ hg.1)
  have h2 : (fun ω => f (Q.X ω)) =ᵐ[Q.μ] fun ω => g (Q.X ω) :=
    ae_of_ae_map hX₂.aemeasurable h1
  exact ⟨hf.1, h2.trans hg.2.2⟩

/-- **Arm identification by a standardized source surface.** For a correct outcome model `f` of
`Y(t)` in the source, absolute constancy of the arm, overlap `Q_X ≪ P_X`, and integrable
potential outcomes, the target mean of `Y(t)` is `∫ f dQ_X`, and `f` is integrable under
`Q_X`. -/
theorem integral_covLaw_eq_armMean_of_structurallyInvariant [IsFiniteMeasure Q.μ] {t : ι}
    {f : 𝒳 → ℝ} (hX₁ : Measurable P.X) (hX₂ : Measurable Q.X) (_hYP : Integrable (P.Y t) P.μ)
    (hYQ : Integrable (Q.Y t) Q.μ) (hf : P.IsCondMean t f)
    (hsi : StructurallyInvariant P.μ P.X (P.Y t) Q.μ Q.X (Q.Y t)) (hov : Q.covLaw ≪ P.covLaw) :
    Integrable f Q.covLaw ∧ ∫ x, f x ∂Q.covLaw = Q.armMean t := by
  have hQ := hf.of_structurallyInvariant hX₁ hX₂ hsi hov
  exact ⟨hQ.integrable hX₂, hQ.integral_eq hX₂ hYQ⟩

/-! ### Target effects -/

/-- **The target marginal effect from correct source surfaces**, on every scale. Arm `a` is
modeled in the source `P` and arm `b` in the source `P'` (possibly `P' = P`); each surface is a
correct outcome model there, each arm has absolute constancy from its source to the target, and
`Q_X` is absolutely continuous with respect to both source covariate laws. Then the target
marginal effect of `b` relative to `a` is the marginal estimand of the two surfaces under
`Q_X`. -/
theorem marginalEffect_eq_linkMarginal_of_structurallyInvariant {Ω₃ : Type*}
    [MeasurableSpace Ω₃] {P' : Population Ω₃ 𝒳 ι} [IsFiniteMeasure Q.μ] (g : ℝ → ℝ) {a b : ι}
    {ma mb : 𝒳 → ℝ} (hX₁ : Measurable P.X) (hX₃ : Measurable P'.X) (hX₂ : Measurable Q.X)
    (_hYa : Integrable (P.Y a) P.μ) (_hYb : Integrable (P'.Y b) P'.μ)
    (hYQa : Integrable (Q.Y a) Q.μ) (hYQb : Integrable (Q.Y b) Q.μ) (ha : P.IsCondMean a ma)
    (hb : P'.IsCondMean b mb) (hsa : StructurallyInvariant P.μ P.X (P.Y a) Q.μ Q.X (Q.Y a))
    (hsb : StructurallyInvariant P'.μ P'.X (P'.Y b) Q.μ Q.X (Q.Y b))
    (hova : Q.covLaw ≪ P.covLaw) (hovb : Q.covLaw ≪ P'.covLaw) :
    Q.marginalEffect g a b = linkMarginal g Q.covLaw ma mb :=
  Q.marginalEffect_eq_linkMarginal g hX₂ hYQa hYQb (ha.of_structurallyInvariant hX₁ hX₂ hsa hova)
    (hb.of_structurallyInvariant hX₃ hX₂ hsb hovb)

/-- **The unanchored comparison by outcome models.** In the unanchored setting, with a correct
outcome model of arm `a` in its source and of arm `b` in its source, absolute constancy of each
arm from its source to the target and overlap of the target with both sources, the target
marginal effect of `b` relative to `a` on the scale `g` is the marginal estimand of the two
surfaces under the target covariate law. -/
theorem _root_.CausalInference.IndirectComparison.UnanchoredSetting.marginalEffect_target_eq
    {Ω₃ : Type*} [MeasurableSpace Ω₃] (S : UnanchoredSetting Ω₁ Ω₂ Ω₃ 𝒳 ι)
    [IsFiniteMeasure S.target.μ] (g : ℝ → ℝ) {ma mb : 𝒳 → ℝ} (hXa : Measurable S.sourceA.X)
    (hXb : Measurable S.sourceB.X) (hXt : Measurable S.target.X)
    (hYa : Integrable (S.sourceA.Y S.a) S.sourceA.μ)
    (hYb : Integrable (S.sourceB.Y S.b) S.sourceB.μ)
    (hYta : Integrable (S.target.Y S.a) S.target.μ)
    (hYtb : Integrable (S.target.Y S.b) S.target.μ) (ha : S.sourceA.IsCondMean S.a ma)
    (hb : S.sourceB.IsCondMean S.b mb)
    (hsa : StructurallyInvariant S.sourceA.μ S.sourceA.X (S.sourceA.Y S.a) S.target.μ
      S.target.X (S.target.Y S.a))
    (hsb : StructurallyInvariant S.sourceB.μ S.sourceB.X (S.sourceB.Y S.b) S.target.μ
      S.target.X (S.target.Y S.b))
    (hova : S.target.covLaw ≪ S.sourceA.covLaw) (hovb : S.target.covLaw ≪ S.sourceB.covLaw) :
    S.target.marginalEffect g S.a S.b = linkMarginal g S.target.covLaw ma mb :=
  marginalEffect_eq_linkMarginal_of_structurallyInvariant g hXa hXb hXt hYa hYb hYta hYtb ha hb
    hsa hsb hova hovb

/-- **The unanchored comparison with the second arm observed in the target.** If arm `a` is
modeled in the source with absolute constancy and overlap, the target marginal effect of `b`
relative to `a` is `g(E_Q[Y(b)]) - g(∫ m_a dQ_X)`. -/
theorem marginalEffect_eq_sub_linkPosition [IsFiniteMeasure Q.μ] (g : ℝ → ℝ) {a b : ι}
    {ma : 𝒳 → ℝ} (hX₁ : Measurable P.X) (hX₂ : Measurable Q.X) (hYa : Integrable (P.Y a) P.μ)
    (hYQa : Integrable (Q.Y a) Q.μ) (ha : P.IsCondMean a ma)
    (hsa : StructurallyInvariant P.μ P.X (P.Y a) Q.μ Q.X (Q.Y a)) (hov : Q.covLaw ≪ P.covLaw) :
    Q.marginalEffect g a b = g (Q.armMean b) - linkPosition g Q.covLaw ma := by
  rw [Population.marginalEffect, linkPosition,
    (integral_covLaw_eq_armMean_of_structurallyInvariant hX₁ hX₂ hYa hYQa ha hsa hov).2]

/-- **The anchored comparison by outcome models.** The source `P` compares `a` with the common
comparator `c` and gives correct outcome models `m_a`, `m_c` of both arms; both arms have
absolute constancy from `P` to the target `Q`, and `Q_X ≪ P_X`. Then the target marginal effect
of `b` relative to `a` is the marginal estimand of `c` relative to `a` from the standardized
surfaces, minus the effect of `c` relative to `b` in the target:
`d_ab(Q) = linkMarginal g Q_X m_a m_c - d_bc(Q)`. -/
theorem marginalEffect_anchored_of_structurallyInvariant [IsFiniteMeasure Q.μ] (g : ℝ → ℝ)
    {a b c : ι} {ma mc : 𝒳 → ℝ} (hX₁ : Measurable P.X) (hX₂ : Measurable Q.X)
    (hYa : Integrable (P.Y a) P.μ) (hYc : Integrable (P.Y c) P.μ)
    (hYQa : Integrable (Q.Y a) Q.μ) (hYQc : Integrable (Q.Y c) Q.μ) (ha : P.IsCondMean a ma)
    (hc : P.IsCondMean c mc) (hsa : StructurallyInvariant P.μ P.X (P.Y a) Q.μ Q.X (Q.Y a))
    (hsc : StructurallyInvariant P.μ P.X (P.Y c) Q.μ Q.X (Q.Y c)) (hov : Q.covLaw ≪ P.covLaw) :
    Q.marginalEffect g a b = linkMarginal g Q.covLaw ma mc - Q.marginalEffect g b c := by
  rw [Q.marginalEffect_eq_sub a b c,
    marginalEffect_eq_linkMarginal_of_structurallyInvariant g hX₁ hX₁ hX₂ hYa hYc hYQa hYQc ha hc
      hsa hsc hov hov]

/-- **The anchored average conditional effect under conditional constancy.** The source `P`
gives correct outcome models `m_a`, `m_c` of `a` and the common comparator `c`; the relative
effect of `c` against `a` is conditionally constant from `P` to the target `Q` on the measurable
scale `g`; `Q_X ≪ P_X`; `m'_a` and `m'_c` are conditional mean functions in the target, `m'_b`
is any function (in the application, the target conditional mean of `b`), and the conditional
effects of `c` against `a` and against `b` are integrable under `Q_X`. Then the target average
conditional effect of `b` relative to `a` is the anchored estimand: the source conditional
effect of `c` against `a` averaged over `Q_X`, minus the target average conditional effect of
`c` against `b`. -/
theorem linkConditional_anchored_of_relativeConstancy [IsFiniteMeasure P.μ]
    [IsFiniteMeasure Q.μ] {g : ℝ → ℝ} (hg : Measurable g) {a c : ι}
    {ma mc ma' mb' mc' : 𝒳 → ℝ} (hX₁ : Measurable P.X) (hX₂ : Measurable Q.X)
    (hcc : RelativeConstancy g P Q a c) (hov : Q.covLaw ≪ P.covLaw) (ha : P.IsCondMean a ma)
    (hc : P.IsCondMean c mc) (ha' : Q.IsCondMean a ma') (hc' : Q.IsCondMean c mc')
    (hac : Integrable (linkContrast g ma' mc') Q.covLaw)
    (hbc : Integrable (linkContrast g mb' mc') Q.covLaw) :
    linkConditional g Q.covLaw ma' mb' =
      anchoredEstimand Q.covLaw (linkContrast g ma mc) (linkContrast g mb' mc') := by
  rw [linkConditional_eq_sub hac hbc, anchoredEstimand,
    (linkConditional_eq_of_relativeConstancy hg hcc hX₁ hX₂ hov ha hc ha' hc').1]
  rfl

/-! ### Standardization and density ratio weighting -/

/-- **Standardizing a correct surface is weighting by the density ratio.** Let `f` be a
conditional mean function of an integrable `Y(t)` in the source, `Q_X ≪ P_X`, and let the
weighted outcome `w(X) Y(t)` be integrable in the source, where `w` is the density ratio of the
covariate laws. Then `f` is integrable under `Q_X` and
`∫ f dQ_X = E_P[w(X) f(X)] = E_P[w(X) Y(t)]`. No constancy assumption is involved: both sides
are functionals of the source and of `Q_X`. -/
theorem integral_covLaw_eq_integral_densityRatio_mul [IsFiniteMeasure P.μ]
    [IsFiniteMeasure Q.μ] {t : ι} {f : 𝒳 → ℝ} (hX₁ : Measurable P.X)
    (hov : Q.covLaw ≪ P.covLaw) (hY : Integrable (P.Y t) P.μ) (hf : P.IsCondMean t f)
    (hwY : Integrable (fun ω => densityRatio P.μ P.X Q.μ Q.X (P.X ω) * P.Y t ω) P.μ) :
    Integrable f Q.covLaw ∧
      ∫ x, f x ∂Q.covLaw = ∫ ω, densityRatio P.μ P.X Q.μ Q.X (P.X ω) * f (P.X ω) ∂P.μ ∧
      ∫ x, f x ∂Q.covLaw = ∫ ω, densityRatio P.μ P.X Q.μ Q.X (P.X ω) * P.Y t ω ∂P.μ := by
  set w := densityRatio P.μ P.X Q.μ Q.X
  have hwm : StronglyMeasurable[MeasurableSpace.comap P.X inferInstance]
      (fun ω => w (P.X ω)) :=
    ((measurable_densityRatio P.μ P.X Q.μ Q.X).comp (comap_measurable P.X)).stronglyMeasurable
  have hpull := condExp_mul_of_stronglyMeasurable_left hwm hwY hY
  have hint : Integrable (fun ω => w (P.X ω) * f (P.X ω)) P.μ := by
    refine (integrable_condExp (m := MeasurableSpace.comap P.X inferInstance) (μ := P.μ)
      (f := fun ω => w (P.X ω) * P.Y t ω)).congr ?_
    filter_upwards [hpull, hf.2] with ω h1 h2
    refine h1.trans ?_
    rw [Pi.mul_apply, ← h2]
  have e2 := integral_densityRatio_mul (μ₂ := Q.μ) (X₂ := Q.X) hX₁ hov hf.1
  have e3 := integral_densityRatio_mul_common (μ₂ := Q.μ) (X₂ := Q.X) hX₁ hY hf.2 hwY
  exact ⟨(integrable_densityRatio_mul_iff hX₁ hov hf.1).1 hint, e2, e2.trans e3⟩

/-- **Standardization, weighting and the target mean agree under absolute constancy.** Under the
hypotheses of `integral_covLaw_eq_integral_densityRatio_mul`, absolute constancy of the arm and an
integrable target potential outcome, the target mean of `Y(t)` is
`∫ f dQ_X = E_P[w(X) Y(t)]`. -/
theorem armMean_eq_integral_densityRatio_mul [IsFiniteMeasure P.μ] [IsFiniteMeasure Q.μ]
    {t : ι} {f : 𝒳 → ℝ} (hX₁ : Measurable P.X) (hX₂ : Measurable Q.X)
    (hov : Q.covLaw ≪ P.covLaw) (hY : Integrable (P.Y t) P.μ) (hYQ : Integrable (Q.Y t) Q.μ)
    (hf : P.IsCondMean t f) (hsi : StructurallyInvariant P.μ P.X (P.Y t) Q.μ Q.X (Q.Y t))
    (hwY : Integrable (fun ω => densityRatio P.μ P.X Q.μ Q.X (P.X ω) * P.Y t ω) P.μ) :
    Q.armMean t = ∫ x, f x ∂Q.covLaw ∧
      Q.armMean t = ∫ ω, densityRatio P.μ P.X Q.μ Q.X (P.X ω) * P.Y t ω ∂P.μ := by
  have h := (integral_covLaw_eq_armMean_of_structurallyInvariant hX₁ hX₂ hY hYQ hf hsi hov).2
  exact ⟨h.symm, h.symm.trans (integral_covLaw_eq_integral_densityRatio_mul hX₁ hov hY hf hwY).2.2⟩

/-- **The target marginal effect by density ratio weighting of the source outcomes**: under the
hypotheses of `armMean_eq_integral_densityRatio_mul` for both arms,
`d_ab(Q) = g(E_P[w(X) Y(b)]) - g(E_P[w(X) Y(a)])`, and it is the marginal estimand of the
standardized surfaces. -/
theorem marginalEffect_eq_densityRatio_weighting [IsFiniteMeasure P.μ] [IsFiniteMeasure Q.μ]
    (g : ℝ → ℝ) {a b : ι} {ma mb : 𝒳 → ℝ} (hX₁ : Measurable P.X) (hX₂ : Measurable Q.X)
    (hov : Q.covLaw ≪ P.covLaw) (hYa : Integrable (P.Y a) P.μ) (hYb : Integrable (P.Y b) P.μ)
    (hYQa : Integrable (Q.Y a) Q.μ) (hYQb : Integrable (Q.Y b) Q.μ) (ha : P.IsCondMean a ma)
    (hb : P.IsCondMean b mb) (hsa : StructurallyInvariant P.μ P.X (P.Y a) Q.μ Q.X (Q.Y a))
    (hsb : StructurallyInvariant P.μ P.X (P.Y b) Q.μ Q.X (Q.Y b))
    (hwa : Integrable (fun ω => densityRatio P.μ P.X Q.μ Q.X (P.X ω) * P.Y a ω) P.μ)
    (hwb : Integrable (fun ω => densityRatio P.μ P.X Q.μ Q.X (P.X ω) * P.Y b ω) P.μ) :
    Q.marginalEffect g a b = linkMarginal g Q.covLaw ma mb ∧
      Q.marginalEffect g a b =
        g (∫ ω, densityRatio P.μ P.X Q.μ Q.X (P.X ω) * P.Y b ω ∂P.μ) -
          g (∫ ω, densityRatio P.μ P.X Q.μ Q.X (P.X ω) * P.Y a ω ∂P.μ) := by
  obtain ⟨ea, ea'⟩ := armMean_eq_integral_densityRatio_mul hX₁ hX₂ hov hYa hYQa ha hsa hwa
  obtain ⟨eb, eb'⟩ := armMean_eq_integral_densityRatio_mul hX₁ hX₂ hov hYb hYQb hb hsb hwb
  exact ⟨by rw [Population.marginalEffect, ea, eb]; rfl,
    by rw [Population.marginalEffect, ea', eb']⟩

/-! ### The surface from the observed regression of a trial -/

section Trial

open PointTreatment

variable {Ω 𝒳' : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳'] {T : Trial Ω 𝒳' Bool}

/-- **The observed trial regression is a correct outcome model.** In a trial with treatments
`Bool`, let `m(A, X)` be a version of the observed regression `E[Y | X, A]` and `e(X)` the
propensity score; if the potential outcomes are integrable, arm `t` is mean ignorable given `X`
and has positive probability given almost every `X`, then `m t` is a conditional mean function
of `Y(t)` in the trial population. A randomized trial satisfies mean ignorability
(`PointTreatment.ignorable_of_indepFun`). -/
theorem _root_.CausalInference.IndirectComparison.Trial.isCondMean_of_isOutcomeRegression
    [IsFiniteMeasure T.μ] (hX : Measurable T.X) (hA : Measurable T.A)
    (hYi : ∀ t, Integrable (T.Y t) T.μ) {m : Bool → 𝒳' → ℝ} {e : 𝒳' → ℝ}
    (hreg : IsOutcomeRegression T.μ T.A T.X T.obsOutcome m)
    (hps : IsPropensityScore T.μ T.A T.X e) (t : Bool) (hmi : MeanIgnorable T.μ T.A T.X T.Y t)
    (hpos : ∀ᵐ ω ∂T.μ, 0 < armProb e t (T.X ω)) : T.toPopulation.IsCondMean t (m t) :=
  ⟨hreg.1 t, hreg.ae_eq_condExp hX hA hYi hps t hmi hpos⟩

/-- **The target effect from the observed trial regression.** In a trial with treatments `Bool`
and a target `Q`, if `m` is a version of the observed trial regression, both arms are mean
ignorable and positive, the potential outcomes are integrable in both populations, both arms
have absolute constancy from the trial to `Q`, and `Q_X ≪ T_X`, then on every scale the target
marginal effect of `true` relative to `false` is the marginal estimand
`linkMarginal g Q_X (m false) (m true)` of the fitted regression. -/
theorem _root_.CausalInference.IndirectComparison.Trial.marginalEffect_eq_of_isOutcomeRegression
    [IsFiniteMeasure T.μ] {Ω₂' : Type*} [MeasurableSpace Ω₂'] {Q' : Population Ω₂' 𝒳' Bool}
    [IsFiniteMeasure Q'.μ] (g : ℝ → ℝ) (hX : Measurable T.X) (hA : Measurable T.A)
    (hX₂ : Measurable Q'.X) (hYi : ∀ t, Integrable (T.Y t) T.μ)
    (hYQ : ∀ t, Integrable (Q'.Y t) Q'.μ) {m : Bool → 𝒳' → ℝ} {e : 𝒳' → ℝ}
    (hreg : IsOutcomeRegression T.μ T.A T.X T.obsOutcome m)
    (hps : IsPropensityScore T.μ T.A T.X e) (hmi : ∀ t, MeanIgnorable T.μ T.A T.X T.Y t)
    (hpos : ∀ t, ∀ᵐ ω ∂T.μ, 0 < armProb e t (T.X ω))
    (hsi : ∀ t, StructurallyInvariant T.μ T.X (T.Y t) Q'.μ Q'.X (Q'.Y t))
    (hov : Q'.covLaw ≪ T.covLaw) :
    Q'.marginalEffect g false true = linkMarginal g Q'.covLaw (m false) (m true) :=
  marginalEffect_eq_linkMarginal_of_structurallyInvariant (P := T.toPopulation)
    (P' := T.toPopulation) g hX hX hX₂ (hYi false) (hYi true) (hYQ false) (hYQ true)
    (T.isCondMean_of_isOutcomeRegression hX hA hYi hreg hps false (hmi false) (hpos false))
    (T.isCondMean_of_isOutcomeRegression hX hA hYi hreg hps true (hmi true) (hpos true))
    (hsi false) (hsi true) hov hov

end Trial

end PopulationAdjustment

end CausalInference
