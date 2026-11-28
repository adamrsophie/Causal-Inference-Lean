/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedContrast
public import CausalInference.Transport.Formula
public import CausalInference.Transport.Identification
public import Mathlib.Analysis.SpecialFunctions.Sigmoid

/-!
# Population adjustment: the density ratio interpretation of the tilting weights

In the population, reweighting the trial (the source of a `Transport.TransportModel`) to the
target is reweighting by the density ratio `w = dP*_X / dP_X` (`Transport.densityRatio`). The
exponential tilting weights are this density ratio exactly when the log density ratio is affine
in the features.

* **Log linear density ratio.** Suppose the target covariate law has density
  `exp(α + βᵀ(φ(x) - c))` with respect to the trial covariate law. Then the target law is
  absolutely continuous with respect to the trial law, the density ratio is the tilting weight
  almost everywhere (`densityRatio_ae_eq_tiltWeight`), the target law is the trial law
  exponentially tilted by `βᵀ(φ - c)` (`map_eq_tilted`), and the tilting weights balance the
  features at their target means in the population (`populationBalanced_tiltWeight`). The
  hypothesis is stated as an equality of measures, not as a statement about the logarithm of a
  Radon and Nikodym derivative.
* **The weighted trial arm mean is the target mean.** In a trial randomized with a constant
  probability, under conditional transportability of the arm, every weight function equal almost
  everywhere to a nonzero multiple of the density ratio gives a population weighted arm mean
  equal to the target mean (`lawWeightedArmMean_sourceLaw_eq_targetMean`); for a log linear
  density ratio this holds for the tilting weights with any intercept
  (`lawWeightedArmMean_tiltWeight_eq_targetMean`). The proof uses the transport formula
  `Transport.integral_target_eq_transport`. The weighted contrast is then the target marginal
  contrast, and on the identity scale with common regressions the anchored comparison is
  `anchoredEstimand` (`lawWeightedContrast_eq_targetMean_sub`,
  `lawWeightedContrast_sub_eq_anchoredEstimand`).
* **Logistic trial membership.** Pool the trial (`S = true`) and the target (`S = false`) on one
  probability space. If `P(S = true | X = x) = σ(α̃ + β̃ᵀx)`, then the covariate law of the target
  has density `k exp(-α̃ - β̃ᵀx)` with respect to that of the trial, `k = P(S = 1) / P(S = 0)`:
  the log density ratio is affine with `β = -β̃` (`map_cond_eq_withDensity_tiltWeight`). This is
  the instance of the log linear hypothesis.
* **Inverse odds weights.** The inverse odds `c exp(-α̃ - β̃ᵀx)` of trial membership is a positive
  multiple of the tilting weight with `β = -β̃` (`inverse_odds_eq_mul_tiltWeight`); conversely a
  positive multiple relation forces `β = -β̃`, everywhere (`inverse_odds_proportional_iff`) and
  almost everywhere under a law not carried by a hyperplane (`inverse_odds_proportional_ae_iff`),
  but not under a point mass (`inverse_odds_proportional_ae_counterexample`). The weighted arm
  means with inverse odds weights and with tilting weights coincide
  (`weightedArmMean_inverse_odds`).

## Main results

* `integral_map_eq_integral_tiltWeight_mul`, `densityRatio_ae_eq_tiltWeight`,
  `integral_tiltWeight_eq_one`, `populationBalanced_tiltWeight`, `map_eq_tilted`.
* `lawWeightedArmMean_sourceLaw_eq_targetMean`, `lawWeightedArmMean_tiltWeight_eq_targetMean`,
  `lawWeightedContrast_eq_targetMean_sub`, `lawWeightedContrast_sub_eq_anchoredEstimand`.
* `map_restrict_eq_withDensity_armProb`, `map_cond_eq_withDensity_tiltWeight`.
* `inverse_odds_eq_mul_tiltWeight`, `inverse_odds_proportional_iff`,
  `inverse_odds_proportional_ae_iff`, `inverse_odds_proportional_ae_counterexample`,
  `weightedArmMean_inverse_odds`.

## References

* D. Westreich, J. K. Edwards, C. R. Lesko, E. Stuart and S. R. Cole, *Transportability of
  trial results using inverse odds of sampling weights*, American Journal of Epidemiology 186
  (2017).
* J. E. Signorovitch and coauthors, PharmacoEconomics 28 (2010).
* D. M. Phillippo, A. E. Ades, S. Dias, S. Palmer, K. R. Abrams and N. J. Welton, *Methods for
  population-adjusted indirect comparisons in health technology appraisal*, Medical Decision
  Making 38 (2018).
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open MeasureTheory ProbabilityTheory MissingData PointTreatment Transport IndirectComparison
open scoped ENNReal

/-! ### A log linear density ratio -/

section LogLinear

variable {𝒳 : Type*} [MeasurableSpace 𝒳] {p : ℕ} {φ : 𝒳 → Fin p → ℝ} {c : Fin p → ℝ}
  {α : ℝ} {β : Fin p → ℝ}

omit [MeasurableSpace 𝒳] in
/-- The density `exp(α + βᵀ(φ(x) - c))` as a function with values in `ℝ≥0∞`. -/
theorem ofReal_tiltWeight_eq (x : 𝒳) :
    ENNReal.ofReal (tiltWeight φ c α β x) = ((Real.toNNReal (tiltWeight φ c α β x) : NNReal) :
      ℝ≥0∞) := rfl

/-- **Integrals under a tilted law.** If `ν' = ν.withDensity (exp(α + βᵀ(φ - c)))`, then
`∫ g dν' = ∫ w g dν` for the tilting weight `w`. -/
theorem integral_map_eq_integral_tiltWeight_mul (hφ : Measurable φ) {ν ν' : Measure 𝒳}
    (htilt : ν' = ν.withDensity fun x => ENNReal.ofReal (tiltWeight φ c α β x)) (g : 𝒳 → ℝ) :
    ∫ x, g x ∂ν' = ∫ x, tiltWeight φ c α β x * g x ∂ν := by
  have hm : Measurable fun x => Real.toNNReal (tiltWeight φ c α β x) :=
    (measurable_tiltWeight φ c α β hφ).real_toNNReal
  rw [htilt]
  simp_rw [ofReal_tiltWeight_eq]
  rw [integral_withDensity_eq_integral_smul hm]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [NNReal.smul_def, Real.coe_toNNReal _ (tiltWeight_pos φ c α β x).le]

variable {Ω₁ Ω₂ : Type*} {mΩ₁ : MeasurableSpace Ω₁} {mΩ₂ : MeasurableSpace Ω₂}
  {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} [IsFiniteMeasure μ₁] {X₁ : Ω₁ → 𝒳} {X₂ : Ω₂ → 𝒳}

/-- **A log linear density ratio is the tilting weight.** If the target covariate law has
density `exp(α + βᵀ(φ(x) - c))` with respect to the trial covariate law, then the target law is
absolutely continuous with respect to the trial law and the density ratio equals the tilting
weight almost everywhere under the trial law. -/
theorem densityRatio_ae_eq_tiltWeight (hφ : Measurable φ)
    (htilt : μ₂.map X₂ = (μ₁.map X₁).withDensity fun x => ENNReal.ofReal (tiltWeight φ c α β x)) :
    μ₂.map X₂ ≪ μ₁.map X₁ ∧
      densityRatio μ₁ X₁ μ₂ X₂ =ᵐ[μ₁.map X₁] tiltWeight φ c α β := by
  refine ⟨htilt ▸ withDensity_absolutelyContinuous _ _, ?_⟩
  have hm : Measurable fun x => ENNReal.ofReal (tiltWeight φ c α β x) :=
    (measurable_tiltWeight φ c α β hφ).ennreal_ofReal
  have := Measure.rnDeriv_withDensity (μ₁.map X₁) hm
  rw [← htilt] at this
  filter_upwards [this] with x hx
  rw [densityRatio, hx, ENNReal.toReal_ofReal (tiltWeight_pos φ c α β x).le]

omit [IsFiniteMeasure μ₁] in
/-- **The tilting weights have mean one under the trial law** when the target is a probability
law. -/
theorem integral_tiltWeight_eq_one [IsProbabilityMeasure μ₂] (hφ : Measurable φ)
    (htilt : μ₂.map X₂ = (μ₁.map X₁).withDensity fun x => ENNReal.ofReal (tiltWeight φ c α β x)) :
    ∫ x, tiltWeight φ c α β x ∂(μ₁.map X₁) = 1 := by
  have := integral_map_eq_integral_tiltWeight_mul hφ htilt (fun _ => 1)
  simpa using this.symm

omit [IsFiniteMeasure μ₁] in
/-- **The tilting weights balance the features in the population**: under a log linear density
ratio, if the features are integrable under the target covariate law, the tilting weights
balance them under the trial covariate law at their target means `tⱼ = ∫ φⱼ dP*_X`. -/
theorem populationBalanced_tiltWeight [IsProbabilityMeasure μ₂] (hφ : Measurable φ)
    (htilt : μ₂.map X₂ = (μ₁.map X₁).withDensity fun x => ENNReal.ofReal (tiltWeight φ c α β x))
    (hint : ∀ j, Integrable (fun x => φ x j) (μ₂.map X₂)) :
    PopulationBalanced (μ₁.map X₁) (tiltWeight φ c α β) φ (fun j => ∫ x, φ x j ∂(μ₂.map X₂)) := by
  intro j
  rw [← integral_map_eq_integral_tiltWeight_mul hφ htilt, integral_sub (hint j)
    (integrable_const _), integral_const, probReal_univ, one_smul, sub_self]

omit [IsFiniteMeasure μ₁] in
/-- **The target law is the exponentially tilted trial law**: under a log linear density ratio
(with a probability target), the target covariate law is Mathlib's tilted measure of the trial
covariate law by `βᵀ(φ - c)`; the intercept is determined by the normalization. -/
theorem map_eq_tilted [IsProbabilityMeasure μ₂] (hφ : Measurable φ)
    (htilt : μ₂.map X₂ = (μ₁.map X₁).withDensity fun x => ENNReal.ofReal (tiltWeight φ c α β x)) :
    μ₂.map X₂ = (μ₁.map X₁).tilted fun x => β ⬝ᵥ (φ x - c) := by
  have h1 := integral_tiltWeight_eq_one hφ htilt
  simp_rw [tiltWeight_eq_exp_mul] at h1
  rw [integral_const_mul] at h1
  have hZ : ∫ x, Real.exp (β ⬝ᵥ (φ x - c)) ∂(μ₁.map X₁) = (Real.exp α)⁻¹ := by
    exact eq_inv_of_mul_eq_one_right h1
  rw [htilt, Measure.tilted, hZ]
  congr 1
  funext x
  rw [div_inv_eq_mul, tiltWeight_eq_exp_mul, mul_comm]

end LogLinear

/-! ### The weighted trial arm mean is the target mean -/

section TargetMean

variable {Ω₁ Ω₂ 𝒳 : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace 𝒳]

/-- **The population weighted arm mean is the target mean.** Let the source study of a transport
model be randomized with a constant probability `q ∈ (0, 1)` of `A = true`, and let the arm `a`
be conditionally transportable. Then every measurable weight function equal almost everywhere
(under the trial covariate law) to a nonzero multiple `C` of the density ratio gives
`E₁[w(X₁) 1{A = a} Y] / E₁[w(X₁) 1{A = a}] = E₂[Y₂(a)]`. The numerator is `C q_a E₂[Y₂(a)]` by
the transport formula and the denominator is `C q_a`, the density ratio having mean one. -/
theorem lawWeightedArmMean_sourceLaw_eq_targetMean {M : TransportModel Ω₁ Ω₂ 𝒳} {a : Bool}
    (hM : M.IsConditionallyTransportable a) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hps : IsPropensityScore M.μ₁ M.A M.X₁ fun _ => q) {C : ℝ} (hC : C ≠ 0) {w : 𝒳 → ℝ}
    (hwm : Measurable w)
    (hw : w =ᵐ[M.μ₁.map M.X₁] fun x => C * densityRatio M.μ₁ M.X₁ M.μ₂ M.X₂ x) :
    lawWeightedArmMean M.sourceLaw w a = M.targetMean a := by
  have := hM.isProbabilityMeasure_μ₁
  have := hM.isProbabilityMeasure_μ₂
  have hX₁ := hM.measurable_X₁
  have hX₂ := hM.measurable_X₂
  have hA := hM.measurable_A
  obtain ⟨g, hcom⟩ := hM.structurallyInvariant
  set wd := densityRatio M.μ₁ M.X₁ M.μ₂ M.X₂ with hwd_def
  have hwd := measurable_densityRatio M.μ₁ M.X₁ M.μ₂ M.X₂
  set qa : ℝ := if a then q else 1 - q with hqa_def
  have hqa : ∀ x, armProb (fun _ : 𝒳 => q) a x = qa := fun x => by cases a <;> simp [qa]
  have hqa0 : 0 < qa := by
    cases a
    · simp only [qa, Bool.false_eq_true, ↓reduceIte]; linarith
    · simpa [qa] using hq0
  have hpos : ∀ᵐ ω ∂M.μ₁, 0 < armProb (fun _ : 𝒳 => q) a (M.X₁ ω) :=
    Filter.Eventually.of_forall fun ω => (hqa _).symm ▸ hqa0
  obtain ⟨-, -, -, -, h5⟩ := integral_target_eq_transport a hX₁ hX₂ hA (hM.measurable_Y₁ a)
    hM.integrable_Y₁ hM.integrable_Y₂ hM.marMean hps hpos hcom hM.overlap hM.integrable_weight
  rw [← hwd_def] at h5
  -- the source law integrals as integrals over the source
  have hsrc : Measurable fun ω => (M.X₁ ω, M.A ω, obsOutcome M.A M.Y₁ ω) :=
    hX₁.prodMk (hA.prodMk (measurable_obsOutcome hA hM.measurable_Y₁))
  have hite : Measurable fun z : 𝒳 × Bool × ℝ => if z.2.1 = a then w z.1 else 0 :=
    Measurable.ite ((measurable_fst.comp measurable_snd) (measurableSet_singleton a))
      (hwm.comp measurable_fst) measurable_const
  have hrw : ∀ ω, (if M.A ω = a then w (M.X₁ ω) else 0) = w (M.X₁ ω) * respInd (arm M.A a) ω :=
    fun ω => by rw [respInd_arm_apply]; split_ifs <;> simp
  have hae : ∀ᵐ ω ∂M.μ₁, w (M.X₁ ω) = C * wd (M.X₁ ω) := ae_of_ae_map hX₁.aemeasurable hw
  -- the numerator
  have hnum : ∫ z, (if z.2.1 = a then w z.1 else 0) * z.2.2 ∂M.sourceLaw =
      C * qa * M.targetMean a := by
    rw [TransportModel.sourceLaw, integral_map hsrc.aemeasurable
      (f := fun z : 𝒳 × Bool × ℝ => (if z.2.1 = a then w z.1 else 0) * z.2.2)
      (hite.mul (measurable_snd.comp measurable_snd)).aestronglyMeasurable]
    have h6 : M.targetMean a = qa⁻¹ * ∫ ω, wd (M.X₁ ω) * respInd (arm M.A a) ω *
        obsOutcome M.A M.Y₁ ω ∂M.μ₁ := by
      rw [TransportModel.targetMean, h5, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      simp only [hqa]
      field_simp
    rw [h6, ← mul_assoc, mul_assoc C, mul_inv_cancel₀ hqa0.ne', mul_one, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hae] with ω hω
    simp only [hrw]
    rw [hω]
    ring
  -- the denominator
  have hwI : Integrable (fun ω => wd (M.X₁ ω)) M.μ₁ := by
    have := (integrable_densityRatio_mul_iff hX₁ hM.overlap (g := fun _ => (1 : ℝ))
      measurable_const).2 (integrable_const _)
    simpa using this
  have hw1 : ∫ ω, wd (M.X₁ ω) ∂M.μ₁ = 1 := by
    have := integral_densityRatio_mul hX₁ hM.overlap (g := fun _ => (1 : ℝ)) measurable_const
    simpa using this.symm
  have hwR : Integrable (fun ω => wd (M.X₁ ω) * respInd (arm M.A a) ω) M.μ₁ := by
    refine hwI.mono'
      ((hwd.comp hX₁).mul (measurable_respInd (measurable_arm hA a))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [norm_mul, Real.norm_of_nonneg (densityRatio_nonneg _ _ _ _ _),
      Real.norm_of_nonneg (respInd_nonneg _ _)]
    exact mul_le_of_le_one_right (densityRatio_nonneg _ _ _ _ _) (respInd_le_one _ _)
  have hden0 : ∫ ω, wd (M.X₁ ω) * respInd (arm M.A a) ω ∂M.μ₁ = qa := by
    have hce := hps.condExp_arm hX₁ hA a
    have := integral_densityRatio_mul_common (μ₂ := M.μ₂) (X₂ := M.X₂) (g := fun _ => qa) hX₁
      (integrable_respInd (measurable_arm hA a))
      (Filter.EventuallyEq.trans (Filter.Eventually.of_forall fun ω => (hqa (M.X₁ ω)).symm :
        (fun ω => qa) =ᵐ[M.μ₁] fun ω => armProb (fun _ : 𝒳 => q) a (M.X₁ ω)) hce.symm) hwR
    rw [← this, integral_mul_const, hw1, one_mul]
  have hden : ∫ z, (if z.2.1 = a then w z.1 else 0) ∂M.sourceLaw = C * qa := by
    rw [TransportModel.sourceLaw, integral_map hsrc.aemeasurable
      (f := fun z : 𝒳 × Bool × ℝ => if z.2.1 = a then w z.1 else 0) hite.aestronglyMeasurable,
      ← hden0, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hae] with ω hω
    simp only [hrw]
    rw [hω]
    ring
  rw [lawWeightedArmMean, hnum, hden]
  field_simp

/-- **The weighted contrast is the target contrast**: under the hypotheses of
`lawWeightedArmMean_sourceLaw_eq_targetMean` for both arms, the population weighted estimate of
the effect of `false` relative to `true` on the scale `g` is
`g(E₂[Y₂(false)]) - g(E₂[Y₂(true)])`. -/
theorem lawWeightedContrast_eq_targetMean_sub {M : TransportModel Ω₁ Ω₂ 𝒳}
    (hMt : M.IsConditionallyTransportable true) (hMf : M.IsConditionallyTransportable false)
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hps : IsPropensityScore M.μ₁ M.A M.X₁ fun _ => q)
    {C : ℝ} (hC : C ≠ 0) {w : 𝒳 → ℝ} (hwm : Measurable w)
    (hw : w =ᵐ[M.μ₁.map M.X₁] fun x => C * densityRatio M.μ₁ M.X₁ M.μ₂ M.X₂ x) (g : ℝ → ℝ) :
    lawWeightedContrast g M.sourceLaw w true false =
      g (M.targetMean false) - g (M.targetMean true) := by
  rw [lawWeightedContrast, lawWeightedArmMean_sourceLaw_eq_targetMean hMf hq0 hq1 hps hC hwm hw,
    lawWeightedArmMean_sourceLaw_eq_targetMean hMt hq0 hq1 hps hC hwm hw]

/-- **The anchored weighted comparison identifies the anchored estimand** on the identity scale:
under the hypotheses of `lawWeightedContrast_eq_targetMean_sub`, if `m t` is a common regression
of `Y(t)` in the two populations for both arms, then the population weighted contrast minus the
mean `∫ τ_bc dP*_X` of the effect of the aggregate data trial, standardized to the target, is
`anchoredEstimand P*_X (m false - m true) τ_bc`. -/
theorem lawWeightedContrast_sub_eq_anchoredEstimand {M : TransportModel Ω₁ Ω₂ 𝒳}
    (hMt : M.IsConditionallyTransportable true) (hMf : M.IsConditionallyTransportable false)
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hps : IsPropensityScore M.μ₁ M.A M.X₁ fun _ => q)
    {C : ℝ} (hC : C ≠ 0) {w : 𝒳 → ℝ} (hwm : Measurable w)
    (hw : w =ᵐ[M.μ₁.map M.X₁] fun x => C * densityRatio M.μ₁ M.X₁ M.μ₂ M.X₂ x)
    {m : Bool → 𝒳 → ℝ}
    (hm : ∀ t, IsCommonRegression M.μ₁ M.X₁ (M.Y₁ t) M.μ₂ M.X₂ (M.Y₂ t) (m t))
    (τbc : 𝒳 → ℝ) :
    lawWeightedContrast id M.sourceLaw w true false - ∫ x, τbc x ∂M.targetCovLaw =
      anchoredEstimand M.targetCovLaw (fun x => m false x - m true x) τbc := by
  have := hMt.isProbabilityMeasure_μ₂
  have hX₂ := hMt.measurable_X₂
  have ht := integral_target_eq_integral_common hX₂ hMt.integrable_Y₂ (hm true).1 (hm true).2.2
  have hf := integral_target_eq_integral_common hX₂ hMf.integrable_Y₂ (hm false).1
    (hm false).2.2
  rw [lawWeightedContrast_eq_targetMean_sub hMt hMf hq0 hq1 hps hC hwm hw, anchoredEstimand,
    TransportModel.targetCovLaw, integral_sub hf.1 ht.1, TransportModel.targetMean,
    TransportModel.targetMean, ht.2, hf.2]
  rfl

/-- **The tilting weights give the target mean under a log linear density ratio**: if the target
covariate law has density `exp(α + βᵀ(φ - c))` with respect to the trial covariate law, the
tilting weights with the same `β` and any intercept `α'` give a population weighted arm mean
equal to the target mean, under the hypotheses of `lawWeightedArmMean_sourceLaw_eq_targetMean`
on the trial. -/
theorem lawWeightedArmMean_tiltWeight_eq_targetMean {M : TransportModel Ω₁ Ω₂ 𝒳} {a : Bool}
    (hM : M.IsConditionallyTransportable a) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hps : IsPropensityScore M.μ₁ M.A M.X₁ fun _ => q) {p : ℕ} {φ : 𝒳 → Fin p → ℝ}
    (hφ : Measurable φ) {c : Fin p → ℝ} {α : ℝ} {β : Fin p → ℝ}
    (htilt : M.targetCovLaw =
      (M.μ₁.map M.X₁).withDensity fun x => ENNReal.ofReal (tiltWeight φ c α β x)) (α' : ℝ) :
    lawWeightedArmMean M.sourceLaw (tiltWeight φ c α' β) a = M.targetMean a := by
  have := hM.isProbabilityMeasure_μ₁
  obtain ⟨-, hae⟩ := densityRatio_ae_eq_tiltWeight hφ htilt
  refine lawWeightedArmMean_sourceLaw_eq_targetMean hM hq0 hq1 hps
    (Real.exp_pos (α' - α)).ne' (measurable_tiltWeight φ c α' β hφ) ?_
  filter_upwards [hae] with x hx
  rw [hx, tiltWeight, tiltWeight, ← Real.exp_add]
  ring_nf

end TargetMean

/-! ### Logistic trial membership -/

section Logistic

variable {Ω 𝒳 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒳] {μ : Measure Ω}
  [IsFiniteMeasure μ] {S : Ω → Bool} {X : Ω → 𝒳} {π : 𝒳 → ℝ}

/-- **The covariate law of a population has density the membership probability**: if `π` is the
propensity score of membership `S`, nonnegative, then the covariate law on `{S = s}` has density
`π_s = armProb π s` with respect to the pooled covariate law. -/
theorem map_restrict_eq_withDensity_armProb (hS : Measurable S) (hX : Measurable X)
    (hps : IsPropensityScore μ S X π) (s : Bool) (h0 : ∀ x, 0 ≤ armProb π s x) :
    (μ.restrict (S ⁻¹' {s})).map X =
      (μ.map X).withDensity fun x => ENNReal.ofReal (armProb π s x) := by
  have hπs : Measurable (armProb π s) := measurable_armProb hps.1 s
  have hce := hps.condExp_arm hX hS s
  have hint : Integrable (fun ω => armProb π s (X ω)) μ :=
    integrable_condExp.congr hce
  ext A hA
  rw [Measure.map_apply hX hA, Measure.restrict_apply (hX hA), withDensity_apply _ hA,
    setLIntegral_map hA hπs.ennreal_ofReal hX,
    ← ofReal_integral_eq_lintegral_ofReal hint.integrableOn
      (Filter.Eventually.of_forall fun ω => h0 _)]
  have hset : MeasurableSet[MeasurableSpace.comap X inferInstance] (X ⁻¹' A) := ⟨A, hA, rfl⟩
  have h1 : ∫ ω in X ⁻¹' A, armProb π s (X ω) ∂μ = ∫ ω in X ⁻¹' A, respInd (arm S s) ω ∂μ := by
    rw [← setIntegral_condExp hX.comap_le (integrable_respInd (measurable_arm hS s)) hset]
    exact setIntegral_congr_ae (hX hA) (hce.mono fun ω h _ => h.symm)
  have h2 : ∫ ω in X ⁻¹' A, respInd (arm S s) ω ∂μ = μ.real (X ⁻¹' A ∩ S ⁻¹' {s}) := by
    have hR : (arm S s) ⁻¹' {true} = S ⁻¹' {s} := by
      ext ω; simp [arm]
    rw [respInd, hR, integral_indicator_one (hS (measurableSet_singleton s)), measureReal_def,
      measureReal_def, Measure.restrict_apply (hS (measurableSet_singleton s)), Set.inter_comm]
  rw [h1, h2, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- Under the logistic model the inverse membership odds is an exponential:
`(1 - σ(z)) / σ(z) = exp(-z)`. -/
theorem one_sub_sigmoid_div_sigmoid (z : ℝ) :
    (1 - Real.sigmoid z) / Real.sigmoid z = Real.exp (-z) := by
  have h : 0 < 1 + Real.exp (-z) := by positivity
  rw [Real.sigmoid_def]
  field_simp
  ring

variable {p : ℕ}

/-- **Logistic membership gives a log linear density ratio.** Pool the trial (`S = true`) and the
target (`S = false`) on a probability space, both of positive probability, and let the membership
propensity be logistic, `P(S = true | X = x) = σ(α̃ + β̃ᵀx)`. Then the target covariate law has
density `exp(log k - α̃ + (-β̃)ᵀx)` with respect to the trial covariate law,
`k = P(S = true) / P(S = false)`: the density ratio is the tilting weight with features `x`,
centering `0`, intercept `log k - α̃` and slope `-β̃` (`densityRatio_ae_eq_tiltWeight` then
applies). -/
theorem map_cond_eq_withDensity_tiltWeight [IsProbabilityMeasure μ] {S : Ω → Bool}
    {X : Ω → Fin p → ℝ} {α' : ℝ} {β' : Fin p → ℝ} (hS : Measurable S) (hX : Measurable X)
    (hps : IsPropensityScore μ S X fun x => Real.sigmoid (α' + β' ⬝ᵥ x))
    (h1 : μ (S ⁻¹' {true}) ≠ 0) (h0 : μ (S ⁻¹' {false}) ≠ 0) :
    (μ[|S ⁻¹' {false}]).map X = ((μ[|S ⁻¹' {true}]).map X).withDensity fun x =>
      ENNReal.ofReal (tiltWeight id 0
        (Real.log (μ.real (S ⁻¹' {true}) / μ.real (S ⁻¹' {false})) - α') (-β') x) := by
  set π : (Fin p → ℝ) → ℝ := fun x => Real.sigmoid (α' + β' ⬝ᵥ x) with hπ_def
  set S1 := S ⁻¹' {true}
  set S0 := S ⁻¹' {false}
  have hπm : Measurable π := hps.1
  have hπpos : ∀ x, 0 < π x := fun x => Real.sigmoid_pos _
  have hπlt : ∀ x, π x < 1 := fun x => Real.sigmoid_lt_one _
  have hν1 := map_restrict_eq_withDensity_armProb hS hX hps true fun x => (hπpos x).le
  have hν0 := map_restrict_eq_withDensity_armProb hS hX hps false
    fun x => by simp only [armProb_false]; linarith [hπlt x]
  have hk1 : 0 < μ.real S1 := ENNReal.toReal_pos h1 (measure_ne_top _ _)
  have hk0 : 0 < μ.real S0 := ENNReal.toReal_pos h0 (measure_ne_top _ _)
  set k := μ.real S1 / μ.real S0 with hk
  have hkpos : 0 < k := div_pos hk1 hk0
  -- the tilting weight is `k (1 - π) / π`
  have hw : ∀ x, tiltWeight id 0 (Real.log k - α') (-β') x = k * ((1 - π x) / π x) := by
    intro x
    rw [tiltWeight, one_sub_sigmoid_div_sigmoid, Real.exp_add, Real.exp_sub, Real.exp_log hkpos]
    simp only [id, sub_zero, neg_dotProduct, neg_add]
    rw [Real.exp_add, Real.exp_neg α', div_eq_mul_inv]
    ring
  simp_rw [hw]
  set ρ : (Fin p → ℝ) → ℝ≥0∞ := fun x => ENNReal.ofReal (k * ((1 - π x) / π x))
  have hρm : Measurable ρ :=
    (measurable_const.mul ((measurable_const.sub hπm).div hπm)).ennreal_ofReal
  have hAC : (μ[|S1]).map X = (μ S1)⁻¹ • (μ.map X).withDensity fun x => ENNReal.ofReal (π x) := by
    rw [ProbabilityTheory.cond, Measure.map_smul]
    exacts [congrArg _ hν1, hX.aemeasurable]
  have hBC : (μ[|S0]).map X =
      (μ S0)⁻¹ • (μ.map X).withDensity fun x => ENNReal.ofReal (1 - π x) := by
    rw [ProbabilityTheory.cond, Measure.map_smul]
    exacts [congrArg _ hν0, hX.aemeasurable]
  have hpt : ∀ x, ENNReal.ofReal (π x) * ρ x =
      ENNReal.ofReal k * ENNReal.ofReal (1 - π x) := by
    intro x
    simp only [ρ]
    rw [← ENNReal.ofReal_mul (hπpos x).le, ← ENNReal.ofReal_mul hkpos.le]
    congr 1
    have := (hπpos x).ne'
    field_simp
  have hkE : ENNReal.ofReal k = μ S1 / μ S0 := by
    rw [hk, ENNReal.ofReal_div_of_pos hk0, measureReal_def, measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top _ _), ENNReal.ofReal_toReal (measure_ne_top _ _)]
  ext A hA
  rw [withDensity_apply _ hA, hAC, Measure.restrict_smul, lintegral_smul_measure,
    setLIntegral_withDensity_eq_setLIntegral_mul _ hπm.ennreal_ofReal hρm hA, hBC,
    FunLike.coe_smul, Pi.smul_apply, withDensity_apply _ hA]
  simp only [Pi.mul_apply, hpt, hkE]
  rw [lintegral_const_mul (f := fun x => ENNReal.ofReal (1 - π x)) _
      (measurable_const.sub hπm).ennreal_ofReal, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    ENNReal.div_eq_inv_mul, ← mul_assoc, mul_comm (μ S1)⁻¹, mul_assoc (μ S0)⁻¹,
    ENNReal.inv_mul_cancel h1 (measure_ne_top _ _), mul_one]

end Logistic

/-! ### Inverse odds weights -/

section InverseOdds

variable {p : ℕ}

/-- **The inverse odds weight is a positive multiple of the tilting weight**: for every intercept
`α` and centering `c`, `k exp(-α̃ - β̃ᵀx) = C exp(α + (-β̃)ᵀ(x - c))` with
`C = k exp(-α̃ - α - β̃ᵀc)`, which is positive when `k > 0`. -/
theorem inverse_odds_eq_mul_tiltWeight (k α' α : ℝ) (β' c : Fin p → ℝ) :
    (∀ x : Fin p → ℝ, k * Real.exp (-α' - β' ⬝ᵥ x) =
      k * Real.exp (-α' - α - β' ⬝ᵥ c) * tiltWeight id c α (-β') x) ∧
      (0 < k → 0 < k * Real.exp (-α' - α - β' ⬝ᵥ c)) := by
  refine ⟨fun x => ?_, fun hk => by positivity⟩
  rw [tiltWeight, mul_assoc, ← Real.exp_add]
  congr 2
  simp only [id, dotProduct_sub, neg_dotProduct]
  ring

/-- **Proportionality to the tilting weight exactly when `β = -β̃`**: for `k > 0`, the inverse
odds `k exp(-α̃ - β̃ᵀx)` is a positive constant times `exp(α + βᵀ(x - c))` for every `x ∈ ℝ^p`
if and only if `β = -β̃`. Taking logarithms, two affine functions differ by a constant, so their
slopes agree. -/
theorem inverse_odds_proportional_iff (k α' α : ℝ) (β' β c : Fin p → ℝ) (hk : 0 < k) :
    (∃ C : ℝ, 0 < C ∧ ∀ x : Fin p → ℝ, k * Real.exp (-α' - β' ⬝ᵥ x) =
      C * tiltWeight id c α β x) ↔ β = -β' := by
  constructor
  · rintro ⟨C, hC, h⟩
    have hlog : ∀ x : Fin p → ℝ, Real.log k + (-α' - β' ⬝ᵥ x) =
        Real.log C + (α + β ⬝ᵥ (x - c)) := by
      intro x
      have := congrArg Real.log (h x)
      rwa [tiltWeight, Real.log_mul hk.ne' (Real.exp_pos _).ne',
        Real.log_mul hC.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp] at this
    funext i
    classical
    have h1 := hlog (Pi.single i 1)
    have h0 := hlog 0
    simp only [dotProduct_sub, dotProduct_single, dotProduct_zero, mul_one] at h1 h0
    simp only [Pi.neg_apply]
    linarith
  · rintro rfl
    obtain ⟨h, hpos⟩ := inverse_odds_eq_mul_tiltWeight k α' α β' c
    exact ⟨_, hpos hk, h⟩

/-- **The almost everywhere form**: if the covariate law `ν` is not carried by any affine
hyperplane `{vᵀx = r}` with `v ≠ 0`, then `k exp(-α̃ - β̃ᵀx) = C exp(α + βᵀ(x - c))` for
`ν`-almost every `x` and some `C > 0` if and only if `β = -β̃`. -/
theorem inverse_odds_proportional_ae_iff {ν : MeasureTheory.Measure (Fin p → ℝ)}
    (hnd : ∀ v : Fin p → ℝ, v ≠ 0 → ∀ r : ℝ, ¬ ∀ᵐ x ∂ν, v ⬝ᵥ x = r)
    (k α' α : ℝ) (β' β c : Fin p → ℝ) (hk : 0 < k) :
    (∃ C : ℝ, 0 < C ∧ ∀ᵐ x ∂ν, k * Real.exp (-α' - β' ⬝ᵥ x) =
      C * tiltWeight id c α β x) ↔ β = -β' := by
  constructor
  · rintro ⟨C, hC, h⟩
    by_contra hne
    refine hnd (β + β') (fun h0 => hne ?_)
      (Real.log k - α' - Real.log C - α + β ⬝ᵥ c) ?_
    · rw [← sub_eq_zero, sub_neg_eq_add]
      exact h0
    · filter_upwards [h] with x hx
      have := congrArg Real.log hx
      rw [tiltWeight, Real.log_mul hk.ne' (Real.exp_pos _).ne',
        Real.log_mul hC.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp] at this
      simp only [id, add_dotProduct, dotProduct_sub] at this ⊢
      linarith
  · rintro rfl
    obtain ⟨h, hpos⟩ := inverse_odds_eq_mul_tiltWeight k α' α β' c
    exact ⟨_, hpos hk, Filter.Eventually.of_forall h⟩

/-- **The nondegeneracy condition cannot be dropped**: for covariates concentrated at `0 ∈ ℝ¹`,
the inverse odds `1 · exp(0)` (`α̃ = 0`, `β̃ = 0`) is almost everywhere `1` times the tilting
weight `exp(x)` (`α = 0`, `β = 1`, `c = 0`), although `β ≠ -β̃`. -/
theorem inverse_odds_proportional_ae_counterexample :
    (∃ C : ℝ, 0 < C ∧ ∀ᵐ x ∂(MeasureTheory.Measure.dirac (0 : Fin 1 → ℝ)),
      1 * Real.exp (-0 - (0 : Fin 1 → ℝ) ⬝ᵥ x) = C * tiltWeight id 0 0 (fun _ => 1) x) ∧
      (fun _ => (1 : ℝ)) ≠ -(0 : Fin 1 → ℝ) := by
  refine ⟨⟨1, one_pos, ?_⟩, fun h => by simpa using congrFun h 0⟩
  rw [MeasureTheory.ae_dirac_eq, Filter.eventually_pure]
  simp [tiltWeight]

/-- **Inverse odds weights and tilting weights give the same weighted arm means**: for `k > 0`
and any sample, the weighted arm mean with the inverse odds weights `k exp(-α̃ - β̃ᵀxᵢ)` equals
the weighted arm mean with the tilting weights `exp(α + (-β̃)ᵀ(xᵢ - c))`. -/
theorem weightedArmMean_inverse_odds {n : ℕ} {ι' : Type*} [DecidableEq ι']
    (x : Fin n → Fin p → ℝ) (a : Fin n → ι') (y : Fin n → ℝ) (t : ι') (k α' α : ℝ)
    (β' c : Fin p → ℝ) (hk : 0 < k) :
    weightedArmMean (fun i => k * Real.exp (-α' - β' ⬝ᵥ x i)) a y t =
      weightedArmMean (fun i => tiltWeight id c α (-β') (x i)) a y t := by
  obtain ⟨h, hpos⟩ := inverse_odds_eq_mul_tiltWeight k α' α β' c
  simp_rw [h]
  exact weightedArmMean_smul (hpos hk).ne' _ a y t

end InverseOdds

end PopulationAdjustment

end CausalInference
