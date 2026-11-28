/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PointTreatment.SampleEstimators
public import CausalInference.PointTreatment.Randomized
public import CausalInference.Estimation.InstrumentalVariables

/-!
# Point treatment: consistency of the inverse probability weighted estimators

The Horvitz and Thompson estimator `n⁻¹ ∑ 1{A_i = a} Y_i / π̂_a(W_i)` and the Hájek estimator
(the same divided by the mean weight `n⁻¹ ∑ 1{A_i = a} / π̂_a(W_i)`) of the arm mean `E[Y(a)]`,
for an i.i.d. sample of the observed data `(W, A, Y)`.

**Known score.** With the true propensity score, the estimators are sample means, and the law of
large numbers sends them to the population weighting functionals, which equal `E[Y(a)]` under
ignorability and positivity (`IndicatorIgnorable.armMean_eq_ipw`) and `1` for the weights
(`ipwWeight_integral`). Positivity `P(A = a | W) > 0` almost surely suffices; no bound away from
zero is needed.

**Fitted score.** For a fitted score `ê` that converges to the true score at the sampled
covariates (`TendstoOnSample`) the estimators have the same limits under strict positivity
`ε ≤ e(W) ≤ 1 - ε`: on the events where `|ê - e| ≤ δ` at the sampled points, each weighted term
moves by at most `η` times `|1{A_i = a} Y_i|`, and `isConsistent_sampleMean_fitted` applies.

**Randomized trial.** If `A ⫫ (W, (Y(0), Y(1)))` with `0 < P(A = 1) < 1`, the true score is the
constant `P(A = 1)`, which the sample proportion of treated units estimates consistently. The
Horvitz and Thompson estimator with this fitted score is exactly the observed arm mean, so the
consistency of the observed arm means and of their difference for the average effect is a
corollary (`isConsistent_sampleNaiveContrast_of_indepFun`). With bounded outcomes the expected
difference in means converges to the average effect.

## Main results

* `IndicatorIgnorable.isConsistent_sampleIpwArmMean`, `IndicatorIgnorable.isConsistent_sampleIpwAte`
  and `Ignorable.isConsistent_sampleIpwAte`: known score, both forms.
* `isConsistent_sampleMean_div_armProb_fitted`: the perturbation step for a fitted score.
* `IndicatorIgnorable.isConsistent_sampleIpwArmMean_fitted`,
  `IndicatorIgnorable.isConsistent_sampleIpwAte_fitted`,
  `Ignorable.isConsistent_sampleIpwAte_fitted`: fitted score, both forms.
* `sampleIpwArmMean_propTreated`, `isConsistent_sampleArmMean_of_indepFun`,
  `isConsistent_sampleNaiveContrast_of_indepFun`,
  `tendsto_integral_sampleNaiveContrast_of_indepFun`: the randomized trial.

## References

* D. G. Horvitz and D. J. Thompson, *A generalization of sampling without replacement from a
  finite universe*, Journal of the American Statistical Association 47 (1952).
* J. Hájek, comment on a paper by D. Basu, in *Foundations of Statistical Inference*, Holt,
  Rinehart and Winston (1971).
* K. Hirano, G. W. Imbens and G. Ridder, *Efficient estimation of average treatment effects
  using the estimated propensity score*, Econometrica 71 (2003).
-/

@[expose] public section

namespace CausalInference

open MeasureTheory ProbabilityTheory MissingData Filter Finset
open scoped Topology

variable {Ξ : Type*} {mΞ : MeasurableSpace Ξ} {P : Measure Ξ}

/-- A sequence of almost everywhere strongly measurable functions bounded by a constant almost
everywhere is uniformly integrable under a finite measure. -/
theorem uniformIntegrable_of_ae_abs_le [IsFiniteMeasure P] {f : ℕ → Ξ → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) P) {K : ℝ} (hK : ∀ n, ∀ᵐ ξ ∂P, |f n ξ| ≤ K) :
    UniformIntegrable f 1 P := by
  refine uniformIntegrable_of le_rfl ENNReal.one_ne_top hf fun ε _ =>
    ⟨Real.toNNReal (K + 1), fun n => ?_⟩
  have h0 : {x | Real.toNNReal (K + 1) ≤ ‖f n x‖₊}.indicator (f n) =ᵐ[P] 0 := by
    filter_upwards [hK n] with ξ hξ
    rw [Set.indicator_of_notMem]
    · rfl
    · simp only [Set.mem_ofPred_eq, not_le]
      rw [← NNReal.coe_lt_coe, coe_nnNorm, Real.norm_eq_abs,
        Real.coe_toNNReal _ (by linarith [abs_nonneg (f n ξ)])]
      linarith
  rw [eLpNorm_congr_ae h0, eLpNorm_zero]
  exact zero_le

namespace PointTreatment

variable {Ω 𝒲 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒲] {μ : Measure Ω}
  {A : Ω → Bool} {W : Ω → 𝒲} {Y : Bool → Ω → ℝ} {e : 𝒲 → ℝ} {O : ℕ → Ξ → 𝒲 × Bool × ℝ}

/-! ### Two inequalities -/

omit [MeasurableSpace 𝒲] in
/-- The two arm probabilities move by the change of the score. -/
theorem abs_armProb_sub_armProb (e' e : 𝒲 → ℝ) (a : Bool) (w : 𝒲) :
    |armProb e' a w - armProb e a w| = |e' w - e w| := by
  cases a
  · simp only [armProb_false]
    rw [show 1 - e' w - (1 - e w) = -(e' w - e w) by ring, abs_neg]
  · simp

omit [MeasurableSpace 𝒲] in
/-- Strict positivity at a point bounds both arm probabilities below. -/
theorem le_armProb_of_mem {ε : ℝ} {w : 𝒲} (h : ε ≤ e w ∧ e w ≤ 1 - ε) (a : Bool) :
    ε ≤ armProb e a w := by
  cases a
  · simp only [armProb_false]; linarith [h.2]
  · exact h.1

/-- A ratio moves by at most `η |x|` when its denominator, at least `ε > 0`, moves by at most
`δ ≤ min (ε / 2) (η ε² / 2)`. -/
theorem abs_div_sub_div_le {x p q ε δ η : ℝ} (hε : 0 < ε) (hp : ε ≤ p) (hpq : |q - p| ≤ δ)
    (hδ1 : δ ≤ ε / 2) (hδ2 : δ ≤ η * ε ^ 2 / 2) (hη : 0 ≤ η) : |x / q - x / p| ≤ η * |x| := by
  have hq : ε / 2 ≤ q := by linarith [(abs_le.1 hpq).1]
  have hq0 : 0 < q := by linarith
  have hp0 : 0 < p := by linarith
  have hqp : ε ^ 2 / 2 ≤ q * p := by
    calc ε ^ 2 / 2 = ε / 2 * ε := by ring
      _ ≤ q * p := mul_le_mul hq hp hε.le hq0.le
  have heq : x / q - x / p = x * (p - q) / (q * p) := by
    rw [div_sub_div _ _ hq0.ne' hp0.ne']; ring
  have h1 : |p - q| ≤ δ := by rw [abs_sub_comm]; exact hpq
  rw [heq, abs_div, abs_mul, abs_of_pos (mul_pos hq0 hp0), div_le_iff₀ (mul_pos hq0 hp0)]
  calc |x| * |p - q| ≤ |x| * δ := mul_le_mul_of_nonneg_left h1 (abs_nonneg x)
    _ ≤ |x| * (η * ε ^ 2 / 2) := mul_le_mul_of_nonneg_left hδ2 (abs_nonneg x)
    _ = η * |x| * (ε ^ 2 / 2) := by ring
    _ ≤ η * |x| * (q * p) := mul_le_mul_of_nonneg_left hqp (by positivity)

/-! ### The perturbation step for a fitted score -/

/-- **Fitted inverse probability weights.** Let the true score satisfy strict positivity
`ε ≤ e ≤ 1 - ε` at almost every observed covariate, let `ê` converge to `e` on the sample, and
let `x (O 0)` be integrable. If the sample mean of `x / π_a(w)` is consistent for `c`, so is
the sample mean of `x / π̂_a(w)`. -/
theorem isConsistent_sampleMean_div_armProb_fitted [IsProbabilityMeasure P]
    (hO : IsIIDSample O P) {ε : ℝ} (hε : 0 < ε)
    (hstrict : ∀ᵐ z ∂(P.map (O 0)), ε ≤ e z.1 ∧ e z.1 ≤ 1 - ε) (a : Bool)
    {x : 𝒲 × Bool × ℝ → ℝ} (hx : Measurable x) (hxi : Integrable (fun ξ => x (O 0 ξ)) P)
    {c : ℝ} (h₀ : IsConsistent (sampleMean (fun z => x z / armProb e a z.1) O) c P)
    {ê : ℕ → Ξ → 𝒲 → ℝ} (hfit : TendstoOnSample P O ê e) :
    IsConsistent (fun n ξ => sampleMean (fun z => x z / armProb (ê n ξ) a z.1) O n ξ) c P := by
  refine isConsistent_sampleMean_fitted hO h₀ (g := fun z => |x z|)
    (continuous_abs.measurable.comp hx) hxi.abs fun η hη => ?_
  have hδ : 0 < min (ε / 2) (η * ε ^ 2 / 2) := lt_min (half_pos hε) (by positivity)
  refine ((WithProbTendingToOne.of_ae (hO.ae_forall hstrict)).inter (hfit _ hδ)).mono
    fun n ξ hξ i hi => ?_
  obtain ⟨h1, h2⟩ := hξ
  simp only [Set.mem_ofPred_eq] at h1 h2
  have hq : |armProb (ê n ξ) a (O i ξ).1 - armProb e a (O i ξ).1| ≤
      min (ε / 2) (η * ε ^ 2 / 2) := by
    rw [abs_armProb_sub_armProb]; exact h2 i hi
  exact abs_div_sub_div_le hε (le_armProb_of_mem (h1 i) a) hq (min_le_left _ _)
    (min_le_right _ _) hη.le

/-! ### Integrability of the observation functions -/

omit [MeasurableSpace 𝒲] in
/-- The weighted outcome numerator `1{A = a} Y` is integrable when `Y(a)` is. -/
theorem integrable_respInd_arm_mul_obsOutcome [IsFiniteMeasure μ] (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (a : Bool) (hYi : Integrable (Y a) μ) :
    Integrable (fun ω => armIndObs a (W ω, A ω, obsOutcome A Y ω) * obsOutcome A Y ω) μ := by
  refine hYi.abs.mono' (((measurable_respInd (measurable_arm hA a)).mul
    (measurable_obsOutcome hA hY)).aestronglyMeasurable.congr
      (Filter.Eventually.of_forall fun ω => by simp only [Pi.mul_apply, armIndObs_comp]))
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, armIndObs_comp, respInd_arm_mul_obsOutcome, abs_mul,
    abs_of_nonneg (respInd_nonneg _ _)]
  exact mul_le_of_le_one_left (abs_nonneg _) (respInd_le_one _ _)

/-! ### Known score -/

section Oracle

variable [IsProbabilityMeasure P] [IsProbabilityMeasure μ]

/-- **Horvitz and Thompson estimator with the known score.** Under the indicator form of
ignorability, positivity of the arm and integrability of `Y(a)`, for an i.i.d. sample of
`(W, A, Y)` the Horvitz and Thompson estimator with the true score is consistent for `E[Y(a)]`. -/
theorem IndicatorIgnorable.isConsistent_sampleIpwArmMean (hW : Measurable W) (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hign : IndicatorIgnorable μ A W Y)
    (hps : IsPropensityScore μ A W e) (a : Bool) (hpos : ∀ᵐ ω ∂μ, 0 < armProb e a (W ω))
    (hYi : Integrable (Y a) μ) (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = μ.map fun ω => (W ω, A ω, obsOutcome A Y ω)) :
    IsConsistent (sampleIpwArmMean (fun _ _ => e) a O) (armMean μ Y a) P := by
  have hD : Measurable fun ω => (W ω, A ω, obsOutcome A Y ω) :=
    hW.prodMk (hA.prodMk (measurable_obsOutcome hA hY))
  have hint : Integrable (fun ω => ipwObs e a (W ω, A ω, obsOutcome A Y ω)) μ := by
    rw [ipwObs_comp]; exact hign.integrable_ipw hW hA hY hps a hpos hYi
  have h := isConsistent_sampleMean_of_map_eq hO hD.aemeasurable hlaw (measurable_ipwObs hps.1 a)
    hint
  rw [ipwObs_comp] at h
  rw [hign.armMean_eq_ipw hW hA hY hps a hpos hYi]
  exact h

/-- **The mean weight with the known score is consistent for one**, under positivity of the
arm; no ignorability is needed. -/
theorem isConsistent_sampleIpwWeightMean (hW : Measurable W) (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hps : IsPropensityScore μ A W e) (a : Bool)
    (hpos : ∀ᵐ ω ∂μ, 0 < armProb e a (W ω)) (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = μ.map fun ω => (W ω, A ω, obsOutcome A Y ω)) :
    IsConsistent (sampleIpwWeightMean (fun _ _ => e) a O) 1 P := by
  have hD : Measurable fun ω => (W ω, A ω, obsOutcome A Y ω) :=
    hW.prodMk (hA.prodMk (measurable_obsOutcome hA hY))
  obtain ⟨hint, h1⟩ := ipwWeight_integral hW hA hps a hpos
  rw [← ipwWeightObs_comp W A Y] at hint h1
  have h := isConsistent_sampleMean_of_map_eq hO hD.aemeasurable hlaw
    (measurable_ipwWeightObs hps.1 a) hint
  rw [h1] at h
  exact h

/-- **Hájek estimator with the known score**, under the hypotheses of
`IndicatorIgnorable.isConsistent_sampleIpwArmMean`. -/
theorem IndicatorIgnorable.isConsistent_sampleHajekArmMean (hW : Measurable W)
    (hA : Measurable A) (hY : ∀ a, Measurable (Y a)) (hign : IndicatorIgnorable μ A W Y)
    (hps : IsPropensityScore μ A W e) (a : Bool) (hpos : ∀ᵐ ω ∂μ, 0 < armProb e a (W ω))
    (hYi : Integrable (Y a) μ) (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = μ.map fun ω => (W ω, A ω, obsOutcome A Y ω)) :
    IsConsistent (sampleHajekArmMean (fun _ _ => e) a O) (armMean μ Y a) P := by
  have h := (hign.isConsistent_sampleIpwArmMean hW hA hY hps a hpos hYi hO hlaw).div
    (isConsistent_sampleIpwWeightMean hW hA hY hps a hpos hO hlaw) one_ne_zero
  rw [div_one] at h
  exact h

/-- **The weighted estimators of the average effect with the known score**: under the indicator
form of ignorability, positivity `0 < e(W) < 1` and integrable potential outcomes, the Horvitz
and Thompson and the Hájek estimators are consistent for `E[Y(1) - Y(0)]`. -/
theorem IndicatorIgnorable.isConsistent_sampleIpwAte (hW : Measurable W) (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hYi : ∀ a, Integrable (Y a) μ)
    (hign : IndicatorIgnorable μ A W Y) (hps : IsPropensityScore μ A W e)
    (hov : OverlapAE e (μ.map W)) (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = μ.map fun ω => (W ω, A ω, obsOutcome A Y ω)) :
    IsConsistent (sampleIpwAte (fun _ _ => e) O) (ate μ Y) P ∧
      IsConsistent (sampleHajekAte (fun _ _ => e) O) (ate μ Y) P := by
  have hpos := armProb_pos_of_ae (hov.ae_comp hW.aemeasurable)
  rw [ate_eq_armMean_sub (hYi true) (hYi false)]
  exact ⟨(hign.isConsistent_sampleIpwArmMean hW hA hY hps true (hpos true) (hYi true) hO
      hlaw).sub (hign.isConsistent_sampleIpwArmMean hW hA hY hps false (hpos false)
        (hYi false) hO hlaw),
    (hign.isConsistent_sampleHajekArmMean hW hA hY hps true (hpos true) (hYi true) hO
      hlaw).sub (hign.isConsistent_sampleHajekArmMean hW hA hY hps false (hpos false)
        (hYi false) hO hlaw)⟩

/-- **The weighted estimators of the average effect with the known score under ignorability**
`A ⫫ (Y(0), Y(1)) | W`. -/
theorem Ignorable.isConsistent_sampleIpwAte [StandardBorelSpace Ω] (hW : Measurable W)
    (hA : Measurable A) (hY : ∀ a, Measurable (Y a)) (hYi : ∀ a, Integrable (Y a) μ)
    (hign : Ignorable μ A hW Y) (hps : IsPropensityScore μ A W e)
    (hov : OverlapAE e (μ.map W)) (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = μ.map fun ω => (W ω, A ω, obsOutcome A Y ω)) :
    IsConsistent (sampleIpwAte (fun _ _ => e) O) (ate μ Y) P ∧
      IsConsistent (sampleHajekAte (fun _ _ => e) O) (ate μ Y) P :=
  ((ignorable_iff_indicatorIgnorable hW hA hY).1 hign).isConsistent_sampleIpwAte hW hA hY hYi
    hps hov hO hlaw

end Oracle

/-! ### Fitted score -/

section Fitted

variable [IsProbabilityMeasure P] [IsProbabilityMeasure μ]

/-- **Weighted estimators with a fitted score.** Under the indicator form of ignorability,
strict positivity `ε ≤ e(W) ≤ 1 - ε` of the true score and integrability of `Y(a)`, for an
i.i.d. sample of `(W, A, Y)` and a fitted score `ê` converging to `e` on the sample, the
Horvitz and Thompson and the Hájek estimators with `ê` are consistent for `E[Y(a)]`. The fitted
score may be computed from the same sample and need not be measurable. -/
theorem IndicatorIgnorable.isConsistent_sampleIpwArmMean_fitted (hW : Measurable W)
    (hA : Measurable A) (hY : ∀ a, Measurable (Y a)) (hign : IndicatorIgnorable μ A W Y)
    (hps : IsPropensityScore μ A W e) {ε : ℝ} (hov : StrictOverlapAE e (μ.map W) ε) (a : Bool)
    (hYi : Integrable (Y a) μ) (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = μ.map fun ω => (W ω, A ω, obsOutcome A Y ω))
    {ê : ℕ → Ξ → 𝒲 → ℝ} (hfit : TendstoOnSample P O ê e) :
    IsConsistent (sampleIpwArmMean ê a O) (armMean μ Y a) P ∧
      IsConsistent (sampleHajekArmMean ê a O) (armMean μ Y a) P := by
  have hD : Measurable fun ω => (W ω, A ω, obsOutcome A Y ω) :=
    hW.prodMk (hA.prodMk (measurable_obsOutcome hA hY))
  have hstrict := ae_fst_of_map_eq hW hA hY hlaw hov.2
  have hpos := armProb_pos_of_ae (hov.overlapAE.ae_comp hW.aemeasurable) a
  have hxY : Measurable fun z : 𝒲 × Bool × ℝ => armIndObs a z * z.2.2 :=
    (measurable_armIndObs a).mul measurable_snd.snd
  have hHT := isConsistent_sampleMean_div_armProb_fitted hO hov.1 hstrict a hxY
    (integrable_comp_of_map_eq hO hD.aemeasurable hlaw hxY
      (integrable_respInd_arm_mul_obsOutcome hA hY a hYi))
    (hign.isConsistent_sampleIpwArmMean hW hA hY hps a hpos hYi hO hlaw) hfit
  have hint1 : Integrable (fun ω => armIndObs a (W ω, A ω, obsOutcome A Y ω)) μ := by
    simp only [armIndObs_comp]
    exact integrable_respInd (measurable_arm hA a)
  have hWt := isConsistent_sampleMean_div_armProb_fitted hO hov.1 hstrict a
    (measurable_armIndObs a)
    (integrable_comp_of_map_eq hO hD.aemeasurable hlaw (measurable_armIndObs a) hint1)
    (isConsistent_sampleIpwWeightMean hW hA hY hps a hpos hO hlaw) hfit
  refine ⟨hHT, ?_⟩
  have h := hHT.div hWt one_ne_zero
  rw [div_one] at h
  exact h

/-- **Weighted estimators of the average effect with a fitted score**: under the indicator form
of ignorability, strict positivity of the true score and integrable potential outcomes, for a
fitted score converging to the true score on the sample, the Horvitz and Thompson and the Hájek
estimators are consistent for `E[Y(1) - Y(0)]`. -/
theorem IndicatorIgnorable.isConsistent_sampleIpwAte_fitted (hW : Measurable W)
    (hA : Measurable A) (hY : ∀ a, Measurable (Y a)) (hYi : ∀ a, Integrable (Y a) μ)
    (hign : IndicatorIgnorable μ A W Y) (hps : IsPropensityScore μ A W e) {ε : ℝ}
    (hov : StrictOverlapAE e (μ.map W) ε) (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = μ.map fun ω => (W ω, A ω, obsOutcome A Y ω))
    {ê : ℕ → Ξ → 𝒲 → ℝ} (hfit : TendstoOnSample P O ê e) :
    IsConsistent (sampleIpwAte ê O) (ate μ Y) P ∧
      IsConsistent (sampleHajekAte ê O) (ate μ Y) P := by
  obtain ⟨h1, h1'⟩ := hign.isConsistent_sampleIpwArmMean_fitted hW hA hY hps hov true
    (hYi true) hO hlaw hfit
  obtain ⟨h0, h0'⟩ := hign.isConsistent_sampleIpwArmMean_fitted hW hA hY hps hov false
    (hYi false) hO hlaw hfit
  rw [ate_eq_armMean_sub (hYi true) (hYi false)]
  exact ⟨h1.sub h0, h1'.sub h0'⟩

/-- **Weighted estimators of the average effect with a fitted score under ignorability**
`A ⫫ (Y(0), Y(1)) | W` and strict positivity. -/
theorem Ignorable.isConsistent_sampleIpwAte_fitted [StandardBorelSpace Ω] (hW : Measurable W)
    (hA : Measurable A) (hY : ∀ a, Measurable (Y a)) (hYi : ∀ a, Integrable (Y a) μ)
    (hign : Ignorable μ A hW Y) (hps : IsPropensityScore μ A W e) {ε : ℝ}
    (hov : StrictOverlapAE e (μ.map W) ε) (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = μ.map fun ω => (W ω, A ω, obsOutcome A Y ω))
    {ê : ℕ → Ξ → 𝒲 → ℝ} (hfit : TendstoOnSample P O ê e) :
    IsConsistent (sampleIpwAte ê O) (ate μ Y) P ∧
      IsConsistent (sampleHajekAte ê O) (ate μ Y) P :=
  ((ignorable_iff_indicatorIgnorable hW hA hY).1 hign).isConsistent_sampleIpwAte_fitted hW hA
    hY hYi hps hov hO hlaw hfit

end Fitted

/-! ### The randomized trial -/

omit [MeasurableSpace 𝒲] in
theorem armIndObs_false (z : 𝒲 × Bool × ℝ) : armIndObs false z = 1 - armIndObs true z := by
  unfold armIndObs; cases z.2.1 <;> simp

omit [MeasurableSpace 𝒲] in
/-- With the sample proportion of treated units as a constant score, the probability of the arm
`a` is the sample proportion of the arm `a` (for a nonempty sample). -/
theorem armProb_sampleMean_armIndObs {n : ℕ} (hn : n ≠ 0) (a : Bool) (ξ : Ξ) (w : 𝒲) :
    armProb (fun _ => sampleMean (armIndObs true) O n ξ) a w = sampleMean (armIndObs a) O n ξ := by
  cases a
  · simp only [armProb_false, sampleMean, armIndObs_false, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, mul_sub]
    rw [inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn)]
  · rfl

omit [MeasurableSpace 𝒲] in
/-- **The Horvitz and Thompson estimator with the sample proportion of treated units as score is
the observed arm mean**: `n⁻¹ ∑ 1{A_i = a} Y_i / p̂_a = ∑ 1{A_i = a} Y_i / ∑ 1{A_i = a}`, where
`p̂_a` is the sample proportion of the arm `a`. Both sides vanish for an empty sample, and both
vanish (as divisions by zero) when no sampled unit is in the arm `a`. -/
theorem sampleIpwArmMean_propTreated (a : Bool) (O : ℕ → Ξ → 𝒲 × Bool × ℝ) (n : ℕ) (ξ : Ξ) :
    sampleIpwArmMean (fun n ξ _ => sampleMean (armIndObs true) O n ξ) a O n ξ =
      sampleArmMean a O n ξ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [sampleIpwArmMean, sampleArmMean, sampleMean]
  · have key : ∀ z, ipwObs (fun _ => sampleMean (armIndObs true) O n ξ) a z =
        armIndObs a z * z.2.2 / sampleMean (armIndObs a) O n ξ := fun z => by
      rw [ipwObs, armProb_sampleMean_armIndObs hn.ne' a ξ]
    change (n : ℝ)⁻¹ * ∑ i ∈ range n, ipwObs (fun _ => sampleMean (armIndObs true) O n ξ) a
        (O i ξ) = ((n : ℝ)⁻¹ * ∑ i ∈ range n, armIndObs a (O i ξ) * (O i ξ).2.2) /
          sampleMean (armIndObs a) O n ξ
    simp only [key]
    rw [← Finset.sum_div, mul_div_assoc]

variable [IsProbabilityMeasure P] [IsProbabilityMeasure μ]

/-- **The observed arm means of a randomized trial are consistent.** If
`A ⫫ (W, (Y(0), Y(1)))`, `0 < P(A = 1) < 1` and `Y(a)` is integrable, then for an i.i.d.
sample of `(W, A, Y)` the observed mean of the outcome in the arm `a` is consistent for
`E[Y(a)]`. It is the Horvitz and Thompson estimator with the sample proportion of treated
units as fitted constant score, which converges to the true constant score `P(A = 1)`. -/
theorem isConsistent_sampleArmMean_of_indepFun (hW : Measurable W) (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hind : IndepFun A (fun ω => (W ω, potentialPair Y ω)) μ)
    (h0 : 0 < μ.real (A ⁻¹' {true})) (h1 : μ.real (A ⁻¹' {true}) < 1) (a : Bool)
    (hYi : Integrable (Y a) μ) (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = μ.map fun ω => (W ω, A ω, obsOutcome A Y ω)) :
    IsConsistent (sampleArmMean a O) (armMean μ Y a) P := by
  have hD : Measurable fun ω => (W ω, A ω, obsOutcome A Y ω) :=
    hW.prodMk (hA.prodMk (measurable_obsOutcome hA hY))
  have hps := isPropensityScore_const_of_indepFun hW hA (hind.comp measurable_id measurable_fst)
  have hign := indicatorIgnorable_of_indepFun hW hA hY hind
  have hov := (strictOverlap_const (𝒲 := 𝒲) h0 h1).strictOverlapAE (μ.map W)
  have hp : IsConsistent (sampleMean (armIndObs true) O) (μ.real (A ⁻¹' {true})) P := by
    have hint : Integrable (fun ω => armIndObs true (W ω, A ω, obsOutcome A Y ω)) μ := by
      simp only [armIndObs_comp, arm_true]; exact integrable_respInd hA
    have h := isConsistent_sampleMean_of_map_eq hO hD.aemeasurable hlaw
      (measurable_armIndObs true) hint
    simp only [armIndObs_comp, arm_true, integral_respInd hA] at h
    exact h
  have hfit : TendstoOnSample P O (fun n ξ _ => sampleMean (armIndObs true) O n ξ)
      (fun _ => μ.real (A ⁻¹' {true})) :=
    TendstoOnSample.of_param (h := fun θ (_ : 𝒲) => θ)
      (fun ε hε => ⟨ε, hε, fun θ hθ _ => by rw [Real.dist_eq] at hθ; exact hθ.le⟩) hp
  have h := (hign.isConsistent_sampleIpwArmMean_fitted hW hA hY hps hov a hYi hO hlaw hfit).1
  have heq : sampleIpwArmMean (fun n ξ _ => sampleMean (armIndObs true) O n ξ) a O =
      sampleArmMean a O := funext fun n => funext fun ξ => sampleIpwArmMean_propTreated a O n ξ
  rwa [heq] at h

/-- **The difference in means of a randomized trial is consistent for the average effect.** If
`A ⫫ (W, (Y(0), Y(1)))`, `0 < P(A = 1) < 1` and the potential outcomes are integrable, the
difference of the observed arm means of an i.i.d. sample of `(W, A, Y)` is consistent for
`E[Y(1) - Y(0)]`. -/
theorem isConsistent_sampleNaiveContrast_of_indepFun (hW : Measurable W) (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hYi : ∀ a, Integrable (Y a) μ)
    (hind : IndepFun A (fun ω => (W ω, potentialPair Y ω)) μ)
    (h0 : 0 < μ.real (A ⁻¹' {true})) (h1 : μ.real (A ⁻¹' {true}) < 1) (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = μ.map fun ω => (W ω, A ω, obsOutcome A Y ω)) :
    IsConsistent (sampleNaiveContrast O) (ate μ Y) P := by
  rw [ate_eq_armMean_sub (hYi true) (hYi false)]
  exact (isConsistent_sampleArmMean_of_indepFun hW hA hY hind h0 h1 true (hYi true) hO
    hlaw).sub (isConsistent_sampleArmMean_of_indepFun hW hA hY hind h0 h1 false (hYi false) hO
      hlaw)

omit [MeasurableSpace 𝒲] [IsProbabilityMeasure P] [IsProbabilityMeasure μ] in
/-- The observed arm mean of a sample with outcomes bounded by `C` is bounded by `C`. -/
theorem abs_sampleArmMean_le {C : ℝ} {n : ℕ} {ξ : Ξ} (h : ∀ i, |(O i ξ).2.2| ≤ C) (a : Bool) :
    |sampleArmMean a O n ξ| ≤ C := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (h 0)
  have hn : (0 : ℝ) ≤ (n : ℝ)⁻¹ := inv_nonneg.2 n.cast_nonneg
  have hden : 0 ≤ sampleMean (armIndObs a) O n ξ :=
    mul_nonneg hn (Finset.sum_nonneg fun i _ => armIndObs_nonneg a _)
  have hsum : |∑ i ∈ range n, armIndObs a (O i ξ) * (O i ξ).2.2| ≤
      C * ∑ i ∈ range n, armIndObs a (O i ξ) := by
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul, abs_of_nonneg (armIndObs_nonneg a _), mul_comm]
    exact mul_le_mul_of_nonneg_right (h i) (armIndObs_nonneg a _)
  have hnum : |sampleMean (fun z => armIndObs a z * z.2.2) O n ξ| ≤
      C * sampleMean (armIndObs a) O n ξ := by
    simp only [sampleMean]
    rw [abs_mul, abs_of_nonneg hn]
    calc (n : ℝ)⁻¹ * |∑ i ∈ range n, armIndObs a (O i ξ) * (O i ξ).2.2|
        ≤ (n : ℝ)⁻¹ * (C * ∑ i ∈ range n, armIndObs a (O i ξ)) :=
          mul_le_mul_of_nonneg_left hsum hn
      _ = C * ((n : ℝ)⁻¹ * ∑ i ∈ range n, armIndObs a (O i ξ)) := by ring
  rw [sampleArmMean, abs_div, abs_of_nonneg hden]
  rcases hden.lt_or_eq with hpos | hzero
  · rw [div_le_iff₀ hpos]; exact hnum
  · rw [← hzero, div_zero]; exact hC

/-- **The expected difference in means of a randomized trial converges to the average effect**
when the potential outcomes are bounded: under the hypotheses of
`isConsistent_sampleNaiveContrast_of_indepFun` and `|Y(a)| ≤ C`, the estimators are bounded by
`2 C`, hence uniformly integrable, and their expectations converge to `E[Y(1) - Y(0)]`. -/
theorem tendsto_integral_sampleNaiveContrast_of_indepFun (hW : Measurable W) (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) {C : ℝ} (hb : ∀ a ω, |Y a ω| ≤ C)
    (hind : IndepFun A (fun ω => (W ω, potentialPair Y ω)) μ)
    (h0 : 0 < μ.real (A ⁻¹' {true})) (h1 : μ.real (A ⁻¹' {true}) < 1) (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = μ.map fun ω => (W ω, A ω, obsOutcome A Y ω)) :
    Tendsto (fun n => ∫ ξ, sampleNaiveContrast O n ξ ∂P) atTop (𝓝 (ate μ Y)) := by
  have hYi : ∀ a, Integrable (Y a) μ := fun a => (integrable_const C).mono'
    (hY a).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact hb a ω)
  have hD : Measurable fun ω => (W ω, A ω, obsOutcome A Y ω) :=
    hW.prodMk (hA.prodMk (measurable_obsOutcome hA hY))
  have hbound : ∀ᵐ z ∂(P.map (O 0)), |z.2.2| ≤ C := by
    rw [hlaw]
    exact (ae_map_iff hD.aemeasurable (measurableSet_le
      (continuous_abs.measurable.comp measurable_snd.snd) measurable_const)).2
      (Filter.Eventually.of_forall fun ω => hb (A ω) ω)
  have hall := hO.ae_forall hbound
  have hUI : UniformIntegrable (sampleNaiveContrast O) 1 P :=
    uniformIntegrable_of_ae_abs_le
      (fun n => ((isSampleMeasurable_sampleNaiveContrast O).aemeasurable hO n).aestronglyMeasurable)
      (K := C + C) fun n => hall.mono fun ξ hξ =>
        (abs_sub _ _).trans (add_le_add (abs_sampleArmMean_le hξ true)
          (abs_sampleArmMean_le hξ false))
  exact (isConsistent_sampleNaiveContrast_of_indepFun hW hA hY hYi hind h0 h1 hO
    hlaw).tendsto_integral_of_uniformIntegrable hUI

end PointTreatment

end CausalInference
