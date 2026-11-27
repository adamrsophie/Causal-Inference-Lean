/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.BiasAnalysis.VarianceCovariance
public import CausalInference.Estimation.DeltaMethodSeveralSamples

/-!
# The printed variance formulas for independent studies of different sizes

The variance formulas of `VarianceFormulas` (M. P. Fox, R. F. MacLehose and T. L. Lash (2021),
*Applying Quantitative Bias Analysis to Epidemiologic Data*, second edition, Chapter 10) allow
each input to come from its own study, with its own size. Here each input is a sample proportion
in its own i.i.d. sample, the samples are mutually independent, and the size of sample `i` is
`N i n` with `N i n / n → rᵢ > 0` (`Estimation.DeltaMethodSeveralSamples`). The binomial input
variances are proved (`sampleProportion_isAsymptoticallyLinear`), not assumed. For each formula
two statements are proved: `√n` times the error of the plug-in estimator converges in
distribution to the centered Gaussian whose variance is the printed formula at the input
variances `p (1 - p) / rᵢ` and group sizes `rᵢ`; and `n` times the printed formula evaluated at the
actual sizes `N i n` converges to the same variance.

* `greenland_nondifferential_of_sizes`: Greenland variance, nondifferential misclassification,
  with validation studies for the sensitivity and the specificity and independent samples of
  cases and controls (`D₁`, `D₀` are the limit ratios of the group sizes).
* `greenland_differential_asymptotic` (one sample, the form of
  `VarianceCovariance.greenland_nondifferential_asymptotic`) and
  `greenland_differential_of_sizes`: Greenland variance, differential misclassification.
* `marshall_of_sizes`: Marshall variance for predictive values.
* `ivPooled_of_sizes`: inverse-variance pooling of studies of different sizes, and
  `ivPooled_estimated_of_sizes`: pooling with estimated weights, which does not change the
  asymptotic variance (Slutsky; `tendstoInMeasure_ivPooled_estimated_sub`). This needs a common
  value of the pooled estimates (the fixed-effect model). `ivPooled_smul` shows that the printed
  weights `1 / (σ2ᵢ / Nᵢ)` give the same pooled estimate as `1 / (n σ2ᵢ / Nᵢ)`.

Concrete sampling schemes meeting every hypothesis are in
`BiasAnalysis.VarianceSeveralSamplesWitnesses`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ENNReal NNReal

namespace CausalInference

namespace BiasAnalysis.VarianceSeveralSamples

open VarianceFormulas VarianceCovariance

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### Partial derivatives and the first-order variance -/

/-- If `g` is differentiable at `θ` and has derivative `d` along the `i`th coordinate line, then
the Fréchet derivative of `g` at `θ` sends the `i`th unit vector to `d`. -/
theorem fderiv_apply_single_eq {k : ℕ} {g : (Fin k → ℝ) → ℝ} {θ : Fin k → ℝ}
    (hg : DifferentiableAt ℝ g θ) (i : Fin k) {d : ℝ}
    (hd : HasDerivAt (fun t ↦ g (Function.update θ i t)) d (θ i)) :
    fderiv ℝ g θ (Pi.single i 1) = d := by
  have hg' : HasFDerivAt g (fderiv ℝ g θ) (Function.update θ i (θ i)) := by
    rw [Function.update_eq_self]
    exact hg.hasFDerivAt
  exact (hg'.comp_hasDerivAt (θ i) (hasDerivAt_update θ i (θ i))).unique hd

/-- **Several samples, partial derivatives.** The form of
`tendstoInDistribution_comp_hasFDerivAt_of_sizes` with the derivative given by partial derivatives
`dᵢ` and the influence functions of second moments `σ2ᵢ`: the limit is the centered Gaussian with
variance `firstOrderVariance d (σ2ᵢ / rᵢ)`. -/
theorem tendstoInDistribution_of_sizes {k : ℕ} {𝒪 : Fin k → Type*} [∀ i, MeasurableSpace (𝒪 i)]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {O : ∀ i, ℕ → Ω → 𝒪 i}
    (hO : ∀ i, IsIIDSample (O i) μ) (hind : iIndepFun (fun i ω ↦ fun j ↦ O i j ω) μ)
    {θhat : Fin k → ℕ → Ω → ℝ} {θ : Fin k → ℝ} {φ : ∀ i, 𝒪 i → ℝ}
    (h : ∀ i, IsAsymptoticallyLinear (θhat i) (θ i) (φ i) (O i) μ)
    {σ2 : Fin k → ℝ} (hσ : ∀ i, μ[fun ω ↦ φ i (O i 0 ω) ^ 2] = σ2 i)
    {N : Fin k → ℕ → ℕ} {r : Fin k → ℝ} (hr : ∀ i, 0 < r i)
    (hN : ∀ i, Tendsto (fun n ↦ (N i n : ℝ) / n) atTop (𝓝 (r i)))
    {g : (Fin k → ℝ) → ℝ} (hg : DifferentiableAt ℝ g θ) {d : Fin k → ℝ}
    (hd : ∀ i, HasDerivAt (fun t ↦ g (Function.update θ i t)) (d i) (θ i))
    (hmeas : ∀ n, AEMeasurable (fun ω ↦ g (fun i ↦ θhat i (N i n) ω)) μ)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → ℝ}
    (hY : HasLaw Y (gaussianReal 0 (firstOrderVariance d fun i ↦ σ2 i / r i).toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) * (g (fun i ↦ θhat i (N i n) ω) - g θ))
      atTop Y (fun _ ↦ μ) P' := by
  refine tendstoInDistribution_comp_hasFDerivAt_of_sizes hO hind h hr hN hg.hasFDerivAt hmeas ?_
  have : ∑ i, fderiv ℝ g θ (Pi.single i 1) ^ 2 * μ[fun ω ↦ φ i (O i 0 ω) ^ 2] / r i =
      firstOrderVariance d fun i ↦ σ2 i / r i := by
    simp only [firstOrderVariance, fderiv_apply_single_eq hg _ (hd _), hσ, mul_div_assoc]
  rw [this]
  exact hY

/-- **The printed variance with the actual sample sizes.** If the input variances are
`σ2ᵢ / N i n` (a variance per observation divided by the size of the sample), then `n` times the
first-order variance converges to the asymptotic variance `firstOrderVariance d (σ2ᵢ / rᵢ)`. -/
theorem tendsto_mul_firstOrderVariance_div_sizes {k : ℕ} (d σ2 : Fin k → ℝ)
    {N : Fin k → ℕ → ℕ} {r : Fin k → ℝ} (hr : ∀ i, 0 < r i)
    (hN : ∀ i, Tendsto (fun n ↦ (N i n : ℝ) / n) atTop (𝓝 (r i))) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * firstOrderVariance d fun i ↦ σ2 i / N i n) atTop
      (𝓝 (firstOrderVariance d fun i ↦ σ2 i / r i)) := by
  have hlim : Tendsto (fun n : ℕ ↦ firstOrderVariance d fun i ↦ σ2 i / ((N i n : ℝ) / n)) atTop
      (𝓝 (firstOrderVariance d fun i ↦ σ2 i / r i)) :=
    tendsto_finsetSum _ fun i _ ↦
      (tendsto_const_nhds.div (hN i) (hr i).ne').const_mul _
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (n : ℝ) ≠ 0 := by positivity
  simp only [firstOrderVariance, mul_sum]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [div_div_eq_mul_div]
  ring

/-! ### Sample proportions -/

/-- **Binomial variance.** For an indicator `f` (values `0` or `1`) with `E f (O 0) = p`, the
centered indicator has second moment `p (1 - p)`. -/
theorem integral_sq_indicator_sub {𝒪 : Type*} [MeasurableSpace 𝒪] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → 𝒪} (hX : AEMeasurable X μ) {f : 𝒪 → ℝ}
    (hf : Measurable f) (h01 : ∀ x, f x = 0 ∨ f x = 1) {p : ℝ} (hp : μ[fun ω ↦ f (X ω)] = p) :
    μ[fun ω ↦ (f (X ω) - p) ^ 2] = p * (1 - p) := by
  have hint : Integrable (fun ω ↦ f (X ω)) μ := by
    refine Integrable.of_bound (hf.comp_aemeasurable hX).aestronglyMeasurable 1
      (ae_of_all _ fun ω ↦ ?_)
    rcases h01 (X ω) with h | h <;> simp [h]
  have hpt : ∀ ω, (f (X ω) - p) ^ 2 = (1 - 2 * p) * f (X ω) + p ^ 2 := by
    intro ω
    rcases h01 (X ω) with h | h <;> rw [h] <;> ring
  simp_rw [hpt]
  rw [integral_add (hint.const_mul _) (integrable_const _), integral_const_mul, integral_const,
    hp]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  ring

/-- **The sample proportion is asymptotically linear** with influence function `f - p` and
asymptotic variance `p (1 - p)`. -/
theorem sampleProportion_isAsymptoticallyLinear {𝒪 : Type*} [MeasurableSpace 𝒪]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {O : ℕ → Ω → 𝒪} (hO : IsIIDSample O μ)
    {f : 𝒪 → ℝ} (hf : Measurable f) (h01 : ∀ x, f x = 0 ∨ f x = 1) {p : ℝ}
    (hp : μ[fun ω ↦ f (O 0 ω)] = p) :
    IsAsymptoticallyLinear (sampleMean f O) p (fun x ↦ f x - p) O μ ∧
      μ[fun ω ↦ (f (O 0 ω) - p) ^ 2] = p * (1 - p) := by
  have h2 : MemLp (fun ω ↦ f (O 0 ω)) 2 μ := by
    refine MemLp.of_bound (hf.comp_aemeasurable (hO.aemeasurable 0)).aestronglyMeasurable 1
      (ae_of_all _ fun ω ↦ ?_)
    rcases h01 (O 0 ω) with h | h <;> simp [h]
  have hAL := sampleMean_isAsymptoticallyLinear hf h2
  rw [hp] at hAL
  exact ⟨hAL, integral_sq_indicator_sub (hO.aemeasurable 0) hf h01 hp⟩

/-! ### Greenland variance, nondifferential misclassification -/

/-- The gradient of the nondifferential adjusted log odds ratio in `(SE, SP, pe₁, pe₀)`. -/
noncomputable def greenlandNondiffGrad (se sp pe₁ pe₀ : ℝ) : Fin 4 → ℝ :=
  ![-(1 / (se - pe₁)) + 1 / (se - pe₀), 1 / (pe₁ + sp - 1) - 1 / (pe₀ + sp - 1),
    1 / (pe₁ + sp - 1) + 1 / (se - pe₁), -(1 / (pe₀ + sp - 1) + 1 / (se - pe₀))]

/-- The partial derivatives of `logORSeSpNondiffVec` along the coordinate lines. -/
theorem hasDerivAt_logORSeSpNondiffVec_update {se sp pe₁ pe₀ : ℝ} (hA₁ : 0 < pe₁ + sp - 1)
    (hB₁ : 0 < se - pe₁) (hA₀ : 0 < pe₀ + sp - 1) (hB₀ : 0 < se - pe₀) (i : Fin 4) :
    HasDerivAt (fun t ↦ logORSeSpNondiffVec (Function.update ![se, sp, pe₁, pe₀] i t))
      (greenlandNondiffGrad se sp pe₁ pe₀ i) (![se, sp, pe₁, pe₀] i) := by
  obtain ⟨d0, d1, d2, d3, -⟩ := greenland_nondifferential (vse := 0) (vsp := 0)
    hA₁ hB₁ one_pos hA₀ hB₀ one_pos
  fin_cases i
  · refine d0.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ ?_)
    simp [logORSeSpNondiffVec]
  · refine d1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ ?_)
    simp [logORSeSpNondiffVec]
  · refine d2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ ?_)
    simp [logORSeSpNondiffVec]
  · refine d3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ ?_)
    simp [logORSeSpNondiffVec]

/-- The nondifferential adjusted log odds ratio is a measurable function of its inputs. -/
theorem measurable_logORSeSpNondiffVec : Measurable logORSeSpNondiffVec := by
  unfold logORSeSpNondiffVec logORSeSp logOddsSeSp
  fun_prop

/-- **Greenland variance, nondifferential, four independent studies of different sizes.** The
sensitivity is estimated by the proportion classified exposed in a validation sample of truly
exposed subjects (`O 0`, indicator `f 0`), the specificity by the proportion classified unexposed
in a validation sample of truly unexposed subjects (`O 1`), and the observed exposure proportions
by the proportions in a sample of cases (`O 2`) and of controls (`O 3`). The four samples are
i.i.d., mutually independent, and of sizes `N i n` with `N i n / n → r i > 0`. At an admissible
point, `√n` times the error of the plug-in adjusted log odds ratio converges in distribution to
the centered Gaussian whose variance is the printed Greenland formula `greenlandNondiff` with the
binomial variances `SE (1 - SE) / r 0`, `SP (1 - SP) / r 1` and group sizes `D₁ = r 2`,
`D₀ = r 3`; and `n` times the printed formula evaluated at the actual sizes `N i n` converges to
the same variance. The binomial variances are proved (`sampleProportion_isAsymptoticallyLinear`),
not assumed. -/
theorem greenland_nondifferential_of_sizes {𝒪 : Fin 4 → Type*} [∀ i, MeasurableSpace (𝒪 i)]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {O : ∀ i, ℕ → Ω → 𝒪 i}
    (hO : ∀ i, IsIIDSample (O i) μ) (hind : iIndepFun (fun i ω ↦ fun j ↦ O i j ω) μ)
    {f : ∀ i, 𝒪 i → ℝ} (hf : ∀ i, Measurable (f i)) (h01 : ∀ i x, f i x = 0 ∨ f i x = 1)
    {se sp pe₁ pe₀ : ℝ} (hp : ∀ i, μ[fun ω ↦ f i (O i 0 ω)] = ![se, sp, pe₁, pe₀] i)
    {N : Fin 4 → ℕ → ℕ} {r : Fin 4 → ℝ} (hr : ∀ i, 0 < r i)
    (hN : ∀ i, Tendsto (fun n ↦ (N i n : ℝ) / n) atTop (𝓝 (r i)))
    (hA₁ : 0 < pe₁ + sp - 1) (hB₁ : 0 < se - pe₁) (hA₀ : 0 < pe₀ + sp - 1) (hB₀ : 0 < se - pe₀)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → ℝ}
    (hY : HasLaw Y (gaussianReal 0 (greenlandNondiff (se * (1 - se) / r 0) (sp * (1 - sp) / r 1)
      se sp pe₁ (r 2) pe₀ (r 3)).toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) *
        (logORSeSp (sampleMean (f 0) (O 0) (N 0 n) ω) (sampleMean (f 1) (O 1) (N 1 n) ω)
          (sampleMean (f 2) (O 2) (N 2 n) ω) (sampleMean (f 0) (O 0) (N 0 n) ω)
          (sampleMean (f 1) (O 1) (N 1 n) ω) (sampleMean (f 3) (O 3) (N 3 n) ω) -
        logORSeSp se sp pe₁ se sp pe₀)) atTop Y (fun _ ↦ μ) P' ∧
      Tendsto (fun n : ℕ ↦ (n : ℝ) * greenlandNondiff (se * (1 - se) / N 0 n)
          (sp * (1 - sp) / N 1 n) se sp pe₁ (N 2 n) pe₀ (N 3 n)) atTop
        (𝓝 (greenlandNondiff (se * (1 - se) / r 0) (sp * (1 - sp) / r 1) se sp pe₁ (r 2) pe₀
          (r 3))) := by
  set θ : Fin 4 → ℝ := ![se, sp, pe₁, pe₀] with hθ
  have hAL : ∀ i, IsAsymptoticallyLinear (sampleMean (f i) (O i)) (θ i)
      (fun x ↦ f i x - θ i) (O i) μ ∧
      μ[fun ω ↦ (f i (O i 0 ω) - θ i) ^ 2] = θ i * (1 - θ i) := fun i ↦
    sampleProportion_isAsymptoticallyLinear (hO i) (hf i) (h01 i) (hp i)
  set σ2 : Fin 4 → ℝ := fun i ↦ θ i * (1 - θ i) with hσ2
  have hfov : ∀ D : Fin 4 → ℝ, (∀ i, 0 < D i) →
      firstOrderVariance (greenlandNondiffGrad se sp pe₁ pe₀) (fun i ↦ σ2 i / D i) =
        greenlandNondiff (se * (1 - se) / D 0) (sp * (1 - sp) / D 1) se sp pe₁ (D 2) pe₀
          (D 3) := by
    intro D hD
    have := (greenland_nondifferential (vse := se * (1 - se) / D 0) (vsp := sp * (1 - sp) / D 1)
      hA₁ hB₁ (hD 2) hA₀ hB₀ (hD 3)).2.2.2.2
    rw [← this]
    simp only [firstOrderVariance, Fin.sum_univ_four, greenlandNondiffGrad, hσ2, hθ]
    simp
  refine ⟨?_, ?_⟩
  · refine tendstoInDistribution_of_sizes hO hind (fun i ↦ (hAL i).1) (fun i ↦ (hAL i).2) hr hN
      (differentiableAt_logORSeSpNondiffVec hA₁ hB₁ hA₀ hB₀)
      (hasDerivAt_logORSeSpNondiffVec_update hA₁ hB₁ hA₀ hB₀)
      (fun n ↦ measurable_logORSeSpNondiffVec.comp_aemeasurable
        (AEMeasurable.of_eval fun i ↦
          (isSampleMeasurable_sampleMean (hf i) (O i)).aemeasurable (hO i) (N i n))) ?_
    rw [hfov r hr]
    exact hY
  · have h := tendsto_mul_firstOrderVariance_div_sizes (greenlandNondiffGrad se sp pe₁ pe₀) σ2
      hr hN
    rw [hfov r hr] at h
    refine h.congr' ?_
    filter_upwards [eventually_all.2 fun i ↦
      (tendsto_atTop_of_div_tendsto (hr i) (hN i)).eventually (eventually_ge_atTop 1)] with n hn
    rw [hfov (fun i ↦ (N i n : ℝ)) fun i ↦ by exact_mod_cast hn i]

/-! ### Greenland variance, differential misclassification -/

/-- The differential adjusted log odds ratio as a function of the input vector
`(SE₁, SP₁, pe₁, SE₀, SP₀, pe₀)`. -/
noncomputable def logORSeSpVec (v : Fin 6 → ℝ) : ℝ :=
  logORSeSp (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)

/-- The gradient of the differential adjusted log odds ratio. -/
noncomputable def greenlandGrad (se₁ sp₁ pe₁ se₀ sp₀ pe₀ : ℝ) : Fin 6 → ℝ :=
  ![-(1 / (se₁ - pe₁)), 1 / (pe₁ + sp₁ - 1), 1 / (pe₁ + sp₁ - 1) + 1 / (se₁ - pe₁),
    1 / (se₀ - pe₀), -(1 / (pe₀ + sp₀ - 1)), -(1 / (pe₀ + sp₀ - 1) + 1 / (se₀ - pe₀))]

/-- The differential adjusted log odds ratio is differentiable at an admissible point. -/
theorem differentiableAt_logORSeSpVec {se₁ sp₁ pe₁ se₀ sp₀ pe₀ : ℝ} (hA₁ : 0 < pe₁ + sp₁ - 1)
    (hB₁ : 0 < se₁ - pe₁) (hA₀ : 0 < pe₀ + sp₀ - 1) (hB₀ : 0 < se₀ - pe₀) :
    DifferentiableAt ℝ logORSeSpVec ![se₁, sp₁, pe₁, se₀, sp₀, pe₀] := by
  have p : ∀ i : Fin 6, DifferentiableAt ℝ (fun v : Fin 6 → ℝ ↦ v i)
      ![se₁, sp₁, pe₁, se₀, sp₀, pe₀] := fun i ↦ differentiableAt_apply i _
  unfold logORSeSpVec logORSeSp logOddsSeSp
  refine (((((p 2).add (p 1)).sub_const 1).log ?_).sub (((p 0).sub (p 2)).log ?_)).sub
    (((((p 5).add (p 4)).sub_const 1).log ?_).sub (((p 3).sub (p 5)).log ?_))
  · exact hA₁.ne'
  · exact hB₁.ne'
  · exact hA₀.ne'
  · exact hB₀.ne'

/-- The partial derivatives of `logORSeSpVec` along the coordinate lines. -/
theorem hasDerivAt_logORSeSpVec_update {se₁ sp₁ pe₁ se₀ sp₀ pe₀ : ℝ} (hA₁ : 0 < pe₁ + sp₁ - 1)
    (hB₁ : 0 < se₁ - pe₁) (hA₀ : 0 < pe₀ + sp₀ - 1) (hB₀ : 0 < se₀ - pe₀) (i : Fin 6) :
    HasDerivAt (fun t ↦ logORSeSpVec (Function.update ![se₁, sp₁, pe₁, se₀, sp₀, pe₀] i t))
      (greenlandGrad se₁ sp₁ pe₁ se₀ sp₀ pe₀ i) (![se₁, sp₁, pe₁, se₀, sp₀, pe₀] i) := by
  obtain ⟨d0, d1, d2, d3, d4, d5, -⟩ := greenland_differential (vse₁ := 0) (vsp₁ := 0)
    (vse₀ := 0) (vsp₀ := 0) hA₁ hB₁ one_pos hA₀ hB₀ one_pos
  fin_cases i
  · refine d0.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ ?_)
    simp [logORSeSpVec]
  · refine d1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ ?_)
    simp [logORSeSpVec]
  · refine d2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ ?_)
    simp [logORSeSpVec]
  · refine d3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ ?_)
    simp [logORSeSpVec]
  · refine d4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ ?_)
    simp [logORSeSpVec]
  · refine d5.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ ?_)
    simp [logORSeSpVec]

/-- The differential adjusted log odds ratio is a measurable function of its inputs. -/
theorem measurable_logORSeSpVec : Measurable logORSeSpVec := by
  unfold logORSeSpVec logORSeSp logOddsSeSp
  fun_prop

/-- The first-order variance with the gradient `greenlandGrad` is the sum of the two
`greenlandTerm`s. -/
theorem firstOrderVariance_greenlandGrad {vse₁ vsp₁ se₁ sp₁ pe₁ D₁ vse₀ vsp₀ se₀ sp₀ pe₀ D₀ : ℝ}
    (hA₁ : 0 < pe₁ + sp₁ - 1) (hB₁ : 0 < se₁ - pe₁) (hD₁ : 0 < D₁)
    (hA₀ : 0 < pe₀ + sp₀ - 1) (hB₀ : 0 < se₀ - pe₀) (hD₀ : 0 < D₀) :
    firstOrderVariance (greenlandGrad se₁ sp₁ pe₁ se₀ sp₀ pe₀)
        ![vse₁, vsp₁, pe₁ * (1 - pe₁) / D₁, vse₀, vsp₀, pe₀ * (1 - pe₀) / D₀] =
      greenlandTerm vse₁ vsp₁ se₁ sp₁ pe₁ D₁ + greenlandTerm vse₀ vsp₀ se₀ sp₀ pe₀ D₀ :=
  (greenland_differential hA₁ hB₁ hD₁ hA₀ hB₀ hD₀).2.2.2.2.2.2

/-- **The Greenland differential variance is an asymptotic variance (one sample).** The form of
`VarianceCovariance.greenland_nondifferential_asymptotic` for differential misclassification:
with six asymptotically linear inputs `(SE₁, SP₁, pe₁, SE₀, SP₀, pe₀)` of pairwise independent
influence functions with second moments `Var SE₁`, `Var SP₁`, `pe₁ (1 - pe₁) / D₁`, `Var SE₀`,
`Var SP₀`, `pe₀ (1 - pe₀) / D₀`, the plug-in adjusted log odds ratio is asymptotically linear and
its asymptotic variance is `greenlandTerm … D₁ + greenlandTerm … D₀`. -/
theorem greenland_differential_asymptotic {𝒪 : Type*} [MeasurableSpace 𝒪] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {O : ℕ → Ω → 𝒪} (hO : IsIIDSample O μ)
    {θhat : Fin 6 → ℕ → Ω → ℝ} {φ : Fin 6 → 𝒪 → ℝ}
    {vse₁ vsp₁ se₁ sp₁ pe₁ D₁ vse₀ vsp₀ se₀ sp₀ pe₀ D₀ : ℝ}
    (h : ∀ i, IsAsymptoticallyLinear (θhat i) (![se₁, sp₁, pe₁, se₀, sp₀, pe₀] i) (φ i) O μ)
    (hind : Pairwise fun i j ↦ IndepFun (fun ω ↦ φ i (O 0 ω)) (fun ω ↦ φ j (O 0 ω)) μ)
    (hσ : ∀ i, μ[fun ω ↦ φ i (O 0 ω) ^ 2] =
      ![vse₁, vsp₁, pe₁ * (1 - pe₁) / D₁, vse₀, vsp₀, pe₀ * (1 - pe₀) / D₀] i)
    (hA₁ : 0 < pe₁ + sp₁ - 1) (hB₁ : 0 < se₁ - pe₁) (hD₁ : 0 < D₁)
    (hA₀ : 0 < pe₀ + sp₀ - 1) (hB₀ : 0 < se₀ - pe₀) (hD₀ : 0 < D₀) :
    IsAsymptoticallyLinear
        (fun n ω ↦ logORSeSp (θhat 0 n ω) (θhat 1 n ω) (θhat 2 n ω) (θhat 3 n ω) (θhat 4 n ω)
          (θhat 5 n ω))
        (logORSeSp se₁ sp₁ pe₁ se₀ sp₀ pe₀)
        (fun x ↦ ∑ i, greenlandGrad se₁ sp₁ pe₁ se₀ sp₀ pe₀ i * φ i x) O μ ∧
      μ[fun ω ↦ (∑ i, greenlandGrad se₁ sp₁ pe₁ se₀ sp₀ pe₀ i * φ i (O 0 ω)) ^ 2] =
        greenlandTerm vse₁ vsp₁ se₁ sp₁ pe₁ D₁ + greenlandTerm vse₀ vsp₀ se₀ sp₀ pe₀ D₀ := by
  have key := asymptoticVariance_eq_firstOrderVariance hO h hind hσ
    (differentiableAt_logORSeSpVec hA₁ hB₁ hA₀ hB₀)
    (hasDerivAt_logORSeSpVec_update hA₁ hB₁ hA₀ hB₀)
  rw [firstOrderVariance_greenlandGrad hA₁ hB₁ hD₁ hA₀ hB₀ hD₀] at key
  exact key

/-- **Greenland variance, differential, six independent studies of different sizes.** As
`greenland_nondifferential_of_sizes`, with separate validation samples for the sensitivity and
specificity among cases (`O 0`, `O 1`) and among controls (`O 3`, `O 4`), and samples of cases
(`O 2`) and controls (`O 5`). The limit variance is the printed differential Greenland formula,
`greenlandTerm` for cases plus `greenlandTerm` for controls, with binomial input variances
`p (1 - p) / rᵢ` and group sizes `D₁ = r 2`, `D₀ = r 5`; `n` times the printed formula at the
actual sizes converges to it. -/
theorem greenland_differential_of_sizes {𝒪 : Fin 6 → Type*} [∀ i, MeasurableSpace (𝒪 i)]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {O : ∀ i, ℕ → Ω → 𝒪 i}
    (hO : ∀ i, IsIIDSample (O i) μ) (hind : iIndepFun (fun i ω ↦ fun j ↦ O i j ω) μ)
    {f : ∀ i, 𝒪 i → ℝ} (hf : ∀ i, Measurable (f i)) (h01 : ∀ i x, f i x = 0 ∨ f i x = 1)
    {se₁ sp₁ pe₁ se₀ sp₀ pe₀ : ℝ}
    (hp : ∀ i, μ[fun ω ↦ f i (O i 0 ω)] = ![se₁, sp₁, pe₁, se₀, sp₀, pe₀] i)
    {N : Fin 6 → ℕ → ℕ} {r : Fin 6 → ℝ} (hr : ∀ i, 0 < r i)
    (hN : ∀ i, Tendsto (fun n ↦ (N i n : ℝ) / n) atTop (𝓝 (r i)))
    (hA₁ : 0 < pe₁ + sp₁ - 1) (hB₁ : 0 < se₁ - pe₁) (hA₀ : 0 < pe₀ + sp₀ - 1)
    (hB₀ : 0 < se₀ - pe₀)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → ℝ}
    (hY : HasLaw Y (gaussianReal 0
      (greenlandTerm (se₁ * (1 - se₁) / r 0) (sp₁ * (1 - sp₁) / r 1) se₁ sp₁ pe₁ (r 2) +
        greenlandTerm (se₀ * (1 - se₀) / r 3) (sp₀ * (1 - sp₀) / r 4) se₀ sp₀ pe₀ (r 5)).toNNReal)
      P') :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) *
        (logORSeSp (sampleMean (f 0) (O 0) (N 0 n) ω) (sampleMean (f 1) (O 1) (N 1 n) ω)
          (sampleMean (f 2) (O 2) (N 2 n) ω) (sampleMean (f 3) (O 3) (N 3 n) ω)
          (sampleMean (f 4) (O 4) (N 4 n) ω) (sampleMean (f 5) (O 5) (N 5 n) ω) -
        logORSeSp se₁ sp₁ pe₁ se₀ sp₀ pe₀)) atTop Y (fun _ ↦ μ) P' ∧
      Tendsto (fun n : ℕ ↦ (n : ℝ) *
          (greenlandTerm (se₁ * (1 - se₁) / N 0 n) (sp₁ * (1 - sp₁) / N 1 n) se₁ sp₁ pe₁ (N 2 n) +
            greenlandTerm (se₀ * (1 - se₀) / N 3 n) (sp₀ * (1 - sp₀) / N 4 n) se₀ sp₀ pe₀
              (N 5 n))) atTop
        (𝓝 (greenlandTerm (se₁ * (1 - se₁) / r 0) (sp₁ * (1 - sp₁) / r 1) se₁ sp₁ pe₁ (r 2) +
          greenlandTerm (se₀ * (1 - se₀) / r 3) (sp₀ * (1 - sp₀) / r 4) se₀ sp₀ pe₀ (r 5))) := by
  set θ : Fin 6 → ℝ := ![se₁, sp₁, pe₁, se₀, sp₀, pe₀] with hθ
  have hAL : ∀ i, IsAsymptoticallyLinear (sampleMean (f i) (O i)) (θ i)
      (fun x ↦ f i x - θ i) (O i) μ ∧
      μ[fun ω ↦ (f i (O i 0 ω) - θ i) ^ 2] = θ i * (1 - θ i) := fun i ↦
    sampleProportion_isAsymptoticallyLinear (hO i) (hf i) (h01 i) (hp i)
  set σ2 : Fin 6 → ℝ := fun i ↦ θ i * (1 - θ i) with hσ2
  have hfov : ∀ D : Fin 6 → ℝ, (∀ i, 0 < D i) →
      firstOrderVariance (greenlandGrad se₁ sp₁ pe₁ se₀ sp₀ pe₀) (fun i ↦ σ2 i / D i) =
        greenlandTerm (se₁ * (1 - se₁) / D 0) (sp₁ * (1 - sp₁) / D 1) se₁ sp₁ pe₁ (D 2) +
          greenlandTerm (se₀ * (1 - se₀) / D 3) (sp₀ * (1 - sp₀) / D 4) se₀ sp₀ pe₀ (D 5) := by
    intro D hD
    rw [← firstOrderVariance_greenlandGrad hA₁ hB₁ (hD 2) hA₀ hB₀ (hD 5)]
    simp only [firstOrderVariance, Fin.sum_univ_six, hσ2, hθ]
    simp
  refine ⟨?_, ?_⟩
  · refine tendstoInDistribution_of_sizes hO hind (fun i ↦ (hAL i).1) (fun i ↦ (hAL i).2) hr hN
      (differentiableAt_logORSeSpVec hA₁ hB₁ hA₀ hB₀)
      (hasDerivAt_logORSeSpVec_update hA₁ hB₁ hA₀ hB₀)
      (fun n ↦ measurable_logORSeSpVec.comp_aemeasurable
        (AEMeasurable.of_eval fun i ↦
          (isSampleMeasurable_sampleMean (hf i) (O i)).aemeasurable (hO i) (N i n))) ?_
    rw [hfov r hr]
    exact hY
  · have h := tendsto_mul_firstOrderVariance_div_sizes (greenlandGrad se₁ sp₁ pe₁ se₀ sp₀ pe₀)
      σ2 hr hN
    rw [hfov r hr] at h
    refine h.congr' ?_
    filter_upwards [eventually_all.2 fun i ↦
      (tendsto_atTop_of_div_tendsto (hr i) (hN i)).eventually (eventually_ge_atTop 1)] with n hn
    rw [hfov (fun i ↦ (N i n : ℝ)) fun i ↦ by exact_mod_cast hn i]

/-! ### Marshall variance -/

/-- The gradient of the predictive-value adjusted log odds ratio, as in
`VarianceCovariance.marshall_asymptotic`. -/
noncomputable def marshallGrad (ppv₁ npv₁ pe₁ ppv₀ npv₀ pe₀ : ℝ) : Fin 6 → ℝ :=
  let P₁ := trueProportionPV ppv₁ npv₁ pe₁
  let P₀ := trueProportionPV ppv₀ npv₀ pe₀
  ![pe₁ / (P₁ * (1 - P₁)), -(1 - pe₁) / (P₁ * (1 - P₁)), (ppv₁ - (1 - npv₁)) / (P₁ * (1 - P₁)),
    -(pe₀ / (P₀ * (1 - P₀))), -(-(1 - pe₀) / (P₀ * (1 - P₀))),
    -((ppv₀ - (1 - npv₀)) / (P₀ * (1 - P₀)))]

/-- The partial derivatives of `logORPVVec` along the coordinate lines. -/
theorem hasDerivAt_logORPVVec_update {ppv₁ npv₁ pe₁ ppv₀ npv₀ pe₀ : ℝ}
    (hP₁₀ : 0 < trueProportionPV ppv₁ npv₁ pe₁) (hP₁₁ : trueProportionPV ppv₁ npv₁ pe₁ < 1)
    (hP₀₀ : 0 < trueProportionPV ppv₀ npv₀ pe₀) (hP₀₁ : trueProportionPV ppv₀ npv₀ pe₀ < 1)
    (i : Fin 6) :
    HasDerivAt (fun t ↦ logORPVVec (Function.update ![ppv₁, npv₁, pe₁, ppv₀, npv₀, pe₀] i t))
      (marshallGrad ppv₁ npv₁ pe₁ ppv₀ npv₀ pe₀ i) (![ppv₁, npv₁, pe₁, ppv₀, npv₀, pe₀] i) := by
  obtain ⟨d0, d1, d2, d3, d4, d5⟩ := hasDerivAt_logORPV hP₁₀ hP₁₁ hP₀₀ hP₀₁
  fin_cases i
  · refine d0.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ ?_)
    simp [logORPVVec]
  · refine d1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ ?_)
    simp [logORPVVec]
  · refine d2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ ?_)
    simp [logORPVVec]
  · refine d3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ ?_)
    simp [logORPVVec]
  · refine d4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ ?_)
    simp [logORPVVec]
  · refine d5.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ ?_)
    simp [logORPVVec]

/-- The predictive-value adjusted log odds ratio is differentiable where both corrected
proportions lie strictly inside `(0, 1)`. -/
theorem differentiableAt_logORPVVec {ppv₁ npv₁ pe₁ ppv₀ npv₀ pe₀ : ℝ}
    (hP₁₀ : 0 < trueProportionPV ppv₁ npv₁ pe₁) (hP₁₁ : trueProportionPV ppv₁ npv₁ pe₁ < 1)
    (hP₀₀ : 0 < trueProportionPV ppv₀ npv₀ pe₀) (hP₀₁ : trueProportionPV ppv₀ npv₀ pe₀ < 1) :
    DifferentiableAt ℝ logORPVVec ![ppv₁, npv₁, pe₁, ppv₀, npv₀, pe₀] := by
  unfold logORPVVec logORPV
  exact (differentiableAt_logOddsPV_comp 0 1 2 hP₁₀ hP₁₁).sub
    (differentiableAt_logOddsPV_comp 3 4 5 hP₀₀ hP₀₁)

/-- The predictive-value adjusted log odds ratio is a measurable function of its inputs. -/
theorem measurable_logORPVVec : Measurable logORPVVec := by
  unfold logORPVVec logORPV logOddsPV logit trueProportionPV
  fun_prop

/-- **Marshall variance, six independent studies of different sizes.** The positive and negative
predictive values among cases are estimated by proportions in validation samples of cases
classified exposed (`O 0`) and classified unexposed (`O 1`), the observed exposure proportion of
cases by a sample of cases (`O 2`), and likewise for controls (`O 3`, `O 4`, `O 5`). The samples are
i.i.d., mutually independent, of sizes `N i n` with `N i n / n → r i > 0`. Where both corrected
proportions lie strictly inside `(0, 1)`, `√n` times the error of the plug-in adjusted log odds
ratio converges in distribution to the centered Gaussian whose variance is the printed Marshall
formula with the binomial input variances `p (1 - p) / rᵢ`, and `n` times the printed formula at
the actual sizes converges to it. -/
theorem marshall_of_sizes {𝒪 : Fin 6 → Type*} [∀ i, MeasurableSpace (𝒪 i)]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {O : ∀ i, ℕ → Ω → 𝒪 i}
    (hO : ∀ i, IsIIDSample (O i) μ) (hind : iIndepFun (fun i ω ↦ fun j ↦ O i j ω) μ)
    {f : ∀ i, 𝒪 i → ℝ} (hf : ∀ i, Measurable (f i)) (h01 : ∀ i x, f i x = 0 ∨ f i x = 1)
    {ppv₁ npv₁ pe₁ ppv₀ npv₀ pe₀ : ℝ}
    (hp : ∀ i, μ[fun ω ↦ f i (O i 0 ω)] = ![ppv₁, npv₁, pe₁, ppv₀, npv₀, pe₀] i)
    {N : Fin 6 → ℕ → ℕ} {r : Fin 6 → ℝ} (hr : ∀ i, 0 < r i)
    (hN : ∀ i, Tendsto (fun n ↦ (N i n : ℝ) / n) atTop (𝓝 (r i)))
    (hP₁₀ : 0 < trueProportionPV ppv₁ npv₁ pe₁) (hP₁₁ : trueProportionPV ppv₁ npv₁ pe₁ < 1)
    (hP₀₀ : 0 < trueProportionPV ppv₀ npv₀ pe₀) (hP₀₁ : trueProportionPV ppv₀ npv₀ pe₀ < 1)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → ℝ}
    (hY : HasLaw Y (gaussianReal 0
      (marshallA (ppv₀ * (1 - ppv₀) / r 3) (npv₀ * (1 - npv₀) / r 4) (pe₀ * (1 - pe₀) / r 5)
          ppv₀ npv₀ pe₀ / (trueProportionPV ppv₀ npv₀ pe₀ *
            (1 - trueProportionPV ppv₀ npv₀ pe₀)) ^ 2 +
        marshallA (ppv₁ * (1 - ppv₁) / r 0) (npv₁ * (1 - npv₁) / r 1) (pe₁ * (1 - pe₁) / r 2)
          ppv₁ npv₁ pe₁ / (trueProportionPV ppv₁ npv₁ pe₁ *
            (1 - trueProportionPV ppv₁ npv₁ pe₁)) ^ 2).toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) *
        (logORPV (sampleMean (f 0) (O 0) (N 0 n) ω) (sampleMean (f 1) (O 1) (N 1 n) ω)
          (sampleMean (f 2) (O 2) (N 2 n) ω) (sampleMean (f 3) (O 3) (N 3 n) ω)
          (sampleMean (f 4) (O 4) (N 4 n) ω) (sampleMean (f 5) (O 5) (N 5 n) ω) -
        logORPV ppv₁ npv₁ pe₁ ppv₀ npv₀ pe₀)) atTop Y (fun _ ↦ μ) P' ∧
      Tendsto (fun n : ℕ ↦ (n : ℝ) *
          (marshallA (ppv₀ * (1 - ppv₀) / N 3 n) (npv₀ * (1 - npv₀) / N 4 n)
              (pe₀ * (1 - pe₀) / N 5 n) ppv₀ npv₀ pe₀ / (trueProportionPV ppv₀ npv₀ pe₀ *
                (1 - trueProportionPV ppv₀ npv₀ pe₀)) ^ 2 +
            marshallA (ppv₁ * (1 - ppv₁) / N 0 n) (npv₁ * (1 - npv₁) / N 1 n)
              (pe₁ * (1 - pe₁) / N 2 n) ppv₁ npv₁ pe₁ / (trueProportionPV ppv₁ npv₁ pe₁ *
                (1 - trueProportionPV ppv₁ npv₁ pe₁)) ^ 2)) atTop
        (𝓝 (marshallA (ppv₀ * (1 - ppv₀) / r 3) (npv₀ * (1 - npv₀) / r 4)
            (pe₀ * (1 - pe₀) / r 5) ppv₀ npv₀ pe₀ / (trueProportionPV ppv₀ npv₀ pe₀ *
              (1 - trueProportionPV ppv₀ npv₀ pe₀)) ^ 2 +
          marshallA (ppv₁ * (1 - ppv₁) / r 0) (npv₁ * (1 - npv₁) / r 1)
            (pe₁ * (1 - pe₁) / r 2) ppv₁ npv₁ pe₁ / (trueProportionPV ppv₁ npv₁ pe₁ *
              (1 - trueProportionPV ppv₁ npv₁ pe₁)) ^ 2)) := by
  set θ : Fin 6 → ℝ := ![ppv₁, npv₁, pe₁, ppv₀, npv₀, pe₀] with hθ
  have hAL : ∀ i, IsAsymptoticallyLinear (sampleMean (f i) (O i)) (θ i)
      (fun x ↦ f i x - θ i) (O i) μ ∧
      μ[fun ω ↦ (f i (O i 0 ω) - θ i) ^ 2] = θ i * (1 - θ i) := fun i ↦
    sampleProportion_isAsymptoticallyLinear (hO i) (hf i) (h01 i) (hp i)
  set σ2 : Fin 6 → ℝ := fun i ↦ θ i * (1 - θ i) with hσ2
  have hfov : ∀ D : Fin 6 → ℝ,
      firstOrderVariance (marshallGrad ppv₁ npv₁ pe₁ ppv₀ npv₀ pe₀) (fun i ↦ σ2 i / D i) =
        marshallA (ppv₀ * (1 - ppv₀) / D 3) (npv₀ * (1 - npv₀) / D 4) (pe₀ * (1 - pe₀) / D 5)
            ppv₀ npv₀ pe₀ / (trueProportionPV ppv₀ npv₀ pe₀ *
              (1 - trueProportionPV ppv₀ npv₀ pe₀)) ^ 2 +
          marshallA (ppv₁ * (1 - ppv₁) / D 0) (npv₁ * (1 - npv₁) / D 1) (pe₁ * (1 - pe₁) / D 2)
            ppv₁ npv₁ pe₁ / (trueProportionPV ppv₁ npv₁ pe₁ *
              (1 - trueProportionPV ppv₁ npv₁ pe₁)) ^ 2 := by
    intro D
    rw [← marshall_variance hP₁₀ hP₁₁ hP₀₀ hP₀₁]
    simp only [firstOrderVariance, Fin.sum_univ_six, hσ2, hθ, marshallGrad]
    simp
  refine ⟨?_, ?_⟩
  · refine tendstoInDistribution_of_sizes hO hind (fun i ↦ (hAL i).1) (fun i ↦ (hAL i).2) hr hN
      (differentiableAt_logORPVVec hP₁₀ hP₁₁ hP₀₀ hP₀₁)
      (hasDerivAt_logORPVVec_update hP₁₀ hP₁₁ hP₀₀ hP₀₁)
      (fun n ↦ measurable_logORPVVec.comp_aemeasurable
        (AEMeasurable.of_eval fun i ↦
          (isSampleMeasurable_sampleMean (hf i) (O i)).aemeasurable (hO i) (N i n))) ?_
    rw [hfov r]
    exact hY
  · have h := tendsto_mul_firstOrderVariance_div_sizes (marshallGrad ppv₁ npv₁ pe₁ ppv₀ npv₀ pe₀)
      σ2 hr hN
    rw [hfov r] at h
    refine h.congr fun n ↦ ?_
    rw [hfov (fun i ↦ (N i n : ℝ))]

/-! ### Inverse-variance pooling of studies of different sizes -/

/-- **The pooled estimate does not change when all variances are scaled.** For `c ≠ 0`,
`ivPooled θ (c • V) = ivPooled θ V`; the pooled variance scales by `c`. So pooling with the
printed variances `σ2ᵢ / Nᵢ` is pooling with `n σ2ᵢ / Nᵢ`, which converge to `σ2ᵢ / rᵢ`. -/
theorem ivPooled_smul {k : ℕ} (θ V : Fin k → ℝ) {c : ℝ} (hc : c ≠ 0) :
    ivPooled θ (c • V) = ivPooled θ V ∧ ivPooledVariance (c • V) = c * ivPooledVariance V := by
  have hW : ivTotalWeight (c • V) = c⁻¹ * ivTotalWeight V := by
    simp only [ivTotalWeight, Pi.smul_apply, smul_eq_mul, mul_sum]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [mul_one_div, one_div, mul_inv]
    ring
  refine ⟨?_, ?_⟩
  · have hS : ∑ i, θ i / (c • V) i = c⁻¹ * ∑ i, θ i / V i := by
      simp only [Pi.smul_apply, smul_eq_mul, mul_sum]
      refine sum_congr rfl fun i _ ↦ ?_
      rw [div_mul_eq_div_div_swap]
      ring
    rw [ivPooled, ivPooled, hS, hW, mul_div_mul_left _ _ (inv_ne_zero hc)]
  · rw [ivPooledVariance, ivPooledVariance, hW]
    by_cases hW0 : ivTotalWeight V = 0
    · simp [hW0]
    · field_simp

/-- On the event where the total weight does not vanish, the pooled estimate minus `θ₀` is the
weighted sum of the errors `θᵢ - θ₀`. -/
theorem ivPooled_sub_eq_sum {k : ℕ} (θ V : Fin k → ℝ) (θ₀ : ℝ) (hW : ivTotalWeight V ≠ 0) :
    ivPooled θ V - θ₀ = ∑ i, (1 / V i) / ivTotalWeight V * (θ i - θ₀) := by
  have hs : ∑ i, (1 / V i) / ivTotalWeight V = 1 := by
    rw [← sum_div]
    exact div_self hW
  simp only [mul_sub, sum_sub_distrib, ← sum_mul, hs, one_mul, ivPooled, sum_div]
  congr 1
  refine sum_congr rfl fun i _ ↦ ?_
  ring

/-- A sequence that vanishes outside events of vanishing probability tends to zero in
probability. -/
theorem tendstoInMeasure_zero_of_measure_ne_zero {μ : Measure Ω} {X : ℕ → Ω → ℝ}
    (h : Tendsto (fun n ↦ μ {ω | X n ω ≠ 0}) atTop (𝓝 0)) : TendstoInMeasure μ X atTop 0 := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ ↦ zero_le)
    fun n ↦ measure_mono fun ω hω ↦ ?_
  simp only [Set.mem_ofPred_eq, Pi.zero_apply, sub_zero] at hω ⊢
  intro h0
  rw [h0, norm_zero] at hω
  exact absurd hω (not_le.2 hε)

/-- **Pooling studies of different sizes with known weights.** Let `θhat i` be asymptotically
linear at `θ i` with influence function `φ i` in its own i.i.d. sample `O i`, the samples mutually
independent and of sizes `N i n` with `N i n / n → r i > 0`, and let the second moments
`σ2ᵢ = E φᵢ²` be positive. With `Vᵢ = σ2ᵢ / rᵢ` (the asymptotic variance of `θhat i` on the
`√n` scale), `√n (ivPooled θhat V - ivPooled θ V)` converges in distribution to the centered
Gaussian with variance `ivPooledVariance V`, and `n` times the printed pooled variance at the
actual sizes, `ivPooledVariance (σ2ᵢ / Nᵢ)`, converges to it. -/
theorem ivPooled_of_sizes {k : ℕ} (hk : 0 < k) {𝒪 : Fin k → Type*} [∀ i, MeasurableSpace (𝒪 i)]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {O : ∀ i, ℕ → Ω → 𝒪 i}
    (hO : ∀ i, IsIIDSample (O i) μ) (hind : iIndepFun (fun i ω ↦ fun j ↦ O i j ω) μ)
    {θhat : Fin k → ℕ → Ω → ℝ} {θ : Fin k → ℝ} {φ : ∀ i, 𝒪 i → ℝ}
    (h : ∀ i, IsAsymptoticallyLinear (θhat i) (θ i) (φ i) (O i) μ)
    {σ2 : Fin k → ℝ} (hσpos : ∀ i, 0 < σ2 i) (hσ : ∀ i, μ[fun ω ↦ φ i (O i 0 ω) ^ 2] = σ2 i)
    {N : Fin k → ℕ → ℕ} {r : Fin k → ℝ} (hr : ∀ i, 0 < r i)
    (hN : ∀ i, Tendsto (fun n ↦ (N i n : ℝ) / n) atTop (𝓝 (r i)))
    (hmeas : ∀ n, AEMeasurable (fun ω ↦ ivPooled (fun i ↦ θhat i (N i n) ω) fun i ↦ σ2 i / r i) μ)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → ℝ}
    (hY : HasLaw Y (gaussianReal 0 (ivPooledVariance fun i ↦ σ2 i / r i).toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) *
        (ivPooled (fun i ↦ θhat i (N i n) ω) (fun i ↦ σ2 i / r i) -
          ivPooled θ fun i ↦ σ2 i / r i)) atTop Y (fun _ ↦ μ) P' ∧
      Tendsto (fun n : ℕ ↦ (n : ℝ) * ivPooledVariance fun i ↦ σ2 i / N i n) atTop
        (𝓝 (ivPooledVariance fun i ↦ σ2 i / r i)) := by
  set V : Fin k → ℝ := fun i ↦ σ2 i / r i with hVdef
  have hV : ∀ i, 0 < V i := fun i ↦ div_pos (hσpos i) (hr i)
  set w : Fin k → ℝ := fun i ↦ (1 / V i) / ivTotalWeight V with hw
  let L : (Fin k → ℝ) →L[ℝ] ℝ := ∑ i, w i • ContinuousLinearMap.proj i
  have hL : (fun v ↦ ivPooled v V) = ⇑L := by
    funext v
    simp only [ivPooled, L, FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply,
      smul_eq_mul, hw, Finset.sum_div]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [ContinuousLinearMap.proj_apply]
    ring
  have hLs : ∀ i, L (Pi.single i 1) = w i := by
    intro i
    simp [L, Pi.single_apply]
  refine ⟨?_, ?_⟩
  · refine tendstoInDistribution_comp_hasFDerivAt_of_sizes hO hind h hr hN
      (g := fun v ↦ ivPooled v V) (L := L) (by rw [hL]; exact L.hasFDerivAt) hmeas ?_
    have : ∑ i, L (Pi.single i 1) ^ 2 * μ[fun ω ↦ φ i (O i 0 ω) ^ 2] / r i =
        ivPooledVariance V := by
      rw [← (firstOrderVariance_ivWeights hV hk).2]
      simp only [firstOrderVariance, hLs, hσ, hVdef, hw, mul_div_assoc]
    rw [this]
    exact hY
  · have hW : Tendsto (fun n : ℕ ↦ ∑ i, ((N i n : ℝ) / n) / σ2 i) atTop
        (𝓝 (ivTotalWeight V)) := by
      refine tendsto_finsetSum _ fun i _ ↦ ?_
      have : 1 / V i = r i / σ2 i := by rw [hVdef]; simp only [one_div_div]
      rw [this]
      exact (hN i).div_const (σ2 i)
    have hW0 : ivTotalWeight V ≠ 0 := (ivTotalWeight_pos hV hk).ne'
    have hlim := (tendsto_const_nhds (x := (1 : ℝ))).div hW hW0
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ≠ 0 := by positivity
    have hs : ∑ i, ((N i n : ℝ) / n) / σ2 i = (∑ i, 1 / (σ2 i / N i n)) / n := by
      rw [sum_div]
      refine sum_congr rfl fun i _ ↦ ?_
      rw [one_div_div]
      ring
    simp only [Pi.div_apply, ivPooledVariance, ivTotalWeight, hs]
    rw [one_div_div, mul_one_div]

/-- The inverse-variance weight `(1 / xᵢ) / ∑ⱼ (1 / xⱼ)` is continuous at a vector of positive
variances. -/
theorem continuousAt_ivWeight {k : ℕ} (hk : 0 < k) {V : Fin k → ℝ} (hV : ∀ i, 0 < V i)
    (i : Fin k) : ContinuousAt (fun x : Fin k → ℝ ↦ (1 / x i) / ivTotalWeight x) V := by
  have hinv : ∀ j, ContinuousAt (fun x : Fin k → ℝ ↦ 1 / x j) V := fun j ↦
    (continuousAt_const.div (continuous_apply j).continuousAt (hV j).ne')
  have hW : ContinuousAt (fun x : Fin k → ℝ ↦ ivTotalWeight x) V := by
    unfold ivTotalWeight ContinuousAt
    exact tendsto_finsetSum _ fun j _ ↦ hinv j
  exact (hinv i).div hW (ivTotalWeight_pos hV hk).ne'

/-- **Pooling with estimated weights (Slutsky).** Let the studies estimate a common value `θ₀`
(the fixed-effect model): `θhat i` is asymptotically linear at `θ₀` in its own i.i.d. sample, of
size `N i n` with `N i n / n → r i > 0`. Let `V̂ i n` be consistent for `Vᵢ > 0`. Then pooling with
the estimated weights instead of the limiting ones changes `√n (pooled - θ₀)` by a term that tends
to zero in probability. Independence between the samples is not needed for this step.

The common value is needed: with study-specific `θᵢ`, the difference contains
`√n ∑ᵢ (ŵᵢ - wᵢ) θᵢ`, which does not vanish in general. The event where the estimated total
weight is zero (on which the totalized `ivPooled` is `0`) has vanishing probability and is
handled explicitly. -/
theorem tendstoInMeasure_ivPooled_estimated_sub {k : ℕ} (hk : 0 < k) {𝒪 : Fin k → Type*}
    [∀ i, MeasurableSpace (𝒪 i)] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {O : ∀ i, ℕ → Ω → 𝒪 i} (hO : ∀ i, IsIIDSample (O i) μ)
    {θhat : Fin k → ℕ → Ω → ℝ} {θ₀ : ℝ} {φ : ∀ i, 𝒪 i → ℝ}
    (h : ∀ i, IsAsymptoticallyLinear (θhat i) θ₀ (φ i) (O i) μ)
    {N : Fin k → ℕ → ℕ} {r : Fin k → ℝ} (hr : ∀ i, 0 < r i)
    (hN : ∀ i, Tendsto (fun n ↦ (N i n : ℝ) / n) atTop (𝓝 (r i)))
    {V : Fin k → ℝ} (hV : ∀ i, 0 < V i) {Vhat : Fin k → ℕ → Ω → ℝ}
    (hVhat : ∀ i, TendstoInMeasure μ (Vhat i) atTop (fun _ ↦ V i)) :
    TendstoInMeasure μ (fun (n : ℕ) ω ↦
      √(n : ℝ) * (ivPooled (fun i ↦ θhat i (N i n) ω) (fun i ↦ Vhat i n ω) - θ₀) -
        √(n : ℝ) * (ivPooled (fun i ↦ θhat i (N i n) ω) V - θ₀)) atTop 0 := by
  set w : Fin k → ℝ := fun i ↦ (1 / V i) / ivTotalWeight V with hw
  have hW0 : ivTotalWeight V ≠ 0 := (ivTotalWeight_pos hV hk).ne'
  have hdw : ∀ i, TendstoInMeasure μ (fun n ω ↦
      (1 / Vhat i n ω) / ivTotalWeight (fun j ↦ Vhat j n ω) - w i) atTop 0 := by
    intro i
    have hc : ContinuousAt (fun x : Fin k → ℝ ↦ (1 / x i) / ivTotalWeight x - w i) V :=
      (continuousAt_ivWeight hk hV i).sub continuousAt_const
    have := tendstoInMeasure_pi_comp hVhat hc
    simp only [hw, sub_self] at this
    exact this
  have hE := tendstoInMeasure_finset_sum univ (μ := μ)
    (X := fun i (n : ℕ) ω ↦ ((1 / Vhat i n ω) / ivTotalWeight (fun j ↦ Vhat j n ω) - w i) *
      (√(n : ℝ) * (θhat i (N i n) ω - θ₀)))
    fun i _ ↦ tendstoInMeasure_mul_of_bounded (hdw i)
      ((h i).boundedInProbability_of_sizes (hO i) (hr i) (hN i))
  have hWc : TendstoInMeasure μ (fun n ω ↦ ivTotalWeight (fun j ↦ Vhat j n ω)) atTop
      (fun _ ↦ ivTotalWeight V) := by
    have hc : ContinuousAt (fun x : Fin k → ℝ ↦ ivTotalWeight x) V := by
      unfold ivTotalWeight ContinuousAt
      exact tendsto_finsetSum _ fun j _ ↦
        continuousAt_const.div (continuous_apply j).continuousAt (hV j).ne'
    exact tendstoInMeasure_pi_comp hVhat hc
  have hR : TendstoInMeasure μ (fun (n : ℕ) ω ↦
      (√(n : ℝ) * (ivPooled (fun i ↦ θhat i (N i n) ω) (fun i ↦ Vhat i n ω) - θ₀) -
        √(n : ℝ) * (ivPooled (fun i ↦ θhat i (N i n) ω) V - θ₀)) -
      ∑ i, ((1 / Vhat i n ω) / ivTotalWeight (fun j ↦ Vhat j n ω) - w i) *
        (√(n : ℝ) * (θhat i (N i n) ω - θ₀))) atTop 0 := by
    refine tendstoInMeasure_zero_of_measure_ne_zero ?_
    rw [tendstoInMeasure_iff_norm] at hWc
    have hpos : 0 < ‖ivTotalWeight V‖ := norm_pos_iff.2 hW0
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hWc _ hpos)
      (fun _ ↦ zero_le) fun n ↦ measure_mono fun ω hω ↦ ?_
    simp only [Set.mem_ofPred_eq] at hω ⊢
    by_contra hlt
    apply hω
    have hne : ivTotalWeight (fun j ↦ Vhat j n ω) ≠ 0 := by
      intro h0
      apply hlt
      rw [h0, zero_sub, norm_neg]
    rw [ivPooled_sub_eq_sum _ _ θ₀ hne, ivPooled_sub_eq_sum _ _ θ₀ hW0, mul_sum, mul_sum,
      ← sum_sub_distrib, sub_eq_zero]
    refine sum_congr rfl fun i _ ↦ ?_
    simp only [hw]
    ring
  have hsum := hR.add hE
  rw [add_zero] at hsum
  convert hsum using 1
  funext n ω
  simp only [Pi.add_apply]
  ring

/-- **Pooled estimate with estimated weights, studies of different sizes.** Under a common value
`θ₀`, with mutually independent samples of sizes `N i n` (`N i n / n → r i > 0`), positive second
moments `σ2ᵢ` of the influence functions, and weights from consistent estimates `V̂ i n` of
`Vᵢ = σ2ᵢ / rᵢ`, `√n (ivPooled θhat V̂ - θ₀)` converges in distribution to the centered Gaussian
with variance `ivPooledVariance V`: estimating the weights does not change the asymptotic
variance. -/
theorem ivPooled_estimated_of_sizes {k : ℕ} (hk : 0 < k) {𝒪 : Fin k → Type*}
    [∀ i, MeasurableSpace (𝒪 i)] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {O : ∀ i, ℕ → Ω → 𝒪 i} (hO : ∀ i, IsIIDSample (O i) μ)
    (hind : iIndepFun (fun i ω ↦ fun j ↦ O i j ω) μ)
    {θhat : Fin k → ℕ → Ω → ℝ} {θ₀ : ℝ} {φ : ∀ i, 𝒪 i → ℝ}
    (h : ∀ i, IsAsymptoticallyLinear (θhat i) θ₀ (φ i) (O i) μ)
    {σ2 : Fin k → ℝ} (hσpos : ∀ i, 0 < σ2 i) (hσ : ∀ i, μ[fun ω ↦ φ i (O i 0 ω) ^ 2] = σ2 i)
    {N : Fin k → ℕ → ℕ} {r : Fin k → ℝ} (hr : ∀ i, 0 < r i)
    (hN : ∀ i, Tendsto (fun n ↦ (N i n : ℝ) / n) atTop (𝓝 (r i)))
    {Vhat : Fin k → ℕ → Ω → ℝ}
    (hVhat : ∀ i, TendstoInMeasure μ (Vhat i) atTop (fun _ ↦ σ2 i / r i))
    (hmeas : ∀ n, AEMeasurable (fun ω ↦ ivPooled (fun i ↦ θhat i (N i n) ω) fun i ↦ σ2 i / r i) μ)
    (hmeas' : ∀ n, AEMeasurable
      (fun ω ↦ ivPooled (fun i ↦ θhat i (N i n) ω) fun i ↦ Vhat i n ω) μ)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → ℝ}
    (hY : HasLaw Y (gaussianReal 0 (ivPooledVariance fun i ↦ σ2 i / r i).toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) *
        (ivPooled (fun i ↦ θhat i (N i n) ω) (fun i ↦ Vhat i n ω) - θ₀)) atTop Y
      (fun _ ↦ μ) P' := by
  have hV : ∀ i, 0 < σ2 i / r i := fun i ↦ div_pos (hσpos i) (hr i)
  have hθ : ivPooled (fun _ : Fin k ↦ θ₀) (fun i ↦ σ2 i / r i) = θ₀ := by
    have := ivPooled_sub_eq_sum (fun _ : Fin k ↦ θ₀) (fun i ↦ σ2 i / r i) θ₀
      (ivTotalWeight_pos hV hk).ne'
    simpa [sub_eq_zero] using this
  have hknown := (ivPooled_of_sizes hk hO hind h hσpos hσ hr hN hmeas hY).1
  rw [hθ] at hknown
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ Y hknown ?_
    fun n ↦ ((hmeas' n).sub_const _).const_mul _
  have := tendstoInMeasure_ivPooled_estimated_sub hk hO h hr hN hV hVhat
  convert this using 1

end BiasAnalysis.VarianceSeveralSamples

end CausalInference
