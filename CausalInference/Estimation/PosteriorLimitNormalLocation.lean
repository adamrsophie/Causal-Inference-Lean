/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.PosteriorLimitCoverage
public import CausalInference.MetaAnalysis.Conjugacy

/-!
# The Bernstein and von Mises conclusion in the normal location model

Observations `Y₁, Y₂, ...` are real, with known sampling variance `σ² > 0`, and the location `θ`
carries the proper normal prior `N(θ₀', τ²)`, `τ² > 0`. After `n` observations the posterior is
`N(m_n, v_n)` with precision `1/τ² + n/σ²`,
`m_n = (θ₀'/τ² + ∑ Yᵢ / σ²) / (1/τ² + n/σ²)` and `v_n = 1 / (1/τ² + n/σ²)`
(`posteriorMean`, `posteriorVariance` of the common effect model with all variances `σ²`;
`posterior_commonEffectLikelihood` identifies it with the normalized prior times likelihood).

* `tendsto_tvDist_gaussianReal`: `(m, v) ↦ ‖N(m, v) - N(0, s)‖_TV` is continuous at `(0, s)` for
  `s > 0`, by the dominated convergence argument for densities.
* `normalLocation_isBernsteinVonMises`: if the sample mean is consistent for `θ₀`, the posteriors
  satisfy the total variation Bernstein and von Mises conclusion with centering the sample mean
  and limit `N(0, σ²)`, for **every** proper normal prior. The data need not be normal: only the
  consistency of the sample mean is used, and it holds for every i.i.d. sample with integrable
  observations (`normalLocation_isBernsteinVonMises_of_iid`).
* `quantile_gaussianReal`, `credibleInterval_gaussianReal`: the equal tailed credible interval of
  `N(m, v)` is `[m - √v z, m + √v z]` with `Φ(z) = 1 - α/2`.
* `normalLocation_credibleInterval_coverage`: for i.i.d. data with variance `σ²` the credible
  interval of the posterior covers `θ₀` with probability tending to `1 - α`.
* `normalLocation_credibleInterval_coverage_of_gaussian`: the same with every hypothesis
  verified, for observations with law `N(θ₀, σ²)`.
* `normalLocation_sq_credibleInterval_coverage`: the concrete vanishing derivative
  counterexample: the target `θ²` at `θ₀ = 0` has coverage `0` at every sample size although the
  Bernstein and von Mises conclusion holds and the rescaled quantiles converge.
* `normalLocation_numeric`: prior `N(0, 1)`, `σ² = 1`, data `1, 2, 3` give the posterior
  `N(3/2, 1/4)` and the credible interval `[3/2 - z/2, 3/2 + z/2]`.
* `tendsto_posteriorMean_flat`, `tendsto_posteriorVariance_flat`: as `τ² → ∞` the posterior
  tends to `N(Ȳ_n, σ²/n)` and the credible interval to the Wald interval
  (`tendsto_credibleInterval_endpoints_flat`).

## References

* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press (1998), chapter 10.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace CausalInference

namespace PosteriorLimit

open BiasAnalysis.Distributions MetaAnalysis PopulationAdjustment

/-! ### Total variation between normal laws -/

/-- For two probability densities, `∫ |f - g| = 2 ∫ (g - f)⁺`. -/
lemma integral_abs_sub_eq_two_mul_integral_posPart {α : Type*} {mα : MeasurableSpace α}
    {ρ : Measure α} {f g : α → ℝ} (hf : Integrable f ρ) (hg : Integrable g ρ)
    (hfg : ∫ x, f x ∂ρ = ∫ x, g x ∂ρ) :
    ∫ x, |f x - g x| ∂ρ = 2 * ∫ x, max (g x - f x) 0 ∂ρ := by
  have hpt : ∀ x, |f x - g x| = (f x - g x) + 2 * max (g x - f x) 0 := by
    intro x
    rcases le_total (f x) (g x) with h | h
    · rw [abs_of_nonpos (by linarith), max_eq_left (by linarith)]
      ring
    · rw [abs_of_nonneg (by linarith), max_eq_right (by linarith)]
      ring
  have hpos : Integrable (fun x ↦ max (g x - f x) 0) ρ := (hg.sub hf).pos_part
  simp_rw [hpt]
  rw [integral_add (f := fun x ↦ f x - g x) (hf.sub hg) (hpos.const_mul 2), integral_sub hf hg,
    hfg, sub_self, zero_add, integral_const_mul]

lemma continuousAt_gaussianPDFReal_param {s : ℝ} (hs : 0 < s) (x : ℝ) :
    ContinuousAt (fun p : ℝ × ℝ ↦ gaussianPDFReal p.1 p.2.toNNReal x) (0, s) := by
  have hc : Continuous fun p : ℝ × ℝ ↦ ((p.2.toNNReal : ℝ≥0) : ℝ) :=
    NNReal.continuous_coe.comp (continuous_real_toNNReal.comp continuous_snd)
  have hs' : ((s.toNNReal : ℝ≥0) : ℝ) = s := Real.coe_toNNReal _ hs.le
  simp only [gaussianPDFReal_def]
  refine ContinuousAt.mul ?_ ?_
  · refine ContinuousAt.inv₀ ?_ ?_
    · exact (Real.continuous_sqrt.comp (continuous_const.mul hc)).continuousAt
    · simp only [hs']
      exact (Real.sqrt_pos.2 (by positivity)).ne'
  · refine Real.continuous_exp.continuousAt.comp ?_
    refine ContinuousAt.div ?_ (continuous_const.mul hc).continuousAt ?_
    · exact ((continuous_const.sub continuous_fst).pow 2).neg.continuousAt
    · simp only [hs']
      positivity

/-- **Total variation between normal laws is continuous** at `(0, s)`, `s > 0`:
`‖N(m, v) - N(0, s)‖_TV → 0` as `(m, v) → (0, s)`. -/
theorem tendsto_tvDist_gaussianReal {s : ℝ} (hs : 0 < s) :
    Tendsto (fun p : ℝ × ℝ ↦ tvDist (gaussianReal p.1 p.2.toNNReal) (gaussianReal 0 s.toNNReal))
      (𝓝 (0, s)) (𝓝 0) := by
  set g : ℝ → ℝ := gaussianPDFReal 0 s.toNNReal with hg
  have hs0 : s.toNNReal ≠ 0 := by simpa using hs
  have hpos : ∀ᶠ p : ℝ × ℝ in 𝓝 (0, s), 0 < p.2 :=
    continuous_snd.continuousAt.eventually (lt_mem_nhds hs)
  -- the integral of `|f_p - g|` tends to zero
  have hint : Tendsto (fun p : ℝ × ℝ ↦ ∫ x, |gaussianPDFReal p.1 p.2.toNNReal x - g x|)
      (𝓝 (0, s)) (𝓝 0) := by
    have hlim : Tendsto (fun p : ℝ × ℝ ↦ 2 * ∫ x, max (g x - gaussianPDFReal p.1 p.2.toNNReal x) 0)
        (𝓝 (0, s)) (𝓝 (2 * ∫ _ : ℝ, (0 : ℝ))) := by
      refine Tendsto.const_mul 2 ?_
      refine tendsto_integral_filter_of_dominated_convergence g ?_ ?_
        (integrable_gaussianPDFReal 0 _) (ae_of_all _ fun x ↦ ?_)
      · refine Eventually.of_forall fun p ↦ ?_
        exact ((measurable_gaussianPDFReal 0 _).sub (measurable_gaussianPDFReal _ _)).max
          measurable_const |>.aestronglyMeasurable
      · refine Eventually.of_forall fun p ↦ ae_of_all _ fun x ↦ ?_
        have h1 := gaussianPDFReal_nonneg p.1 p.2.toNNReal x
        have h2 := gaussianPDFReal_nonneg 0 s.toNNReal x
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        exact max_le (by simp only [hg]; linarith) h2
      · have hcx := continuousAt_gaussianPDFReal_param hs x
        have : Tendsto (fun p : ℝ × ℝ ↦ max (g x - gaussianPDFReal p.1 p.2.toNNReal x) 0)
            (𝓝 (0, s)) (𝓝 (max (g x - gaussianPDFReal 0 s.toNNReal x) 0)) :=
          ((tendsto_const_nhds.sub hcx.tendsto).max tendsto_const_nhds)
        simpa [hg] using this
    rw [integral_zero, mul_zero] at hlim
    refine hlim.congr' ?_
    filter_upwards [hpos] with p hp
    have hp0 : p.2.toNNReal ≠ 0 := by simpa using hp
    rw [integral_abs_sub_eq_two_mul_integral_posPart (integrable_gaussianPDFReal _ _)
      (integrable_gaussianPDFReal _ _)]
    rw [integral_gaussianPDFReal_eq_one _ hp0, integral_gaussianPDFReal_eq_one _ hs0]
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ tvDist_nonneg) ?_ hint
  filter_upwards [hpos] with p hp
  have hp0 : p.2.toNNReal ≠ 0 := by simpa using hp
  rw [gaussianReal_of_var_ne_zero _ hp0, gaussianReal_of_var_ne_zero _ hs0, gaussianPDF_def,
    gaussianPDF_def]
  exact tvDist_withDensity_le (integrable_gaussianPDFReal _ _) (integrable_gaussianPDFReal _ _)
    (gaussianPDFReal_nonneg _ _) (gaussianPDFReal_nonneg _ _)

/-! ### Closed forms -/

/-- The posterior precision with `n` observations of variance `σ²`: `1/τ² + n/σ²`. -/
lemma posteriorPrecision_fin_const (τ2 σ2 : ℝ) (n : ℕ) :
    posteriorPrecision τ2 (fun _ : Fin n ↦ σ2) = 1 / τ2 + n / σ2 := by
  simp [posteriorPrecision, ivWeight, div_eq_mul_inv]

/-- The posterior mean with `n` observations of variance `σ²`:
`(θ₀'/τ² + ∑ yᵢ / σ²) / (1/τ² + n/σ²)`. -/
lemma posteriorMean_fin_const (θp τ2 σ2 : ℝ) (n : ℕ) (y : Fin n → ℝ) :
    posteriorMean θp τ2 (fun _ : Fin n ↦ σ2) y =
      (θp / τ2 + (∑ i, y i) / σ2) / (1 / τ2 + n / σ2) := by
  rw [posteriorMean, posteriorPrecision_fin_const]
  congr 2
  simp only [ivwEstimate, weightedMean, ivWeight, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · by_cases hσ : σ2 = 0
    · simp [hσ]
    · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      rw [← Finset.mul_sum]
      field_simp

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- The posterior law of the location after `n` observations `Y₀, ..., Y_{n-1}` with known
variance `σ²` under the prior `N(θ₀', τ²)`. -/
noncomputable def normalLocationPosterior (θp τ2 σ2 : ℝ) (Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    Measure ℝ :=
  gaussianReal (posteriorMean θp τ2 (fun _ : Fin n ↦ σ2) fun i ↦ Y i ω)
    (posteriorVariance τ2 (fun _ : Fin n ↦ σ2)).toNNReal

instance (θp τ2 σ2 : ℝ) (Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    IsProbabilityMeasure (normalLocationPosterior θp τ2 σ2 Y n ω) := by
  unfold normalLocationPosterior
  infer_instance

/-- `normalLocationPosterior` is the posterior: for `n ≥ 1` it is the prior `N(θ₀', τ²)`
reweighted by the normal likelihood of the first `n` observations and normalized. -/
theorem normalLocationPosterior_eq {θp τ2 σ2 : ℝ} (hτ : 0 < τ2) (hσ : 0 < σ2) (Y : ℕ → Ω → ℝ)
    {n : ℕ} (hn : 1 ≤ n) (ω : Ω) :
    normalLocationPosterior θp τ2 σ2 Y n ω =
      (∫⁻ θ, ENNReal.ofReal (commonEffectLikelihood (fun _ : Fin n ↦ σ2) θ fun i ↦ Y i ω)
          ∂gaussianReal θp τ2.toNNReal)⁻¹ •
        (gaussianReal θp τ2.toNNReal).withDensity
          (fun θ ↦ ENNReal.ofReal (commonEffectLikelihood (fun _ : Fin n ↦ σ2) θ fun i ↦ Y i ω)) :=
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  ((posterior_commonEffectLikelihood (θ0 := θp) hτ (fun _ ↦ hσ) _).2.2).symm

/-- A deterministic convergent sequence converges in probability. -/
lemma tendstoInMeasure_of_tendsto_seq {E : Type*} [PseudoMetricSpace E] {a : ℕ → E} {c : E}
    (ha : Tendsto a atTop (𝓝 c)) :
    TendstoInMeasure P (fun n (_ : Ω) ↦ a n) atTop (fun _ ↦ c) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [ha.eventually (Metric.ball_mem_nhds c hε)] with n hn
  have : {ω : Ω | ε ≤ dist (a n) c} = ∅ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
    exact Metric.mem_ball.1 hn
  rw [this, measure_empty]

/-- **The Bernstein and von Mises conclusion in the normal location model.** Let the sample mean
`Ȳ_n` of the observations converge in probability to `θ₀`. Then, for every proper normal prior
`N(θ₀', τ²)` and known variance `σ² > 0`, the posteriors satisfy the total variation Bernstein
and von Mises conclusion with centering `Ȳ_n` and limit `N(0, σ²)`:
`‖Π_n - N(Ȳ_n, σ²/n)‖_TV → 0` in probability. -/
theorem normalLocation_isBernsteinVonMises {θp τ2 σ2 : ℝ} (hτ : 0 < τ2) (hσ : 0 < σ2)
    {Y : ℕ → Ω → ℝ} {θ₀ : ℝ} (hcons : TendstoInMeasure P (sampleMean id Y) atTop (fun _ ↦ θ₀)) :
    IsBernsteinVonMises P (normalLocationPosterior θp τ2 σ2 Y) (sampleMean id Y)
      (gaussianReal 0 σ2.toNNReal) where
  isProbabilityMeasure _ _ := inferInstance
  isProbabilityMeasure_limit := inferInstance
  tendsto := by
    set A : ℕ → ℝ := fun n ↦ 1 / τ2 + n / σ2 with hA
    have hApos : ∀ n : ℕ, 0 < A n := fun n ↦ by simp only [hA]; positivity
    set d : ℕ → ℝ := fun n ↦ n / A n with hd
    set c : ℕ → ℝ := fun n ↦ √(n : ℝ) / (τ2 * A n) with hc
    -- `d n → σ²`
    have hdlim : Tendsto d atTop (𝓝 σ2) := by
      have h1 : Tendsto (fun n : ℕ ↦ ((n : ℝ)⁻¹ * τ2⁻¹ + σ2⁻¹)⁻¹) atTop (𝓝 ((0 * τ2⁻¹ + σ2⁻¹)⁻¹)) :=
        ((tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).mul_const _ |>.add_const _).inv₀
          (by simp [hσ.ne'])
      rw [zero_mul, zero_add, inv_inv] at h1
      refine h1.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn)
      simp only [hd, hA]
      field_simp
    -- `c n → 0`
    have hclim : Tendsto c atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ ↦ (√(n : ℝ))⁻¹ * d n / τ2) atTop (𝓝 (0 * σ2 / τ2)) :=
        ((tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp
          tendsto_natCast_atTop_atTop)).mul hdlim).div_const _
      rw [zero_mul, zero_div] at h1
      refine h1.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hsq : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
      have hsq2 : √(n : ℝ) ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg _)
      simp only [hc, hd]
      have := hApos n
      have hnA : (n : ℝ) / A n = √(n : ℝ) * (√(n : ℝ) / A n) := by
        rw [← mul_div_assoc, Real.mul_self_sqrt (Nat.cast_nonneg _)]
      rw [hnA]
      field_simp
    -- joint convergence of the parameters of the rescaled posterior
    have hX : TendstoInMeasure P
        (fun n ω ↦ (c n * (θp - sampleMean id Y n ω), d n)) atTop (fun _ ↦ ((0 : ℝ), σ2)) := by
      have h1 : TendstoInMeasure P (fun n ω ↦ θp - sampleMean id Y n ω) atTop
          (fun _ ↦ θp - θ₀) :=
        hcons.comp_continuousAt (continuous_const.sub continuous_id).continuousAt
      have h2 := ((tendstoInMeasure_of_tendsto_seq (P := P) hclim).prodMk h1).comp_continuousAt
        (g := fun p : ℝ × ℝ ↦ p.1 * p.2) (continuous_fst.mul continuous_snd).continuousAt
      simp only [zero_mul] at h2
      exact h2.prodMk (tendstoInMeasure_of_tendsto_seq hdlim)
    have hH : ContinuousAt (fun p : ℝ × ℝ ↦
        tvDist (gaussianReal p.1 p.2.toNNReal) (gaussianReal 0 σ2.toNNReal)) ((0 : ℝ), σ2) := by
      unfold ContinuousAt
      dsimp only
      rw [tvDist_self]
      exact tendsto_tvDist_gaussianReal hσ
    have hfin := hX.comp_continuousAt hH
    simp only [tvDist_self] at hfin
    refine TendstoInMeasure.congr' ?_ EventuallyEq.rfl hfin
    filter_upwards [eventually_ge_atTop 1] with n hn
    refine ae_of_all _ fun ω ↦ ?_
    -- identify the total variation distance after the affine change of variables
    set xb := sampleMean id Y n ω with hxb
    set r := √(n : ℝ) with hr
    have hr0 : 0 < r := Real.sqrt_pos.2 (by exact_mod_cast hn)
    have hr2 : r ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg _)
    have hfm : Measurable fun u : ℝ ↦ r * (u - xb) := by fun_prop
    have hgm : Measurable fun u : ℝ ↦ xb + r⁻¹ * u := by fun_prop
    have hgf : ∀ u, xb + r⁻¹ * (r * (u - xb)) = u := fun u ↦ by field_simp; ring
    simp only
    symm
    rw [← tvDist_map_eq_of_leftInverse (μ := normalLocationPosterior θp τ2 σ2 Y n ω) hfm hgm hgf]
    have hN : ((gaussianReal 0 σ2.toNNReal).map fun z ↦ xb + r⁻¹ • z).map
        (fun u ↦ r * (u - xb)) = gaussianReal 0 σ2.toNNReal := by
      rw [Measure.map_map hfm (by fun_prop)]
      have : ((fun u ↦ r * (u - xb)) ∘ fun z : ℝ ↦ xb + r⁻¹ • z) = id := by
        funext z
        simp only [Function.comp_apply, smul_eq_mul, id]
        field_simp
        ring
      rw [this, Measure.map_id]
    rw [hN]
    have hP : (normalLocationPosterior θp τ2 σ2 Y n ω).map (fun u ↦ r * (u - xb)) =
        gaussianReal (c n * (θp - xb)) (d n).toNNReal := by
      have hcomp : (fun u : ℝ ↦ r * (u - xb)) = (fun u ↦ r * u) ∘ fun u ↦ u - xb := rfl
      rw [normalLocationPosterior, hcomp, ← Measure.map_map (by fun_prop) (by fun_prop),
        gaussianReal_map_sub_const, gaussianReal_map_const_mul]
      have hM : posteriorMean θp τ2 (fun _ : Fin n ↦ σ2) (fun i ↦ Y i ω) =
          (θp / τ2 + n * xb / σ2) / A n := by
        rw [posteriorMean_fin_const, hxb, sampleMean, Fin.sum_univ_eq_sum_range (fun i ↦ Y i ω)]
        have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn)
        simp only [hA, id]
        field_simp
      have hV : posteriorVariance τ2 (fun _ : Fin n ↦ σ2) = 1 / A n := by
        rw [posteriorVariance, posteriorPrecision_fin_const]
      congr 1
      · rw [hM, hc]
        have := hApos n
        simp only [hA, hr] at this ⊢
        field_simp
        ring
      · ext
        simp only [NNReal.coe_mul, NNReal.coe_mk, hV, hd]
        rw [Real.coe_toNNReal _ (by have := hApos n; positivity),
          Real.coe_toNNReal _ (by have := hApos n; positivity), hr2]
        ring
    rw [hP]

/-- **The Bernstein and von Mises conclusion for i.i.d. data.** For an i.i.d. sample with
integrable observations, mean `θ₀`, the normal location posteriors under every proper normal
prior satisfy the total variation conclusion with centering the sample mean. -/
theorem normalLocation_isBernsteinVonMises_of_iid [IsProbabilityMeasure P] {θp τ2 σ2 : ℝ}
    (hτ : 0 < τ2) (hσ : 0 < σ2) {Y : ℕ → Ω → ℝ} (hY : IsIIDSample Y P)
    (hint : Integrable (Y 0) P) :
    IsBernsteinVonMises P (normalLocationPosterior θp τ2 σ2 Y) (sampleMean id Y)
      (gaussianReal 0 σ2.toNNReal) :=
  normalLocation_isBernsteinVonMises hτ hσ (sampleMean_isConsistent hY measurable_id hint)

/-! ### The credible interval in closed form -/

/-- **Normal quantiles.** For `v > 0` and `Φ(z) = p`, the `p` quantile of `N(m, v)` is
`m + √v z`. -/
theorem quantile_gaussianReal (m : ℝ) {v : ℝ} (hv : 0 < v) {p z : ℝ}
    (hz : cdf (gaussianReal 0 1) z = p) :
    quantile (gaussianReal m v.toNNReal) p = m + √v * z := by
  have hs : 0 < √v := Real.sqrt_pos.2 hv
  have hvv : ((v.toNNReal : ℝ≥0) : ℝ) = √v ^ 2 := by
    rw [Real.coe_toNNReal _ hv.le, Real.sq_sqrt hv.le]
  have hv0 : v.toNNReal ≠ 0 := by simpa using hv
  obtain ⟨h1, h2⟩ := gaussianReal_cdf_strict_crossing hv z
  rw [hz] at h1 h2
  have hp := mem_Ioo_of_strict_crossing h1 h2
  have hcdf : cdf (gaussianReal m v.toNNReal) (m + √v * z) = p := by
    rw [cdf_gaussianReal_affine m hs hvv z, hz]
  refine le_antisymm ((quantile_le_iff hp _).2 hcdf.ge) (not_lt.1 fun hlt ↦ ?_)
  have hle := (quantile_le_iff hp _).1 (le_refl (quantile (gaussianReal m v.toNNReal) p))
  have := cdf_gaussianReal_strictMono m hv0 hlt
  linarith

/-- **The equal tailed credible interval of a normal law.** For `v > 0` and `Φ(z) = 1 - α/2`,
the credible interval of `N(m, v)` is `[m - √v z, m + √v z]`. -/
theorem credibleInterval_gaussianReal (m : ℝ) {v : ℝ} (hv : 0 < v) {α z : ℝ}
    (hz : cdf (gaussianReal 0 1) z = 1 - α / 2) :
    credibleInterval (gaussianReal m v.toNNReal) α = Icc (m - √v * z) (m + √v * z) := by
  have hzn : cdf (gaussianReal 0 1) (-z) = α / 2 := by
    rw [cdf_gaussianReal_zero_one_neg, hz]; ring
  rw [credibleInterval, quantile_gaussianReal m hv hzn, quantile_gaussianReal m hv hz, mul_neg,
    ← sub_eq_add_neg]

/-- The posterior variance with `n` observations is positive. -/
lemma posteriorVariance_fin_const_pos {τ2 σ2 : ℝ} (hτ : 0 < τ2) (hσ : 0 < σ2) (n : ℕ) :
    0 < posteriorVariance τ2 (fun _ : Fin n ↦ σ2) := by
  rw [posteriorVariance, posteriorPrecision_fin_const]
  positivity

/-- **The normal location credible interval.** The equal tailed credible interval of the
posterior is `[m_n - √v_n z, m_n + √v_n z]`. -/
theorem normalLocation_credibleInterval {θp τ2 σ2 : ℝ} (hτ : 0 < τ2) (hσ : 0 < σ2)
    (Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) {α z : ℝ} (hz : cdf (gaussianReal 0 1) z = 1 - α / 2) :
    credibleInterval (normalLocationPosterior θp τ2 σ2 Y n ω) α =
      Icc (posteriorMean θp τ2 (fun _ : Fin n ↦ σ2) (fun i ↦ Y i ω) -
          √(posteriorVariance τ2 (fun _ : Fin n ↦ σ2)) * z)
        (posteriorMean θp τ2 (fun _ : Fin n ↦ σ2) (fun i ↦ Y i ω) +
          √(posteriorVariance τ2 (fun _ : Fin n ↦ σ2)) * z) :=
  credibleInterval_gaussianReal _ (posteriorVariance_fin_const_pos hτ hσ n) hz

/-! ### Frequentist coverage -/

/-- **Coverage in the normal location model.** Let the observations be i.i.d. with finite second
moment, mean `θ₀` and variance equal to the known variance `σ² > 0`. For every proper normal
prior, `α ∈ (0, 1)` and `Φ(z) = 1 - α/2`, the probability that the equal tailed credible interval
of the posterior contains `θ₀` tends to `1 - α`. -/
theorem normalLocation_credibleInterval_coverage [IsProbabilityMeasure P] {θp τ2 σ2 : ℝ}
    (hτ : 0 < τ2) (hσ : 0 < σ2) {Y : ℕ → Ω → ℝ} (hY : IsIIDSample Y P) (hmem : MemLp (Y 0) 2 P)
    (hvar : P[fun ω ↦ (Y 0 ω - P[Y 0]) ^ 2] = σ2) {α z : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1)
    (hz : cdf (gaussianReal 0 1) z = 1 - α / 2) :
    Tendsto (fun n ↦
        P.real {ω | P[Y 0] ∈ credibleInterval (normalLocationPosterior θp τ2 σ2 Y n ω) α})
      atTop (𝓝 (1 - α)) := by
  have hbvm := (normalLocation_isBernsteinVonMises_of_iid (θp := θp) hτ hσ hY
    (hmem.integrable one_le_two)).isBernsteinVonMisesWeak
  have hlaw : HasLaw (id : ℝ → ℝ) (gaussianReal 0 σ2.toNNReal) (gaussianReal 0 σ2.toNNReal) :=
    HasLaw.id
  have hal := sampleMean_isAsymptoticallyLinear (O := Y) measurable_id hmem
  have hT := hal.tendstoInDistribution_of_isSampleMeasurable hY
    (isSampleMeasurable_sampleMean measurable_id Y) (Y := id) (P' := gaussianReal 0 σ2.toNNReal)
    (by simpa only [id, hvar] using hlaw)
  exact hbvm.tendsto_credibleInterval_coverage hσ hlaw (by simpa only [id] using hT) hα hz

/-! ### The flat prior limit -/

/-- **The flat prior limit of the posterior mean.** For `n ≥ 1` observations, as the prior
variance `τ² → ∞` the posterior mean tends to the sample mean `(∑ yᵢ)/n`. -/
theorem tendsto_posteriorMean_flat (θp σ2 : ℝ) (hσ : 0 < σ2) {n : ℕ} (hn : 1 ≤ n)
    (y : Fin n → ℝ) :
    Tendsto (fun τ2 ↦ posteriorMean θp τ2 (fun _ : Fin n ↦ σ2) y) atTop
      (𝓝 ((n : ℝ)⁻¹ * ∑ i, y i)) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn)
  simp_rw [posteriorMean_fin_const]
  have hinv : Tendsto (fun τ2 : ℝ ↦ τ2⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have := ((hinv.mul_const θp).add_const ((∑ i, y i) / σ2)).div
    (hinv.add_const ((n : ℝ) / σ2)) (by positivity)
  rw [zero_mul, zero_add, zero_add] at this
  convert this using 2 with τ2
  · simp only [div_eq_mul_inv, one_mul, Pi.mul_apply, Pi.inv_apply]
    ring
  · field_simp

/-- **The flat prior limit of the posterior variance:** `v_n → σ²/n` as `τ² → ∞`. -/
theorem tendsto_posteriorVariance_flat (σ2 : ℝ) (hσ : 0 < σ2) {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (fun τ2 ↦ posteriorVariance τ2 (fun _ : Fin n ↦ σ2)) atTop (𝓝 (σ2 / n)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  simp_rw [posteriorVariance, posteriorPrecision_fin_const]
  have := ((tendsto_inv_atTop_zero (𝕜 := ℝ)).add_const ((n : ℝ) / σ2)).inv₀ (by positivity)
  rw [zero_add, inv_div] at this
  simpa only [one_div] using this

/-- **The flat prior limit of the credible interval is the Wald interval.** For `n ≥ 1`
observations and `Φ(z) = 1 - α/2`, as `τ² → ∞` the endpoints of the equal tailed credible
interval of the posterior tend to the endpoints `ȳ ∓ z σ / √n` of the Wald interval
`waldInterval ȳ σ z n`. -/
theorem tendsto_credibleInterval_endpoints_flat (θp σ2 : ℝ) (hσ : 0 < σ2) {n : ℕ} (hn : 1 ≤ n)
    (y : Fin n → ℝ) {α z : ℝ} (hz : cdf (gaussianReal 0 1) z = 1 - α / 2) :
    Tendsto (fun τ2 ↦ (quantile (gaussianReal (posteriorMean θp τ2 (fun _ : Fin n ↦ σ2) y)
          (posteriorVariance τ2 (fun _ : Fin n ↦ σ2)).toNNReal) (α / 2),
        quantile (gaussianReal (posteriorMean θp τ2 (fun _ : Fin n ↦ σ2) y)
          (posteriorVariance τ2 (fun _ : Fin n ↦ σ2)).toNNReal) (1 - α / 2))) atTop
      (𝓝 ((n : ℝ)⁻¹ * (∑ i, y i) - z * √σ2 / √n, (n : ℝ)⁻¹ * (∑ i, y i) + z * √σ2 / √n)) ∧
      waldInterval ((n : ℝ)⁻¹ * ∑ i, y i) (√σ2) z n =
        Icc ((n : ℝ)⁻¹ * (∑ i, y i) - z * √σ2 / √n) ((n : ℝ)⁻¹ * (∑ i, y i) + z * √σ2 / √n) := by
  refine ⟨?_, rfl⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hzn : cdf (gaussianReal 0 1) (-z) = α / 2 := by
    rw [cdf_gaussianReal_zero_one_neg, hz]; ring
  have hM := tendsto_posteriorMean_flat θp σ2 hσ hn y
  have hS := (Real.continuous_sqrt.tendsto _).comp (tendsto_posteriorVariance_flat σ2 hσ hn)
  have hlim : √(σ2 / n) = √σ2 / √n := Real.sqrt_div' σ2 hn'.le
  rw [hlim] at hS
  have hE : ∀ᶠ τ2 : ℝ in atTop, 0 < τ2 := eventually_gt_atTop 0
  refine Tendsto.prodMk_nhds ?_ ?_
  · have := hM.add (hS.mul_const (-z))
    refine Tendsto.congr' ?_ (by convert this using 2; ring)
    filter_upwards [hE] with τ2 hτ
    rw [quantile_gaussianReal _ (posteriorVariance_fin_const_pos hτ hσ n) hzn]
    simp only [Function.comp_apply]
  · have := hM.add (hS.mul_const z)
    refine Tendsto.congr' ?_ (by convert this using 2; ring)
    filter_upwards [hE] with τ2 hτ
    rw [quantile_gaussianReal _ (posteriorVariance_fin_const_pos hτ hσ n) hz]
    simp only [Function.comp_apply]

/-! ### Every hypothesis verified for normal data -/

/-- **Coverage for normal data.** For i.i.d. observations with law `N(θ₀, σ²)`, the known
variance of the model, every proper normal prior, `α ∈ (0, 1)` and `Φ(z) = 1 - α/2`, the
probability that the equal tailed credible interval of the posterior contains `θ₀` tends to
`1 - α`. -/
theorem normalLocation_credibleInterval_coverage_of_gaussian [IsProbabilityMeasure P]
    {θp τ2 σ2 θ₀ : ℝ} (hτ : 0 < τ2) (hσ : 0 < σ2) {Y : ℕ → Ω → ℝ} (hY : IsIIDSample Y P)
    (hlaw : P.map (Y 0) = gaussianReal θ₀ σ2.toNNReal) {α z : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1)
    (hz : cdf (gaussianReal 0 1) z = 1 - α / 2) :
    Tendsto (fun n ↦
        P.real {ω | θ₀ ∈ credibleInterval (normalLocationPosterior θp τ2 σ2 Y n ω) α})
      atTop (𝓝 (1 - α)) := by
  have h0 : AEMeasurable (Y 0) P := (hY.ident 0).aemeasurable_fst
  have hmem : MemLp (Y 0) 2 P := by
    have := IsGaussian.memLp_id (gaussianReal θ₀ σ2.toNNReal) 2 (by simp)
    rw [← hlaw] at this
    exact (memLp_map_measure_iff aestronglyMeasurable_id h0).1 this
  have hmean : P[Y 0] = θ₀ := by
    have := integral_map (μ := P) h0 (aestronglyMeasurable_id (μ := P.map (Y 0)))
    simp only [id] at this
    rw [← this, hlaw]
    exact integral_id_gaussianReal
  have hvar : P[fun ω ↦ (Y 0 ω - P[Y 0]) ^ 2] = σ2 := by
    rw [hmean, ← integral_map h0 (by fun_prop : AEStronglyMeasurable (fun x : ℝ ↦ (x - θ₀) ^ 2)
      (P.map (Y 0))), hlaw]
    have := variance_eq_integral (X := id) (μ := gaussianReal θ₀ σ2.toNNReal) aemeasurable_id
    simp only [id, integral_id_gaussianReal] at this
    rw [variance_id_gaussianReal, Real.coe_toNNReal _ hσ.le] at this
    exact this.symm
  have := normalLocation_credibleInterval_coverage (θp := θp) hτ hσ hY hmem hvar hα hz
  rwa [hmean] at this

/-! ### A vanishing derivative in the normal location model -/

/-- **The counterexample, concretely.** For i.i.d. observations with integrable law of mean `0`
and every proper normal prior, the normal location posteriors satisfy the Bernstein and von Mises
conclusion, and for the target `θ²` at the truth `θ₀ = 0` the rescaled posterior quantiles
converge, yet the equal tailed credible interval of the posterior of `θ²` never contains `0`: its
coverage is `0` at every sample size. -/
theorem normalLocation_sq_credibleInterval_coverage [IsProbabilityMeasure P] {θp τ2 σ2 : ℝ}
    (hτ : 0 < τ2) (hσ : 0 < σ2) {Y : ℕ → Ω → ℝ} (hY : IsIIDSample Y P)
    (hint : Integrable (Y 0) P) (hmean : P[Y 0] = 0) {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    IsBernsteinVonMises P (normalLocationPosterior θp τ2 σ2 Y) (sampleMean id Y)
        (gaussianReal 0 σ2.toNNReal) ∧
      (∀ p ∈ Ioo (0 : ℝ) 1, TendstoInMeasure P (fun (n : ℕ) ω ↦
        √(n : ℝ) * (quantile ((normalLocationPosterior θp τ2 σ2 Y n ω).map fun θ ↦ θ ^ 2) p -
          sampleMean id Y n ω ^ 2)) atTop (fun _ ↦ 0)) ∧
      ∀ n, P.real {ω | (0 : ℝ) ^ 2 ∈
        credibleInterval ((normalLocationPosterior θp τ2 σ2 Y n ω).map fun θ ↦ θ ^ 2) α} = 0 := by
  have hbvm := normalLocation_isBernsteinVonMises_of_iid (θp := θp) hτ hσ hY hint
  have hcons : TendstoInMeasure P (sampleMean id Y) atTop (fun _ ↦ 0) := by
    have := sampleMean_isConsistent hY measurable_id hint
    simp only [id] at this
    rw [hmean] at this
    exact this
  have h0 : ∀ n ω, normalLocationPosterior θp τ2 σ2 Y n ω {0} = 0 := by
    intro n ω
    have hv : (posteriorVariance τ2 (fun _ : Fin n ↦ σ2)).toNNReal ≠ 0 := by
      simpa using posteriorVariance_fin_const_pos hτ hσ n
    have := nullSingletonClass_gaussianReal
      (μ := posteriorMean θp τ2 (fun _ : Fin n ↦ σ2) fun i ↦ Y i ω) hv
    rw [normalLocationPosterior]
    exact measure_singleton 0
  exact ⟨hbvm, sq_credibleInterval_coverage hbvm.isBernsteinVonMisesWeak hcons h0 hα⟩

/-! ### A numeric instance -/

/-- **A numeric instance.** Prior `N(0, 1)`, known variance `σ² = 1`, observations `1, 2, 3`: the
posterior precision is `4`, the posterior is `N(3/2, 1/4)`, and the equal tailed credible
interval is `[3/2 - z/2, 3/2 + z/2]` with `Φ(z) = 1 - α/2`. -/
theorem normalLocation_numeric {α z : ℝ} (hz : cdf (gaussianReal 0 1) z = 1 - α / 2) :
    posteriorMean 0 1 (fun _ : Fin 3 ↦ 1) ![1, 2, 3] = 3 / 2 ∧
      posteriorVariance 1 (fun _ : Fin 3 ↦ 1) = 1 / 4 ∧
      credibleInterval (gaussianReal (posteriorMean 0 1 (fun _ : Fin 3 ↦ 1) ![1, 2, 3])
        (posteriorVariance 1 (fun _ : Fin 3 ↦ (1 : ℝ))).toNNReal) α =
        Icc (3 / 2 - z / 2) (3 / 2 + z / 2) := by
  have hM : posteriorMean 0 1 (fun _ : Fin 3 ↦ 1) ![1, 2, 3] = 3 / 2 := by
    rw [posteriorMean_fin_const, Fin.sum_univ_three]
    norm_num
  have hV : posteriorVariance 1 (fun _ : Fin 3 ↦ (1 : ℝ)) = 1 / 4 := by
    rw [posteriorVariance, posteriorPrecision_fin_const]
    norm_num
  refine ⟨hM, hV, ?_⟩
  rw [hM, hV, credibleInterval_gaussianReal _ (by norm_num) hz]
  have : √(1 / 4 : ℝ) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [this]
  congr 1 <;> ring

end PosteriorLimit

end CausalInference
