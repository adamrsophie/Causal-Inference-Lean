/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.LikelihoodTests

/-!
# Local asymptotic normality of a regular parametric family

For an i.i.d. sample of size `n` from `P_θ₀` and a local parameter `h`, the log likelihood ratio
of `θ₀ + h/√n` against `θ₀` is

`Λ_n(h) = h S_n - h² I(θ₀) / 2 + o_P(1)`, with `S_n = n^{-1/2} ∑_{i < n} s(θ₀; O_i)`,

and `S_n` converges in distribution to `N(0, I(θ₀))`: the family is locally asymptotically
normal. The expansion is proved for a regular point (`ParametricFamily.IsRegularAt`) with the
second derivative of the log density smooth and dominated on a ball (`IsScoreRegular`), the
conditions under which Wilks' theorem holds in `CausalInference.Estimation.LikelihoodTests`.

The likelihood ratio is also a change of measure: integrating a function of the first `n`
observations against `e^{Λ_n}` gives its integral under the law of the sample family at the
alternative (`ParametricFamily.pi`), as long as the alternative has the same support.

## Main definitions

* `CausalInference.ParametricFamily.logLikRatio`: `∑_{i < n} (ℓ(θ; O_i) - ℓ(θ₀; O_i))`.

## Main results

* `CausalInference.ParametricFamily.law_eq_withDensity_ratio`: a law with the same support is
  the tilt `P_θ = (f_θ / f_θ₀) P_θ₀` of the reference law.
* `CausalInference.ParametricFamily.lintegral_mul_exp_logLikRatio`: the change of measure for an
  i.i.d. sample, `E[g(O_0, …, O_{n-1}) e^{Λ}] = ∫ g d(P_θ)^n`.
* `CausalInference.ParametricFamily.logLikRatio_sub_tendstoInMeasure`: **local asymptotic
  normality**, `Λ_n(h) - (h S_n - h² I(θ₀)/2) → 0` in probability.

The instance in which every hypothesis is checked is in
`CausalInference.Estimation.HajekConvolutionExamples`.

References: L. Le Cam (1960), *Locally asymptotically normal families of distributions*,
University of California Publications in Statistics; A. W. van der Vaart (1998), *Asymptotic
Statistics*, chapter 7.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Metric
open scoped Topology ENNReal NNReal

namespace CausalInference

namespace ParametricFamily

/-! ### Likelihood ratios as densities -/

section ChangeOfMeasure

variable {P S : Type*} [MeasurableSpace S] {F : ParametricFamily P S}

/-- **A law with the same support is a tilt of the reference law.** If `f(·;θ) > 0` exactly where
`f(·;θ₀) > 0`, then `P_θ = (f_θ / f_θ₀) P_θ₀`. -/
theorem law_eq_withDensity_ratio {θ₀ θ : P} (hθ₀ : θ₀ ∈ F.Θ) (hθ : θ ∈ F.Θ)
    (hsupp : ∀ x, 0 < F.density θ x ↔ 0 < F.density θ₀ x) :
    F.law θ = (F.law θ₀).withDensity fun x ↦ ENNReal.ofReal (F.density θ x / F.density θ₀ x) := by
  rw [law, law, ← withDensity_mul _ (f := fun x ↦ ENNReal.ofReal (F.density θ₀ x))
    (g := fun x ↦ ENNReal.ofReal (F.density θ x / F.density θ₀ x))
    (F.measurable_density θ₀).ennreal_ofReal
    ((F.measurable_density θ).div (F.measurable_density θ₀)).ennreal_ofReal]
  congr 1
  funext x
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (F.density_nonneg θ₀ hθ₀ x)]
  congr 1
  rcases (F.density_nonneg θ₀ hθ₀ x).lt_or_eq with h | h
  · field_simp
  · have h1 : ¬ 0 < F.density θ x := fun h' ↦ (lt_irrefl (0 : ℝ)) (h ▸ (hsupp x).1 h')
    have h2 : F.density θ x = 0 := le_antisymm (not_lt.1 h1) (F.density_nonneg θ hθ x)
    rw [← h, h2, zero_mul]

/-- A finite product of nonnegative reals is positive exactly when every factor is. -/
lemma prod_pos_iff_of_nonneg {ι : Type*} [Fintype ι] {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) :
    0 < ∏ i, a i ↔ ∀ i, 0 < a i := by
  refine ⟨fun h i ↦ ?_, fun h ↦ Finset.prod_pos fun i _ ↦ h i⟩
  by_contra hi
  have h0 : a i = 0 := le_antisymm (not_lt.1 hi) (ha i)
  rw [Finset.prod_eq_zero (Finset.mem_univ i) h0] at h
  exact lt_irrefl _ h

variable [SigmaFinite F.ν]

/-- The density of the sample family is the likelihood `∏_i f(x_i;θ)`. -/
theorem pi_density (n : ℕ) (θ : P) (x : Fin n → S) :
    (F.pi n).density θ x = ∏ i, F.density θ (x i) := rfl

/-- Common support passes to the sample family. -/
theorem pi_density_pos_iff {θ₀ θ : P} (hθ₀ : θ₀ ∈ F.Θ) (hθ : θ ∈ F.Θ)
    (hsupp : ∀ x, 0 < F.density θ x ↔ 0 < F.density θ₀ x) (n : ℕ) (x : Fin n → S) :
    0 < (F.pi n).density θ x ↔ 0 < (F.pi n).density θ₀ x := by
  rw [pi_density, pi_density, prod_pos_iff_of_nonneg fun i ↦ F.density_nonneg θ hθ (x i),
    prod_pos_iff_of_nonneg fun i ↦ F.density_nonneg θ₀ hθ₀ (x i)]
  exact forall_congr' fun i ↦ hsupp (x i)

end ChangeOfMeasure

variable {S : Type*} [MeasurableSpace S] {F : ParametricFamily ℝ S}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {O : ℕ → Ω → S} {θ₀ : ℝ}

variable (F) in
/-- The log likelihood ratio `∑_{i < n} (ℓ(θ; O_i) - ℓ(θ₀; O_i))` of `θ` against `θ₀` for the first
`n` observations. It is half the likelihood ratio statistic `lrStat` at the constant estimator
`θ` (`ParametricFamily.lrStat_const`). Lean's `Real.log 0 = 0` never carries a result: under
`P_θ₀` the observations have positive density almost surely (`ParametricFamily.ae_law_pos`), and
the theorems assume that `θ` has the support of `θ₀`, so both logarithms are of positive
numbers almost surely. -/
noncomputable def logLikRatio (O : ℕ → Ω → S) (θ₀ θ : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ range n, (F.logLik θ (O i ω) - F.logLik θ₀ (O i ω))

/-- The likelihood ratio statistic at a constant estimator is twice the log likelihood ratio. -/
theorem lrStat_const (θ₀ θ : ℝ) (n : ℕ) (ω : Ω) :
    F.lrStat O (fun _ _ ↦ θ) θ₀ n ω = 2 * F.logLikRatio O θ₀ θ n ω := rfl

/-- **Change of measure for an i.i.d. sample.** Let `O` be an i.i.d. sample with law `P_θ₀` and
let `θ ∈ Θ` have the same support as `θ₀`. Integrating `g` of the first `n` observations against
`e^{Λ}`, with `Λ` the log likelihood ratio of `θ` against `θ₀`, gives the integral of `g` under
the law `(P_θ)^n` of the sample family. -/
theorem lintegral_mul_exp_logLikRatio [SigmaFinite F.ν] [IsProbabilityMeasure μ]
    (hO : IsIIDSample O μ) (hlaw : μ.map (O 0) = F.law θ₀) {θ : ℝ} (hθ₀ : θ₀ ∈ F.Θ)
    (hθ : θ ∈ F.Θ) (hsupp : ∀ x, 0 < F.density θ x ↔ 0 < F.density θ₀ x) (n : ℕ)
    {g : (Fin n → S) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ ω, g (fun i ↦ O i ω) * ENNReal.ofReal (Real.exp (F.logLikRatio O θ₀ θ n ω)) ∂μ =
      ∫⁻ x, g x ∂(F.pi n).law θ := by
  set r : (Fin n → S) → ℝ≥0∞ := fun x ↦
    ENNReal.ofReal ((F.pi n).density θ x / (F.pi n).density θ₀ x) with hr
  have hrm : Measurable r :=
    (((F.pi n).measurable_density θ).div ((F.pi n).measurable_density θ₀)).ennreal_ofReal
  have hlaw' := law_eq_withDensity_ratio (F := F.pi n) hθ₀ hθ
    (pi_density_pos_iff hθ₀ hθ hsupp n)
  have hmap : μ.map (fun ω (i : Fin n) ↦ O i ω) = (F.pi n).law θ₀ := by
    rw [hO.map_fin_eq_pi n, hlaw, pi_law n hθ₀]
  have hR : AEMeasurable (fun ω (i : Fin n) ↦ O i ω) μ :=
    AEMeasurable.of_eval fun i ↦ hO.aemeasurable i
  rw [hlaw', lintegral_withDensity_eq_lintegral_mul _ hrm hg, ← hmap,
    lintegral_map' (hrm.mul hg).aemeasurable hR]
  refine lintegral_congr_ae ?_
  have hpos : ∀ᵐ ω ∂μ, ∀ i, 0 < F.density θ₀ (O i ω) :=
    hO.ae_forall (by rw [hlaw]; exact ae_law_pos)
  filter_upwards [hpos] with ω hω
  simp only [Pi.mul_apply]
  rw [mul_comm]
  congr 1
  have hp : ∀ i, 0 < F.density θ (O i ω) := fun i ↦ (hsupp _).2 (hω i)
  rw [hr, logLikRatio, Real.exp_sum]
  congr 1
  symm
  rw [pi_density, pi_density, ← Finset.prod_div_distrib, Fin.prod_univ_eq_prod_range
    (fun i ↦ F.density θ (O i ω) / F.density θ₀ (O i ω))]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [logLik, logLik, Real.exp_sub, Real.exp_log (hp i), Real.exp_log (hω i)]

/-- **Local asymptotic normality of a regular family.** Let `O` be an i.i.d. sample with law
`P_θ₀`, `θ₀` a regular point (`IsRegularAt`), the second derivative of the log density smooth and
dominated on a closed ball of radius `r` (`IsScoreRegular`), and `θ ↦ ℓ(θ; z)` with derivative
`s(θ; z)` on the ball for `P_θ₀`-almost every `z`. Then for every `h`, the log likelihood ratio of
`θ₀ + h/√n` against `θ₀` is `h S_n - h² I(θ₀) / 2 + o_P(1)` with
`S_n = n^{-1/2} ∑_{i < n} s(θ₀; O_i)`. The second order expansion of `θ ↦ n⁻¹ ∑_{i < n} ℓ(θ; O_i)`
around `θ₀` (`abs_sub_sub_le_of_hasDerivAt_two`), the uniform law of large numbers for the second
derivative and the information equality `E_θ₀ ∂²ℓ(θ₀; X) = -I(θ₀)` bound the remainder by
`η h²` with probability tending to one, for every `η > 0`. The derivative hypotheses are only
used `P_θ₀`-almost surely, where the density at `θ₀` is positive. -/
theorem logLikRatio_sub_tendstoInMeasure [IsProbabilityMeasure μ] (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = F.law θ₀) (hreg : F.IsRegularAt θ₀) {r : ℝ}
    (hs : F.IsScoreRegular θ₀ r)
    (hdl : ∀ᵐ z ∂F.law θ₀, ∀ θ ∈ closedBall θ₀ r,
      HasDerivAt (fun u ↦ F.logLik u z) (F.score θ z) θ) (h : ℝ) :
    TendstoInMeasure μ (fun (n : ℕ) ω ↦ F.logLikRatio O θ₀ (θ₀ + h / √(n : ℝ)) n ω -
      (h * ((√(n : ℝ))⁻¹ * ∑ i ∈ range n, F.score θ₀ (O i ω)) -
        h ^ 2 * F.fisherInfo θ₀ / 2)) atTop 0 := by
  obtain ⟨-, -, hinfo⟩ := hreg.information_equality
  obtain ⟨H, hH, hdom⟩ := hs.dominated
  obtain ⟨hMc, hunif⟩ := uniform_law_of_large_numbers_real hO (isCompact_closedBall θ₀ r)
    (ψ := fun z θ ↦ F.hessLogLik θ z) hs.measurable_hessLogLik
    (by rw [hlaw]; exact hs.continuousOn_hessLogLik) (by rw [hlaw]; exact hH)
    (by rw [hlaw]; exact hdom)
  generalize hMdef : (fun θ ↦ ∫ z, F.hessLogLik θ z ∂(μ.map (O 0))) = M at hMc hunif
  have hMI : M θ₀ = -F.fisherInfo θ₀ := by rw [← hMdef, hlaw, hinfo, neg_neg]
  have hMat : ContinuousAt M θ₀ := hMc.continuousAt (closedBall_mem_nhds θ₀ hs.pos)
  have hboth : ∀ᵐ z ∂(μ.map (O 0)), ∀ θ ∈ closedBall θ₀ r,
      HasDerivAt (fun u ↦ F.logLik u z) (F.score θ z) θ ∧
        HasDerivAt (fun u ↦ F.score u z) (F.hessLogLik θ z) θ := by
    rw [hlaw]
    filter_upwards [hdl, hs.hasDerivAt_score] with z h1 h2 θ hθ' using ⟨h1 θ hθ', h2 θ hθ'⟩
  have h0 : (0 : Ω → ℝ) = fun _ ↦ 0 := rfl
  rw [h0]
  refine tendstoInMeasure_of_good_events fun ε hε κ hκ ↦ ?_
  set η := ε / (h ^ 2 + 1) with hηdef
  have hη : 0 < η := by positivity
  obtain ⟨δ, hδ, hMδ⟩ := Metric.continuousAt_iff.1 hMat (η / 4) (by positivity)
  have hδr : 0 < min δ r := lt_min hδ hs.pos
  have hlim : Tendsto (fun n : ℕ ↦ |h| / √(n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  refine ⟨_, ((hunif (η / 4) (by positivity)).inter
    (WithProbTendingToOne.of_ae (hO.ae_forall hboth))).eventually_le hκ, ?_⟩
  filter_upwards [eventually_gt_atTop 0, hlim.eventually (gt_mem_nhds hδr)] with n hn hnδ ω hω
  obtain ⟨h2, h3⟩ := hω
  simp only [Set.mem_ofPred_eq] at h2 h3
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hsq : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn'
  have hd : |θ₀ + h / √(n : ℝ) - θ₀| < min δ r := by
    rw [add_sub_cancel_left, abs_div, abs_of_pos hsq]; exact hnδ
  have hmem : ∀ t ∈ Set.uIcc θ₀ (θ₀ + h / √(n : ℝ)), dist t θ₀ < min δ r := fun t ht ↦ by
    rw [Real.dist_eq]
    exact lt_of_le_of_lt (Set.abs_sub_left_of_mem_uIcc ht) hd
  have hball : ∀ t ∈ Set.uIcc θ₀ (θ₀ + h / √(n : ℝ)), t ∈ closedBall θ₀ r := fun t ht ↦
    mem_closedBall.2 ((hmem t ht).le.trans (min_le_right _ _))
  set Z := sampleMean (fun z ↦ F.score θ₀ z) O n ω with hZ
  have hR := abs_sub_sub_le_of_hasDerivAt_two (a := θ₀) (b := θ₀ + h / √(n : ℝ)) (c := M θ₀)
    (η := η / 2)
    (g := fun t ↦ sampleMean (fun z ↦ F.logLik t z) O n ω - (t - θ₀) * Z)
    (g' := fun t ↦ sampleMean (fun z ↦ F.score t z) O n ω - Z)
    (g'' := fun t ↦ sampleMean (fun z ↦ F.hessLogLik t z) O n ω)
    (fun t ht ↦ by
      have h1 : HasDerivAt (fun t ↦ (n : ℝ)⁻¹ * ∑ i ∈ range n, F.logLik t (O i ω))
          ((n : ℝ)⁻¹ * ∑ i ∈ range n, F.score t (O i ω)) t :=
        (HasDerivAt.fun_sum fun i _ ↦ (h3 i t (hball t ht)).1).const_mul _
      have h2 := ((hasDerivAt_id t).sub_const θ₀).mul_const Z
      simp only [sampleMean]
      convert h1.sub h2 using 1
      · rfl
      · ring)
    (fun t ht ↦ ((HasDerivAt.fun_sum fun i _ ↦
      (h3 i t (hball t ht)).2).const_mul (n : ℝ)⁻¹).sub_const Z)
    (fun t ht ↦ by
      have e1 := h2 t (hball t ht)
      have e2 := hMδ (lt_of_lt_of_le (hmem t ht) (min_le_left _ _))
      rw [Real.dist_eq] at e1 e2
      calc |sampleMean (fun z ↦ F.hessLogLik t z) O n ω - M θ₀|
          ≤ |sampleMean (fun z ↦ F.hessLogLik t z) O n ω - M t| + |M t - M θ₀| :=
            abs_sub_le _ _ _
        _ ≤ η / 2 := by linarith)
    (sub_self _)
  have e1 := natCast_mul_sampleMean (fun z ↦ F.logLik (θ₀ + h / √(n : ℝ)) z) O n ω
  have e2 := natCast_mul_sampleMean (fun z ↦ F.logLik θ₀ z) O n ω
  have e3 := natCast_mul_sampleMean (fun z ↦ F.score θ₀ z) O n ω
  rw [← hZ] at e3
  have hnd : (n : ℝ) * (h / √(n : ℝ)) ^ 2 = h ^ 2 := by
    rw [div_pow, Real.sq_sqrt hn'.le]; field_simp
  have key : F.logLikRatio O θ₀ (θ₀ + h / √(n : ℝ)) n ω -
      (h * ((√(n : ℝ))⁻¹ * ∑ i ∈ range n, F.score θ₀ (O i ω)) - h ^ 2 * F.fisherInfo θ₀ / 2) =
      (n : ℝ) * (sampleMean (fun z ↦ F.logLik (θ₀ + h / √(n : ℝ)) z) O n ω -
        (θ₀ + h / √(n : ℝ) - θ₀) * Z - (sampleMean (fun z ↦ F.logLik θ₀ z) O n ω -
        (θ₀ - θ₀) * Z) - M θ₀ * (θ₀ + h / √(n : ℝ) - θ₀) ^ 2 / 2) := by
    rw [logLikRatio, Finset.sum_sub_distrib, ← e1, ← e2, ← e3, hMI]
    linear_combination (-(F.fisherInfo θ₀) / 2) * hnd
  rw [Real.dist_eq, sub_zero, key, abs_mul, abs_of_pos hn']
  calc (n : ℝ) * |_| ≤ n * (η / 2 * (θ₀ + h / √(n : ℝ) - θ₀) ^ 2) :=
        mul_le_mul_of_nonneg_left hR hn'.le
    _ = η / 2 * h ^ 2 := by rw [add_sub_cancel_left, ← hnd]; ring
    _ < ε := by
        rw [hηdef]
        have : ε / (h ^ 2 + 1) * h ^ 2 < ε := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith
        nlinarith

end ParametricFamily

end CausalInference
