/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.MaximumLikelihoodNormality
public import CausalInference.Estimation.LimitLaws
public import CausalInference.Estimation.DeltaMethod

/-!
# The Wald, score and likelihood ratio tests

For a real parameter and an i.i.d. sample of size `n` from `P_θ₀`, the three classical
statistics for the null hypothesis `θ = θ₀` are

* the Wald statistic `W_n = n (θ̂_n - θ₀)² Î_n`, with `Î_n` the information `I(θ₀)` or any
  consistent estimate of it, such as `I(θ̂_n)`;
* the score statistic `R_n = (n^{-1/2} ∑_{i < n} s(θ₀; O_i))² / I(θ₀)`;
* the likelihood ratio statistic `Λ_n = 2 ∑_{i < n} (ℓ(θ̂_n; O_i) - ℓ(θ₀; O_i))`.

Under the null each converges in distribution to the chi-square law with one degree of freedom,
the law of the square of a standard Gaussian. The likelihood ratio statistic differs from the Wald
statistic by a term that tends to zero in probability (second order Taylor expansion of the
log-likelihood at its maximizer), and so does the score statistic (asymptotic linearity of the
estimator): the three tests are asymptotically equivalent under the null.

## Main definitions

* `CausalInference.chiSquaredOne`: the chi-square law with one degree of freedom.
* `CausalInference.waldStat`, `CausalInference.ParametricFamily.scoreStat`,
  `CausalInference.ParametricFamily.lrStat`.

## Main results

* `CausalInference.gaussianReal_map_sq_div`: `X² / v` has law `χ²₁` when `X ~ N(0, v)`, `v ≠ 0`.
* `CausalInference.waldStat_tendstoInDistribution`: the Wald statistic, with known or
  consistently estimated information.
* `CausalInference.ParametricFamily.scoreStat_tendstoInDistribution`: the score statistic.
* `CausalInference.ParametricFamily.lrStat_sub_waldStat_tendstoInMeasure` and
  `scoreStat_sub_waldStat_tendstoInMeasure`: asymptotic equivalence with the Wald statistic.
* `CausalInference.ParametricFamily.lrStat_tendstoInDistribution`: **Wilks' theorem**.

The instance in which every hypothesis is checked is in
`CausalInference.Estimation.BernoulliLikelihoodTests`.

References: S. S. Wilks (1938), *The large-sample distribution of the likelihood ratio for
testing composite hypotheses*, Annals of Mathematical Statistics; A. Wald (1943), *Tests of
statistical hypotheses concerning several parameters when the number of observations is large*,
Transactions of the American Mathematical Society; C. R. Rao (1948), *Large sample tests of
statistical hypotheses concerning several parameters with applications to problems of
estimation*, Proceedings of the Cambridge Philosophical Society; A. W. van der Vaart (1998),
*Asymptotic Statistics*, chapter 16.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Metric
open scoped Topology ENNReal NNReal

namespace CausalInference

/-- The chi-square law with one degree of freedom: the law of `Z²` for a standard Gaussian `Z`. -/
noncomputable def chiSquaredOne : Measure ℝ :=
  (gaussianReal 0 1).map fun x ↦ x ^ 2

instance : IsProbabilityMeasure chiSquaredOne :=
  (Measure.isProbabilityMeasure_map_iff (by fun_prop)).2 inferInstance

/-- **The square of a centered Gaussian, scaled by its variance, is chi-square**: if `v ≠ 0`,
the image of `N(0, v)` under `x ↦ x² / v` is `χ²₁`. -/
theorem gaussianReal_map_sq_div {v : ℝ≥0} (hv : v ≠ 0) :
    (gaussianReal 0 v).map (fun x ↦ x ^ 2 / (v : ℝ)) = chiSquaredOne := by
  have hv' : (0 : ℝ) < v := by positivity
  have hg : gaussianReal 0 v = (gaussianReal 0 1).map (fun x ↦ √(v : ℝ) * x) := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext; simp [Real.sq_sqrt hv'.le]
  rw [hg, Measure.map_map (by fun_prop) (by fun_prop), chiSquaredOne]
  congr 1
  funext x
  simp only [Function.comp_apply, mul_pow, Real.sq_sqrt hv'.le]
  field_simp

/-- A random variable `Y ~ N(0, v)` with `v ≠ 0` makes `Y² / v` chi-square. -/
theorem _root_.ProbabilityTheory.HasLaw.sq_div_chiSquaredOne {Ω' : Type*}
    {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} {Y : Ω' → ℝ} {v : ℝ≥0}
    (hY : HasLaw Y (gaussianReal 0 v) P') (hv : v ≠ 0) :
    HasLaw (fun ω ↦ Y ω ^ 2 / (v : ℝ)) chiSquaredOne P' :=
  HasLaw.fun_comp (Y := fun x : ℝ ↦ x ^ 2 / (v : ℝ))
    ⟨(by fun_prop : Measurable fun x : ℝ ↦ x ^ 2 / (v : ℝ)).aemeasurable,
      gaussianReal_map_sq_div hv⟩ hY

section Wald

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The Wald statistic `n (θ̂_n - θ₀)² Î_n` for the null `θ = θ₀`, with information `Î_n`. -/
noncomputable def waldStat (θh : ℕ → Ω → ℝ) (θ₀ : ℝ) (Ih : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  n * (θh n ω - θ₀) ^ 2 * Ih n ω

/-- `n x² = (√n x)²`. -/
lemma natCast_mul_sq_eq (n : ℕ) (x : ℝ) : (n : ℝ) * x ^ 2 = (√(n : ℝ) * x) ^ 2 := by
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]

/-- **The Wald test.** If `√n (θ̂_n - θ₀)` converges in distribution to `N(0, I⁻¹)` with
`I > 0` and `Î_n → I` in probability (`Î_n = I` for the known information), then
`W_n = n (θ̂_n - θ₀)² Î_n` converges in distribution to every variable with law `χ²₁`. -/
theorem waldStat_tendstoInDistribution {θh : ℕ → Ω → ℝ} {θ₀ I : ℝ} (hI : 0 < I)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → ℝ} (hY : HasLaw Y (gaussianReal 0 I⁻¹.toNNReal) P')
    (hN : TendstoInDistribution (fun (n : ℕ) ω ↦ √n * (θh n ω - θ₀)) atTop Y (fun _ ↦ μ) P')
    {Ih : ℕ → Ω → ℝ} (hIh : TendstoInMeasure μ Ih atTop (fun _ ↦ I))
    (hIhm : ∀ n, AEMeasurable (Ih n) μ)
    {Ω'' : Type*} {mΩ'' : MeasurableSpace Ω''} {P'' : Measure Ω''} [IsProbabilityMeasure P'']
    {W : Ω'' → ℝ} (hW : HasLaw W chiSquaredOne P'') :
    TendstoInDistribution (waldStat θh θ₀ Ih) atTop W (fun _ ↦ μ) P'' := by
  have hv : I⁻¹.toNNReal ≠ 0 := by simpa using hI
  have hvI : ((I⁻¹.toNNReal : ℝ≥0) : ℝ) = I⁻¹ := Real.coe_toNNReal _ (inv_nonneg.2 hI.le)
  have h := hN.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : ℝ × ℝ ↦ p.1 ^ 2 * p.2) (by fun_prop) hIh hIhm
  have hlaw : HasLaw (fun ω ↦ Y ω ^ 2 * I) chiSquaredOne P' := by
    have := hY.sq_div_chiSquaredOne hv
    rw [hvI] at this
    simpa [div_inv_eq_mul] using this
  convert h.of_hasLaw hlaw hW using 1
  funext n ω
  simp only [waldStat, natCast_mul_sq_eq]

end Wald

namespace ParametricFamily

variable {S : Type*} [MeasurableSpace S] {F : ParametricFamily ℝ S} {Ω : Type*}
  {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] {O : ℕ → Ω → S} {θ₀ : ℝ}

/-- The score statistic `(n^{-1/2} ∑_{i < n} s(θ₀; O_i))² / I(θ₀)`. -/
noncomputable def scoreStat (F : ParametricFamily ℝ S) (O : ℕ → Ω → S) (θ₀ : ℝ) (n : ℕ)
    (ω : Ω) : ℝ :=
  ((√(n : ℝ))⁻¹ * ∑ i ∈ range n, F.score θ₀ (O i ω)) ^ 2 / F.fisherInfo θ₀

/-- The likelihood ratio statistic `2 ∑_{i < n} (ℓ(θ̂_n; O_i) - ℓ(θ₀; O_i))`. -/
noncomputable def lrStat (F : ParametricFamily ℝ S) (O : ℕ → Ω → S) (θh : ℕ → Ω → ℝ) (θ₀ : ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  2 * ∑ i ∈ range n, (F.logLik (θh n ω) (O i ω) - F.logLik θ₀ (O i ω))

/-- **The central limit theorem for the score**: if `θ₀` is a regular point and the observations
have law `P_θ₀`, `n^{-1/2} ∑_{i < n} s(θ₀; O_i)` converges in distribution to `N(0, I(θ₀))`. -/
theorem sum_score_tendstoInDistribution (hO : IsIIDSample O μ) (hlaw : μ.map (O 0) = F.law θ₀)
    (hreg : F.IsRegularAt θ₀) (hm : Measurable (F.score θ₀))
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → ℝ} (hY : HasLaw Y (gaussianReal 0 (F.fisherInfo θ₀).toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω ↦ (√(n : ℝ))⁻¹ * ∑ i ∈ range n, F.score θ₀ (O i ω))
      atTop Y (fun _ ↦ μ) P' := by
  have hθ₀ : θ₀ ∈ F.Θ := mem_of_mem_nhds hreg.mem_nhds
  have := isProbabilityMeasure_law hθ₀
  have hX := hO.aemeasurable 0
  have hφ := hO.comp hm
  have hzero : μ[fun ω ↦ F.score θ₀ (O 0 ω)] = 0 := by
    rw [← integral_map hX hm.aestronglyMeasurable, hlaw, hreg.integral_score_eq_zero]
  have hB : MemLp (fun ω ↦ F.score θ₀ (O 0 ω)) 2 μ :=
    (memLp_map_measure_iff hm.aestronglyMeasurable hX).1 (by rw [hlaw]; exact hreg.memLp_score)
  have hvar : Var[fun ω ↦ F.score θ₀ (O 0 ω); μ] = F.fisherInfo θ₀ := by
    rw [variance_of_integral_eq_zero hB.aemeasurable hzero,
      integral_score_sq_eq_fisherInfo hX hlaw hm]
  have h := tendstoInDistribution_inv_sqrt_mul_sum_sub (X := fun i ω ↦ F.score θ₀ (O i ω))
    (by rw [hvar]; exact hY) hB hφ.indep hφ.ident
  simpa [hzero] using h

/-- **The score test.** If `θ₀` is a regular point with positive information and the
observations have law `P_θ₀`, the score statistic converges in distribution to every variable
with law `χ²₁`. No estimator is involved. -/
theorem scoreStat_tendstoInDistribution (hO : IsIIDSample O μ) (hlaw : μ.map (O 0) = F.law θ₀)
    (hreg : F.IsRegularAt θ₀) (hm : Measurable (F.score θ₀)) (hI : 0 < F.fisherInfo θ₀)
    {Ω'' : Type*} {mΩ'' : MeasurableSpace Ω''} {P'' : Measure Ω''} [IsProbabilityMeasure P'']
    {W : Ω'' → ℝ} (hW : HasLaw W chiSquaredOne P'') :
    TendstoInDistribution (F.scoreStat O θ₀) atTop W (fun _ ↦ μ) P'' := by
  set v := (F.fisherInfo θ₀).toNNReal
  have hv : v ≠ 0 := by simpa [v] using hI
  have hvI : (v : ℝ) = F.fisherInfo θ₀ := Real.coe_toNNReal _ hI.le
  have h0 := sum_score_tendstoInDistribution hO hlaw hreg hm (P' := gaussianReal 0 v) (Y := id)
    HasLaw.id
  have h := h0.continuous_comp (g := fun x ↦ x ^ 2 / (v : ℝ)) (by fun_prop)
  have h' := h.of_hasLaw (HasLaw.id.sq_div_chiSquaredOne hv) hW
  convert h' using 1
  funext n ω
  simp [scoreStat, hvI]

/-! ### Wilks' theorem -/

/-- **Second order expansion at a critical point.** If on `[[a, b]]` the function `g` has
derivative `g'`, `g'` has derivative `g''` with `|g'' t - c| ≤ η`, and `g' a = 0`, then
`|g b - g a - c (b - a)² / 2| ≤ η (b - a)²`. -/
theorem abs_sub_sub_le_of_hasDerivAt_two {g g' g'' : ℝ → ℝ} {a b c η : ℝ}
    (hg : ∀ t ∈ Set.uIcc a b, HasDerivAt g (g' t) t)
    (hg' : ∀ t ∈ Set.uIcc a b, HasDerivAt g' (g'' t) t)
    (hb : ∀ t ∈ Set.uIcc a b, |g'' t - c| ≤ η) (ha : g' a = 0) :
    |g b - g a - c * (b - a) ^ 2 / 2| ≤ η * (b - a) ^ 2 := by
  set k : ℝ → ℝ := fun t ↦ g t - g a - c * (t - a) ^ 2 / 2 with hk
  set k' : ℝ → ℝ := fun t ↦ g' t - c * (t - a) with hk'
  have hkd : ∀ t ∈ Set.uIcc a b, HasDerivAt k (k' t) t := fun t ht ↦ by
    have := (((hg t ht).sub_const (g a)).sub
      ((((hasDerivAt_id' t).sub_const a).pow 2).const_mul c |>.div_const 2))
    convert this using 1
    simp only [hk', Nat.cast_ofNat]; ring
  have hk'd : ∀ t ∈ Set.uIcc a b, HasDerivAt k' (g'' t - c) t := fun t ht ↦ by
    have := (hg' t ht).sub (((hasDerivAt_id' t).sub_const a).const_mul c)
    convert this using 1
    ring
  have hk'b : ∀ t ∈ Set.uIcc a b, |k' t| ≤ η * |b - a| := by
    intro t ht
    have hsub : Set.uIcc a t ⊆ Set.uIcc a b := Set.uIcc_subset_uIcc Set.left_mem_uIcc ht
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := k') (s := Set.uIcc a t)
      (fun x hx ↦ (hk'd x (hsub hx)).hasDerivWithinAt) (fun x hx ↦ hb x (hsub hx))
      (convex_uIcc _ _) Set.left_mem_uIcc Set.right_mem_uIcc
    have hka : k' a = 0 := by simp [hk', ha]
    rw [hka, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at h
    have hη : 0 ≤ η := (abs_nonneg _).trans (hb a Set.left_mem_uIcc)
    calc |k' t| ≤ η * |t - a| := h
      _ ≤ η * |b - a| := mul_le_mul_of_nonneg_left (Set.abs_sub_left_of_mem_uIcc ht) hη
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := k) (s := Set.uIcc a b)
    (fun x hx ↦ (hkd x hx).hasDerivWithinAt) hk'b (convex_uIcc _ _) Set.left_mem_uIcc
    Set.right_mem_uIcc
  have hka : k a = 0 := by simp [hk]
  rw [hka, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at h
  calc |g b - g a - c * (b - a) ^ 2 / 2| = |k b| := rfl
    _ ≤ η * |b - a| * |b - a| := h
    _ = η * (b - a) ^ 2 := by rw [mul_assoc, ← abs_mul, ← sq, abs_sq]

omit [IsProbabilityMeasure μ] in
/-- A sequence dominated, for every `η > 0` and with probability tending to one, by `η` times
the square of a sequence bounded in probability tends to zero in probability. -/
theorem tendstoInMeasure_zero_of_abs_le_mul_sq {A X : ℕ → Ω → ℝ}
    (hX : BoundedInProbability μ (fun n ω ↦ ‖X n ω‖))
    (h : ∀ η : ℝ, 0 < η → WithProbTendingToOne μ (fun n ↦ {ω | |A n ω| ≤ η * X n ω ^ 2})) :
    TendstoInMeasure μ A atTop 0 := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro κ hκ
  obtain ⟨M, hM, hXM⟩ := hX (κ / 2) (ENNReal.half_pos hκ.ne')
  have hη : 0 < ε / (2 * M ^ 2) := by positivity
  filter_upwards [hXM, (h _ hη).eventually_le (ENNReal.half_pos hκ.ne')] with n h1 h2
  calc μ {ω | ε ≤ dist (A n ω) ((0 : ℕ → Ω → ℝ) n ω)}
      ≤ μ ({ω | |A n ω| ≤ ε / (2 * M ^ 2) * X n ω ^ 2}ᶜ ∪ {ω | M ≤ |‖X n ω‖|}) := by
        refine measure_mono fun ω hω ↦ ?_
        simp only [Set.mem_ofPred_eq, Pi.zero_apply, Real.dist_eq, sub_zero] at hω
        by_cases hE : |A n ω| ≤ ε / (2 * M ^ 2) * X n ω ^ 2
        · right
          simp only [Set.mem_ofPred_eq, Real.norm_eq_abs, abs_abs]
          by_contra hlt
          push Not at hlt
          have hsq : X n ω ^ 2 < M ^ 2 := by nlinarith [abs_nonneg (X n ω), sq_abs (X n ω)]
          have : ε / (2 * M ^ 2) * X n ω ^ 2 ≤ ε / (2 * M ^ 2) * M ^ 2 :=
            mul_le_mul_of_nonneg_left hsq.le hη.le
          have he : ε / (2 * M ^ 2) * M ^ 2 = ε / 2 := by field_simp
          linarith
        · left; exact hE
    _ ≤ μ {ω | |A n ω| ≤ ε / (2 * M ^ 2) * X n ω ^ 2}ᶜ + μ {ω | M ≤ |‖X n ω‖|} :=
        measure_union_le _ _
    _ ≤ κ / 2 + κ / 2 := add_le_add h2 h1
    _ = κ := ENNReal.add_halves κ

omit [MeasurableSpace S] [IsProbabilityMeasure μ] in
/-- `n` times a sample mean is the sum. -/
lemma natCast_mul_sampleMean (f : S → ℝ) (O : ℕ → Ω → S) (n : ℕ) (ω : Ω) :
    (n : ℝ) * sampleMean f O n ω = ∑ i ∈ range n, f (O i ω) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [sampleMean, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hn.ne'), one_mul]

/-- **The likelihood ratio and Wald statistics are asymptotically equivalent.** Under the
hypotheses of `mle_isAsymptoticallyLinear` with the root condition, and `θ ↦ ℓ(θ; z)` having
derivative `s(θ; z)` on the ball, `Λ_n - n (θ̂_n - θ₀)² I(θ₀) → 0` in probability. With
probability tending to one, the second order expansion of `n⁻¹ ℓ_n` at its critical point `θ̂_n`
(`abs_sub_sub_le_of_hasDerivAt_two`) gives `|Λ_n - W_n| ≤ η n (θ̂_n - θ₀)²`, and
`√n (θ̂_n - θ₀)` is bounded in probability. -/
theorem lrStat_sub_waldStat_tendstoInMeasure (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = F.law θ₀) (hreg : F.IsRegularAt θ₀) {r : ℝ}
    (hs : F.IsScoreRegular θ₀ r) (hI : 0 < F.fisherInfo θ₀)
    (hdl : ∀ᵐ z ∂F.law θ₀, ∀ θ ∈ closedBall θ₀ r,
      HasDerivAt (fun u ↦ F.logLik u z) (F.score θ z) θ)
    {θh : ℕ → Ω → ℝ} (hθm : ∀ n, AEMeasurable (θh n) μ) (hθ : IsConsistent θh θ₀ μ)
    (hroot : WithProbTendingToOne μ (fun n ↦ {ω | ∑ i ∈ range n, F.score (θh n ω) (O i ω) = 0})) :
    TendstoInMeasure μ (F.lrStat O θh θ₀ - waldStat θh θ₀ (fun _ _ ↦ F.fisherInfo θ₀)) atTop 0 := by
  obtain ⟨-, -, hinfo⟩ := hreg.information_equality
  obtain ⟨H, hH, hdom⟩ := hs.dominated
  have hN := mle_tendstoInDistribution hO hlaw hreg hs hI hθm hθ hroot
    (P' := gaussianReal 0 (F.fisherInfo θ₀)⁻¹.toNNReal) (Y := id) HasLaw.id
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
  refine tendstoInMeasure_zero_of_abs_le_mul_sq hN.boundedInProbability fun η hη ↦ ?_
  obtain ⟨δ, hδ, hMδ⟩ := Metric.continuousAt_iff.1 hMat (η / 4) (by positivity)
  have hδr : 0 < min δ r := lt_min hδ hs.pos
  refine ((((TendstoInMeasure.withProbTendingToOne_dist_lt hθ hδr).inter
    (hunif (η / 4) (by positivity))).inter (WithProbTendingToOne.of_ae (hO.ae_forall hboth))).inter
    hroot).mono fun n ω hω ↦ ?_
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hω
  simp only [Set.mem_ofPred_eq] at h1 h2 h3 h4 ⊢
  set a := θh n ω with ha
  have hmem : ∀ t ∈ Set.uIcc a θ₀, dist t θ₀ < min δ r := fun t ht ↦ by
    rw [Real.dist_eq, abs_sub_comm]
    exact lt_of_le_of_lt (Set.abs_sub_right_of_mem_uIcc ht) (by rwa [abs_sub_comm, ← Real.dist_eq])
  have hball : ∀ t ∈ Set.uIcc a θ₀, t ∈ closedBall θ₀ r := fun t ht ↦
    mem_closedBall.2 ((hmem t ht).le.trans (min_le_right _ _))
  have hR := abs_sub_sub_le_of_hasDerivAt_two (a := a) (b := θ₀) (c := M θ₀) (η := η / 2)
    (g := fun t ↦ sampleMean (fun z ↦ F.logLik t z) O n ω)
    (g' := fun t ↦ sampleMean (fun z ↦ F.score t z) O n ω)
    (g'' := fun t ↦ sampleMean (fun z ↦ F.hessLogLik t z) O n ω)
    (fun t ht ↦ (HasDerivAt.fun_sum fun i _ ↦ (h3 i t (hball t ht)).1).const_mul _)
    (fun t ht ↦ (HasDerivAt.fun_sum fun i _ ↦ (h3 i t (hball t ht)).2).const_mul _)
    (fun t ht ↦ by
      have e1 := h2 t (hball t ht)
      have e2 := hMδ (lt_of_lt_of_le (hmem t ht) (min_le_left _ _))
      rw [Real.dist_eq] at e1 e2
      calc |sampleMean (fun z ↦ F.hessLogLik t z) O n ω - M θ₀|
          ≤ |sampleMean (fun z ↦ F.hessLogLik t z) O n ω - M t| + |M t - M θ₀| :=
            abs_sub_le _ _ _
        _ ≤ η / 2 := by linarith)
    (by simp [sampleMean, h4])
  have key : (F.lrStat O θh θ₀ - waldStat θh θ₀ fun _ _ ↦ F.fisherInfo θ₀) n ω =
      -(2 * n) * (sampleMean (fun z ↦ F.logLik θ₀ z) O n ω -
        sampleMean (fun z ↦ F.logLik a z) O n ω - M θ₀ * (θ₀ - a) ^ 2 / 2) := by
    simp only [Pi.sub_apply, lrStat, waldStat, Finset.sum_sub_distrib,
      ← natCast_mul_sampleMean, hMI, ← ha]
    ring
  rw [key, abs_mul, abs_neg, abs_of_nonneg (by positivity), ← natCast_mul_sq_eq]
  calc 2 * (n : ℝ) * |sampleMean (fun z ↦ F.logLik θ₀ z) O n ω -
        sampleMean (fun z ↦ F.logLik a z) O n ω - M θ₀ * (θ₀ - a) ^ 2 / 2|
      ≤ 2 * n * (η / 2 * (θ₀ - a) ^ 2) := mul_le_mul_of_nonneg_left hR (by positivity)
    _ = η * (n * (a - θ₀) ^ 2) := by ring

/-- **Wilks' theorem.** Under the hypotheses of `lrStat_sub_waldStat_tendstoInMeasure` and joint
measurability of `(θ, z) ↦ ℓ(θ; z)`, the likelihood ratio statistic
`Λ_n = 2 ∑_{i < n} (ℓ(θ̂_n; O_i) - ℓ(θ₀; O_i))` converges in distribution to every variable
with law `χ²₁`. -/
theorem lrStat_tendstoInDistribution (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = F.law θ₀) (hreg : F.IsRegularAt θ₀) {r : ℝ}
    (hs : F.IsScoreRegular θ₀ r) (hI : 0 < F.fisherInfo θ₀)
    (hdl : ∀ᵐ z ∂F.law θ₀, ∀ θ ∈ closedBall θ₀ r,
      HasDerivAt (fun u ↦ F.logLik u z) (F.score θ z) θ)
    (hjoint : Measurable fun p : ℝ × S ↦ F.logLik p.1 p.2)
    {θh : ℕ → Ω → ℝ} (hθm : ∀ n, AEMeasurable (θh n) μ) (hθ : IsConsistent θh θ₀ μ)
    (hroot : WithProbTendingToOne μ (fun n ↦ {ω | ∑ i ∈ range n, F.score (θh n ω) (O i ω) = 0}))
    {Ω'' : Type*} {mΩ'' : MeasurableSpace Ω''} {P'' : Measure Ω''} [IsProbabilityMeasure P'']
    {W : Ω'' → ℝ} (hW : HasLaw W chiSquaredOne P'') :
    TendstoInDistribution (F.lrStat O θh θ₀) atTop W (fun _ ↦ μ) P'' := by
  have hN := mle_tendstoInDistribution hO hlaw hreg hs hI hθm hθ hroot
    (P' := gaussianReal 0 (F.fisherInfo θ₀)⁻¹.toNNReal) (Y := id) HasLaw.id
  have hWald := waldStat_tendstoInDistribution hI HasLaw.id hN
    (tendstoInMeasure_const (F.fisherInfo θ₀)) (fun _ ↦ aemeasurable_const) hW
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ W hWald
    (lrStat_sub_waldStat_tendstoInMeasure hO hlaw hreg hs hI hdl hθm hθ hroot) fun n ↦ ?_
  have hX := hO.aemeasurable
  exact (Finset.aemeasurable_fun_sum _ fun i _ ↦
    (hjoint.comp_aemeasurable ((hθm n).prodMk (hX i))).sub
      (hjoint.comp_aemeasurable (aemeasurable_const.prodMk (hX i)))).const_mul 2

/-- **The score and Wald statistics are asymptotically equivalent.** Under the hypotheses of
`mle_isAsymptoticallyLinear_of_root`, `R_n - n (θ̂_n - θ₀)² I(θ₀) → 0` in probability. With
`D_n = √n (θ̂_n - θ₀) - I(θ₀)⁻¹ S_n` and `S_n = n^{-1/2} ∑_{i < n} s(θ₀; O_i)`, the difference is
`-(I(θ₀) D_n² + 2 D_n S_n)`; `D_n → 0` by asymptotic linearity and `S_n` is bounded in
probability by the central limit theorem. -/
theorem scoreStat_sub_waldStat_tendstoInMeasure (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = F.law θ₀) (hreg : F.IsRegularAt θ₀) {r : ℝ}
    (hs : F.IsScoreRegular θ₀ r) (hI : 0 < F.fisherInfo θ₀) {θh : ℕ → Ω → ℝ}
    (hθ : IsConsistent θh θ₀ μ)
    (hroot : WithProbTendingToOne μ (fun n ↦ {ω | ∑ i ∈ range n, F.score (θh n ω) (O i ω) = 0})) :
    TendstoInMeasure μ (F.scoreStat O θ₀ - waldStat θh θ₀ (fun _ _ ↦ F.fisherInfo θ₀)) atTop
      0 := by
  have hI0 : F.fisherInfo θ₀ ≠ 0 := hI.ne'
  have hlin := mle_isAsymptoticallyLinear_of_root hO hlaw hreg hs hI hθ hroot
  have hD0 : TendstoInMeasure μ (fun (n : ℕ) ω ↦ √(n : ℝ) * (θh n ω - θ₀) -
      (√(n : ℝ))⁻¹ * ∑ i ∈ range n, (F.fisherInfo θ₀)⁻¹ * F.score θ₀ (O i ω)) atTop
      (fun _ ↦ 0) := hlin.remainder
  have hSb : BoundedInProbability μ
      (fun (n : ℕ) ω ↦ (√(n : ℝ))⁻¹ * ∑ i ∈ range n, F.score θ₀ (O i ω)) := by
    have h := (sum_score_tendstoInDistribution hO hlaw hreg hs.measurable_score
      (P' := gaussianReal 0 (F.fisherInfo θ₀).toNNReal) (Y := id) HasLaw.id).boundedInProbability
    intro κ hκ
    obtain ⟨M, hM, hev⟩ := h κ hκ
    exact ⟨M, hM, by simpa only [Real.norm_eq_abs, abs_abs] using hev⟩
  have hDD := tendstoInMeasure_mul_of_bounded hD0
    (boundedInProbability_of_tendstoInMeasure hD0)
  have hDS := tendstoInMeasure_mul_of_bounded hD0 hSb
  have hpair := (hDD.prodMk (a := (0 : ℝ)) (b := (0 : ℝ)) hDS).comp_continuousAt
    (g := fun p : ℝ × ℝ ↦ -(F.fisherInfo θ₀ * p.1 + 2 * p.2)) (by fun_prop)
  refine hpair.congr' (Eventually.of_forall fun n ↦ Eventually.of_forall fun ω ↦ ?_)
    (Eventually.of_forall fun ω ↦ by simp only [Pi.zero_apply]; ring)
  have hsum : (√(n : ℝ))⁻¹ * ∑ i ∈ range n, (F.fisherInfo θ₀)⁻¹ * F.score θ₀ (O i ω) =
      (F.fisherInfo θ₀)⁻¹ * ((√(n : ℝ))⁻¹ * ∑ i ∈ range n, F.score θ₀ (O i ω)) := by
    rw [← mul_sum]; ring
  change -(F.fisherInfo θ₀ * ((√(n : ℝ) * (θh n ω - θ₀) -
      (√(n : ℝ))⁻¹ * ∑ i ∈ range n, (F.fisherInfo θ₀)⁻¹ * F.score θ₀ (O i ω)) *
      (√(n : ℝ) * (θh n ω - θ₀) -
      (√(n : ℝ))⁻¹ * ∑ i ∈ range n, (F.fisherInfo θ₀)⁻¹ * F.score θ₀ (O i ω))) +
      2 * ((√(n : ℝ) * (θh n ω - θ₀) -
      (√(n : ℝ))⁻¹ * ∑ i ∈ range n, (F.fisherInfo θ₀)⁻¹ * F.score θ₀ (O i ω)) *
      ((√(n : ℝ))⁻¹ * ∑ i ∈ range n, F.score θ₀ (O i ω)))) =
    ((√(n : ℝ))⁻¹ * ∑ i ∈ range n, F.score θ₀ (O i ω)) ^ 2 / F.fisherInfo θ₀ -
      (n : ℝ) * (θh n ω - θ₀) ^ 2 * F.fisherInfo θ₀
  rw [hsum, natCast_mul_sq_eq]
  generalize √(n : ℝ) * (θh n ω - θ₀) = x
  generalize (√(n : ℝ))⁻¹ * ∑ i ∈ range n, F.score θ₀ (O i ω) = y
  field_simp
  ring

end ParametricFamily

end CausalInference
