/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.HajekConvolutionExamples

/-!
# A regular estimator that does not attain the Hájek bound

The Bernoulli sample family `bernoulli.pi n` (`n` independent Bernoulli(`p`) observations, one
parameter `p`) is regular at every `p₀ ∈ (0, 1)`: its score is the sum of the coordinate scores,
its information is `n / (p₀ (1 - p₀))`, its score is regular on the closed ball of radius
`min p₀ (1 - p₀) / 2`, and its log density has derivative the score on that ball.

For pairs (`n = 2`) the information is `I(p₀) = 2 / (p₀ (1 - p₀))`, so the Hájek bound is
`I(p₀)⁻¹ = p₀ (1 - p₀) / 2`. On a sample of pairs, the mean of the first coordinates is
asymptotically linear with influence function `(x₁, x₂) ↦ x₁ - p₀`, and it is regular in
Hájek's sense with limit `N(0, p₀ (1 - p₀))`: its law under the pair family is the law of the
sample proportion of the first coordinates, which is regular for the Bernoulli family. Its limit
variance is twice the bound, so by the equality case of the convolution theorem it is not
asymptotically linear in the efficient influence function
`I(p₀)⁻¹ s(p₀; x) = ((x₁ - p₀) + (x₂ - p₀)) / 2`. The mean of both coordinates is asymptotically
linear in the efficient influence function and attains the bound. At `p₀ = 1/4` the information
is `32/3`, the bound is `3/32`, and the first coordinate mean has limit variance `3/16`.

## Main results

* `CausalInference.ParametricFamily.bernoulli_pi_isRegularAt`,
  `CausalInference.ParametricFamily.bernoulli_pi_isScoreRegular`,
  `CausalInference.ParametricFamily.bernoulli_pi_fisherInfo`: regularity and information of the
  Bernoulli sample family.
* `CausalInference.ParametricFamily.firstCoordMean_isHajekRegular`: the first coordinate mean is
  regular with limit `N(0, p₀ (1 - p₀))`.
* `CausalInference.ParametricFamily.inv_fisherInfo_pair_lt`: the bound is strictly smaller.
* `CausalInference.ParametricFamily.firstCoordMean_not_isAsymptoticallyLinear`: the first
  coordinate mean is not asymptotically linear in the efficient influence function.
* `CausalInference.ParametricFamily.pairMean_attains_hajek_bound`: the mean of both coordinates
  attains the bound.

References: J. Hájek (1970), *A characterization of limiting distributions of regular
estimates*, Zeitschrift für Wahrscheinlichkeitstheorie und verwandte Gebiete; A. W. van der
Vaart (1998), *Asymptotic Statistics*, chapter 8.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Metric
open scoped Topology ENNReal NNReal

namespace CausalInference

namespace ParametricFamily

/-! ### The Bernoulli sample family -/

/-- The Bernoulli density has derivative `1` at a success and `-1` at a failure. -/
theorem bernoulli_hasDerivAt_density (u : ℝ) (b : Bool) :
    HasDerivAt (fun v ↦ bernoulli.density v b) (if b then 1 else -1) u := by
  cases b
  · simpa [bernoulli_density] using (hasDerivAt_id u).const_sub 1
  · simpa [bernoulli_density] using hasDerivAt_id' u

open scoped ContDiff in
/-- The Bernoulli density is smooth in the parameter. -/
theorem contDiff_bernoulli_density (b : Bool) :
    ContDiff ℝ ∞ (fun u ↦ bernoulli.density u b) := by
  cases b
  · simpa [bernoulli_density] using contDiff_const.sub contDiff_id
  · simp only [bernoulli_density, ite_true]
    exact contDiff_id

variable {n : ℕ}

/-- The likelihood of `n` Bernoulli observations is positive for `u ∈ (0, 1)`. -/
theorem bernoulli_pi_density_pos {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) (x : Fin n → Bool) :
    0 < (bernoulli.pi n).density u x := by
  rw [pi_density]
  exact Finset.prod_pos fun i _ ↦ bernoulli_density_pos hu (x i)

open scoped ContDiff in
/-- The likelihood of `n` Bernoulli observations is smooth in the parameter. -/
theorem contDiff_bernoulli_pi_density (x : Fin n → Bool) :
    ContDiff ℝ ∞ (fun u ↦ (bernoulli.pi n).density u x) := by
  simp only [pi_density]
  exact contDiff_prod fun i _ ↦ contDiff_bernoulli_density (x i)

/-- The log likelihood of `n` Bernoulli observations is the sum of the coordinate log
densities, for `u ∈ (0, 1)`. -/
theorem bernoulli_pi_logLik {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) (x : Fin n → Bool) :
    (bernoulli.pi n).logLik u x = ∑ i, bernoulli.logLik u (x i) := by
  rw [logLik, pi_density, Real.log_prod fun i _ ↦ (bernoulli_density_pos hu (x i)).ne']
  rfl

/-- The score of `n` Bernoulli observations is the sum of the coordinate scores. -/
theorem bernoulli_pi_score {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) (x : Fin n → Bool) :
    (bernoulli.pi n).score u x = ∑ i, bernoulli.score u (x i) :=
  pi_score (fun i ↦ bernoulli_density_pos hu (x i))
    fun i ↦ (bernoulli_hasDerivAt_density u (x i)).differentiableAt

/-- The log likelihood of `n` Bernoulli observations has derivative the score on `(0, 1)`. -/
theorem bernoulli_pi_hasDerivAt_logLik {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1)
    (x : Fin n → Bool) :
    HasDerivAt (fun v ↦ (bernoulli.pi n).logLik v x) ((bernoulli.pi n).score u x) u := by
  rw [bernoulli_pi_score hu]
  have h := HasDerivAt.fun_sum (u := Finset.univ) (A := fun i v ↦ bernoulli.logLik v (x i))
    fun i _ ↦ bernoulli_hasDerivAt_logLik hu (x i)
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioo.mem_nhds hu] with v hv using bernoulli_pi_logLik hv x

/-- The score of `n` Bernoulli observations has derivative the sum of the coordinate second
derivatives on `(0, 1)`. -/
theorem bernoulli_pi_hasDerivAt_score {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (x : Fin n → Bool) :
    HasDerivAt (fun u ↦ (bernoulli.pi n).score u x) (∑ i, bernoulli.hessLogLik t (x i)) t := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) (A := fun i u ↦ bernoulli.score u (x i))
    (A' := fun i ↦ bernoulli.hessLogLik t (x i)) (x := t) fun i _ ↦ by
      rw [bernoulli_hessLogLik ht]
      exact bernoulli_hasDerivAt_score ht (x i)
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioo.mem_nhds ht] with v hv using bernoulli_pi_score hv x

/-- The second derivative of the log likelihood of `n` Bernoulli observations is the sum of the
coordinate second derivatives on `(0, 1)`. -/
theorem bernoulli_pi_hessLogLik {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (x : Fin n → Bool) :
    (bernoulli.pi n).hessLogLik t x = ∑ i, bernoulli.hessLogLik t (x i) := by
  have heq : (fun u ↦ deriv (fun v ↦ (bernoulli.pi n).logLik v x) u) =ᶠ[𝓝 t]
      fun u ↦ (bernoulli.pi n).score u x := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
    exact (bernoulli_pi_hasDerivAt_logLik hu x).deriv
  rw [hessLogLik, heq.deriv_eq, (bernoulli_pi_hasDerivAt_score ht x).deriv]

/-- On the closed ball of radius `min p₀ (1 - p₀) / 2` the Bernoulli second derivative of the
log density is bounded by `(p₀ / 2)⁻² + ((1 - p₀) / 2)⁻²`. -/
theorem abs_bernoulli_hessLogLik_le {p₀ t : ℝ} (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (ht : t ∈ closedBall p₀ (min p₀ (1 - p₀) / 2)) (b : Bool) :
    |bernoulli.hessLogLik t b| ≤ ((p₀ / 2) ^ 2)⁻¹ + (((1 - p₀) / 2) ^ 2)⁻¹ := by
  have hq : 0 < 1 - p₀ := by linarith [hp₀.2]
  obtain ⟨h1, h2⟩ := le_of_mem_closedBall_half_min ht
  have ha : ((t ^ 2)⁻¹ : ℝ) ≤ ((p₀ / 2) ^ 2)⁻¹ :=
    inv_anti₀ (pow_pos (half_pos hp₀.1) 2) (pow_le_pow_left₀ (half_pos hp₀.1).le h1 2)
  have hb : (((1 - t) ^ 2)⁻¹ : ℝ) ≤ (((1 - p₀) / 2) ^ 2)⁻¹ :=
    inv_anti₀ (pow_pos (half_pos hq) 2) (pow_le_pow_left₀ (half_pos hq).le h2 2)
  have hc : 0 ≤ ((p₀ / 2) ^ 2)⁻¹ := by positivity
  have hd : 0 ≤ (((1 - p₀) / 2) ^ 2)⁻¹ := by positivity
  rw [bernoulli_hessLogLik (mem_Ioo_of_mem_closedBall hp₀ ht)]
  cases b
  · simp only [Bool.false_eq_true, ite_false, abs_neg]
    rw [abs_of_nonneg (by positivity)]; linarith
  · simp only [ite_true, abs_neg]
    rw [abs_of_nonneg (by positivity)]; linarith

/-- The Bernoulli second derivative of the log density is continuous on the closed ball of
radius `min p₀ (1 - p₀) / 2`. -/
theorem continuousOn_bernoulli_hessLogLik {p₀ : ℝ} (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1) (b : Bool) :
    ContinuousOn (fun u ↦ bernoulli.hessLogLik u b) (closedBall p₀ (min p₀ (1 - p₀) / 2)) := by
  have hIoo := fun t (ht : t ∈ closedBall p₀ (min p₀ (1 - p₀) / 2)) ↦
    mem_Ioo_of_mem_closedBall hp₀ ht
  refine ContinuousOn.congr (f := fun u ↦ if b then -(u ^ 2)⁻¹ else -((1 - u) ^ 2)⁻¹) ?_
    fun t ht ↦ bernoulli_hessLogLik (hIoo t ht) b
  cases b
  · exact (((continuousOn_const.sub continuousOn_id).pow 2).inv₀ fun t ht ↦
      pow_ne_zero 2 (by change (1 : ℝ) - t ≠ 0; linarith [(hIoo t ht).2])).neg
  · exact ((continuousOn_id.pow 2).inv₀ fun t ht ↦ pow_ne_zero 2 (hIoo t ht).1.ne').neg

/-- **The score of the Bernoulli sample family is regular** on the closed ball of radius
`min p₀ (1 - p₀) / 2`. -/
theorem bernoulli_pi_isScoreRegular (n : ℕ) {p₀ : ℝ} (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1) :
    (bernoulli.pi n).IsScoreRegular p₀ (min p₀ (1 - p₀) / 2) := by
  have hIoo := fun t (ht : t ∈ closedBall p₀ (min p₀ (1 - p₀) / 2)) ↦
    mem_Ioo_of_mem_closedBall hp₀ ht
  have := isProbabilityMeasure_law (F := bernoulli.pi n) hp₀
  refine ⟨half_pos (lt_min hp₀.1 (by linarith [hp₀.2])), .of_discrete, fun _ _ ↦ .of_discrete,
    ae_of_all _ fun x t ht ↦ ?_, ae_of_all _ fun x ↦ ?_,
    ⟨fun _ ↦ n * (((p₀ / 2) ^ 2)⁻¹ + (((1 - p₀) / 2) ^ 2)⁻¹), integrable_const _,
      ae_of_all _ fun x t ht ↦ ?_⟩⟩
  · rw [bernoulli_pi_hessLogLik (hIoo t ht)]
    exact bernoulli_pi_hasDerivAt_score (hIoo t ht) x
  · exact ContinuousOn.congr (continuousOn_finsetSum _ fun i _ ↦
      continuousOn_bernoulli_hessLogLik hp₀ (x i)) fun t ht ↦ bernoulli_pi_hessLogLik (hIoo t ht) x
  · rw [bernoulli_pi_hessLogLik (hIoo t ht)]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ ↦ abs_bernoulli_hessLogLik_le hp₀ ht (x i)).trans ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, le_refl]

/-- The log likelihood of the Bernoulli sample family has derivative the score on the closed
ball of radius `min p₀ (1 - p₀) / 2`. -/
theorem bernoulli_pi_hasDerivAt_logLik_closedBall (n : ℕ) {p₀ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ᵐ z ∂(bernoulli.pi n).law p₀, ∀ θ ∈ closedBall p₀ (min p₀ (1 - p₀) / 2),
      HasDerivAt (fun u ↦ (bernoulli.pi n).logLik u z) ((bernoulli.pi n).score θ z) θ :=
  ae_of_all _ fun z _ ht ↦ bernoulli_pi_hasDerivAt_logLik (mem_Ioo_of_mem_closedBall hp₀ ht) z

/-- **The Bernoulli sample family is regular** at every `p ∈ (0, 1)`. -/
theorem bernoulli_pi_isRegularAt (n : ℕ) {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    (bernoulli.pi n).IsRegularAt p := by
  have := isProbabilityMeasure_law (F := bernoulli) hp
  have hΘ : bernoulli.Θ ∈ 𝓝 p := isOpen_Ioo.mem_nhds hp
  have hreg := bernoulli_isRegularAt hp
  have hK : IsCompact (closedBall p (min p (1 - p))) := isCompact_closedBall _ _
  have hd2 : ∀ x : Fin n → Bool, ∃ C, ∀ u ∈ closedBall p (min p (1 - p)),
      ‖(bernoulli.pi n).densityDeriv2 u x‖ ≤ C := fun x ↦
    hK.exists_bound_of_continuousOn
      ((contDiff_bernoulli_pi_density x).iterate_deriv 2).continuous.continuousOn
  choose C hC using hd2
  refine ⟨?_, ⟨min p (1 - p), lt_min hp.1 (by linarith [hp.2]), ball_subset_Ioo p,
    ae_of_all _ fun x ↦ (contDiff_infty.1 (contDiff_bernoulli_pi_density x) 2).contDiffOn,
    fun _ ↦ (n : ℝ), C, integrable_const _, Integrable.of_finite,
    ae_of_all _ fun x u hu ↦ ⟨abs_bernoulli_pi_densityDeriv_le n x (ball_subset_Ioo p hu),
      by simpa [Real.norm_eq_abs] using hC x u (ball_subset_closedBall hu)⟩⟩,
    (pi_fisherInfo n hΘ hreg.derivInterchange.self_of_nhds hreg.ae_differentiableAt
      hreg.memLp_score).1⟩
  filter_upwards [isOpen_Ioo.mem_nhds hp] with u hu x
  exact iff_of_true (bernoulli_pi_density_pos hu x) (bernoulli_pi_density_pos hp x)

/-- **The information of `n` Bernoulli observations** is `n / (p (1 - p))`. -/
theorem bernoulli_pi_fisherInfo (n : ℕ) {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    (bernoulli.pi n).fisherInfo p = n / (p * (1 - p)) := by
  have hreg := bernoulli_isRegularAt hp
  rw [(pi_fisherInfo n (isOpen_Ioo.mem_nhds hp) hreg.derivInterchange.self_of_nhds
    hreg.ae_differentiableAt hreg.memLp_score).2, bernoulli_fisherInfo hp, mul_one_div]

/-! ### Pairs of Bernoulli observations -/

/-- The information of a pair of Bernoulli observations is `2 / (p (1 - p))`. -/
theorem fisherInfo_pair {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    (bernoulli.pi 2).fisherInfo p = 2 / (p * (1 - p)) := by
  rw [bernoulli_pi_fisherInfo 2 hp]
  norm_num

/-- The information of a pair of Bernoulli observations is positive. -/
theorem fisherInfo_pair_pos {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    0 < (bernoulli.pi 2).fisherInfo p := by
  rw [fisherInfo_pair hp]
  exact div_pos two_pos (mul_pos hp.1 (by linarith [hp.2]))

/-- **The Hájek bound for pairs** is `I(p)⁻¹ = p (1 - p) / 2`. -/
theorem inv_fisherInfo_pair {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    ((bernoulli.pi 2).fisherInfo p)⁻¹ = p * (1 - p) / 2 := by
  rw [fisherInfo_pair hp, inv_div]

/-- **The bound is strictly smaller than `p (1 - p)`.** -/
theorem inv_fisherInfo_pair_lt {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    ((bernoulli.pi 2).fisherInfo p)⁻¹ < p * (1 - p) := by
  rw [inv_fisherInfo_pair hp]
  have : 0 < p * (1 - p) := mul_pos hp.1 (by linarith [hp.2])
  linarith

/-- **The efficient influence function for pairs** is
`I(p)⁻¹ s(p; x) = ((x₁ - p) + (x₂ - p)) / 2`. -/
theorem inv_fisherInfo_pair_mul_score {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) (x : Fin 2 → Bool) :
    ((bernoulli.pi 2).fisherInfo p)⁻¹ * (bernoulli.pi 2).score p x =
      ((successIndicator (x 0) - p) + (successIndicator (x 1) - p)) / 2 := by
  rw [← bernoulli_inv_fisherInfo_mul_score hp, ← bernoulli_inv_fisherInfo_mul_score hp,
    bernoulli_pi_score hp, Fin.sum_univ_two, inv_fisherInfo_pair hp, bernoulli_inv_fisherInfo hp]
  ring

/-- The mean of the first coordinates of `m` observed pairs. -/
noncomputable def firstCoordMean (m : ℕ) (y : Fin m → Fin 2 → Bool) : ℝ :=
  bernoulliSampleMean m fun k ↦ y k 0

/-- The mean of both coordinates of `m` observed pairs. -/
noncomputable def pairMean (m : ℕ) (y : Fin m → Fin 2 → Bool) : ℝ :=
  (m : ℝ)⁻¹ * ∑ k, (successIndicator (y k 0) + successIndicator (y k 1)) / 2

/-- The first coordinates of a sample of pairs under `p` have the law of a Bernoulli sample. -/
theorem map_fst_pi_law (m : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) :
    (((bernoulli.pi 2).pi m).law θ).map (fun x k ↦ x k 0) = (bernoulli.pi m).law θ := by
  have := isProbabilityMeasure_law (F := bernoulli) hθ
  have hev : (Measure.pi fun _ : Fin 2 ↦ bernoulli.law θ).map (fun z ↦ z 0) = bernoulli.law θ :=
    (measurePreserving_eval (fun _ : Fin 2 ↦ bernoulli.law θ) 0).map_eq
  have : ∀ _ : Fin m, SigmaFinite ((Measure.pi fun _ : Fin 2 ↦ bernoulli.law θ).map
      (fun z ↦ z 0)) := fun _ ↦ by rw [hev]; infer_instance
  rw [pi_law (F := bernoulli.pi 2) m hθ, pi_law (F := bernoulli) 2 hθ,
    pi_law (F := bernoulli) m hθ]
  refine (Measure.pi_map_pi (μ := fun _ : Fin m ↦ Measure.pi fun _ : Fin 2 ↦ bernoulli.law θ)
    (f := fun _ z ↦ z 0) fun _ ↦ (measurable_pi_apply 0).aemeasurable).trans ?_
  simp only [hev]

/-- **The first coordinate mean is regular in Hájek's sense** for the pair family at every
`p₀ ∈ (0, 1)`, with limit `N(0, p₀ (1 - p₀))`. -/
theorem firstCoordMean_isHajekRegular {p₀ : ℝ} (hp : p₀ ∈ Set.Ioo (0 : ℝ) 1) :
    (bernoulli.pi 2).IsHajekRegular firstCoordMean p₀
      (gaussianReal 0 (p₀ * (1 - p₀)).toNNReal) := by
  have hB := bernoulliSampleMean_isHajekRegular hp
  refine ⟨fun _ ↦ .of_discrete, fun h f ↦ (hB.tendsto h f).congr' ?_⟩
  have ht : Tendsto (fun n : ℕ ↦ p₀ + h / √(n : ℝ)) atTop (𝓝 p₀) := by
    simpa using tendsto_const_nhds.add ((tendsto_const_nhds (x := h)).div_atTop
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop))
  filter_upwards [ht.eventually (isOpen_Ioo.mem_nhds hp)] with n hn
  rw [← map_fst_pi_law n hn, integral_map (Measurable.of_discrete).aemeasurable
    (Measurable.of_discrete).aestronglyMeasurable]
  rfl

variable {p₀ : ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {O : ℕ → Ω → Fin 2 → Bool}

omit [IsProbabilityMeasure μ] in
/-- The first coordinate mean of the first `n` pairs is a sample mean. -/
theorem firstCoordMean_eq_sampleMean (n : ℕ) (ω : Ω) :
    firstCoordMean n (fun i ↦ O i ω) = sampleMean (fun x ↦ successIndicator (x 0)) O n ω :=
  bernoulliSampleMean_eq_sampleMean (O := fun i ω ↦ O i ω 0) n ω

omit [IsProbabilityMeasure μ] in
/-- The mean of both coordinates of the first `n` pairs is a sample mean. -/
theorem pairMean_eq_sampleMean (n : ℕ) (ω : Ω) :
    pairMean n (fun i ↦ O i ω) =
      sampleMean (fun x ↦ (successIndicator (x 0) + successIndicator (x 1)) / 2) O n ω := by
  rw [pairMean, sampleMean, ← Fin.sum_univ_eq_sum_range
    (fun i ↦ (successIndicator (O i ω 0) + successIndicator (O i ω 1)) / 2)]

omit [IsProbabilityMeasure μ] in
/-- Under the pair family, a function of one pair has the integral it has under the product
of two Bernoulli laws, and is square integrable at the first observation. -/
theorem pair_integral_memLp (hO : IsIIDSample O μ) (hlaw : μ.map (O 0) = (bernoulli.pi 2).law p₀)
    (hp : p₀ ∈ Set.Ioo (0 : ℝ) 1) (g : (Fin 2 → Bool) → ℝ) :
    μ[fun ω ↦ g (O 0 ω)] = ∫ x, g x ∂(Measure.pi fun _ : Fin 2 ↦ bernoulli.law p₀) ∧
      MemLp (fun ω ↦ g (O 0 ω)) 2 μ := by
  have := isProbabilityMeasure_law (F := bernoulli.pi 2) hp
  have hm : Measurable g := .of_discrete
  refine ⟨?_, ?_⟩
  · rw [← integral_map (hO.aemeasurable 0) hm.aestronglyMeasurable, hlaw,
      pi_law (F := bernoulli) 2 hp]
  · have h2 : MemLp g 2 (μ.map (O 0)) := by rw [hlaw]; exact MemLp.of_discrete
    exact h2.comp_of_map (hO.aemeasurable 0)

/-- **The first coordinate mean is asymptotically linear** with influence function
`x ↦ x₁ - p₀`, which is not the efficient one. -/
theorem firstCoordMean_isAsymptoticallyLinear (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = (bernoulli.pi 2).law p₀) (hp : p₀ ∈ Set.Ioo (0 : ℝ) 1) :
    IsAsymptoticallyLinear (fun n ω ↦ firstCoordMean n fun i ↦ O i ω) p₀
      (fun x ↦ successIndicator (x 0) - p₀) O μ := by
  obtain ⟨hmean, h2⟩ := pair_integral_memLp hO hlaw hp fun x ↦ successIndicator (x 0)
  rw [(bernoulli_pi_coord (n := 2) hp 0).1] at hmean
  have hAL := sampleMean_isAsymptoticallyLinear (f := fun x : Fin 2 → Bool ↦
    successIndicator (x 0)) .of_discrete h2
  rw [hmean] at hAL
  have hT : (fun n ω ↦ firstCoordMean n fun i ↦ O i ω) =
      sampleMean (fun x ↦ successIndicator (x 0)) O :=
    funext fun n ↦ funext fun ω ↦ firstCoordMean_eq_sampleMean n ω
  rw [hT]
  exact hAL

/-- **The first coordinate mean is not asymptotically linear in the efficient influence
function**: its limit variance `p₀ (1 - p₀)` exceeds the bound `I(p₀)⁻¹ = p₀ (1 - p₀) / 2`, so the
equality case of the convolution theorem fails. -/
theorem firstCoordMean_not_isAsymptoticallyLinear (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = (bernoulli.pi 2).law p₀) (hp : p₀ ∈ Set.Ioo (0 : ℝ) 1) :
    ¬ IsAsymptoticallyLinear (fun n ω ↦ firstCoordMean n fun i ↦ O i ω) p₀
      (fun x ↦ ((bernoulli.pi 2).fisherInfo p₀)⁻¹ * (bernoulli.pi 2).score p₀ x) O μ := by
  rw [← hajek_eq_iff_isAsymptoticallyLinear hO hlaw (bernoulli_pi_isRegularAt 2 hp)
    (bernoulli_pi_isScoreRegular 2 hp) (bernoulli_pi_hasDerivAt_logLik_closedBall 2 hp)
    (fisherInfo_pair_pos hp) (firstCoordMean_isHajekRegular hp),
    Real.coe_toNNReal _ (mul_pos hp.1 (by linarith [hp.2])).le]
  exact (inv_fisherInfo_pair_lt hp).ne'

/-- **The Hájek bound for pairs**: every estimator sequence regular at `p₀ ∈ (0, 1)` for the
pair family with limit `N(0, V)` has `p₀ (1 - p₀) / 2 ≤ V`. -/
theorem pair_hajek_convolution_bound (hp : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    {T : ∀ n, (Fin n → Fin 2 → Bool) → ℝ} {V : ℝ≥0}
    (hT : (bernoulli.pi 2).IsHajekRegular T p₀ (gaussianReal 0 V)) :
    p₀ * (1 - p₀) / 2 ≤ V := by
  rw [← inv_fisherInfo_pair hp]
  exact hajek_convolution_bound (bernoulli_pi_isRegularAt 2 hp) (bernoulli_pi_isScoreRegular 2 hp)
    (bernoulli_pi_hasDerivAt_logLik_closedBall 2 hp) (fisherInfo_pair_pos hp) hT

/-- **The mean of both coordinates is asymptotically linear in the efficient influence
function.** -/
theorem pairMean_isAsymptoticallyLinear (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = (bernoulli.pi 2).law p₀) (hp : p₀ ∈ Set.Ioo (0 : ℝ) 1) :
    IsAsymptoticallyLinear (fun n ω ↦ pairMean n fun i ↦ O i ω) p₀
      (fun x ↦ ((bernoulli.pi 2).fisherInfo p₀)⁻¹ * (bernoulli.pi 2).score p₀ x) O μ := by
  obtain ⟨hmean, h2⟩ := pair_integral_memLp hO hlaw hp
    fun x ↦ (successIndicator (x 0) + successIndicator (x 1)) / 2
  have := isProbabilityMeasure_law (F := bernoulli) hp
  have hint : ∫ x, (successIndicator (x 0) + successIndicator (x 1)) / 2
      ∂(Measure.pi fun _ : Fin 2 ↦ bernoulli.law p₀) = p₀ := by
    rw [integral_div, integral_add Integrable.of_finite Integrable.of_finite,
      (bernoulli_pi_coord (n := 2) hp 0).1, (bernoulli_pi_coord (n := 2) hp 1).1,
      add_self_div_two]
  rw [hint] at hmean
  have hAL := sampleMean_isAsymptoticallyLinear (f := fun x : Fin 2 → Bool ↦
    (successIndicator (x 0) + successIndicator (x 1)) / 2) .of_discrete h2
  rw [hmean] at hAL
  have hφ : (fun x ↦ ((bernoulli.pi 2).fisherInfo p₀)⁻¹ * (bernoulli.pi 2).score p₀ x) =
      fun x ↦ (successIndicator (x 0) + successIndicator (x 1)) / 2 - p₀ :=
    funext fun x ↦ by rw [inv_fisherInfo_pair_mul_score hp]; ring
  have hT : (fun n ω ↦ pairMean n fun i ↦ O i ω) =
      sampleMean (fun x ↦ (successIndicator (x 0) + successIndicator (x 1)) / 2) O :=
    funext fun n ↦ funext fun ω ↦ pairMean_eq_sampleMean n ω
  rw [hφ, hT]
  exact hAL

/-- **The mean of both coordinates is regular** with limit `N(0, p₀ (1 - p₀) / 2)`, the bound. -/
theorem pairMean_isHajekRegular (hp : p₀ ∈ Set.Ioo (0 : ℝ) 1) :
    (bernoulli.pi 2).IsHajekRegular pairMean p₀
      (gaussianReal 0 (p₀ * (1 - p₀) / 2).toNNReal) := by
  have := isProbabilityMeasure_law (F := bernoulli.pi 2) hp
  obtain ⟨Ω', _, P', O', hP', -, hO', hlaw'⟩ := exists_isIIDSample ((bernoulli.pi 2).law p₀)
  rw [← inv_fisherInfo_pair hp]
  exact isHajekRegular_of_isAsymptoticallyLinear hO' (hlaw' 0).map_eq
    (bernoulli_pi_isRegularAt 2 hp) (bernoulli_pi_isScoreRegular 2 hp)
    (bernoulli_pi_hasDerivAt_logLik_closedBall 2 hp) (fisherInfo_pair_pos hp)
    (fun _ ↦ .of_discrete) (pairMean_isAsymptoticallyLinear hO' (hlaw' 0).map_eq hp)

/-- **The mean of both coordinates attains the bound**: its limit variance is `I(p₀)⁻¹`. -/
theorem pairMean_attains_hajek_bound (hp : p₀ ∈ Set.Ioo (0 : ℝ) 1) :
    ((p₀ * (1 - p₀) / 2).toNNReal : ℝ) = ((bernoulli.pi 2).fisherInfo p₀)⁻¹ := by
  rw [inv_fisherInfo_pair hp,
    Real.coe_toNNReal _ (div_nonneg (mul_pos hp.1 (by linarith [hp.2])).le two_pos.le)]

/-! ### Numbers at `p₀ = 1/4` -/

/-- At `p₀ = 1/4` the pair information is `32/3`. -/
theorem fisherInfo_pair_quarter : (bernoulli.pi 2).fisherInfo (1 / 4) = 32 / 3 := by
  rw [fisherInfo_pair ⟨by norm_num, by norm_num⟩]
  norm_num

/-- At `p₀ = 1/4` the Hájek bound for pairs is `3/32`. -/
theorem inv_fisherInfo_pair_quarter : ((bernoulli.pi 2).fisherInfo (1 / 4))⁻¹ = 3 / 32 := by
  rw [fisherInfo_pair_quarter]
  norm_num

/-- At `p₀ = 1/4` the first coordinate mean is regular with limit `N(0, 3/16)`, twice the bound
`3/32`. -/
theorem firstCoordMean_isHajekRegular_quarter :
    (bernoulli.pi 2).IsHajekRegular firstCoordMean (1 / 4)
      (gaussianReal 0 (3 / 16 : ℝ).toNNReal) ∧
      (3 / 16 : ℝ) = 2 * ((bernoulli.pi 2).fisherInfo (1 / 4))⁻¹ := by
  refine ⟨?_, by rw [inv_fisherInfo_pair_quarter]; norm_num⟩
  have h := firstCoordMean_isHajekRegular (p₀ := 1 / 4) ⟨by norm_num, by norm_num⟩
  norm_num at h ⊢
  exact h

/-- At `p₀ = 1/4` the mean of both coordinates is regular with limit `N(0, 3/32)`, the bound. -/
theorem pairMean_isHajekRegular_quarter :
    (bernoulli.pi 2).IsHajekRegular pairMean (1 / 4) (gaussianReal 0 (3 / 32 : ℝ).toNNReal) := by
  have h := pairMean_isHajekRegular (p₀ := 1 / 4) ⟨by norm_num, by norm_num⟩
  norm_num at h ⊢
  exact h

end ParametricFamily

end CausalInference
