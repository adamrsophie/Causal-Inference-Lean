/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.LeCamThirdLemma
public import CausalInference.Estimation.LocalAsymptoticNormality

/-!
# The Hájek convolution bound, scalar parameter

An estimator sequence `T_n` of a real parameter is regular at `θ₀` in Hájek's sense when, for
every local parameter `h`, under the product law of the alternative `θ_n = θ₀ + h/√n` the law of
`√n (T_n - θ_n)` converges weakly to one limit law `L`, the same for every `h`. In a regular
family with positive information, a regular estimator with a centered Gaussian limit
`N(0, V)` has `V ≥ I(θ₀)⁻¹`, with equality exactly when the estimator is asymptotically linear
with the efficient influence function `I(θ₀)⁻¹ s(θ₀; ·)`; conversely every estimator
asymptotically linear in the efficient influence function is regular.

The proof follows Le Cam: along a subsequence, `√n (T_n - θ₀)` and the normalized score `S_n`
converge jointly to some `μ` (Prokhorov); local asymptotic normality and Le Cam's third lemma turn
regularity into the tilt identity `∫ f(x + h) dN(0, V) = ∫ f(x) e^{h z - h² I / 2} dμ(x, z)`;
differentiating it at `h = 0` pins the covariance `∫ x z dμ = 1`, and then
`V - I⁻¹ = ∫ (x - I⁻¹ z)² dμ ≥ 0`.

## Main definitions

* `CausalInference.ParametricFamily.IsHajekRegular F T θ₀ L`: the estimator `T n`, a measurable
  function of a sample of size `n`, is regular at `θ₀` with limit law `L`. The sample of size
  `n` lives under the law `(F.pi n).law θ` of the sample family `ParametricFamily.pi`.

## Main results

* `CausalInference.integral_mul_exp_gaussianReal`: the Gaussian shift identity
  `∫ f(z) e^{t z - t² v / 2} dN(0, v) = ∫ f(z + t v) dN(0, v)`.
* `CausalInference.tilt_integral_mul_eq_one` and `tilt_variance_bound`: a joint law with
  Gaussian marginals satisfying the tilt identity has `∫ x z = 1` and `V - I⁻¹ = ∫ (x - I⁻¹ z)²`.
* `CausalInference.ParametricFamily.IsHajekRegular.tendstoInDistribution`: on an i.i.d. sample
  from `P_θ₀`, `√n (T_n - θ₀)` converges in distribution to `L`.
* `CausalInference.ParametricFamily.hajek_tilt_subseq`: subsequential joint limits of a regular
  estimator and the score satisfy the tilt identity.
* `CausalInference.ParametricFamily.hajek_convolution_bound`: `I(θ₀)⁻¹ ≤ V`.
* `CausalInference.ParametricFamily.hajek_eq_iff_isAsymptoticallyLinear`: `V = I(θ₀)⁻¹` if and
  only if the estimator is asymptotically linear with influence function `I(θ₀)⁻¹ s(θ₀; ·)`.
* `CausalInference.ParametricFamily.isHajekRegular_of_isAsymptoticallyLinear`: an estimator
  asymptotically linear in the efficient influence function is regular with limit
  `N(0, I(θ₀)⁻¹)`.

The instances in which every hypothesis is checked (the Bernoulli family with the sample mean)
are in `CausalInference.Estimation.HajekConvolutionExamples`.

References: J. Hájek (1970), *A characterization of limiting distributions of regular
estimates*, Zeitschrift für Wahrscheinlichkeitstheorie und verwandte Gebiete; L. Le Cam (1960),
*Locally asymptotically normal families of distributions*, University of California Publications
in Statistics; A. W. van der Vaart (1998), *Asymptotic Statistics*, chapter 8.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Metric
open scoped Topology ENNReal NNReal BoundedContinuousFunction

namespace CausalInference

/-! ### Gaussian tilts -/

section Tilt

/-- **The Gaussian shift identity.** Tilting `N(0, v)`, `v ≠ 0`, by the likelihood ratio
`e^{t z - t² v / 2}` gives `N(t v, v)`: `∫ f(z) e^{t z - t² v / 2} dN(0, v) = ∫ f(z + t v) dN(0, v)`
for every measurable `f`. The densities satisfy
`φ_{0,v}(z) e^{t z - t² v / 2} = φ_{t v, v}(z)`. -/
theorem integral_mul_exp_gaussianReal {v : ℝ≥0} (hv : v ≠ 0) (t : ℝ) {f : ℝ → ℝ}
    (hf : Measurable f) :
    ∫ z, f z * Real.exp (t * z - t ^ 2 * v / 2) ∂gaussianReal 0 v =
      ∫ z, f (z + t * v) ∂gaussianReal 0 v := by
  have hv' : (0 : ℝ) < v := lt_of_le_of_ne v.2 (by exact_mod_cast hv.symm)
  have hpdf : ∀ z, gaussianPDFReal 0 v z * Real.exp (t * z - t ^ 2 * v / 2) =
      gaussianPDFReal (t * v) v z := fun z ↦ by
    simp only [gaussianPDFReal_def, mul_assoc, ← Real.exp_add]
    congr 2
    field_simp
    ring
  rw [← integral_map (measurable_add_const _).aemeasurable hf.aestronglyMeasurable,
    gaussianReal_map_add_const, zero_add, integral_gaussianReal_eq_integral_smul hv,
    integral_gaussianReal_eq_integral_smul hv]
  refine integral_congr_ae (Eventually.of_forall fun z ↦ ?_)
  simp only [smul_eq_mul, ← hpdf]
  ring

/-- The second moment of a centered Gaussian law: `∫ x² dN(0, v) = v`. -/
lemma integral_sq_gaussianReal (v : ℝ≥0) : ∫ x, x ^ 2 ∂gaussianReal 0 v = v := by
  have h := variance_eq_integral (μ := gaussianReal 0 v) (X := fun x ↦ x) aemeasurable_id'
  rw [variance_fun_id_gaussianReal] at h
  have h0 : ∫ x, x ∂gaussianReal 0 v = 0 := integral_id_gaussianReal
  simp only [h0, sub_zero] at h
  exact h.symm

variable {μ : Measure (ℝ × ℝ)}

/-- A function of the second coordinate is integrable when it is integrable for the second
marginal. -/
lemma integrable_comp_snd_of_map {ρ : Measure ℝ} (hZ : μ.map Prod.snd = ρ) {g : ℝ → ℝ}
    (hg : Integrable g ρ) : Integrable (fun p : ℝ × ℝ ↦ g p.2) μ := by
  rw [← hZ] at hg
  exact (integrable_map_measure hg.aestronglyMeasurable measurable_snd.aemeasurable).1 hg

/-- A function of the first coordinate is integrable when it is integrable for the first
marginal. -/
lemma integrable_comp_fst_of_map {ρ : Measure ℝ} (hX : μ.map Prod.fst = ρ) {g : ℝ → ℝ}
    (hg : Integrable g ρ) : Integrable (fun p : ℝ × ℝ ↦ g p.1) μ := by
  rw [← hX] at hg
  exact (integrable_map_measure hg.aestronglyMeasurable measurable_fst.aemeasurable).1 hg

/-- **Exponential moments of a Gaussian marginal**: `e^{K |z|}` is integrable, since
`e^{K|z|} ≤ e^{Kz} + e^{-Kz}` and the Gaussian moment generating function is finite. -/
lemma integrable_exp_mul_abs_snd {v : ℝ≥0} (hZ : μ.map Prod.snd = gaussianReal 0 v) (K : ℝ) :
    Integrable (fun p : ℝ × ℝ ↦ Real.exp (K * |p.2|)) μ := by
  refine integrable_comp_snd_of_map hZ (g := fun z ↦ Real.exp (K * |z|)) ?_
  refine ((integrable_exp_mul_gaussianReal K).add
    (integrable_exp_mul_gaussianReal (-K))).mono' (by fun_prop)
    (Eventually.of_forall fun z ↦ ?_)
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, Pi.add_apply]
  rcases le_total 0 z with hz | hz
  · rw [abs_of_nonneg hz]
    linarith [Real.exp_pos (-K * z)]
  · rw [abs_of_nonpos hz, show K * -z = -K * z by ring]
    linarith [Real.exp_pos (K * z)]

/-- Square integrability of a Gaussian first marginal. -/
lemma integrable_sq_fst {v : ℝ≥0} (hX : μ.map Prod.fst = gaussianReal 0 v) :
    Integrable (fun p : ℝ × ℝ ↦ p.1 ^ 2) μ :=
  integrable_comp_fst_of_map hX (g := fun x ↦ x ^ 2)
    (memLp_id_gaussianReal' 2 (by simp)).integrable_sq

/-- Square integrability of a Gaussian second marginal. -/
lemma integrable_sq_snd {v : ℝ≥0} (hZ : μ.map Prod.snd = gaussianReal 0 v) :
    Integrable (fun p : ℝ × ℝ ↦ p.2 ^ 2) μ :=
  integrable_comp_snd_of_map hZ (g := fun x ↦ x ^ 2)
    (memLp_id_gaussianReal' 2 (by simp)).integrable_sq

/-- The product of two coordinates with Gaussian marginals is integrable. -/
lemma integrable_fst_mul_snd {v w : ℝ≥0} (hX : μ.map Prod.fst = gaussianReal 0 v)
    (hZ : μ.map Prod.snd = gaussianReal 0 w) : Integrable (fun p : ℝ × ℝ ↦ p.1 * p.2) μ := by
  refine (((integrable_sq_fst hX).add (integrable_sq_snd hZ)).div_const 2).mono'
    (by fun_prop) (Eventually.of_forall fun p ↦ ?_)
  change |p.1 * p.2| ≤ (p.1 ^ 2 + p.2 ^ 2) / 2
  rw [abs_mul]
  nlinarith [sq_nonneg (|p.1| - |p.2|), sq_abs p.1, sq_abs p.2]

/-- **The tilt identity pins the covariance.** Let `μ` be a law of `(X, Z)` with `X ∼ N(0, V)`,
`Z ∼ N(0, I)`, `I > 0`, and suppose that for every `h` the shift of `N(0, V)` by `h` is the
exponential tilt `e^{h Z - h² I / 2} dμ` seen through `X`. Then `E[X Z] = 1`. For
`f = sin(t ·)`, differentiating the identity in `h` at `0` (dominated by Gaussian exponential
moments) gives `E[sin(tX) Z] = t E[cos(tX)]`; divide by `t` and let `t → 0`. -/
theorem tilt_integral_mul_eq_one [IsProbabilityMeasure μ] {V : ℝ≥0} {I : ℝ} (hI : 0 < I)
    (hX : μ.map Prod.fst = gaussianReal 0 V) (hZ : μ.map Prod.snd = gaussianReal 0 I.toNNReal)
    (htilt : ∀ h : ℝ, ∀ f : ℝ →ᵇ ℝ, ∫ x, f (x + h) ∂gaussianReal 0 V =
      ∫ p, f p.1 * Real.exp (h * p.2 - h ^ 2 * I / 2) ∂μ) :
    ∫ p, p.1 * p.2 ∂μ = 1 := by
  set N := gaussianReal 0 V with hN
  have hstep : ∀ t : ℝ, ∫ p, Real.sin (t * p.1) * p.2 ∂μ = t * ∫ x, Real.cos (t * x) ∂N := by
    intro t
    let fs : ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
      (fun x ↦ Real.sin (t * x)) (by fun_prop) 1
      (fun x ↦ by rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
    have heq : (fun h : ℝ ↦ ∫ x, Real.sin (t * (x + h)) ∂N) =
        fun h ↦ ∫ p, Real.sin (t * p.1) * Real.exp (h * p.2 - h ^ 2 * I / 2) ∂μ := by
      funext h
      exact htilt h fs
    have hA := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := N)
      (F := fun h x ↦ Real.sin (t * (x + h))) (F' := fun h x ↦ Real.cos (t * (x + h)) * t)
      (x₀ := 0) (bound := fun _ ↦ |t|) Filter.univ_mem
      (Eventually.of_forall fun h ↦ (by fun_prop : Continuous fun x ↦
        Real.sin (t * (x + h))).aestronglyMeasurable)
      (Integrable.of_bound (by fun_prop) 1 (Eventually.of_forall fun x ↦ by
        rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _))
      ((by fun_prop : Continuous fun x ↦ Real.cos (t * (x + 0)) * t).aestronglyMeasurable)
      (Eventually.of_forall fun x h _ ↦ by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_of_le_one_left (abs_nonneg t) (Real.abs_cos_le_one _))
      (integrable_const _)
      (Eventually.of_forall fun x h _ ↦ by
        have := (((hasDerivAt_id' h).const_add x).const_mul t).sin
        simpa using this)
    have hB := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
      (F := fun h p ↦ Real.sin (t * p.1) * Real.exp (h * p.2 - h ^ 2 * I / 2))
      (F' := fun h p ↦ Real.sin (t * p.1) * (Real.exp (h * p.2 - h ^ 2 * I / 2) * (p.2 - h * I)))
      (x₀ := 0) (bound := fun p ↦ Real.exp (2 * |p.2|) + I * Real.exp (1 * |p.2|))
      (Metric.ball_mem_nhds 0 one_pos)
      (Eventually.of_forall fun h ↦ (by fun_prop : Continuous fun p : ℝ × ℝ ↦
        Real.sin (t * p.1) * Real.exp (h * p.2 - h ^ 2 * I / 2)).aestronglyMeasurable)
      (Integrable.of_bound (by fun_prop) 1 (Eventually.of_forall fun p ↦ by
        simp only [zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
          zero_div, sub_zero, Real.exp_zero, mul_one, Real.norm_eq_abs]
        exact Real.abs_sin_le_one _))
      ((by fun_prop : Continuous fun p : ℝ × ℝ ↦ Real.sin (t * p.1) *
        (Real.exp (0 * p.2 - 0 ^ 2 * I / 2) * (p.2 - 0 * I))).aestronglyMeasurable)
      (Eventually.of_forall fun p h hh ↦ by
        have hh1 : |h| < 1 := by simpa using hh
        have he : Real.exp (h * p.2 - h ^ 2 * I / 2) ≤ Real.exp (1 * |p.2|) := by
          refine Real.exp_le_exp.2 ?_
          have : h * p.2 ≤ |h| * |p.2| := by rw [← abs_mul]; exact le_abs_self _
          nlinarith [abs_nonneg h, abs_nonneg p.2, sq_nonneg h]
        have hz : |p.2| ≤ Real.exp (1 * |p.2|) := by
          have := Real.add_one_le_exp (1 * |p.2|); linarith
        have hhI : |p.2 - h * I| ≤ |p.2| + I := by
          calc |p.2 - h * I| ≤ |p.2| + |h * I| := abs_sub _ _
            _ ≤ |p.2| + I := by
              rw [abs_mul, abs_of_pos hI]
              nlinarith [abs_nonneg h]
        have e2 : Real.exp (2 * |p.2|) = Real.exp (1 * |p.2|) * Real.exp (1 * |p.2|) := by
          rw [← Real.exp_add]; ring_nf
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), e2]
        have h1 := Real.abs_sin_le_one (t * p.1)
        have hpos := Real.exp_pos (1 * |p.2|)
        have hE := Real.exp_pos (h * p.2 - h ^ 2 * I / 2)
        calc |Real.sin (t * p.1)| * (Real.exp (h * p.2 - h ^ 2 * I / 2) * |p.2 - h * I|)
            ≤ 1 * (Real.exp (1 * |p.2|) * (|p.2| + I)) := by
              gcongr
          _ ≤ Real.exp (1 * |p.2|) * Real.exp (1 * |p.2|) + I * Real.exp (1 * |p.2|) := by
              nlinarith)
      ((integrable_exp_mul_abs_snd hZ 2).add
        ((integrable_exp_mul_abs_snd hZ 1).const_mul I))
      (Eventually.of_forall fun p h _ ↦ by
        have hq : HasDerivAt (fun h : ℝ ↦ h * p.2 - h ^ 2 * I / 2) (p.2 - h * I) h := by
          have := ((hasDerivAt_id' h).mul_const p.2).sub
            (((hasDerivAt_pow 2 h).mul_const I).div_const 2)
          convert this using 1
          simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
          ring
        exact (hq.exp).const_mul _)
    rw [heq] at hA
    have hu := hA.2.unique hB.2
    simp only [add_zero, zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      zero_div, sub_zero, Real.exp_zero, one_mul] at hu
    rw [← hu, integral_mul_const, mul_comm]
  have hxz := integrable_fst_mul_snd hX hZ
  have hL : Tendsto (fun t : ℝ ↦ ∫ p, t⁻¹ * Real.sin (t * p.1) * p.2 ∂μ) (𝓝[≠] 0)
      (𝓝 (∫ p, p.1 * p.2 ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun p ↦ |p.1 * p.2|)
      (Eventually.of_forall fun t ↦ (by fun_prop : Continuous fun p : ℝ × ℝ ↦
        t⁻¹ * Real.sin (t * p.1) * p.2).aestronglyMeasurable)
      (Eventually.of_forall fun t ↦ Eventually.of_forall fun p ↦ ?_) hxz.abs
      (Eventually.of_forall fun p ↦ ?_)
    · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul p.1]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      rcases eq_or_ne t 0 with rfl | ht
      · simp
      · rw [abs_inv]
        have := Real.abs_sin_le_abs (x := t * p.1)
        rw [abs_mul] at this
        rw [inv_mul_le_iff₀ (abs_pos.2 ht)]
        exact this
    · have hd : HasDerivAt (fun t : ℝ ↦ Real.sin (t * p.1)) (Real.cos (0 * p.1) * (1 * p.1)) 0 :=
        ((hasDerivAt_id' (0 : ℝ)).mul_const p.1).sin
      have := (hasDerivAt_iff_tendsto_slope_zero.1 hd).mul_const p.2
      simp only [zero_mul, Real.cos_zero, one_mul, zero_add, Real.sin_zero, sub_zero,
        smul_eq_mul] at this
      exact this
  have hR : Tendsto (fun t : ℝ ↦ ∫ x, Real.cos (t * x) ∂N) (𝓝[≠] 0) (𝓝 1) := by
    have h := tendsto_integral_filter_of_dominated_convergence (μ := N) (l := 𝓝[≠] (0 : ℝ))
      (F := fun t x ↦ Real.cos (t * x)) (f := fun x ↦ Real.cos (0 * x)) (fun _ ↦ 1)
      (Eventually.of_forall fun t ↦ (by fun_prop : Continuous fun x : ℝ ↦
        Real.cos (t * x)).aestronglyMeasurable)
      (Eventually.of_forall fun t ↦ Eventually.of_forall fun x ↦ by
        rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _) (integrable_const _)
      (Eventually.of_forall fun x ↦ ((by fun_prop : Continuous fun t : ℝ ↦
        Real.cos (t * x)).tendsto 0).mono_left nhdsWithin_le_nhds)
    simpa using h
  have heq : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∫ x, Real.cos (t * x) ∂N =
      ∫ p, t⁻¹ * Real.sin (t * p.1) * p.2 ∂μ := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp_rw [mul_assoc]
    rw [integral_const_mul, hstep t, ← mul_assoc, inv_mul_cancel₀ ht, one_mul]
  exact tendsto_nhds_unique hL (hR.congr' heq)

/-- **The variance bound from the tilt identity.** Under the hypotheses of
`CausalInference.tilt_integral_mul_eq_one`, `V - I⁻¹ = E[(X - I⁻¹ Z)²] ≥ 0`, and `V = I⁻¹`
forces `X = I⁻¹ Z` almost surely. -/
theorem tilt_variance_bound [IsProbabilityMeasure μ] {V : ℝ≥0} {I : ℝ} (hI : 0 < I)
    (hX : μ.map Prod.fst = gaussianReal 0 V) (hZ : μ.map Prod.snd = gaussianReal 0 I.toNNReal)
    (htilt : ∀ h : ℝ, ∀ f : ℝ →ᵇ ℝ, ∫ x, f (x + h) ∂gaussianReal 0 V =
      ∫ p, f p.1 * Real.exp (h * p.2 - h ^ 2 * I / 2) ∂μ) :
    ∫ p, (p.1 - I⁻¹ * p.2) ^ 2 ∂μ = V - I⁻¹ ∧ I⁻¹ ≤ V ∧
      ((V : ℝ) = I⁻¹ → ∀ᵐ p ∂μ, p.1 = I⁻¹ * p.2) := by
  have h1 := tilt_integral_mul_eq_one hI hX hZ htilt
  have hx2 := integrable_sq_fst hX
  have hz2 := integrable_sq_snd hZ
  have hxz := integrable_fst_mul_snd hX hZ
  have ix2 : ∫ p, p.1 ^ 2 ∂μ = V := by
    rw [← integral_sq_gaussianReal V, ← hX, integral_map measurable_fst.aemeasurable
      (by fun_prop)]
  have iz2 : ∫ p, p.2 ^ 2 ∂μ = I := by
    rw [← Real.coe_toNNReal I hI.le, ← integral_sq_gaussianReal I.toNNReal, ← hZ,
      integral_map measurable_snd.aemeasurable (by fun_prop)]
  have hexp : (fun p : ℝ × ℝ ↦ (p.1 - I⁻¹ * p.2) ^ 2) =
      fun p ↦ p.1 ^ 2 - 2 * I⁻¹ * (p.1 * p.2) + I⁻¹ ^ 2 * p.2 ^ 2 := by
    funext p; ring
  have e : ∫ p, (p.1 - I⁻¹ * p.2) ^ 2 ∂μ = V - I⁻¹ := by
    rw [hexp, integral_add (f := fun p : ℝ × ℝ ↦ p.1 ^ 2 - 2 * I⁻¹ * (p.1 * p.2))
      (g := fun p : ℝ × ℝ ↦ I⁻¹ ^ 2 * p.2 ^ 2) (hx2.sub (hxz.const_mul _)) (hz2.const_mul _),
      integral_sub (f := fun p : ℝ × ℝ ↦ p.1 ^ 2) (g := fun p : ℝ × ℝ ↦ 2 * I⁻¹ * (p.1 * p.2))
      hx2 (hxz.const_mul _), integral_const_mul, integral_const_mul, ix2, iz2, h1]
    field_simp
    ring
  have hnn : 0 ≤ ∫ p, (p.1 - I⁻¹ * p.2) ^ 2 ∂μ := integral_nonneg fun p ↦ sq_nonneg _
  refine ⟨e, by linarith, fun hV ↦ ?_⟩
  have hint : Integrable (fun p : ℝ × ℝ ↦ (p.1 - I⁻¹ * p.2) ^ 2) μ := by
    rw [hexp]
    exact (hx2.sub (hxz.const_mul _)).add (hz2.const_mul _)
  have h0 : ∫ p, (p.1 - I⁻¹ * p.2) ^ 2 ∂μ = 0 := by rw [e, hV, sub_self]
  have := (integral_eq_zero_iff_of_nonneg (fun p ↦ sq_nonneg _) hint).1 h0
  filter_upwards [this] with p hp
  have : (p.1 - I⁻¹ * p.2) ^ 2 = 0 := hp
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  linarith

end Tilt

/-- Convergence in probability passes to reindexings `k ↦ X (N k)` with `N k → ∞`. -/
theorem _root_.MeasureTheory.TendstoInMeasure.comp_tendsto_atTop {Ω E : Type*}
    {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [PseudoMetricSpace E] {X : ℕ → Ω → E} {c : Ω → E}
    (h : TendstoInMeasure μ X atTop c) {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) :
    TendstoInMeasure μ (fun k ↦ X (N k)) atTop c := by
  rw [tendstoInMeasure_iff_dist] at h ⊢
  exact fun ε hε ↦ (h ε hε).comp hN

/-! ### Regular estimators -/

namespace ParametricFamily

variable {S : Type*} [MeasurableSpace S] {F : ParametricFamily ℝ S} [SigmaFinite F.ν]
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {O : ℕ → Ω → S} {θ₀ : ℝ}

variable (F) in
/-- **Regularity in Hájek's sense.** The estimator `T n`, a measurable function of a sample
`x : Fin n → S` of size `n`, is regular at `θ₀` with limit law `L` if for every local parameter
`h`, when the sample has the law `(F.pi n).law θ_n` of the sample family at
`θ_n = θ₀ + h / √n` (an i.i.d. sample of size `n` from `P_{θ_n}`), the law of
`√n (T_n - θ_n)` converges weakly to `L`, that is
`∫ f(√n (T_n - θ_n)) d(F.pi n).law θ_n → ∫ f dL` for every bounded continuous `f`. The limit does
not depend on `h`.

The predicate is used at interior points `θ₀` of `Θ`, where `θ_n ∈ Θ` for all large `n`; the
values for the finitely many other `n` do not matter. The connection with an i.i.d. sample
(`CausalInference.IsIIDSample`) is `IsHajekRegular.tendstoInDistribution`. -/
structure IsHajekRegular (T : ∀ n, (Fin n → S) → ℝ) (θ₀ : ℝ) (L : Measure ℝ) : Prop where
  /-- Each `T n` is measurable. -/
  measurable : ∀ n, Measurable (T n)
  /-- Weak convergence of `√n (T_n - θ_n)` under every local alternative. -/
  tendsto : ∀ h : ℝ, ∀ f : ℝ →ᵇ ℝ, Tendsto (fun n : ℕ ↦
    ∫ x, f (√(n : ℝ) * (T n x - (θ₀ + h / √(n : ℝ)))) ∂(F.pi n).law (θ₀ + h / √(n : ℝ)))
    atTop (𝓝 (∫ y, f y ∂L))

/-- The first `n` observations of an i.i.d. sample with law `P_θ₀` have the law of the sample
family at `θ₀`. -/
theorem map_fin_eq_pi_law (hO : IsIIDSample O μ) (hlaw : μ.map (O 0) = F.law θ₀)
    (hθ₀ : θ₀ ∈ F.Θ) (n : ℕ) : μ.map (fun ω (i : Fin n) ↦ O i ω) = (F.pi n).law θ₀ := by
  rw [hO.map_fin_eq_pi n, hlaw, pi_law n hθ₀]

/-- **A regular estimator on an i.i.d. sample.** Under `θ₀` (local parameter `h = 0`), on every
i.i.d. sample with law `P_θ₀`, `√n (T_n(O_0, …, O_{n-1}) - θ₀)` converges in distribution to the
limit law `L`. -/
theorem IsHajekRegular.tendstoInDistribution (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = F.law θ₀) (hθ₀ : θ₀ ∈ F.Θ) {T : ∀ n, (Fin n → S) → ℝ}
    {L : Measure ℝ} [IsProbabilityMeasure L] (hT : F.IsHajekRegular T θ₀ L) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) * (T n (fun i ↦ O i ω) - θ₀)) atTop id
      (fun _ ↦ μ) L := by
  have hR : ∀ n, AEMeasurable (fun ω (i : Fin n) ↦ O i ω) μ := fun n ↦
    AEMeasurable.of_eval fun i ↦ hO.aemeasurable i
  have hTc : ∀ n, Measurable fun x : Fin n → S ↦ √(n : ℝ) * (T n x - θ₀) := fun n ↦
    measurable_const.mul ((hT.measurable n).sub measurable_const)
  refine (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
    (fun n ↦ (hTc n).comp_aemeasurable (hR n)) aemeasurable_id).2 fun f ↦ ?_
  have h0 := hT.tendsto 0 f
  simp only [zero_div, add_zero] at h0
  refine h0.congr fun n ↦ ?_
  rw [← map_fin_eq_pi_law hO hlaw hθ₀ n]
  exact integral_map (hR n) (f.continuous.measurable.comp (hTc n)).aestronglyMeasurable

omit [SigmaFinite F.ν] [IsProbabilityMeasure μ] in
/-- The log likelihood ratio is almost everywhere measurable on a sample. -/
theorem aemeasurable_logLikRatio (hO : IsIIDSample O μ) (θ : ℝ) (n : ℕ) :
    AEMeasurable (F.logLikRatio O θ₀ θ n) μ := by
  unfold logLikRatio logLik
  exact Finset.aemeasurable_fun_sum _ fun i _ ↦
    ((Real.measurable_log.comp (F.measurable_density θ)).comp_aemeasurable
      (hO.aemeasurable i)).sub
      ((Real.measurable_log.comp (F.measurable_density θ₀)).comp_aemeasurable
      (hO.aemeasurable i))

/-- **Le Cam's third lemma for the sample family.** Let `O` be an i.i.d. sample with law `P_θ₀`,
`θ₀` interior to `Θ` with the support of `f(·;θ)` constant near `θ₀`, and `m k → ∞`. If
`(√m (T_m - θ₀), Λ_m)` converges in distribution to `ρ` with `∫ e^ℓ dρ = 1`, where `m = m k` and
`Λ_m` is the log likelihood ratio of `θ₀ + h/√m` against `θ₀`, then under the sample family at
`θ₀ + h/√m` the law of `√m (T_m - θ₀)` converges weakly to the tilt `f ↦ ∫ f(x) e^ℓ dρ(x, ℓ)`. -/
theorem tendsto_integral_pi_law_of_tendstoInDistribution (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = F.law θ₀) (hΘ : F.Θ ∈ 𝓝 θ₀)
    (hsupp : ∀ᶠ θ in 𝓝 θ₀, ∀ x, 0 < F.density θ x ↔ 0 < F.density θ₀ x)
    {T : ∀ n, (Fin n → S) → ℝ} (hTm : ∀ n, Measurable (T n)) {m : ℕ → ℕ}
    (hm : Tendsto m atTop atTop) (h : ℝ) {ρ : Measure (ℝ × ℝ)} [IsProbabilityMeasure ρ]
    (hjoint : TendstoInDistribution (fun k ω ↦ (√(m k : ℝ) * (T (m k) (fun i ↦ O i ω) - θ₀),
      F.logLikRatio O θ₀ (θ₀ + h / √(m k : ℝ)) (m k) ω)) atTop id (fun _ ↦ μ) ρ)
    (hmass : ∫ p, Real.exp p.2 ∂ρ = 1) (f : ℝ →ᵇ ℝ) :
    Tendsto (fun k ↦ ∫ x, f (√(m k : ℝ) * (T (m k) x - θ₀))
      ∂(F.pi (m k)).law (θ₀ + h / √(m k : ℝ))) atTop (𝓝 (∫ p, f p.1 * Real.exp p.2 ∂ρ)) := by
  have hθ₀ : θ₀ ∈ F.Θ := mem_of_mem_nhds hΘ
  have hTc : ∀ n (c : ℝ), Measurable fun x : Fin n → S ↦ √(n : ℝ) * (T n x - c) := fun n c ↦
    measurable_const.mul ((hTm n).sub measurable_const)
  set θk : ℕ → ℝ := fun k ↦ θ₀ + h / √(m k : ℝ) with hθk_def
  have hθk : Tendsto θk atTop (𝓝 θ₀) := by
    have : Tendsto (fun k ↦ h / √(m k : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        ((Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).comp hm)
    simpa using this.const_add θ₀
  set ν : ℕ → Measure ℝ := fun k ↦ ((F.pi (m k)).law (θk k)).map
    fun x ↦ √(m k : ℝ) * (T (m k) x - θ₀) with hν
  have hev : ∀ᶠ k in atTop, θk k ∈ F.Θ ∧ ∀ x, 0 < F.density (θk k) x ↔ 0 < F.density θ₀ x :=
    (hθk.eventually hΘ).and (hθk.eventually hsupp)
  have hν1 : ∀ᶠ k in atTop, ν k Set.univ ≤ 1 := by
    filter_upwards [hev] with k hk
    have := isProbabilityMeasure_law (F := F.pi (m k)) hk.1
    rw [hν, Measure.map_apply (hTc _ _) MeasurableSet.univ, Set.preimage_univ, measure_univ]
  have hdom : ∀ᶠ k in atTop, ∀ g : ℝ → ℝ≥0∞, Measurable g →
      ∫⁻ ω, g (√(m k : ℝ) * (T (m k) (fun i ↦ O i ω) - θ₀)) *
        ENNReal.ofReal (Real.exp (F.logLikRatio O θ₀ (θk k) (m k) ω)) ∂μ ≤ ∫⁻ x, g x ∂ν k := by
    filter_upwards [hev] with k hk g hg
    rw [hν, lintegral_map hg (hTc _ _)]
    exact (lintegral_mul_exp_logLikRatio hO hlaw hθ₀ hk.1 hk.2 (m k)
      (hg.comp (hTc _ _))).le
  have h3 := lecam_third_lemma hjoint hmass hν1 hdom f
  refine h3.congr fun k ↦ ?_
  rw [hν, integral_map (hTc _ _).aemeasurable f.continuous.aestronglyMeasurable]

/-- **Subsequential joint limits of a regular estimator and the score satisfy the tilt
identity.** Let `O` be an i.i.d. sample with law `P_θ₀`, the family regular at `θ₀` with positive
information and the smoothness of `logLikRatio_sub_tendstoInMeasure`, and `T` regular at `θ₀`
with limit `N(0, V)`. Along every `ψ k → ∞`, some further subsequence of
`(√n (T_n - θ₀), S_n)`, `S_n = n^{-1/2} ∑_{i < n} s(θ₀; O_i)`, converges in distribution to a law
`μ'` with marginals `N(0, V)` and `N(0, I(θ₀))` and, for every `h` and bounded continuous `f`,
`∫ f(x + h) dN(0, V) = ∫ f(x) e^{h z - h² I(θ₀) / 2} dμ'(x, z)`. The proof combines Prokhorov's
theorem, local asymptotic normality, the change of measure for the sample family, Le Cam's third
lemma and regularity at `h`. -/
theorem hajek_tilt_subseq (hO : IsIIDSample O μ) (hlaw : μ.map (O 0) = F.law θ₀)
    (hreg : F.IsRegularAt θ₀) {r : ℝ} (hs : F.IsScoreRegular θ₀ r)
    (hdl : ∀ᵐ z ∂F.law θ₀, ∀ θ ∈ closedBall θ₀ r,
      HasDerivAt (fun u ↦ F.logLik u z) (F.score θ z) θ)
    (hI : 0 < F.fisherInfo θ₀) {T : ∀ n, (Fin n → S) → ℝ} {V : ℝ≥0}
    (hT : F.IsHajekRegular T θ₀ (gaussianReal 0 V)) {ψ : ℕ → ℕ} (hψ : Tendsto ψ atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ μ' : ProbabilityMeasure (ℝ × ℝ),
      TendstoInDistribution (fun k ω ↦
        (√(ψ (φ k) : ℝ) * (T (ψ (φ k)) (fun i ↦ O i ω) - θ₀),
          (√(ψ (φ k) : ℝ))⁻¹ * ∑ i ∈ range (ψ (φ k)), F.score θ₀ (O i ω))) atTop id
        (fun _ ↦ μ) (μ' : Measure (ℝ × ℝ)) ∧
      (μ' : Measure (ℝ × ℝ)).map Prod.fst = gaussianReal 0 V ∧
      (μ' : Measure (ℝ × ℝ)).map Prod.snd = gaussianReal 0 (F.fisherInfo θ₀).toNNReal ∧
      ∀ h : ℝ, ∀ f : ℝ →ᵇ ℝ, ∫ x, f (x + h) ∂gaussianReal 0 V =
        ∫ p, f p.1 * Real.exp (h * p.2 - h ^ 2 * F.fisherInfo θ₀ / 2)
          ∂(μ' : Measure (ℝ × ℝ)) := by
  set I := F.fisherInfo θ₀ with hIdef
  have hθ₀ : θ₀ ∈ F.Θ := mem_of_mem_nhds hreg.mem_nhds
  have hR : ∀ n, AEMeasurable (fun ω (i : Fin n) ↦ O i ω) μ := fun n ↦
    AEMeasurable.of_eval fun i ↦ hO.aemeasurable i
  have hXm : ∀ n : ℕ, AEMeasurable (fun ω ↦ √(n : ℝ) * (T n (fun i ↦ O i ω) - θ₀)) μ :=
    fun n ↦ (measurable_const.mul ((hT.measurable n).sub measurable_const)).comp_aemeasurable
      (hR n)
  have hXlaw := hT.tendstoInDistribution hO hlaw hθ₀
  have hclt := sum_score_tendstoInDistribution hO hlaw hreg hs.measurable_score
    (P' := gaussianReal 0 I.toNNReal) (Y := id) HasLaw.id
  obtain ⟨φ, hφ, μ', hjoint, h1, h2⟩ := exists_subseq_tendstoInDistribution_prodMk
    (hXlaw.comp_tendsto_atTop hψ) (hclt.comp_tendsto_atTop hψ)
  refine ⟨φ, hφ, μ', hjoint, h1, h2, fun h f ↦ ?_⟩
  set m : ℕ → ℕ := fun k ↦ ψ (φ k) with hmdef
  have hm : Tendsto m atTop atTop := hψ.comp hφ.tendsto_atTop
  have hlan := (logLikRatio_sub_tendstoInMeasure hO hlaw hreg hs hdl h).comp_tendsto_atTop hm
  set g : ℝ × ℝ → ℝ × ℝ := fun p ↦ (p.1, h * p.2 - h ^ 2 * I / 2) with hg
  have hgc : Continuous g := by fun_prop
  have hj2 : TendstoInDistribution (fun k ω ↦ (√(m k : ℝ) * (T (m k) (fun i ↦ O i ω) - θ₀),
      h * ((√(m k : ℝ))⁻¹ * ∑ i ∈ range (m k), F.score θ₀ (O i ω)) - h ^ 2 * I / 2)) atTop id
      (fun _ ↦ μ) ((μ' : Measure (ℝ × ℝ)).map g) :=
    (hjoint.continuous_comp hgc).of_hasLaw ⟨hgc.aemeasurable, rfl⟩ HasLaw.id
  have hj3 : TendstoInDistribution (fun k ω ↦ (√(m k : ℝ) * (T (m k) (fun i ↦ O i ω) - θ₀),
      F.logLikRatio O θ₀ (θ₀ + h / √(m k : ℝ)) (m k) ω)) atTop id (fun _ ↦ μ)
      ((μ' : Measure (ℝ × ℝ)).map g) := by
    refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hj2 ?_
      fun k ↦ (hXm (m k)).prodMk (aemeasurable_logLikRatio hO _ (m k))
    have hp := (tendstoInMeasure_const (μ := μ) (0 : ℝ)).prodMk hlan
    refine hp.congr' (Eventually.of_forall fun k ↦ Eventually.of_forall fun ω ↦ ?_)
      (Eventually.of_forall fun _ ↦ rfl)
    simp only [Pi.sub_apply, Prod.mk_sub_mk, sub_self, hmdef]
    rfl
  have hmass : ∫ p, Real.exp p.2 ∂((μ' : Measure (ℝ × ℝ)).map g) = 1 := by
    rw [integral_map hgc.aemeasurable (by fun_prop)]
    have e : ∫ p, Real.exp (g p).2 ∂(μ' : Measure (ℝ × ℝ)) =
        ∫ z, Real.exp (h * z - h ^ 2 * I / 2) ∂gaussianReal 0 I.toNNReal := by
      rw [← h2, integral_map measurable_snd.aemeasurable (by fun_prop)]
    rw [e]
    have hv : I.toNNReal ≠ 0 := by simpa using hI
    have := integral_mul_exp_gaussianReal hv h (f := fun _ ↦ 1) measurable_const
    simp only [one_mul, integral_const, smul_eq_mul, Real.coe_toNNReal I hI.le,
      measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] at this
    exact this
  have h3 := tendsto_integral_pi_law_of_tendstoInDistribution hO hlaw hreg.mem_nhds
    hreg.support hT.measurable hm h hj3 hmass f
  rw [integral_map hgc.aemeasurable (by fun_prop)] at h3
  let f' : ℝ →ᵇ ℝ := f.compContinuous ⟨fun y ↦ y + h, by fun_prop⟩
  have hf' : ∀ y, f' y = f (y + h) := fun y ↦ rfl
  have hr := (hT.tendsto h f').comp hm
  have heq : ∀ᶠ k in atTop, ∫ x, f (√(m k : ℝ) * (T (m k) x - θ₀))
      ∂(F.pi (m k)).law (θ₀ + h / √(m k : ℝ)) =
      ∫ x, f' (√(m k : ℝ) * (T (m k) x - (θ₀ + h / √(m k : ℝ))))
      ∂(F.pi (m k)).law (θ₀ + h / √(m k : ℝ)) := by
    filter_upwards [hm.eventually (eventually_gt_atTop 0)] with k hk
    have hs0 : √(m k : ℝ) ≠ 0 := (Real.sqrt_pos.2 (Nat.cast_pos.2 hk)).ne'
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    simp only [hf']
    congr 1
    field_simp
    ring
  have hr' := hr.congr' (heq.mono fun k hk ↦ hk.symm)
  have := tendsto_nhds_unique hr' h3
  simp only [hf'] at this
  simpa [hg] using this

/-- **The Hájek convolution bound on a given sample.** Under the hypotheses of
`hajek_tilt_subseq`, a regular estimator with limit `N(0, V)` has `I(θ₀)⁻¹ ≤ V`. -/
theorem hajek_convolution_bound_of_isIIDSample (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = F.law θ₀) (hreg : F.IsRegularAt θ₀) {r : ℝ}
    (hs : F.IsScoreRegular θ₀ r)
    (hdl : ∀ᵐ z ∂F.law θ₀, ∀ θ ∈ closedBall θ₀ r,
      HasDerivAt (fun u ↦ F.logLik u z) (F.score θ z) θ)
    (hI : 0 < F.fisherInfo θ₀) {T : ∀ n, (Fin n → S) → ℝ} {V : ℝ≥0}
    (hT : F.IsHajekRegular T θ₀ (gaussianReal 0 V)) : (F.fisherInfo θ₀)⁻¹ ≤ V := by
  obtain ⟨φ, -, μ', -, h1, h2, ht⟩ := hajek_tilt_subseq hO hlaw hreg hs hdl hI hT tendsto_id
  exact (tilt_variance_bound hI h1 h2 ht).2.1

/-- **The Hájek convolution bound, scalar parameter.** In a family regular at `θ₀` with positive
information `I(θ₀)`, the second derivative of the log density smooth with an integrable envelope
on a closed ball around `θ₀` (`IsScoreRegular`) and `θ ↦ ℓ(θ; z)` with derivative `s(θ; z)` there,
every estimator sequence regular at `θ₀` in Hájek's sense with limit `N(0, V)` has
`V ≥ I(θ₀)⁻¹`. The proof runs `hajek_convolution_bound_of_isIIDSample` on an i.i.d. sample with
law `P_θ₀`, which exists by `exists_isIIDSample`. -/
theorem hajek_convolution_bound (hreg : F.IsRegularAt θ₀) {r : ℝ}
    (hs : F.IsScoreRegular θ₀ r)
    (hdl : ∀ᵐ z ∂F.law θ₀, ∀ θ ∈ closedBall θ₀ r,
      HasDerivAt (fun u ↦ F.logLik u z) (F.score θ z) θ)
    (hI : 0 < F.fisherInfo θ₀) {T : ∀ n, (Fin n → S) → ℝ} {V : ℝ≥0}
    (hT : F.IsHajekRegular T θ₀ (gaussianReal 0 V)) : (F.fisherInfo θ₀)⁻¹ ≤ V := by
  have := isProbabilityMeasure_law (mem_of_mem_nhds hreg.mem_nhds)
  obtain ⟨Ω', _, P', O', hP', -, hO', hlaw'⟩ := exists_isIIDSample (F.law θ₀)
  exact hajek_convolution_bound_of_isIIDSample hO' (hlaw' 0).map_eq hreg hs hdl hI hT

/-- **Equality in the Hájek bound is asymptotic linearity in the efficient influence function.**
Under the hypotheses of `hajek_tilt_subseq`, on any i.i.d. sample with law `P_θ₀`, a regular
estimator with limit `N(0, V)` has `V = I(θ₀)⁻¹` if and only if it is asymptotically linear at
`θ₀` with influence function `I(θ₀)⁻¹ s(θ₀; ·)`. If `V = I(θ₀)⁻¹`, every subsequential joint limit
of `(√n (T_n - θ₀), S_n)` is carried by the line `x = I⁻¹ z` (`tilt_variance_bound`), so along a
further subsequence of any subsequence the remainder tends to `δ₀` in distribution, hence to `0`
in probability. Conversely an asymptotically linear estimator has the limit
`N(0, E[(I⁻¹ s)²]) = N(0, I(θ₀)⁻¹)`, and Gaussian limits are unique. -/
theorem hajek_eq_iff_isAsymptoticallyLinear (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = F.law θ₀) (hreg : F.IsRegularAt θ₀) {r : ℝ}
    (hs : F.IsScoreRegular θ₀ r)
    (hdl : ∀ᵐ z ∂F.law θ₀, ∀ θ ∈ closedBall θ₀ r,
      HasDerivAt (fun u ↦ F.logLik u z) (F.score θ z) θ)
    (hI : 0 < F.fisherInfo θ₀) {T : ∀ n, (Fin n → S) → ℝ} {V : ℝ≥0}
    (hT : F.IsHajekRegular T θ₀ (gaussianReal 0 V)) :
    (V : ℝ) = (F.fisherInfo θ₀)⁻¹ ↔ IsAsymptoticallyLinear (fun n ω ↦ T n fun i ↦ O i ω) θ₀
      (fun x ↦ (F.fisherInfo θ₀)⁻¹ * F.score θ₀ x) O μ := by
  set I := F.fisherInfo θ₀ with hIdef
  have hθ₀ : θ₀ ∈ F.Θ := mem_of_mem_nhds hreg.mem_nhds
  have := isProbabilityMeasure_law hθ₀
  have hX0 := hO.aemeasurable 0
  have hsm := hs.measurable_score
  have hsum : ∀ (n : ℕ) (ω : Ω), (√(n : ℝ))⁻¹ * ∑ i ∈ range n, I⁻¹ * F.score θ₀ (O i ω) =
      I⁻¹ * ((√(n : ℝ))⁻¹ * ∑ i ∈ range n, F.score θ₀ (O i ω)) := fun n ω ↦ by
    rw [← Finset.mul_sum]; ring
  constructor
  · intro hV
    have hmem : MemLp (fun ω ↦ F.score θ₀ (O 0 ω)) 2 μ :=
      (memLp_map_measure_iff hsm.aestronglyMeasurable hX0).1 (by rw [hlaw]; exact hreg.memLp_score)
    refine ⟨hsm.const_mul _, hmem.const_mul _, ?_, ?_⟩
    · rw [integral_const_mul, ← integral_map hX0 hsm.aestronglyMeasurable, hlaw,
        hreg.integral_score_eq_zero, mul_zero]
    rw [tendstoInMeasure_iff_dist]
    intro ε hε
    refine tendsto_of_subseq_tendsto fun ns hns ↦ ?_
    obtain ⟨φ, -, μ', hjoint, h1, h2, ht⟩ := hajek_tilt_subseq hO hlaw hreg hs hdl hI hT hns
    obtain ⟨-, -, hae⟩ := tilt_variance_bound hI h1 h2 ht
    have hd : (μ' : Measure (ℝ × ℝ)).map (fun p ↦ p.1 - I⁻¹ * p.2) = Measure.dirac 0 := by
      rw [Measure.map_congr ((hae hV).mono fun p hp ↦
        (show p.1 - I⁻¹ * p.2 = (fun _ ↦ (0 : ℝ)) p by rw [hp]; ring)),
        Measure.map_const, measure_univ, one_smul]
    have hc : Continuous fun p : ℝ × ℝ ↦ p.1 - I⁻¹ * p.2 := by fun_prop
    have hl := (hjoint.continuous_comp hc).of_hasLaw ⟨hc.aemeasurable, hd⟩ HasLaw.id
    have hp := tendstoInMeasure_of_tendstoInDistribution_dirac hl
    rw [tendstoInMeasure_iff_dist] at hp
    refine ⟨φ, (hp ε hε).congr fun k ↦ ?_⟩
    congr 1
    ext ω
    simp only [Set.mem_ofPred_eq, Function.comp_apply, Pi.zero_apply, hsum]
  · intro hlin
    have hmeas : ∀ n, AEMeasurable (fun ω ↦ T n fun i ↦ O i ω) μ := fun n ↦
      (hT.measurable n).comp_aemeasurable (AEMeasurable.of_eval fun i ↦ hO.aemeasurable i)
    have hsq : μ[fun ω ↦ (I⁻¹ * F.score θ₀ (O 0 ω)) ^ 2] = I⁻¹ := by
      simp_rw [mul_pow]
      rw [integral_const_mul, integral_score_sq_eq_fisherInfo hX0 hlaw hsm, ← hIdef]
      field_simp
    have hA := hlin.tendstoInDistribution hO hmeas (Y := id)
      (P' := gaussianReal 0 (μ[fun ω ↦ (I⁻¹ * F.score θ₀ (O 0 ω)) ^ 2]).toNNReal) HasLaw.id
    have hB := hT.tendstoInDistribution hO hlaw hθ₀
    have e := tendstoInDistribution_unique _ hB hA
    simp only [Measure.map_id] at e
    have := congrArg (fun m ↦ Var[fun x : ℝ ↦ x; m]) e
    simp only [variance_fun_id_gaussianReal] at this
    rw [this, hsq, Real.coe_toNNReal _ (inv_nonneg.2 hI.le)]

/-- The image of `N(0, I)` under `z ↦ I⁻¹ z` is `N(0, I⁻¹)`, for `I > 0`. -/
lemma gaussianReal_map_inv_mul {I : ℝ} (hI : 0 < I) :
    (gaussianReal 0 I.toNNReal).map (fun z ↦ I⁻¹ * z) = gaussianReal 0 I⁻¹.toNNReal := by
  rw [gaussianReal_map_const_mul, mul_zero]
  congr 1
  apply NNReal.eq
  rw [NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal _ hI.le,
    Real.coe_toNNReal _ (inv_nonneg.2 hI.le)]
  field_simp

/-- **An estimator asymptotically linear in the efficient influence function is regular.** Under
the hypotheses of `hajek_tilt_subseq`, if `T` is asymptotically linear at `θ₀` with influence
function `I(θ₀)⁻¹ s(θ₀; ·)` on an i.i.d. sample with law `P_θ₀`, then `T` is regular at `θ₀` in
Hájek's sense with limit `N(0, I(θ₀)⁻¹)`. Jointly with the log likelihood ratio,
`(√n (T_n - θ₀), Λ_n(h))` converges to the image of `N(0, I)` under
`z ↦ (I⁻¹ z, h z - h² I / 2)`; by Le Cam's third lemma and the Gaussian shift identity, under
`θ₀ + h/√n` the law of `√n (T_n - θ₀)` tends to `N(h, I⁻¹)`. -/
theorem isHajekRegular_of_isAsymptoticallyLinear (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = F.law θ₀) (hreg : F.IsRegularAt θ₀) {r : ℝ}
    (hs : F.IsScoreRegular θ₀ r)
    (hdl : ∀ᵐ z ∂F.law θ₀, ∀ θ ∈ closedBall θ₀ r,
      HasDerivAt (fun u ↦ F.logLik u z) (F.score θ z) θ)
    (hI : 0 < F.fisherInfo θ₀) {T : ∀ n, (Fin n → S) → ℝ} (hTm : ∀ n, Measurable (T n))
    (hlin : IsAsymptoticallyLinear (fun n ω ↦ T n fun i ↦ O i ω) θ₀
      (fun x ↦ (F.fisherInfo θ₀)⁻¹ * F.score θ₀ x) O μ) :
    F.IsHajekRegular T θ₀ (gaussianReal 0 (F.fisherInfo θ₀)⁻¹.toNNReal) := by
  refine ⟨hTm, fun h f ↦ ?_⟩
  set I := F.fisherInfo θ₀ with hIdef
  have hR : ∀ n, AEMeasurable (fun ω (i : Fin n) ↦ O i ω) μ := fun n ↦
    AEMeasurable.of_eval fun i ↦ hO.aemeasurable i
  have hXm : ∀ n : ℕ, AEMeasurable (fun ω ↦ √(n : ℝ) * (T n (fun i ↦ O i ω) - θ₀)) μ :=
    fun n ↦ (measurable_const.mul ((hTm n).sub measurable_const)).comp_aemeasurable (hR n)
  have hclt := sum_score_tendstoInDistribution hO hlaw hreg hs.measurable_score
    (P' := gaussianReal 0 I.toNNReal) (Y := id) HasLaw.id
  set G : ℝ → ℝ × ℝ := fun z ↦ (I⁻¹ * z, h * z - h ^ 2 * I / 2) with hG
  have hGc : Continuous G := by fun_prop
  set ρ := (gaussianReal 0 I.toNNReal).map G with hρ
  have hj2 : TendstoInDistribution (fun (n : ℕ) ω ↦
      G ((√(n : ℝ))⁻¹ * ∑ i ∈ range n, F.score θ₀ (O i ω))) atTop id (fun _ ↦ μ) ρ :=
    (hclt.continuous_comp hGc).of_hasLaw ⟨hGc.aemeasurable, rfl⟩ HasLaw.id
  have hlan := logLikRatio_sub_tendstoInMeasure hO hlaw hreg hs hdl h
  have hj3 : TendstoInDistribution (fun (k : ℕ) ω ↦
      (√(k : ℝ) * (T k (fun i ↦ O i ω) - θ₀), F.logLikRatio O θ₀ (θ₀ + h / √(k : ℝ)) k ω))
      atTop id (fun _ ↦ μ) ρ := by
    refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hj2 ?_
      fun k ↦ (hXm k).prodMk (aemeasurable_logLikRatio hO _ k)
    have hp := hlin.remainder.prodMk (a := (0 : ℝ)) (b := (0 : ℝ)) hlan
    refine hp.congr' (Eventually.of_forall fun k ↦ Eventually.of_forall fun ω ↦ ?_)
      (Eventually.of_forall fun _ ↦ rfl)
    have hsum : (√(k : ℝ))⁻¹ * ∑ i ∈ range k, I⁻¹ * F.score θ₀ (O i ω) =
        I⁻¹ * ((√(k : ℝ))⁻¹ * ∑ i ∈ range k, F.score θ₀ (O i ω)) := by
      rw [← Finset.mul_sum]; ring
    simp only [Pi.sub_apply, Prod.mk_sub_mk, hG, ← hIdef, hsum]
  have hmass : ∫ p, Real.exp p.2 ∂ρ = 1 := by
    rw [hρ, integral_map hGc.aemeasurable (by fun_prop)]
    have hv : I.toNNReal ≠ 0 := by simpa using hI
    have := integral_mul_exp_gaussianReal hv h (f := fun _ ↦ 1) measurable_const
    simp only [one_mul, integral_const, smul_eq_mul, Real.coe_toNNReal I hI.le,
      measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] at this
    exact this
  let f' : ℝ →ᵇ ℝ := f.compContinuous ⟨fun y ↦ y - h, by fun_prop⟩
  have hf' : ∀ y, f' y = f (y - h) := fun y ↦ rfl
  have h3 := tendsto_integral_pi_law_of_tendstoInDistribution hO hlaw hreg.mem_nhds
    hreg.support hTm (m := fun k ↦ k) tendsto_id h hj3 hmass f'
  have hlim : ∫ p, f' p.1 * Real.exp p.2 ∂ρ = ∫ y, f y ∂gaussianReal 0 I⁻¹.toNNReal := by
    have hv : I.toNNReal ≠ 0 := by simpa using hI
    rw [hρ, integral_map hGc.aemeasurable (by fun_prop)]
    have e1 := integral_mul_exp_gaussianReal hv h (f := fun z ↦ f' (I⁻¹ * z))
      (f'.continuous.comp (continuous_const.mul continuous_id)).measurable
    simp only [Real.coe_toNNReal I hI.le] at e1
    simp only [hG]
    rw [e1, ← gaussianReal_map_inv_mul hI,
      integral_map (measurable_const_mul _).aemeasurable f.continuous.aestronglyMeasurable]
    refine integral_congr_ae (Eventually.of_forall fun z ↦ ?_)
    simp only [hf']
    congr 1
    field_simp
    ring
  rw [hlim] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hs0 : √(n : ℝ) ≠ 0 := (Real.sqrt_pos.2 (Nat.cast_pos.2 hn)).ne'
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp only [hf']
  congr 1
  field_simp
  ring

end ParametricFamily

end CausalInference
