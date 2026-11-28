/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.HajekConvolutionGeneral
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# The Hájek convolution theorem

In a regular family with positive information `I(θ₀)`, the limit law `L` of every estimator
regular at `θ₀` in Hájek's sense is a convolution `L = N(0, I(θ₀)⁻¹) ∗ M` of the efficient
Gaussian law with some probability measure `M`. No moment condition on `L` is needed.

The proof starts from a joint law `μ` of `(X, Z)` with `X ∼ L`, `Z ∼ N(0, I)` and the tilt
identity `∫ f(x + h) dL = ∫ f(x) e^{h z - h² I / 2} dμ(x, z)` for real `h`
(`hajek_tilt_subseq_general`). For a fixed `t`, the function
`F(w) = ∫ e^{i t x} e^{w z} dμ(x, z)` of a complex `w` is entire (the Gaussian marginal has all
exponential moments), and for real `h` the tilt identity with `f = cos(t ·)` and `f = sin(t ·)`
gives `F(h) = e^{h² I / 2 + i t h} φ_L(t)`. By the identity theorem the two entire functions agree
everywhere. At `w = -i t / I`, `F(w) = φ_M(t)` with `M` the law of `X - I⁻¹ Z`, and the right side
is `e^{t² / (2 I)} φ_L(t)`; so `φ_L(t) = e^{-t² / (2 I)} φ_M(t)`, the characteristic function of
`N(0, I⁻¹) ∗ M`.

## Main results

* `CausalInference.differentiable_integral_exp_mul_snd`: `F` is entire.
* `CausalInference.tilt_eq_conv`: under the tilt identity, `L = N(0, I⁻¹) ∗ M` with `M` the law
  of `X - I⁻¹ Z` under `μ`.
* `CausalInference.variance_gaussianReal_conv`: `Var(N(0, v) ∗ M) = v + Var(M)`.
* `CausalInference.ParametricFamily.hajek_convolution`: the convolution theorem for a regular
  estimator.
* `CausalInference.ParametricFamily.hajek_convolution_variance`: for `L` of finite second moment,
  `Var(L) = I(θ₀)⁻¹ + Var(M)`, the variance bound read off the convolution.

References: J. Hájek (1970), *A characterization of limiting distributions of regular
estimates*, Zeitschrift für Wahrscheinlichkeitstheorie und verwandte Gebiete; A. W. van der
Vaart (1998), *Asymptotic Statistics*, chapter 8.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Metric
open scoped Topology ENNReal NNReal BoundedContinuousFunction

namespace CausalInference

section Analytic

variable {μ : Measure (ℝ × ℝ)}

/-- `∫ e^{i a} w = ∫ cos(a) w + i ∫ sin(a) w` for real `a` and `w`. -/
lemma integral_cexp_mul_I_mul_ofReal {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {a w : X → ℝ} (hc : Integrable (fun x ↦ Real.cos (a x) * w x) ν)
    (hs : Integrable (fun x ↦ Real.sin (a x) * w x) ν) :
    ∫ x, Complex.exp ((a x : ℂ) * Complex.I) * (w x : ℂ) ∂ν =
      ((∫ x, Real.cos (a x) * w x ∂ν : ℝ) : ℂ) +
        ((∫ x, Real.sin (a x) * w x ∂ν : ℝ) : ℂ) * Complex.I := by
  have h : ∀ x, Complex.exp ((a x : ℂ) * Complex.I) * (w x : ℂ) =
      ((Real.cos (a x) * w x : ℝ) : ℂ) + ((Real.sin (a x) * w x : ℝ) : ℂ) * Complex.I := by
    intro x
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast
    ring
  simp_rw [h]
  rw [integral_add hc.ofReal (hs.ofReal.mul_const _), integral_mul_const,
    integral_complex_ofReal, integral_complex_ofReal]

/-- The integrand `e^{i t x} e^{w z}` is dominated by `e^{K |z|}` for `|Re w| ≤ K`. -/
lemma norm_cexp_mul_I_mul_cexp_le (t x z : ℝ) (w : ℂ) {K : ℝ} (hK : |w.re| ≤ K) :
    ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) * Complex.exp (w * z)‖ ≤
      Real.exp (K * |z|) := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_exp]
  refine Real.exp_le_exp.2 ?_
  have : (w * (z : ℂ)).re = w.re * z := by simp
  rw [this]
  calc w.re * z ≤ |w.re * z| := le_abs_self _
    _ = |w.re| * |z| := abs_mul _ _
    _ ≤ K * |z| := mul_le_mul_of_nonneg_right hK (abs_nonneg _)

variable {v : ℝ≥0} (hZ : μ.map Prod.snd = gaussianReal 0 v)
include hZ

/-- The integrand `e^{i t x} e^{w z}` is integrable when the second marginal is Gaussian. -/
lemma integrable_cexp_mul_I_mul_cexp_snd (t : ℝ) (w : ℂ) :
    Integrable (fun p : ℝ × ℝ ↦
      Complex.exp (((t * p.1 : ℝ) : ℂ) * Complex.I) * Complex.exp (w * p.2)) μ :=
  (integrable_exp_mul_abs_snd hZ |w.re|).mono' (by fun_prop)
    (Eventually.of_forall fun p ↦ norm_cexp_mul_I_mul_cexp_le t p.1 p.2 w le_rfl)

/-- **The transform `w ↦ ∫ e^{i t x} e^{w z} dμ(x, z)` is entire** when the second marginal of
`μ` is Gaussian: differentiate under the integral sign, the derivative `z e^{i t x} e^{w z}` being
dominated near `w₀` by `e^{(|Re w₀| + 2) |z|}`. -/
theorem differentiable_integral_exp_mul_snd (t : ℝ) :
    Differentiable ℂ fun w : ℂ ↦ ∫ p, Complex.exp (((t * p.1 : ℝ) : ℂ) * Complex.I) *
      Complex.exp (w * p.2) ∂μ := by
  intro w₀
  set K := |w₀.re| + 1 with hK
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (𝕜 := ℂ)
    (F := fun w p ↦ Complex.exp (((t * p.1 : ℝ) : ℂ) * Complex.I) * Complex.exp (w * p.2))
    (F' := fun w p ↦ Complex.exp (((t * p.1 : ℝ) : ℂ) * Complex.I) *
      (Complex.exp (w * p.2) * p.2))
    (x₀ := w₀) (bound := fun p ↦ Real.exp ((K + 1) * |p.2|)) (Metric.ball_mem_nhds w₀ one_pos)
    (Eventually.of_forall fun w ↦ (integrable_cexp_mul_I_mul_cexp_snd hZ t w).aestronglyMeasurable)
    (integrable_cexp_mul_I_mul_cexp_snd hZ t w₀)
    ((by fun_prop : Continuous fun p : ℝ × ℝ ↦ Complex.exp (((t * p.1 : ℝ) : ℂ) * Complex.I) *
      (Complex.exp (w₀ * p.2) * p.2)).aestronglyMeasurable)
    (Eventually.of_forall fun p w hw ↦ by
      have hre : |w.re| ≤ K := by
        have h1 : |w.re - w₀.re| ≤ ‖w - w₀‖ := by
          rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
        have h2 : ‖w - w₀‖ < 1 := by rwa [← dist_eq_norm]
        have h3 := abs_sub_abs_le_abs_sub w.re w₀.re
        rw [hK]; linarith
      have hb := norm_cexp_mul_I_mul_cexp_le t p.1 p.2 w hre
      rw [← mul_assoc, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hz : |p.2| ≤ Real.exp (1 * |p.2|) := by
        have := Real.add_one_le_exp (1 * |p.2|); linarith
      calc ‖Complex.exp (((t * p.1 : ℝ) : ℂ) * Complex.I) * Complex.exp (w * p.2)‖ * |p.2|
          ≤ Real.exp (K * |p.2|) * Real.exp (1 * |p.2|) :=
            mul_le_mul hb hz (abs_nonneg _) (Real.exp_pos _).le
        _ = Real.exp ((K + 1) * |p.2|) := by rw [← Real.exp_add]; ring_nf)
    (integrable_exp_mul_abs_snd hZ (K + 1))
    (Eventually.of_forall fun p w _ ↦ by
      have := ((hasDerivAt_id w).mul_const (p.2 : ℂ)).cexp
      simp only [id, one_mul] at this
      exact this.const_mul _)
  exact hd.2.differentiableAt

end Analytic

section Convolution

variable {μ : Measure (ℝ × ℝ)} [IsProbabilityMeasure μ] {L : Measure ℝ} [IsProbabilityMeasure L]
  {I : ℝ}

omit [IsProbabilityMeasure μ] in
/-- **The tilt identity in complex form.** Under the tilt identity, for real `h` and `t`,
`∫ e^{i t x} e^{h z} dμ = e^{h² I / 2 + i t h} φ_L(t)`. -/
theorem integral_exp_mul_snd_ofReal (hI : 0 < I)
    (hZ : μ.map Prod.snd = gaussianReal 0 I.toNNReal)
    (htilt : ∀ h : ℝ, ∀ f : ℝ →ᵇ ℝ, ∫ x, f (x + h) ∂L =
      ∫ p, f p.1 * Real.exp (h * p.2 - h ^ 2 * I / 2) ∂μ) (t h : ℝ) :
    ∫ p, Complex.exp (((t * p.1 : ℝ) : ℂ) * Complex.I) * Complex.exp ((h : ℂ) * p.2) ∂μ =
      Complex.exp ((h : ℂ) ^ 2 * I / 2 + t * h * Complex.I) * charFun L t := by
  let fc : ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x ↦ Real.cos (t * x)) (by fun_prop) 1
    (fun x ↦ by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  let fs : ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x ↦ Real.sin (t * x)) (by fun_prop) 1
    (fun x ↦ by rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  have hc := htilt h fc
  have hs := htilt h fs
  simp only [fc, fs, BoundedContinuousFunction.coe_ofNormedAddCommGroup] at hc hs
  have hexp : Integrable (fun p : ℝ × ℝ ↦ Real.exp (h * p.2 - h ^ 2 * I / 2)) μ := by
    refine (integrable_exp_mul_abs_snd hZ |h|).mono' (by fun_prop)
      (Eventually.of_forall fun p ↦ ?_)
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    refine Real.exp_le_exp.2 ?_
    have : h * p.2 ≤ |h| * |p.2| := by rw [← abs_mul]; exact le_abs_self _
    nlinarith [sq_nonneg h]
  have hbc : ∀ g : ℝ → ℝ, Continuous g → (∀ x, |g x| ≤ 1) →
      Integrable (fun p : ℝ × ℝ ↦ g (t * p.1) * Real.exp (h * p.2 - h ^ 2 * I / 2)) μ :=
    fun g hg hb ↦ hexp.bdd_mul (c := 1) (by fun_prop)
      (Eventually.of_forall fun p ↦ by rw [Real.norm_eq_abs]; exact hb _)
  have hμ := integral_cexp_mul_I_mul_ofReal (ν := μ) (a := fun p ↦ t * p.1)
    (w := fun p ↦ Real.exp (h * p.2 - h ^ 2 * I / 2))
    (hbc _ Real.continuous_cos Real.abs_cos_le_one)
    (hbc _ Real.continuous_sin Real.abs_sin_le_one)
  have hL := integral_cexp_mul_I_mul_ofReal (ν := L) (a := fun x ↦ t * (x + h)) (w := fun _ ↦ 1)
    (Integrable.of_bound (by fun_prop) 1 (Eventually.of_forall fun x ↦ by
      rw [mul_one, Real.norm_eq_abs]; exact Real.abs_cos_le_one _))
    (Integrable.of_bound (by fun_prop) 1 (Eventually.of_forall fun x ↦ by
      rw [mul_one, Real.norm_eq_abs]; exact Real.abs_sin_le_one _))
  simp only [mul_one, Complex.ofReal_one] at hL
  rw [← hc, ← hs, ← hL] at hμ
  have hsplit : ∀ p : ℝ × ℝ, Complex.exp ((h : ℂ) * p.2) =
      Complex.exp ((h : ℂ) ^ 2 * I / 2) *
        ((Real.exp (h * p.2 - h ^ 2 * I / 2) : ℝ) : ℂ) := by
    intro p
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hshift : ∀ x : ℝ, Complex.exp (((t * (x + h) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (t * h * Complex.I) * Complex.exp (t * x * Complex.I) := by
    intro x
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [hsplit, hshift] at *
  rw [charFun_apply_real, Complex.exp_add, mul_assoc, ← integral_const_mul, ← integral_const_mul,
    integral_const_mul, ← hμ, ← integral_const_mul]
  congr 1
  funext p
  ring

/-- **The tilt identity makes `L` a convolution with the efficient Gaussian law.** Let `μ` be a
probability law of `(X, Z)` with `Z ∼ N(0, I)`, `I > 0`, and the tilt identity
`∫ f(x + h) dL = ∫ f(x) e^{h z - h² I / 2} dμ(x, z)` for every real `h` and bounded continuous `f`.
Then `L = N(0, I⁻¹) ∗ M`, where `M` is the law of `X - I⁻¹ Z` under `μ`. The identity at `h = 0`
makes `L` the law of `X`; no moment of `L` is used. -/
theorem tilt_eq_conv (hI : 0 < I) (hZ : μ.map Prod.snd = gaussianReal 0 I.toNNReal)
    (htilt : ∀ h : ℝ, ∀ f : ℝ →ᵇ ℝ, ∫ x, f (x + h) ∂L =
      ∫ p, f p.1 * Real.exp (h * p.2 - h ^ 2 * I / 2) ∂μ) :
    L = gaussianReal 0 I⁻¹.toNNReal ∗ μ.map (fun p ↦ p.1 - I⁻¹ * p.2) := by
  have hI0 : (I : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hI.ne'
  refine Measure.ext_of_charFun (funext fun t ↦ ?_)
  -- the entire functions `F` and `G`
  set F : ℂ → ℂ := fun w ↦ ∫ p, Complex.exp (((t * p.1 : ℝ) : ℂ) * Complex.I) *
    Complex.exp (w * p.2) ∂μ with hF
  set G : ℂ → ℂ := fun w ↦ Complex.exp (w ^ 2 * I / 2 + t * w * Complex.I) * charFun L t
    with hG
  have hFa : AnalyticOnNhd ℂ F Set.univ := fun w _ ↦
    (differentiable_integral_exp_mul_snd hZ t).analyticAt w
  have hGa : AnalyticOnNhd ℂ G Set.univ := fun w _ ↦
    (by fun_prop : Differentiable ℂ G).analyticAt w
  have hreal : ∀ h : ℝ, F h = G h := fun h ↦ integral_exp_mul_snd_ofReal hI hZ htilt t h
  have hfreq : ∃ᶠ w in 𝓝[≠] (0 : ℂ), F w = G w := by
    have hmap : Tendsto (fun x : ℝ ↦ (x : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have := (Complex.continuous_ofReal.tendsto 0).mono_left
          (nhdsWithin_le_nhds (s := {(0 : ℝ)}ᶜ))
        simpa using this
      · filter_upwards [self_mem_nhdsWithin] with x hx
        simpa using hx
    exact hmap.frequently (Eventually.of_forall hreal).frequently
  have hFG := hFa.eq_of_frequently_eq hGa hfreq
  -- evaluate at `w = -i t / I`
  set w₀ : ℂ := -(t / I) * Complex.I with hw₀
  have hFw : F w₀ = charFun (μ.map fun p ↦ p.1 - I⁻¹ * p.2) t := by
    rw [charFun_apply_real, integral_map (by fun_prop) (by fun_prop), hF]
    refine integral_congr_ae (Eventually.of_forall fun p ↦ ?_)
    dsimp only
    rw [← Complex.exp_add, hw₀]
    congr 1
    push_cast
    field_simp
    ring
  have hGw : G w₀ = Complex.exp (t ^ 2 / (2 * I)) * charFun L t := by
    rw [hG]
    dsimp only
    congr 2
    rw [hw₀]
    field_simp
    linear_combination (-(t : ℂ) ^ 2) * Complex.I_sq
  have hkey : charFun (μ.map fun p ↦ p.1 - I⁻¹ * p.2) t =
      Complex.exp (t ^ 2 / (2 * I)) * charFun L t := by
    rw [← hFw, ← hGw, hFG]
  rw [charFun_conv, charFun_gaussianReal, hkey, ← mul_assoc, ← Complex.exp_add,
    Real.coe_toNNReal _ (inv_nonneg.2 hI.le)]
  have : (t : ℂ) * ((0 : ℝ) : ℂ) * Complex.I - ((I⁻¹ : ℝ) : ℂ) * t ^ 2 / 2 + t ^ 2 / (2 * I) =
      0 := by
    push_cast
    field_simp
    ring
  rw [this, Complex.exp_zero, one_mul]

/-- **The variance of a Gaussian convolution.** For a probability measure `M` with finite
second moment, `Var(N(0, v) ∗ M) = v + Var(M)`: the convolution is the law of the sum of the
coordinates under the product measure, whose coordinates are independent. -/
theorem variance_gaussianReal_conv {M : Measure ℝ} [IsProbabilityMeasure M] (hM : MemLp id 2 M)
    (v : ℝ≥0) : Var[id; gaussianReal 0 v ∗ M] = v + Var[id; M] := by
  rw [Measure.conv, variance_map aemeasurable_id (by fun_prop)]
  have h := variance_add_prod (μ := gaussianReal 0 v) (ν := M) (X := id) (Y := id)
    (memLp_id_gaussianReal 2) hM
  rw [variance_id_gaussianReal] at h
  exact h

end Convolution

/-! ### The convolution theorem for regular estimators -/

namespace ParametricFamily

variable {S : Type*} [MeasurableSpace S] {F : ParametricFamily ℝ S} [SigmaFinite F.ν] {θ₀ : ℝ}

/-- **The Hájek convolution theorem.** In a family regular at `θ₀` with positive information
`I(θ₀)`, the second derivative of the log density smooth with an integrable envelope on a closed
ball around `θ₀` (`IsScoreRegular`) and `θ ↦ ℓ(θ; z)` with derivative `s(θ; z)` there, the limit
law `L` of every estimator regular at `θ₀` in Hájek's sense is a convolution
`L = N(0, I(θ₀)⁻¹) ∗ M` with a probability measure `M`. Here `M` is the law of
`X - I(θ₀)⁻¹ Z` under a joint limit `(X, Z)` of `√n (T_n - θ₀)` and the normalized score. -/
theorem hajek_convolution (hreg : F.IsRegularAt θ₀) {r : ℝ} (hs : F.IsScoreRegular θ₀ r)
    (hdl : ∀ᵐ z ∂F.law θ₀, ∀ θ ∈ closedBall θ₀ r,
      HasDerivAt (fun u ↦ F.logLik u z) (F.score θ z) θ)
    (hI : 0 < F.fisherInfo θ₀) {T : ∀ n, (Fin n → S) → ℝ} {L : Measure ℝ}
    (hT : F.IsHajekRegular T θ₀ L) :
    ∃ M : ProbabilityMeasure ℝ,
      L = gaussianReal 0 (F.fisherInfo θ₀)⁻¹.toNNReal ∗ (M : Measure ℝ) := by
  have := isProbabilityMeasure_law (mem_of_mem_nhds hreg.mem_nhds)
  have := hT.isProbabilityMeasure (mem_of_mem_nhds hreg.mem_nhds)
  obtain ⟨Ω', _, P', O', hP', -, hO', hlaw'⟩ := exists_isIIDSample (F.law θ₀)
  obtain ⟨φ, -, μ', -, -, h2, ht⟩ := hajek_tilt_subseq_general hO' (hlaw' 0).map_eq hreg hs hdl
    hI hT tendsto_id
  refine ⟨μ'.map fun p : ℝ × ℝ ↦ p.1 - (F.fisherInfo θ₀)⁻¹ * p.2, ?_⟩
  rw [ProbabilityMeasure.toMeasure_map]
  exact tilt_eq_conv hI h2 ht

/-- **The variance bound from the convolution theorem.** Under the hypotheses of
`hajek_convolution`, if the limit law `L` has a finite second moment, then `L = N(0, I(θ₀)⁻¹) ∗ M`
with `M` a probability measure of finite second moment and `Var(L) = I(θ₀)⁻¹ + Var(M)`; in
particular `Var(L) ≥ I(θ₀)⁻¹`, the excess being the variance of the independent noise `M`. -/
theorem hajek_convolution_variance (hreg : F.IsRegularAt θ₀) {r : ℝ}
    (hs : F.IsScoreRegular θ₀ r)
    (hdl : ∀ᵐ z ∂F.law θ₀, ∀ θ ∈ closedBall θ₀ r,
      HasDerivAt (fun u ↦ F.logLik u z) (F.score θ z) θ)
    (hI : 0 < F.fisherInfo θ₀) {T : ∀ n, (Fin n → S) → ℝ} {L : Measure ℝ}
    (hT : F.IsHajekRegular T θ₀ L) (hL : MemLp id 2 L) :
    ∃ M : ProbabilityMeasure ℝ, MemLp id 2 (M : Measure ℝ) ∧
      L = gaussianReal 0 (F.fisherInfo θ₀)⁻¹.toNNReal ∗ (M : Measure ℝ) ∧
      Var[id; L] = (F.fisherInfo θ₀)⁻¹ + Var[id; (M : Measure ℝ)] := by
  have := isProbabilityMeasure_law (mem_of_mem_nhds hreg.mem_nhds)
  have := hT.isProbabilityMeasure (mem_of_mem_nhds hreg.mem_nhds)
  obtain ⟨Ω', _, P', O', hP', -, hO', hlaw'⟩ := exists_isIIDSample (F.law θ₀)
  obtain ⟨φ, -, μ', -, h1, h2, ht⟩ := hajek_tilt_subseq_general hO' (hlaw' 0).map_eq hreg hs
    hdl hI hT tendsto_id
  set w : ℝ × ℝ → ℝ := fun p ↦ p.1 - (F.fisherInfo θ₀)⁻¹ * p.2 with hw
  have hx : MemLp (fun p : ℝ × ℝ ↦ p.1) 2 (μ' : Measure (ℝ × ℝ)) :=
    (memLp_map_measure_iff aestronglyMeasurable_id measurable_fst.aemeasurable).1
      (by rw [h1]; exact hL)
  have hz : MemLp (fun p : ℝ × ℝ ↦ p.2) 2 (μ' : Measure (ℝ × ℝ)) :=
    (memLp_map_measure_iff aestronglyMeasurable_id measurable_snd.aemeasurable).1
      (by rw [h2]; exact memLp_id_gaussianReal 2)
  have hM : MemLp id 2 ((μ' : Measure (ℝ × ℝ)).map w) :=
    (memLp_map_measure_iff aestronglyMeasurable_id (by fun_prop)).2
      (hx.sub (hz.const_mul _))
  have hconv := tilt_eq_conv hI h2 ht
  refine ⟨μ'.map w, by rwa [ProbabilityMeasure.toMeasure_map], by
    rwa [ProbabilityMeasure.toMeasure_map], ?_⟩
  rw [ProbabilityMeasure.toMeasure_map]
  conv_lhs => rw [hconv]
  rw [variance_gaussianReal_conv hM, Real.coe_toNNReal _ (inv_nonneg.2 hI.le)]

end ParametricFamily

end CausalInference
