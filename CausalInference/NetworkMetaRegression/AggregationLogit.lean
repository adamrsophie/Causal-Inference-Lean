/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.AggregationLeadingOrder
public import Mathlib.Analysis.SpecialFunctions.Sigmoid

/-!
# The logit link: bounds and signs of the aggregation bias

On the logit link the aggregate mean of a Gaussian linear predictor `N(m, τ)` is the logit
normal mean `J(m, τ) = ∫ σ dN(m, τ)`, which has no closed form. This file proves what holds
without one: reflection, the value at `m = 0`, strict monotonicity in `m`, the exact sign of the
bias `J(m, τ) - σ(m)` for every `τ > 0`, and its leading order `½ σ''(m) τ`.

## Main results

* `logitNormalMean_reflect`, `logitNormalMean_zero`, `logitNormalMean_strictMono`.
* `logitNormalMean_lt_sigmoid`, `sigmoid_lt_logitNormalMean`: for `τ > 0` the plug in
  probability `σ(m)` overstates the aggregate mean when `m > 0` and understates it when `m < 0`.
* `isLittleO_logitNormalMean_sub`: `J(m, τ) - σ(m) = ½ σ''(m) τ + o(τ)` as `τ → 0`.
* `MultilevelModel.armMean_sigmoid_gaussian`, `MultilevelModel.aggBias_sigmoid_neg`,
  `MultilevelModel.aggBias_sigmoid_pos`: the same for an arm under Gaussian covariates, with
  `m = η_k(x̄)` and `τ = v_k`: the logit aggregation bias pulls the probability toward `1/2`.

## References

* D. M. Phillippo, S. Dias, A. E. Ades, M. Belger, A. Brnabic, A. Schacht, D. Saure, Z. Kadziola
  and N. J. Welton, *Multilevel network meta-regression for population-adjusted treatment
  comparisons*, Journal of the Royal Statistical Society Series A 183 (2020).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaRegression

open MeasureTheory ProbabilityTheory IndirectComparison NetworkMetaAnalysis
open scoped NNReal

section Logit

open Real

/-- The derivative `σ' = σ(1 - σ)` of the logistic function `σ`. -/
noncomputable def sigmoidDeriv1 (x : ℝ) : ℝ := sigmoid x * (1 - sigmoid x)

/-- The second derivative `σ'' = σ(1 - σ)(1 - 2σ)`. -/
noncomputable def sigmoidDeriv2 (x : ℝ) : ℝ := sigmoidDeriv1 x * (1 - 2 * sigmoid x)

/-- The third derivative `σ(1 - σ)(1 - 6σ + 6σ²)`. -/
noncomputable def sigmoidDeriv3 (x : ℝ) : ℝ :=
  sigmoidDeriv1 x * (1 - 6 * sigmoid x + 6 * sigmoid x ^ 2)

theorem hasDerivAt_sigmoidD1 (x : ℝ) : HasDerivAt sigmoidDeriv1 (sigmoidDeriv2 x) x := by
  have h := hasDerivAt_sigmoid x
  have e : sigmoidDeriv2 x = sigmoid x * (1 - sigmoid x) * (1 - sigmoid x) +
      sigmoid x * -(sigmoid x * (1 - sigmoid x)) := by
    unfold sigmoidDeriv2 sigmoidDeriv1; ring
  rw [e]; exact h.mul (h.const_sub 1)

theorem hasDerivAt_sigmoidD2 (x : ℝ) : HasDerivAt sigmoidDeriv2 (sigmoidDeriv3 x) x := by
  have h := hasDerivAt_sigmoid x
  have e : sigmoidDeriv3 x = sigmoidDeriv2 x * (1 - 2 * sigmoid x) +
      sigmoidDeriv1 x * -(2 * (sigmoid x * (1 - sigmoid x))) := by
    unfold sigmoidDeriv3 sigmoidDeriv2 sigmoidDeriv1; ring
  rw [e]; exact (hasDerivAt_sigmoidD1 x).mul ((h.const_mul 2).const_sub 1)

/-- `σ' > 0`. -/
theorem sigmoidDeriv1_pos (x : ℝ) : 0 < sigmoidDeriv1 x :=
  mul_pos (sigmoid_pos x) (sub_pos.mpr (sigmoid_lt_one x))

theorem abs_sigmoidD1_le (x : ℝ) : |sigmoidDeriv1 x| ≤ 1 := by
  rw [abs_of_pos (sigmoidDeriv1_pos x), sigmoidDeriv1]
  nlinarith [sigmoid_pos x, sigmoid_lt_one x]

theorem abs_sigmoidD3_le (x : ℝ) : |sigmoidDeriv3 x| ≤ 1 := by
  have h0 := sigmoid_pos x
  have h1 := sigmoid_lt_one x
  have hq : |1 - 6 * sigmoid x + 6 * sigmoid x ^ 2| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith
  rw [sigmoidDeriv3, abs_mul]
  calc |sigmoidDeriv1 x| * |1 - 6 * sigmoid x + 6 * sigmoid x ^ 2| ≤ 1 * 1 :=
        mul_le_mul (abs_sigmoidD1_le x) hq (abs_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- A continuous function bounded by one is integrable for a finite measure. -/
theorem integrable_of_abs_le_one_of_continuous {ν : Measure ℝ} [IsFiniteMeasure ν] {f : ℝ → ℝ}
    (hf : Continuous f) (h : ∀ x, |f x| ≤ 1) : Integrable f ν :=
  (integrable_const 1).mono' hf.aestronglyMeasurable (ae_of_all _ fun x => by
    rw [Real.norm_eq_abs]; exact h x)

theorem continuous_sigmoidD1 : Continuous sigmoidDeriv1 := by
  unfold sigmoidDeriv1; fun_prop

/-- A strict integral inequality from a pointwise one that is strict on a set of positive
measure. -/
theorem integral_lt_integral_of_le_of_measure_ne {ν : Measure ℝ} [IsFiniteMeasure ν] {f g : ℝ → ℝ}
    (hf : Integrable f ν) (hg : Integrable g ν) (hle : ∀ x, f x ≤ g x)
    (hlt : ν {x | f x < g x} ≠ 0) : ∫ x, f x ∂ν < ∫ x, g x ∂ν := by
  rw [← sub_pos, ← integral_sub hg hf, integral_pos_iff_support_of_nonneg
    (fun x => sub_nonneg.mpr (hle x)) (hg.sub hf)]
  refine pos_iff_ne_zero.mpr (mt (measure_mono_null ?_) hlt)
  intro x hx
  simp only [Function.mem_support, ne_eq, sub_eq_zero]
  exact (Set.mem_ofPred_eq ▸ hx).ne'

/-- The **logit normal mean** `J(m, τ) = ∫ σ dN(m, τ)`: the aggregate mean of the logit link
when the linear predictor is `N(m, τ)`. It has no closed form; only bounds and signs follow. -/
noncomputable def logitNormalMean (m : ℝ) (τ : ℝ≥0) : ℝ := ∫ z, sigmoid z ∂(gaussianReal m τ)

/-- `J(m, τ) = E σ(m + W)` with `W ∼ N(0, τ)`. -/
theorem logitNormalMean_eq_shift (m : ℝ) (τ : ℝ≥0) :
    logitNormalMean m τ = ∫ z, sigmoid (m + z) ∂(gaussianReal 0 τ) := by
  have h := gaussianReal_map_const_add (μ := 0) (v := τ) m
  rw [zero_add] at h
  rw [logitNormalMean, ← h, integral_map (by fun_prop) continuous_sigmoid.aestronglyMeasurable]

/-- **Reflection**: `J(m, τ) = 1 - J(-m, τ)`. -/
theorem logitNormalMean_reflect (m : ℝ) (τ : ℝ≥0) :
    logitNormalMean m τ = 1 - logitNormalMean (-m) τ := by
  have hint : Integrable sigmoid (gaussianReal m τ) :=
    integrable_of_abs_le_one_of_continuous continuous_sigmoid fun x => by
      rw [abs_of_pos (sigmoid_pos x)]; exact sigmoid_le_one x
  rw [logitNormalMean, logitNormalMean, ← gaussianReal_map_neg,
    integral_map (by fun_prop) continuous_sigmoid.aestronglyMeasurable]
  simp_rw [sigmoid_neg]
  rw [integral_sub (integrable_const 1) hint]
  simp

/-- **The symmetric point**: `J(0, τ) = 1/2 = σ(0)` for every `τ`. -/
theorem logitNormalMean_zero (τ : ℝ≥0) :
    logitNormalMean 0 τ = 1 / 2 ∧ logitNormalMean 0 τ = sigmoid 0 := by
  have h := logitNormalMean_reflect 0 τ
  rw [neg_zero] at h
  have h2 : logitNormalMean 0 τ = 1 / 2 := by linarith
  exact ⟨h2, by rw [h2, sigmoid_zero]; norm_num⟩

/-- **Monotonicity in the location**: `∂_m J = E σ'(N(m, τ)) > 0`. -/
theorem logitNormalMean_hasDerivAt (m : ℝ) (τ : ℝ≥0) :
    HasDerivAt (fun m => logitNormalMean m τ) (∫ z, sigmoidDeriv1 z ∂(gaussianReal m τ)) m ∧
      0 < ∫ z, sigmoidDeriv1 z ∂(gaussianReal m τ) := by
  constructor
  · have hshift : ∫ z, sigmoidDeriv1 z ∂(gaussianReal m τ) =
        ∫ z, sigmoidDeriv1 (m + z) ∂(gaussianReal 0 τ) := by
      have h := gaussianReal_map_const_add (μ := 0) (v := τ) m
      rw [zero_add] at h
      rw [← h, integral_map (by fun_prop) continuous_sigmoidD1.aestronglyMeasurable]
    rw [hshift, show (fun m => logitNormalMean m τ) =
      fun m => ∫ z, sigmoid (m + z) ∂(gaussianReal 0 τ) from
        funext fun m => logitNormalMean_eq_shift m τ]
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun _ => 1)
      (F' := fun m z => sigmoidDeriv1 (m + z)) Filter.univ_mem
      (Filter.Eventually.of_forall fun m => (by fun_prop : Continuous fun z => sigmoid (m + z))
        |>.aestronglyMeasurable)
      (integrable_of_abs_le_one_of_continuous (by fun_prop) fun x => by
        rw [abs_of_pos (sigmoid_pos _)]; exact sigmoid_le_one _)
      (continuous_sigmoidD1.comp (continuous_const.add continuous_id)).aestronglyMeasurable
      (ae_of_all _ fun z x _ => by rw [Real.norm_eq_abs]; exact abs_sigmoidD1_le _)
      (integrable_const 1) (ae_of_all _ fun z x _ => ?_)).2
    have := (hasDerivAt_sigmoid (x + z)).comp x ((hasDerivAt_id x).add_const z)
    simpa [sigmoidDeriv1, Function.comp_def] using this
  · rw [integral_pos_iff_support_of_nonneg (fun x => (sigmoidDeriv1_pos x).le)
      (integrable_of_abs_le_one_of_continuous continuous_sigmoidD1 abs_sigmoidD1_le)]
    have : Function.support sigmoidDeriv1 = Set.univ :=
      Set.eq_univ_of_forall fun x => (sigmoidDeriv1_pos x).ne'
    simp [this]

/-- `J(·, τ)` is strictly increasing. -/
theorem logitNormalMean_strictMono (τ : ℝ≥0) : StrictMono fun m => logitNormalMean m τ := by
  intro m m' hmm'
  simp only [logitNormalMean_eq_shift]
  refine integral_lt_integral_of_le_of_measure_ne
    (integrable_of_abs_le_one_of_continuous (by fun_prop) fun x => by
      rw [abs_of_pos (sigmoid_pos _)]; exact sigmoid_le_one _)
    (integrable_of_abs_le_one_of_continuous (by fun_prop) fun x => by
      rw [abs_of_pos (sigmoid_pos _)]; exact sigmoid_le_one _)
    (fun z => (sigmoid_strictMono (by linarith)).le) ?_
  have : {z : ℝ | sigmoid (m + z) < sigmoid (m' + z)} = Set.univ :=
    Set.eq_univ_of_forall fun z => sigmoid_strictMono (by linarith)
  simp [this]

/-- For `m > 0` and `z ≠ 0`, `σ(m + z) + σ(m - z) < 2σ(m)`. -/
theorem sigmoid_add_add_sigmoid_sub_lt {m z : ℝ} (hm : 0 < m) (hz : z ≠ 0) :
    sigmoid (m + z) + sigmoid (m - z) < 2 * sigmoid m := by
  set a := Real.exp (-m) with ha
  set c := Real.exp (-z) with hc
  have ha0 : 0 < a := Real.exp_pos _
  have ha1 : a < 1 := (Real.exp_lt_exp.mpr (by linarith : -m < 0)).trans_eq Real.exp_zero
  have hc0 : 0 < c := Real.exp_pos _
  have hc1 : c ≠ 1 := by
    rw [hc]; intro h; exact hz (by simpa using Real.exp_eq_one_iff (-z) |>.mp h)
  have e1 : Real.exp (-(m + z)) = a * c := by rw [neg_add, Real.exp_add]
  have e2 : Real.exp (-(m - z)) = a / c := by
    rw [show -(m - z) = -m + z by ring, Real.exp_add, hc, Real.exp_neg z, div_inv_eq_mul]
  rw [sigmoid_def, sigmoid_def, sigmoid_def, e1, e2, ← ha]
  have hpos : 0 < a * (1 - a) * (c - 1) ^ 2 :=
    mul_pos (mul_pos ha0 (by linarith))
      (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.mpr hc1))))
  rw [show (1 + a / c)⁻¹ = c / (c + a) by field_simp]
  rw [inv_eq_one_div, inv_eq_one_div, div_add_div _ _ (by positivity) (by positivity),
    mul_one_div, div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hpos]

/-- **The sign of the logit aggregation bias for `m > 0`**: for every `τ > 0`, `J(m, τ) < σ(m)`. -/
theorem logitNormalMean_lt_sigmoid {m : ℝ} (hm : 0 < m) {τ : ℝ≥0} (hτ : τ ≠ 0) :
    logitNormalMean m τ < sigmoid m := by
  have hb : ∀ y, Integrable (fun z => sigmoid (y + z)) (gaussianReal 0 τ) := fun y =>
    integrable_of_abs_le_one_of_continuous (by fun_prop) fun x => by
      rw [abs_of_pos (sigmoid_pos _)]; exact sigmoid_le_one _
  have hb' : Integrable (fun z => sigmoid (m - z)) (gaussianReal 0 τ) := by
    simpa [sub_eq_add_neg] using
      (integrable_of_abs_le_one_of_continuous (ν := gaussianReal 0 τ)
        (f := fun z => sigmoid (m - z))
        (by fun_prop) fun x => by
        rw [abs_of_pos (sigmoid_pos _)]; exact sigmoid_le_one _)
  have hsym : ∫ z, sigmoid (m + z) ∂(gaussianReal 0 τ) =
      ∫ z, sigmoid (m - z) ∂(gaussianReal 0 τ) := by
    have h := gaussianReal_map_neg (μ := (0 : ℝ)) (v := τ)
    rw [neg_zero] at h
    conv_lhs => rw [← h]
    rw [integral_map measurable_neg.aemeasurable
      ((by fun_prop : Continuous fun z => sigmoid (m + z)).aestronglyMeasurable)]
    simp [sub_eq_add_neg]
  have h2 : 2 * logitNormalMean m τ =
      ∫ z, (sigmoid (m + z) + sigmoid (m - z)) ∂(gaussianReal 0 τ) := by
    rw [integral_add (hb m) hb', ← hsym, logitNormalMean_eq_shift]; ring
  have hlt : ∫ z, (sigmoid (m + z) + sigmoid (m - z)) ∂(gaussianReal 0 τ) <
      ∫ _z, 2 * sigmoid m ∂(gaussianReal 0 τ) := by
    have := nullSingletonClass_gaussianReal (μ := (0 : ℝ)) hτ
    refine integral_lt_integral_of_le_of_measure_ne ((hb m).add hb') (integrable_const _)
      (fun z => ?_) ?_
    · rcases eq_or_ne z 0 with rfl | hz
      · simp only [add_zero, sub_zero]; linarith
      · exact (sigmoid_add_add_sigmoid_sub_lt hm hz).le
    · intro h0
      have hsub : ({0}ᶜ : Set ℝ) ⊆ {z | sigmoid (m + z) + sigmoid (m - z) < 2 * sigmoid m} :=
        fun z hz => sigmoid_add_add_sigmoid_sub_lt hm hz
      have := measure_mono_null hsub h0
      rw [measure_compl (measurableSet_singleton 0) (measure_ne_top _ _), measure_singleton,
        measure_univ] at this
      simp at this
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hlt
  linarith

/-- **The sign for `m < 0`**: for every `τ > 0`, `σ(m) < J(m, τ)`. -/
theorem sigmoid_lt_logitNormalMean {m : ℝ} (hm : m < 0) {τ : ℝ≥0} (hτ : τ ≠ 0) :
    sigmoid m < logitNormalMean m τ := by
  have h := logitNormalMean_lt_sigmoid (neg_pos.mpr hm) hτ
  rw [sigmoid_neg] at h
  rw [logitNormalMean_reflect m τ]
  linarith

/-- The third absolute central moment of `N(m, τ)` is `τ √τ E|Z|³`. -/
theorem integral_abs_sub_pow_three_gaussianReal (m : ℝ) (τ : ℝ≥0) :
    ∫ x, |x - m| ^ 3 ∂(gaussianReal m τ) =
      τ * √τ * ∫ z, |z| ^ 3 ∂(gaussianReal 0 1) := by
  have hN : gaussianReal m τ = ((gaussianReal 0 1).map (√τ * ·)).map (· + m) := by
    rw [gaussianReal_map_const_mul, gaussianReal_map_add_const]
    congr 1
    · simp
    · ext; simp
  rw [hN, integral_map (by fun_prop) (by fun_prop), integral_map (by fun_prop) (by fun_prop)]
  simp only [add_sub_cancel_right, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow]
  rw [integral_const_mul]
  have : √(τ : ℝ) ^ 3 = τ * √τ := by
    rw [pow_succ, Real.sq_sqrt (NNReal.coe_nonneg τ)]
  rw [this]

/-- **The leading order logit bias and its sign**: as `τ → 0`,
`J(m, τ) - σ(m) = ½ σ''(m) τ + o(τ)`, and `σ''(m)` is positive for `m < 0` and negative for
`m > 0`. -/
theorem isLittleO_logitNormalMean_sub (m : ℝ) :
    (fun τ : ℝ≥0 => logitNormalMean m τ - sigmoid m - sigmoidDeriv2 m / 2 * τ) =o[nhds 0]
        (fun τ : ℝ≥0 => (τ : ℝ)) ∧
      (m < 0 → 0 < sigmoidDeriv2 m) ∧ (0 < m → sigmoidDeriv2 m < 0) := by
  refine ⟨?_, fun hm => ?_, fun hm => ?_⟩
  · have hint : ∀ τ : ℝ≥0, Integrable sigmoid (gaussianReal m τ) := fun τ =>
      integrable_of_abs_le_one_of_continuous continuous_sigmoid fun x => by
        rw [abs_of_pos (sigmoid_pos x)]; exact sigmoid_le_one x
    have h3 : ∀ τ : ℝ≥0, Integrable (fun x => |x - ∫ y, y ∂(gaussianReal m τ)| ^ 3)
        (gaussianReal m τ) := fun τ => by
      rw [integral_id_gaussianReal]
      have := ((memLp_id_gaussianReal' (μ := m) (v := τ) 3 (by simp)).sub
        (memLp_const m)).integrable_norm_pow (p := 3) (by norm_num)
      simpa [Real.norm_eq_abs] using this
    have hK : ∀ τ : ℝ≥0, ∫ x, |x - ∫ y, y ∂(gaussianReal m τ)| ^ 3 ∂(gaussianReal m τ) ≤
        (∫ z, |z| ^ 3 ∂(gaussianReal 0 1)) * variance (fun x => x) (gaussianReal m τ) *
          √(variance (fun x => x) (gaussianReal m τ)) := fun τ => by
      rw [integral_id_gaussianReal, variance_fun_id_gaussianReal,
        integral_abs_sub_pow_three_gaussianReal]
      exact le_of_eq (by ring)
    have hv : Filter.Tendsto (fun τ : ℝ≥0 => variance (fun x => x) (gaussianReal m τ))
        (nhds 0) (nhds 0) := by
      simp_rw [variance_fun_id_gaussianReal]
      exact NNReal.tendsto_coe.mpr Filter.tendsto_id
    have h := isLittleO_integral_sub_taylor_two (ψ₁ := sigmoidDeriv1) (ψ₂ := sigmoidDeriv2)
      (ψ₃ := sigmoidDeriv3) (I := Set.univ) convex_univ
      (fun x _ => (hasDerivAt_sigmoid x).hasDerivWithinAt)
      (fun x _ => (hasDerivAt_sigmoidD1 x).hasDerivWithinAt)
      (fun x _ => (hasDerivAt_sigmoidD2 x).hasDerivWithinAt) (M := 1)
      (fun x _ => abs_sigmoidD3_le x) (fun τ : ℝ≥0 => gaussianReal m τ)
      (fun _ => ae_of_all _ fun _ => trivial)
      (fun τ => memLp_id_gaussianReal' (μ := m) (v := τ) 2 (by simp)) hint h3 hK hv
    simp only [integral_id_gaussianReal, variance_fun_id_gaussianReal] at h
    exact h
  · have hs : sigmoid m < 1 / 2 := by
      have := sigmoid_strictMono hm; rwa [sigmoid_zero, ← one_div] at this
    exact mul_pos (sigmoidDeriv1_pos m) (by linarith)
  · have hs : 1 / 2 < sigmoid m := by
      have := sigmoid_strictMono hm; rwa [sigmoid_zero, ← one_div] at this
    exact mul_neg_of_pos_of_neg (sigmoidDeriv1_pos m) (by linarith)

end Logit

namespace MultilevelModel

variable {J K : Type*} {p : ℕ}

/-- **Logit aggregation under Gaussian covariates**: the aggregate mean of arm `k` is the logit
normal mean `J(η_k(x̄), v_k)`. -/
theorem armMean_sigmoid_gaussian (M : MultilevelModel J K p) (α : ℝ) (F : Measure (Fin p → ℝ))
    [IsGaussian F] (k : K) :
    M.armMean Real.sigmoid α F k =
      logitNormalMean (M.eta α k (covMean F)) (slopeVar F (M.β₁ + M.β₂ k)).toNNReal := by
  have hL := M.hasLaw_eta_gaussian α F k
  rw [armMean, logitNormalMean, ← hL.map_eq,
    integral_map hL.aemeasurable continuous_sigmoid.aestronglyMeasurable]
  rfl

/-- **For a positive plug in predictor the logit bias is negative** when `v_k > 0`. -/
theorem aggBias_sigmoid_neg (M : MultilevelModel J K p) (α : ℝ) (F : Measure (Fin p → ℝ))
    [IsGaussian F] (k : K) (hv : 0 < slopeVar F (M.β₁ + M.β₂ k))
    (hm : 0 < M.eta α k (covMean F)) : M.aggBias Real.sigmoid α F k < 0 := by
  rw [aggBias, armMean_sigmoid_gaussian, sub_neg]
  exact logitNormalMean_lt_sigmoid hm (by simpa using hv)

/-- **For a negative plug in predictor the logit bias is positive** when `v_k > 0`. -/
theorem aggBias_sigmoid_pos (M : MultilevelModel J K p) (α : ℝ) (F : Measure (Fin p → ℝ))
    [IsGaussian F] (k : K) (hv : 0 < slopeVar F (M.β₁ + M.β₂ k))
    (hm : M.eta α k (covMean F) < 0) : 0 < M.aggBias Real.sigmoid α F k := by
  rw [aggBias, armMean_sigmoid_gaussian, sub_pos]
  exact sigmoid_lt_logitNormalMean hm (by simpa using hv)

/-- At a zero plug in predictor the logit bias vanishes, for every covariance. -/
theorem aggBias_sigmoid_eq_zero (M : MultilevelModel J K p) (α : ℝ) (F : Measure (Fin p → ℝ))
    [IsGaussian F] (k : K) (hm : M.eta α k (covMean F) = 0) :
    M.aggBias Real.sigmoid α F k = 0 := by
  rw [aggBias, armMean_sigmoid_gaussian, hm, (logitNormalMean_zero _).2, sub_self]

end MultilevelModel

end NetworkMetaRegression

end CausalInference
