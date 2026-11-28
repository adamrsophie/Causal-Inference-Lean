/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.HajekConvolution

/-!
# The Hájek convolution bound for a general limit law, scalar parameter

`CausalInference.ParametricFamily.hajek_convolution_bound` bounds the variance of a regular
estimator whose limit law is a centered Gaussian `N(0, V)`. This file removes the Gaussian
assumption: in a regular family with positive information `I(θ₀)`, every estimator regular at
`θ₀` in Hájek's sense, with an arbitrary limit law `L` of finite second moment, has
`Var(L) ≥ I(θ₀)⁻¹`. Without a moment condition the bound holds for the extended variance.

The proof is the Gaussian one with the moments of `L` in place of those of `N(0, V)`. Along a
subsequence, `√n (T_n - θ₀)` and the normalized score `S_n` converge jointly to a law `μ`
(Prokhorov) whose first marginal is `L` and second marginal is `N(0, I)`. Local asymptotic
normality and Le Cam's third lemma turn regularity into the tilt identity
`∫ f(x + h) dL = ∫ f(x) e^{h z - h² I / 2} dμ(x, z)` for every `h` and every bounded continuous
`f`. This step uses no moment of `L`. Differentiating the identity at `h = 0` for `f = sin(t ·)`
and letting `t → 0` gives `∫ x z dμ = 1`; this step uses the integrability of `x z` under `μ`,
which follows from `∫ x² dL < ∞` and the Gaussian second marginal. With `m = ∫ x dL` and
`∫ z dμ = 0`, `Var(L) - I⁻¹ = ∫ (x - m - I⁻¹ z)² dμ ≥ 0`, which uses `∫ x² dL < ∞` once more.

## Main results

* `CausalInference.tilt_integral_mul_eq_one_of_memLp`: a joint law with first marginal `L`
  (square integrable), Gaussian second marginal and the tilt identity has `∫ x z = 1`.
* `CausalInference.tilt_variance_bound_of_memLp`: under the same hypotheses
  `Var(L) - I⁻¹ = ∫ (x - m - I⁻¹ z)²`, so `I⁻¹ ≤ Var(L)`, with equality only if
  `x = m + I⁻¹ z` almost surely.
* `CausalInference.ParametricFamily.IsHajekRegular.isProbabilityMeasure`: the limit law of a
  regular estimator is a probability measure.
* `CausalInference.ParametricFamily.hajek_tilt_subseq_general`: subsequential joint limits of a
  regular estimator with any limit law and the score satisfy the tilt identity.
* `CausalInference.ParametricFamily.hajek_convolution_bound_general`: `I(θ₀)⁻¹ ≤ Var(L)` for a
  limit law `L` with finite second moment.
* `CausalInference.ParametricFamily.hajek_convolution_bound_evariance`: `I(θ₀)⁻¹` is at most the
  extended variance of `L`, with no moment condition.

References: J. Hájek (1970), *A characterization of limiting distributions of regular
estimates*, Zeitschrift für Wahrscheinlichkeitstheorie und verwandte Gebiete; L. Le Cam (1960),
*Locally asymptotically normal families of distributions*, University of California Publications
in Statistics; A. W. van der Vaart (1998), *Asymptotic Statistics*, chapter 8.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Metric
open scoped Topology ENNReal NNReal BoundedContinuousFunction

namespace CausalInference

/-! ### The tilt identity with a general first marginal -/

section Tilt

variable {μ : Measure (ℝ × ℝ)}

/-- The product of the coordinates is integrable when the first marginal is square integrable
and the second is Gaussian. -/
lemma integrable_fst_mul_snd_of_memLp {L : Measure ℝ} (hL : MemLp id 2 L)
    (hX : μ.map Prod.fst = L) {w : ℝ≥0} (hZ : μ.map Prod.snd = gaussianReal 0 w) :
    Integrable (fun p : ℝ × ℝ ↦ p.1 * p.2) μ := by
  have hx2 : Integrable (fun p : ℝ × ℝ ↦ p.1 ^ 2) μ :=
    integrable_comp_fst_of_map hX (g := fun x ↦ x ^ 2) hL.integrable_sq
  refine (((hx2.add (integrable_sq_snd hZ)).div_const 2)).mono'
    (by fun_prop) (Eventually.of_forall fun p ↦ ?_)
  change |p.1 * p.2| ≤ (p.1 ^ 2 + p.2 ^ 2) / 2
  rw [abs_mul]
  nlinarith [sq_nonneg (|p.1| - |p.2|), sq_abs p.1, sq_abs p.2]

/-- **The tilt identity pins the covariance, general first marginal.** Let `μ` be a law of
`(X, Z)` with `X ∼ L`, `L` a probability measure with finite second moment, `Z ∼ N(0, I)`,
`I > 0`, and suppose that for every `h` the shift of `L` by `h` is the exponential tilt
`e^{h Z - h² I / 2} dμ` seen through `X`. Then `E[X Z] = 1`. For `f = sin(t ·)`, differentiating
the identity in `h` at `0` gives `E[sin(tX) Z] = t E[cos(tX)]`; divide by `t` and let `t → 0`,
by dominated convergence with the integrable bound `|X Z|`. -/
theorem tilt_integral_mul_eq_one_of_memLp [IsProbabilityMeasure μ] {L : Measure ℝ}
    [IsProbabilityMeasure L] (hL : MemLp id 2 L) {I : ℝ} (hI : 0 < I)
    (hX : μ.map Prod.fst = L) (hZ : μ.map Prod.snd = gaussianReal 0 I.toNNReal)
    (htilt : ∀ h : ℝ, ∀ f : ℝ →ᵇ ℝ, ∫ x, f (x + h) ∂L =
      ∫ p, f p.1 * Real.exp (h * p.2 - h ^ 2 * I / 2) ∂μ) :
    ∫ p, p.1 * p.2 ∂μ = 1 := by
  have hstep : ∀ t : ℝ, ∫ p, Real.sin (t * p.1) * p.2 ∂μ = t * ∫ x, Real.cos (t * x) ∂L := by
    intro t
    let fs : ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
      (fun x ↦ Real.sin (t * x)) (by fun_prop) 1
      (fun x ↦ by rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
    have heq : (fun h : ℝ ↦ ∫ x, Real.sin (t * (x + h)) ∂L) =
        fun h ↦ ∫ p, Real.sin (t * p.1) * Real.exp (h * p.2 - h ^ 2 * I / 2) ∂μ := by
      funext h
      exact htilt h fs
    have hA := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := L)
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
  have hxz := integrable_fst_mul_snd_of_memLp hL hX hZ
  have hLim : Tendsto (fun t : ℝ ↦ ∫ p, t⁻¹ * Real.sin (t * p.1) * p.2 ∂μ) (𝓝[≠] 0)
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
  have hR : Tendsto (fun t : ℝ ↦ ∫ x, Real.cos (t * x) ∂L) (𝓝[≠] 0) (𝓝 1) := by
    have h := tendsto_integral_filter_of_dominated_convergence (μ := L) (l := 𝓝[≠] (0 : ℝ))
      (F := fun t x ↦ Real.cos (t * x)) (f := fun x ↦ Real.cos (0 * x)) (fun _ ↦ 1)
      (Eventually.of_forall fun t ↦ (by fun_prop : Continuous fun x : ℝ ↦
        Real.cos (t * x)).aestronglyMeasurable)
      (Eventually.of_forall fun t ↦ Eventually.of_forall fun x ↦ by
        rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _) (integrable_const _)
      (Eventually.of_forall fun x ↦ ((by fun_prop : Continuous fun t : ℝ ↦
        Real.cos (t * x)).tendsto 0).mono_left nhdsWithin_le_nhds)
    simpa using h
  have heq : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∫ x, Real.cos (t * x) ∂L =
      ∫ p, t⁻¹ * Real.sin (t * p.1) * p.2 ∂μ := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp_rw [mul_assoc]
    rw [integral_const_mul, hstep t, ← mul_assoc, inv_mul_cancel₀ ht, one_mul]
  exact tendsto_nhds_unique hLim (hR.congr' heq)

/-- **The variance bound from the tilt identity, general first marginal.** Under the hypotheses
of `CausalInference.tilt_integral_mul_eq_one_of_memLp`, with `m = ∫ x dL`,
`Var(L) - I⁻¹ = E[(X - m - I⁻¹ Z)²] ≥ 0`, and `Var(L) = I⁻¹` forces `X = m + I⁻¹ Z` almost
surely. -/
theorem tilt_variance_bound_of_memLp [IsProbabilityMeasure μ] {L : Measure ℝ}
    [IsProbabilityMeasure L] (hL : MemLp id 2 L) {I : ℝ} (hI : 0 < I)
    (hX : μ.map Prod.fst = L) (hZ : μ.map Prod.snd = gaussianReal 0 I.toNNReal)
    (htilt : ∀ h : ℝ, ∀ f : ℝ →ᵇ ℝ, ∫ x, f (x + h) ∂L =
      ∫ p, f p.1 * Real.exp (h * p.2 - h ^ 2 * I / 2) ∂μ) :
    ∫ p, (p.1 - (∫ x, x ∂L) - I⁻¹ * p.2) ^ 2 ∂μ = Var[id; L] - I⁻¹ ∧ I⁻¹ ≤ Var[id; L] ∧
      (Var[id; L] = I⁻¹ → ∀ᵐ p ∂μ, p.1 = (∫ x, x ∂L) + I⁻¹ * p.2) := by
  set m := ∫ x, x ∂L with hm
  have h1 := tilt_integral_mul_eq_one_of_memLp hL hI hX hZ htilt
  have hxm : Integrable (fun p : ℝ × ℝ ↦ (p.1 - m) ^ 2) μ :=
    integrable_comp_fst_of_map hX (g := fun x ↦ (x - m) ^ 2)
      (hL.sub (memLp_const m)).integrable_sq
  have hz : Integrable (fun p : ℝ × ℝ ↦ p.2) μ :=
    integrable_comp_snd_of_map hZ (g := id) ((memLp_id_gaussianReal 1).integrable le_rfl)
  have hz2 := integrable_sq_snd hZ
  have hxz := integrable_fst_mul_snd_of_memLp hL hX hZ
  have ixm : ∫ p, (p.1 - m) ^ 2 ∂μ = Var[id; L] := by
    rw [variance_eq_integral measurable_id.aemeasurable, ← hX,
      integral_map measurable_fst.aemeasurable (by fun_prop)]
    rw [hX]
    rfl
  have iz : ∫ p, p.2 ∂μ = 0 := by
    rw [← integral_id_gaussianReal (μ := (0 : ℝ)) (v := I.toNNReal), ← hZ,
      integral_map measurable_snd.aemeasurable (by fun_prop)]
  have iz2 : ∫ p, p.2 ^ 2 ∂μ = I := by
    rw [← Real.coe_toNNReal I hI.le, ← integral_sq_gaussianReal I.toNNReal, ← hZ,
      integral_map measurable_snd.aemeasurable (by fun_prop)]
  have hexp : (fun p : ℝ × ℝ ↦ (p.1 - m - I⁻¹ * p.2) ^ 2) =
      fun p ↦ ((p.1 - m) ^ 2 - 2 * I⁻¹ * (p.1 * p.2)) +
        (2 * I⁻¹ * m * p.2 + I⁻¹ ^ 2 * p.2 ^ 2) := by
    funext p; ring
  have hA : Integrable (fun p : ℝ × ℝ ↦ (p.1 - m) ^ 2 - 2 * I⁻¹ * (p.1 * p.2)) μ :=
    hxm.sub (hxz.const_mul _)
  have hB : Integrable (fun p : ℝ × ℝ ↦ 2 * I⁻¹ * m * p.2 + I⁻¹ ^ 2 * p.2 ^ 2) μ :=
    (hz.const_mul _).add (hz2.const_mul _)
  have e : ∫ p, (p.1 - m - I⁻¹ * p.2) ^ 2 ∂μ = Var[id; L] - I⁻¹ := by
    rw [hexp, integral_add hA hB, integral_sub hxm (hxz.const_mul _),
      integral_add (hz.const_mul _) (hz2.const_mul _), integral_const_mul, integral_const_mul,
      integral_const_mul, ixm, h1, iz, iz2]
    field_simp
    ring
  have hnn : 0 ≤ ∫ p, (p.1 - m - I⁻¹ * p.2) ^ 2 ∂μ := integral_nonneg fun p ↦ sq_nonneg _
  refine ⟨e, by linarith, fun hV ↦ ?_⟩
  have hint : Integrable (fun p : ℝ × ℝ ↦ (p.1 - m - I⁻¹ * p.2) ^ 2) μ := by
    rw [hexp]
    exact hA.add hB
  have h0 : ∫ p, (p.1 - m - I⁻¹ * p.2) ^ 2 ∂μ = 0 := by rw [e, hV, sub_self]
  have := (integral_eq_zero_iff_of_nonneg (fun p ↦ sq_nonneg _) hint).1 h0
  filter_upwards [this] with p hp
  have : (p.1 - m - I⁻¹ * p.2) ^ 2 = 0 := hp
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  linarith

end Tilt

/-! ### Regular estimators with a general limit law -/

namespace ParametricFamily

variable {S : Type*} [MeasurableSpace S] {F : ParametricFamily ℝ S} [SigmaFinite F.ν]
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {O : ℕ → Ω → S} {θ₀ : ℝ}

/-- **The limit law of a regular estimator is a probability measure.** At `θ₀ ∈ Θ` the sample
laws at local parameter `0` are probability measures and the constant `1` is a test function. -/
theorem IsHajekRegular.isProbabilityMeasure (hθ₀ : θ₀ ∈ F.Θ) {T : ∀ n, (Fin n → S) → ℝ}
    {L : Measure ℝ} (hT : F.IsHajekRegular T θ₀ L) : IsProbabilityMeasure L := by
  have h1 := hT.tendsto 0 (BoundedContinuousFunction.const _ 1)
  simp only [BoundedContinuousFunction.const_apply, integral_const, smul_eq_mul, mul_one,
    zero_div, add_zero] at h1
  refine isProbabilityMeasure_iff_real.2 (tendsto_nhds_unique h1 (tendsto_const_nhds.congr ?_))
  intro n
  have := isProbabilityMeasure_law (F := F.pi n) hθ₀
  exact probReal_univ.symm

/-- **Subsequential joint limits of a regular estimator and the score satisfy the tilt
identity, general limit law.** Let `O` be an i.i.d. sample with law `P_θ₀`, the family regular at
`θ₀` with positive information and the smoothness of `logLikRatio_sub_tendstoInMeasure`, and `T`
regular at `θ₀` with an arbitrary limit law `L`. Along every `ψ k → ∞`, some further subsequence
of `(√n (T_n - θ₀), S_n)`, `S_n = n^{-1/2} ∑_{i < n} s(θ₀; O_i)`, converges in distribution to a
law `μ'` with marginals `L` and `N(0, I(θ₀))` and, for every `h` and bounded continuous `f`,
`∫ f(x + h) dL = ∫ f(x) e^{h z - h² I(θ₀) / 2} dμ'(x, z)`. No moment of `L` is used. -/
theorem hajek_tilt_subseq_general (hO : IsIIDSample O μ) (hlaw : μ.map (O 0) = F.law θ₀)
    (hreg : F.IsRegularAt θ₀) {r : ℝ} (hs : F.IsScoreRegular θ₀ r)
    (hdl : ∀ᵐ z ∂F.law θ₀, ∀ θ ∈ closedBall θ₀ r,
      HasDerivAt (fun u ↦ F.logLik u z) (F.score θ z) θ)
    (hI : 0 < F.fisherInfo θ₀) {T : ∀ n, (Fin n → S) → ℝ} {L : Measure ℝ}
    (hT : F.IsHajekRegular T θ₀ L) {ψ : ℕ → ℕ} (hψ : Tendsto ψ atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ μ' : ProbabilityMeasure (ℝ × ℝ),
      TendstoInDistribution (fun k ω ↦
        (√(ψ (φ k) : ℝ) * (T (ψ (φ k)) (fun i ↦ O i ω) - θ₀),
          (√(ψ (φ k) : ℝ))⁻¹ * ∑ i ∈ range (ψ (φ k)), F.score θ₀ (O i ω))) atTop id
        (fun _ ↦ μ) (μ' : Measure (ℝ × ℝ)) ∧
      (μ' : Measure (ℝ × ℝ)).map Prod.fst = L ∧
      (μ' : Measure (ℝ × ℝ)).map Prod.snd = gaussianReal 0 (F.fisherInfo θ₀).toNNReal ∧
      ∀ h : ℝ, ∀ f : ℝ →ᵇ ℝ, ∫ x, f (x + h) ∂L =
        ∫ p, f p.1 * Real.exp (h * p.2 - h ^ 2 * F.fisherInfo θ₀ / 2)
          ∂(μ' : Measure (ℝ × ℝ)) := by
  set I := F.fisherInfo θ₀ with hIdef
  have hθ₀ : θ₀ ∈ F.Θ := mem_of_mem_nhds hreg.mem_nhds
  have := hT.isProbabilityMeasure hθ₀
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

/-- **The Hájek convolution bound on a given sample, general limit law.** Under the hypotheses
of `hajek_tilt_subseq_general`, a regular estimator whose limit law `L` has a finite second
moment has `I(θ₀)⁻¹ ≤ Var(L)`. -/
theorem hajek_convolution_bound_general_of_isIIDSample (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = F.law θ₀) (hreg : F.IsRegularAt θ₀) {r : ℝ}
    (hs : F.IsScoreRegular θ₀ r)
    (hdl : ∀ᵐ z ∂F.law θ₀, ∀ θ ∈ closedBall θ₀ r,
      HasDerivAt (fun u ↦ F.logLik u z) (F.score θ z) θ)
    (hI : 0 < F.fisherInfo θ₀) {T : ∀ n, (Fin n → S) → ℝ} {L : Measure ℝ}
    (hT : F.IsHajekRegular T θ₀ L) (hL : MemLp id 2 L) :
    (F.fisherInfo θ₀)⁻¹ ≤ Var[id; L] := by
  have := hT.isProbabilityMeasure (mem_of_mem_nhds hreg.mem_nhds)
  obtain ⟨φ, -, μ', -, h1, h2, ht⟩ := hajek_tilt_subseq_general hO hlaw hreg hs hdl hI hT
    tendsto_id
  exact (tilt_variance_bound_of_memLp hL hI h1 h2 ht).2.1

/-- **The Hájek convolution bound, general limit law.** In a family regular at `θ₀` with
positive information `I(θ₀)`, the second derivative of the log density smooth with an
integrable envelope on a closed ball around `θ₀` (`IsScoreRegular`) and `θ ↦ ℓ(θ; z)` with
derivative `s(θ; z)` there, every estimator sequence regular at `θ₀` in Hájek's sense whose limit
law `L` has a finite second moment has `Var(L) ≥ I(θ₀)⁻¹`. The limit law need not be Gaussian
nor centered. -/
theorem hajek_convolution_bound_general (hreg : F.IsRegularAt θ₀) {r : ℝ}
    (hs : F.IsScoreRegular θ₀ r)
    (hdl : ∀ᵐ z ∂F.law θ₀, ∀ θ ∈ closedBall θ₀ r,
      HasDerivAt (fun u ↦ F.logLik u z) (F.score θ z) θ)
    (hI : 0 < F.fisherInfo θ₀) {T : ∀ n, (Fin n → S) → ℝ} {L : Measure ℝ}
    (hT : F.IsHajekRegular T θ₀ L) (hL : MemLp id 2 L) :
    (F.fisherInfo θ₀)⁻¹ ≤ Var[id; L] := by
  have := isProbabilityMeasure_law (mem_of_mem_nhds hreg.mem_nhds)
  obtain ⟨Ω', _, P', O', hP', -, hO', hlaw'⟩ := exists_isIIDSample (F.law θ₀)
  exact hajek_convolution_bound_general_of_isIIDSample hO' (hlaw' 0).map_eq hreg hs hdl hI hT hL

/-- **The Hájek convolution bound for the extended variance.** Under the hypotheses of
`hajek_convolution_bound_general` without any moment condition on the limit law `L`,
`I(θ₀)⁻¹` is at most the extended variance `evariance id L ∈ [0, ∞]`: if `L` has no finite
second moment the extended variance is `∞`, and otherwise it is `Var(L)`. -/
theorem hajek_convolution_bound_evariance (hreg : F.IsRegularAt θ₀) {r : ℝ}
    (hs : F.IsScoreRegular θ₀ r)
    (hdl : ∀ᵐ z ∂F.law θ₀, ∀ θ ∈ closedBall θ₀ r,
      HasDerivAt (fun u ↦ F.logLik u z) (F.score θ z) θ)
    (hI : 0 < F.fisherInfo θ₀) {T : ∀ n, (Fin n → S) → ℝ} {L : Measure ℝ}
    (hT : F.IsHajekRegular T θ₀ L) :
    ENNReal.ofReal (F.fisherInfo θ₀)⁻¹ ≤ evariance id L := by
  have := hT.isProbabilityMeasure (mem_of_mem_nhds hreg.mem_nhds)
  by_cases hL : MemLp id 2 L
  · rw [← hL.ofReal_variance_eq]
    exact ENNReal.ofReal_le_ofReal (hajek_convolution_bound_general hreg hs hdl hI hT hL)
  · rw [(evariance_eq_top_iff aestronglyMeasurable_id).2 hL]
    exact le_top

end ParametricFamily

end CausalInference
