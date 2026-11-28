/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.PosteriorLimitLogisticInformation

/-!
# The Bernstein and von Mises theorem for logistic regression

**The posterior.** For a prior density `π` on the coefficients `ξ ∈ ℝ^κ` (against Lebesgue
measure) and records `x = ((cᵢ, yᵢ))_{i < n}`, the posterior of the logistic model is the
normalized product of the prior density and the likelihood (`logisticPosterior`):

  `Π_n(dξ) ∝ π(ξ) ∏ᵢ logisticDens (z(cᵢ) ⬝ ξ) yᵢ dξ`.

It is the normalized density, not Mathlib's posterior kernel `ProbabilityTheory.posterior`,
which is determined only almost everywhere under the marginal law of the data. The likelihood is
positive and at most one, so for a prior density with positive integral the normalizer is
positive and finite at every data value (`isProbabilityMeasure_logisticPosterior`).

**The theorem** (`isBernsteinVonMises_logistic`). Let the records be i.i.d. with design
arguments of law `R`, let the design be bounded almost surely and of full rank under `R`, let
`K` be a compact neighborhood of `ξ₀` on which the maximum likelihood fit `ξ̂_n` converges in
probability to `ξ₀`, and let the prior density be integrable, continuous and positive at `ξ₀`.
Then, in probability,

  `‖Π_n - N(ξ̂_n, n⁻¹ I(ξ₀)⁻¹)‖_TV → 0`,

with the information matrix `I(ξ₀) = ∫ w(z(c) ⬝ ξ₀) z(c) z(c)ᵀ dR`. This is the conclusion of
`PosteriorLimit.IsBernsteinVonMises` with the limit `N(0, I(ξ₀)⁻¹)` (van der Vaart (1998),
Theorem 10.1, for this model).

**Proof.** On events of probability tending to one: the fit lies in the interior of `K`, so the
score vanishes there (`logisticScoreSum_glmMLE_eq_zero`); it is within `δ` of `ξ₀`; the
empirical information at `ξ₀` is within `n e` of `n I(ξ₀)` entrywise (the weak law of large
numbers); and the design of every record is bounded. There the log likelihood has the quadratic
expansion of `abs_logisticLogLik_quad_le` with error `η = O(δ + e)`, and the deterministic bound
`tvDist_densityPosterior_gaussian_le` applies. Its first term is small once `δ` and `e` are, and
its second term tends to zero as `n → ∞`.

## Main definitions

* `PosteriorLimit.logisticPosterior`.

## Main results

* `integral_pos_of_continuousAt`, `isProbabilityMeasure_densityPosterior_of_le_one`.
* `isProbabilityMeasure_logisticPosterior`, `logisticPosterior_eq_map`.
* `withProbTendingToOne_logisticScoreSum_glmMLE_eq_zero`.
* `isBernsteinVonMises_logistic_euclidean`, `isBernsteinVonMises_logistic`.

## References

* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press (1998), Theorem 10.1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open scoped ENNReal NNReal

namespace CausalInference

namespace PosteriorLimit

open PopulationAdjustment

/-! ### Positivity of the normalizer -/

/-- A nonnegative integrable function that is continuous and positive at a point has positive
integral against a measure charging every open set. -/
theorem integral_pos_of_continuousAt {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] {μ : Measure X} [μ.IsOpenPosMeasure] {p : X → ℝ}
    (hp0 : ∀ x, 0 ≤ p x) (hpi : Integrable p μ) {x₀ : X} (hpc : ContinuousAt p x₀)
    (hpx₀ : 0 < p x₀) : 0 < ∫ x, p x ∂μ := by
  rw [integral_pos_iff_support_of_nonneg hp0 hpi]
  have hnhds : {x | 0 < p x} ∈ 𝓝 x₀ := hpc.eventually (lt_mem_nhds hpx₀)
  exact (μ.measure_pos_of_mem_nhds hnhds).trans_le
    (measure_mono fun x hx ↦ (show 0 < p x from hx).ne')

/-- **The posterior of a likelihood in `(0, 1]` is a probability law** for a prior density with
positive integral. -/
theorem isProbabilityMeasure_densityPosterior_of_le_one {Θ : Type*} [MeasurableSpace Θ]
    {ρ : Measure Θ} {p L : Θ → ℝ} (hpm : Measurable p) (hp0 : ∀ θ, 0 ≤ p θ)
    (hpi : Integrable p ρ) (hpZ : 0 < ∫ θ, p θ ∂ρ) (hLm : Measurable L) (hL0 : ∀ θ, 0 < L θ)
    (hL1 : ∀ θ, L θ ≤ 1) : IsProbabilityMeasure (densityPosterior ρ p L) := by
  have hpLi : Integrable (fun θ ↦ p θ * L θ) ρ :=
    hpi.mono' (hpm.mul hLm).aestronglyMeasurable (ae_of_all _ fun θ ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hp0 θ) (hL0 θ).le)]
      exact mul_le_of_le_one_right (hp0 θ) (hL1 θ))
  refine isProbabilityMeasure_densityPosterior hpm hp0 hLm (fun θ ↦ (hL0 θ).le) hpLi ?_
  rw [integral_pos_iff_support_of_nonneg (fun θ ↦ mul_nonneg (hp0 θ) (hL0 θ).le) hpLi]
  rw [integral_pos_iff_support_of_nonneg hp0 hpi] at hpZ
  exact hpZ.trans_le (measure_mono fun θ hθ ↦ mul_ne_zero hθ (hL0 θ).ne')

/-- `e^{-c n} n^{k/2} → 0` for `c > 0`. -/
lemma tendsto_exp_neg_mul_sqrt_pow {c : ℝ} (hc : 0 < c) (k : ℕ) :
    Tendsto (fun n : ℕ ↦ Real.exp (-((n : ℝ) * c)) * (√(n : ℝ)) ^ k) atTop (𝓝 0) := by
  have hlim := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp
    (tendsto_natCast_atTop_atTop.atTop_mul_const hc)
  have hlim' : Tendsto (fun n : ℕ ↦ c⁻¹ ^ k * (((n : ℝ) * c) ^ k * Real.exp (-((n : ℝ) * c))))
      atTop (𝓝 0) := by
    have := hlim.const_mul (c⁻¹ ^ k)
    rw [mul_zero] at this
    exact this
  refine squeeze_zero' (Eventually.of_forall fun n ↦ by positivity) ?_ hlim'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsq : √(n : ℝ) ≤ n := Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith⟩
  calc Real.exp (-((n : ℝ) * c)) * (√(n : ℝ)) ^ k
      ≤ Real.exp (-((n : ℝ) * c)) * (n : ℝ) ^ k := by gcongr
    _ = c⁻¹ ^ k * (((n : ℝ) * c) ^ k * Real.exp (-((n : ℝ) * c))) := by
        rw [mul_pow, inv_pow]
        field_simp

/-! ### The logistic posterior -/

variable {C κ : Type*} [Fintype κ]

/-- The **posterior of the logistic model** for the prior density `π` (against Lebesgue measure on
`ℝ^κ`) and records `x`: the normalized product `π(ξ) ∏ᵢ logisticDens (z(cᵢ) ⬝ ξ) yᵢ`. -/
noncomputable def logisticPosterior (p : (κ → ℝ) → ℝ) (z : C → κ → ℝ) {n : ℕ}
    (x : Fin n → C × ℝ) : Measure (κ → ℝ) :=
  densityPosterior volume p (glmLikelihood logisticDens z x)

lemma logisticDens_le_one (η y : ℝ) : logisticDens η y ≤ 1 := by
  unfold logisticDens
  split_ifs <;> linarith [Real.sigmoid_pos η, Real.sigmoid_lt_one η]

/-- The logistic log likelihood is nonpositive: every factor of the likelihood is at most one. -/
lemma logisticLogLik_nonpos (z : C → κ → ℝ) {n : ℕ} (x : Fin n → C × ℝ) (ξ : κ → ℝ) :
    logisticLogLik z x ξ ≤ 0 :=
  Finset.sum_nonpos fun _ _ ↦ Real.log_nonpos (logisticDens_pos _ _).le (logisticDens_le_one _ _)

lemma continuous_logisticLogLik (z : C → κ → ℝ) {n : ℕ} (x : Fin n → C × ℝ) :
    Continuous (logisticLogLik z x) :=
  continuousOn_univ.mp ((concaveOn_logisticLogLik z x).continuousOn isOpen_univ)

lemma continuous_logisticLogLik_ofLp (z : C → κ → ℝ) {n : ℕ} (x : Fin n → C × ℝ) :
    Continuous fun θ : EuclideanSpace ℝ κ ↦ logisticLogLik z x (WithLp.ofLp θ) :=
  (continuous_logisticLogLik z x).comp (PiLp.continuous_ofLp 2 _)

/-- **The logistic posterior is a probability law** for every sample when the prior density is
measurable, nonnegative and integrable with positive integral. -/
theorem isProbabilityMeasure_logisticPosterior {p : (κ → ℝ) → ℝ} (hpm : Measurable p)
    (hp0 : ∀ ξ, 0 ≤ p ξ) (hpi : Integrable p) (hpZ : 0 < ∫ ξ, p ξ) (z : C → κ → ℝ) {n : ℕ}
    (x : Fin n → C × ℝ) : IsProbabilityMeasure (logisticPosterior p z x) := by
  unfold logisticPosterior
  have he : glmLikelihood logisticDens z x = fun ξ ↦ Real.exp (logisticLogLik z x ξ) :=
    funext (glmLikelihood_logisticDens_eq_exp z x)
  rw [he]
  exact isProbabilityMeasure_densityPosterior_of_le_one hpm hp0 hpi hpZ
    (continuous_logisticLogLik z x).measurable.exp (fun _ ↦ Real.exp_pos _)
    (fun ξ ↦ Real.exp_le_one_iff.2 (logisticLogLik_nonpos z x ξ))

/-- **The logistic posterior in Euclidean coordinates**: it is the image under `ofLp` of the
posterior on `EuclideanSpace ℝ κ` of the prior density `π ∘ ofLp` and the likelihood
`e^{ℓ_n ∘ ofLp}`. -/
theorem logisticPosterior_eq_map {p : (κ → ℝ) → ℝ} (hpm : Measurable p) (z : C → κ → ℝ)
    {n : ℕ} (x : Fin n → C × ℝ) :
    logisticPosterior p z x =
      (densityPosterior volume (fun θ : EuclideanSpace ℝ κ ↦ p (WithLp.ofLp θ))
        fun θ ↦ Real.exp (logisticLogLik z x (WithLp.ofLp θ))).map
        (PiLp.continuousLinearEquiv 2 ℝ fun _ : κ ↦ ℝ) := by
  set e : EuclideanSpace ℝ κ ≃ᵐ (κ → ℝ) := (MeasurableEquiv.toLp 2 (κ → ℝ)).symm
  have hcoe : ⇑(PiLp.continuousLinearEquiv 2 ℝ fun _ : κ ↦ ℝ) = ⇑e := rfl
  have hofm : Measurable fun θ : EuclideanSpace ℝ κ ↦ WithLp.ofLp θ := e.measurable
  have hpEm : Measurable fun θ : EuclideanSpace ℝ κ ↦ p (WithLp.ofLp θ) := hpm.comp hofm
  rw [hcoe, map_densityPosterior e hpEm ((continuous_logisticLogLik_ofLp z x).measurable.exp)]
  have hvol : (volume : Measure (EuclideanSpace ℝ κ)).map e = volume :=
    (PiLp.volume_preserving_ofLp κ).map_eq
  rw [hvol]
  unfold logisticPosterior
  congr 1
  funext ξ
  simp [e, glmLikelihood_logisticDens_eq_exp]

/-- **The score vanishes at the fit with probability tending to one** when `K` is a compact
neighborhood of `ξ₀` and the fit over `K` converges in probability to `ξ₀`: the fit then lies in
the interior of `K`, where it is a local maximizer of the log likelihood. -/
theorem withProbTendingToOne_logisticScoreSum_glmMLE_eq_zero {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {O : ℕ → Ω → C × ℝ} {z : C → κ → ℝ}
    {K : Set (κ → ℝ)} (hK : IsCompact K) {ξ₀ : κ → ℝ} (hKξ₀ : K ∈ 𝓝 ξ₀)
    (hcons : TendstoInMeasure P (glmMLE logisticDens z K O) atTop (fun _ ↦ ξ₀)) :
    WithProbTendingToOne P fun n ↦ {ω | logisticScoreSum z (fun i : Fin n ↦ O i ω)
      (glmMLE logisticDens z K O n ω) = 0} := by
  obtain ⟨r, hr, hrK⟩ := Metric.mem_nhds_iff.1 hKξ₀
  refine (hcons.withProbTendingToOne_dist_lt hr).mono fun n ω h1 ↦ ?_
  simp only [Set.mem_ofPred_eq] at h1 ⊢
  refine logisticScoreSum_glmMLE_eq_zero z hK O n ω (Metric.mem_nhds_iff.2
    ⟨r - dist (glmMLE logisticDens z K O n ω) ξ₀, sub_pos.2 h1, fun y hy ↦ hrK ?_⟩)
  rw [Metric.mem_ball] at hy ⊢
  linarith [dist_triangle y (glmMLE logisticDens z K O n ω) ξ₀]

/-! ### The theorem -/

variable [MeasurableSpace C] [DecidableEq κ]

/-- **The Bernstein and von Mises theorem for logistic regression, in Euclidean coordinates.**
Under the hypotheses of `isBernsteinVonMises_logistic`, the posteriors on `EuclideanSpace ℝ κ`
of the prior density `π ∘ ofLp` and the likelihood `e^{ℓ_n ∘ ofLp}` satisfy the total variation
conclusion with centering the maximum likelihood fit and limit `N(0, I(ξ₀)⁻¹)`. -/
theorem isBernsteinVonMises_logistic_euclidean {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {O : ℕ → Ω → C × ℝ} (hO : IsIIDSample O P)
    {R : Measure C} (hR : P.map (fun ω ↦ (O 0 ω).1) = R) {z : C → κ → ℝ}
    (hz : ∀ j, Measurable fun c ↦ z c j) {B : ℝ} (hB : ∀ᵐ c ∂R, ∀ j, |z c j| ≤ B)
    (hfull : ∀ v : κ → ℝ, (∀ᵐ c ∂R, z c ⬝ᵥ v = 0) → v = 0) {K : Set (κ → ℝ)}
    (hK : IsCompact K) {ξ₀ : κ → ℝ} (hKξ₀ : K ∈ 𝓝 ξ₀)
    (hcons : TendstoInMeasure P (glmMLE logisticDens z K O) atTop (fun _ ↦ ξ₀))
    {p : (κ → ℝ) → ℝ} (hpm : Measurable p) (hp0 : ∀ ξ, 0 ≤ p ξ) (hpi : Integrable p)
    (hpc : ContinuousAt p ξ₀) (hpξ₀ : 0 < p ξ₀) :
    IsBernsteinVonMises P
      (fun n ω ↦ densityPosterior volume (fun θ : EuclideanSpace ℝ κ ↦ p (WithLp.ofLp θ))
        fun θ ↦ Real.exp (logisticLogLik z (fun i : Fin n ↦ O i ω) (WithLp.ofLp θ)))
      (fun n ω ↦ WithLp.toLp 2 (glmMLE logisticDens z K O n ω))
      (multivariateGaussian 0 (logisticInfo R z ξ₀)⁻¹) := by
  have hzm : Measurable z := measurable_pi_iff.2 hz
  have hO1 : AEMeasurable (fun ω ↦ (O 0 ω).1) P := (hO.aemeasurable 0).fst
  have : IsProbabilityMeasure R := by
    rw [← hR]
    exact (Measure.isProbabilityMeasure_map_iff hO1).2 inferInstance
  set B' := max B 0 with hB'def
  have hB' : ∀ᵐ c ∂R, ∀ j, |z c j| ≤ B' := hB.mono fun c hc j ↦ (hc j).trans (le_max_left _ _)
  have hB'0 : 0 ≤ B' := le_max_right _ _
  set I := logisticInfo R z ξ₀ with hIdef
  have hI : I.PosDef := posDef_logisticInfo hzm hB hfull ξ₀
  obtain ⟨lam, hlam, hQ⟩ := exists_mul_sq_norm_le_quadForm hI
  -- the prior in Euclidean coordinates
  set pE : EuclideanSpace ℝ κ → ℝ := fun θ ↦ p (WithLp.ofLp θ) with hpEdef
  have hmp := PiLp.volume_preserving_ofLp κ
  have hpEm : Measurable pE := hpm.comp hmp.measurable
  have hpE0 : ∀ θ, 0 ≤ pE θ := fun θ ↦ hp0 _
  have hpEi : Integrable pE := (hmp.integrable_comp hpi.aestronglyMeasurable).2 hpi
  have hpEc : ContinuousAt pE (WithLp.toLp 2 ξ₀) :=
    hpc.comp (PiLp.continuous_ofLp 2 _).continuousAt
  have hpEZ : 0 < ∫ θ, pE θ := integral_pos_of_continuousAt hpE0 hpEi hpEc hpξ₀
  refine ⟨fun n ω ↦ ?_, inferInstance, ?_⟩
  · exact isProbabilityMeasure_densityPosterior_of_le_one hpEm hpE0 hpEi hpEZ
      (continuous_logisticLogLik_ofLp z _).measurable.exp (fun _ ↦ Real.exp_pos _)
      (fun θ ↦ Real.exp_le_one_iff.2 (logisticLogLik_nonpos z _ _))
  refine tendstoInMeasure_of_good_events fun ε hε κ' hκ' ↦ ?_
  -- constants
  set q : ℝ := (Fintype.card κ : ℝ) with hq
  set K0 := gaussianNormConst I with hK0def
  have hK0 : 0 < K0 := gaussianNormConst_pos hI
  set p₀ := p ξ₀ with hp₀
  set G8 := gaussianMass κ (lam / 8) with hG8def
  set G4 := gaussianMass κ (lam / 4) with hG4def
  have hG8 : 0 ≤ G8 := gaussianMass_nonneg (by positivity)
  have hG4 : 0 ≤ G4 := gaussianMass_nonneg (by positivity)
  set t := ε * p₀ / (8 * K0 * (G8 + 1)) with htdef
  have ht : 0 < t := by positivity
  set ηt := min (lam / 4) (t * lam / (8 * p₀)) with hηtdef
  have hηt : 0 < ηt := lt_min (by positivity) (by positivity)
  set e := ηt / (q ^ 2 + 1) with hedef
  have he : 0 < e := by positivity
  obtain ⟨δp, hδp, hδpc⟩ := Metric.continuousAt_iff.1 hpEc t ht
  set a := (q * B') ^ 3 with hadef
  have ha : 0 ≤ a := by positivity
  set δ := min (δp / 2) (ηt / (4 * (a + 1))) with hδdef
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  set η := a * (2 * δ) + q ^ 2 * e / 2 with hηdef
  have hη0 : 0 ≤ η := by positivity
  have hηle : η ≤ ηt := by
    have h1 : δ ≤ ηt / (4 * (a + 1)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h1
    have h2 : e * (q ^ 2 + 1) = ηt := div_mul_cancel₀ _ (by positivity)
    nlinarith [hδ.le, he.le, sq_nonneg q]
  -- the events
  obtain ⟨r, hr, hrK⟩ := Metric.mem_nhds_iff.1 hKξ₀
  have hcE : TendstoInMeasure P (fun n ω ↦ WithLp.toLp 2 (glmMLE logisticDens z K O n ω)) atTop
      (fun _ ↦ WithLp.toLp 2 ξ₀) :=
    hcons.comp_continuousAt (PiLp.continuous_toLp 2 _).continuousAt
  have A1 := hcons.withProbTendingToOne_dist_lt hr
  have A2 := hcE.withProbTendingToOne_dist_lt hδ
  have A3 := withProbTendingToOne_abs_logisticEmpInfo_sub_le hO hR hzm hB ξ₀ he
  have hset : MeasurableSet {x : C × ℝ | ∀ j, |z x.1 j| ≤ B'} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j ↦
      measurableSet_le (continuous_abs.measurable.comp ((hz j).comp measurable_fst))
        measurable_const
  have hBO : ∀ᵐ x ∂(P.map (O 0)), ∀ j, |z x.1 j| ≤ B' := by
    rw [ae_map_iff (hO.aemeasurable 0) hset]
    rw [← hR] at hB'
    exact ae_of_ae_map hO1 hB'
  have A4 := WithProbTendingToOne.of_ae (hO.ae_forall hBO)
  have hA := ((A1.inter A2).inter A3).inter A4
  refine ⟨_, hA.eventually_le hκ', ?_⟩
  -- the deterministic remainder tends to zero
  set S : ℕ → ℝ := fun n ↦ 2 * K0 / p₀ * (Real.exp (-((n : ℝ) * lam / 4) * δ ^ 2) *
    ((√(n : ℝ)) ^ Fintype.card κ * (∫ θ, pE θ) + p₀ * G4)) with hSdef
  have hS : Tendsto S atTop (𝓝 0) := by
    have hc : 0 < lam / 4 * δ ^ 2 := by positivity
    have h1 := tendsto_exp_neg_mul_sqrt_pow hc (Fintype.card κ)
    have h0 := tendsto_exp_neg_mul_sqrt_pow hc 0
    have := ((h1.mul_const (∫ θ, pE θ)).add (h0.mul_const (p₀ * G4))).const_mul (2 * K0 / p₀)
    simp only [pow_zero, mul_one, zero_mul, add_zero, mul_zero] at this
    refine this.congr fun n ↦ ?_
    simp only [hSdef]
    rw [show -((n : ℝ) * lam / 4) * δ ^ 2 = -((n : ℝ) * (lam / 4 * δ ^ 2)) by ring]
    ring
  filter_upwards [hS.eventually (gt_mem_nhds (half_pos hε)), eventually_ge_atTop 1]
    with n hSn hn ω hω
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hω
  simp only [Set.mem_ofPred_eq] at h1 h2 h3 h4
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set x : Fin n → C × ℝ := fun i ↦ O i ω with hxdef
  set ξh := glmMLE logisticDens z K O n ω with hξh
  set m : EuclideanSpace ℝ κ := WithLp.toLp 2 ξh with hmdef
  -- the score vanishes at the fit
  have hnhds : K ∈ 𝓝 ξh := Metric.mem_nhds_iff.2 ⟨r - dist ξh ξ₀, sub_pos.2 h1, fun y hy ↦
    hrK (by
      rw [Metric.mem_ball] at hy ⊢
      linarith [dist_triangle y ξh ξ₀])⟩
  have hscore : logisticScoreSum z x (WithLp.ofLp m) = 0 :=
    logisticScoreSum_glmMLE_eq_zero z hK O n ω hnhds
  have hm : ‖m - WithLp.toLp 2 ξ₀‖ < δ := by rw [← dist_eq_norm]; exact h2
  -- the quadratic expansion on the ball of radius `δ`
  have hquad : ∀ u, ‖u‖ ≤ δ → |logisticLogLik z x (WithLp.ofLp (m + u)) -
      logisticLogLik z x (WithLp.ofLp m) + n / 2 * quadForm I u| ≤ η * n * ‖u‖ ^ 2 := by
    intro u hu
    refine (abs_logisticLogLik_quad_le hB'0 (x := x) (fun i j ↦ h4 i j) ξ₀ I
      (fun j k ↦ h3 j k) hscore u).trans ?_
    have hle : a * (‖m - WithLp.toLp 2 ξ₀‖ + ‖u‖) + q ^ 2 * e / 2 ≤ η := by
      simp only [hηdef]
      nlinarith [norm_nonneg u, norm_nonneg (m - WithLp.toLp 2 ξ₀)]
    calc (n : ℝ) * (a * (‖m - WithLp.toLp 2 ξ₀‖ + ‖u‖) + q ^ 2 * e / 2) * ‖u‖ ^ 2
        ≤ n * η * ‖u‖ ^ 2 := by gcongr
      _ = η * n * ‖u‖ ^ 2 := by ring
  -- the prior varies by at most `t` near the fit
  have hosc : ∀ θ, ‖θ - m‖ ≤ δ → |pE θ - pE (WithLp.toLp 2 ξ₀)| ≤ t := by
    intro θ hθ
    have hd : dist θ (WithLp.toLp 2 ξ₀) < δp := by
      rw [dist_eq_norm]
      calc ‖θ - WithLp.toLp 2 ξ₀‖ = ‖(θ - m) + (m - WithLp.toLp 2 ξ₀)‖ := by
            rw [sub_add_sub_cancel]
        _ ≤ ‖θ - m‖ + ‖m - WithLp.toLp 2 ξ₀‖ := norm_add_le _ _
        _ < δ + δ := add_lt_add_of_le_of_lt hθ hm
        _ ≤ δp := by linarith [min_le_left (δp / 2) (ηt / (4 * (a + 1)))]
    have := hδpc hd
    rw [Real.dist_eq] at this
    exact this.le
  have hbound := tvDist_densityPosterior_gaussian_le hI hlam hQ hpEm hpE0 hpEi hpEZ
    (concaveOn_logisticLogLik_ofLp z x) hnR hη0 (hηle.trans (min_le_left _ _)) hδ hquad hosc
    hpξ₀
  have h8 : 8 * p₀ * η / lam ≤ t := by
    rw [div_le_iff₀ hlam]
    have h := hηle.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h
    nlinarith
  have hfirst : 2 * K0 / p₀ * ((t + 8 * p₀ * η / lam) * G8) ≤ ε / 2 := by
    calc 2 * K0 / p₀ * ((t + 8 * p₀ * η / lam) * G8) ≤ 2 * K0 / p₀ * ((2 * t) * G8) := by
          gcongr
          linarith
      _ = ε / 2 * (G8 / (G8 + 1)) := by
          simp only [htdef]
          field_simp
          ring
      _ ≤ ε / 2 := mul_le_of_le_one_right (by positivity)
          ((div_le_one (by positivity)).2 (by linarith))
  rw [Real.dist_eq, sub_zero, abs_of_nonneg tvDist_nonneg]
  calc _ ≤ _ := hbound
    _ = 2 * K0 / p₀ * ((t + 8 * p₀ * η / lam) * G8) + S n := by
        simp only [hSdef]
        ring
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt hfirst hSn
    _ = ε := add_halves ε

/-- **The Bernstein and von Mises theorem for logistic regression.** Let the records `O i` be
i.i.d. with design arguments of law `R`, let the design `z` be measurable, bounded `R`-almost
surely and of full rank under `R`, let `K` be a compact neighborhood of `ξ₀` on which the
maximum likelihood fit `ξ̂_n` converges in probability to `ξ₀`, and let the prior density `π` be
measurable, nonnegative, integrable, continuous at `ξ₀` and positive there. Then the logistic
posteriors satisfy `‖Π_n - N(ξ̂_n, n⁻¹ I(ξ₀)⁻¹)‖_TV → 0` in probability: the conclusion of
`IsBernsteinVonMises` with the limit `N(0, I(ξ₀)⁻¹)`, the information matrix being
`I(ξ₀) = ∫ w(z(c) ⬝ ξ₀) z(c) z(c)ᵀ dR`. -/
theorem isBernsteinVonMises_logistic {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {O : ℕ → Ω → C × ℝ} (hO : IsIIDSample O P)
    {R : Measure C} (hR : P.map (fun ω ↦ (O 0 ω).1) = R) {z : C → κ → ℝ}
    (hz : ∀ j, Measurable fun c ↦ z c j) {B : ℝ} (hB : ∀ᵐ c ∂R, ∀ j, |z c j| ≤ B)
    (hfull : ∀ v : κ → ℝ, (∀ᵐ c ∂R, z c ⬝ᵥ v = 0) → v = 0) {K : Set (κ → ℝ)}
    (hK : IsCompact K) {ξ₀ : κ → ℝ} (hKξ₀ : K ∈ 𝓝 ξ₀)
    (hcons : TendstoInMeasure P (glmMLE logisticDens z K O) atTop (fun _ ↦ ξ₀))
    {p : (κ → ℝ) → ℝ} (hpm : Measurable p) (hp0 : ∀ ξ, 0 ≤ p ξ) (hpi : Integrable p)
    (hpc : ContinuousAt p ξ₀) (hpξ₀ : 0 < p ξ₀) :
    IsBernsteinVonMises P (fun n ω ↦ logisticPosterior p z fun i : Fin n ↦ O i ω)
      (glmMLE logisticDens z K O)
      ((multivariateGaussian 0 (logisticInfo R z ξ₀)⁻¹).map
        (PiLp.continuousLinearEquiv 2 ℝ fun _ : κ ↦ ℝ)) := by
  have h := (isBernsteinVonMises_logistic_euclidean hO hR hz hB hfull hK hKξ₀ hcons hpm hp0 hpi
    hpc hpξ₀).map_continuousLinearEquiv (PiLp.continuousLinearEquiv 2 ℝ fun _ : κ ↦ ℝ)
  have hPn : (fun n ω ↦ logisticPosterior p z fun i : Fin n ↦ O i ω) = fun n ω ↦
      (densityPosterior volume (fun θ : EuclideanSpace ℝ κ ↦ p (WithLp.ofLp θ))
        fun θ ↦ Real.exp (logisticLogLik z (fun i : Fin n ↦ O i ω) (WithLp.ofLp θ))).map
        (PiLp.continuousLinearEquiv 2 ℝ fun _ : κ ↦ ℝ) :=
    funext fun n ↦ funext fun ω ↦ logisticPosterior_eq_map hpm z _
  rw [hPn]
  exact h

end PosteriorLimit

end CausalInference
