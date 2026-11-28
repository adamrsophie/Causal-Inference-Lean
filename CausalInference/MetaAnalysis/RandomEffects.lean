/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.MetaAnalysis.CochranQ
public import CausalInference.PartialIdentification.IdentifiedSet

/-!
# Meta-analysis: the random effects model and identifiability

In the **random effects model** the estimate of study `i` is `Yᵢ = θ + bᵢ + εᵢ`: a mean effect
`θ`, a study effect `bᵢ` with mean `0` and **between study variance** `τ² ≥ 0`, and a sampling
error `εᵢ` with mean `0` and known within-study variance `vᵢ > 0`.

* `IsRandomEffectsModel` asks only for moments: square integrable components, the stated means
  and variances, and no correlation between different components. This is what the moment
  estimator of `τ²` needs.
* `IsGaussianRandomEffectsModel` asks that the `2k` variables are independent with
  `bᵢ ~ N(0, τ²)` and `εᵢ ~ N(0, vᵢ)` (the joint law of the two vectors is the product of the
  `2k` Gaussian laws).

**The marginal law.** In the Gaussian model the estimates are independent with
`Yᵢ ~ N(θ, vᵢ + τ²)`: the random effects model is the Gaussian common effect model with the
shifted variances `vᵢ + τ²` (`IsGaussianRandomEffectsModel.isGaussianCommonEffectModel`). Hence
the **random effects weights** are `ivWeight (fun i => v i + τ²) i = 1 / (vᵢ + τ²)` and the random
effects pooled estimate is `ivwEstimate (fun i => v i + τ²)`, and every theorem on the common
effect model applies with these variances. In the moment model the pooled estimate with the
shifted weights is unbiased with variance `1 / ∑ᵢ 1 / (vᵢ + τ²)`
(`IsRandomEffectsModel.integral_variance_ivwEstimate`).

**Identifiability.** With known `vᵢ > 0` and at least one study, `(θ, τ²)` is point identified
by the law of the data on `ℝ × [0, ∞)` (`pointIdentified_randomEffects`): the law of the first
study already determines its mean `θ` and its variance `v₁ + τ²`. Identification fails in
exactly these ways:

* with no study at all, every parameter gives the same (trivial) law
  (`not_pointIdentified_randomEffects_of_isEmpty`);
* when the within-study variances are not known, `(v, τ²)` and `(v + δ, τ² - δ)` give the same
  law, so `τ²` is not identified from one law, for any number of studies
  (`not_pointIdentified_tau_of_unknown_variance`);
* with one study and known `v₁`, the law identifies `τ²`, but Cochran's `Q` is identically `0`
  and its slope `c` in `τ²` is `0`, so the moment equation `E[Q] = (k - 1) + τ² c` carries no
  information on `τ²` (`cochranQ_of_card_eq_one`, `cochranQSlope_of_card_eq_one`).

## Main definitions

* `IsRandomEffectsModel`, `IsGaussianRandomEffectsModel`.

## Main results

* `IsGaussianRandomEffectsModel.isRandomEffectsModel`,
  `IsGaussianRandomEffectsModel.hasLaw_pi`,
  `IsGaussianRandomEffectsModel.isGaussianCommonEffectModel`.
* `IsRandomEffectsModel.integral_eq`, `IsRandomEffectsModel.variance_eq`,
  `IsRandomEffectsModel.covariance_eq_zero`, `IsRandomEffectsModel.integral_cochranQ`,
  `IsRandomEffectsModel.integral_variance_ivwEstimate`.
* `randomEffects_identifiable`, `pointIdentified_randomEffects`,
  `not_pointIdentified_randomEffects_of_isEmpty`,
  `not_pointIdentified_tau_of_unknown_variance`, `cochranQ_of_card_eq_one`,
  `cochranQSlope_of_card_eq_one`.
* `isGaussianRandomEffectsModel_prod`: the coordinates of `⊗ᵢ N(0, τ²) ⊗ ⊗ᵢ N(0, vᵢ)` form a
  Gaussian random effects model, so every hypothesis of this file is met.

## References

* R. DerSimonian and N. Laird, *Meta-analysis in clinical trials*, Controlled Clinical Trials 7
  (1986).
* J. P. T. Higgins, S. G. Thompson and D. J. Spiegelhalter, *A re-evaluation of random-effects
  meta-analysis*, Journal of the Royal Statistical Society A 172 (2009).
-/

@[expose] public section

namespace CausalInference

namespace MetaAnalysis

open MeasureTheory ProbabilityTheory Finset

/-! ### The two models -/

section Model

variable {ι Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {b ε : ι → Ω → ℝ}
  {τ2 : ℝ} {v : ι → ℝ}

variable (P b ε τ2 v) in
/-- The **random effects model, moment form**: for the estimates `Yᵢ = θ + bᵢ + εᵢ`, the study
effects `bᵢ` and the errors `εᵢ` are square integrable with mean `0`, `Var(bᵢ) = τ² ≥ 0`,
`Var(εᵢ) = vᵢ > 0`, and different components are uncorrelated. -/
structure IsRandomEffectsModel : Prop where
  /-- `P` is a probability measure. -/
  isProbabilityMeasure : IsProbabilityMeasure P
  /-- The study effects are square integrable. -/
  memLp_b : ∀ i, MemLp (b i) 2 P
  /-- The errors are square integrable. -/
  memLp_ε : ∀ i, MemLp (ε i) 2 P
  /-- `E[bᵢ] = 0`. -/
  integral_b : ∀ i, ∫ ω, b i ω ∂P = 0
  /-- `E[εᵢ] = 0`. -/
  integral_ε : ∀ i, ∫ ω, ε i ω ∂P = 0
  /-- `Var(bᵢ) = τ²`. -/
  variance_b : ∀ i, Var[b i; P] = τ2
  /-- `Var(εᵢ) = vᵢ`. -/
  variance_ε : ∀ i, Var[ε i; P] = v i
  /-- Study effects of different studies are uncorrelated. -/
  cov_bb : ∀ i j, i ≠ j → cov[b i, b j; P] = 0
  /-- Errors of different studies are uncorrelated. -/
  cov_εε : ∀ i j, i ≠ j → cov[ε i, ε j; P] = 0
  /-- Every study effect is uncorrelated with every error. -/
  cov_bε : ∀ i j, cov[b i, ε j; P] = 0
  /-- `τ² ≥ 0`. -/
  tau_nonneg : 0 ≤ τ2
  /-- The within-study variances are positive. -/
  pos : ∀ i, 0 < v i

variable [Fintype ι]

variable (P b ε τ2 v) in
/-- The **Gaussian random effects model**: the study effects and the errors are `2k` independent
variables with `bᵢ ~ N(0, τ²)` and `εᵢ ~ N(0, vᵢ)`, `τ² ≥ 0`, `vᵢ > 0`; that is, the pair of
vectors `(b, ε)` has the law `⊗ᵢ N(0, τ²) ⊗ ⊗ᵢ N(0, vᵢ)`. The estimates are
`Yᵢ = θ + bᵢ + εᵢ`. -/
structure IsGaussianRandomEffectsModel : Prop where
  /-- The joint law of the study effects and the errors. -/
  hasLaw : HasLaw (fun ω => ((fun i => b i ω), fun i => ε i ω))
    ((Measure.pi fun _ : ι => gaussianReal 0 τ2.toNNReal).prod
      (Measure.pi fun i => gaussianReal 0 (v i).toNNReal)) P
  /-- `τ² ≥ 0`. -/
  tau_nonneg : 0 ≤ τ2
  /-- The within-study variances are positive. -/
  pos : ∀ i, 0 < v i

namespace IsGaussianRandomEffectsModel

variable (h : IsGaussianRandomEffectsModel P b ε τ2 v)
include h

/-- The vector of study effects has law `⊗ᵢ N(0, τ²)`. -/
theorem hasLaw_b :
    HasLaw (fun ω i => b i ω) (Measure.pi fun _ : ι => gaussianReal 0 τ2.toNNReal) P :=
  (measurePreserving_fst (μ := Measure.pi fun _ : ι => gaussianReal 0 τ2.toNNReal)
    (ν := Measure.pi fun i => gaussianReal 0 (v i).toNNReal)).hasLaw.comp h.hasLaw

/-- The vector of errors has law `⊗ᵢ N(0, vᵢ)`. -/
theorem hasLaw_ε :
    HasLaw (fun ω i => ε i ω) (Measure.pi fun i => gaussianReal 0 (v i).toNNReal) P :=
  (measurePreserving_snd (μ := Measure.pi fun _ : ι => gaussianReal 0 τ2.toNNReal)
    (ν := Measure.pi fun i => gaussianReal 0 (v i).toNNReal)).hasLaw.comp h.hasLaw

/-- **The marginal law of the random effects model**: the estimates `Yᵢ = θ + bᵢ + εᵢ` are
independent with `Yᵢ ~ N(θ, vᵢ + τ²)`. Proof: regroup the product law coordinatewise and
convolve the two Gaussian laws of each study. -/
theorem hasLaw_pi (θ : ℝ) :
    HasLaw (fun ω i => θ + b i ω + ε i ω)
      (Measure.pi fun i => gaussianReal θ (v i + τ2).toNNReal) P := by
  have e := measurePreserving_arrowProdEquivProdArrow ℝ ℝ ι
    (fun _ => gaussianReal 0 τ2.toNNReal) (fun i => gaussianReal 0 (v i).toNNReal)
  have hF : HasLaw (fun x : ι → ℝ × ℝ => fun i => θ + (x i).1 + (x i).2)
      (Measure.pi fun i => gaussianReal θ (v i + τ2).toNNReal)
      (Measure.pi fun i => (gaussianReal 0 τ2.toNNReal).prod
        (gaussianReal 0 (v i).toNNReal)) := by
    refine ⟨by fun_prop, ?_⟩
    rw [Measure.pi_map_pi (f := fun (_ : ι) (p : ℝ × ℝ) => θ + p.1 + p.2)
      (fun i => by fun_prop)]
    congr 1
    funext i
    have hsplit : (fun p : ℝ × ℝ => θ + p.1 + p.2) =
        (fun x => θ + x) ∘ fun p : ℝ × ℝ => p.1 + p.2 := by
      funext p
      simp only [Function.comp_apply]
      ring
    rw [hsplit, ← Measure.map_map (by fun_prop) (by fun_prop)]
    change ((gaussianReal 0 τ2.toNNReal) ∗ (gaussianReal 0 (v i).toNNReal)).map _ = _
    rw [gaussianReal_conv_gaussianReal, gaussianReal_map_const_add, add_zero, zero_add,
      add_comm (v i), Real.toNNReal_add h.tau_nonneg (h.pos i).le]
  exact hF.comp ((MeasurePreserving.symm _ e).hasLaw.comp h.hasLaw)

/-- **The random effects model is the common effect model with shifted variances**: in the
Gaussian random effects model the estimates `Yᵢ = θ + bᵢ + εᵢ` form a Gaussian common effect
model with variances `vᵢ + τ²`. Every result on the common effect model therefore applies to
the random effects pooled estimate `ivwEstimate (fun i => v i + τ²)`. -/
theorem isGaussianCommonEffectModel (θ : ℝ) :
    IsGaussianCommonEffectModel P (fun i ω => θ + b i ω + ε i ω) θ fun i => v i + τ2 :=
  isGaussianCommonEffectModel_of_hasLaw (fun i => add_pos_of_pos_of_nonneg (h.pos i)
    h.tau_nonneg) (h.hasLaw_pi θ)

/-- The Gaussian random effects model satisfies the moment form. -/
theorem isRandomEffectsModel : IsRandomEffectsModel P b ε τ2 v := by
  have hP : IsProbabilityMeasure P := h.hasLaw.isProbabilityMeasure
  have hBi : ∀ i, HasLaw (b i) (gaussianReal 0 τ2.toNNReal) P := fun i =>
    (measurePreserving_eval (fun _ : ι => gaussianReal 0 τ2.toNNReal) i).hasLaw.comp h.hasLaw_b
  have hEi : ∀ i, HasLaw (ε i) (gaussianReal 0 (v i).toNNReal) P := fun i =>
    (measurePreserving_eval (fun i => gaussianReal 0 (v i).toNNReal) i).hasLaw.comp h.hasLaw_ε
  have hBind : iIndepFun b P := (iIndepFun_iff_hasLaw_pi_pi hBi).2 h.hasLaw_b
  have hEind : iIndepFun ε P := (iIndepFun_iff_hasLaw_pi_pi hEi).2 h.hasLaw_ε
  have hBE : IndepFun (fun ω i => b i ω) (fun ω i => ε i ω) P :=
    (indepFun_iff_hasLaw_prodMk_prod h.hasLaw_b h.hasLaw_ε).2 h.hasLaw
  have hBm : ∀ i, MemLp (b i) 2 P := fun i => (hBi i).memLp (memLp_id_gaussianReal 2)
  have hEm : ∀ i, MemLp (ε i) 2 P := fun i => (hEi i).memLp (memLp_id_gaussianReal 2)
  exact
    { isProbabilityMeasure := hP
      memLp_b := hBm
      memLp_ε := hEm
      integral_b := fun i => by rw [(hBi i).integral_eq, integral_id_gaussianReal]
      integral_ε := fun i => by rw [(hEi i).integral_eq, integral_id_gaussianReal]
      variance_b := fun i => by
        rw [(hBi i).variance_eq, variance_id_gaussianReal, Real.coe_toNNReal _ h.tau_nonneg]
      variance_ε := fun i => by
        rw [(hEi i).variance_eq, variance_id_gaussianReal, Real.coe_toNNReal _ (h.pos i).le]
      cov_bb := fun i j hij => (hBind.indepFun hij).covariance_eq_zero (hBm i) (hBm j)
      cov_εε := fun i j hij => (hEind.indepFun hij).covariance_eq_zero (hEm i) (hEm j)
      cov_bε := fun i j => (hBE.comp (φ := fun x : ι → ℝ => x i) (ψ := fun x : ι → ℝ => x j)
        (by fun_prop) (by fun_prop)).covariance_eq_zero (hBm i) (hEm j)
      tau_nonneg := h.tau_nonneg
      pos := h.pos }

end IsGaussianRandomEffectsModel

end Model

/-! ### Moments of the estimates -/

namespace IsRandomEffectsModel

variable {ι Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {b ε : ι → Ω → ℝ}
  {τ2 : ℝ} {v : ι → ℝ}

variable (h : IsRandomEffectsModel P b ε τ2 v)
include h

/-- The estimates are square integrable. -/
theorem memLp (θ : ℝ) (i : ι) : MemLp (fun ω => θ + b i ω + ε i ω) 2 P :=
  have := h.isProbabilityMeasure
  ((memLp_const θ).add (h.memLp_b i)).add (h.memLp_ε i)

/-- `E[Yᵢ] = θ`. -/
theorem integral_eq (θ : ℝ) (i : ι) : ∫ ω, θ + b i ω + ε i ω ∂P = θ := by
  have := h.isProbabilityMeasure
  rw [integral_add (f := fun ω => θ + b i ω)
      ((integrable_const θ).add ((h.memLp_b i).integrable one_le_two))
      ((h.memLp_ε i).integrable one_le_two),
    integral_add (f := fun _ => θ) (integrable_const θ) ((h.memLp_b i).integrable one_le_two),
    h.integral_b,
    h.integral_ε, integral_const, probReal_univ, one_smul, add_zero, add_zero]

/-- The covariance of two estimates: `cov(Yᵢ, Yⱼ) = cov(bᵢ, bⱼ) + cov(εᵢ, εⱼ)`. -/
theorem covariance_eq_add (θ : ℝ) (i j : ι) :
    cov[fun ω => θ + b i ω + ε i ω, fun ω => θ + b j ω + ε j ω; P] =
      cov[b i, b j; P] + cov[ε i, ε j; P] := by
  have := h.isProbabilityMeasure
  have hδ : ∀ i, MemLp (b i + ε i) 2 P := fun i => (h.memLp_b i).add (h.memLp_ε i)
  have hYe : ∀ i, (fun ω => θ + b i ω + ε i ω) = fun ω => θ + (b i + ε i) ω := fun i => by
    funext ω; simp only [Pi.add_apply]; ring
  rw [hYe i, hYe j, covariance_const_add_left ((hδ i).integrable one_le_two),
    covariance_const_add_right ((hδ j).integrable one_le_two),
    covariance_add_left (h.memLp_b i) (h.memLp_ε i) (hδ j),
    covariance_add_right (h.memLp_b i) (h.memLp_b j) (h.memLp_ε j),
    covariance_add_right (h.memLp_ε i) (h.memLp_b j) (h.memLp_ε j),
    covariance_comm (ε i) (b j), h.cov_bε, h.cov_bε]
  ring

/-- `Var(Yᵢ) = vᵢ + τ²`. -/
theorem variance_eq (θ : ℝ) (i : ι) : Var[fun ω => θ + b i ω + ε i ω; P] = v i + τ2 := by
  rw [← covariance_self (h.memLp θ i).aemeasurable, h.covariance_eq_add,
    covariance_self (h.memLp_b i).aemeasurable, covariance_self (h.memLp_ε i).aemeasurable,
    h.variance_b, h.variance_ε, add_comm]

/-- Estimates of different studies are uncorrelated. -/
theorem covariance_eq_zero (θ : ℝ) {i j : ι} (hij : i ≠ j) :
    cov[fun ω => θ + b i ω + ε i ω, fun ω => θ + b j ω + ε j ω; P] = 0 := by
  rw [h.covariance_eq_add, h.cov_bb i j hij, h.cov_εε i j hij, add_zero]

variable [Fintype ι]

/-- **`E[Q]` in the random effects model**: with the within-study weights `1 / vᵢ`, `Q` is
integrable and `E[Q] = (k - 1) + τ² c`, `c = cochranQSlope v`. -/
theorem integral_cochranQ [Nonempty ι] (θ : ℝ) :
    Integrable (fun ω => cochranQ v fun i => θ + b i ω + ε i ω) P ∧
      ∫ ω, cochranQ v (fun i => θ + b i ω + ε i ω) ∂P =
        (Fintype.card ι - 1) + τ2 * cochranQSlope v :=
  have := h.isProbabilityMeasure
  integral_cochranQ_of_components h.pos h.memLp_b h.memLp_ε h.integral_b h.integral_ε
    h.variance_b h.variance_ε h.cov_bb h.cov_εε h.cov_bε

/-- **The random effects pooled estimate**: with the weights `1 / (vᵢ + τ²)`, the pooled
estimate `ivwEstimate (fun i => v i + τ²)` is unbiased for `θ` with variance
`1 / ∑ᵢ 1 / (vᵢ + τ²)`. -/
theorem integral_variance_ivwEstimate [Nonempty ι] (θ : ℝ) :
    ∫ ω, ivwEstimate (fun i => v i + τ2) (fun i => θ + b i ω + ε i ω) ∂P = θ ∧
      Var[fun ω => ivwEstimate (fun i => v i + τ2) (fun i => θ + b i ω + ε i ω); P] =
        1 / ∑ i, ivWeight (fun i => v i + τ2) i := by
  have := h.isProbabilityMeasure
  have hv : ∀ i, 0 < v i + τ2 := fun i => add_pos_of_pos_of_nonneg (h.pos i) h.tau_nonneg
  exact ⟨integral_ivwEstimate hv (fun i => (h.memLp θ i).integrable one_le_two)
      (h.integral_eq θ),
    variance_ivwEstimate (Y := fun i ω => θ + b i ω + ε i ω) hv (h.memLp θ) (h.variance_eq θ)
      fun _ _ hij => h.covariance_eq_zero θ hij⟩

end IsRandomEffectsModel

/-! ### Identifiability -/

section Identifiability

variable {ι : Type*} [Fintype ι]

/-- **Identifiability of the random effects parameters**: with known within-study variances
`vᵢ > 0` and at least one study, the law `⊗ᵢ N(θ, vᵢ + τ²)` determines `θ` and `τ² ≥ 0`. Proof:
the law of the first study has mean `θ` and variance `v₁ + τ²`. -/
theorem randomEffects_identifiable [Nonempty ι] {v : ι → ℝ} (hv : ∀ i, 0 < v i)
    {θ θ' τ2 τ2' : ℝ} (hτ : 0 ≤ τ2) (hτ' : 0 ≤ τ2')
    (h : Measure.pi (fun i => gaussianReal θ (v i + τ2).toNNReal) =
      Measure.pi (fun i => gaussianReal θ' (v i + τ2').toNNReal)) :
    θ = θ' ∧ τ2 = τ2' := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hm : ∀ a t : ℝ, (Measure.pi fun j => gaussianReal a (v j + t).toNNReal).map
      (Function.eval i) = gaussianReal a (v i + t).toNNReal := fun a t =>
    (measurePreserving_eval (fun j => gaussianReal a (v j + t).toNNReal) i).map_eq
  have h1 : gaussianReal θ (v i + τ2).toNNReal = gaussianReal θ' (v i + τ2').toNNReal := by
    rw [← hm, ← hm, h]
  have hmean := congrArg (fun μ => ∫ x, x ∂μ) h1
  have hvar := congrArg (fun μ => Var[fun x => x; μ]) h1
  simp only [integral_id_gaussianReal] at hmean
  simp only [variance_fun_id_gaussianReal, Real.coe_toNNReal _ (add_nonneg (hv i).le hτ),
    Real.coe_toNNReal _ (add_nonneg (hv i).le hτ')] at hvar
  exact ⟨hmean, by linarith⟩

/-- **`(θ, τ²)` is point identified** on `ℝ × [0, ∞)` by the law of the data, for known
`vᵢ > 0` and at least one study. -/
theorem pointIdentified_randomEffects [Nonempty ι] {v : ι → ℝ} (hv : ∀ i, 0 < v i) :
    PointIdentified {p : ℝ × ℝ | 0 ≤ p.2}
      (fun p => Measure.pi fun i => gaussianReal p.1 (v i + p.2).toNNReal) id := by
  rintro ⟨θ, τ2⟩ hτ ⟨θ', τ2'⟩ hτ' h
  obtain ⟨h1, h2⟩ := randomEffects_identifiable hv hτ hτ' h
  exact Prod.ext h1 h2

/-- **No study, no identification**: with an empty set of studies every parameter gives the
same law, so neither `θ` nor `τ²` is identified. -/
theorem not_pointIdentified_randomEffects_of_isEmpty [IsEmpty ι] (v : ι → ℝ) :
    ¬ PointIdentified {p : ℝ × ℝ | 0 ≤ p.2}
      (fun p => Measure.pi fun i => gaussianReal p.1 (v i + p.2).toNNReal) id := by
  intro h
  have := h (0, 0) (show (0 : ℝ) ≤ 0 from le_rfl) (1, 1) (show (0 : ℝ) ≤ 1 from zero_le_one) (by
    simp only
    rw [Measure.pi_of_empty, Measure.pi_of_empty])
  simp at this

/-- **Unknown within-study variances: `τ²` is not identified**, for any number of studies. The
parameter `(v, τ²)` with `v ≡ 2, τ² = 0` and with `v ≡ 1, τ² = 1` gives the same law
`⊗ᵢ N(θ, 2)`: only the sums `vᵢ + τ²` are identified. -/
theorem not_pointIdentified_tau_of_unknown_variance [Nonempty ι] (θ : ℝ) :
    ¬ PointIdentified {p : (ι → ℝ) × ℝ | (∀ i, 0 < p.1 i) ∧ 0 ≤ p.2}
      (fun p => Measure.pi fun i => gaussianReal θ (p.1 i + p.2).toNNReal) Prod.snd := by
  intro h
  have := h ((fun _ => 2), 0) ⟨fun _ => two_pos, le_rfl⟩ ((fun _ => 1), 1)
    ⟨fun _ => one_pos, zero_le_one⟩ (by norm_num)
  norm_num at this

/-- **One study: `Q` is identically zero**, whatever the data. -/
theorem cochranQ_of_card_eq_one {v : ι → ℝ} (hv : ∀ i, 0 < v i) (hk : Fintype.card ι = 1)
    (y : ι → ℝ) : cochranQ v y = 0 := by
  obtain ⟨i, hi⟩ := Fintype.card_eq_one_iff.1 hk
  exact (cochranQ_eq_zero_iff hv y).2 fun j l => by rw [hi j, hi l]

/-- **One study: the slope of `E[Q]` in `τ²` is zero**, `c = w₁ - w₁² / w₁ = 0`, so the
expectation `E[Q] = (k - 1) + τ² c` does not depend on `τ²`. -/
theorem cochranQSlope_of_card_eq_one {v : ι → ℝ} (hv : ∀ i, 0 < v i)
    (hk : Fintype.card ι = 1) : cochranQSlope v = 0 := by
  obtain ⟨i, hi⟩ := Fintype.card_eq_one_iff.1 hk
  have huniv : (Finset.univ : Finset ι) = {i} := by
    ext j; simp [hi j]
  rw [cochranQSlope, huniv, Finset.sum_singleton, Finset.sum_singleton, sq,
    mul_div_cancel_right₀ _ (ivWeight_pos hv i).ne', sub_self]

end Identifiability

/-! ### A concrete model -/

/-- **A concrete Gaussian random effects model**: on the product space
`(ι → ℝ) × (ι → ℝ)` with the law `⊗ᵢ N(0, τ²) ⊗ ⊗ᵢ N(0, vᵢ)`, `τ² ≥ 0`, `vᵢ > 0`, the two
coordinate vectors form a Gaussian random effects model. -/
theorem isGaussianRandomEffectsModel_prod {ι : Type*} [Fintype ι] {v : ι → ℝ}
    (hv : ∀ i, 0 < v i) {τ2 : ℝ} (hτ : 0 ≤ τ2) :
    IsGaussianRandomEffectsModel
      ((Measure.pi fun _ : ι => gaussianReal 0 τ2.toNNReal).prod
        (Measure.pi fun i => gaussianReal 0 (v i).toNNReal))
      (fun i ω => ω.1 i) (fun i ω => ω.2 i) τ2 v where
  hasLaw := by
    have : (fun ω : (ι → ℝ) × (ι → ℝ) => ((fun i => ω.1 i), fun i => ω.2 i)) = id := rfl
    rw [this]
    exact HasLaw.id
  tau_nonneg := hτ
  pos := hv

end MetaAnalysis

end CausalInference
