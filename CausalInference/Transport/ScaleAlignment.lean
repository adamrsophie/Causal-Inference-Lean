/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Transport.Direct
public import CausalInference.Measures.OddsRatioLink
public import CausalInference.Estimation.Consistency
public import Mathlib.Analysis.SpecialFunctions.Sigmoid
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Transport: misaligned scales and the consistency of the two step estimator

**Scale alignment.** A model on the link `g` with inverse `ginv` gives the arms the predictors
`η_C(x)` and `η_B(x) = η_C(x) + γ`: the effect on the `g` scale is the constant `γ`. An effect
reported on the scale `h` compares the means through `ψ = h ∘ ginv`; at a stratum with predictor
`η` it is `ψ(η + γ) - ψ(η)`. On an open interval `(a, b)` of predictor values:

* **If `ψ` is affine**, `ψ(η) = k η + l`, the reported effect is `k γ` in every stratum, so it is
  the same in every population (`linkContrast_eq_of_affine`, `linkConditional_eq_of_affine`).
  This direction needs no regularity of `ψ`. The aligned case of
  `linkContrast_eq_of_isAlignedScale` is `k = 1`, `l = 0`.
* **If `ψ` is differentiable and not affine**, there are two predictor values and a shift
  `γ ≠ 0` at which the reported effects differ (`exists_sub_ne_of_not_affine`); the point
  masses at two strata with a common effect `γ` on the `g` scale then have different average
  conditional effects on the `h` scale (`exists_linkConditional_ne_of_not_affine`). This
  direction uses differentiability of `ψ` on `(a, b)`, in particular it holds when `ψ` is twice
  continuously differentiable there (`exists_sub_ne_of_contDiffOn`).

Together (`forall_sub_eq_iff_affine`): for `ψ` differentiable on `(a, b)`, the reported effect of
a common shift is the same at every pair of strata exactly when `ψ` is affine on `(a, b)`. The
proof differentiates `η ↦ ψ(η + γ) - ψ(η)`, which is locally constant, so `ψ'` is constant and
`ψ` is affine by the mean value theorem (`IsOpen.exists_eq_add_of_deriv_eq`).

The checks: the log link reported as a risk difference, `ψ = exp`, gives risk differences `1`
and `2` (`exp_sub_example`), and the logit link reported as a risk difference,
`ψ = sigmoid`, gives `1/6` and `2/15` under the common log odds ratio `log 2`
(`sigmoid_sub_example`).

**The two step estimator.** If `â_n` is consistent for the source regression standardized to the
intermediate covariate law and `d̂_n` is consistent for the effect reported in the intermediate
population against a third arm, then `d̂_n - â_n` is consistent for the effect of the third arm
against the source arm in the intermediate population (`isConsistent_twoStep`). With sample means
of i.i.d. samples every hypothesis on the estimators holds (`isConsistent_twoStep_sampleMean`).

## Main results

* `linkContrast_eq_of_affine`, `linkConditional_eq_of_affine`.
* `affine_of_forall_sub_eq`, `forall_sub_eq_iff_affine`, `exists_sub_ne_of_not_affine`,
  `exists_sub_ne_of_contDiffOn`, `exists_linkConditional_ne_of_not_affine`.
* `exp_sub_example`, `logit_sigmoid`, `sigmoid_sub_example`.
* `isConsistent_twoStep`, `isConsistent_twoStep_sampleMean`.

## References

* E. Bareinboim and J. Pearl, *Causal inference and the data-fusion problem*, Proceedings of the
  National Academy of Sciences 113 (2016).
* D. M. Phillippo, A. E. Ades, S. Dias, S. Palmer, K. R. Abrams and N. J. Welton, *Methods for
  population-adjusted indirect comparisons in health technology appraisal*, Medical Decision
  Making 38 (2018).
-/

@[expose] public section

namespace CausalInference

namespace Transport

open MeasureTheory ProbabilityTheory Set Filter Topology EffectMeasure MissingData PointTreatment

/-! ### The affine direction -/

/-- **An affine reported scale keeps the effect constant.** If `ψ = h ∘ ginv` is affine,
`ψ(η) = k η + l`, on a set `I` of predictor values, and the predictors of the two arms differ by
`γ` and lie in `I`, the reported conditional effect is `k γ`. No regularity is needed. -/
theorem linkContrast_eq_of_affine {X : Type*} {I : Set ℝ} {ginv h : ℝ → ℝ} {k l : ℝ}
    (hψ : ∀ η ∈ I, h (ginv η) = k * η + l) {ηB ηC : X → ℝ} {γ : ℝ} {x : X}
    (hγ : ηB x - ηC x = γ) (hB : ηB x ∈ I) (hC : ηC x ∈ I) :
    linkContrast h (fun y => ginv (ηC y)) (fun y => ginv (ηB y)) x = k * γ := by
  rw [linkContrast, hψ _ hB, hψ _ hC, ← hγ]
  ring

/-- **An affine reported scale is transported.** Under the hypotheses of
`linkContrast_eq_of_affine`, with the predictors almost surely in `I` under a covariate law `P`,
the average conditional effect on the scale `h` is `k γ`, whatever `P`. -/
theorem linkConditional_eq_of_affine {X : Type*} [MeasurableSpace X] {I : Set ℝ}
    {ginv h : ℝ → ℝ} {k l : ℝ} (hψ : ∀ η ∈ I, h (ginv η) = k * η + l) {ηB ηC : X → ℝ} {γ : ℝ}
    (hγ : ∀ x, ηB x - ηC x = γ) (P : Measure X) [IsProbabilityMeasure P]
    (hP : ∀ᵐ x ∂P, ηB x ∈ I ∧ ηC x ∈ I) :
    linkConditional h P (fun y => ginv (ηC y)) (fun y => ginv (ηB y)) = k * γ := by
  rw [linkConditional, integral_congr_ae (g := fun _ => k * γ)
    (hP.mono fun x hx => linkContrast_eq_of_affine hψ (hγ x) hx.1 hx.2)]
  simp

/-! ### The non affine direction -/

/-- **Equal differences for every shift make a differentiable function affine.** If `ψ` is
differentiable on `(a, b)` and `ψ(η₁ + γ) - ψ(η₁) = ψ(η₂ + γ) - ψ(η₂)` whenever the four points
lie in `(a, b)`, then `ψ` is affine on `(a, b)`. -/
theorem affine_of_forall_sub_eq {ψ : ℝ → ℝ} {a b : ℝ} (hψ : DifferentiableOn ℝ ψ (Ioo a b))
    (H : ∀ η₁ η₂ γ, η₁ ∈ Ioo a b → η₁ + γ ∈ Ioo a b → η₂ ∈ Ioo a b → η₂ + γ ∈ Ioo a b →
      ψ (η₁ + γ) - ψ η₁ = ψ (η₂ + γ) - ψ η₂) :
    ∃ k l, ∀ η ∈ Ioo a b, ψ η = k * η + l := by
  by_cases hab : a < b
  swap
  · exact ⟨0, 0, fun η hη => absurd (hη.1.trans hη.2) hab⟩
  have hdiff : ∀ x ∈ Ioo a b, HasDerivAt ψ (deriv ψ x) x := fun x hx =>
    (hψ.differentiableAt (Ioo_mem_nhds hx.1 hx.2)).hasDerivAt
  -- the derivative takes the same value at any two points `p < q`
  have hd : ∀ p ∈ Ioo a b, ∀ q ∈ Ioo a b, p < q → deriv ψ q = deriv ψ p := by
    intro p hp q hq hpq
    set γ := q - p with hγ
    have hq' : p + γ = q := by rw [hγ]; ring
    have hloc : (fun x => ψ (x + γ) - ψ x) =ᶠ[𝓝 p] fun _ => ψ (p + γ) - ψ p := by
      have hmem : Ioo a (b - γ) ∈ 𝓝 p := Ioo_mem_nhds hp.1 (by rw [hγ]; linarith [hq.2])
      filter_upwards [hmem] with x hx
      exact H x p γ ⟨hx.1, by linarith [hx.2]⟩ ⟨by linarith [hx.1], by linarith [hx.2]⟩ hp
        (hq' ▸ hq)
    have hq'' : HasDerivAt ψ (deriv ψ q) (p + γ) := by rw [hq']; exact hdiff q hq
    have hder : HasDerivAt (fun x => ψ (x + γ) - ψ x) (deriv ψ q - deriv ψ p) p :=
      (hq''.comp_add_const p γ).sub (hdiff p hp)
    have h0 : HasDerivAt (fun x => ψ (x + γ) - ψ x) 0 p :=
      (hasDerivAt_const p (ψ (p + γ) - ψ p)).congr_of_eventuallyEq hloc
    linarith [hder.unique h0]
  set m := (a + b) / 2
  have hm : m ∈ Ioo a b := ⟨by simp only [m]; linarith, by simp only [m]; linarith⟩
  set c := deriv ψ m
  have hc : EqOn (deriv ψ) (deriv fun η => c * η) (Ioo a b) := by
    intro x hx
    rw [((hasDerivAt_id' x).const_mul c).deriv, mul_one]
    rcases lt_trichotomy x m with h | h | h
    · exact (hd x hx m hm h).symm
    · rw [h]
    · exact hd m hm x hx h
  obtain ⟨l, hl⟩ := isOpen_Ioo.exists_eq_add_of_deriv_eq isPreconnected_Ioo hψ
    (differentiable_id.const_mul c).differentiableOn hc
  exact ⟨c, l, fun η hη => hl hη⟩

/-- **The characterization.** For `ψ` differentiable on `(a, b)`, the difference
`ψ(η + γ) - ψ(η)` does not depend on `η` (for all points in `(a, b)`) exactly when `ψ` is affine
on `(a, b)`. The direction from affine needs no differentiability. -/
theorem forall_sub_eq_iff_affine {ψ : ℝ → ℝ} {a b : ℝ} (hψ : DifferentiableOn ℝ ψ (Ioo a b)) :
    (∀ η₁ η₂ γ, η₁ ∈ Ioo a b → η₁ + γ ∈ Ioo a b → η₂ ∈ Ioo a b → η₂ + γ ∈ Ioo a b →
      ψ (η₁ + γ) - ψ η₁ = ψ (η₂ + γ) - ψ η₂) ↔ ∃ k l, ∀ η ∈ Ioo a b, ψ η = k * η + l := by
  refine ⟨affine_of_forall_sub_eq hψ, ?_⟩
  rintro ⟨k, l, h⟩ η₁ η₂ γ h1 h1' h2 h2'
  rw [h _ h1, h _ h1', h _ h2, h _ h2']
  ring

/-- **The misaligned case.** If `ψ = h ∘ ginv` is differentiable and not affine on `(a, b)`, there
are predictor values `η₁, η₂` and a shift `γ ≠ 0`, with `η_i, η_i + γ ∈ (a, b)`, at which the
reported effects of the common shift `γ` differ. -/
theorem exists_sub_ne_of_not_affine {ginv h : ℝ → ℝ} {a b : ℝ}
    (hψ : DifferentiableOn ℝ (fun η => h (ginv η)) (Ioo a b))
    (hna : ¬ ∃ k l, ∀ η ∈ Ioo a b, h (ginv η) = k * η + l) :
    ∃ η₁ η₂ γ, γ ≠ 0 ∧ η₁ ∈ Ioo a b ∧ η₁ + γ ∈ Ioo a b ∧ η₂ ∈ Ioo a b ∧ η₂ + γ ∈ Ioo a b ∧
      h (ginv (η₁ + γ)) - h (ginv η₁) ≠ h (ginv (η₂ + γ)) - h (ginv η₂) := by
  by_contra hne
  refine hna (affine_of_forall_sub_eq hψ fun η₁ η₂ γ h1 h1' h2 h2' => ?_)
  by_contra hneq
  refine hne ⟨η₁, η₂, γ, fun hγ => hneq ?_, h1, h1', h2, h2', hneq⟩
  subst hγ
  simp

/-- The misaligned case for `ψ = h ∘ ginv` twice continuously differentiable on `(a, b)`. -/
theorem exists_sub_ne_of_contDiffOn {ginv h : ℝ → ℝ} {a b : ℝ}
    (hψ : ContDiffOn ℝ 2 (fun η => h (ginv η)) (Ioo a b))
    (hna : ¬ ∃ k l, ∀ η ∈ Ioo a b, h (ginv η) = k * η + l) :
    ∃ η₁ η₂ γ, γ ≠ 0 ∧ η₁ ∈ Ioo a b ∧ η₁ + γ ∈ Ioo a b ∧ η₂ ∈ Ioo a b ∧ η₂ + γ ∈ Ioo a b ∧
      h (ginv (η₁ + γ)) - h (ginv η₁) ≠ h (ginv (η₂ + γ)) - h (ginv η₂) :=
  exists_sub_ne_of_not_affine (hψ.differentiableOn (by norm_num)) hna

/-- **A misaligned scale is not transported.** If `ψ = h ∘ ginv` is differentiable and not affine
on `(a, b)`, there are predictors `η_C, η_B = η_C + γ` on two strata, with values in `(a, b)` and a
common effect `γ ≠ 0` on the `g` scale, such that the average conditional effect on the scale `h`
differs between the point mass at the stratum `false` and the point mass at the stratum
`true`. -/
theorem exists_linkConditional_ne_of_not_affine {ginv h : ℝ → ℝ} {a b : ℝ}
    (hψ : DifferentiableOn ℝ (fun η => h (ginv η)) (Ioo a b))
    (hna : ¬ ∃ k l, ∀ η ∈ Ioo a b, h (ginv η) = k * η + l) :
    ∃ (ηC : Bool → ℝ) (γ : ℝ), γ ≠ 0 ∧ (∀ x, ηC x ∈ Ioo a b ∧ ηC x + γ ∈ Ioo a b) ∧
      linkConditional h (Measure.dirac false) (fun x => ginv (ηC x))
          (fun x => ginv (ηC x + γ)) ≠
        linkConditional h (Measure.dirac true) (fun x => ginv (ηC x))
          (fun x => ginv (ηC x + γ)) := by
  obtain ⟨η₁, η₂, γ, hγ, h1, h1', h2, h2', hne⟩ := exists_sub_ne_of_not_affine hψ hna
  refine ⟨fun x => if x then η₂ else η₁, γ, hγ, fun x => ?_, ?_⟩
  · cases x
    · exact ⟨h1, h1'⟩
    · exact ⟨h2, h2'⟩
  · simpa [linkConditional, linkContrast] using hne

/-! ### The checks -/

theorem log_two_mem_Ioo : Real.log 2 ∈ Ioo (0 : ℝ) 1 :=
  ⟨by linarith [Real.log_two_gt_d9], by linarith [Real.log_two_lt_d9]⟩

/-- **The log link reported as a risk difference.** For `g = log`, `ginv = exp`, `h = id`,
`ψ = exp` is not affine on `(-1, 2)`, and with `η₁ = 0`, `η₂ = log 2` and the common log risk
ratio `γ = log 2`, the risk differences are `1` and `2`. -/
theorem exp_sub_example :
    ¬ (∃ k l, ∀ η ∈ Ioo (-1 : ℝ) 2, id (Real.exp η) = k * η + l) ∧
    id (Real.exp (0 + Real.log 2)) - id (Real.exp 0) = 1 ∧
    id (Real.exp (Real.log 2 + Real.log 2)) - id (Real.exp (Real.log 2)) = 2 := by
  have h1 : Real.exp (0 + Real.log 2) - Real.exp 0 = 1 := by
    rw [zero_add, Real.exp_log (by norm_num), Real.exp_zero]; norm_num
  have h2 : Real.exp (Real.log 2 + Real.log 2) - Real.exp (Real.log 2) = 2 := by
    rw [Real.exp_add, Real.exp_log (by norm_num)]; norm_num
  have hl := log_two_mem_Ioo
  refine ⟨fun haff => ?_, h1, h2⟩
  have := (forall_sub_eq_iff_affine (Real.differentiable_exp.differentiableOn.comp
    differentiableOn_id (mapsTo_univ _ _))).2 haff 0 (Real.log 2) (Real.log 2)
    ⟨by norm_num, by norm_num⟩ ⟨by linarith [hl.1], by linarith [hl.2]⟩
    ⟨by linarith [hl.1], by linarith [hl.2]⟩ ⟨by linarith [hl.1], by linarith [hl.2]⟩
  simp only [id, Function.comp_apply] at this
  linarith

/-- The sigmoid inverts the logit: `logit (sigmoid η) = η`. -/
theorem logit_sigmoid (η : ℝ) : logit (Real.sigmoid η) = η := by
  have h1 : 1 - Real.sigmoid η = Real.sigmoid η * Real.exp (-η) := by
    rw [Real.sigmoid_mul_rexp_neg, Real.sigmoid_neg]
  rw [logit, odds, h1, div_mul_cancel_left₀ (Real.sigmoid_pos η).ne', Real.exp_neg, inv_inv,
    Real.log_exp]

theorem sigmoid_log_two : Real.sigmoid (Real.log 2) = 2 / 3 := by
  rw [Real.sigmoid_def, Real.exp_neg, Real.exp_log (by norm_num)]; norm_num

theorem sigmoid_two_log_two : Real.sigmoid (Real.log 2 + Real.log 2) = 4 / 5 := by
  rw [Real.sigmoid_def, Real.exp_neg, Real.exp_add, Real.exp_log (by norm_num)]; norm_num

/-- **The logit link reported as a risk difference.** For `g = logit`, `ginv = sigmoid`
(`logit_sigmoid`), `h = id`, `ψ = sigmoid` is not affine on `(-1, 2)`, and with `η₁ = 0`,
`η₂ = log 2` and the common log odds ratio `γ = log 2`, the risk differences are
`2/3 - 1/2 = 1/6` and `4/5 - 2/3 = 2/15`. -/
theorem sigmoid_sub_example :
    ¬ (∃ k l, ∀ η ∈ Ioo (-1 : ℝ) 2, id (Real.sigmoid η) = k * η + l) ∧
    id (Real.sigmoid (0 + Real.log 2)) - id (Real.sigmoid 0) = 1 / 6 ∧
    id (Real.sigmoid (Real.log 2 + Real.log 2)) - id (Real.sigmoid (Real.log 2)) = 2 / 15 := by
  have h1 : Real.sigmoid (0 + Real.log 2) - Real.sigmoid 0 = 1 / 6 := by
    rw [zero_add, sigmoid_log_two, Real.sigmoid_zero]; norm_num
  have h2 : Real.sigmoid (Real.log 2 + Real.log 2) - Real.sigmoid (Real.log 2) = 2 / 15 := by
    rw [sigmoid_two_log_two, sigmoid_log_two]; norm_num
  have hl := log_two_mem_Ioo
  have hdiff : DifferentiableOn ℝ (fun η => id (Real.sigmoid η)) (Ioo (-1 : ℝ) 2) :=
    fun x _ => (Real.hasDerivAt_sigmoid x).differentiableAt.differentiableWithinAt
  refine ⟨fun haff => ?_, h1, h2⟩
  have := (forall_sub_eq_iff_affine hdiff).2 haff 0 (Real.log 2) (Real.log 2)
    ⟨by norm_num, by norm_num⟩ ⟨by linarith [hl.1], by linarith [hl.2]⟩
    ⟨by linarith [hl.1], by linarith [hl.2]⟩ ⟨by linarith [hl.1], by linarith [hl.2]⟩
  simp only [id] at this
  linarith

/-! ### Consistency of the two step estimator -/

section TwoStep

variable {Ω₁ Ω₂ 𝒳 : Type*} {mΩ₁ : MeasurableSpace Ω₁} {mΩ₂ : MeasurableSpace Ω₂}
  [MeasurableSpace 𝒳] {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} [IsFiniteMeasure μ₁]
  [IsFiniteMeasure μ₂] {X₁ : Ω₁ → 𝒳} {X₂ : Ω₂ → 𝒳} {A : Ω₁ → Bool} {Y₁ : Bool → Ω₁ → ℝ}
  {Y₂ : Bool → Ω₂ → ℝ} {e : 𝒳 → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **The two step estimator is consistent.** Under the hypotheses of
`sub_linkMarginal_regression_eq` (the transport g-formula for both source arms, and an
intermediate population reporting `d = g(m_C) - g(E₂[Y₂(false)])` against a third arm), let
`aHat` be consistent for the source regression standardized to the intermediate covariate law,
`linkMarginal g P*_X (m 0) (m 1)`, and `dHat` consistent for `d`, both under the sampling law
`P`. Then `dHat - aHat` is consistent for the effect `g(m_C) - g(E₂[Y₂(true)])` of the third arm
against the source arm in the intermediate population. -/
theorem isConsistent_twoStep (g : ℝ → ℝ) (hX₁ : Measurable X₁) (hX₂ : Measurable X₂)
    (hA : Measurable A) (hY : ∀ b, Measurable (Y₁ b)) (hYi : ∀ b, Integrable (Y₁ b) μ₁)
    (hY₂ : ∀ b, Integrable (Y₂ b) μ₂) (hign : IndicatorIgnorable μ₁ A X₁ Y₁)
    (hps : IsPropensityScore μ₁ A X₁ e) (hpos : ∀ b, ∀ᵐ ω ∂μ₁, 0 < armProb e b (X₁ ω))
    {m : Bool → 𝒳 → ℝ} (hreg : IsOutcomeRegression μ₁ A X₁ (obsOutcome A Y₁) m)
    {gc : Bool → 𝒳 → ℝ} (hcom : ∀ b, IsCommonRegression μ₁ X₁ (Y₁ b) μ₂ X₂ (Y₂ b) (gc b))
    (hov : μ₂.map X₂ ≪ μ₁.map X₁) {mC : ℝ} {aHat dHat : ℕ → Ω → ℝ}
    (ha : IsConsistent aHat (linkMarginal g (μ₂.map X₂) (m false) (m true)) P)
    (hd : IsConsistent dHat (g mC - g (∫ ω, Y₂ false ω ∂μ₂)) P) :
    IsConsistent (fun n ω => dHat n ω - aHat n ω) (g mC - g (∫ ω, Y₂ true ω ∂μ₂)) P := by
  have h := (sub_linkMarginal_regression_eq g hX₁ hX₂ hA hY hYi hY₂ hign hps hpos hreg hcom hov
    (mC := mC) rfl).2
  rw [← h]
  exact hd.sub ha

/-- **The two step estimator from sample means.** Let `O` be an i.i.d. sample of covariate values
whose law is the intermediate covariate law `P*_X`, and `Z` an i.i.d. sample of integrable
reported differences with mean `m_C - E₂[Y₂(false)]`. On the risk difference scale `g = id`,
with the source regressions `m 0`, `m 1` integrable under `P*_X`, the difference of the sample
means of `Z` and of `m 1(O) - m 0(O)` is consistent for `m_C - E₂[Y₂(true)]`. -/
theorem isConsistent_twoStep_sampleMean [IsProbabilityMeasure P] (hX₁ : Measurable X₁)
    (hX₂ : Measurable X₂) (hA : Measurable A) (hY : ∀ b, Measurable (Y₁ b))
    (hYi : ∀ b, Integrable (Y₁ b) μ₁) (hY₂ : ∀ b, Integrable (Y₂ b) μ₂)
    (hign : IndicatorIgnorable μ₁ A X₁ Y₁) (hps : IsPropensityScore μ₁ A X₁ e)
    (hpos : ∀ b, ∀ᵐ ω ∂μ₁, 0 < armProb e b (X₁ ω))
    {m : Bool → 𝒳 → ℝ} (hreg : IsOutcomeRegression μ₁ A X₁ (obsOutcome A Y₁) m)
    {gc : Bool → 𝒳 → ℝ} (hcom : ∀ b, IsCommonRegression μ₁ X₁ (Y₁ b) μ₂ X₂ (Y₂ b) (gc b))
    (hov : μ₂.map X₂ ≪ μ₁.map X₁) (hmi : ∀ b, Integrable (m b) (μ₂.map X₂))
    {O : ℕ → Ω → 𝒳} (hO : IsIIDSample O P) (hlaw : P.map (O 0) = μ₂.map X₂)
    {Z : ℕ → Ω → ℝ} (hZ : IsIIDSample Z P) (hZi : Integrable (Z 0) P) {mC : ℝ}
    (hZm : ∫ ω, Z 0 ω ∂P = mC - ∫ ω, Y₂ false ω ∂μ₂) :
    IsConsistent (fun n ω => sampleMean id Z n ω - sampleMean (fun x => m true x - m false x) O n ω)
      (mC - ∫ ω, Y₂ true ω ∂μ₂) P := by
  have hm : ∀ b, Measurable (m b) := hreg.1
  have hO0 : AEMeasurable (O 0) P := hO.aemeasurable 0
  have hfi : Integrable (fun ω => m true (O 0 ω) - m false (O 0 ω)) P := by
    have h1 : Integrable (fun x => m true x - m false x) (P.map (O 0)) := by
      rw [hlaw]; exact (hmi true).sub (hmi false)
    exact h1.comp_aemeasurable hO0
  have ha := sampleMean_isConsistent hO ((hm true).sub (hm false)) hfi
  have hint : ∫ ω, m true (O 0 ω) - m false (O 0 ω) ∂P =
      linkMarginal id (μ₂.map X₂) (m false) (m true) := by
    rw [← integral_map (f := fun x => m true x - m false x) hO0
      ((hm true).sub (hm false)).aestronglyMeasurable, hlaw, linkMarginal,
      integral_sub (hmi true) (hmi false)]
    rfl
  have hd := sampleMean_isConsistent hZ measurable_id hZi
  simp only [id] at hd
  rw [hZm] at hd
  exact isConsistent_twoStep id hX₁ hX₂ hA hY hYi hY₂ hign hps hpos hreg hcom hov
    (by convert ha using 1; exact hint.symm) hd

end TwoStep

end Transport

end CausalInference
