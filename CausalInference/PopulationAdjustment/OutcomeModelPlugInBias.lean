/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.OutcomeModelLinear
public import CausalInference.Measures.LinkJensen
public import CausalInference.Estimation.ConvergenceInProbability
public import Mathlib.Analysis.Calculus.Taylor

/-!
# The bias of the plug-in at the mean covariates

An outcome model on the link `g` with inverse `g⁻¹` has arm means `m_t = g⁻¹ ∘ η_t` with the
linear predictor `η_t = interactionPredictor α γ β₁ β₂ t`. Evaluating the fitted model at the
mean covariates `x̄` of the target gives the plug-in `plugInEffect g ν m_false m_true`; the
estimand is the marginal effect `linkMarginal g ν m_false m_true`.

* **What the plug-in estimates** (`tendstoInMeasure_plugIn`): if the fitted relative effect,
  interactions and mean covariates converge in probability, the plug-in converges in probability
  to `γ + x̄ᵀβ₂`, the conditional effect at the mean covariates, whatever the fitted prognostic
  effects; that is the marginal effect only when the bias below is zero.
* **The second order Taylor form** (`exists_eq_taylor_two_lagrange`): for `g⁻¹` twice
  continuously differentiable on an open interval,
  `g⁻¹(a) = g⁻¹(b) + (g⁻¹)'(b)(a - b) + ½(a - b)²(g⁻¹)''(ξ)` with `ξ` between `a` and `b`.
* **The Jensen gap in Lagrange form** (`exists_integral_sub_eq_lagrange`): for an integrable
  predictor `η` with mean `η̄`, `E[g⁻¹(η)] - g⁻¹(η̄) = ½ E[(η - η̄)² (g⁻¹)''(ξ)]` with `ξ`
  between `η` and `η̄`, and the remainder integrand is integrable.
* **When it is nonzero** (`integral_comp_ne_of_iteratedDeriv_pos`,
  `integral_comp_ne_of_iteratedDeriv_neg`): if `(g⁻¹)''` is positive (negative) on the interval
  and the predictor is not almost surely constant, the gap is positive (negative). This is
  Jensen's inequality (`averagingGap_neg_of_strictConvexOn`) with strict convexity from the
  curvature.
* **The arm level gap** (`arm_linkGap_eq_averagingGap`, `arm_linkGap_eq_zero_iff`,
  `arm_gap_eq_lagrange`, `arm_gap_ne_zero`): on the link scale the gap of arm `t` is
  `g(∫ m_t dν) - η_t(x̄)`, the averaging gap `J_g(m_t)` (`averagingGap`); it vanishes
  exactly when the response scale gap `∫ m_t dν - m_t(x̄)` does, for a link injective on a set
  containing both means; the response gap is
  `½ ∫ ((x - x̄)ᵀ(β₁ + 1{t}β₂))² (g⁻¹)''(ξ_x) dν`.
* **The contrast bias** (`plugInEffect_sub_linkMarginal`): the plug-in minus the marginal effect
  is `J_g(m_false) - J_g(m_true)`, and the plug-in is the average conditional effect. On the
  identity link it is zero (`plugInEffect_sub_linkMarginal_id`); on the logit link it is
  nonzero (`outcomeModel_logit_plugIn_bias`).

## Main results

* `tendstoInMeasure_plugIn`.
* `exists_eq_taylor_two_lagrange`, `exists_integral_sub_eq_lagrange`,
  `integral_comp_ne_of_iteratedDeriv_pos`, `integral_comp_ne_of_iteratedDeriv_neg`.
* `arm_linkGap_eq_averagingGap`, `arm_linkGap_eq_zero_iff`, `arm_gap_eq_lagrange`,
  `arm_gap_ne_zero`.
* `plugInEffect_sub_linkMarginal`, `plugInEffect_sub_linkMarginal_id`.

## References

* D. M. Phillippo, A. E. Ades, S. Dias, S. Palmer, K. R. Abrams and N. J. Welton, *Methods for
  population-adjusted indirect comparisons in health technology appraisal*, Medical Decision
  Making 38 (2018).
* J. L. W. V. Jensen, *Sur les fonctions convexes et les inégalités entre les valeurs
  moyennes*, Acta Mathematica 30 (1906).
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open MeasureTheory ProbabilityTheory Filter Topology EffectMeasure IndirectComparison

/-! ### Taylor and Jensen forms -/

section Taylor

/-- **Second order Taylor expansion with the Lagrange remainder.** If `φ` is twice continuously
differentiable on an open interval `U` and `a, b ∈ U`, there is `ξ` between `a` and `b` with
`φ(a) = φ(b) + φ'(b)(a - b) + ½(a - b)² φ''(ξ)`. -/
theorem exists_eq_taylor_two_lagrange {φ : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hUc : U.OrdConnected) (hφ : ContDiffOn ℝ 2 φ U) {a b : ℝ} (ha : a ∈ U) (hb : b ∈ U) :
    ∃ ξ ∈ Set.uIcc a b,
      φ a = φ b + deriv φ b * (a - b) + 1 / 2 * (a - b) ^ 2 * iteratedDeriv 2 φ ξ := by
  by_cases hab : b = a
  · subst hab
    exact ⟨b, Set.left_mem_uIcc, by ring⟩
  have hsub : Set.uIcc b a ⊆ U := hUc.uIcc_subset hb ha
  have hcd : ContDiffOn ℝ ((1 : ℕ) + 1) φ (Set.uIcc b a) :=
    (hφ.mono hsub).of_le (by norm_num)
  obtain ⟨ξ, hξ, h⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hab hcd
  have ht := taylorWithinEval_succ φ 0 (Set.uIcc b a) b a
  simp only [Nat.cast_zero, zero_add, Nat.factorial_zero, Nat.cast_one, mul_one, inv_one,
    one_mul, pow_one, smul_eq_mul, iteratedDerivWithin_one, taylor_within_zero_eval] at ht
  have hd : DifferentiableAt ℝ φ b :=
    (hφ.contDiffAt (hU.mem_nhds hb)).differentiableAt (by norm_num)
  rw [hd.derivWithin (uniqueDiffOn_uIcc hab b Set.left_mem_uIcc)] at ht
  rw [ht, show (1 : ℕ) + 1 = 2 from rfl, Nat.factorial_two, Nat.cast_ofNat] at h
  refine ⟨ξ, ?_, by linear_combination h⟩
  rw [Set.uIcc_comm]
  exact Set.uIoo_subset_uIcc_self hξ

variable {𝒳 : Type*} [MeasurableSpace 𝒳] {ν : Measure 𝒳} [IsProbabilityMeasure ν]

/-- **The Jensen gap in Lagrange form.** Let `φ` be twice continuously differentiable on an open
interval `U`, and let `η` be integrable under the probability law `ν` with mean `η̄ ∈ U` and
values almost surely in `U`, with `φ ∘ η` integrable. Then there is `ξ` with `ξ(x)` between `η(x)`
and `η̄` almost surely, the pointwise expansion
`φ(η(x)) = φ(η̄) + φ'(η̄)(η(x) - η̄) + ½(η(x) - η̄)² φ''(ξ(x))` holds almost surely, the remainder
integrand `(η - η̄)² φ''(ξ)` is integrable, and
`∫ φ ∘ η dν - φ(η̄) = ½ ∫ (η - η̄)² φ''(ξ) dν`. -/
theorem exists_integral_sub_eq_lagrange {φ : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hUc : U.OrdConnected) (hφ : ContDiffOn ℝ 2 φ U) {η : 𝒳 → ℝ} (hηi : Integrable η ν)
    (hηU : ∀ᵐ x ∂ν, η x ∈ U) (hmU : ∫ x, η x ∂ν ∈ U) (hφi : Integrable (fun x => φ (η x)) ν) :
    ∃ ξ : 𝒳 → ℝ, (∀ᵐ x ∂ν, ξ x ∈ Set.uIcc (η x) (∫ y, η y ∂ν)) ∧
      (∀ᵐ x ∂ν, φ (η x) = φ (∫ y, η y ∂ν) + deriv φ (∫ y, η y ∂ν) * (η x - ∫ y, η y ∂ν) +
        1 / 2 * (η x - ∫ y, η y ∂ν) ^ 2 * iteratedDeriv 2 φ (ξ x)) ∧
      Integrable (fun x => (η x - ∫ y, η y ∂ν) ^ 2 * iteratedDeriv 2 φ (ξ x)) ν ∧
      ∫ x, φ (η x) ∂ν - φ (∫ y, η y ∂ν) =
        1 / 2 * ∫ x, (η x - ∫ y, η y ∂ν) ^ 2 * iteratedDeriv 2 φ (ξ x) ∂ν := by
  set m := ∫ y, η y ∂ν
  have hT : ∀ x, η x ∈ U → ∃ ξ ∈ Set.uIcc (η x) m,
      φ (η x) = φ m + deriv φ m * (η x - m) + 1 / 2 * (η x - m) ^ 2 * iteratedDeriv 2 φ ξ :=
    fun x hx => exists_eq_taylor_two_lagrange hU hUc hφ hx hmU
  classical
  let ξ : 𝒳 → ℝ := fun x => if hx : η x ∈ U then (hT x hx).choose else m
  have hξ : ∀ x, η x ∈ U → ξ x ∈ Set.uIcc (η x) m ∧
      φ (η x) = φ m + deriv φ m * (η x - m) + 1 / 2 * (η x - m) ^ 2 * iteratedDeriv 2 φ (ξ x) :=
    fun x hx => by simp only [ξ, hx, ↓reduceDIte]; exact (hT x hx).choose_spec
  have hR : (fun x => 2 * (φ (η x) - φ m - deriv φ m * (η x - m))) =ᵐ[ν]
      fun x => (η x - m) ^ 2 * iteratedDeriv 2 φ (ξ x) := by
    filter_upwards [hηU] with x hx
    rw [(hξ x hx).2]
    ring
  have i₁ : Integrable (fun x => φ (η x) - φ m) ν := hφi.sub (integrable_const _)
  have i₂ : Integrable (fun x => deriv φ m * (η x - m)) ν :=
    (hηi.sub (integrable_const _)).const_mul _
  have i₃ : Integrable (fun x => 2 * (φ (η x) - φ m - deriv φ m * (η x - m))) ν :=
    ((i₁.sub i₂).const_mul 2).congr (ae_of_all _ fun x => by simp only [Pi.sub_apply])
  have hRi : Integrable (fun x => (η x - m) ^ 2 * iteratedDeriv 2 φ (ξ x)) ν := i₃.congr hR
  refine ⟨ξ, hηU.mono fun x hx => (hξ x hx).1, hηU.mono fun x hx => (hξ x hx).2, hRi, ?_⟩
  rw [← integral_congr_ae hR, integral_const_mul, integral_sub i₁ i₂,
    integral_sub hφi (integrable_const _), integral_const_mul,
    integral_sub hηi (integrable_const _)]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  ring

/-- **The Jensen gap is positive for a positive curvature**: if `φ` is continuous on the
interval `U` with `φ'' > 0` on `U`, and the integrable `η` with values almost surely in `U` and
`φ ∘ η` integrable is not almost surely constant, then `φ(∫ η dν) < ∫ φ ∘ η dν`. -/
theorem integral_comp_ne_of_iteratedDeriv_pos {φ : ℝ → ℝ} {U : Set ℝ} (hUc : U.OrdConnected)
    (hφ : ContinuousOn φ U) (hpos : ∀ s ∈ U, 0 < iteratedDeriv 2 φ s) {η : 𝒳 → ℝ}
    (hηi : Integrable η ν) (hηU : ∀ᵐ x ∂ν, η x ∈ U) (hφi : Integrable (fun x => φ (η x)) ν)
    (hnd : IsPrognostic ν η) : φ (∫ x, η x ∂ν) < ∫ x, φ (η x) ∂ν := by
  have hsc : StrictConvexOn ℝ U φ := strictConvexOn_of_deriv2_pos hUc.convex hφ fun s hs => by
    rw [← iteratedDeriv_eq_iterate]; exact hpos s (interior_subset hs)
  have := averagingGap_neg_of_strictConvexOn hsc hηi hηU hφi hnd
  rw [averagingGap] at this
  linarith

/-- **The Jensen gap is negative for a negative curvature**: as
`integral_comp_ne_of_iteratedDeriv_pos` with `φ'' < 0` on `U`,
`∫ φ ∘ η dν < φ(∫ η dν)`. -/
theorem integral_comp_ne_of_iteratedDeriv_neg {φ : ℝ → ℝ} {U : Set ℝ} (hUc : U.OrdConnected)
    (hφ : ContinuousOn φ U) (hneg : ∀ s ∈ U, iteratedDeriv 2 φ s < 0) {η : 𝒳 → ℝ}
    (hηi : Integrable η ν) (hηU : ∀ᵐ x ∂ν, η x ∈ U) (hφi : Integrable (fun x => φ (η x)) ν)
    (hnd : IsPrognostic ν η) : ∫ x, φ (η x) ∂ν < φ (∫ x, η x ∂ν) := by
  have hsc : StrictConcaveOn ℝ U φ := strictConcaveOn_of_deriv2_neg hUc.convex hφ fun s hs => by
    rw [← iteratedDeriv_eq_iterate]; exact hneg s (interior_subset hs)
  have := averagingGap_pos_of_strictConcaveOn hsc hηi hηU hφi hnd
  rw [averagingGap] at this
  linarith

end Taylor

/-! ### The arm level gap of the outcome model -/

section Arm

variable {p : ℕ} {ν : Measure (Fin p → ℝ)} [IsProbabilityMeasure ν] {g ginv : ℝ → ℝ}

/-- **The link scale gap of an arm is its averaging gap.** If `g(g⁻¹(s)) = s` for every `s` and
the covariates have integrable coordinates under `ν`, then for `m_t = g⁻¹ ∘ η_t` the link scale
gap `g(∫ m_t dν) - η_t(x̄)` between the marginal link position and the linear predictor at the
mean covariates is the averaging gap `J_g(m_t) = g(∫ m_t dν) - ∫ g ∘ m_t dν`. -/
theorem arm_linkGap_eq_averagingGap (hg : ∀ s, g (ginv s) = s)
    (hν : ∀ k, Integrable (fun x : Fin p → ℝ => x k) ν) (α γ : ℝ) (β₁ β₂ : Fin p → ℝ)
    (t : Bool) :
    g (∫ x, ginv (interactionPredictor α γ β₁ β₂ t x) ∂ν) -
        interactionPredictor α γ β₁ β₂ t (covMean ν) =
      averagingGap g ν fun x => ginv (interactionPredictor α γ β₁ β₂ t x) := by
  simp only [averagingGap, hg, integral_interactionPredictor hν]

omit [IsProbabilityMeasure ν] in
/-- **The link scale gap vanishes exactly when the response scale gap does**, for a link that is
injective on a set `D` containing the marginal mean `∫ m_t dν` and the plug-in mean `m_t(x̄)`. -/
theorem arm_linkGap_eq_zero_iff (hg : ∀ s, g (ginv s) = s) {D : Set ℝ} (hinj : Set.InjOn g D)
    (α γ : ℝ) (β₁ β₂ : Fin p → ℝ) (t : Bool)
    (hD : ∫ x, ginv (interactionPredictor α γ β₁ β₂ t x) ∂ν ∈ D)
    (hD' : ginv (interactionPredictor α γ β₁ β₂ t (covMean ν)) ∈ D) :
    g (∫ x, ginv (interactionPredictor α γ β₁ β₂ t x) ∂ν) -
          interactionPredictor α γ β₁ β₂ t (covMean ν) = 0 ↔
      ∫ x, ginv (interactionPredictor α γ β₁ β₂ t x) ∂ν -
          ginv (interactionPredictor α γ β₁ β₂ t (covMean ν)) = 0 := by
  have h := hinj.eq_iff hD hD'
  rw [hg] at h
  rw [sub_eq_zero, sub_eq_zero]
  exact h

/-- **The arm level gap in Lagrange form.** Let `g⁻¹` be twice continuously differentiable on an
open interval `U` containing the predictor of arm `t` almost surely and at the mean covariates,
the covariates have integrable coordinates and `m_t = g⁻¹ ∘ η_t` be integrable under `ν`. Then
there is `ξ` with `ξ(x)` between `η_t(x)` and `η_t(x̄)` almost surely, the remainder integrand is
integrable, and
`∫ m_t dν - m_t(x̄) = ½ ∫ ((x - x̄)ᵀ(β₁ + 1{t}β₂))² (g⁻¹)''(ξ(x)) dν`. -/
theorem arm_gap_eq_lagrange {U : Set ℝ} (hU : IsOpen U) (hUc : U.OrdConnected)
    (hginv : ContDiffOn ℝ 2 ginv U) (hν : ∀ k, Integrable (fun x : Fin p → ℝ => x k) ν)
    (α γ : ℝ) (β₁ β₂ : Fin p → ℝ) (t : Bool)
    (hηU : ∀ᵐ x ∂ν, interactionPredictor α γ β₁ β₂ t x ∈ U)
    (hmU : interactionPredictor α γ β₁ β₂ t (covMean ν) ∈ U)
    (hmi : Integrable (fun x => ginv (interactionPredictor α γ β₁ β₂ t x)) ν) :
    ∃ ξ : (Fin p → ℝ) → ℝ,
      (∀ᵐ x ∂ν, ξ x ∈ Set.uIcc (interactionPredictor α γ β₁ β₂ t x)
        (interactionPredictor α γ β₁ β₂ t (covMean ν))) ∧
      Integrable (fun x => (∑ j, (x j - covMean ν j) * interactionSlope β₁ β₂ t j) ^ 2 *
        iteratedDeriv 2 ginv (ξ x)) ν ∧
      ∫ x, ginv (interactionPredictor α γ β₁ β₂ t x) ∂ν -
          ginv (interactionPredictor α γ β₁ β₂ t (covMean ν)) =
        1 / 2 * ∫ x, (∑ j, (x j - covMean ν j) * interactionSlope β₁ β₂ t j) ^ 2 *
          iteratedDeriv 2 ginv (ξ x) ∂ν := by
  have hmean := integral_interactionPredictor hν α γ β₁ β₂ t
  obtain ⟨ξ, hξ, -, hRi, hgap⟩ := exists_integral_sub_eq_lagrange hU hUc hginv
    (integrable_interactionPredictor hν α γ β₁ β₂ t) hηU (hmean ▸ hmU) hmi
  simp only [hmean, interactionPredictor_sub_interactionPredictor] at hξ hRi hgap
  exact ⟨ξ, hξ, hRi, hgap⟩

/-- **The arm level gap is nonzero for a curved inverse link and a prognostic predictor.** If
`g⁻¹` is continuous on the interval `U` with `(g⁻¹)''` of one strict sign on `U`, the predictor
of arm `t` lies almost surely in `U` and is not almost surely constant (the covariates are
prognostic for the arm), the covariates have integrable coordinates and `m_t` is integrable,
then the response scale gap `∫ m_t dν - m_t(x̄)` is nonzero; if moreover `g(g⁻¹(s)) = s` and `g`
is injective on a set containing both means, the link scale gap is nonzero. -/
theorem arm_gap_ne_zero {U : Set ℝ} (hUc : U.OrdConnected) (hginv : ContinuousOn ginv U)
    (hsign : (∀ s ∈ U, 0 < iteratedDeriv 2 ginv s) ∨ (∀ s ∈ U, iteratedDeriv 2 ginv s < 0))
    (hν : ∀ k, Integrable (fun x : Fin p → ℝ => x k) ν) (α γ : ℝ) (β₁ β₂ : Fin p → ℝ)
    (t : Bool) (hηU : ∀ᵐ x ∂ν, interactionPredictor α γ β₁ β₂ t x ∈ U)
    (hmi : Integrable (fun x => ginv (interactionPredictor α γ β₁ β₂ t x)) ν)
    (hnd : IsPrognostic ν (interactionPredictor α γ β₁ β₂ t)) :
    ∫ x, ginv (interactionPredictor α γ β₁ β₂ t x) ∂ν -
        ginv (interactionPredictor α γ β₁ β₂ t (covMean ν)) ≠ 0 ∧
      ((∀ s, g (ginv s) = s) → ∀ {D : Set ℝ}, Set.InjOn g D →
        ∫ x, ginv (interactionPredictor α γ β₁ β₂ t x) ∂ν ∈ D →
        ginv (interactionPredictor α γ β₁ β₂ t (covMean ν)) ∈ D →
        g (∫ x, ginv (interactionPredictor α γ β₁ β₂ t x) ∂ν) -
          interactionPredictor α γ β₁ β₂ t (covMean ν) ≠ 0) := by
  have hηi := integrable_interactionPredictor hν α γ β₁ β₂ t
  have hmean := integral_interactionPredictor hν α γ β₁ β₂ t
  have hne : ∫ x, ginv (interactionPredictor α γ β₁ β₂ t x) ∂ν -
      ginv (interactionPredictor α γ β₁ β₂ t (covMean ν)) ≠ 0 := by
    rw [← hmean]
    rcases hsign with h | h
    · have := integral_comp_ne_of_iteratedDeriv_pos hUc hginv h hηi hηU hmi hnd
      linarith
    · have := integral_comp_ne_of_iteratedDeriv_neg hUc hginv h hηi hηU hmi hnd
      linarith
  exact ⟨hne, fun hg D hinj hD hD' h0 =>
    hne ((arm_linkGap_eq_zero_iff hg hinj α γ β₁ β₂ t hD hD').1 h0)⟩

end Arm

/-! ### The contrast bias of the plug-in -/

section Contrast

variable {p : ℕ} {ν : Measure (Fin p → ℝ)} [IsProbabilityMeasure ν]

/-- **The bias of the plug-in at the mean covariates.** Let the arm means satisfy
`g(m_t(x)) = η_t(x)` at every covariate value, with integrable arm means and integrable
covariate coordinates under the probability law `ν`. Then the plug-in is the average
conditional effect, and the plug-in minus the marginal effect is the difference of the averaging
gaps of the reference and the active arm:
`plugInEffect - linkMarginal = J_g(m_false) - J_g(m_true)`. -/
theorem plugInEffect_sub_linkMarginal (hν : ∀ k, Integrable (fun x : Fin p → ℝ => x k) ν)
    {g : ℝ → ℝ} {m : Bool → (Fin p → ℝ) → ℝ} {α γ : ℝ} {β₁ β₂ : Fin p → ℝ}
    (hm : ∀ t x, g (m t x) = interactionPredictor α γ β₁ β₂ t x)
    (hmi : ∀ t, Integrable (m t) ν) :
    plugInEffect g ν (m false) (m true) = linkConditional g ν (m false) (m true) ∧
      plugInEffect g ν (m false) (m true) - linkMarginal g ν (m false) (m true) =
        averagingGap g ν (m false) - averagingGap g ν (m true) := by
  have hc := (linkConditional_eq_plugInEffect_interactionPredictor hν hm).1
  have hgi : ∀ t, Integrable (fun x => g (m t x)) ν := fun t => by
    simp only [hm]; exact integrable_interactionPredictor hν α γ β₁ β₂ t
  have h := linkMarginal_sub_linkConditional (hmi false) (hmi true) (hgi false) (hgi true)
  refine ⟨hc.symm, ?_⟩
  rw [← hc]
  linarith

/-- **No bias on the identity link**: for the linear model with interactions, the plug-in at the
mean covariates equals the marginal effect. -/
theorem plugInEffect_sub_linkMarginal_id (hν : ∀ k, Integrable (fun x : Fin p → ℝ => x k) ν)
    (α γ : ℝ) (β₁ β₂ : Fin p → ℝ) :
    plugInEffect id ν (interactionPredictor α γ β₁ β₂ false)
        (interactionPredictor α γ β₁ β₂ true) -
      linkMarginal id ν (interactionPredictor α γ β₁ β₂ false)
        (interactionPredictor α γ β₁ β₂ true) = 0 := by
  rw [(linkMarginal_id_interactionPredictor hν α γ β₁ β₂).2.1, sub_self]

end Contrast

/-! ### What the plug-in converges to -/

section Limit

variable {p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **What the plug-in at the mean covariates estimates.** Let `g(g⁻¹(s)) = s` for every `s`.
Fitted parameters `α̂_n, γ̂_n, β̂₁_n, β̂₂_n` and estimated mean covariates `x̂_n` are random. If
`γ̂_n → γ`, `β̂₂_n → β₂` and `x̂_n → x̄ = covMean ν` in probability, then the plug-in
`g(m̂_true(x̂_n)) - g(m̂_false(x̂_n))` of the fitted model converges in probability to the
plug-in effect of the true model, `γ + x̄ᵀβ₂`; the fitted prognostic effects may be arbitrary. -/
theorem tendstoInMeasure_plugIn {g ginv : ℝ → ℝ} (hg : ∀ s, g (ginv s) = s)
    {ν : Measure (Fin p → ℝ)} {αh γh : ℕ → Ω → ℝ} {β₁h β₂h xh : ℕ → Ω → Fin p → ℝ}
    {α γ : ℝ} {β₁ β₂ : Fin p → ℝ} (hγ : TendstoInMeasure μ γh atTop fun _ => γ)
    (hβ : TendstoInMeasure μ β₂h atTop fun _ => β₂)
    (hx : TendstoInMeasure μ xh atTop fun _ => covMean ν) :
    TendstoInMeasure μ (fun n ω => linkContrast g
        (fun x => ginv (interactionPredictor (αh n ω) (γh n ω) (β₁h n ω) (β₂h n ω) false x))
        (fun x => ginv (interactionPredictor (αh n ω) (γh n ω) (β₁h n ω) (β₂h n ω) true x))
        (xh n ω)) atTop
      (fun _ => plugInEffect g ν (fun x => ginv (interactionPredictor α γ β₁ β₂ false x))
        (fun x => ginv (interactionPredictor α γ β₁ β₂ true x))) := by
  have e : ∀ (a c : ℝ) (b₁ b₂ x : Fin p → ℝ),
      linkContrast g (fun y => ginv (interactionPredictor a c b₁ b₂ false y))
        (fun y => ginv (interactionPredictor a c b₁ b₂ true y)) x = c + ∑ j, x j * b₂ j :=
    fun a c b₁ b₂ x => linkContrast_interactionPredictor (fun _ _ => hg _) x
  have e₀ : plugInEffect g ν (fun x => ginv (interactionPredictor α γ β₁ β₂ false x))
      (fun x => ginv (interactionPredictor α γ β₁ β₂ true x)) =
      γ + ∑ j, covMean ν j * β₂ j := e α γ β₁ β₂ (covMean ν)
  simp only [e, e₀]
  have hc : Continuous fun q : ℝ × (Fin p → ℝ) × (Fin p → ℝ) => q.1 + ∑ j, q.2.2 j * q.2.1 j := by
    fun_prop
  exact (hγ.prodMk (hβ.prodMk hx)).comp_continuousAt hc.continuousAt

end Limit

end PopulationAdjustment

end CausalInference
