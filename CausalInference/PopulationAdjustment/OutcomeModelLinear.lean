/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.StandardizationEstimand

/-!
# Outcome models with a linear predictor: collapse at the mean covariates

The outcome model of a two arm trial on the link `g` has the linear predictor

`η_t(x) = α + xᵀβ₁ + 1{t}(γ + xᵀβ₂)`

(`interactionPredictor`; for the active arm it is `anchoredPredictor`), prognostic effects `β₁`, a
relative effect `γ` and treatment by covariate interactions `β₂`; the arm means are
`m_t = g⁻¹ ∘ η_t`.

* The linear predictor averages to its value at the mean covariates:
  `∫ η_t dν = η_t(x̄)` (`integral_interactionPredictor`), and it changes along the arm slope
  `β₁ + 1{t} β₂` (`interactionPredictor_sub_interactionPredictor`).
* On every link the plug-in at the mean covariates is `γ + x̄ᵀβ₂`, and so is the average
  conditional effect (`plugInEffect_interactionPredictor`,
  `linkConditional_eq_plugInEffect_interactionPredictor`).
* **Collapse on the identity link** (`linkMarginal_id_interactionPredictor`): the marginal
  estimand of a linear model with interactions is `γ + x̄ᵀβ₂`, the conditional effect at the
  mean covariates of the target, and without interactions it is `γ`
  (`linkMarginal_id_interactionPredictor_of_zero`). The same holds for any two arms of an
  anchored model (`AnchoredModel.linkMarginal_id_predictor`) and for the marginal effect of a
  population whose conditional means are linear (`marginalEffect_id_eq_plugInEffect`).

Off the identity link the plug-in is the conditional effect at `x̄` but not the marginal effect;
the difference is the bias of the plug-in, `plugInEffect_sub_linkMarginal`.

## Main definitions

* `interactionSlope β₁ β₂ t`: the covariate slope `β₁ + 1{t} β₂` of arm `t`.

## Main results

* `integrable_interactionPredictor`, `integral_interactionPredictor`,
  `integral_anchoredPredictor`, `interactionPredictor_sub_interactionPredictor`.
* `plugInEffect_interactionPredictor`, `linkConditional_eq_plugInEffect_interactionPredictor`.
* `linkMarginal_id_interactionPredictor`, `linkMarginal_id_interactionPredictor_of_zero`,
  `AnchoredModel.linkMarginal_id_predictor`, `marginalEffect_id_eq_plugInEffect`.

## References

* J. J. Caro and K. J. Ishak, *No head-to-head trial? Simulate the missing arms*,
  PharmacoEconomics 28 (2010).
* D. M. Phillippo, A. E. Ades, S. Dias, S. Palmer, K. R. Abrams and N. J. Welton, *Methods for
  population-adjusted indirect comparisons in health technology appraisal*, Medical Decision
  Making 38 (2018).
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open MeasureTheory EffectMeasure IndirectComparison

variable {p : ℕ} {ν : Measure (Fin p → ℝ)}

/-! ### The linear predictor under a covariate law -/

/-- The **covariate slope** of arm `t` of the interaction model: `β₁` for the reference arm
`false` and `β₁ + β₂` for the active arm `true`. -/
def interactionSlope (β₁ β₂ : Fin p → ℝ) (t : Bool) : Fin p → ℝ := if t then β₁ + β₂ else β₁

/-- The linear predictor of arm `t` changes along its slope:
`η_t(x) - η_t(y) = ∑ⱼ (x_j - y_j) (β₁ + 1{t} β₂)_j`. -/
theorem interactionPredictor_sub_interactionPredictor (α γ : ℝ) (β₁ β₂ : Fin p → ℝ) (t : Bool)
    (x y : Fin p → ℝ) :
    interactionPredictor α γ β₁ β₂ t x - interactionPredictor α γ β₁ β₂ t y =
      ∑ j, (x j - y j) * interactionSlope β₁ β₂ t j := by
  cases t
  · simp only [interactionPredictor, interactionSlope, Bool.false_eq_true, ite_false, add_zero,
      sub_mul, Finset.sum_sub_distrib]
    ring
  · simp only [interactionPredictor, interactionSlope, ite_true, Pi.add_apply, sub_mul, mul_add,
      Finset.sum_sub_distrib, Finset.sum_add_distrib]
    ring

/-- A linear form in covariates with integrable coordinates is integrable. -/
theorem integrable_sum_mul (hν : ∀ k, Integrable (fun x : Fin p → ℝ => x k) ν)
    (β : Fin p → ℝ) : Integrable (fun x : Fin p → ℝ => ∑ j, x j * β j) ν :=
  integrable_finsetSum _ fun j _ => (hν j).mul_const _

/-- The mean of a linear form is the linear form of the mean covariates. -/
theorem integral_sum_mul (hν : ∀ k, Integrable (fun x : Fin p → ℝ => x k) ν) (β : Fin p → ℝ) :
    ∫ x, ∑ j, x j * β j ∂ν = ∑ j, covMean ν j * β j := by
  rw [integral_finsetSum _ fun j _ => (hν j).mul_const _]
  simp only [integral_mul_const, covMean]

/-- The linear predictor is integrable under a finite covariate law with integrable
coordinates. -/
theorem integrable_interactionPredictor [IsFiniteMeasure ν]
    (hν : ∀ k, Integrable (fun x : Fin p → ℝ => x k) ν) (α γ : ℝ) (β₁ β₂ : Fin p → ℝ)
    (t : Bool) : Integrable (interactionPredictor α γ β₁ β₂ t) ν := by
  have h₁ : Integrable (fun x : Fin p → ℝ => α + ∑ j, x j * β₁ j) ν :=
    (integrable_const α).add (integrable_sum_mul hν β₁)
  have h₂ : Integrable (fun x : Fin p → ℝ => γ + ∑ j, x j * β₂ j) ν :=
    (integrable_const γ).add (integrable_sum_mul hν β₂)
  cases t
  · unfold interactionPredictor
    simpa using h₁
  · unfold interactionPredictor
    exact (h₁.add h₂).congr (Filter.Eventually.of_forall fun x => by simp)

/-- **The linear predictor averages to its value at the mean covariates**:
`∫ η_t dν = η_t(x̄)` for a probability covariate law with integrable coordinates. -/
theorem integral_interactionPredictor [IsProbabilityMeasure ν]
    (hν : ∀ k, Integrable (fun x : Fin p → ℝ => x k) ν) (α γ : ℝ) (β₁ β₂ : Fin p → ℝ)
    (t : Bool) :
    ∫ x, interactionPredictor α γ β₁ β₂ t x ∂ν = interactionPredictor α γ β₁ β₂ t (covMean ν) := by
  cases t
  · simp only [interactionPredictor, Bool.false_eq_true, ite_false, add_zero]
    rw [integral_add (integrable_const _) (integrable_sum_mul hν β₁), integral_const,
      integral_sum_mul hν]
    simp
  · simp only [interactionPredictor, ite_true]
    have h₁ : Integrable (fun x : Fin p → ℝ => α + ∑ j, x j * β₁ j) ν :=
      (integrable_const α).add (integrable_sum_mul hν β₁)
    have h₂ : Integrable (fun x : Fin p → ℝ => γ + ∑ j, x j * β₂ j) ν :=
      (integrable_const γ).add (integrable_sum_mul hν β₂)
    rw [integral_add h₁ h₂,
      integral_add (integrable_const _) (integrable_sum_mul hν β₁),
      integral_add (integrable_const _) (integrable_sum_mul hν β₂), integral_const,
      integral_const, integral_sum_mul hν, integral_sum_mul hν]
    simp

/-- The anchored predictor averages to its value at the mean covariates. -/
theorem integral_anchoredPredictor [IsProbabilityMeasure ν]
    (hν : ∀ k, Integrable (fun x : Fin p → ℝ => x k) ν) (α : ℝ) (β₁ : Fin p → ℝ) (γ : ℝ)
    (β₂ : Fin p → ℝ) :
    ∫ x, anchoredPredictor α β₁ γ β₂ x ∂ν = anchoredPredictor α β₁ γ β₂ (covMean ν) := by
  simp only [fun x => (anchoredPredictor_eq_interactionPredictor α γ β₁ β₂ x).1]
  exact integral_interactionPredictor hν α γ β₁ β₂ true

/-! ### The plug-in on any link -/

/-- **The plug-in at the mean covariates on any link.** If the link of each arm mean is the
linear predictor at every covariate value, `g(m_t(x)) = η_t(x)`, the plug-in effect of the
active arm relative to the reference arm is `γ + x̄ᵀβ₂`. -/
theorem plugInEffect_interactionPredictor {g : ℝ → ℝ} {m : Bool → (Fin p → ℝ) → ℝ} {α γ : ℝ}
    {β₁ β₂ : Fin p → ℝ} (hm : ∀ t x, g (m t x) = interactionPredictor α γ β₁ β₂ t x)
    (ν : Measure (Fin p → ℝ)) : plugInEffect g ν (m false) (m true) = γ + covMean ν ⬝ᵥ β₂ :=
  linkContrast_interactionPredictor hm (covMean ν)

/-- **The average conditional effect is the plug-in on any link**: with `g(m_t(x)) = η_t(x)` at
every `x` and a probability covariate law with integrable coordinates, the average conditional
effect of the active arm is `γ + x̄ᵀβ₂`, the plug-in at the mean covariates. -/
theorem linkConditional_eq_plugInEffect_interactionPredictor [IsProbabilityMeasure ν]
    (hν : ∀ k, Integrable (fun x : Fin p → ℝ => x k) ν) {g : ℝ → ℝ}
    {m : Bool → (Fin p → ℝ) → ℝ} {α γ : ℝ} {β₁ β₂ : Fin p → ℝ}
    (hm : ∀ t x, g (m t x) = interactionPredictor α γ β₁ β₂ t x) :
    linkConditional g ν (m false) (m true) = plugInEffect g ν (m false) (m true) ∧
      linkConditional g ν (m false) (m true) = γ + covMean ν ⬝ᵥ β₂ := by
  have e : linkConditional g ν (m false) (m true) = γ + covMean ν ⬝ᵥ β₂ := by
    simp only [linkConditional, linkContrast_interactionPredictor hm]
    rw [integral_add (integrable_const _) (integrable_sum_mul hν β₂), integral_const,
      integral_sum_mul hν]
    simp [dotProduct]
  exact ⟨e.trans (plugInEffect_interactionPredictor hm ν).symm, e⟩

/-! ### Collapse on the identity link -/

/-- **Collapse of a linear outcome model with interactions.** On the identity link, under a
probability covariate law with integrable coordinates, the marginal estimand of the linear model
is `γ + x̄ᵀβ₂`: it equals the plug-in at the mean covariates and the average conditional
effect. -/
theorem linkMarginal_id_interactionPredictor [IsProbabilityMeasure ν]
    (hν : ∀ k, Integrable (fun x : Fin p → ℝ => x k) ν) (α γ : ℝ) (β₁ β₂ : Fin p → ℝ) :
    linkMarginal id ν (interactionPredictor α γ β₁ β₂ false)
        (interactionPredictor α γ β₁ β₂ true) = γ + covMean ν ⬝ᵥ β₂ ∧
      linkMarginal id ν (interactionPredictor α γ β₁ β₂ false)
          (interactionPredictor α γ β₁ β₂ true) =
        plugInEffect id ν (interactionPredictor α γ β₁ β₂ false)
          (interactionPredictor α γ β₁ β₂ true) ∧
      linkMarginal id ν (interactionPredictor α γ β₁ β₂ false)
          (interactionPredictor α γ β₁ β₂ true) =
        linkConditional id ν (interactionPredictor α γ β₁ β₂ false)
          (interactionPredictor α γ β₁ β₂ true) := by
  have hm : ∀ t x, id (interactionPredictor α γ β₁ β₂ t x) = interactionPredictor α γ β₁ β₂ t x :=
    fun _ _ => rfl
  have e : linkMarginal id ν (interactionPredictor α γ β₁ β₂ false)
      (interactionPredictor α γ β₁ β₂ true) = γ + covMean ν ⬝ᵥ β₂ := by
    rw [linkMarginal, integral_interactionPredictor hν, integral_interactionPredictor hν]
    exact plugInEffect_interactionPredictor hm ν
  refine ⟨e, e.trans (plugInEffect_interactionPredictor hm ν).symm, ?_⟩
  rw [e, (linkConditional_eq_plugInEffect_interactionPredictor hν hm).2]

/-- **Collapse of a linear outcome model without interactions**: on the identity link the
marginal estimand of `α + xᵀβ₁ + 1{t} γ` is the conditional effect `γ`, under every probability
covariate law with integrable coordinates. -/
theorem linkMarginal_id_interactionPredictor_of_zero [IsProbabilityMeasure ν]
    (hν : ∀ k, Integrable (fun x : Fin p → ℝ => x k) ν) (α γ : ℝ) (β₁ : Fin p → ℝ) :
    linkMarginal id ν (interactionPredictor α γ β₁ 0 false) (interactionPredictor α γ β₁ 0 true) =
      γ := by
  rw [(linkMarginal_id_interactionPredictor hν α γ β₁ 0).1, dotProduct_zero, add_zero]

/-- **Collapse for two arms of an anchored model.** On the identity link, under a probability
covariate law with integrable coordinates, the marginal estimand of arm `b` relative to arm `a`
is `(γ_b - γ_a) + x̄ᵀ(β₂,b - β₂,a)`, the plug-in at the mean covariates. -/
theorem AnchoredModel.linkMarginal_id_predictor {ι : Type*} [IsProbabilityMeasure ν]
    (hν : ∀ k, Integrable (fun x : Fin p → ℝ => x k) ν) (M : AnchoredModel ι p) (a b : ι) :
    linkMarginal id ν (M.predictor a) (M.predictor b) =
        M.γ b - M.γ a + covMean ν ⬝ᵥ (M.β₂ b - M.β₂ a) ∧
      linkMarginal id ν (M.predictor a) (M.predictor b) =
        plugInEffect id ν (M.predictor a) (M.predictor b) := by
  have hint : ∀ t, ∫ x, M.predictor t x ∂ν = M.predictor t (covMean ν) := fun t =>
    integral_anchoredPredictor hν M.α M.β₁ (M.γ t) (M.β₂ t)
  have e : linkMarginal id ν (M.predictor a) (M.predictor b) =
      plugInEffect id ν (M.predictor a) (M.predictor b) := by
    rw [linkMarginal, hint, hint]; rfl
  refine ⟨?_, e⟩
  rw [e, plugInEffect_eq]
  simp only [id, AnchoredModel.predictor, anchoredPredictor, dotProduct, Pi.sub_apply, mul_sub,
    Finset.sum_sub_distrib]
  ring

/-- **Collapse in a population.** If the conditional mean functions of the two arms of a
probability population with covariates in `ℝ^p` are the linear predictor of the interaction
model (identity link), the potential outcomes and the covariates are integrable, then the
marginal effect of the active arm on the identity scale is the plug-in at the mean covariates,
`γ + E[X]ᵀβ₂`. -/
theorem marginalEffect_id_eq_plugInEffect {Ω : Type*} [MeasurableSpace Ω]
    {Q : Population Ω (Fin p → ℝ) Bool} [IsProbabilityMeasure Q.μ] (hX : Measurable Q.X)
    (hXi : ∀ k, Integrable (fun ω => Q.X ω k) Q.μ) (hY : ∀ t, Integrable (Q.Y t) Q.μ)
    {α γ : ℝ} {β₁ β₂ : Fin p → ℝ}
    (hm : ∀ t, Q.IsCondMean t (interactionPredictor α γ β₁ β₂ t)) :
    Q.marginalEffect id false true =
        plugInEffect id Q.covLaw (interactionPredictor α γ β₁ β₂ false)
          (interactionPredictor α γ β₁ β₂ true) ∧
      Q.marginalEffect id false true = γ + covMean Q.covLaw ⬝ᵥ β₂ := by
  have : IsProbabilityMeasure Q.covLaw := Q.isProbabilityMeasure_covLaw hX
  have hν : ∀ k, Integrable (fun x : Fin p → ℝ => x k) Q.covLaw := fun k =>
    (integrable_map_measure (measurable_pi_apply k).aestronglyMeasurable hX.aemeasurable).2
      (hXi k)
  rw [Q.marginalEffect_eq_linkMarginal id hX (hY false) (hY true) (hm false) (hm true)]
  obtain ⟨h1, h2, -⟩ := linkMarginal_id_interactionPredictor hν α γ β₁ β₂
  exact ⟨h2, h1⟩

end PopulationAdjustment

end CausalInference
