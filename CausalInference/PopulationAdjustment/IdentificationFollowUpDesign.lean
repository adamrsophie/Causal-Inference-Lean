/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.IndirectComparison.SmallestNetwork

/-!
# Shared effect modifiers in the smallest network, for anchored models

The smallest anchored network: a trial of `a` against the common comparator `c` with individual
data, which give the conditional means of `a` and `c` as functions of the covariate `x`, and a
trial of `b` against `c` with aggregate data over a covariate law `f`, which give the average
conditional effect of `b` relative to `c` (the reported contrast). Both trials follow one
anchored model `M` (`AnchoredModel`); the aggregate trial has its own intercept
(`AnchoredModel.withIntercept`). The mean of treatment `t` is `g⁻¹ ∘ η_t`, for a mean function
`g⁻¹` with `g (g⁻¹ y) = y` (the identity, `exp` for the log link, the logistic function for the
logit). The target is a population with covariate law `Q`.

* `AnchoredModel.linkConditional_predictor`: the average conditional effect of `t` relative to
  `s` under `Q` is `γ_t - γ_s + x̄_Qᵀ(β₂,t - β₂,s)`, with `x̄_Q = covMean Q`.
* **Identification of the target effect** (`AnchoredModel.linkConditional_eq_of_shared_of_design`):
  two models anchored at `c` with shared effect modifiers for `{a, b}` that reproduce the
  individual data at full column rank designs and the reported contrast have the same target
  effect of `b` relative to `a` in every target. This is `sharedEffectModifiers_identifiable` for
  anchored models.
* **The assumption has no testable implication in the smallest network, and it matters exactly
  when the target differs from the aggregate trial in its covariate means**
  (`AnchoredModel.sharedEffectModifiers_untestable`): for a model anchored at `c` with shared
  effect modifiers and a target with `x̄_Q ≠ x̄_f`, there is a model `M'`, anchored at `c`, without
  shared effect modifiers, with the same conditional means of `a` and `c` at every covariate value,
  the same conditional mean of `c` and the same reported contrast in the aggregate trial, the
  same mean linear predictor of `b` in the aggregate trial (the aggregate mean of `b` on the
  identity link), and a target effect of `b` relative to `a` larger by `‖x̄_Q - x̄_f‖² > 0`.
  Conversely, when `x̄_Q = x̄_f` every two models that agree on these data have the same target
  effect, with or without the assumption (`AnchoredModel.linkConditional_eq_of_covMean_eq`).
* **A second aggregate trial gives a testable restriction, which characterizes the assumption**
  (`AnchoredModel.sharedEffectModifiers_iff_overidentifying`): with the reported contrasts `d_f`
  of aggregate trials of `b` against `c` over laws `f` and the contrast `τ_ac(x) = η_a(x) - η_c(x)`
  given by the individual data, `M` shares the effect modifiers of `a` and `b` if and only if
  `d_f - d_f' = τ_ac(x̄_f) - τ_ac(x̄_f')` for every two laws `f`, `f'` with integrable
  coordinates; with `x̄_f ≠ x̄_f'` this is an equation between observed quantities.

## Main definitions

* `AnchoredModel.withIntercept`, `AnchoredModel.unsharedExampleModel`.

## Main results

* `AnchoredModel.integral_anchoredPredictor`, `AnchoredModel.linkConditional_predictor`.
* `AnchoredModel.linkConditional_eq_of_shared_of_design`.
* `AnchoredModel.sharedEffectModifiers_untestable`,
  `AnchoredModel.linkConditional_eq_of_covMean_eq`.
* `AnchoredModel.sharedEffectModifiers_iff_overidentifying`.
* `AnchoredModel.sharedEffectModifiers_untestable_example`, `AnchoredModel.overidentifying_example`,
  `AnchoredModel.shared_of_design_example`.

## References

* D. M. Phillippo, A. E. Ades, S. Dias, S. Palmer, K. R. Abrams and N. J. Welton, *Methods for
  population-adjusted indirect comparisons in health technology appraisal*, Medical Decision
  Making 38 (2018).
* D. M. Phillippo, S. Dias, A. E. Ades, M. Belger, A. Brnabic, A. Schacht, D. Saure, Z. Kadziola
  and N. J. Welton, *Multilevel network meta-regression for population-adjusted treatment
  comparisons*, Journal of the Royal Statistical Society Series A 183 (2020).
-/

@[expose] public section

namespace CausalInference

namespace IndirectComparison

open MeasureTheory EffectMeasure

variable {p : ℕ}

namespace AnchoredModel

variable {ι : Type*}

/-- The anchored model `M` with the intercept replaced by `α₂`: the model of a second study with
its own baseline and the same prognostic effects, relative effects and interactions. -/
def withIntercept (M : AnchoredModel ι p) (α₂ : ℝ) : AnchoredModel ι p :=
  ⟨α₂, M.β₁, M.γ, M.β₂⟩

/-- **The mean of an anchored predictor**: under a probability law `f` with integrable
coordinates, `∫ (α + xᵀβ₁ + γ + xᵀβ₂) df = α + γ + x̄ᵀ(β₁ + β₂)`. -/
theorem integral_anchoredPredictor {f : Measure (Fin p → ℝ)} [IsProbabilityMeasure f]
    (hf : ∀ k, Integrable (fun x => x k) f) (α : ℝ) (β₁ : Fin p → ℝ) (γ : ℝ)
    (β₂ : Fin p → ℝ) :
    ∫ x, anchoredPredictor α β₁ γ β₂ x ∂f = α + γ + covMean f ⬝ᵥ (β₁ + β₂) := by
  have e : ∀ x, anchoredPredictor α β₁ γ β₂ x = (α + γ) + ∑ j, x j * (β₁ + β₂) j := fun x => by
    simp only [anchoredPredictor, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    ring
  simp only [e]
  rw [integral_add (integrable_const _) (integrable_finsetSum _ fun j _ => (hf j).mul_const _),
    integral_const, integral_finsetSum _ fun j _ => (hf j).mul_const _]
  simp only [integral_mul_const, probReal_univ, smul_eq_mul, one_mul, covMean, dotProduct]

/-- **The average conditional effect in an anchored model.** If `g (g⁻¹ y) = y` for all `y`, then
under a probability law `Q` with integrable coordinates the average conditional effect on the
scale `g` of `t` relative to `s`, with means `g⁻¹ ∘ η`, is `γ_t - γ_s + x̄_Qᵀ(β₂,t - β₂,s)`. -/
theorem linkConditional_predictor {g ginv : ℝ → ℝ} (hg : ∀ y, g (ginv y) = y)
    (M : AnchoredModel ι p) {Q : Measure (Fin p → ℝ)} [IsProbabilityMeasure Q]
    (hQ : ∀ k, Integrable (fun x => x k) Q) (s t : ι) :
    linkConditional g Q (fun x => ginv (M.predictor s x)) (fun x => ginv (M.predictor t x)) =
      M.γ t - M.γ s + covMean Q ⬝ᵥ (M.β₂ t - M.β₂ s) := by
  have e : ∀ x, linkContrast g (fun x => ginv (M.predictor s x))
      (fun x => ginv (M.predictor t x)) x = (M.γ t - M.γ s) + ∑ j, x j * (M.β₂ t - M.β₂ s) j :=
    fun x => by
      simp only [linkContrast, hg, predictor, anchoredPredictor, Pi.sub_apply, mul_sub,
        Finset.sum_sub_distrib]
      ring
  simp only [linkConditional, e]
  rw [integral_add (integrable_const _) (integrable_finsetSum _ fun j _ => (hQ j).mul_const _),
    integral_const, integral_finsetSum _ fun j _ => (hQ j).mul_const _]
  simp only [integral_mul_const, probReal_univ, smul_eq_mul, one_mul, covMean, dotProduct]

/-! ### Identification of the target effect -/

/-- **Shared effect modifiers identify the target effect.** Let `M`, `M'` be anchored at `c` with
shared effect modifiers for `{a, b}`. Suppose that both reproduce the individual data, meaning
the link values `g(m_c)` and `g(m_a)` at the design points `x_c`, `x_a` of full column rank
designs. Suppose also that both reproduce the reported contrast of the aggregate trial over a law
`f` with integrable coordinates (with intercepts `α₂`, `α₂'`). Then in every target law `Q` with
integrable coordinates the two models give the same average conditional effect of `b` relative
to `a`, and it is `γ_b - γ_a`. -/
theorem linkConditional_eq_of_shared_of_design {g ginv : ℝ → ℝ} (hg : ∀ y, g (ginv y) = y)
    {M M' : AnchoredModel ι p} {a b c : ι} (hc : M.IsAnchoredAt c) (hc' : M'.IsAnchoredAt c)
    (hS : M.SharedEffectModifiers {a, b}) (hS' : M'.SharedEffectModifiers {a, b}) {nc na : ℕ}
    {xc : Fin nc → Fin p → ℝ} {xa : Fin na → Fin p → ℝ}
    (hrc : LinearIndependent ℝ (designMatrix xc).col)
    (hra : LinearIndependent ℝ (designMatrix xa).col) {mc ma : (Fin p → ℝ) → ℝ}
    (hdc : ∀ i, g (mc (xc i)) = M.predictor c (xc i))
    (hda : ∀ i, g (ma (xa i)) = M.predictor a (xa i))
    (hdc' : ∀ i, g (mc (xc i)) = M'.predictor c (xc i))
    (hda' : ∀ i, g (ma (xa i)) = M'.predictor a (xa i))
    {f : Measure (Fin p → ℝ)} [IsProbabilityMeasure f] (hf : ∀ k, Integrable (fun x => x k) f)
    (α₂ α₂' : ℝ)
    (hd : linkConditional g f (fun x => ginv ((M.withIntercept α₂).predictor c x))
        (fun x => ginv ((M.withIntercept α₂).predictor b x)) =
      linkConditional g f (fun x => ginv ((M'.withIntercept α₂').predictor c x))
        (fun x => ginv ((M'.withIntercept α₂').predictor b x)))
    {Q : Measure (Fin p → ℝ)} [IsProbabilityMeasure Q] (hQ : ∀ k, Integrable (fun x => x k) Q) :
    linkConditional g Q (fun x => ginv (M.predictor a x)) (fun x => ginv (M.predictor b x)) =
        linkConditional g Q (fun x => ginv (M'.predictor a x))
          (fun x => ginv (M'.predictor b x)) ∧
      linkConditional g Q (fun x => ginv (M.predictor a x)) (fun x => ginv (M.predictor b x)) =
        M.γ b - M.γ a := by
  have hab : M.β₂ b = M.β₂ a := hS b (by simp) a (by simp)
  have hab' : M'.β₂ b = M'.β₂ a := hS' b (by simp) a (by simp)
  have hpc : ∀ x, M.predictor c x = anchoredPredictor M.α M.β₁ 0 0 x := fun x => by
    rw [predictor, hc.1, hc.2]
  have hpc' : ∀ x, M'.predictor c x = anchoredPredictor M'.α M'.β₁ 0 0 x := fun x => by
    rw [predictor, hc'.1, hc'.2]
  have hbg : ∀ x, g (ginv ((M.withIntercept α₂).predictor b x)) =
      anchoredPredictor α₂ M.β₁ (M.γ b) (M.β₂ a) x := fun x => by
    rw [hg, ← hab]; rfl
  have hcg : ∀ x, g (ginv ((M.withIntercept α₂).predictor c x)) =
      anchoredPredictor α₂ M.β₁ 0 0 x := fun x => by
    rw [hg]; change anchoredPredictor α₂ M.β₁ (M.γ c) (M.β₂ c) x = _; rw [hc.1, hc.2]
  have hbg' : ∀ x, g (ginv ((M'.withIntercept α₂').predictor b x)) =
      anchoredPredictor α₂' M'.β₁ (M'.γ b) (M'.β₂ a) x := fun x => by
    rw [hg, ← hab']; rfl
  have hcg' : ∀ x, g (ginv ((M'.withIntercept α₂').predictor c x)) =
      anchoredPredictor α₂' M'.β₁ 0 0 x := fun x => by
    rw [hg]; change anchoredPredictor α₂' M'.β₁ (M'.γ c) (M'.β₂ c) x = _; rw [hc'.1, hc'.2]
  obtain ⟨-, hγa, hγb, -, -⟩ := sharedEffectModifiers_identifiable hrc hra hf
    (fun i => (hdc i).trans (hpc _)) hda hbg hcg rfl
    (fun i => (hdc' i).trans (hpc' _)) hda' hbg' hcg' hd.symm
  have e := linkConditional_predictor hg M hQ a b
  have e' := linkConditional_predictor hg M' hQ a b
  rw [hab, sub_self, dotProduct_zero, add_zero] at e
  rw [hab', sub_self, dotProduct_zero, add_zero] at e'
  exact ⟨by rw [e, e', hγa, hγb], e⟩

/-! ### No testable implication in the smallest network -/

/-- **Shared effect modifiers cannot be tested in the smallest network, and they matter exactly
when the covariate means of the target differ from those of the aggregate trial.** Let `M` be
anchored at `c` with shared effect modifiers for `{a, b}`, `a ≠ b`, `c ≠ b`, `g (g⁻¹ y) = y`,
an aggregate trial over `f` with intercept `α₂` and a target law `Q`, both with integrable
coordinates, and `x̄_Q ≠ x̄_f`. Moving the interactions of `b` by `v = x̄_Q - x̄_f` and its
relative effect by `-x̄_fᵀv` gives a model `M'` that is anchored at `c`, does not share the
effect modifiers of `a` and `b`, has the same predictors of `a` and `c` (the individual data), the
same predictor of `c` in the aggregate trial, the same reported contrast of `b` against `c` and the
same mean predictor of `b` in the aggregate trial, while its target effect of `b` relative to `a`
exceeds that of `M` by `vᵀv > 0`. -/
theorem sharedEffectModifiers_untestable {g ginv : ℝ → ℝ}
    (hg : ∀ y, g (ginv y) = y) {M : AnchoredModel ι p} {a b c : ι} (hab : a ≠ b) (hcb : c ≠ b)
    (hc : M.IsAnchoredAt c) (hS : M.SharedEffectModifiers {a, b}) (α₂ : ℝ)
    {f Q : Measure (Fin p → ℝ)} [IsProbabilityMeasure f] [IsProbabilityMeasure Q]
    (hf : ∀ k, Integrable (fun x => x k) f) (hQ : ∀ k, Integrable (fun x => x k) Q)
    (hne : covMean Q ≠ covMean f) :
    ∃ M' : AnchoredModel ι p, M'.IsAnchoredAt c ∧ ¬ M'.SharedEffectModifiers {a, b} ∧
      M'.predictor a = M.predictor a ∧ M'.predictor c = M.predictor c ∧
      (M'.withIntercept α₂).predictor c = (M.withIntercept α₂).predictor c ∧
      linkConditional g f (fun x => ginv ((M'.withIntercept α₂).predictor c x))
          (fun x => ginv ((M'.withIntercept α₂).predictor b x)) =
        linkConditional g f (fun x => ginv ((M.withIntercept α₂).predictor c x))
          (fun x => ginv ((M.withIntercept α₂).predictor b x)) ∧
      ∫ x, (M'.withIntercept α₂).predictor b x ∂f = ∫ x, (M.withIntercept α₂).predictor b x ∂f ∧
      linkConditional g Q (fun x => ginv (M'.predictor a x)) (fun x => ginv (M'.predictor b x)) -
          linkConditional g Q (fun x => ginv (M.predictor a x))
            (fun x => ginv (M.predictor b x)) =
        (covMean Q - covMean f) ⬝ᵥ (covMean Q - covMean f) ∧
      0 < (covMean Q - covMean f) ⬝ᵥ (covMean Q - covMean f) := by
  classical
  set v := covMean Q - covMean f with hv
  have hv0 : v ≠ 0 := sub_ne_zero.2 hne
  let M' : AnchoredModel ι p :=
    ⟨M.α, M.β₁, Function.update M.γ b (M.γ b - covMean f ⬝ᵥ v),
      Function.update M.β₂ b (M.β₂ b + v)⟩
  have γb : M'.γ b = M.γ b - covMean f ⬝ᵥ v := Function.update_self _ _ _
  have βb : M'.β₂ b = M.β₂ b + v := Function.update_self _ _ _
  have γo : ∀ t, t ≠ b → M'.γ t = M.γ t := fun t ht => Function.update_of_ne ht _ _
  have βo : ∀ t, t ≠ b → M'.β₂ t = M.β₂ t := fun t ht => Function.update_of_ne ht _ _
  have hpa : M'.predictor a = M.predictor a := by
    funext x; simp only [predictor, γo a hab, βo a hab]; rfl
  have hpc : M'.predictor c = M.predictor c := by
    funext x; simp only [predictor, γo c hcb, βo c hcb]; rfl
  have hpc₂ : (M'.withIntercept α₂).predictor c = (M.withIntercept α₂).predictor c := by
    funext x
    change anchoredPredictor α₂ M.β₁ (M'.γ c) (M'.β₂ c) x =
      anchoredPredictor α₂ M.β₁ (M.γ c) (M.β₂ c) x
    rw [γo c hcb, βo c hcb]
  have hab₂ : M.β₂ a = M.β₂ b := hS a (by simp) b (by simp)
  refine ⟨M', ⟨by rw [γo c hcb]; exact hc.1, by rw [βo c hcb]; exact hc.2⟩, fun hS' => ?_,
    hpa, hpc, hpc₂, ?_, ?_, ?_, ?_⟩
  · have h := hS' a (by simp) b (by simp)
    rw [βo a hab, βb, hab₂] at h
    exact hv0 (by simpa using h)
  · rw [linkConditional_predictor hg _ hf, linkConditional_predictor hg _ hf]
    change M'.γ b - M'.γ c + covMean f ⬝ᵥ (M'.β₂ b - M'.β₂ c) =
      M.γ b - M.γ c + covMean f ⬝ᵥ (M.β₂ b - M.β₂ c)
    rw [γb, βb, γo c hcb, βo c hcb, show M.β₂ b + v - M.β₂ c = (M.β₂ b - M.β₂ c) + v by abel,
      dotProduct_add]
    ring
  · change ∫ x, anchoredPredictor α₂ M.β₁ (M'.γ b) (M'.β₂ b) x ∂f =
      ∫ x, anchoredPredictor α₂ M.β₁ (M.γ b) (M.β₂ b) x ∂f
    rw [integral_anchoredPredictor hf, integral_anchoredPredictor hf, γb, βb,
      show M.β₁ + (M.β₂ b + v) = (M.β₁ + M.β₂ b) + v by abel, dotProduct_add]
    ring
  · rw [linkConditional_predictor hg _ hQ, linkConditional_predictor hg _ hQ, γb, βb, γo a hab,
      βo a hab, show M.β₂ b + v - M.β₂ a = (M.β₂ b - M.β₂ a) + v by abel, dotProduct_add]
    have : covMean Q = v + covMean f := by rw [hv]; abel
    rw [this, add_dotProduct v (covMean f) v]
    ring
  · exact dotProduct_self_pos_of_ne hv0

/-- **Without a covariate shift the target effect is identified without the assumption.** If two
anchored models (not necessarily with shared effect modifiers) have the same predictors of `a`
and `c`, the same reported contrast of `b` against `c` in the aggregate trial over `f` (with
intercepts `α₂`, `α₂'`), and the target law `Q` has the covariate means `x̄_Q = x̄_f`, then they
give the same target effect of `b` relative to `a`. -/
theorem linkConditional_eq_of_covMean_eq {g ginv : ℝ → ℝ} (hg : ∀ y, g (ginv y) = y)
    {M M' : AnchoredModel ι p} {a b c : ι} (hpa : M'.predictor a = M.predictor a)
    (hpc : M'.predictor c = M.predictor c) (α₂ α₂' : ℝ) {f Q : Measure (Fin p → ℝ)}
    [IsProbabilityMeasure f] [IsProbabilityMeasure Q] (hf : ∀ k, Integrable (fun x => x k) f)
    (hQ : ∀ k, Integrable (fun x => x k) Q)
    (hd : linkConditional g f (fun x => ginv ((M'.withIntercept α₂').predictor c x))
        (fun x => ginv ((M'.withIntercept α₂').predictor b x)) =
      linkConditional g f (fun x => ginv ((M.withIntercept α₂).predictor c x))
        (fun x => ginv ((M.withIntercept α₂).predictor b x)))
    (hmean : covMean Q = covMean f) :
    linkConditional g Q (fun x => ginv (M'.predictor a x)) (fun x => ginv (M'.predictor b x)) =
      linkConditional g Q (fun x => ginv (M.predictor a x)) (fun x => ginv (M.predictor b x)) := by
  have ica := linkConditional_predictor hg M hQ c a
  have ica' := linkConditional_predictor hg M' hQ c a
  rw [hpa, hpc] at ica'
  rw [linkConditional_predictor hg _ hf, linkConditional_predictor hg _ hf] at hd
  change M'.γ b - M'.γ c + covMean f ⬝ᵥ (M'.β₂ b - M'.β₂ c) =
    M.γ b - M.γ c + covMean f ⬝ᵥ (M.β₂ b - M.β₂ c) at hd
  rw [linkConditional_predictor hg _ hQ, linkConditional_predictor hg _ hQ, hmean]
  rw [ica, hmean] at ica'
  simp only [dotProduct_sub] at hd ica' ⊢
  linarith

/-! ### The overidentifying restriction -/

/-- **A second aggregate trial gives a testable restriction, and it characterizes shared effect
modifiers.** For an anchored model `M` and `g (g⁻¹ y) = y`, write `d_f` for the reported contrast
of `b` against `c` in an aggregate trial over `f` with intercept `α₂`, and
`τ_ac(x) = η_a(x) - η_c(x)` for the contrast of `a` against `c`, which the individual data give
at every `x`. Then `M` shares the effect modifiers of `a` and `b` if and only if
`d_f - d_f' = τ_ac(x̄_f) - τ_ac(x̄_f')` for every two probability laws `f`, `f'` with integrable
coordinates (and any intercepts). In general `d_f - d_f' = (x̄_f - x̄_f')ᵀ(β₂,b - β₂,c)`. -/
theorem sharedEffectModifiers_iff_overidentifying {g ginv : ℝ → ℝ} (hg : ∀ y, g (ginv y) = y)
    (M : AnchoredModel ι p) (a b c : ι) :
    M.SharedEffectModifiers {a, b} ↔
      ∀ (f f' : Measure (Fin p → ℝ)) [IsProbabilityMeasure f] [IsProbabilityMeasure f'],
        (∀ k, Integrable (fun x => x k) f) → (∀ k, Integrable (fun x => x k) f') →
        ∀ α₂ α₂' : ℝ,
        linkConditional g f (fun x => ginv ((M.withIntercept α₂).predictor c x))
            (fun x => ginv ((M.withIntercept α₂).predictor b x)) -
          linkConditional g f' (fun x => ginv ((M.withIntercept α₂').predictor c x))
            (fun x => ginv ((M.withIntercept α₂').predictor b x)) =
        (M.predictor a (covMean f) - M.predictor c (covMean f)) -
          (M.predictor a (covMean f') - M.predictor c (covMean f')) := by
  have hτ : ∀ y : Fin p → ℝ, M.predictor a y - M.predictor c y =
      M.γ a - M.γ c + y ⬝ᵥ (M.β₂ a - M.β₂ c) := fun y => by
    simp only [predictor, anchoredPredictor, dotProduct, Pi.sub_apply, mul_sub,
      Finset.sum_sub_distrib]
    ring
  have hd : ∀ (f : Measure (Fin p → ℝ)) [IsProbabilityMeasure f],
      (∀ k, Integrable (fun x => x k) f) → ∀ α₂ : ℝ,
      linkConditional g f (fun x => ginv ((M.withIntercept α₂).predictor c x))
          (fun x => ginv ((M.withIntercept α₂).predictor b x)) =
        M.γ b - M.γ c + covMean f ⬝ᵥ (M.β₂ b - M.β₂ c) := fun f _ hf α₂ =>
    linkConditional_predictor hg (M.withIntercept α₂) hf c b
  constructor
  · intro hS f f' _ _ hf hf' α₂ α₂'
    have hab : M.β₂ b = M.β₂ a := hS b (by simp) a (by simp)
    rw [hd f hf, hd f' hf', hτ, hτ, hab]
    ring
  · intro h
    have hdirac : ∀ y : Fin p → ℝ, ∀ k, Integrable (fun x : Fin p → ℝ => x k) (Measure.dirac y) :=
      fun _ _ => integrable_dirac (by simp)
    have hmean : ∀ y : Fin p → ℝ, covMean (Measure.dirac y) = y := fun y => by
      funext k; simp [covMean]
    have key : ∀ y : Fin p → ℝ, y ⬝ᵥ (M.β₂ b - M.β₂ c) = y ⬝ᵥ (M.β₂ a - M.β₂ c) := fun y => by
      have := h (Measure.dirac y) (Measure.dirac 0) (hdirac y) (hdirac 0) 0 0
      rw [hd _ (hdirac y), hd _ (hdirac 0), hτ, hτ, hmean, hmean] at this
      simp only [zero_dotProduct] at this
      linarith
    have hba : M.β₂ b = M.β₂ a := by
      funext j
      have := key (Pi.single j 1)
      simp only [single_one_dotProduct, Pi.sub_apply] at this
      linarith
    intro s hs t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · rfl
    · exact hba.symm
    · exact hba
    · rfl

/-! ### Instances -/

/-- An anchored model on one covariate for the treatments `0, 1, 2` without shared effect
modifiers: intercept `0`, prognostic effect `1`, relative effects `γ = (0, 1, 4)` and
interactions `β₂ = (0, 2, 1)`. It differs from `sharedExampleModel` (`γ = (0, 1, 3)`,
`β₂ = (0, 2, 2)`) only in treatment `2`; it is the model `M'` of
`sharedEffectModifiers_untestable` for `sharedExampleModel` with `a = 1`, `b = 2`, `c = 0`,
`x̄_f = 1` and `x̄_Q = 0`. -/
def unsharedExampleModel : AnchoredModel (Fin 3) 1 :=
  ⟨0, fun _ => 1, ![0, 1, 4], ![0, fun _ => 2, fun _ => 1]⟩

/-- The covariate means of a point mass. -/
theorem covMean_dirac (y : Fin p → ℝ) : covMean (Measure.dirac y) = y := by
  funext k; simp [covMean]

/-- A point mass has integrable coordinates. -/
theorem integrable_coord_dirac (y : Fin p → ℝ) (k : Fin p) :
    Integrable (fun x : Fin p → ℝ => x k) (Measure.dirac y) :=
  integrable_dirac (by simp)

/-- **Shared effect modifiers are untestable in the smallest network: two explicit models.**
With `a = 1`, `b = 2`, `c = 0` on the identity scale, an aggregate trial of `2` against `0` with
intercept `0` and covariate concentrated at `1`, and a target concentrated at `0`:
`sharedExampleModel` (shared effect modifiers) and `unsharedExampleModel` (not shared), both
anchored at `0`, have the same predictors of `0` and `1` (the individual data), the same
aggregate predictor of `0`, the same reported contrast `5` and the same aggregate mean predictor
`6` of `2`, but target effects of `2` relative to `1` equal to `2` and `3`. -/
theorem sharedEffectModifiers_untestable_example :
    let f : Measure (Fin 1 → ℝ) := Measure.dirac fun _ => 1
    let Q : Measure (Fin 1 → ℝ) := Measure.dirac fun _ => 0
    let M := sharedExampleModel
    let M' := unsharedExampleModel
    M.SharedEffectModifiers {1, 2} ∧ M.IsAnchoredAt 0 ∧ M'.IsAnchoredAt 0 ∧
      ¬ M'.SharedEffectModifiers {1, 2} ∧
      M'.predictor 1 = M.predictor 1 ∧ M'.predictor 0 = M.predictor 0 ∧
      ((M'.withIntercept 0).predictor 0) = ((M.withIntercept 0).predictor 0) ∧
      linkConditional id f ((M.withIntercept 0).predictor 0) ((M.withIntercept 0).predictor 2) = 5 ∧
      linkConditional id f ((M'.withIntercept 0).predictor 0)
        ((M'.withIntercept 0).predictor 2) = 5 ∧
      ∫ x, (M.withIntercept 0).predictor 2 x ∂f = 6 ∧
      ∫ x, (M'.withIntercept 0).predictor 2 x ∂f = 6 ∧
      linkConditional id Q (M.predictor 1) (M.predictor 2) = 2 ∧
      linkConditional id Q (M'.predictor 1) (M'.predictor 2) = 3 := by
  intro f Q M M'
  obtain ⟨hA, hS, -⟩ := sharedExampleModel_transport
  have hc : ∀ (N : AnchoredModel (Fin 3) 1) (y : Fin 1 → ℝ) (s t : Fin 3),
      linkConditional id (Measure.dirac y) (N.predictor s) (N.predictor t) =
        N.γ t - N.γ s + y ⬝ᵥ (N.β₂ t - N.β₂ s) := fun N y s t => by
    have h := linkConditional_predictor (g := id) (ginv := id) (fun _ => rfl) N
      (integrable_coord_dirac y) s t
    rw [covMean_dirac] at h
    exact h
  refine ⟨hS, hA, ⟨rfl, rfl⟩, fun h => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := congrFun (h 1 (by simp) 2 (by simp)) 0
    simp [M', unsharedExampleModel] at this
  · funext x; rfl
  · funext x; rfl
  · funext x; rfl
  · rw [hc]; simp [M, sharedExampleModel, withIntercept, dotProduct]; norm_num
  · rw [hc]; simp [M', unsharedExampleModel, withIntercept, dotProduct]; norm_num
  · change ∫ x, anchoredPredictor 0 M.β₁ (M.γ 2) (M.β₂ 2) x ∂f = 6
    rw [integral_anchoredPredictor (integrable_coord_dirac _), covMean_dirac]
    simp [M, sharedExampleModel, dotProduct]; norm_num
  · change ∫ x, anchoredPredictor 0 M'.β₁ (M'.γ 2) (M'.β₂ 2) x ∂f = 6
    rw [integral_anchoredPredictor (integrable_coord_dirac _), covMean_dirac]
    simp [M', unsharedExampleModel, dotProduct]; norm_num
  · rw [hc]; simp [M, sharedExampleModel, dotProduct]; norm_num
  · rw [hc]; simp [M', unsharedExampleModel, dotProduct]; norm_num

/-- **The restriction of a second aggregate trial, on the two explicit models.** On the identity
scale with `a = 1`, `b = 2`, `c = 0`, aggregate trials over the point masses at `1` and at `0`
(intercepts `0`) and the individual data contrast `τ_ac(x) = η_1(x) - η_0(x) = 1 + 2x`: in
`sharedExampleModel` the difference of the reported contrasts is `2 = τ_ac(1) - τ_ac(0)`, as
`sharedEffectModifiers_iff_overidentifying` requires; in `unsharedExampleModel` it is `1`, so the
restriction fails and, by the same theorem, the effect modifiers are not shared. With a target
concentrated at `1`, the covariate mean of the first aggregate trial, the two models give the
same target effect `2`, as `linkConditional_eq_of_covMean_eq` requires. -/
theorem overidentifying_example :
    let f : Measure (Fin 1 → ℝ) := Measure.dirac fun _ => 1
    let f' : Measure (Fin 1 → ℝ) := Measure.dirac fun _ => 0
    let M := sharedExampleModel
    let M' := unsharedExampleModel
    linkConditional id f ((M.withIntercept 0).predictor 0) ((M.withIntercept 0).predictor 2) -
          linkConditional id f' ((M.withIntercept 0).predictor 0)
            ((M.withIntercept 0).predictor 2) =
        2 ∧
      (M.predictor 1 (covMean f) - M.predictor 0 (covMean f)) -
          (M.predictor 1 (covMean f') - M.predictor 0 (covMean f')) = 2 ∧
      linkConditional id f ((M'.withIntercept 0).predictor 0) ((M'.withIntercept 0).predictor 2) -
          linkConditional id f' ((M'.withIntercept 0).predictor 0)
            ((M'.withIntercept 0).predictor 2) = 1 ∧
      (M'.predictor 1 (covMean f) - M'.predictor 0 (covMean f)) -
          (M'.predictor 1 (covMean f') - M'.predictor 0 (covMean f')) = 2 ∧
      ¬ M'.SharedEffectModifiers {1, 2} ∧
      linkConditional id f (M'.predictor 1) (M'.predictor 2) =
        linkConditional id f (M.predictor 1) (M.predictor 2) ∧
      linkConditional id f (M.predictor 1) (M.predictor 2) = 2 := by
  intro f f' M M'
  obtain ⟨-, hS, -⟩ := sharedExampleModel_transport
  have hc : ∀ (N : AnchoredModel (Fin 3) 1) (y : Fin 1 → ℝ) (s t : Fin 3),
      linkConditional id (Measure.dirac y) (N.predictor s) (N.predictor t) =
        N.γ t - N.γ s + y ⬝ᵥ (N.β₂ t - N.β₂ s) := fun N y s t => by
    have h := linkConditional_predictor (g := id) (ginv := id) (fun _ => rfl) N
      (integrable_coord_dirac y) s t
    rw [covMean_dirac] at h
    exact h
  have hM := (sharedEffectModifiers_iff_overidentifying (g := id) (ginv := id) (fun _ => rfl)
    M 1 2 0).1 hS f f' (integrable_coord_dirac _) (integrable_coord_dirac _) 0 0
  have hτM : (M.predictor 1 (covMean f) - M.predictor 0 (covMean f)) -
      (M.predictor 1 (covMean f') - M.predictor 0 (covMean f')) = 2 := by
    simp [f, f', covMean_dirac, M, sharedExampleModel, predictor, anchoredPredictor]
  have hτM' : (M'.predictor 1 (covMean f) - M'.predictor 0 (covMean f)) -
      (M'.predictor 1 (covMean f') - M'.predictor 0 (covMean f')) = 2 := by
    simp [f, f', covMean_dirac, M', unsharedExampleModel, predictor, anchoredPredictor]
  have hdM' : linkConditional id f ((M'.withIntercept 0).predictor 0)
        ((M'.withIntercept 0).predictor 2) -
      linkConditional id f' ((M'.withIntercept 0).predictor 0) ((M'.withIntercept 0).predictor 2) =
        1 := by
    rw [hc, hc]; simp [M', unsharedExampleModel, withIntercept, dotProduct]
  have hd : linkConditional id f (fun x => (M'.withIntercept 0).predictor 0 x)
        (fun x => (M'.withIntercept 0).predictor 2 x) =
      linkConditional id f (fun x => (M.withIntercept 0).predictor 0 x)
        (fun x => (M.withIntercept 0).predictor 2 x) := by
    rw [hc, hc]
    simp [M, M', sharedExampleModel, unsharedExampleModel, withIntercept, dotProduct]
    norm_num
  have heq := linkConditional_eq_of_covMean_eq (g := id) (ginv := id) (fun _ => rfl)
    (M := M) (M' := M') (a := 1) (b := 2) (c := 0) (by funext x; rfl) (by funext x; rfl) 0 0
    (integrable_coord_dirac _) (integrable_coord_dirac _) hd rfl
  refine ⟨hM.trans hτM, hτM, hdM', hτM', fun hS' => ?_, heq, ?_⟩
  · have := (sharedEffectModifiers_iff_overidentifying (g := id) (ginv := id) (fun _ => rfl)
      M' 1 2 0).1 hS' f f' (integrable_coord_dirac _) (integrable_coord_dirac _) 0 0
    have h1 : linkConditional id f (fun x => id ((M'.withIntercept 0).predictor 0 x))
          (fun x => id ((M'.withIntercept 0).predictor 2 x)) -
        linkConditional id f' (fun x => id ((M'.withIntercept 0).predictor 0 x))
          (fun x => id ((M'.withIntercept 0).predictor 2 x)) = 1 := hdM'
    rw [h1, hτM'] at this
    norm_num at this
  · rw [hc]; simp [M, sharedExampleModel, dotProduct]; norm_num

/-- **The target effect under shared effect modifiers, on `sharedExampleModel`.** On the identity
scale with `a = 1`, `b = 2`, `c = 0`, the individual data at the design points `0, 1` (a full
column rank design) and an aggregate trial over the point mass at `1`, the hypotheses of
`linkConditional_eq_of_shared_of_design` hold for `sharedExampleModel` (anchored at `0`, with
shared effect modifiers for `{1, 2}`), and the target effect of `2` relative to `1` is
`γ_2 - γ_1 = 2` in every target with integrable coordinates. -/
theorem shared_of_design_example {Q : Measure (Fin 1 → ℝ)} [IsProbabilityMeasure Q]
    (hQ : ∀ k, Integrable (fun x => x k) Q) :
    linkConditional id Q (sharedExampleModel.predictor 1) (sharedExampleModel.predictor 2) = 2 := by
  obtain ⟨hA, hS, -⟩ := sharedExampleModel_transport
  have h := (linkConditional_eq_of_shared_of_design (g := id) (ginv := id) (fun _ => rfl)
    (M := sharedExampleModel) (M' := sharedExampleModel) (a := 1) (b := 2) (c := 0) hA hA hS hS
    linearIndependent_twoPointDesign linearIndependent_twoPointDesign
    (mc := sharedExampleModel.predictor 0) (ma := sharedExampleModel.predictor 1)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (f := Measure.dirac fun _ => 1) (integrable_coord_dirac _) 0 0 rfl hQ).2
  rw [show (sharedExampleModel.predictor 1) = fun x => id (sharedExampleModel.predictor 1 x)
    from rfl, show (sharedExampleModel.predictor 2) = fun x => id (sharedExampleModel.predictor 2 x)
    from rfl, h]
  simp [sharedExampleModel]; norm_num

end AnchoredModel

end IndirectComparison

end CausalInference
