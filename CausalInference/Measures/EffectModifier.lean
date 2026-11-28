/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Measures.LinkScale

/-!
# Effect modifiers and prognostic variables

A covariate `X` with law `ν` and the conditional mean functions `a` (reference treatment) and
`b` (active treatment). On the scale of a link `g`:

* `X` is an **effect modifier** when the conditional effect `g (b X) - g (a X)` is not almost
  surely constant (`IsEffectModifier ν g a b`);
* `X` is **prognostic** for an arm with mean `m` when `m X` is not almost surely constant
  (`IsPrognostic ν m`).

The pointwise forms, for covariates split into `x` and `w`, ask whether the conditional effect,
or the mean, at `(x, w)` depends on `w` (`ModifiesEffectPointwise`, `IsPrognosticPointwise`).

## Main definitions

* `IsEffectModifier`, `IsPrognostic`, `ModifiesEffectPointwise`, `IsPrognosticPointwise`.
* `interactionPredictor α γ β₁ β₂ t x = α + xᵀβ₁ + t (γ + xᵀβ₂)`: the linear predictor of a
  regression model with treatment by covariate interactions; `StatisticalInteraction`.

## Main results

* `isPrognostic_or_of_isEffectModifier`: an effect modifier is prognostic for one of the arms.
* `prognostic_not_effectModifier_example`, `effectModifier_not_prognostic_example`: neither
  notion implies the other, on a binary covariate with both levels of probability `1/2`.
* `not_isEffectModifier_of_not_modifiesEffectPointwise` and
  `not_modifiesEffectPointwise_of_not_isEffectModifier`: the pointwise and the almost sure
  definitions agree when every value of `w` has positive probability.
* `isEffectModifier_stratumLaw_iff`, `isEffectModifier_id_iff_additiveModification`,
  `isEffectModifier_log_iff_multiplicativeModification`: for a stratifier with finitely many
  levels of positive probability, an effect modifier on the identity scale is additive effect
  modification and on the log scale multiplicative effect modification
  (`Measures/Collapsibility.lean`).
* `integral_linkContrast_eq_integral_map_fst`: if `w` does not modify the effect, the average
  conditional effect is an integral against the law of `x` alone.
* `not_isPrognostic_of_not_isPrognosticPointwise`, `not_isPrognosticPointwise_of_not_isPrognostic`:
  the same agreement for prognostic variables.
* `integral_linkContrast_eq_of_map_fst_eq`: if `w` does not modify the effect on the scale `g`,
  two populations with the same law of `x` have the same average conditional effect, however
  differently `w` is distributed in them; `integral_linkContrast_eq_of_forall_eq` is the case of
  a fixed `x`.
* `linkContrast_interactionPredictor`, `exists_update_linkContrast_ne_iff`,
  `not_isEffectModifier_of_interaction_eq_zero`, `statisticalInteraction_iff`: in a model with
  linear predictor `interactionPredictor` on the scale `g`, the conditional effect is
  `γ + xᵀβ₂`, the covariate `x_j` modifies the effect if and only if `β₂ j ≠ 0`, and without
  interactions no covariate law makes `x` an effect modifier.

## References

* M. A. Hernán and J. M. Robins, *Causal Inference: What If* (2020), Section 4.1.
-/

@[expose] public section

open MeasureTheory

namespace CausalInference

namespace EffectMeasure

/-! ### Almost sure definitions -/

section AlmostSure

variable {X : Type*} [MeasurableSpace X]

/-- `X` is an **effect modifier** of the active mean `b` against the reference mean `a` on the
scale `g` under the covariate law `ν`: the conditional effect `g (b X) - g (a X)` is not
`ν`-almost surely constant. -/
def IsEffectModifier (ν : Measure X) (g : ℝ → ℝ) (a b : X → ℝ) : Prop :=
  ¬ ∃ c : ℝ, ∀ᵐ x ∂ν, linkContrast g a b x = c

/-- `X` is **prognostic** for an arm with conditional mean `m` under the covariate law `ν`:
`m X` is not `ν`-almost surely constant. -/
def IsPrognostic (ν : Measure X) (m : X → ℝ) : Prop :=
  ¬ ∃ c : ℝ, ∀ᵐ x ∂ν, m x = c

/-- **An effect modifier is prognostic for at least one arm**, on every scale: if both means are
almost surely constant, so is the conditional effect. -/
theorem isPrognostic_or_of_isEffectModifier {ν : Measure X} {g : ℝ → ℝ} {a b : X → ℝ}
    (h : IsEffectModifier ν g a b) : IsPrognostic ν a ∨ IsPrognostic ν b := by
  by_contra hn
  simp only [not_or, IsPrognostic, not_not] at hn
  obtain ⟨⟨ca, ha⟩, ⟨cb, hb⟩⟩ := hn
  refine h ⟨g cb - g ca, ?_⟩
  filter_upwards [ha, hb] with x hxa hxb
  simp [linkContrast, hxa, hxb]

end AlmostSure

/-! ### Finitely many strata -/

section Strata

variable {V : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]

/-- Under `stratumLaw π`, a function is almost surely constant exactly when it is constant on
the levels of positive probability. -/
theorem exists_ae_eq_const_stratumLaw_iff_of_pos (π : V → ℝ) {f : V → ℝ} :
    (∃ c, ∀ᵐ v ∂(stratumLaw π), f v = c) ↔ ∀ v w, 0 < π v → 0 < π w → f v = f w := by
  simp only [ae_stratumLaw_iff]
  constructor
  · rintro ⟨c, hc⟩ v w hv hw
    rw [hc v hv, hc w hw]
  · intro h
    by_cases hex : ∃ v, 0 < π v
    · obtain ⟨v₀, hv₀⟩ := hex
      exact ⟨f v₀, fun v hv => h v v₀ hv hv₀⟩
    · push Not at hex
      exact ⟨0, fun v hv => absurd hv (not_lt.2 (hex v))⟩

/-- Under `stratumLaw π` with every level of positive probability, a function is almost surely
constant exactly when it is constant. -/
theorem exists_ae_eq_const_stratumLaw_iff {π : V → ℝ} (hπ : ∀ v, 0 < π v) {f : V → ℝ} :
    (∃ c, ∀ᵐ v ∂(stratumLaw π), f v = c) ↔ ∀ v w, f v = f w := by
  rw [exists_ae_eq_const_stratumLaw_iff_of_pos]
  exact ⟨fun h v w => h v w (hπ v) (hπ w), fun h v w _ _ => h v w⟩

/-- Under `stratumLaw π`, a prognostic stratifier is one whose mean takes two different values
on levels of positive probability. -/
theorem isPrognostic_stratumLaw_iff_of_pos (π : V → ℝ) {m : V → ℝ} :
    IsPrognostic (stratumLaw π) m ↔ ∃ v w, 0 < π v ∧ 0 < π w ∧ m v ≠ m w := by
  rw [IsPrognostic, exists_ae_eq_const_stratumLaw_iff_of_pos]
  push Not
  rfl

/-- For a stratifier whose levels all have positive probability, an effect modifier on the scale
`g` is a stratifier on which the conditional effect varies. -/
theorem isEffectModifier_stratumLaw_iff {π : V → ℝ} (hπ : ∀ v, 0 < π v) {g : ℝ → ℝ}
    {a b : V → ℝ} :
    IsEffectModifier (stratumLaw π) g a b ↔ ∃ v w, linkContrast g a b v ≠ linkContrast g a b w := by
  rw [IsEffectModifier, exists_ae_eq_const_stratumLaw_iff hπ]
  push Not
  rfl

/-- For a stratifier whose levels all have positive probability, a prognostic stratifier is one
on which the mean varies. -/
theorem isPrognostic_stratumLaw_iff {π : V → ℝ} (hπ : ∀ v, 0 < π v) {m : V → ℝ} :
    IsPrognostic (stratumLaw π) m ↔ ∃ v w, m v ≠ m w := by
  rw [IsPrognostic, exists_ae_eq_const_stratumLaw_iff hπ]
  push Not
  rfl

/-- **An effect modifier on the identity scale is additive effect modification**
(`AdditiveModification`, `Measures/Collapsibility.lean`), for strata of positive probability. -/
theorem isEffectModifier_id_iff_additiveModification {π : V → ℝ} (hπ : ∀ v, 0 < π v)
    {p₁ p₀ : V → ℝ} : IsEffectModifier (stratumLaw π) id p₀ p₁ ↔ AdditiveModification p₁ p₀ := by
  rw [isEffectModifier_stratumLaw_iff hπ]
  rfl

/-- **An effect modifier on the log scale is multiplicative effect modification**
(`MultiplicativeModification`, `Measures/Collapsibility.lean`), for strata of positive
probability and positive risks. -/
theorem isEffectModifier_log_iff_multiplicativeModification {π : V → ℝ} (hπ : ∀ v, 0 < π v)
    {p₁ p₀ : V → ℝ} (h₀ : ∀ v, 0 < p₀ v) (h₁ : ∀ v, 0 < p₁ v) :
    IsEffectModifier (stratumLaw π) Real.log p₀ p₁ ↔ MultiplicativeModification p₁ p₀ := by
  have hlog : ∀ v, linkContrast Real.log p₀ p₁ v = Real.log (riskRatio (p₁ v) (p₀ v)) := fun v => by
    rw [linkContrast, riskRatio, Real.log_div (h₁ v).ne' (h₀ v).ne']
  have hrr : ∀ v, 0 < riskRatio (p₁ v) (p₀ v) := fun v => div_pos (h₁ v) (h₀ v)
  rw [isEffectModifier_stratumLaw_iff hπ, MultiplicativeModification]
  simp only [hlog]
  constructor
  · rintro ⟨v, w, h⟩
    exact ⟨v, w, h₀ v, h₀ w, fun e => h (by rw [e])⟩
  · rintro ⟨v, w, -, -, h⟩
    exact ⟨v, w, fun e => h (Real.log_injOn_pos (hrr v) (hrr w) e)⟩

end Strata

/-! ### Neither notion implies the other -/

/-- **A prognostic variable need not modify the effect.** On a binary covariate with both levels
of probability `1/2`, the means `3/10` and `7/10` in both arms: the covariate is prognostic for
both arms and is an effect modifier on no scale. -/
theorem prognostic_not_effectModifier_example (g : ℝ → ℝ) :
    let m : Bool → ℝ := fun v => if v then 7 / 10 else 3 / 10
    IsPrognostic halfLaw m ∧ ¬ IsEffectModifier halfLaw g m m := by
  intro m
  have hπ : ∀ v : Bool, 0 < (fun _ => (1 / 2 : ℝ)) v := fun _ => by norm_num
  refine ⟨(isPrognostic_stratumLaw_iff hπ).2 ⟨true, false, by norm_num [m]⟩, ?_⟩
  rw [isEffectModifier_stratumLaw_iff hπ]
  rintro ⟨v, w, h⟩
  simp [linkContrast] at h

/-- **An effect modifier need not be prognostic for a given arm.** On a binary covariate with
both levels of probability `1/2`, the reference mean `4/10` in both strata and the active means
`7/10` and `4/10`: the covariate modifies the effect on the identity scale and is not prognostic
for the reference arm. -/
theorem effectModifier_not_prognostic_example :
    IsEffectModifier halfLaw id (fun _ => 4 / 10) (fun v => if v then 7 / 10 else 4 / 10) ∧
      ¬ IsPrognostic halfLaw (fun _ => (4 / 10 : ℝ)) := by
  have hπ : ∀ v : Bool, 0 < (fun _ => (1 / 2 : ℝ)) v := fun _ => by norm_num
  refine ⟨(isEffectModifier_stratumLaw_iff hπ).2 ⟨true, false, by norm_num [linkContrast]⟩, ?_⟩
  rw [isPrognostic_stratumLaw_iff hπ]
  rintro ⟨v, w, h⟩
  exact h rfl

/-! ### Pointwise definitions -/

section Pointwise

variable {X W : Type*}

/-- `w` **modifies the effect pointwise** on the scale `g`, for means `a x w` and `b x w`
indexed by the covariates `(x, w)`: for some `x` the conditional effect at `(x, w)` takes two
different values as `w` varies. -/
def ModifiesEffectPointwise (g : ℝ → ℝ) (a b : X → W → ℝ) : Prop :=
  ∃ x w w', linkContrast g (a x) (b x) w ≠ linkContrast g (a x) (b x) w'

/-- `w` is **prognostic pointwise** for an arm with mean `m x w`: for some `x` the mean takes
two different values as `w` varies. -/
def IsPrognosticPointwise (m : X → W → ℝ) : Prop := ∃ x w w', m x w ≠ m x w'

variable [MeasurableSpace W] {g : ℝ → ℝ} {a b : X → W → ℝ}

/-- **Pointwise implies almost sure**: if `w` does not modify the effect pointwise, then for every
`x` and every law of `w` it is not an effect modifier. -/
theorem not_isEffectModifier_of_not_modifiesEffectPointwise
    (h : ¬ ModifiesEffectPointwise g a b) (x : X) (ν : Measure W) :
    ¬ IsEffectModifier ν g (a x) (b x) := by
  simp only [ModifiesEffectPointwise, not_exists, not_not] at h
  intro hEM
  rcases isEmpty_or_nonempty W with hW | ⟨⟨w₀⟩⟩
  · exact hEM ⟨0, Filter.Eventually.of_forall fun w => isEmptyElim w⟩
  · exact hEM ⟨_, Filter.Eventually.of_forall fun w => h x w w₀⟩

/-- An almost sure equality holds at every point of positive mass. -/
theorem eq_of_ae_eq_of_measure_singleton_ne_zero {ν : Measure W} {f : W → ℝ} {c : ℝ}
    (h : ∀ᵐ w ∂ν, f w = c) {w : W} (hw : ν {w} ≠ 0) : f w = c := by
  by_contra hne
  exact hw (measure_mono_null (fun y hy => by simp_all) (ae_iff.1 h))

/-- **Almost sure implies pointwise when every value of `w` has positive mass**: if for every `x`
the covariate `w` is not an effect modifier under a law `ν` that charges every point, then `w`
does not modify the effect pointwise. -/
theorem not_modifiesEffectPointwise_of_not_isEffectModifier {ν : Measure W}
    (hν : ∀ w, ν {w} ≠ 0) (h : ∀ x, ¬ IsEffectModifier ν g (a x) (b x)) :
    ¬ ModifiesEffectPointwise g a b := by
  rintro ⟨x, w, w', hne⟩
  obtain ⟨c, hc⟩ := not_not.1 (h x)
  exact hne ((eq_of_ae_eq_of_measure_singleton_ne_zero hc (hν w)).trans
    (eq_of_ae_eq_of_measure_singleton_ne_zero hc (hν w')).symm)

variable {m : X → W → ℝ}

/-- **Pointwise implies almost sure, for prognostic variables**: if `w` is not prognostic
pointwise, then for every `x` and every law of `w` it is not prognostic. -/
theorem not_isPrognostic_of_not_isPrognosticPointwise (h : ¬ IsPrognosticPointwise m) (x : X)
    (ν : Measure W) : ¬ IsPrognostic ν (m x) := by
  simp only [IsPrognosticPointwise, not_exists, not_not] at h
  intro hP
  rcases isEmpty_or_nonempty W with hW | ⟨⟨w₀⟩⟩
  · exact hP ⟨0, Filter.Eventually.of_forall fun w => isEmptyElim w⟩
  · exact hP ⟨_, Filter.Eventually.of_forall fun w => h x w w₀⟩

/-- **Almost sure implies pointwise when every value of `w` has positive mass**, for prognostic
variables. -/
theorem not_isPrognosticPointwise_of_not_isPrognostic {ν : Measure W} (hν : ∀ w, ν {w} ≠ 0)
    (h : ∀ x, ¬ IsPrognostic ν (m x)) : ¬ IsPrognosticPointwise m := by
  rintro ⟨x, w, w', hne⟩
  obtain ⟨c, hc⟩ := not_not.1 (h x)
  exact hne ((eq_of_ae_eq_of_measure_singleton_ne_zero hc (hν w)).trans
    (eq_of_ae_eq_of_measure_singleton_ne_zero hc (hν w')).symm)

end Pointwise

/-! ### A variable that does not modify the effect cancels from the average effect -/

section Cancellation

variable {X W : Type*} [MeasurableSpace X] [MeasurableSpace W] {g : ℝ → ℝ}

/-- **The average effect only sees the law of `x`** when the conditional effect on the scale `g`
at `(x, w)` is a measurable function that does not depend on `w`: for any `w₀`, its average under
a joint law `P` of `(x, w)` is the average of `x ↦ g (b (x, w₀)) - g (a (x, w₀))` under the law
of `x`. -/
theorem integral_linkContrast_eq_integral_map_fst {a b : X × W → ℝ}
    (h : ∀ x w w', linkContrast g a b (x, w) = linkContrast g a b (x, w'))
    (hm : Measurable (linkContrast g a b)) (P : Measure (X × W)) (w₀ : W) :
    ∫ p, linkContrast g a b p ∂P = ∫ x, linkContrast g a b (x, w₀) ∂(P.map Prod.fst) := by
  have hτ : Measurable fun x => linkContrast g a b (x, w₀) := hm.comp measurable_prodMk_right
  have hconst : linkContrast g a b = fun p => linkContrast g a b (p.1, w₀) :=
    funext fun p => h p.1 p.2 w₀
  rw [integral_map measurable_fst.aemeasurable hτ.aestronglyMeasurable]
  conv_lhs => rw [hconst]

/-- **Average effects do not see the law of a variable that does not modify the effect.** Let
the conditional effect on the scale `g` at `(x, w)` be a measurable function that does not depend
on `w`. Two populations, joint laws `P₁` and `P₂` of `(x, w)`, with the same law of `x` have the
same average conditional effect, however differently `w` is distributed given `x`; and the
conditional effect is integrable under `P₂` as soon as it is under `P₁`. -/
theorem integral_linkContrast_eq_of_map_fst_eq {a b : X × W → ℝ}
    (h : ∀ x w w', linkContrast g a b (x, w) = linkContrast g a b (x, w'))
    (hm : Measurable (linkContrast g a b)) {P₁ P₂ : Measure (X × W)}
    (hint : Integrable (linkContrast g a b) P₁) (hX : P₁.map Prod.fst = P₂.map Prod.fst) :
    Integrable (linkContrast g a b) P₂ ∧
      ∫ p, linkContrast g a b p ∂P₁ = ∫ p, linkContrast g a b p ∂P₂ := by
  rcases isEmpty_or_nonempty W with hW | ⟨⟨w₀⟩⟩
  · have e₁ : P₁ = 0 := Measure.eq_zero_of_isEmpty P₁
    have e₂ : P₂ = 0 := Measure.eq_zero_of_isEmpty P₂
    subst e₁ e₂
    exact ⟨integrable_zero_measure, rfl⟩
  set τ : X → ℝ := fun x => linkContrast g a b (x, w₀)
  have hτ : Measurable τ := hm.comp measurable_prodMk_right
  have hconst : linkContrast g a b = fun p => τ p.1 := funext fun p => h p.1 p.2 w₀
  rw [hconst] at hint ⊢
  have hi₁ : Integrable τ (P₁.map Prod.fst) :=
    (integrable_map_measure hτ.aestronglyMeasurable measurable_fst.aemeasurable).2 hint
  rw [hX] at hi₁
  refine ⟨(integrable_map_measure hτ.aestronglyMeasurable measurable_fst.aemeasurable).1 hi₁, ?_⟩
  rw [← integral_map measurable_fst.aemeasurable hτ.aestronglyMeasurable, hX,
    integral_map measurable_fst.aemeasurable hτ.aestronglyMeasurable]

/-- **The case of a fixed `x`.** If the conditional effect `g (b w) - g (a w)` does not depend on
`w`, its average is the same under any two probability laws of `w`, for instance the laws of `w`
given `x` in two populations. -/
theorem integral_linkContrast_eq_of_forall_eq {a b : W → ℝ}
    (h : ∀ w w', linkContrast g a b w = linkContrast g a b w') (ν ν' : Measure W)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ν'] :
    ∫ w, linkContrast g a b w ∂ν = ∫ w, linkContrast g a b w ∂ν' := by
  obtain ⟨w₀⟩ := nonempty_of_isProbabilityMeasure ν
  have hconst : linkContrast g a b = fun _ => linkContrast g a b w₀ := funext fun w => h w w₀
  rw [hconst, integral_const, integral_const, probReal_univ, probReal_univ]

end Cancellation

/-! ### Regression models with treatment by covariate interactions -/

section Interaction

variable {p : ℕ}

/-- The linear predictor `α + xᵀβ₁ + t (γ + xᵀβ₂)` of a regression model with main effects `β₁`,
treatment effect `γ` and treatment by covariate interactions `β₂`; `t = true` is the active
treatment. -/
def interactionPredictor (α γ : ℝ) (β₁ β₂ : Fin p → ℝ) (t : Bool) (x : Fin p → ℝ) : ℝ :=
  α + ∑ j, x j * β₁ j + if t then γ + ∑ j, x j * β₂ j else 0

theorem interactionPredictor_sub (α γ : ℝ) (β₁ β₂ x : Fin p → ℝ) :
    interactionPredictor α γ β₁ β₂ true x - interactionPredictor α γ β₁ β₂ false x =
      γ + ∑ j, x j * β₂ j := by
  simp [interactionPredictor]

/-- Moving the component `x_j` to `s` changes `γ + xᵀβ₂` by `(s - x_j) β₂ j`. -/
theorem interaction_update_sub (γ : ℝ) (β₂ x : Fin p → ℝ) (j : Fin p) (s : ℝ) :
    (γ + ∑ k, Function.update x j s k * β₂ k) - (γ + ∑ k, x k * β₂ k) = (s - x j) * β₂ j := by
  have hk : ∀ k, (Function.update x j s k - x k) * β₂ k =
      if k = j then (s - x j) * β₂ j else 0 := by
    intro k
    by_cases h : k = j
    · subst h
      simp
    · simp [h]
  rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  simp only [← sub_mul, hk, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

variable {g : ℝ → ℝ} {μ : Bool → (Fin p → ℝ) → ℝ} {α γ : ℝ} {β₁ β₂ : Fin p → ℝ}

/-- **The conditional effect in the interaction model**: if `g (μ t x)` is the linear predictor
`α + xᵀβ₁ + t (γ + xᵀβ₂)`, the conditional effect on the scale `g` is `γ + xᵀβ₂`. -/
theorem linkContrast_interactionPredictor
    (hmodel : ∀ t x, g (μ t x) = interactionPredictor α γ β₁ β₂ t x) (x : Fin p → ℝ) :
    linkContrast g (μ false) (μ true) x = γ + ∑ j, x j * β₂ j := by
  simp only [linkContrast, hmodel]
  exact interactionPredictor_sub α γ β₁ β₂ x

/-- **A component modifies the effect exactly when its interaction is nonzero.** In the
interaction model, if the component `x_j` can move inside the set `S` with the other components
fixed, then moving `x_j` inside `S` changes the conditional effect for some `x ∈ S` if and only if
`β₂ j ≠ 0`. -/
theorem exists_update_linkContrast_ne_iff
    (hmodel : ∀ t x, g (μ t x) = interactionPredictor α γ β₁ β₂ t x) (j : Fin p)
    {S : Set (Fin p → ℝ)} (hvar : ∃ x ∈ S, ∃ s, s ≠ x j ∧ Function.update x j s ∈ S) :
    (∃ x ∈ S, ∃ s, Function.update x j s ∈ S ∧
      linkContrast g (μ false) (μ true) (Function.update x j s) ≠
        linkContrast g (μ false) (μ true) x) ↔ β₂ j ≠ 0 := by
  simp only [linkContrast_interactionPredictor hmodel]
  constructor
  · rintro ⟨x, -, s, -, hne⟩ h0
    apply hne
    have := interaction_update_sub γ β₂ x j s
    rw [h0, mul_zero] at this
    linarith
  · intro h0
    obtain ⟨x, hx, s, hs, hxs⟩ := hvar
    refine ⟨x, hx, s, hxs, fun heq => ?_⟩
    have := interaction_update_sub γ β₂ x j s
    rw [heq, sub_self] at this
    rcases mul_eq_zero.1 this.symm with h | h
    · exact hs (sub_eq_zero.1 h)
    · exact h0 h

/-- **No interaction, no effect modification**: in the interaction model with `β₂ = 0` the
conditional effect is the constant `γ`, so under no covariate law is `x` an effect modifier on
the scale `g`. -/
theorem not_isEffectModifier_of_interaction_eq_zero
    (hmodel : ∀ t x, g (μ t x) = interactionPredictor α γ β₁ β₂ t x) (h0 : β₂ = 0)
    (ν : Measure (Fin p → ℝ)) : ¬ IsEffectModifier ν g (μ false) (μ true) := by
  refine fun h => h ⟨γ, Filter.Eventually.of_forall fun x => ?_⟩
  rw [linkContrast_interactionPredictor hmodel, h0]
  simp

/-- A **statistical interaction** between treatment and the component `x_j` in a model with
linear predictor `η t x`: a departure from additivity in `t` and `x_j`, that is, a nonzero
interaction contrast `[η 1 x' - η 0 x'] - [η 1 x - η 0 x]` for some `x` and some `x'` that
differs from `x` only in the component `j`. -/
def StatisticalInteraction (η : Bool → (Fin p → ℝ) → ℝ) (j : Fin p) : Prop :=
  ∃ x s, η true (Function.update x j s) - η false (Function.update x j s) -
    (η true x - η false x) ≠ 0

/-- **In the interaction model a statistical interaction is a nonzero coefficient**: the
predictor `α + xᵀβ₁ + t (γ + xᵀβ₂)` departs from additivity in `t` and `x_j` if and only if
`β₂ j ≠ 0`. -/
theorem statisticalInteraction_iff (j : Fin p) :
    StatisticalInteraction (interactionPredictor α γ β₁ β₂) j ↔ β₂ j ≠ 0 := by
  simp only [StatisticalInteraction, interactionPredictor_sub, interaction_update_sub]
  constructor
  · rintro ⟨x, s, h⟩ h0
    rw [h0, mul_zero] at h
    exact h rfl
  · intro h0
    exact ⟨0, 1, by simpa using h0⟩

end Interaction

end EffectMeasure

end CausalInference
