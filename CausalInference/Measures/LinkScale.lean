/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Measures.Aggregation
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Conditional and marginal effects on a link scale

A covariate `X` with law `ν` (a probability measure) and two conditional mean functions
`a, b : X → ℝ`, the means of the outcome given `X = x` under a reference treatment and under an
active one. A link `g` (the identity, the logarithm, the logit) defines the effect scale.

* The **conditional effect** at `x` is `g (b x) - g (a x)` (`linkContrast`).
* The **marginal effect** is `g (∫ b dν) - g (∫ a dν)` (`linkMarginal`): the link applied to the
  population means.
* The **average conditional effect** is `∫ (g ∘ b - g ∘ a) dν` (`linkConditional`).

An effect measure is **collapsible** on its scale when a constant conditional effect is also the
marginal effect, for every covariate law (`LinkCollapsible`), and **directly collapsible** when
the marginal effect is always the average conditional effect (`LinkDirectlyCollapsible`). These
are the measure-theoretic forms of the finite-strata notions of `Measures/Collapsibility.lean`:
`stratumLaw π` turns stratum weights into a covariate law, `integral_stratumLaw` identifies its
integrals with `standardizedRisk`, and the bridges below recover the finite results. The
finite notions `IsCollapsible` and `IsCollapsibleOver` are statements about one table; the
predicates here quantify over all covariate laws and all mean functions with values in the
domain of the link.

## Main definitions

* `stratumLaw π`: the law `∑ v, π v δ_v` of a stratifier with finitely many levels.
* `linkContrast`, `linkMarginal`, `linkConditional`, `averagingGap`.
* `LinkCollapsible D g`, `LinkDirectlyCollapsible D g`: collapsibility on the scale `g` for
  means in `D`.

## Main results

* `linkMarginal_sub_linkConditional`: the marginal minus the average conditional effect is the
  difference `J_g(b) - J_g(a)` of the averaging gaps `J_g(m) = g (∫ m) - ∫ g ∘ m`;
  `averagingGap_affine` and `linkMarginal_eq_linkConditional_affine`: an affine link has no
  gap.
* `linkDirectlyCollapsible_id`, `linkCollapsible_id`: the risk difference (identity link) is
  directly collapsible. `linkCollapsible_log`: the risk ratio (log link, positive means) is
  collapsible. `integral_div_integral_eq_integral_mul_weight`: the marginal risk ratio is the
  average of the conditional risk ratios with the weights `a / ∫ a`.
* `not_linkDirectlyCollapsible_log`: the risk ratio is not directly collapsible, and
  `logRiskRatio_marginal_gt_example`, `logRiskRatio_marginal_lt_example` show that the marginal
  log risk ratio can lie on either side of the average conditional one.
* Bridges to the finite strata results: `riskDiff_marginal_eq_of_common_of_collapsible`,
  `riskRatio_marginal_eq_of_common_of_collapsible`, `riskRatio_eq_sum_rrWeight_of_weight`.

## References

* M. A. Hernán and J. M. Robins, *Causal Inference: What If* (2020), Fine Point 4.3 and
  Technical Point 4.3.
-/

@[expose] public section

open MeasureTheory

namespace CausalInference

namespace EffectMeasure

/-! ### The law of a stratifier with finitely many levels -/

section StratumLaw

variable {V : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]

/-- The law `∑ v, π v δ_v` of a stratifier whose level `v` has probability `π v`. -/
noncomputable def stratumLaw (π : V → ℝ) : Measure V :=
  ∑ v, ENNReal.ofReal (π v) • Measure.dirac v

/-- Every real function is integrable against `stratumLaw π`. -/
theorem integrable_stratumLaw (π : V → ℝ) (f : V → ℝ) : Integrable f (stratumLaw π) := by
  rw [stratumLaw]
  exact integrable_finsetSum_measure.2 fun v _ =>
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

/-- Integrals against `stratumLaw π` are standardized risks. -/
theorem integral_stratumLaw {π : V → ℝ} (hπ : ∀ v, 0 ≤ π v) (f : V → ℝ) :
    ∫ v, f v ∂(stratumLaw π) = standardizedRisk π f := by
  rw [stratumLaw, integral_finsetSum_measure]
  · refine Finset.sum_congr rfl fun v _ => ?_
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hπ v), smul_eq_mul]
  · intro v _
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

omit [MeasurableSingletonClass V] in
/-- Weights give a probability law. -/
theorem isProbabilityMeasure_stratumLaw {π : V → ℝ} (hπ : IsWeights π) :
    IsProbabilityMeasure (stratumLaw π) := by
  constructor
  simp only [stratumLaw, FunLike.coe_sum, Finset.sum_apply, smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun v _ => hπ.1 v), hπ.2, ENNReal.ofReal_one]

/-- A property holds `stratumLaw π`-almost surely if and only if it holds on every level of
positive probability. -/
theorem ae_stratumLaw_iff (π : V → ℝ) {P : V → Prop} :
    (∀ᵐ v ∂(stratumLaw π), P v) ↔ ∀ v, 0 < π v → P v := by
  rw [ae_iff, stratumLaw, FunLike.coe_sum, Finset.sum_apply, Finset.sum_eq_zero_iff]
  refine forall_congr' fun v => ?_
  simp only [Finset.mem_univ, true_implies, smul_apply, smul_eq_mul, mul_eq_zero,
    ENNReal.ofReal_eq_zero, Measure.dirac_apply, Set.indicator_apply_eq_zero, Pi.one_apply,
    one_ne_zero, imp_false, Set.mem_ofPred_eq, not_not]
  constructor
  · rintro (h | h) hv
    · linarith
    · exact h
  · intro h
    by_cases hv : 0 < π v
    · exact Or.inr (h hv)
    · exact Or.inl (not_lt.1 hv)

end StratumLaw

/-! ### Contrasts on a link scale -/

section Contrast

variable {X : Type*}

/-- The **conditional effect on the scale `g`** of the active mean `b` against the reference
mean `a` at `x`: `g (b x) - g (a x)`. -/
def linkContrast (g : ℝ → ℝ) (a b : X → ℝ) (x : X) : ℝ := g (b x) - g (a x)

variable [MeasurableSpace X]

/-- The **marginal effect on the scale `g`** under the covariate law `ν`: the link applied to the
two population means, `g (∫ b dν) - g (∫ a dν)`. -/
noncomputable def linkMarginal (g : ℝ → ℝ) (ν : Measure X) (a b : X → ℝ) : ℝ :=
  g (∫ x, b x ∂ν) - g (∫ x, a x ∂ν)

/-- The **average conditional effect on the scale `g`** under `ν`: `∫ (g (b x) - g (a x)) dν`. -/
noncomputable def linkConditional (g : ℝ → ℝ) (ν : Measure X) (a b : X → ℝ) : ℝ :=
  ∫ x, linkContrast g a b x ∂ν

/-- The **averaging gap** of a mean function `m` on the scale `g`:
`J_g(m) = g (∫ m dν) - ∫ g (m x) dν`, the error made by exchanging the link and the mean. -/
noncomputable def averagingGap (g : ℝ → ℝ) (ν : Measure X) (m : X → ℝ) : ℝ :=
  g (∫ x, m x ∂ν) - ∫ x, g (m x) ∂ν

/-- **The marginal and the average conditional effect differ by the averaging gaps**:
`marginal - conditional = J_g(b) - J_g(a)`. The means and their images under `g` are
integrable, so every integral is a genuine mean. -/
theorem linkMarginal_sub_linkConditional {g : ℝ → ℝ} {ν : Measure X} {a b : X → ℝ}
    (_ha : Integrable a ν) (_hb : Integrable b ν) (hga : Integrable (fun x => g (a x)) ν)
    (hgb : Integrable (fun x => g (b x)) ν) :
    linkMarginal g ν a b - linkConditional g ν a b = averagingGap g ν b - averagingGap g ν a := by
  simp only [linkMarginal, linkConditional, linkContrast, averagingGap]
  rw [integral_sub hgb hga]
  ring

variable {ν : Measure X} [IsProbabilityMeasure ν]

/-- **An affine link has no averaging gap**: for `g u = c u + d` and an integrable `m`,
`J_g(m) = 0`. -/
theorem averagingGap_affine {m : X → ℝ} (hm : Integrable m ν) (c d : ℝ) :
    averagingGap (fun u => c * u + d) ν m = 0 := by
  simp only [averagingGap]
  rw [integral_add (hm.const_mul c) (integrable_const d), integral_const_mul]
  simp

/-- **On an affine scale the marginal effect is the average conditional effect**, for every
covariate law and every pair of integrable mean functions. -/
theorem linkMarginal_eq_linkConditional_affine {a b : X → ℝ} (ha : Integrable a ν)
    (hb : Integrable b ν) (c d : ℝ) :
    linkMarginal (fun u => c * u + d) ν a b = linkConditional (fun u => c * u + d) ν a b := by
  have h := linkMarginal_sub_linkConditional (g := fun u => c * u + d) ha hb
    ((ha.const_mul c).add (integrable_const d)) ((hb.const_mul c).add (integrable_const d))
  rw [averagingGap_affine ha, averagingGap_affine hb, sub_zero] at h
  linarith

end Contrast

/-! ### Collapsibility on a link scale -/

/-- The effect measure on the scale `g`, for means in `D`, is **collapsible**: for every
covariate law `ν` and every pair of integrable mean functions with values almost surely in `D`
whose conditional effect is almost surely a constant `c`, the marginal effect is `c`. -/
def LinkCollapsible (D : Set ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν] (a b : X → ℝ),
    Integrable a ν → Integrable b ν → (∀ᵐ x ∂ν, a x ∈ D ∧ b x ∈ D) →
    ∀ c : ℝ, (∀ᵐ x ∂ν, linkContrast g a b x = c) → linkMarginal g ν a b = c

/-- The effect measure on the scale `g`, for means in `D`, is **directly collapsible**: for every
covariate law and every pair of integrable mean functions with values almost surely in `D` and an
integrable conditional effect, the marginal effect is the average conditional effect. -/
def LinkDirectlyCollapsible (D : Set ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν] (a b : X → ℝ),
    Integrable a ν → Integrable b ν → (∀ᵐ x ∂ν, a x ∈ D ∧ b x ∈ D) →
    Integrable (linkContrast g a b) ν → linkMarginal g ν a b = linkConditional g ν a b

/-- **Direct collapsibility implies collapsibility**: an almost surely constant conditional
effect is integrable, with average the constant. -/
theorem LinkDirectlyCollapsible.collapsible {D : Set ℝ} {g : ℝ → ℝ}
    (h : LinkDirectlyCollapsible D g) : LinkCollapsible D g := by
  intro X _ ν _ a b ha hb hD c hc
  have hi : Integrable (linkContrast g a b) ν := (integrable_congr hc).2 (integrable_const c)
  rw [h X ν a b ha hb hD hi, linkConditional, integral_congr_ae hc]
  simp

/-- **The risk difference is directly collapsible**: on the identity scale the marginal effect is
the average conditional effect. -/
theorem linkDirectlyCollapsible_id : LinkDirectlyCollapsible Set.univ id := by
  intro X _ ν _ a b ha hb _ _
  simp only [linkMarginal, linkConditional, linkContrast, id]
  rw [integral_sub hb ha]

/-- **The risk difference is collapsible.** -/
theorem linkCollapsible_id : LinkCollapsible Set.univ id :=
  linkDirectlyCollapsible_id.collapsible

/-- An almost surely positive integrable function has a positive mean under a probability law. -/
theorem integral_pos_of_ae_pos {X : Type*} [MeasurableSpace X] {ν : Measure X}
    [IsProbabilityMeasure ν] {f : X → ℝ} (hf : Integrable f ν) (h : ∀ᵐ x ∂ν, 0 < f x) :
    0 < ∫ x, f x ∂ν := by
  rw [integral_pos_iff_support_of_nonneg_ae (h.mono fun x hx => hx.le) hf]
  have hc : ν (Function.support f)ᶜ = 0 :=
    measure_mono_null (fun x hx => by simp_all) (ae_iff.1 h)
  have h1 : ν Set.univ ≤ ν (Function.support f) + ν (Function.support f)ᶜ := by
    rw [← Set.union_compl_self (Function.support f)]
    exact measure_union_le _ _
  rw [hc, add_zero, measure_univ] at h1
  exact lt_of_lt_of_le zero_lt_one h1

/-- **The risk ratio is collapsible**: on the log scale with positive means, a conditional log
risk ratio that is almost surely the constant `c` is also the marginal log risk ratio, for
every covariate law. -/
theorem linkCollapsible_log : LinkCollapsible (Set.Ioi 0) Real.log := by
  intro X _ ν _ a b ha hb hD c hc
  have hpos : 0 < ∫ x, a x ∂ν := integral_pos_of_ae_pos ha (hD.mono fun x hx => hx.1)
  have hrel : ∀ᵐ x ∂ν, b x = Real.exp c * a x := by
    filter_upwards [hD, hc] with x hx hcx
    simp only [linkContrast] at hcx
    rw [← hcx, Real.exp_sub, Real.exp_log hx.1, Real.exp_log hx.2]
    field_simp [(hx.1 : (0 : ℝ) < a x).ne']
  rw [linkMarginal, integral_congr_ae hrel, integral_const_mul,
    Real.log_mul (Real.exp_pos c).ne' hpos.ne', Real.log_exp]
  ring

/-- **The marginal risk ratio is a weighted average of the conditional risk ratios.** With
the weights `w x = a x / ∫ a dν`, which are almost surely nonnegative and integrate to one,
`(∫ b dν) / (∫ a dν) = ∫ (b x / a x) w x dν`, for an almost surely positive reference mean. -/
theorem integral_div_integral_eq_integral_mul_weight {X : Type*} [MeasurableSpace X]
    {ν : Measure X} [IsProbabilityMeasure ν] {a b : X → ℝ} (ha : Integrable a ν)
    (_hb : Integrable b ν) (hpos : ∀ᵐ x ∂ν, 0 < a x) :
    (∀ᵐ x ∂ν, 0 ≤ a x / ∫ y, a y ∂ν) ∧ ∫ x, a x / (∫ y, a y ∂ν) ∂ν = 1 ∧
      (∫ x, b x ∂ν) / (∫ x, a x ∂ν) = ∫ x, (b x / a x) * (a x / ∫ y, a y ∂ν) ∂ν := by
  have hm : 0 < ∫ y, a y ∂ν := integral_pos_of_ae_pos ha hpos
  refine ⟨hpos.mono fun x hx => div_nonneg hx.le hm.le, ?_, ?_⟩
  · rw [integral_div, div_self hm.ne']
  · have e : (fun x => (b x / a x) * (a x / ∫ y, a y ∂ν)) =ᵐ[ν] fun x => b x / ∫ y, a y ∂ν := by
      filter_upwards [hpos] with x hx
      field_simp [hx.ne']
    rw [integral_congr_ae e, integral_div]

/-! ### The log scale is not directly collapsible, in either direction -/

section LogRiskRatio

/-- The law of a binary stratifier with both levels of probability `1/2`. -/
noncomputable abbrev halfLaw : Measure Bool := stratumLaw fun _ => (1 / 2 : ℝ)

theorem isWeights_half : IsWeights (fun _ : Bool => (1 / 2 : ℝ)) :=
  ⟨fun _ => by norm_num, by simp⟩

instance : IsProbabilityMeasure halfLaw := isProbabilityMeasure_stratumLaw isWeights_half

/-- Integrals against `halfLaw` are averages of the two values. -/
theorem integral_halfLaw (f : Bool → ℝ) : ∫ v, f v ∂halfLaw = (f true + f false) / 2 := by
  rw [integral_stratumLaw (fun _ => by norm_num), standardizedRisk, Fintype.sum_bool]
  ring

/-- `halfLaw`-almost sure statements hold at both levels. -/
theorem ae_halfLaw_iff {P : Bool → Prop} : (∀ᵐ v ∂halfLaw, P v) ↔ ∀ v, P v := by
  rw [ae_stratumLaw_iff _]
  exact ⟨fun h v => h v (by norm_num), fun h v _ => h v⟩

/-- **The marginal log risk ratio above the average conditional one.** Reference risks `1/4` in
both strata, active risks `1/4` and `3/4` (conditional risk ratios `1` and `3`): the marginal log
risk ratio is `log 2`, the average conditional one is `log 3 / 2 < log 2`. -/
theorem logRiskRatio_marginal_gt_example :
    linkMarginal Real.log halfLaw (fun _ => 1 / 4) (fun v => if v then 3 / 4 else 1 / 4) =
        Real.log 2 ∧
      linkConditional Real.log halfLaw (fun _ => 1 / 4) (fun v => if v then 3 / 4 else 1 / 4) =
        Real.log 3 / 2 ∧
      Real.log 3 / 2 < Real.log 2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [linkMarginal, integral_halfLaw, integral_halfLaw, ← Real.log_div (by norm_num)
      (by norm_num)]
    norm_num
  · rw [linkConditional, integral_halfLaw]
    simp only [linkContrast, ite_true, Bool.false_eq_true, ite_false, sub_self, add_zero]
    rw [← Real.log_div (by norm_num) (by norm_num)]
    norm_num
  · have hlt : Real.log 3 < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    linarith

/-- **The marginal log risk ratio below the average conditional one.** Reference risks `9/10`
and `1/10`, conditional risk ratios `1/2` and `2` (active risks `9/20` and `1/5`): the average
conditional log risk ratio is `0`, while the marginal risk ratio is `13/20`, with negative
logarithm. So there is no general inequality between the marginal log risk ratio and the
average conditional one; the general statement is the weighted average identity
`integral_div_integral_eq_integral_mul_weight`. -/
theorem logRiskRatio_marginal_lt_example :
    linkMarginal Real.log halfLaw (fun v => if v then 9 / 10 else 1 / 10)
        (fun v => if v then 9 / 20 else 1 / 5) = Real.log (13 / 20) ∧
      linkConditional Real.log halfLaw (fun v => if v then 9 / 10 else 1 / 10)
        (fun v => if v then 9 / 20 else 1 / 5) = 0 ∧
      Real.log (13 / 20) < 0 := by
  refine ⟨?_, ?_, Real.log_neg (by norm_num) (by norm_num)⟩
  · rw [linkMarginal, integral_halfLaw, integral_halfLaw, ← Real.log_div (by norm_num)
      (by norm_num)]
    norm_num
  · rw [linkConditional, integral_halfLaw]
    simp only [linkContrast, ite_true, Bool.false_eq_true, ite_false]
    rw [← Real.log_div (by norm_num) (by norm_num), ← Real.log_div (by norm_num) (by norm_num)]
    have : Real.log (1 / 2) = -Real.log 2 := by
      rw [one_div, Real.log_inv]
    norm_num [this]

/-- **The risk ratio is not directly collapsible**: in `logRiskRatio_marginal_gt_example` the
marginal log risk ratio differs from the average conditional one. -/
theorem not_linkDirectlyCollapsible_log : ¬ LinkDirectlyCollapsible (Set.Ioi 0) Real.log := by
  intro h
  obtain ⟨h1, h2, h3⟩ := logRiskRatio_marginal_gt_example
  have key := h Bool halfLaw (fun _ => 1 / 4) (fun v => if v then 3 / 4 else 1 / 4)
    (integrable_stratumLaw _ _) (integrable_stratumLaw _ _)
    (ae_halfLaw_iff.2 fun v => by cases v <;> norm_num) (integrable_stratumLaw _ _)
  rw [h1, h2] at key
  linarith

end LogRiskRatio

/-! ### Bridges to the finite strata results -/

section Bridges

variable {V : Type} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]

/-- The finite strata `riskDiff_marginal_eq_of_common` (`Measures/Aggregation.lean`) is the
case `ν = stratumLaw π` of the collapsibility of the identity scale. -/
theorem riskDiff_marginal_eq_of_common_of_collapsible {π p₁ p₀ : V → ℝ} {δ : ℝ}
    (hπ : IsWeights π) (h : ∀ v, riskDiff (p₁ v) (p₀ v) = δ) :
    riskDiff (standardizedRisk π p₁) (standardizedRisk π p₀) = δ := by
  have := isProbabilityMeasure_stratumLaw hπ
  have := linkCollapsible_id V (stratumLaw π) p₀ p₁ (integrable_stratumLaw _ _)
    (integrable_stratumLaw _ _) (Filter.Eventually.of_forall fun _ => ⟨trivial, trivial⟩) δ
    (Filter.Eventually.of_forall fun v => h v)
  rwa [linkMarginal, integral_stratumLaw hπ.1, integral_stratumLaw hπ.1] at this

/-- The finite strata `riskRatio_marginal_eq_of_common` (`Measures/Aggregation.lean`) for
positive risks is the case `ν = stratumLaw π` of the collapsibility of the log scale. The
finite statement also allows a zero risk under treatment; here the stratum hypotheses are needed
only on the strata of positive weight. -/
theorem riskRatio_marginal_eq_of_common_of_collapsible {π p₁ p₀ : V → ℝ} {ρ : ℝ}
    (hπ : IsWeights π) (h₀ : ∀ v, 0 < π v → 0 < p₀ v) (h₁ : ∀ v, 0 < π v → 0 < p₁ v)
    (h : ∀ v, 0 < π v → riskRatio (p₁ v) (p₀ v) = ρ) :
    riskRatio (standardizedRisk π p₁) (standardizedRisk π p₀) = ρ := by
  have := isProbabilityMeasure_stratumLaw hπ
  obtain ⟨v₀, hv₀⟩ : ∃ v, 0 < π v := by
    by_contra hn
    push Not at hn
    have : ∑ v, π v = 0 := Finset.sum_eq_zero fun v _ => le_antisymm (hn v) (hπ.1 v)
    linarith [hπ.2]
  have hρ : 0 < ρ := by
    rw [← h v₀ hv₀]
    exact div_pos (h₁ v₀ hv₀) (h₀ v₀ hv₀)
  have hD : ∀ᵐ v ∂(stratumLaw π), p₀ v ∈ Set.Ioi 0 ∧ p₁ v ∈ Set.Ioi 0 :=
    (ae_stratumLaw_iff π).2 fun v hv => ⟨h₀ v hv, h₁ v hv⟩
  have hc : ∀ᵐ v ∂(stratumLaw π), linkContrast Real.log p₀ p₁ v = Real.log ρ := by
    refine (ae_stratumLaw_iff π).2 fun v hv => ?_
    rw [linkContrast, ← h v hv, riskRatio, Real.log_div (h₁ v hv).ne' (h₀ v hv).ne']
  have key := linkCollapsible_log V (stratumLaw π) p₀ p₁ (integrable_stratumLaw _ _)
    (integrable_stratumLaw _ _) hD _ hc
  rw [linkMarginal, integral_stratumLaw hπ.1, integral_stratumLaw hπ.1] at key
  have hP0 : 0 < standardizedRisk π p₀ := by
    rw [← integral_stratumLaw hπ.1]
    exact integral_pos_of_ae_pos (integrable_stratumLaw _ _) (hD.mono fun v hv => hv.1)
  have hP1 : 0 < standardizedRisk π p₁ := by
    rw [← integral_stratumLaw hπ.1]
    exact integral_pos_of_ae_pos (integrable_stratumLaw _ _) (hD.mono fun v hv => hv.2)
  rw [← Real.log_div hP1.ne' hP0.ne'] at key
  exact Real.log_injOn_pos (Set.mem_Ioi.2 (div_pos hP1 hP0)) (Set.mem_Ioi.2 hρ) key

/-- The finite strata `riskRatio_eq_sum_rrWeight` (`Measures/Collapsibility.lean`) is the case
`ν = stratumLaw π` of `integral_div_integral_eq_integral_mul_weight`. Here the baseline risks
need to be positive only on the strata of positive weight. -/
theorem riskRatio_eq_sum_rrWeight_of_weight {π p₁ p₀ : V → ℝ} (hπ : IsWeights π)
    (h₀ : ∀ v, 0 < π v → 0 < p₀ v) :
    riskRatio (standardizedRisk π p₁) (standardizedRisk π p₀) =
      ∑ v, rrWeight π p₀ v * riskRatio (p₁ v) (p₀ v) := by
  have := isProbabilityMeasure_stratumLaw hπ
  obtain ⟨-, -, h⟩ := integral_div_integral_eq_integral_mul_weight (ν := stratumLaw π)
    (a := p₀) (b := p₁) (integrable_stratumLaw _ _) (integrable_stratumLaw _ _)
    ((ae_stratumLaw_iff π).2 h₀)
  simp only [integral_stratumLaw hπ.1] at h
  rw [riskRatio, h, standardizedRisk]
  refine Finset.sum_congr rfl fun v _ => ?_
  rcases (hπ.1 v).eq_or_lt with hv | hv
  · simp [rrWeight, ← hv]
  · have := (h₀ v hv).ne'
    simp only [rrWeight, riskRatio]
    field_simp

end Bridges

end EffectMeasure

end CausalInference
