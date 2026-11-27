/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Measures.Collapsibility
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Aggregation bias and noncollapsibility

A binary treatment, a binary outcome and a stratifier `V` with finitely many levels, as in
`Measures/Collapsibility.lean`: stratum weights `π` (the same in both arms, so the stratifier is
independent of treatment, as randomization gives), stratum baseline risks `p₀ v` and stratum
risks under treatment `p₁ v`. The marginal risks are the standardized risks `∑ π p`.

TSD 3, Section 1.1.5 ("Aggregation bias") states that a covariate that modifies the baseline
risk but not the treatment effect biases the pooled effect toward the null on nonlinear scales
and not on linear ones. This file proves the precise form of the claim for the odds ratio,
shows which hypotheses it needs, and corrects it for the log scale.

## Main definitions

* `riskOfOddsRatio ψ p = ψ p / (1 + (ψ - 1) p)`: the risk with odds ratio `ψ` against `p`.
* `aggregationGap ψ π p`: the weighted dispersion of the baseline risks that measures the bias.
* `collapsedRisk q a b = q a + (1 - q) b`: the risk of a trial arm with a proportion `q` of men.

## Main results

* `riskOfOddsRatio_sub_standardizedRisk`: the exact identity
  `f(∑ π p) - ∑ π f(p) = (ψ - 1) ψ G` with `f = riskOfOddsRatio ψ`, `G = aggregationGap ψ π p`.
* `oddsRatio_marginal_mem_Ioo_of_one_lt`, `oddsRatio_marginal_mem_Ioo_of_lt_one`: with a
  common stratum odds ratio `ψ`, the stratifier independent of treatment, and a baseline risk
  that varies on strata of positive weight, the marginal odds ratio lies strictly between `1`
  and `ψ` (aggregation bias toward the null, TSD 3, Section 1.1.5).
* `table44_marginal_oddsRatio_mem_Ioo`: Table 4.4 of Hernán and Robins is an instance.
* Countermodels, one per hypothesis: `oddsRatio_marginal_eq_of_const` (no variation of the
  baseline risk on the support: no bias) and `oddsRatio_marginal_confounded` (stratifier
  associated with treatment: the marginal odds ratio `203/55` exceeds the common `2`).
* `riskDiff_marginal_eq_of_common`, `riskRatio_marginal_eq_of_common`: a common risk difference
  and a common risk ratio survive pooling. The second corrects the document, which says that
  aggregation bias affects log models: for binomial risks it does not.
* Collapsed category data (TSD 3, Section 1.1.4): `riskDiff_collapsedRisk` (identity link,
  the trial effect is affine in the proportion of men, so the model is exact),
  `log_riskRatio_collapsedRisk_of_common` (log link with a common risk ratio: exact), and
  `log_riskRatio_collapsedRisk_not_affine` (log link with an interaction: no affine model fits).
  So the failure on the log scale needs effect modification; the claim "not valid for logit,
  log or other commonly used models" holds for the log link only in that case.

## References

* S. Dias, A. J. Sutton, N. J. Welton, A. E. Ades, *NICE DSU Technical Support Document 3:
  Heterogeneity: Subgroups, Meta-Regression, Bias and Bias-Adjustment* (2011, updated 2012),
  Sections 1.1.4 and 1.1.5.
* M. A. Hernán and J. M. Robins, *Causal Inference: What If* (2020), Fine Point 4.3,
  Table 4.4.
-/

@[expose] public section

namespace CausalInference

namespace EffectMeasure

open Finset

variable {V : Type*} [Fintype V]

/-- The risk under treatment implied by the baseline risk `p` and the odds ratio `ψ`:
`ψ p / (1 + (ψ - 1) p)`, the solution `p₁` of `odds p₁ = ψ odds p`. -/
noncomputable def riskOfOddsRatio (ψ p : ℝ) : ℝ := ψ * p / (1 + (ψ - 1) * p)

theorem riskOfOddsRatio_denom_pos {ψ p : ℝ} (hψ : 0 < ψ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 < 1 + (ψ - 1) * p := by
  rcases hp0.eq_or_lt with h | h
  · rw [← h]; norm_num
  · nlinarith [mul_pos hψ h]

/-- A risk `p₁ < 1` has odds ratio `ψ` against a baseline risk `p ∈ (0, 1)` exactly when
`p₁ = riskOfOddsRatio ψ p`. -/
theorem eq_riskOfOddsRatio {p₁ p ψ : ℝ} (h₁ : p₁ < 1) (h0 : 0 < p) (h1 : p < 1) (hψ : 0 < ψ)
    (h : oddsRatio p₁ p = ψ) : p₁ = riskOfOddsRatio ψ p := by
  have hD := riskOfOddsRatio_denom_pos hψ h0.le h1.le
  rw [oddsRatio_eq_cross h₁ h0 h1, div_eq_iff (by nlinarith)] at h
  rw [riskOfOddsRatio, eq_div_iff hD.ne']
  linarith

theorem riskOfOddsRatio_lt_one {ψ p : ℝ} (hψ : 0 < ψ) (h0 : 0 ≤ p) (h1 : p < 1) :
    riskOfOddsRatio ψ p < 1 := by
  have hD := riskOfOddsRatio_denom_pos hψ h0 h1.le
  rw [riskOfOddsRatio, div_lt_one hD]
  linarith

theorem odds_riskOfOddsRatio {ψ p : ℝ} (hψ : 0 < ψ) (h0 : 0 ≤ p) (h1 : p < 1) :
    odds (riskOfOddsRatio ψ p) = ψ * odds p := by
  have hD := riskOfOddsRatio_denom_pos hψ h0 h1.le
  have : (1 : ℝ) - p ≠ 0 := by linarith
  have hD' := hD.ne'
  unfold odds riskOfOddsRatio
  rw [one_sub_div hD', div_div_div_cancel_right₀ hD']
  have : 1 + (ψ - 1) * p - ψ * p = 1 - p := by ring
  rw [this]
  ring

/-- **The tangent-line identity behind aggregation bias.** With weights `π`, baseline risks
`p v ∈ [0, 1]` and an odds ratio `ψ > 0`, write `m = ∑ π p` and `c = ψ - 1`. Then
`f(m) - ∑ π f(p v) = c ψ ∑ π v (p v - m)² / ((1 + c p v) (1 + c m)²)`, where
`f = riskOfOddsRatio ψ`. The map `f` is strictly concave for `ψ > 1` and strictly convex for
`ψ < 1`. -/
theorem riskOfOddsRatio_sub_standardizedRisk {π p : V → ℝ} {ψ : ℝ} (hπ : IsWeights π)
    (hψ : 0 < ψ) (h0 : ∀ v, 0 ≤ p v) (h1 : ∀ v, p v ≤ 1) :
    riskOfOddsRatio ψ (standardizedRisk π p) -
        standardizedRisk π (fun v => riskOfOddsRatio ψ (p v)) =
      (ψ - 1) * ψ * ∑ v, π v * ((p v - standardizedRisk π p) ^ 2 /
        ((1 + (ψ - 1) * p v) * (1 + (ψ - 1) * standardizedRisk π p) ^ 2)) := by
  set m := standardizedRisk π p with hm
  have hm01 : m ∈ Set.Icc (0 : ℝ) 1 := standardizedRisk_mem_Icc hπ.1 hπ.2 fun v => ⟨h0 v, h1 v⟩
  have hDm := riskOfOddsRatio_denom_pos hψ hm01.1 hm01.2
  -- tangent line at `m`
  have key : ∀ v, riskOfOddsRatio ψ (p v) = riskOfOddsRatio ψ m +
      ψ / (1 + (ψ - 1) * m) ^ 2 * (p v - m) -
      (ψ - 1) * ψ * ((p v - m) ^ 2 / ((1 + (ψ - 1) * p v) * (1 + (ψ - 1) * m) ^ 2)) := by
    intro v
    have hA := (riskOfOddsRatio_denom_pos hψ (h0 v) (h1 v)).ne'
    have hB := hDm.ne'
    unfold riskOfOddsRatio
    generalize hA' : 1 + (ψ - 1) * p v = A at *
    generalize hB' : 1 + (ψ - 1) * m = B at *
    field_simp
    rw [← hA', ← hB']
    ring
  have hsum0 : ∑ v, π v * (p v - m) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hπ.2, one_mul]
    rw [hm, standardizedRisk]; ring
  have : standardizedRisk π (fun v => riskOfOddsRatio ψ (p v)) =
      ∑ v, (π v * riskOfOddsRatio ψ m + ψ / (1 + (ψ - 1) * m) ^ 2 * (π v * (p v - m)) -
        (ψ - 1) * ψ * (π v * ((p v - m) ^ 2 /
          ((1 + (ψ - 1) * p v) * (1 + (ψ - 1) * m) ^ 2)))) := by
    unfold standardizedRisk
    exact Finset.sum_congr rfl fun v _ => by dsimp only; rw [key v]; ring
  rw [this, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    ← Finset.mul_sum, hπ.2, hsum0]
  ring

/-- The dispersion term of `riskOfOddsRatio_sub_standardizedRisk`. -/
noncomputable def aggregationGap (ψ : ℝ) (π p : V → ℝ) : ℝ :=
  ∑ v, π v * ((p v - standardizedRisk π p) ^ 2 /
    ((1 + (ψ - 1) * p v) * (1 + (ψ - 1) * standardizedRisk π p) ^ 2))

theorem aggregationGap_nonneg {π p : V → ℝ} {ψ : ℝ} (hπ : IsWeights π) (hψ : 0 < ψ)
    (h0 : ∀ v, 0 ≤ p v) (h1 : ∀ v, p v ≤ 1) : 0 ≤ aggregationGap ψ π p := by
  have hm01 := standardizedRisk_mem_Icc hπ.1 hπ.2 fun v => ⟨h0 v, h1 v⟩
  have hB := riskOfOddsRatio_denom_pos hψ hm01.1 hm01.2
  exact Finset.sum_nonneg fun v _ => mul_nonneg (hπ.1 v)
    (div_nonneg (sq_nonneg _)
      (mul_nonneg (riskOfOddsRatio_denom_pos hψ (h0 v) (h1 v)).le (by positivity)))

/-- The dispersion term is positive when the baseline risk takes two different values on strata
of positive weight. -/
theorem aggregationGap_pos {π p : V → ℝ} {ψ : ℝ} (hπ : IsWeights π) (hψ : 0 < ψ)
    (h0 : ∀ v, 0 ≤ p v) (h1 : ∀ v, p v ≤ 1)
    (hvar : ∃ v w, 0 < π v ∧ 0 < π w ∧ p v ≠ p w) : 0 < aggregationGap ψ π p := by
  have hm01 := standardizedRisk_mem_Icc hπ.1 hπ.2 fun v => ⟨h0 v, h1 v⟩
  have hB := riskOfOddsRatio_denom_pos hψ hm01.1 hm01.2
  obtain ⟨v, w, hv, hw, hvw⟩ := hvar
  have hex : ∃ u, 0 < π u ∧ p u ≠ standardizedRisk π p := by
    by_contra h
    push Not at h
    exact hvw ((h v hv).trans (h w hw).symm)
  obtain ⟨u, hu, hpu⟩ := hex
  refine Finset.sum_pos' (fun x _ => mul_nonneg (hπ.1 x) (div_nonneg (sq_nonneg _)
    (mul_nonneg (riskOfOddsRatio_denom_pos hψ (h0 x) (h1 x)).le (by positivity))))
    ⟨u, Finset.mem_univ _, mul_pos hu (div_pos (sq_pos_of_ne_zero (sub_ne_zero.2 hpu))
      (mul_pos (riskOfOddsRatio_denom_pos hψ (h0 u) (h1 u)) (by positivity)))⟩

/-- The dispersion term vanishes when the baseline risk is constant on the strata of positive
weight. -/
theorem aggregationGap_eq_zero {π p : V → ℝ} {ψ : ℝ} (hπ : IsWeights π)
    (hconst : ∀ v w, 0 < π v → 0 < π w → p v = p w) : aggregationGap ψ π p = 0 := by
  have hsupp : ∀ v, 0 < π v → p v = standardizedRisk π p := by
    intro v hv
    have : standardizedRisk π p = ∑ w, π w * p v := by
      unfold standardizedRisk
      refine Finset.sum_congr rfl fun w _ => ?_
      rcases (hπ.1 w).eq_or_lt with h | h
      · rw [← h, zero_mul, zero_mul]
      · rw [hconst w v h hv]
    rw [this, ← Finset.sum_mul, hπ.2, one_mul]
  refine Finset.sum_eq_zero fun v _ => ?_
  rcases (hπ.1 v).eq_or_lt with h | h
  · rw [← h, zero_mul]
  · rw [hsupp v h, sub_self]; simp

/-- Common setting of the attenuation theorems: with a common stratum odds ratio `ψ > 0`, the
marginal risk under treatment is `f(P) - (ψ - 1) ψ G`, where `P` is the marginal baseline risk,
`f = riskOfOddsRatio ψ` and `G = aggregationGap ψ π p₀`. -/
theorem standardizedRisk_of_common_oddsRatio {π p₁ p₀ : V → ℝ} {ψ : ℝ} (hπ : IsWeights π)
    (hψ : 0 < ψ) (h₁ : ∀ v, p₁ v < 1) (h0 : ∀ v, 0 < p₀ v) (h1 : ∀ v, p₀ v < 1)
    (hOR : ∀ v, oddsRatio (p₁ v) (p₀ v) = ψ) :
    standardizedRisk π p₁ = riskOfOddsRatio ψ (standardizedRisk π p₀) -
      (ψ - 1) * ψ * aggregationGap ψ π p₀ := by
  have hp : p₁ = fun v => riskOfOddsRatio ψ (p₀ v) :=
    funext fun v => eq_riskOfOddsRatio (h₁ v) (h0 v) (h1 v) hψ (hOR v)
  rw [aggregationGap, ← riskOfOddsRatio_sub_standardizedRisk hπ hψ (fun v => (h0 v).le)
    (fun v => (h1 v).le), hp]
  ring

/-- **Aggregation bias of the odds ratio is toward the null** (TSD 3, Section 1.1.5). Let the
stratifier be independent of treatment (stratum weights `π` in both arms), the stratum baseline
risks lie in `(0, 1)`, and the stratum odds ratio be a common `ψ > 1` (no effect modification on
the odds ratio scale). If the baseline risk takes two different values on strata of positive
weight, the marginal odds ratio lies strictly between `1` and `ψ`. -/
theorem oddsRatio_marginal_mem_Ioo_of_one_lt {π p₁ p₀ : V → ℝ} {ψ : ℝ} (hπ : IsWeights π)
    (hψ : 1 < ψ) (h₁ : ∀ v, p₁ v < 1) (h0 : ∀ v, 0 < p₀ v) (h1 : ∀ v, p₀ v < 1)
    (hOR : ∀ v, oddsRatio (p₁ v) (p₀ v) = ψ) (hvar : ∃ v w, 0 < π v ∧ 0 < π w ∧ p₀ v ≠ p₀ w) :
    oddsRatio (standardizedRisk π p₁) (standardizedRisk π p₀) ∈ Set.Ioo 1 ψ := by
  have hψ0 : 0 < ψ := by linarith
  have hP0 : 0 < standardizedRisk π p₀ := lt_standardizedRisk hπ h0
  have hP1 : standardizedRisk π p₀ < 1 := standardizedRisk_lt hπ h1
  have hQ1 : standardizedRisk π p₁ < 1 := standardizedRisk_lt hπ h₁
  have hG := aggregationGap_pos hπ hψ0 (fun v => (h0 v).le) (fun v => (h1 v).le) hvar
  have hQ := standardizedRisk_of_common_oddsRatio hπ hψ0 h₁ h0 h1 hOR
  have hlt : standardizedRisk π p₁ < riskOfOddsRatio ψ (standardizedRisk π p₀) := by
    rw [hQ]; have : 0 < (ψ - 1) * ψ * aggregationGap ψ π p₀ := by positivity
    linarith
  constructor
  · rw [one_lt_oddsRatio_iff hQ1 hP0 hP1, riskDiff, sub_pos]
    have hd : ∀ v, 0 < p₁ v - p₀ v := fun v => by
      have := (one_lt_oddsRatio_iff (h₁ v) (h0 v) (h1 v)).1 (by rw [hOR v]; exact hψ)
      exact this
    have := lt_standardizedRisk hπ hd
    simp only [standardizedRisk, mul_sub, Finset.sum_sub_distrib] at this ⊢
    linarith
  · have hodds := odds_riskOfOddsRatio hψ0 hP0.le hP1
    rw [oddsRatio, div_lt_iff₀ (odds_pos hP0 hP1), ← hodds]
    exact (odds_lt_odds_iff hQ1 (riskOfOddsRatio_lt_one hψ0 hP0.le hP1)).2 hlt

/-- **The mirror statement for a protective effect.** Under the hypotheses of
`oddsRatio_marginal_mem_Ioo_of_one_lt` with a common stratum odds ratio `0 < ψ < 1`, the
marginal odds ratio lies strictly between `ψ` and `1`. -/
theorem oddsRatio_marginal_mem_Ioo_of_lt_one {π p₁ p₀ : V → ℝ} {ψ : ℝ} (hπ : IsWeights π)
    (hψ0 : 0 < ψ) (hψ : ψ < 1) (h₁ : ∀ v, p₁ v < 1) (h0 : ∀ v, 0 < p₀ v) (h1 : ∀ v, p₀ v < 1)
    (hOR : ∀ v, oddsRatio (p₁ v) (p₀ v) = ψ) (hvar : ∃ v w, 0 < π v ∧ 0 < π w ∧ p₀ v ≠ p₀ w) :
    oddsRatio (standardizedRisk π p₁) (standardizedRisk π p₀) ∈ Set.Ioo ψ 1 := by
  have hP0 : 0 < standardizedRisk π p₀ := lt_standardizedRisk hπ h0
  have hP1 : standardizedRisk π p₀ < 1 := standardizedRisk_lt hπ h1
  have hQ1 : standardizedRisk π p₁ < 1 := standardizedRisk_lt hπ h₁
  have hG := aggregationGap_pos hπ hψ0 (fun v => (h0 v).le) (fun v => (h1 v).le) hvar
  have hQ := standardizedRisk_of_common_oddsRatio hπ hψ0 h₁ h0 h1 hOR
  have hlt : riskOfOddsRatio ψ (standardizedRisk π p₀) < standardizedRisk π p₁ := by
    rw [hQ]; have : 0 < (1 - ψ) * ψ * aggregationGap ψ π p₀ := by
      have : 0 < 1 - ψ := by linarith
      positivity
    nlinarith
  constructor
  · have hodds := odds_riskOfOddsRatio hψ0 hP0.le hP1
    rw [oddsRatio, lt_div_iff₀ (odds_pos hP0 hP1), ← hodds]
    exact (odds_lt_odds_iff (riskOfOddsRatio_lt_one hψ0 hP0.le hP1) hQ1).2 hlt
  · rw [oddsRatio_lt_one_iff hQ1 hP0 hP1, riskDiff, sub_neg]
    have hd : ∀ v, p₁ v - p₀ v < 0 := fun v =>
      (oddsRatio_lt_one_iff (h₁ v) (h0 v) (h1 v)).1 (by rw [hOR v]; exact hψ)
    have := standardizedRisk_lt hπ hd
    simp only [standardizedRisk, mul_sub, Finset.sum_sub_distrib] at this ⊢
    linarith

/-- **No aggregation bias without variation of the baseline risk.** Under the hypotheses of
`oddsRatio_marginal_mem_Ioo_of_one_lt` with any common stratum odds ratio `ψ > 0`, if the
baseline risk is the same on all strata of positive weight, the marginal odds ratio equals `ψ`.
So the hypothesis that the baseline risk varies cannot be dropped. -/
theorem oddsRatio_marginal_eq_of_const {π p₁ p₀ : V → ℝ} {ψ : ℝ} (hπ : IsWeights π)
    (hψ0 : 0 < ψ) (h₁ : ∀ v, p₁ v < 1) (h0 : ∀ v, 0 < p₀ v) (h1 : ∀ v, p₀ v < 1)
    (hOR : ∀ v, oddsRatio (p₁ v) (p₀ v) = ψ)
    (hconst : ∀ v w, 0 < π v → 0 < π w → p₀ v = p₀ w) :
    oddsRatio (standardizedRisk π p₁) (standardizedRisk π p₀) = ψ := by
  have hP0 : 0 < standardizedRisk π p₀ := lt_standardizedRisk hπ h0
  have hP1 : standardizedRisk π p₀ < 1 := standardizedRisk_lt hπ h1
  rw [standardizedRisk_of_common_oddsRatio hπ hψ0 h₁ h0 h1 hOR,
    aggregationGap_eq_zero hπ hconst, mul_zero, sub_zero, oddsRatio,
    odds_riskOfOddsRatio hψ0 hP0.le hP1, mul_div_cancel_right₀ _ (odds_pos hP0 hP1).ne']

/-- **Table 4.4 is an instance of the attenuation theorem.** In Hernán and Robins, Table 4.4,
the stratifier is independent of treatment, both stratum odds ratios equal `6`, and the baseline
risks `1/5` and `2/5` differ; so the marginal odds ratio (which is `49/9`,
`table44_marginal_oddsRatio`) lies strictly between `1` and `6`. -/
theorem table44_marginal_oddsRatio_mem_Ioo :
    oddsRatio (margRisk44 true) (margRisk44 false) ∈ Set.Ioo 1 6 := by
  have hc : condV44 false = condV44 true := funext fun v => by rw [table44_indep, table44_indep]
  rw [margRisk44_eq, margRisk44_eq, hc]
  refine oddsRatio_marginal_mem_Ioo_of_one_lt (isWeights_condV44 true) (by norm_num)
    (fun v => ?_) (fun v => ?_) (fun v => ?_) table44_stratum_oddsRatio
    ⟨true, false, ?_, ?_, ?_⟩
  · cases v <;> norm_num [risk44, table44]
  · cases v <;> norm_num [risk44, table44]
  · cases v <;> norm_num [risk44, table44]
  · norm_num [condV44, table44, Fintype.sum_bool]
  · norm_num [condV44, table44, Fintype.sum_bool]
  · norm_num [risk44, table44]

/-! ### Countermodel: confounding by the stratifier -/

/-- Stratum distribution in the treated arm of the confounded countermodel: `3/4` of the treated
are in the high risk stratum `true`. -/
noncomputable def confStratum₁ (v : Bool) : ℝ := if v then 3 / 4 else 1 / 4

/-- Stratum distribution in the untreated arm of the confounded countermodel. -/
noncomputable def confStratum₀ (v : Bool) : ℝ := if v then 1 / 4 else 3 / 4

/-- Baseline risks of the confounded countermodel: `1/2` and `1/5`. -/
noncomputable def confRisk₀ (v : Bool) : ℝ := if v then 1 / 2 else 1 / 5

/-- Risks under treatment of the confounded countermodel: `2/3` and `1/3`. -/
noncomputable def confRisk₁ (v : Bool) : ℝ := if v then 2 / 3 else 1 / 3

/-- **Independence of the stratifier and treatment cannot be dropped.** In the countermodel the
stratum odds ratio is `2` in both strata and the baseline risk varies, but the stratifier is
more common among the treated (`3/4` against `1/4`). The marginal odds ratio is `203/55`,
above `2`: confounding moves it away from the null, outside the interval `(1, 2)` of the
attenuation theorem. -/
theorem oddsRatio_marginal_confounded :
    IsWeights confStratum₁ ∧ IsWeights confStratum₀ ∧
      (∀ v, oddsRatio (confRisk₁ v) (confRisk₀ v) = 2) ∧
      oddsRatio (standardizedRisk confStratum₁ confRisk₁)
          (standardizedRisk confStratum₀ confRisk₀) = 203 / 55 ∧
      (2 : ℝ) < 203 / 55 := by
  refine ⟨⟨fun v => ?_, ?_⟩, ⟨fun v => ?_, ?_⟩, fun v => ?_, ?_, by norm_num⟩
  · cases v <;> norm_num [confStratum₁]
  · norm_num [confStratum₁, Fintype.sum_bool]
  · cases v <;> norm_num [confStratum₀]
  · norm_num [confStratum₀, Fintype.sum_bool]
  · cases v <;> norm_num [oddsRatio, odds, confRisk₁, confRisk₀]
  · norm_num [oddsRatio, odds, standardizedRisk, confStratum₁, confStratum₀, confRisk₁,
      confRisk₀, Fintype.sum_bool]

/-! ### Linear and log scales: no aggregation bias -/

/-- **A common risk difference survives pooling.** With the stratifier independent of treatment
and the same risk difference `δ` in every stratum, the marginal risk difference is `δ`, whatever
the baseline risks. -/
theorem riskDiff_marginal_eq_of_common {π p₁ p₀ : V → ℝ} {δ : ℝ} (hπ : IsWeights π)
    (h : ∀ v, riskDiff (p₁ v) (p₀ v) = δ) :
    riskDiff (standardizedRisk π p₁) (standardizedRisk π p₀) = δ := by
  have := riskDiff_mem_Icc (m := δ) (M := δ) hπ fun v => by rw [h v]; exact ⟨le_rfl, le_rfl⟩
  exact le_antisymm this.2 this.1

/-- **A common risk ratio survives pooling** (the correction to the overstatement of TSD 3,
Sections 1.1.4 and 1.1.5, that aggregation bias affects log models). With the stratifier
independent of treatment, positive baseline risks, and the same risk ratio `ρ` in every
stratum, the marginal risk ratio is `ρ`, however much the baseline risk varies. For binomial
risks the log link is therefore free of aggregation bias; the bias toward the null concerns the
odds ratio (`oddsRatio_marginal_mem_Ioo_of_one_lt`). -/
theorem riskRatio_marginal_eq_of_common {π p₁ p₀ : V → ℝ} {ρ : ℝ} (hπ : IsWeights π)
    (h₀ : ∀ v, 0 < p₀ v) (h : ∀ v, riskRatio (p₁ v) (p₀ v) = ρ) :
    riskRatio (standardizedRisk π p₁) (standardizedRisk π p₀) = ρ := by
  have := riskRatio_mem_Icc (m := ρ) (M := ρ) hπ h₀ fun v => by rw [h v]; exact ⟨le_rfl, le_rfl⟩
  exact le_antisymm this.2 this.1

/-! ### Collapsed category data -/

/-- The risk in a trial arm made of a proportion `q` of men (stratum risk `a`) and `1 - q` of
women (stratum risk `b`), the same proportion in both arms (randomization). -/
def collapsedRisk (q a b : ℝ) : ℝ := q * a + (1 - q) * b

/-- **Identity link: the collapsed category model is exact** (TSD 3, Section 1.1.4). The risk
difference of a trial with a proportion `q` of men is affine in `q`: the effect in women plus
`q` times the interaction. So regressing trial risk differences on the proportion of men, with
trials on men (`q = 1`) and on women (`q = 0`), is correctly specified. -/
theorem riskDiff_collapsedRisk (q p₁m p₀m p₁f p₀f : ℝ) :
    riskDiff (collapsedRisk q p₁m p₁f) (collapsedRisk q p₀m p₀f) =
      riskDiff p₁f p₀f + q * (riskDiff p₁m p₀m - riskDiff p₁f p₀f) := by
  unfold riskDiff collapsedRisk; ring

/-- **Log link with a common risk ratio: the collapsed category model is exact.** If the risk
ratio is `ρ` among men and among women, the log risk ratio of a trial with any proportion
`q ∈ [0, 1]` of men is `log ρ`, constant (hence affine) in `q`. -/
theorem log_riskRatio_collapsedRisk_of_common {q p₁m p₀m p₁f p₀f ρ : ℝ} (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) (hm : 0 < p₀m) (hf : 0 < p₀f) (hρm : riskRatio p₁m p₀m = ρ)
    (hρf : riskRatio p₁f p₀f = ρ) :
    Real.log (riskRatio (collapsedRisk q p₁m p₁f) (collapsedRisk q p₀m p₀f)) = Real.log ρ := by
  congr 1
  have hπ : IsWeights (fun v : Bool => if v then q else 1 - q) :=
    ⟨fun v => by cases v <;> simp [hq0, hq1], by simp⟩
  have := riskRatio_marginal_eq_of_common (p₁ := fun v => if v then p₁m else p₁f)
    (p₀ := fun v => if v then p₀m else p₀f) hπ (fun v => by cases v <;> simpa)
    (fun v => by cases v <;> simpa)
  simpa [standardizedRisk, Fintype.sum_bool, collapsedRisk] using this

/-- **Log link with an interaction: the collapsed category model is misspecified** (TSD 3,
Section 1.1.4, "not valid for logit, log or other commonly used models"). Risks `1/10` in
both arms among men (risk ratio `1`), `2/5` against `1/10` among women (risk ratio `4`). No line
`a + b q` gives the log risk ratio of a trial with proportion `q` of men for every
`q ∈ [0, 1]`: at `q = 0`, `1/2`, `1` the risk ratios are `4`, `5/2`, `1`, and a line would need
`log (5/2) = (log 4 + log 1) / 2 = log 2`. -/
theorem log_riskRatio_collapsedRisk_not_affine :
    ¬ ∃ a b : ℝ, ∀ q ∈ Set.Icc (0 : ℝ) 1,
      Real.log (riskRatio (collapsedRisk q (1 / 10) (2 / 5)) (collapsedRisk q (1 / 10) (1 / 10)))
        = a + b * q := by
  rintro ⟨a, b, h⟩
  have h0 := h 0 (by norm_num)
  have h1 := h 1 (by norm_num)
  have hh := h (1 / 2) (by norm_num)
  norm_num [riskRatio, collapsedRisk] at h0 h1 hh
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have : Real.log (5 / 2) = Real.log 2 := by linarith
  have := Real.log_injOn_pos (Set.mem_Ioi.2 (by norm_num)) (Set.mem_Ioi.2 (by norm_num)) this
  norm_num at this

end EffectMeasure

end CausalInference
