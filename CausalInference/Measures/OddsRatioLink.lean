/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Measures.EffectModifier

/-!
# The odds ratio on a general covariate law: attenuation toward the null

A covariate law `ν`, a reference risk `a x` and an active risk `b x`, both almost surely in
`(0, 1)`, with a conditional odds ratio `oddsRatio (b x) (a x)` that is almost surely a constant
`ψ`. The marginal odds ratio is `oddsRatio (∫ b dν) (∫ a dν)`.

This is the measure-theoretic form of the finite strata attenuation theorems of
`Measures/Aggregation.lean`; `oddsRatio_marginal_mem_Ioo_of_stratumLaw` recovers them.

## Main definitions

* `logit p = log (odds p)`, the logit link on `(0, 1)`. It is the same function as the logit of
  `Designs/DifferenceInDifferences/Scale.lean`, which is not imported here.

## Main results

* `oddsRatio_integral_mem_Ioo`: if the reference risk is not almost surely constant (the
  covariate is prognostic for the reference arm), the marginal odds ratio lies strictly between
  `1` and `ψ`: in `(1, ψ)` for `ψ > 1` and in `(ψ, 1)` for `ψ < 1`.
* `oddsRatio_integral_eq_iff`: for `ψ ≠ 1` the marginal odds ratio equals `ψ` if and only if
  the covariate is not prognostic for the reference arm; `oddsRatio_integral_eq_one`: at the
  null `ψ = 1` the marginal odds ratio is `1` for every covariate law.
* `logit_linkMarginal_attenuation`: on the logit scale, with a conditional log odds ratio that
  is almost surely a constant `c ≠ 0`, the marginal log odds ratio has the sign of `c` and
  `0 < |marginal| < |c|`.
* `oddsRatio_marginal_mem_Ioo_of_stratumLaw`: the finite strata theorems
  `oddsRatio_marginal_mem_Ioo_of_one_lt` and `oddsRatio_marginal_mem_Ioo_of_lt_one` as the case
  of the law `stratumLaw π` of a stratifier.

## References

* M. A. Hernán and J. M. Robins, *Causal Inference: What If* (2020), Fine Point 4.3.
* S. Dias, A. J. Sutton, N. J. Welton, A. E. Ades, *NICE DSU Technical Support Document 3:
  Heterogeneity: Subgroups, Meta-Regression, Bias and Bias-Adjustment* (2011, updated 2012),
  Sections 1.1.4 and 1.1.5.
-/

@[expose] public section

open MeasureTheory

namespace CausalInference

namespace EffectMeasure

/-! ### The logit link -/

/-- The logit `log (p / (1 - p))`, meaningful for `0 < p < 1`. -/
noncomputable def logit (p : ℝ) : ℝ := Real.log (odds p)

/-- The logit in the form `log (p / (1 - p))` (the form of `DiDScale.logit`). -/
theorem logit_eq_log_div (p : ℝ) : logit p = Real.log (p / (1 - p)) := rfl

/-- The logit in the form `log p - log (1 - p)` on `(0, 1)` (the form of
`BiasAnalysis.VarianceFormulas.logit`). -/
theorem logit_eq_log_sub_log {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    logit p = Real.log p - Real.log (1 - p) := by
  rw [logit_eq_log_div, Real.log_div hp0.ne' (by linarith)]

/-- A difference of logits is the logarithm of the odds ratio. -/
theorem logit_sub_logit {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1) :
    logit q - logit p = Real.log (oddsRatio q p) := by
  rw [logit, logit, oddsRatio, Real.log_div (odds_pos hq0 hq1).ne' (odds_pos hp0 hp1).ne']

/-! ### The risk with a given odds ratio -/

theorem riskOfOddsRatio_pos {ψ p : ℝ} (hψ : 0 < ψ) (h0 : 0 < p) (h1 : p ≤ 1) :
    0 < riskOfOddsRatio ψ p :=
  div_pos (mul_pos hψ h0) (riskOfOddsRatio_denom_pos hψ h0.le h1)

/-- The tangent line identity of `f = riskOfOddsRatio ψ` at `m`:
`f m + f' m (p - m) - f p = (ψ - 1) ψ (p - m)² / ((1 + (ψ - 1) p) (1 + (ψ - 1) m)²)`. -/
theorem riskOfOddsRatio_tangent {ψ m p : ℝ} (hm : 0 < 1 + (ψ - 1) * m)
    (hp : 0 < 1 + (ψ - 1) * p) :
    riskOfOddsRatio ψ m + ψ / (1 + (ψ - 1) * m) ^ 2 * (p - m) - riskOfOddsRatio ψ p =
      (ψ - 1) * ψ * ((p - m) ^ 2 / ((1 + (ψ - 1) * p) * (1 + (ψ - 1) * m) ^ 2)) := by
  have hA := hp.ne'
  have hB := hm.ne'
  unfold riskOfOddsRatio
  generalize hA' : 1 + (ψ - 1) * p = A at *
  generalize hB' : 1 + (ψ - 1) * m = B at *
  field_simp
  rw [← hA', ← hB']
  ring

/-- `f p - p = (ψ - 1) p (1 - p) / (1 + (ψ - 1) p)` for `f = riskOfOddsRatio ψ`. -/
theorem riskOfOddsRatio_sub_self {ψ p : ℝ} (hp : 0 < 1 + (ψ - 1) * p) :
    riskOfOddsRatio ψ p - p = (ψ - 1) * (p * (1 - p) / (1 + (ψ - 1) * p)) := by
  have hA := hp.ne'
  unfold riskOfOddsRatio
  generalize hA' : 1 + (ψ - 1) * p = A at *
  field_simp
  rw [← hA']
  ring

/-! ### Attenuation on a general covariate law -/

section Attenuation

variable {X : Type*} [MeasurableSpace X] {ν : Measure X} [IsProbabilityMeasure ν]

/-- The mean of an integrable function with values almost surely in `(0, 1)` lies in `(0, 1)`. -/
theorem integral_mem_Ioo_zero_one {f : X → ℝ} (hf : Integrable f ν)
    (h : ∀ᵐ x ∂ν, f x ∈ Set.Ioo (0 : ℝ) 1) : ∫ x, f x ∂ν ∈ Set.Ioo (0 : ℝ) 1 := by
  refine ⟨integral_pos_of_ae_pos hf (h.mono fun x hx => hx.1), ?_⟩
  have hi : Integrable (fun x => 1 - f x) ν := (integrable_const 1).sub hf
  have := integral_pos_of_ae_pos hi (h.mono fun x hx => by simp only [sub_pos]; exact hx.2)
  rw [integral_sub (integrable_const 1) hf, integral_const] at this
  simp at this
  linarith

variable {a b : X → ℝ} {ψ : ℝ}

/-- The conditional odds ratio of risks in `(0, 1)` is positive. -/
theorem pos_of_ae_oddsRatio_eq (hD : ∀ᵐ x ∂ν, a x ∈ Set.Ioo (0 : ℝ) 1 ∧ b x ∈ Set.Ioo (0 : ℝ) 1)
    (hψ : ∀ᵐ x ∂ν, oddsRatio (b x) (a x) = ψ) : 0 < ψ := by
  obtain ⟨x, hx, hDx⟩ := (hψ.and hD).exists
  rw [← hx]
  exact div_pos (odds_pos hDx.2.1 hDx.2.2) (odds_pos hDx.1.1 hDx.1.2)

/-- With a common conditional odds ratio `ψ`, the active risk is almost surely
`riskOfOddsRatio ψ` of the reference risk. -/
theorem ae_eq_riskOfOddsRatio (hD : ∀ᵐ x ∂ν, a x ∈ Set.Ioo (0 : ℝ) 1 ∧ b x ∈ Set.Ioo (0 : ℝ) 1)
    (hψ : ∀ᵐ x ∂ν, oddsRatio (b x) (a x) = ψ) : ∀ᵐ x ∂ν, b x = riskOfOddsRatio ψ (a x) := by
  have hk := pos_of_ae_oddsRatio_eq hD hψ
  filter_upwards [hψ, hD] with x hx hDx
  exact eq_riskOfOddsRatio hDx.2.2 hDx.1.1 hDx.1.2 hk hx

/-- **Strict attenuation of the marginal odds ratio toward the null.** Let the reference and
active risks lie almost surely in `(0, 1)`, let the conditional odds ratio be almost surely the
constant `ψ ≠ 1`, and let the covariate be prognostic for the reference arm (the reference risk
is not almost surely constant). Then the marginal odds ratio lies strictly between `1` and
`ψ`. -/
theorem oddsRatio_integral_mem_Ioo (ha : Integrable a ν) (hb : Integrable b ν)
    (hD : ∀ᵐ x ∂ν, a x ∈ Set.Ioo (0 : ℝ) 1 ∧ b x ∈ Set.Ioo (0 : ℝ) 1)
    (hψ : ∀ᵐ x ∂ν, oddsRatio (b x) (a x) = ψ) (hψ1 : ψ ≠ 1) (hW : IsPrognostic ν a) :
    (1 < ψ → oddsRatio (∫ x, b x ∂ν) (∫ x, a x ∂ν) ∈ Set.Ioo 1 ψ) ∧
      (ψ < 1 → oddsRatio (∫ x, b x ∂ν) (∫ x, a x ∂ν) ∈ Set.Ioo ψ 1) := by
  have hk := pos_of_ae_oddsRatio_eq hD hψ
  have hrel := ae_eq_riskOfOddsRatio hD hψ
  set m := ∫ x, a x ∂ν with hm_def
  set m1 := ∫ x, b x ∂ν with hm1_def
  have hm : m ∈ Set.Ioo (0 : ℝ) 1 := integral_mem_Ioo_zero_one ha (hD.mono fun x hx => hx.1)
  have hm1 : m1 ∈ Set.Ioo (0 : ℝ) 1 := integral_mem_Ioo_zero_one hb (hD.mono fun x hx => hx.2)
  have hdm := riskOfOddsRatio_denom_pos hk hm.1.le hm.2.le
  set H : ℝ → ℝ := fun p => (p - m) ^ 2 / ((1 + (ψ - 1) * p) * (1 + (ψ - 1) * m) ^ 2)
  -- the gap function, integrable as an affine combination of the two risks
  set G : X → ℝ := fun x => riskOfOddsRatio ψ m + ψ / (1 + (ψ - 1) * m) ^ 2 * (a x - m) - b x
  have i1 : Integrable (fun x => a x - m) ν := ha.sub (integrable_const m)
  have i2 : Integrable (fun x => ψ / (1 + (ψ - 1) * m) ^ 2 * (a x - m)) ν := i1.const_mul _
  have i3 : Integrable (fun x => riskOfOddsRatio ψ m + ψ / (1 + (ψ - 1) * m) ^ 2 * (a x - m)) ν :=
    (integrable_const _).add i2
  have hGi : Integrable G ν := i3.sub hb
  have hGint : ∫ x, G x ∂ν = riskOfOddsRatio ψ m - m1 := by
    simp only [G]
    rw [integral_sub i3 hb, integral_add (integrable_const _) i2, integral_const_mul,
      integral_sub ha (integrable_const m)]
    simp [← hm_def, ← hm1_def]
  have hGH : ∀ᵐ x ∂ν, G x = (ψ - 1) * ψ * H (a x) := by
    filter_upwards [hrel, hD] with x hx hDx
    simp only [G, H]
    rw [hx]
    exact riskOfOddsRatio_tangent hdm (riskOfOddsRatio_denom_pos hk hDx.1.1.le hDx.1.2.le)
  have hk1 : (ψ - 1) * ψ ≠ 0 := mul_ne_zero (sub_ne_zero.2 hψ1) hk.ne'
  have hHi : Integrable (fun x => H (a x)) ν := by
    refine (integrable_congr ?_).1 (hGi.div_const ((ψ - 1) * ψ))
    filter_upwards [hGH] with x hx
    rw [hx, mul_div_cancel_left₀ _ hk1]
  have hH0 : ∀ᵐ x ∂ν, 0 ≤ H (a x) := by
    filter_upwards [hD] with x hDx
    exact div_nonneg (sq_nonneg _) (mul_nonneg
      (riskOfOddsRatio_denom_pos hk hDx.1.1.le hDx.1.2.le).le (sq_nonneg _))
  have hHpos : 0 < ∫ x, H (a x) ∂ν := by
    rcases (integral_nonneg_of_ae hH0).lt_or_eq with h | h
    · exact h
    · exfalso
      have hz := (integral_eq_zero_iff_of_nonneg_ae hH0 hHi).1 h.symm
      refine hW ⟨m, ?_⟩
      filter_upwards [hz, hD] with x hx hDx
      have hd := riskOfOddsRatio_denom_pos hk hDx.1.1.le hDx.1.2.le
      have hx' : H (a x) = 0 := hx
      simp only [H, div_eq_zero_iff, pow_eq_zero_iff, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, mul_eq_zero, hd.ne', hdm.ne', or_false] at hx'
      exact sub_eq_zero.1 hx'
  have hgap : riskOfOddsRatio ψ m - m1 = (ψ - 1) * ψ * ∫ x, H (a x) ∂ν := by
    rw [← hGint, integral_congr_ae hGH, integral_const_mul]
  have hfm1 := riskOfOddsRatio_lt_one hk hm.1.le hm.2
  have hodds_m := odds_pos hm.1 hm.2
  have hfodds := odds_riskOfOddsRatio hk hm.1.le hm.2
  -- the difference of the two risks has the sign of `ψ - 1`
  have hdiff : ∀ᵐ x ∂ν, b x - a x = (ψ - 1) * (a x * (1 - a x) / (1 + (ψ - 1) * a x)) := by
    filter_upwards [hrel, hD] with x hx hDx
    rw [hx]
    exact riskOfOddsRatio_sub_self (riskOfOddsRatio_denom_pos hk hDx.1.1.le hDx.1.2.le)
  have hq : ∀ᵐ x ∂ν, 0 < a x * (1 - a x) / (1 + (ψ - 1) * a x) := by
    filter_upwards [hD] with x hDx
    exact div_pos (mul_pos hDx.1.1 (by linarith [hDx.1.2]))
      (riskOfOddsRatio_denom_pos hk hDx.1.1.le hDx.1.2.le)
  refine ⟨fun hgt => ⟨?_, ?_⟩, fun hlt => ⟨?_, ?_⟩⟩
  · have : 0 < ∫ x, (b x - a x) ∂ν := integral_pos_of_ae_pos (hb.sub ha) (by
      filter_upwards [hdiff, hq] with x hx hqx
      rw [hx]
      exact mul_pos (by linarith) hqx)
    rw [integral_sub hb ha] at this
    rw [oddsRatio, one_lt_div hodds_m]
    exact (odds_lt_odds_iff hm.2 hm1.2).2 (by linarith)
  · have : m1 < riskOfOddsRatio ψ m := by
      have := mul_pos (mul_pos (by linarith : (0 : ℝ) < ψ - 1) hk) hHpos
      linarith
    rw [oddsRatio, div_lt_iff₀ hodds_m, ← hfodds]
    exact (odds_lt_odds_iff hm1.2 hfm1).2 this
  · have : riskOfOddsRatio ψ m < m1 := by
      have := mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith : ψ - 1 < 0) hk) hHpos
      linarith
    rw [oddsRatio, lt_div_iff₀ hodds_m, ← hfodds]
    exact (odds_lt_odds_iff hfm1 hm1.2).2 this
  · have : 0 < ∫ x, (a x - b x) ∂ν := integral_pos_of_ae_pos (ha.sub hb) (by
      filter_upwards [hdiff, hq] with x hx hqx
      have := mul_neg_of_neg_of_pos (by linarith : ψ - 1 < 0) hqx
      linarith)
    rw [integral_sub ha hb] at this
    rw [oddsRatio, div_lt_one hodds_m]
    exact (odds_lt_odds_iff hm1.2 hm.2).2 (by linarith)

/-- **The marginal odds ratio equals a nonnull conditional one exactly without prognostic
variation.** Under the hypotheses of `oddsRatio_integral_mem_Ioo` without the prognostic
hypothesis, for `ψ ≠ 1`, the marginal odds ratio equals `ψ` if and only if the reference risk is
almost surely constant. -/
theorem oddsRatio_integral_eq_iff (ha : Integrable a ν) (hb : Integrable b ν)
    (hD : ∀ᵐ x ∂ν, a x ∈ Set.Ioo (0 : ℝ) 1 ∧ b x ∈ Set.Ioo (0 : ℝ) 1)
    (hψ : ∀ᵐ x ∂ν, oddsRatio (b x) (a x) = ψ) (hψ1 : ψ ≠ 1) :
    oddsRatio (∫ x, b x ∂ν) (∫ x, a x ∂ν) = ψ ↔ ¬ IsPrognostic ν a := by
  constructor
  · intro heq hW
    obtain ⟨hgt, hlt⟩ := oddsRatio_integral_mem_Ioo ha hb hD hψ hψ1 hW
    rcases lt_or_gt_of_ne hψ1 with h | h
    · exact (hlt h).1.ne' heq
    · exact (hgt h).2.ne heq
  · intro hW
    obtain ⟨c, hc⟩ := not_not.1 hW
    have hk := pos_of_ae_oddsRatio_eq hD hψ
    obtain ⟨x₀, hx₀, hD₀⟩ := (hc.and hD).exists
    have hb' : ∀ᵐ x ∂ν, b x = riskOfOddsRatio ψ c := by
      filter_upwards [ae_eq_riskOfOddsRatio hD hψ, hc] with x hx hcx
      rw [hx, hcx]
    rw [integral_congr_ae hc, integral_congr_ae hb', integral_const, integral_const]
    simp only [probReal_univ, one_smul]
    rw [← hx₀, oddsRatio, odds_riskOfOddsRatio hk hD₀.1.1.le hD₀.1.2,
      mul_div_cancel_right₀ _ (odds_pos hD₀.1.1 hD₀.1.2).ne']

/-- **No attenuation at the null**: if the conditional odds ratio is almost surely `1`, the
marginal odds ratio is `1` for every covariate law. -/
theorem oddsRatio_integral_eq_one (ha : Integrable a ν)
    (hD : ∀ᵐ x ∂ν, a x ∈ Set.Ioo (0 : ℝ) 1 ∧ b x ∈ Set.Ioo (0 : ℝ) 1)
    (hψ : ∀ᵐ x ∂ν, oddsRatio (b x) (a x) = 1) :
    oddsRatio (∫ x, b x ∂ν) (∫ x, a x ∂ν) = 1 := by
  have heq : b =ᵐ[ν] a := by
    filter_upwards [hψ, hD] with x hx hDx
    exact (oddsRatio_eq_one_iff hDx.2.2 hDx.1.1 hDx.1.2).1 hx
  rw [integral_congr_ae heq]
  have hm := integral_mem_Ioo_zero_one ha (hD.mono fun x hx => hx.1)
  exact (oddsRatio_eq_one_iff hm.2 hm.1 hm.2).2 rfl

/-- **Attenuation on the logit scale.** If the conditional log odds ratio is almost surely the
constant `c ≠ 0` and the covariate is prognostic for the reference arm, the marginal log odds
ratio has the sign of `c` and is strictly smaller in absolute value: `0 < |marginal| < |c|`. -/
theorem logit_linkMarginal_attenuation (ha : Integrable a ν) (hb : Integrable b ν)
    (hD : ∀ᵐ x ∂ν, a x ∈ Set.Ioo (0 : ℝ) 1 ∧ b x ∈ Set.Ioo (0 : ℝ) 1) {c : ℝ} (hc0 : c ≠ 0)
    (hc : ∀ᵐ x ∂ν, linkContrast logit a b x = c) (hW : IsPrognostic ν a) :
    0 < |linkMarginal logit ν a b| ∧ |linkMarginal logit ν a b| < |c| ∧
      0 < linkMarginal logit ν a b * c := by
  have hω : ∀ᵐ x ∂ν, oddsRatio (b x) (a x) = Real.exp c := by
    filter_upwards [hc, hD] with x hx hDx
    rw [linkContrast, logit_sub_logit hDx.1.1 hDx.1.2 hDx.2.1 hDx.2.2] at hx
    rw [← hx, Real.exp_log (show 0 < oddsRatio (b x) (a x) from
      div_pos (odds_pos hDx.2.1 hDx.2.2) (odds_pos hDx.1.1 hDx.1.2))]
  have hω1 : Real.exp c ≠ 1 := fun h => hc0 (Real.exp_eq_one_iff c |>.1 h)
  have hmA := integral_mem_Ioo_zero_one ha (hD.mono fun x hx => hx.1)
  have hmB := integral_mem_Ioo_zero_one hb (hD.mono fun x hx => hx.2)
  have hlog : linkMarginal logit ν a b = Real.log (oddsRatio (∫ x, b x ∂ν) (∫ x, a x ∂ν)) := by
    rw [linkMarginal, logit_sub_logit hmA.1 hmA.2 hmB.1 hmB.2]
  obtain ⟨hgt, hlt⟩ := oddsRatio_integral_mem_Ioo ha hb hD hω hω1 hW
  have hpos : 0 < oddsRatio (∫ x, b x ∂ν) (∫ x, a x ∂ν) :=
    div_pos (odds_pos hmB.1 hmB.2) (odds_pos hmA.1 hmA.2)
  rw [hlog]
  rcases lt_or_gt_of_ne hc0 with hneg | hpos'
  · obtain ⟨h1, h2⟩ := hlt (Real.exp_lt_one_iff.2 hneg)
    have l1 : Real.log (oddsRatio (∫ x, b x ∂ν) (∫ x, a x ∂ν)) < 0 := Real.log_neg hpos h2
    have l2 : c < Real.log (oddsRatio (∫ x, b x ∂ν) (∫ x, a x ∂ν)) := by
      rw [← Real.log_exp c]
      exact Real.log_lt_log (Real.exp_pos c) h1
    rw [abs_of_neg l1, abs_of_neg hneg]
    exact ⟨by linarith, by linarith, mul_pos_of_neg_of_neg l1 hneg⟩
  · obtain ⟨h1, h2⟩ := hgt (Real.one_lt_exp_iff.2 hpos')
    have l1 : 0 < Real.log (oddsRatio (∫ x, b x ∂ν) (∫ x, a x ∂ν)) := Real.log_pos h1
    have l2 : Real.log (oddsRatio (∫ x, b x ∂ν) (∫ x, a x ∂ν)) < c := by
      rw [← Real.log_exp c]
      exact Real.log_lt_log hpos h2
    rw [abs_of_pos l1, abs_of_pos hpos']
    exact ⟨l1, l2, mul_pos l1 hpos'⟩

end Attenuation

/-! ### Bridge to the finite strata theorems -/

/-- **The finite strata attenuation theorems are the case of a stratifier law.** With weights
`π`, stratum risks on the strata of positive weight as in `oddsRatio_marginal_mem_Ioo_of_one_lt`
(`Measures/Aggregation.lean`) and a baseline risk that varies on strata of positive weight, the
marginal odds ratio lies in `(1, ψ)` for `ψ > 1` and in `(ψ, 1)` for `0 < ψ < 1`. Proof: the
general theorem `oddsRatio_integral_mem_Ioo` under `ν = stratumLaw π`. -/
theorem oddsRatio_marginal_mem_Ioo_of_stratumLaw {V : Type*} [Fintype V] [MeasurableSpace V]
    [MeasurableSingletonClass V] {π p₁ p₀ : V → ℝ} {ψ : ℝ} (hπ : IsWeights π) (hψ0 : 0 < ψ)
    (hψ1 : ψ ≠ 1) (h₁ : ∀ v, 0 < π v → p₁ v < 1) (h0 : ∀ v, 0 < π v → 0 < p₀ v)
    (h1 : ∀ v, 0 < π v → p₀ v < 1) (hOR : ∀ v, 0 < π v → oddsRatio (p₁ v) (p₀ v) = ψ)
    (hvar : ∃ v w, 0 < π v ∧ 0 < π w ∧ p₀ v ≠ p₀ w) :
    (1 < ψ → oddsRatio (standardizedRisk π p₁) (standardizedRisk π p₀) ∈ Set.Ioo 1 ψ) ∧
      (ψ < 1 → oddsRatio (standardizedRisk π p₁) (standardizedRisk π p₀) ∈ Set.Ioo ψ 1) := by
  have := isProbabilityMeasure_stratumLaw hπ
  have hp₁ : ∀ v, 0 < π v → 0 < p₁ v := fun v hv => by
    rw [eq_riskOfOddsRatio (h₁ v hv) (h0 v hv) (h1 v hv) hψ0 (hOR v hv)]
    exact riskOfOddsRatio_pos hψ0 (h0 v hv) (h1 v hv).le
  have hD : ∀ᵐ v ∂(stratumLaw π), p₀ v ∈ Set.Ioo (0 : ℝ) 1 ∧ p₁ v ∈ Set.Ioo (0 : ℝ) 1 :=
    (ae_stratumLaw_iff π).2 fun v hv => ⟨⟨h0 v hv, h1 v hv⟩, ⟨hp₁ v hv, h₁ v hv⟩⟩
  have key := oddsRatio_integral_mem_Ioo (ν := stratumLaw π) (integrable_stratumLaw π p₀)
    (integrable_stratumLaw π p₁) hD ((ae_stratumLaw_iff π).2 hOR) hψ1
    ((isPrognostic_stratumLaw_iff_of_pos π).2 hvar)
  simpa only [integral_stratumLaw hπ.1] using key

end EffectMeasure

end CausalInference
