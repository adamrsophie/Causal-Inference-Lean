/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Survival.Basic

/-!
# Comparing two arms: hazard ratios versus survival and risk contrasts

Two arms, each with its own law of the event time: `(μ₁, T₁)` (for instance treated) and
`(μ₀, T₀)` (untreated); the measures may live on different spaces. In applications they are
the conditional laws given `A = 1` and `A = 0`, or the laws of two counterfactual event times.

## Main results

* `survival_div_survival_eq_prod`: the survival ratio at `k` is the product over `m ≤ k` of
  the ratios `(1 - h₁ m) / (1 - h₀ m)` of one minus the hazards; it is not a function of the
  hazard ratios `h₁ m / h₀ m` alone.
* `survival_eq_survival_of_hazard_eq`: if the hazards of the two arms agree at every time
  `m ≤ k` at which arm `0` has positive at-risk probability, including the times at which the
  hazard of arm `0` is zero, the survivals, and hence the risks, agree at `k`.
  `risk_eq_risk_of_hazard_eq` is the same for risks. A hazard ratio equal to `1` wherever it is
  defined (`h₀ m > 0`) is not enough: at a time with `h₀ m = 0 < h₁ m` the ratio is undefined
  and the survivals separate (`ComparisonExample.hazardRatio_one_where_defined_survival_ne`).
* `survival_eq_prod_hazardRatio`: `S₁ k = ∏_{m = 1}^{k} (1 - HR m * h₀ m)`: the survival in
  arm `1` depends on the hazard ratios at all times up to `k` and on the hazards of arm `0`.
* `risk_sub_risk`: the risk difference is minus the survival difference.
* `hazardRatio_one_eq_risk_ratio`: at time `1` the hazard ratio is the risk ratio, when the
  reference risk at time `1` is positive.
* `hazard_eq_hazard_of_survival_eq`: conversely, equal survival curves up to `k` give equal
  hazards at every `m ≤ k` with positive at-risk probability.

Examples (namespace `ComparisonExample`), all with event time `id` on `ℕ`:

* `hazardRatio_changes_risk_ratio_one`: the hazard ratio is `1/2` at time `1` and `4/3` at
  time `2`, while the survival and the risk at time `2` are equal in the two arms (risk ratio
  `1`). The period-specific hazard ratio changes over time, and no single hazard ratio
  summarizes the effect.
* `hazardRatio_one_where_defined_survival_ne`: arm `0` with masses `1/2, 0, 1/2` and arm `1`
  with masses `1/2, 1/4, 1/4` at times `1, 2, 3`. The hazard ratio is `1` at every time
  `m ≤ 2` at which it is defined, yet `S₀ 2 = 1/2` and `S₁ 2 = 1/4`: at time `2` the hazard of
  arm `0` is `0` and that of arm `1` is `1/2`.
* `techPoint81_hazardRatio`: a numerical instance of What If Technical Point 8.1 written with
  `hazardRatio`: two arms, each a mixture of two frailty strata with equal time `2` hazards in
  the two arms within each stratum, with hazard ratio `1/3` at time `1` and `50/49` at time
  `2`, while each stratum has hazard ratio `1` at time `2`.
* `weighted_hazardRatio_eq_one_survival_ne`: the average of the hazard ratios at times `1` and
  `2`, weighted by the distribution of the event time in arm `0` among those with the event by
  time `2`, equals `1`, yet the survivals at time `2` differ. This is the numerical phenomenon
  behind the remark that a single reported (Cox) hazard ratio may be `1` even if the survival
  curves are not identical; the claim that the Cox estimate is such a weighted average is not
  formalized here.

## Source

M. A. Hernán and J. M. Robins, *Causal Inference: What If* (2020), Chapter 17, Section 17.1
(contrasts of survival and risk, hazard ratio) and Fine Point 17.2 (the hazards of hazard
ratios); Chapter 8, Technical Point 8.1 (the hazard at time `1` is the risk at time `1`; from
time `2` on the hazard conditions on survival). The selection bias built into period-specific
hazard ratios (the second part of Fine Point 17.2, and Technical Point 8.1) is treated in
`CausalInference.Bias.HazardRatio`, in a two-period model with a binary frailty; this file only
records the numerical instance `techPoint81_hazardRatio` in the vocabulary of `hazardRatio`.
-/

@[expose] public section

open MeasureTheory

namespace CausalInference

namespace Survival

variable {Ω₀ Ω₁ : Type*} [MeasurableSpace Ω₀] [MeasurableSpace Ω₁]
  {μ₀ : Measure Ω₀} {μ₁ : Measure Ω₁} [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
  {T₀ : Ω₀ → ℕ} {T₁ : Ω₁ → ℕ}

/-- The hazard ratio at time `k` of arm `1` versus arm `0`: `h₁ k / h₀ k`. It is meaningful
only when both arms have positive at-risk probability at `k` and `h₀ k > 0`. -/
noncomputable def hazardRatio (μ₁ : Measure Ω₁) (T₁ : Ω₁ → ℕ) (μ₀ : Measure Ω₀) (T₀ : Ω₀ → ℕ)
    (k : ℕ) : ℝ :=
  hazard μ₁ T₁ k / hazard μ₀ T₀ k

/-- The survival ratio is a product of ratios of one minus the hazards: if both arms have
positive at-risk probability at `k` and `S₀ k > 0`, then
`S₁ k / S₀ k = ∏_{m = 0}^{k} (1 - h₁ m) / (1 - h₀ m)`, and every denominator `1 - h₀ m` is
positive. -/
theorem survival_div_survival_eq_prod (hT₀ : Measurable T₀) (hT₁ : Measurable T₁) (k : ℕ)
    (hk₀ : 0 < atRisk μ₀ T₀ k) (hk₁ : 0 < atRisk μ₁ T₁ k) (hS₀ : 0 < survival μ₀ T₀ k) :
    (∀ m ≤ k, 0 < 1 - hazard μ₀ T₀ m) ∧
      survival μ₁ T₁ k / survival μ₀ T₀ k =
        ∏ m ∈ Finset.range (k + 1), (1 - hazard μ₁ T₁ m) / (1 - hazard μ₀ T₀ m) := by
  obtain ⟨hpos₀, h₀⟩ := survival_eq_prod_one_sub_hazard hT₀ k hk₀
  obtain ⟨-, h₁⟩ := survival_eq_prod_one_sub_hazard hT₁ k hk₁
  refine ⟨fun m hm => ?_, by rw [h₀, h₁, Finset.prod_div_distrib]⟩
  have hSm : 0 < survival μ₀ T₀ m := lt_of_lt_of_le hS₀ (survival_antitone hm)
  have := survival_eq_atRisk_mul (μ := μ₀) hT₀ m
  rw [this] at hSm
  exact pos_of_mul_pos_right hSm (hpos₀ m hm).le

/-- Equal hazards give equal survival: if `h₁ m = h₀ m` at every `m ≤ k` at which arm `0` has
positive at-risk probability, then `S₁ k = S₀ k`. Times at which arm `0` has at-risk
probability zero impose no condition. -/
theorem survival_eq_survival_of_hazard_eq (hT₀ : Measurable T₀) (hT₁ : Measurable T₁) (k : ℕ)
    (h : ∀ m ≤ k, 0 < atRisk μ₀ T₀ m → hazard μ₁ T₁ m = hazard μ₀ T₀ m) :
    survival μ₁ T₁ k = survival μ₀ T₀ k := by
  induction k with
  | zero =>
    rw [survival_eq_atRisk_mul hT₀, survival_eq_atRisk_mul hT₁, atRisk_zero, atRisk_zero,
      h 0 le_rfl (by rw [atRisk_zero]; exact one_pos)]
  | succ k ih =>
    have ih' := ih fun m hm => h m (hm.trans k.le_succ)
    rw [survival_eq_atRisk_mul hT₀, survival_eq_atRisk_mul hT₁, atRisk_succ, atRisk_succ, ih',
      ← atRisk_succ]
    rcases (measureReal_nonneg : 0 ≤ atRisk μ₀ T₀ (k + 1)).eq_or_lt with h0 | h0
    · rw [show atRisk μ₀ T₀ (k + 1) = 0 from h0.symm, zero_mul, zero_mul]
    · rw [h (k + 1) le_rfl h0]

/-- Equal hazards give equal risks: under the hypothesis of `survival_eq_survival_of_hazard_eq`
the risks `1 - S₁ k` and `1 - S₀ k` agree. -/
theorem risk_eq_risk_of_hazard_eq (hT₀ : Measurable T₀) (hT₁ : Measurable T₁) (k : ℕ)
    (h : ∀ m ≤ k, 0 < atRisk μ₀ T₀ m → hazard μ₁ T₁ m = hazard μ₀ T₀ m) :
    risk μ₁ T₁ k = risk μ₀ T₀ k := by
  rw [risk, risk, survival_eq_survival_of_hazard_eq hT₀ hT₁ k h]

omit [IsProbabilityMeasure μ₀] in
/-- Survival in arm `1` from the hazard ratios and the hazards of arm `0`: if nobody in arm `1`
has the event at time `0`, arm `1` has positive at-risk probability at `k`, and `h₀ m ≠ 0` for
`1 ≤ m ≤ k`, then `S₁ k = ∏_{m = 1}^{k} (1 - HR m * h₀ m)` with
`HR m = h₁ m / h₀ m`. So the survival contrast at `k` depends on the hazard ratios at all
times up to `k` together with the reference hazards, not on any single hazard ratio. -/
theorem survival_eq_prod_hazardRatio (hT₁ : Measurable T₁)
    (h0₁ : μ₁.real {ω | T₁ ω = 0} = 0) (k : ℕ) (hk₁ : 0 < atRisk μ₁ T₁ k)
    (hne : ∀ m ∈ Finset.Icc 1 k, hazard μ₀ T₀ m ≠ 0) :
    survival μ₁ T₁ k =
      ∏ m ∈ Finset.Icc 1 k, (1 - hazardRatio μ₁ T₁ μ₀ T₀ m * hazard μ₀ T₀ m) := by
  rw [survival_eq_prod_Icc hT₁ h0₁ k hk₁]
  refine Finset.prod_congr rfl fun m hm => ?_
  rw [hazardRatio, div_mul_cancel₀ _ (hne m hm)]

omit [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁] in
/-- The risk difference is the survival difference with the sign reversed:
`(1 - S₁ k) - (1 - S₀ k) = S₀ k - S₁ k`. -/
theorem risk_sub_risk (k : ℕ) :
    risk μ₁ T₁ k - risk μ₀ T₀ k = survival μ₀ T₀ k - survival μ₁ T₁ k := by
  rw [risk, risk]; ring

/-- At time `1` the hazard ratio is the risk ratio (Hernán and Robins, Technical Point 8.1):
if nobody has the event at time `0` in either arm and the reference risk `P(T₀ ≤ 1)` is
positive, then the reference hazard `h₀ 1` is positive and
`h₁ 1 / h₀ 1 = P(T₁ ≤ 1) / P(T₀ ≤ 1)`, an equality of two genuine ratios.
From time `2` on, the hazard conditions on survival through the previous time, which is
where the selection bias described in Technical Point 8.1 and Fine Point 17.2 enters. -/
theorem hazardRatio_one_eq_risk_ratio (hT₀ : Measurable T₀) (hT₁ : Measurable T₁)
    (h0₀ : μ₀.real {ω | T₀ ω = 0} = 0) (h0₁ : μ₁.real {ω | T₁ ω = 0} = 0)
    (hpos : 0 < risk μ₀ T₀ 1) :
    0 < hazard μ₀ T₀ 1 ∧ hazardRatio μ₁ T₁ μ₀ T₀ 1 = risk μ₁ T₁ 1 / risk μ₀ T₀ 1 := by
  rw [hazardRatio, hazard_one_eq_risk_one hT₀ h0₀, hazard_one_eq_risk_one hT₁ h0₁]
  exact ⟨hpos, rfl⟩

omit [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁] in
/-- Equal survival curves give equal hazards: if `S₁ m = S₀ m` for every `m ≤ k` and the
total masses agree (`P(T₁ ≥ 0) = P(T₀ ≥ 0)`), then `h₁ m = h₀ m` for every `m ≤ k`. Both
the event probabilities `P(T = m)` and the at-risk probabilities agree, so at a time with
at-risk probability zero the equality is between two conventional values `0`. -/
theorem hazard_eq_hazard_of_survival_eq [IsFiniteMeasure μ₀] [IsFiniteMeasure μ₁]
    (hT₀ : Measurable T₀) (hT₁ : Measurable T₁) (k : ℕ)
    (h0 : atRisk μ₁ T₁ 0 = atRisk μ₀ T₀ 0)
    (h : ∀ m ≤ k, survival μ₁ T₁ m = survival μ₀ T₀ m) :
    ∀ m ≤ k, hazard μ₁ T₁ m = hazard μ₀ T₀ m := by
  intro m hm
  have hR : atRisk μ₁ T₁ m = atRisk μ₀ T₀ m := by
    rcases m with _ | m
    · exact h0
    · rw [atRisk_succ, atRisk_succ, h m (by omega)]
  have e₀ := atRisk_eq_add (μ := μ₀) hT₀ m
  have e₁ := atRisk_eq_add (μ := μ₁) hT₁ m
  have hE : μ₁.real {ω | T₁ ω = m} = μ₀.real {ω | T₀ ω = m} := by
    have := h m hm
    linarith
  rw [hazard, hazard, hE, hR]

namespace ComparisonExample

/-- A law on `ℕ` with mass `a` at `1`, `b` at `2` and `c` at `3`; with `T = id`, time `3`
stands for survival beyond time `2`. -/
noncomputable def threePoint (a b c : ℝ) : Measure ℕ :=
  ENNReal.ofReal a • Measure.dirac 1 + ENNReal.ofReal b • Measure.dirac 2 +
    ENNReal.ofReal c • Measure.dirac 3

theorem threePoint_real {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (s : Set ℕ) :
    (threePoint a b c).real s =
      s.indicator (fun _ => a) 1 + s.indicator (fun _ => b) 2 + s.indicator (fun _ => c) 3 := by
  classical
  simp only [threePoint, measureReal_def, add_apply, smul_apply, Measure.dirac_apply,
    smul_eq_mul, Set.indicator_apply, Pi.one_apply]
  split_ifs <;> simp [ENNReal.toReal_add, ha, hb, hc]

theorem isProbabilityMeasure_threePoint {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a + b + c = 1) : IsProbabilityMeasure (threePoint a b c) := by
  refine ⟨?_⟩
  simp only [threePoint, add_apply, smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add ha hb, ← ENNReal.ofReal_add (add_nonneg ha hb) hc, h,
    ENNReal.ofReal_one]

/-- Arm `0` of the first example: hazards `1/5` at time `1` and `1/4` at time `2`. -/
noncomputable def arm₀ : Measure ℕ := threePoint (1 / 5) (1 / 5) (3 / 5)

/-- Arm `1` of the first example: hazards `1/10` at time `1` and `1/3` at time `2`. -/
noncomputable def arm₁ : Measure ℕ := threePoint (1 / 10) (3 / 10) (3 / 5)

/-- Arm `1` of the second example: hazards `1/10` at time `1` and `3/8` at time `2`. -/
noncomputable def arm₂ : Measure ℕ := threePoint (1 / 10) (27 / 80) (9 / 16)

theorem arm₀_real (s : Set ℕ) : arm₀.real s =
    s.indicator (fun _ => 1 / 5) 1 + s.indicator (fun _ => 1 / 5) 2 +
      s.indicator (fun _ => 3 / 5) 3 :=
  threePoint_real (by norm_num) (by norm_num) (by norm_num) s

theorem arm₁_real (s : Set ℕ) : arm₁.real s =
    s.indicator (fun _ => 1 / 10) 1 + s.indicator (fun _ => 3 / 10) 2 +
      s.indicator (fun _ => 3 / 5) 3 :=
  threePoint_real (by norm_num) (by norm_num) (by norm_num) s

theorem arm₂_real (s : Set ℕ) : arm₂.real s =
    s.indicator (fun _ => 1 / 10) 1 + s.indicator (fun _ => 27 / 80) 2 +
      s.indicator (fun _ => 9 / 16) 3 :=
  threePoint_real (by norm_num) (by norm_num) (by norm_num) s

instance : IsProbabilityMeasure arm₀ :=
  isProbabilityMeasure_threePoint (by norm_num) (by norm_num) (by norm_num) (by norm_num)

instance : IsProbabilityMeasure arm₁ :=
  isProbabilityMeasure_threePoint (by norm_num) (by norm_num) (by norm_num) (by norm_num)

instance : IsProbabilityMeasure arm₂ :=
  isProbabilityMeasure_threePoint (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The period-specific hazard ratio changes over time (`1/2` at time `1`, `4/3` at time `2`)
while the survival and the risk at time `2` coincide in the two arms (`3/5` and `2/5`), so the
risk ratio at time `2` is `1`; the survivals at time `1` differ (`9/10` versus `4/5`). Both
arms have positive at-risk probability and positive hazards at times `1` and `2`. -/
theorem hazardRatio_changes_risk_ratio_one :
    hazardRatio arm₁ id arm₀ id 1 = 1 / 2 ∧ hazardRatio arm₁ id arm₀ id 2 = 4 / 3 ∧
      survival arm₁ id 2 = survival arm₀ id 2 ∧ risk arm₁ id 2 / risk arm₀ id 2 = 1 ∧
      survival arm₁ id 1 ≠ survival arm₀ id 1 ∧
      0 < atRisk arm₀ id 2 ∧ 0 < atRisk arm₁ id 2 ∧
      0 < hazard arm₀ id 1 ∧ 0 < hazard arm₀ id 2 := by
  simp only [hazardRatio, hazard, risk, survival, atRisk, arm₀_real, arm₁_real, id,
    Set.indicator_apply, Set.mem_ofPred_eq]
  norm_num

/-- The average of the hazard ratios at times `1` and `2` (here `1/2` and `3/2`), weighted by
the distribution of the event time in arm `0` among those with the event by time `2`
(`w k = P(T₀ = k) / P(T₀ ≤ 2)`, here `1/2` each), equals `1`, yet the survivals at time `2`
differ (`9/16` versus `3/5`). -/
theorem weighted_hazardRatio_eq_one_survival_ne :
    (∑ k ∈ Finset.Icc 1 2,
        arm₀.real {x | x = k} / arm₀.real {x | x ≤ 2} * hazardRatio arm₂ id arm₀ id k) = 1 ∧
      survival arm₂ id 2 ≠ survival arm₀ id 2 := by
  simp only [Finset.sum_Icc_succ_top (show 1 ≤ 1 + 1 by norm_num), Finset.Icc_self,
    Finset.sum_singleton, hazardRatio, hazard, survival, atRisk, arm₀_real, arm₂_real, id,
    Set.indicator_apply, Set.mem_ofPred_eq]
  norm_num

/-- Arm `0` of the third example: masses `1/2, 0, 1/2` at times `1, 2, 3`; hazards `1/2` at
time `1` and `0` at time `2`. -/
noncomputable def arm₃ : Measure ℕ := threePoint (1 / 2) 0 (1 / 2)

/-- Arm `1` of the third example: masses `1/2, 1/4, 1/4` at times `1, 2, 3`; hazards `1/2` at
time `1` and `1/2` at time `2`. -/
noncomputable def arm₄ : Measure ℕ := threePoint (1 / 2) (1 / 4) (1 / 4)

theorem arm₃_real (s : Set ℕ) : arm₃.real s =
    s.indicator (fun _ => 1 / 2) 1 + s.indicator (fun _ => 0) 2 +
      s.indicator (fun _ => 1 / 2) 3 :=
  threePoint_real (by norm_num) (by norm_num) (by norm_num) s

instance : IsProbabilityMeasure arm₃ :=
  isProbabilityMeasure_threePoint (by norm_num) (by norm_num) (by norm_num) (by norm_num)

instance : IsProbabilityMeasure arm₄ :=
  isProbabilityMeasure_threePoint (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem arm₄_real (s : Set ℕ) : arm₄.real s =
    s.indicator (fun _ => 1 / 2) 1 + s.indicator (fun _ => 1 / 4) 2 +
      s.indicator (fun _ => 1 / 4) 3 :=
  threePoint_real (by norm_num) (by norm_num) (by norm_num) s

/-- A hazard ratio equal to `1` wherever it is defined does not give equal survival. With
arm `0` `arm₃` and arm `1` `arm₄`, at every time `m ≤ 2` at which the reference hazard is
positive the hazard ratio is `1`; yet at time `2` arm `0` has positive at-risk probability and
hazard `0` while arm `1` has hazard `1/2`, and the survivals at time `2` are `1/4` and `1/2`.
So `survival_eq_survival_of_hazard_eq` needs hazard equality at every time of positive at-risk
probability, including the times at which the reference hazard is zero. -/
theorem hazardRatio_one_where_defined_survival_ne :
    (∀ m ≤ 2, 0 < hazard arm₃ id m → hazardRatio arm₄ id arm₃ id m = 1) ∧
      0 < atRisk arm₃ id 2 ∧ hazard arm₃ id 2 = 0 ∧ hazard arm₄ id 2 = 1 / 2 ∧
      survival arm₄ id 2 = 1 / 4 ∧ survival arm₃ id 2 = 1 / 2 := by
  refine ⟨fun m hm => ?_, ?_⟩
  · rcases m with _ | _ | _ | m
    all_goals try (simp only [hazardRatio, hazard, atRisk, arm₃_real, arm₄_real, id,
      Set.indicator_apply, Set.mem_ofPred_eq]; norm_num; done)
    omega
  · simp only [hazard, survival, atRisk, arm₃_real, arm₄_real, id,
      Set.indicator_apply, Set.mem_ofPred_eq]
    norm_num

/-- Numerical instance of Technical Point 8.1 (the book gives no numbers), arm `a`, frailty
stratum `u = 1`: time `1` risk `0` if treated and
`1/4` if untreated, then time `2` risk `1/4` among the survivors in both arms. As masses at
times `1, 2, 3`: treated `0, 1/4, 3/4`; untreated `1/4, 3/16, 9/16`. -/
noncomputable def tp81Stratum₁ (a : Bool) : Measure ℕ :=
  if a then threePoint 0 (1 / 4) (3 / 4) else threePoint (1 / 4) (3 / 16) (9 / 16)

/-- Numerical instance of Technical Point 8.1, arm `a`, frailty stratum `u = 0`: time `1`
risk `1/4` if treated and `1/2` if untreated, then time `2` risk `1/2` among the survivors
in both arms. As masses at times `1, 2, 3`: treated `1/4, 3/8, 3/8`; untreated `1/2, 1/4, 1/4`. -/
noncomputable def tp81Stratum₀ (a : Bool) : Measure ℕ :=
  if a then threePoint (1 / 4) (3 / 8) (3 / 8) else threePoint (1 / 2) (1 / 4) (1 / 4)

/-- Numerical instance of Technical Point 8.1, the law of the event time in arm `a`: the
mixture with weights `1/2` of the two frailty strata, masses `1/8, 5/16, 9/16` if treated
and `3/8, 7/32, 13/32` if untreated (`tp81Arm_real_eq_mix`). -/
noncomputable def tp81Arm (a : Bool) : Measure ℕ :=
  if a then threePoint (1 / 8) (5 / 16) (9 / 16) else threePoint (3 / 8) (7 / 32) (13 / 32)

theorem tp81Stratum₁_real (a : Bool) (s : Set ℕ) : (tp81Stratum₁ a).real s =
    if a then s.indicator (fun _ => 0) 1 + s.indicator (fun _ => 1 / 4) 2 +
        s.indicator (fun _ => 3 / 4) 3
      else s.indicator (fun _ => 1 / 4) 1 + s.indicator (fun _ => 3 / 16) 2 +
        s.indicator (fun _ => 9 / 16) 3 := by
  cases a <;> exact threePoint_real (by norm_num) (by norm_num) (by norm_num) s

theorem tp81Stratum₀_real (a : Bool) (s : Set ℕ) : (tp81Stratum₀ a).real s =
    if a then s.indicator (fun _ => 1 / 4) 1 + s.indicator (fun _ => 3 / 8) 2 +
        s.indicator (fun _ => 3 / 8) 3
      else s.indicator (fun _ => 1 / 2) 1 + s.indicator (fun _ => 1 / 4) 2 +
        s.indicator (fun _ => 1 / 4) 3 := by
  cases a <;> exact threePoint_real (by norm_num) (by norm_num) (by norm_num) s

theorem tp81Arm_real (a : Bool) (s : Set ℕ) : (tp81Arm a).real s =
    if a then s.indicator (fun _ => 1 / 8) 1 + s.indicator (fun _ => 5 / 16) 2 +
        s.indicator (fun _ => 9 / 16) 3
      else s.indicator (fun _ => 3 / 8) 1 + s.indicator (fun _ => 7 / 32) 2 +
        s.indicator (fun _ => 13 / 32) 3 := by
  cases a <;> exact threePoint_real (by norm_num) (by norm_num) (by norm_num) s

/-- The arm law is the equal-weight mixture of the two frailty strata. -/
theorem tp81Arm_real_eq_mix (a : Bool) (s : Set ℕ) :
    (tp81Arm a).real s = 1 / 2 * (tp81Stratum₁ a).real s + 1 / 2 * (tp81Stratum₀ a).real s := by
  classical
  rw [tp81Arm_real, tp81Stratum₁_real, tp81Stratum₀_real]
  cases a <;> simp only [Bool.false_eq_true, ↓reduceIte, Set.indicator_apply] <;>
    split_ifs <;> norm_num

/-- A numerical instance of What If Technical Point 8.1 with `hazardRatio`: the hazard ratio of
the treated arm versus the untreated arm is `1/3` at time `1` and `50/49` at time `2`, although
within each frailty stratum the time `2` hazards are equal in the two arms (hazard ratio `1`).
The time `2` hazard ratio is above `1` because the survivors of time `1` differ in their
frailty distribution between the arms. The same numbers appear in
`CausalInference.Bias.HazardRatio` (`example_hazardRatio1`, `example_hazardRatio2`). -/
theorem techPoint81_hazardRatio :
    hazardRatio (tp81Arm true) id (tp81Arm false) id 1 = 1 / 3 ∧
      hazardRatio (tp81Arm true) id (tp81Arm false) id 2 = 50 / 49 ∧
      hazardRatio (tp81Stratum₁ true) id (tp81Stratum₁ false) id 2 = 1 ∧
      hazardRatio (tp81Stratum₀ true) id (tp81Stratum₀ false) id 2 = 1 := by
  simp only [hazardRatio, hazard, atRisk, tp81Arm_real, tp81Stratum₁_real, tp81Stratum₀_real,
    id, Bool.false_eq_true, ↓reduceIte, Set.indicator_apply, Set.mem_ofPred_eq]
  norm_num

end ComparisonExample

end Survival

end CausalInference
