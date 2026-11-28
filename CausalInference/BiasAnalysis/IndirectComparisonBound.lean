/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.BiasAnalysis.IndirectComparisonEValue
public import Mathlib.Topology.Algebra.Order.Field

/-!
# Unmeasured confounding in an indirect comparison

An indirect comparison of `A` with `B` combines two source comparisons. In the **anchored** form
the source comparisons are `A` against a common comparator `C` and `B` against `C`, each a risk
ratio, and the indirect risk ratio is their quotient. In the **unanchored** form each source
reports one arm level quantity (the risk under `A` in one population, under `B` in another), and
the indirect ratio compares them as if they had been measured in a common target population.

Each source carries its own unmeasured binary covariate `U`, described by the stratum risk model
of `Sensitivity/BiasFormulas.lean`: stratum risks `m a u = P(D = 1 | arm a, U = u)` and
prevalences `π a = P(U = 1 | arm a)`. In the anchored form the bias of a source is the ratio
`crudeRR m π / standardizedRR m r` of its observed to its `U`-standardized risk ratio. The two
biases combine as a quotient, so the bias of the indirect ratio is bounded by the product of the
two bounding factors when the first source is biased upward and the second downward; this is the
direction in which confounding inflates the indirect ratio. The least common strength of the four
confounding parameters that can move an indirect ratio `RR > 1` to the null is then
`eValue √RR`, and this value is attained.

## Main definitions

* `standardizedRR`: the risk ratio standardized to a reference prevalence of `U`.
* `prevMean`: the risk of an arm in a population where `U` has prevalence `p`.
* `requiredStrength ρ y = ρ (y - 1) / (y - ρ)`: the exposure strength needed to explain away a
  ratio `ρ` when the outcome strength is `y`.

## Main results

* `inv_crudeRR_div_standardizedRR_le`: the downward bias of a source is bounded by the bounding
  factor of the comparison with the arms exchanged.
* `anchored_indirect_bias_le`: the bias of the anchored indirect risk ratio is at most
  `boundingFactor K₁ L₁ * boundingFactor K₂ L₂`; `anchored_explainAway_le` is the explain away
  form.
* `unanchored_indirect_bias_le`: the same product bound for the unanchored ratio, with the
  prevalence ratios taken between each source population and the target.
* `eValue_sqrt_le_max_of_le_mul`, `isLeast_eValue_sqrt`: the least common strength that makes
  the product of two bounding factors reach `RR` is `eValue √RR`.
* `anchored_eValue_sqrt_le_max`: a confounding pattern that moves an anchored indirect ratio
  `RR > 1` to the null has a parameter at least `eValue √RR`; `anchored_explainAway_attained`:
  a pattern with all four parameters equal to `eValue √RR` does it exactly.
* `unanchored_eValue_sqrt_le_max`: the same necessary condition for the unanchored ratio.
* `boundingFactor_requiredStrength`, `isLeast_requiredStrength`, `explainAway_set_eq_empty`,
  `requiredStrength_properties`: for a fixed outcome strength `y > ρ` the least exposure strength
  is `requiredStrength ρ y`; for `1 ≤ y ≤ ρ` none exists; as a function of `y` it decreases from
  `+∞` to the unattained limit `ρ` and crosses the diagonal at `eValue ρ`.

## References

* P. Ding and T. J. VanderWeele, *Sensitivity analysis without assumptions*, Epidemiology 27
  (2016).
* T. J. VanderWeele and P. Ding, *Sensitivity analysis in observational research: introducing the
  E-value*, Annals of Internal Medicine 167 (2017).
-/

@[expose] public section

namespace CausalInference

namespace BiasAnalysis

namespace IndirectComparisonBias

open Set BiasFormulas ExternalAdjustment

/-! ### Objects of one source comparison -/

/-- The risk ratio standardized to the reference prevalence `r = P(U = 1)`:
`standardizedMean m r true / standardizedMean m r false`. When `U` suffices for confounding
control it is the causal risk ratio in the population with prevalence `r`. -/
noncomputable def standardizedRR (m : Bool → Bool → ℝ) (r : ℝ) : ℝ :=
  standardizedMean m r true / standardizedMean m r false

/-- Exchanging the two arms of a source comparison: the stratum risks `m (!a) u` and the
prevalences `π (!a)` have the inverse observed risk ratio. -/
theorem crudeRR_swap (m : Bool → Bool → ℝ) (π : Bool → ℝ) :
    crudeRR (fun a u => m (!a) u) (fun a => π (!a)) = (crudeRR m π)⁻¹ := by
  simp only [crudeRR, observedMean, Bool.not_true, Bool.not_false, inv_div]

/-- Exchanging the two arms inverts the standardized risk ratio. -/
theorem standardizedRR_swap (m : Bool → Bool → ℝ) (r : ℝ) :
    standardizedRR (fun a u => m (!a) u) r = (standardizedRR m r)⁻¹ := by
  simp only [standardizedRR, standardizedMean, Bool.not_true, Bool.not_false, inv_div]

/-- The upward bias of a source: `ratio_le_boundingFactor` in terms of `crudeRR` and
`standardizedRR`. -/
theorem crudeRR_div_standardizedRR_le {m : Bool → Bool → ℝ} {π : Bool → ℝ} {w r K L : ℝ}
    (hm : ∀ a u, 0 < m a u) (hπ₀ : 0 < π false) (hπ₀' : π false < 1) (hπ₁ : 0 ≤ π true)
    (hπ₁' : π true ≤ 1) (hw : 0 ≤ w) (hw' : w ≤ 1) (hr : r = w * π true + (1 - w) * π false)
    (hK₁ : π true ≤ K * π false) (hK₀ : 1 - π true ≤ K * (1 - π false))
    (hL : ∀ a, m a true ≤ L * m a false ∧ m a false ≤ L * m a true) :
    crudeRR m π / standardizedRR m r ≤ boundingFactor K L :=
  ratio_le_boundingFactor hm hπ₀ hπ₀' hπ₁ hπ₁' hw hw' hr hK₁ hK₀ hL

/-- **The downward bias of a source.** If the parameters `K, L` bound the comparison with the
two arms exchanged (prevalence ratios of the second arm to the first, risk ratios of `U` in both
directions), the inverse bias `standardizedRR / crudeRR` is at most `boundingFactor K L`. -/
theorem inv_crudeRR_div_standardizedRR_le {m : Bool → Bool → ℝ} {π : Bool → ℝ} {w r K L : ℝ}
    (hm : ∀ a u, 0 < m a u) (hπ₁ : 0 < π true) (hπ₁' : π true < 1) (hπ₀ : 0 ≤ π false)
    (hπ₀' : π false ≤ 1) (hw : 0 ≤ w) (hw' : w ≤ 1) (hr : r = w * π false + (1 - w) * π true)
    (hK₁ : π false ≤ K * π true) (hK₀ : 1 - π false ≤ K * (1 - π true))
    (hL : ∀ a, m a true ≤ L * m a false ∧ m a false ≤ L * m a true) :
    (crudeRR m π / standardizedRR m r)⁻¹ ≤ boundingFactor K L := by
  have h := crudeRR_div_standardizedRR_le (m := fun a u => m (!a) u) (π := fun a => π (!a))
    (w := w) (r := r) (fun a u => hm _ _) hπ₁ hπ₁' hπ₀ hπ₀' hw hw' hr hK₁ hK₀
    (fun a => hL (!a))
  rw [crudeRR_swap, standardizedRR_swap, inv_div_inv] at h
  rwa [inv_div]

/-- The observed risk ratio of a source with positive stratum risks and prevalences in `[0, 1]`
is positive. -/
theorem crudeRR_pos {m : Bool → Bool → ℝ} {π : Bool → ℝ} (hm : ∀ a u, 0 < m a u)
    (hπ : ∀ a, 0 ≤ π a ∧ π a ≤ 1) : 0 < crudeRR m π :=
  div_pos (convex_comb_pos (hπ true).1 (hπ true).2 (hm _ _) (hm _ _))
    (convex_comb_pos (hπ false).1 (hπ false).2 (hm _ _) (hm _ _))

/-- The standardized risk ratio with positive stratum risks and `r ∈ [0, 1]` is positive. -/
theorem standardizedRR_pos {m : Bool → Bool → ℝ} {r : ℝ} (hm : ∀ a u, 0 < m a u)
    (hr : 0 ≤ r) (hr' : r ≤ 1) : 0 < standardizedRR m r :=
  div_pos (convex_comb_pos hr hr' (hm _ _) (hm _ _)) (convex_comb_pos hr hr' (hm _ _) (hm _ _))

/-- A mixture `w x + (1 - w) y` of two points of `[0, 1]` lies in `[0, 1]`. -/
lemma mix_mem_unit {w x y : ℝ} (hw : 0 ≤ w) (hw' : w ≤ 1) (hx : 0 ≤ x) (hx' : x ≤ 1)
    (hy : 0 ≤ y) (hy' : y ≤ 1) : 0 ≤ w * x + (1 - w) * y ∧ w * x + (1 - w) * y ≤ 1 := by
  constructor <;> nlinarith [mul_nonneg hw hx, mul_nonneg (sub_nonneg.2 hw') hy,
    mul_nonneg hw (sub_nonneg.2 hx'), mul_nonneg (sub_nonneg.2 hw') (sub_nonneg.2 hy')]

/-- A prevalence ratio parameter is at least one: if `x ≤ K y` and `1 - x ≤ K (1 - y)`, then
adding gives `1 ≤ K`. -/
lemma one_le_of_prevalence_bounds {x y K : ℝ} (h₁ : x ≤ K * y) (h₀ : 1 - x ≤ K * (1 - y)) :
    1 ≤ K := by linarith

/-- A risk ratio parameter bounding a positive ratio in both directions is at least one. -/
lemma one_le_of_risk_bounds {x y L : ℝ} (hx : 0 < x) (hy : 0 < y) (h₁ : x ≤ L * y)
    (h₀ : y ≤ L * x) : 1 ≤ L := by
  have hL : 0 < L := by
    by_contra hneg
    rw [not_lt] at hneg
    nlinarith
  by_contra hlt
  rw [not_le] at hlt
  nlinarith [mul_pos hL hx, mul_pos hL hy]

/-! ### The anchored indirect comparison -/

/-- **The bias of the anchored indirect risk ratio.** The first source compares `A` with `C`
(stratum risks `m₁`, prevalences `π₁`, reference prevalence `r₁`), the second compares `B` with
`C` (`m₂`, `π₂`, `r₂`). The observed indirect ratio is `crudeRR m₁ π₁ / crudeRR m₂ π₂`, the
`U`-standardized one `standardizedRR m₁ r₁ / standardizedRR m₂ r₂`. If `K₁, L₁` bound the first
source as in `ratio_le_boundingFactor` and `K₂, L₂` bound the second with its arms exchanged,
the observed indirect ratio is at most `boundingFactor K₁ L₁ * boundingFactor K₂ L₂` times the
standardized one. -/
theorem anchored_indirect_bias_le {m₁ m₂ : Bool → Bool → ℝ} {π₁ π₂ : Bool → ℝ}
    {w₁ w₂ r₁ r₂ K₁ L₁ K₂ L₂ : ℝ}
    (hm₁ : ∀ a u, 0 < m₁ a u) (hπ₁₀ : 0 < π₁ false) (hπ₁₀' : π₁ false < 1)
    (hπ₁₁ : 0 ≤ π₁ true) (hπ₁₁' : π₁ true ≤ 1) (hw₁ : 0 ≤ w₁) (hw₁' : w₁ ≤ 1)
    (hr₁ : r₁ = w₁ * π₁ true + (1 - w₁) * π₁ false)
    (hK₁ : π₁ true ≤ K₁ * π₁ false) (hK₁' : 1 - π₁ true ≤ K₁ * (1 - π₁ false))
    (hL₁ : ∀ a, m₁ a true ≤ L₁ * m₁ a false ∧ m₁ a false ≤ L₁ * m₁ a true)
    (hm₂ : ∀ a u, 0 < m₂ a u) (hπ₂₁ : 0 < π₂ true) (hπ₂₁' : π₂ true < 1)
    (hπ₂₀ : 0 ≤ π₂ false) (hπ₂₀' : π₂ false ≤ 1) (hw₂ : 0 ≤ w₂) (hw₂' : w₂ ≤ 1)
    (hr₂ : r₂ = w₂ * π₂ false + (1 - w₂) * π₂ true)
    (hK₂ : π₂ false ≤ K₂ * π₂ true) (hK₂' : 1 - π₂ false ≤ K₂ * (1 - π₂ true))
    (hL₂ : ∀ a, m₂ a true ≤ L₂ * m₂ a false ∧ m₂ a false ≤ L₂ * m₂ a true) :
    (crudeRR m₁ π₁ / crudeRR m₂ π₂) / (standardizedRR m₁ r₁ / standardizedRR m₂ r₂) ≤
      boundingFactor K₁ L₁ * boundingFactor K₂ L₂ := by
  have h₁ := crudeRR_div_standardizedRR_le hm₁ hπ₁₀ hπ₁₀' hπ₁₁ hπ₁₁' hw₁ hw₁' hr₁ hK₁ hK₁' hL₁
  have h₂ := inv_crudeRR_div_standardizedRR_le hm₂ hπ₂₁ hπ₂₁' hπ₂₀ hπ₂₀' hw₂ hw₂' hr₂ hK₂ hK₂'
    hL₂
  subst hr₁ hr₂
  have hc₁ := crudeRR_pos (π := π₁) hm₁ (fun a => by cases a <;> constructor <;> linarith)
  have hs₁ := standardizedRR_pos hm₁ (mix_mem_unit hw₁ hw₁' hπ₁₁ hπ₁₁' hπ₁₀.le hπ₁₀'.le).1
    (mix_mem_unit hw₁ hw₁' hπ₁₁ hπ₁₁' hπ₁₀.le hπ₁₀'.le).2
  have hb₁ : 0 ≤ crudeRR m₁ π₁ / standardizedRR m₁ _ := (div_pos hc₁ hs₁).le
  have hb₂ : 0 ≤ (crudeRR m₂ π₂ /
      standardizedRR m₂ (w₂ * π₂ false + (1 - w₂) * π₂ true))⁻¹ := by
    have hc₂ := crudeRR_pos (π := π₂) hm₂ (fun a => by cases a <;> constructor <;> linarith)
    have hs₂ := standardizedRR_pos hm₂ (mix_mem_unit hw₂ hw₂' hπ₂₀ hπ₂₀' hπ₂₁.le hπ₂₁'.le).1
      (mix_mem_unit hw₂ hw₂' hπ₂₀ hπ₂₀' hπ₂₁.le hπ₂₁'.le).2
    exact (inv_pos.2 (div_pos hc₂ hs₂)).le
  rw [div_div_div_comm, div_eq_mul_inv]
  exact mul_le_mul h₁ h₂ hb₂ (hb₁.trans h₁)

/-- **Explaining away an anchored indirect comparison.** Under the hypotheses of
`anchored_indirect_bias_le`, if the `U`-standardized indirect ratio is at most one (the
confounding explains the observed association away), then the observed indirect ratio is at most
`boundingFactor K₁ L₁ * boundingFactor K₂ L₂`. -/
theorem anchored_explainAway_le {m₁ m₂ : Bool → Bool → ℝ} {π₁ π₂ : Bool → ℝ}
    {w₁ w₂ r₁ r₂ K₁ L₁ K₂ L₂ : ℝ}
    (hm₁ : ∀ a u, 0 < m₁ a u) (hπ₁₀ : 0 < π₁ false) (hπ₁₀' : π₁ false < 1)
    (hπ₁₁ : 0 ≤ π₁ true) (hπ₁₁' : π₁ true ≤ 1) (hw₁ : 0 ≤ w₁) (hw₁' : w₁ ≤ 1)
    (hr₁ : r₁ = w₁ * π₁ true + (1 - w₁) * π₁ false)
    (hK₁ : π₁ true ≤ K₁ * π₁ false) (hK₁' : 1 - π₁ true ≤ K₁ * (1 - π₁ false))
    (hL₁ : ∀ a, m₁ a true ≤ L₁ * m₁ a false ∧ m₁ a false ≤ L₁ * m₁ a true)
    (hm₂ : ∀ a u, 0 < m₂ a u) (hπ₂₁ : 0 < π₂ true) (hπ₂₁' : π₂ true < 1)
    (hπ₂₀ : 0 ≤ π₂ false) (hπ₂₀' : π₂ false ≤ 1) (hw₂ : 0 ≤ w₂) (hw₂' : w₂ ≤ 1)
    (hr₂ : r₂ = w₂ * π₂ false + (1 - w₂) * π₂ true)
    (hK₂ : π₂ false ≤ K₂ * π₂ true) (hK₂' : 1 - π₂ false ≤ K₂ * (1 - π₂ true))
    (hL₂ : ∀ a, m₂ a true ≤ L₂ * m₂ a false ∧ m₂ a false ≤ L₂ * m₂ a true)
    (hnull : standardizedRR m₁ r₁ / standardizedRR m₂ r₂ ≤ 1) :
    crudeRR m₁ π₁ / crudeRR m₂ π₂ ≤ boundingFactor K₁ L₁ * boundingFactor K₂ L₂ := by
  have h := anchored_indirect_bias_le hm₁ hπ₁₀ hπ₁₀' hπ₁₁ hπ₁₁' hw₁ hw₁' hr₁ hK₁ hK₁' hL₁
    hm₂ hπ₂₁ hπ₂₁' hπ₂₀ hπ₂₀' hw₂ hw₂' hr₂ hK₂ hK₂' hL₂
  subst hr₁ hr₂
  have hs : 0 < standardizedRR m₁ (w₁ * π₁ true + (1 - w₁) * π₁ false) /
      standardizedRR m₂ (w₂ * π₂ false + (1 - w₂) * π₂ true) :=
    div_pos (standardizedRR_pos hm₁ (mix_mem_unit hw₁ hw₁' hπ₁₁ hπ₁₁' hπ₁₀.le hπ₁₀'.le).1
      (mix_mem_unit hw₁ hw₁' hπ₁₁ hπ₁₁' hπ₁₀.le hπ₁₀'.le).2)
      (standardizedRR_pos hm₂ (mix_mem_unit hw₂ hw₂' hπ₂₀ hπ₂₀' hπ₂₁.le hπ₂₁'.le).1
      (mix_mem_unit hw₂ hw₂' hπ₂₀ hπ₂₀' hπ₂₁.le hπ₂₁'.le).2)
  rw [div_le_iff₀ hs] at h
  have hc : 0 ≤ crudeRR m₁ π₁ / crudeRR m₂ π₂ :=
    (div_pos (crudeRR_pos (π := π₁) hm₁ (fun a => by cases a <;> constructor <;> linarith))
      (crudeRR_pos (π := π₂) hm₂ (fun a => by cases a <;> constructor <;> linarith))).le
  have hB : 0 ≤ boundingFactor K₁ L₁ * boundingFactor K₂ L₂ := by
    have := mul_nonneg hc hs.le
    nlinarith
  nlinarith

/-! ### The least common strength for an indirect comparison -/

/-- **The product of two bounding factors.** For `RR > 1` and four parameters at least one, if
`RR ≤ boundingFactor a₁ b₁ * boundingFactor a₂ b₂`, then the largest parameter is at least
`eValue √RR`. -/
theorem eValue_sqrt_le_max_of_le_mul {RR a₁ b₁ a₂ b₂ : ℝ} (hRR : 1 < RR) (ha₁ : 1 ≤ a₁)
    (hb₁ : 1 ≤ b₁) (ha₂ : 1 ≤ a₂) (hb₂ : 1 ≤ b₂)
    (h : RR ≤ boundingFactor a₁ b₁ * boundingFactor a₂ b₂) :
    eValue (Real.sqrt RR) ≤ max (max a₁ b₁) (max a₂ b₂) := by
  set M := max (max a₁ b₁) (max a₂ b₂) with hM
  have hM1 : 1 ≤ M := ha₁.trans ((le_max_left _ _).trans (le_max_left _ _))
  have hle₁ : boundingFactor a₁ b₁ ≤ boundingFactor M M :=
    boundingFactor_mono ha₁ ((le_max_left _ _).trans (le_max_left _ _)) hb₁
      ((le_max_right _ _).trans (le_max_left _ _))
  have hle₂ : boundingFactor a₂ b₂ ≤ boundingFactor M M :=
    boundingFactor_mono ha₂ ((le_max_left _ _).trans (le_max_right _ _)) hb₂
      ((le_max_right _ _).trans (le_max_right _ _))
  have hsq : RR ≤ boundingFactor M M ^ 2 := by
    rw [sq]
    exact h.trans (mul_le_mul hle₁ hle₂ (boundingFactor_nonneg ha₂ hb₂)
      (boundingFactor_nonneg hM1 hM1))
  have hroot : Real.sqrt RR ≤ boundingFactor M M := by
    rw [Real.sqrt_le_left (boundingFactor_nonneg hM1 hM1)]
    exact hsq
  have h1 : 1 < Real.sqrt RR := by
    rw [Real.lt_sqrt zero_le_one]; simpa using hRR
  exact (le_boundingFactor_self_iff h1 hM1).1 hroot

/-- **The least common strength for two bounding factors**: for `RR ≥ 1`, `eValue √RR` is the
least `v ≥ 1` with `RR ≤ boundingFactor v v * boundingFactor v v`. -/
theorem isLeast_eValue_sqrt {RR : ℝ} (hRR : 1 ≤ RR) :
    IsLeast {v | 1 ≤ v ∧ RR ≤ boundingFactor v v * boundingFactor v v}
      (eValue (Real.sqrt RR)) := by
  have h1 : 1 ≤ Real.sqrt RR := by
    rw [Real.le_sqrt zero_le_one (by linarith)]; simpa using hRR
  refine ⟨⟨one_le_eValue (zero_lt_one.trans_le h1), ?_⟩, fun v hv => ?_⟩
  · rw [boundingFactor_eValue h1, Real.mul_self_sqrt (by linarith)]
  · have hroot : Real.sqrt RR ≤ boundingFactor v v := by
      rw [Real.sqrt_le_left (boundingFactor_nonneg hv.1 hv.1), sq]
      exact hv.2
    exact (isLeast_eValue h1).2 ⟨hv.1, hroot⟩

/-- **The E-value of an anchored indirect comparison.** Under the hypotheses of
`anchored_explainAway_le`, a confounding pattern that moves an observed indirect ratio `RR > 1`
to the null (`U`-standardized indirect ratio at most one) has a parameter at least
`eValue √RR`. The parameters are at least one by the hypotheses. -/
theorem anchored_eValue_sqrt_le_max {m₁ m₂ : Bool → Bool → ℝ} {π₁ π₂ : Bool → ℝ}
    {w₁ w₂ r₁ r₂ K₁ L₁ K₂ L₂ : ℝ}
    (hm₁ : ∀ a u, 0 < m₁ a u) (hπ₁₀ : 0 < π₁ false) (hπ₁₀' : π₁ false < 1)
    (hπ₁₁ : 0 ≤ π₁ true) (hπ₁₁' : π₁ true ≤ 1) (hw₁ : 0 ≤ w₁) (hw₁' : w₁ ≤ 1)
    (hr₁ : r₁ = w₁ * π₁ true + (1 - w₁) * π₁ false)
    (hK₁ : π₁ true ≤ K₁ * π₁ false) (hK₁' : 1 - π₁ true ≤ K₁ * (1 - π₁ false))
    (hL₁ : ∀ a, m₁ a true ≤ L₁ * m₁ a false ∧ m₁ a false ≤ L₁ * m₁ a true)
    (hm₂ : ∀ a u, 0 < m₂ a u) (hπ₂₁ : 0 < π₂ true) (hπ₂₁' : π₂ true < 1)
    (hπ₂₀ : 0 ≤ π₂ false) (hπ₂₀' : π₂ false ≤ 1) (hw₂ : 0 ≤ w₂) (hw₂' : w₂ ≤ 1)
    (hr₂ : r₂ = w₂ * π₂ false + (1 - w₂) * π₂ true)
    (hK₂ : π₂ false ≤ K₂ * π₂ true) (hK₂' : 1 - π₂ false ≤ K₂ * (1 - π₂ true))
    (hL₂ : ∀ a, m₂ a true ≤ L₂ * m₂ a false ∧ m₂ a false ≤ L₂ * m₂ a true)
    (hnull : standardizedRR m₁ r₁ / standardizedRR m₂ r₂ ≤ 1)
    (hRR : 1 < crudeRR m₁ π₁ / crudeRR m₂ π₂) :
    eValue (Real.sqrt (crudeRR m₁ π₁ / crudeRR m₂ π₂)) ≤ max (max K₁ L₁) (max K₂ L₂) := by
  have h := anchored_explainAway_le hm₁ hπ₁₀ hπ₁₀' hπ₁₁ hπ₁₁' hw₁ hw₁' hr₁ hK₁ hK₁' hL₁
    hm₂ hπ₂₁ hπ₂₁' hπ₂₀ hπ₂₀' hw₂ hw₂' hr₂ hK₂ hK₂' hL₂ hnull
  exact eValue_sqrt_le_max_of_le_mul hRR (one_le_of_prevalence_bounds hK₁ hK₁')
    (one_le_of_risk_bounds (hm₁ true true) (hm₁ true false) (hL₁ true).1 (hL₁ true).2)
    (one_le_of_prevalence_bounds hK₂ hK₂')
    (one_le_of_risk_bounds (hm₂ true true) (hm₂ true false) (hL₂ true).1 (hL₂ true).2) h

/-- **The anchored E-value is attained.** For an indirect ratio `RR > 1` let `E = eValue √RR`.
Take in both sources the stratum risks `m a u = E` for `U = 1` and `1` for `U = 0` in both arms
(no effect within levels of `U`, so the standardized risk ratio is one at every reference
prevalence in `[0, 1]`), the prevalences
`π₁ = (1, 1/E)` in the first source and `π₂ = (1/E, 1)` in the second. All four parameters of
`anchored_explainAway_le` can be taken equal to `E` (with `w₁ = w₂ = 1`), and the observed
indirect ratio is exactly `RR`: confounding of common strength `E` explains it away. -/
theorem anchored_explainAway_attained {RR : ℝ} (hRR : 1 < RR) :
    let E := eValue (Real.sqrt RR)
    let m : Bool → Bool → ℝ := fun _ u => cond u E 1
    let π₁ : Bool → ℝ := fun a => cond a 1 E⁻¹
    let π₂ : Bool → ℝ := fun a => cond a E⁻¹ 1
    (∀ a u, 0 < m a u) ∧ (∀ a, m a true ≤ E * m a false ∧ m a false ≤ E * m a true) ∧
      0 < π₁ false ∧ π₁ false < 1 ∧ π₁ true ≤ 1 ∧ π₁ true ≤ E * π₁ false ∧
      1 - π₁ true ≤ E * (1 - π₁ false) ∧
      0 < π₂ true ∧ π₂ true < 1 ∧ π₂ false ≤ 1 ∧ π₂ false ≤ E * π₂ true ∧
      1 - π₂ false ≤ E * (1 - π₂ true) ∧
      (∀ r, 0 ≤ r → r ≤ 1 → standardizedRR m r = 1) ∧ crudeRR m π₁ / crudeRR m π₂ = RR := by
  intro E m π₁ π₂
  have h1 : 1 < Real.sqrt RR := by
    rw [Real.lt_sqrt zero_le_one]; simpa using hRR
  have hE1 : 1 < E := by
    have hE := (isLeast_eValue h1.le).1.1
    rcases hE.lt_or_eq with h | h
    · exact h
    · exfalso
      have := boundingFactor_eValue h1.le
      rw [← h] at this
      norm_num [boundingFactor] at this
      linarith
  have hE0 : 0 < E := by linarith
  have hBF : E * E / (E + E - 1) = Real.sqrt RR := boundingFactor_eValue h1.le
  have hinv : E⁻¹ < 1 := inv_lt_one_of_one_lt₀ hE1
  have hinv0 : 0 < E⁻¹ := inv_pos.2 hE0
  have hEinv : E * E⁻¹ = 1 := mul_inv_cancel₀ hE0.ne'
  have hd : E⁻¹ * E + (1 - E⁻¹) * 1 ≠ 0 := by
    rw [inv_mul_cancel₀ hE0.ne']; linarith
  have hc₁ : crudeRR m π₁ = Real.sqrt RR := by
    rw [← hBF]
    simp only [crudeRR, observedMean, m, π₁, Bool.cond_true, Bool.cond_false]
    rw [div_eq_div_iff hd (by linarith)]
    linear_combination (E - E ^ 2) * hEinv
  have hc₂ : crudeRR m π₂ = (Real.sqrt RR)⁻¹ := by
    rw [← hBF, inv_div]
    simp only [crudeRR, observedMean, m, π₂, Bool.cond_true, Bool.cond_false]
    rw [div_eq_div_iff (by linarith) (by positivity)]
    linear_combination (E ^ 2 - E) * hEinv
  refine ⟨fun a u => ?_, fun a => ?_, hinv0, hinv, le_rfl, ?_, ?_, hinv0, hinv, le_rfl, ?_, ?_,
    fun r hr hr' => ?_, ?_⟩
  · cases u <;> simp [m, hE0]
  · simp only [m, Bool.cond_true, Bool.cond_false]
    constructor <;> nlinarith
  · simp [π₁, hEinv]
  · simp only [π₁, Bool.cond_true, Bool.cond_false]; nlinarith
  · simp [π₂, hEinv]
  · simp only [π₂, Bool.cond_true, Bool.cond_false]; nlinarith
  · simp only [standardizedRR, standardizedMean, m]
    exact div_self (convex_comb_pos hr hr' hE0 one_pos).ne'
  · rw [hc₁, hc₂, div_inv_eq_mul, Real.mul_self_sqrt (by linarith)]

/-! ### The unanchored indirect comparison -/

/-- The risk of an arm in a population where the covariate `U` has prevalence `p`:
`p R(1) + (1 - p) R(0)`, with `R u` the risk of the arm at `U = u`. -/
def prevMean (R : Bool → ℝ) (p : ℝ) : ℝ := p * R true + (1 - p) * R false

/-- **The bias of one arm level quantity.** For positive stratum risks, a target prevalence
`0 < q < 1` and a source prevalence `p ∈ [0, 1]`, the risk of the arm in the source population
divided by its risk in the target is at most `boundingFactor L K`, with `L` the larger risk ratio
of `U` over its two codings and `K` the larger prevalence ratio of source to target over the two
codings (Ding and VanderWeele 2016, applied to the population instead of the exposure). -/
theorem prevMean_div_le {R : Bool → ℝ} {p q : ℝ} (hR₀ : 0 < R false) (hR₁ : 0 < R true)
    (hq : 0 < q) (hq' : q < 1) (hp : 0 ≤ p) (hp' : p ≤ 1) :
    prevMean R p / prevMean R q ≤ boundingFactor (max (R true / R false) (R false / R true))
      (max (p / q) ((1 - p) / (1 - q))) :=
  jointBoundingFactor_null_max (R := R) (π := fun a => cond a p q) hR₀ hR₁ hq hq' hp hp'

/-- The risk of an arm with positive stratum risks is positive at every prevalence in
`[0, 1]`. -/
theorem prevMean_pos {R : Bool → ℝ} {p : ℝ} (hR₀ : 0 < R false) (hR₁ : 0 < R true)
    (hp : 0 ≤ p) (hp' : p ≤ 1) : 0 < prevMean R p :=
  convex_comb_pos hp hp' hR₁ hR₀

/-- **The bias of the unanchored indirect ratio.** Arm `A` is observed in a population where
`U` has prevalence `p₁`, arm `B` in one where it has prevalence `p₂`, and the comparison is
wanted in a target with prevalence `q`. With stratum risks `R_A`, `R_B` positive and
`0 < q < 1`, `0 < p₂ < 1`, `0 ≤ p₁ ≤ 1`, the observed ratio `R_A(p₁) / R_B(p₂)` is at most the
target ratio `R_A(q) / R_B(q)` times `boundingFactor L_A K₁ * boundingFactor L_B K₂`, where
`K₁` compares the first source with the target and `K₂` the target with the second source. -/
theorem unanchored_indirect_bias_le {RA RB : Bool → ℝ} {p₁ p₂ q : ℝ} (hA₀ : 0 < RA false)
    (hA₁ : 0 < RA true) (hB₀ : 0 < RB false) (hB₁ : 0 < RB true) (hq : 0 < q) (hq' : q < 1)
    (hp₁ : 0 ≤ p₁) (hp₁' : p₁ ≤ 1) (hp₂ : 0 < p₂) (hp₂' : p₂ < 1) :
    (prevMean RA p₁ / prevMean RB p₂) / (prevMean RA q / prevMean RB q) ≤
      boundingFactor (max (RA true / RA false) (RA false / RA true))
          (max (p₁ / q) ((1 - p₁) / (1 - q))) *
        boundingFactor (max (RB true / RB false) (RB false / RB true))
          (max (q / p₂) ((1 - q) / (1 - p₂))) := by
  have hA := prevMean_div_le hA₀ hA₁ hq hq' hp₁ hp₁'
  have hB := prevMean_div_le (R := RB) hB₀ hB₁ hp₂ hp₂' hq.le hq'.le
  have hAp := prevMean_pos hA₀ hA₁ hp₁ hp₁'
  have hAq := prevMean_pos hA₀ hA₁ hq.le hq'.le
  have hBp := prevMean_pos hB₀ hB₁ hp₂.le hp₂'.le
  have hBq := prevMean_pos hB₀ hB₁ hq.le hq'.le
  have e : (prevMean RA p₁ / prevMean RB p₂) / (prevMean RA q / prevMean RB q) =
      (prevMean RA p₁ / prevMean RA q) * (prevMean RB q / prevMean RB p₂) := by
    field_simp
  rw [e]
  exact mul_le_mul hA hB (div_pos hBq hBp).le ((div_pos hAp hAq).le.trans hA)

/-- **A necessary strength for an unanchored indirect comparison.** Under the hypotheses of
`unanchored_indirect_bias_le`, if the target ratio is at most one and the observed ratio
`RR = R_A(p₁) / R_B(p₂)` exceeds one, then the largest of the four parameters is at least
`eValue √RR`. -/
theorem unanchored_eValue_sqrt_le_max {RA RB : Bool → ℝ} {p₁ p₂ q : ℝ} (hA₀ : 0 < RA false)
    (hA₁ : 0 < RA true) (hB₀ : 0 < RB false) (hB₁ : 0 < RB true) (hq : 0 < q) (hq' : q < 1)
    (hp₁ : 0 ≤ p₁) (hp₁' : p₁ ≤ 1) (hp₂ : 0 < p₂) (hp₂' : p₂ < 1)
    (hnull : prevMean RA q / prevMean RB q ≤ 1)
    (hRR : 1 < prevMean RA p₁ / prevMean RB p₂) :
    eValue (Real.sqrt (prevMean RA p₁ / prevMean RB p₂)) ≤
      max (max (max (RA true / RA false) (RA false / RA true))
          (max (p₁ / q) ((1 - p₁) / (1 - q))))
        (max (max (RB true / RB false) (RB false / RB true))
          (max (q / p₂) ((1 - q) / (1 - p₂)))) := by
  have h := unanchored_indirect_bias_le hA₀ hA₁ hB₀ hB₁ hq hq' hp₁ hp₁' hp₂ hp₂'
  have ht : 0 < prevMean RA q / prevMean RB q :=
    div_pos (prevMean_pos hA₀ hA₁ hq.le hq'.le) (prevMean_pos hB₀ hB₁ hq.le hq'.le)
  rw [div_le_iff₀ ht] at h
  have hB : 0 ≤ boundingFactor (max (RA true / RA false) (RA false / RA true))
          (max (p₁ / q) ((1 - p₁) / (1 - q))) *
        boundingFactor (max (RB true / RB false) (RB false / RB true))
          (max (q / p₂) ((1 - q) / (1 - p₂))) :=
    mul_nonneg (boundingFactor_nonneg (one_le_max_div hA₁ hA₀) (one_le_max_prevRatio hq hq'))
      (boundingFactor_nonneg (one_le_max_div hB₁ hB₀) (one_le_max_prevRatio hp₂ hp₂'))
  refine eValue_sqrt_le_max_of_le_mul hRR (one_le_max_div hA₁ hA₀) (one_le_max_prevRatio hq hq')
    (one_le_max_div hB₁ hB₀) (one_le_max_prevRatio hp₂ hp₂') ?_
  nlinarith

/-! ### The strength needed when the outcome association is fixed -/

/-- The confounder to exposure strength `ρ (y - 1) / (y - ρ)` that, with confounder to outcome
strength `y`, makes the bounding factor equal to `ρ` (compare `explainAway_one_iff`). -/
noncomputable def requiredStrength (ρ y : ℝ) : ℝ := ρ * (y - 1) / (y - ρ)

/-- **The required strength solves the bounding factor equation.** For `1 < ρ < y`,
`boundingFactor (requiredStrength ρ y) y = ρ` and `requiredStrength ρ y > 1`. -/
theorem boundingFactor_requiredStrength {ρ y : ℝ} (h1 : 1 < ρ) (hy : ρ < y) :
    boundingFactor (requiredStrength ρ y) y = ρ ∧ 1 < requiredStrength ρ y := by
  have hyr : 0 < y - ρ := by linarith
  have hgt : 1 < requiredStrength ρ y := by
    rw [requiredStrength, one_lt_div hyr]; nlinarith
  refine ⟨?_, hgt⟩
  rw [boundingFactor, div_eq_iff (by linarith)]
  unfold requiredStrength
  field_simp
  ring

/-- **The required strength is least.** For `1 < ρ < y`, `requiredStrength ρ y` is the least
`x ≥ 1` with `ρ ≤ boundingFactor x y`. -/
theorem isLeast_requiredStrength {ρ y : ℝ} (h1 : 1 < ρ) (hy : ρ < y) :
    IsLeast {x | 1 ≤ x ∧ ρ ≤ boundingFactor x y} (requiredStrength ρ y) := by
  obtain ⟨hBF, hgt⟩ := boundingFactor_requiredStrength h1 hy
  refine ⟨⟨hgt.le, hBF.ge⟩, fun x hx => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  have := boundingFactor_lt_boundingFactor_left (b := y) hx.1 hlt (by linarith)
  rw [hBF] at this
  linarith [hx.2]

/-- **No confounder to exposure strength suffices when `y ≤ ρ`.** For `ρ > 1` and an outcome
strength `1 ≤ y ≤ ρ`, no `x ≥ 1` has `ρ ≤ boundingFactor x y`: the bounding factor stays below
`y` (`boundingFactor_lt_right`), and equals one at `y = 1`. -/
theorem explainAway_set_eq_empty {ρ y : ℝ} (h1 : 1 < ρ) (hy : 1 ≤ y) (hyρ : y ≤ ρ) :
    {x | 1 ≤ x ∧ ρ ≤ boundingFactor x y} = ∅ := by
  refine eq_empty_of_forall_notMem fun x hx => ?_
  rcases hy.lt_or_eq with hy1 | hy1
  · linarith [boundingFactor_lt_right hx.1 hy1, hx.2]
  · subst hy1
    have : boundingFactor x 1 = 1 := by
      rw [boundingFactor, mul_one, add_sub_cancel_right, div_self (by linarith [hx.1])]
    linarith [hx.2]

/-- The bounding factor tends to its second argument as the first tends to infinity. -/
theorem tendsto_boundingFactor_atTop (y : ℝ) :
    Filter.Tendsto (fun x => boundingFactor x y) Filter.atTop (nhds y) := by
  have h : Filter.Tendsto (fun x : ℝ => y / (1 + (y - 1) * x⁻¹)) Filter.atTop
      (nhds (y / (1 + (y - 1) * 0))) :=
    tendsto_const_nhds.div (tendsto_const_nhds.add (tendsto_const_nhds.mul
      tendsto_inv_atTop_zero)) (by norm_num)
  rw [mul_zero, add_zero, div_one] at h
  refine h.congr' ((Filter.eventually_gt_atTop (max 0 (1 - y))).mono fun x hx => ?_)
  have hx0 : 0 < x := (le_max_left _ _).trans_lt hx
  have : x + y - 1 ≠ 0 := by linarith [(le_max_right 0 (1 - y)).trans_lt hx]
  have hx1 : x ≠ 0 := hx0.ne'
  have e : 1 + (y - 1) * x⁻¹ = (x + y - 1) / x := by field_simp; ring
  simp only [boundingFactor]
  rw [e, div_div_eq_mul_div]
  ring

/-- The required strength exceeds `ρ` for every `y > ρ > 1`: `ρ (y - 1)/(y - ρ) =
ρ + ρ (ρ - 1)/(y - ρ)`. -/
theorem lt_requiredStrength {ρ y : ℝ} (h1 : 1 < ρ) (hy : ρ < y) : ρ < requiredStrength ρ y := by
  rw [requiredStrength, lt_div_iff₀ (by linarith)]
  nlinarith

/-- **The required strength against the outcome strength.** For `ρ > 1`, `y ↦ requiredStrength
ρ y` is strictly decreasing on `y > ρ`, tends to `+∞` as `y` decreases to `ρ` and to `ρ` as
`y → ∞` (a limit not attained, `lt_requiredStrength`); it equals `eValue ρ` at `y = eValue ρ`,
exceeds it for `ρ < y < eValue ρ` and is below it for `y > eValue ρ`. -/
theorem requiredStrength_properties {ρ : ℝ} (h1 : 1 < ρ) :
    StrictAntiOn (requiredStrength ρ) (Ioi ρ) ∧
      Filter.Tendsto (requiredStrength ρ) (nhdsWithin ρ (Ioi ρ)) Filter.atTop ∧
      Filter.Tendsto (requiredStrength ρ) Filter.atTop (nhds ρ) ∧
      requiredStrength ρ (eValue ρ) = eValue ρ ∧
      (∀ y, ρ < y → y < eValue ρ → eValue ρ < requiredStrength ρ y) ∧
      (∀ y, eValue ρ < y → requiredStrength ρ y < eValue ρ) := by
  have hanti : StrictAntiOn (requiredStrength ρ) (Ioi ρ) := by
    intro a (ha : ρ < a) b (hb : ρ < b) hab
    rw [requiredStrength, requiredStrength, div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith [mul_pos (mul_pos (by linarith : (0 : ℝ) < ρ) (by linarith : (0 : ℝ) < ρ - 1))
      (by linarith : (0 : ℝ) < b - a)]
  have hsm : ρ - 1 < Real.sqrt (ρ * (ρ - 1)) := (Real.lt_sqrt (by linarith)).2 (by nlinarith)
  have hρE : ρ < eValue ρ := by rw [eValue_of_one_le h1.le]; linarith
  have hE : requiredStrength ρ (eValue ρ) = eValue ρ := by
    have hBF := boundingFactor_eValue h1.le
    rw [boundingFactor, div_eq_iff (by linarith)] at hBF
    rw [requiredStrength, div_eq_iff (by linarith)]
    linarith
  refine ⟨hanti, ?_, ?_, hE, fun y hy hyE => ?_, fun y hy => ?_⟩
  · have hsub : Filter.Tendsto (fun y : ℝ => y - ρ) (nhdsWithin ρ (Ioi ρ))
        (nhdsWithin 0 (Ioi 0)) :=
      tendsto_nhdsWithin_iff.2 ⟨((continuous_sub_right ρ).tendsto' ρ 0 (sub_self ρ)).mono_left
        nhdsWithin_le_nhds, eventually_nhdsWithin_of_forall fun y (hy : ρ < y) => sub_pos.2 hy⟩
    have hnum : Filter.Tendsto (fun y : ℝ => ρ * (y - 1)) (nhdsWithin ρ (Ioi ρ))
        (nhds (ρ * (ρ - 1))) :=
      ((continuous_const.mul (continuous_sub_right 1)).tendsto ρ).mono_left nhdsWithin_le_nhds
    refine (Filter.Tendsto.pos_mul_atTop (by nlinarith) hnum
      (tendsto_inv_nhdsGT_zero.comp hsub)).congr fun y => ?_
    simp [requiredStrength, div_eq_mul_inv]
  · have hg : Filter.Tendsto (fun y : ℝ => (y - ρ)⁻¹) Filter.atTop (nhds 0) :=
      (tendsto_inv_atTop_zero.comp (Filter.tendsto_atTop_add_const_right Filter.atTop (-ρ)
        Filter.tendsto_id)).congr fun y => by simp [sub_eq_add_neg]
    have h := tendsto_const_nhds (x := ρ).add (tendsto_const_nhds (x := ρ * (ρ - 1)).mul hg)
    rw [mul_zero, add_zero] at h
    refine h.congr' ((Filter.eventually_gt_atTop ρ).mono fun y hy => ?_)
    have : y - ρ ≠ 0 := by linarith
    rw [requiredStrength]
    field_simp
    ring
  · rw [← hE]; exact hanti hy hρE hyE
  · rw [← hE]; exact hanti hρE (hρE.trans hy) hy

end IndirectComparisonBias

end BiasAnalysis

end CausalInference
