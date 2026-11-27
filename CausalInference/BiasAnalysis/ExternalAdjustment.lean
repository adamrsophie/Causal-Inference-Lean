/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Sensitivity.BiasFormulas
public import CausalInference.Measures.EffectMeasures
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Sign.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# External adjustment for an unmeasured confounder

Closed-form bias analysis for a binary exposure `E`, a binary outcome `D` and an uncontrolled
binary (or polytomous) confounder `C`, following Chapter 5 of Fox, MacLehose and Lash (2021).

## Setting

The data-generating description is the stratum risk model of
`CausalInference.Sensitivity.BiasFormulas`: stratum risks `m e c = P(D = 1 | E = e, C = c)` and
confounder prevalences `π e = P(C = 1 | E = e)`. The crude risk ratio is `crudeRR m π`, and the
bias-adjusted risk ratio of the book is the SMR `smr m π`, the risk ratio standardized to the
confounder distribution of the exposed. Every positive result carries the positivity hypotheses
that its ratios need.

## Main results

* `crudeRR_div_smr`, `smr_eq`: the relative risk due to confounding (Equation 5.9) equals
  `(rr p₁ + 1 - p₁) / (rr p₀ + 1 - p₀)` with `rr` the confounder to disease risk ratio among the
  unexposed (Equation 5.8; effect measure modification allowed); `smr_eq_of_noModification` is
  Equations 5.1 and 5.10; `stratumRR_eq_smr`: without modification the strata are homogeneous.
  Only the unexposed (reference) risks need to be positive, so a zero exposed risk is covered.
* `smr_eq_polytomous`: the polytomous confounder formula.
* `rdAdj_eq`, `rdAdj_eq_exposed`: the difference-scale adjustment, as corollaries of the
  library's bias formulas.
* `projColumn`, `projTable`: all eight projected cells; `projColumn_nonneg_iff`: the projected
  table is valid (no negative cell) exactly when `max 1 rr * x ≤ t * mixFactor rr p` in each
  arm; `projColumn_recovers`, `splitCases_recovers`: Equation 5.5 returns the true stratified
  table when it has the stated risk (or odds) ratio; `projRisk_mem_Icc`: on the valid region
  the projected risks are probabilities; `smr_projRisk`: the SMR of the projected table equals
  the closed form; `splitCases_admissible_iff`, `splitCases_inadmissible`: negative cells.
* `stratumOR_projected`, `mhOddsRatio_projected`: the case-control (odds ratio) version, whose
  projected strata have a common odds ratio equal to the Mantel and Haenszel summary
  (Table 12.5); `mhOddsRatio_of_homogeneous_of_pos`: the summary of homogeneous nonempty
  strata.
* `flandersKhoury`, `smr_mem_flandersKhoury`: the bounding factors of Table 5.9 and the
  resulting interval for the adjusted risk ratio; `oddsRatio_div_mixFactor` identifies the
  fifth factor with `p₁ / p₀`; `biasFactor_range`: the range `[1, rr / mixFactor rr p₀)` when
  only `rr` and `p₀` are fixed; `boundingFactor_le_min`.
* `biasFactor_mono_left`, `biasFactor_anti_right`, `biasFactor_along_mono`: monotonicity in the
  prevalences; `biasFactor_one`, `biasFactor_le_boundingFactor`,
  `biasFactor_eq_boundingFactor_iff`: the Ding and VanderWeele bounding factor is the value at
  `p₁ = 1` and the maximum over `p₁`, attained only at `p₁ = 1` unless `rr = 1` or `K = 1`.
* `explainAway_iff`, `explainAway_one_iff`: Equations 5.11 and 5.12;
  `one_lt_explainAway_sol_iff`, `explainAway_sol_nonpos`, `exists_explainAway_iff`: the
  solution is an admissible risk ratio exactly when `RR_obs < RR_EC`.
* `eValue`: Equation 5.13, extended to protective estimates through `max RR (1 / RR)`;
  `eValue_of_one_le`, `eValue_inv`, `eValue_le_max`; `boundingFactor_eValue`,
  `biasFactor_eValue`: sharpness of the E-value; `gValue_root`, `biasFactor_gValue`,
  `gValue_one`, `eValue_le_gValue`, `eq_gValue_of_root`: the G-value is the only root at least
  one of its quadratic, explains away the observed risk ratio, equals the E-value at `p₁ = 1`
  and is at least the E-value.
* `sign_unadjustedBias`, `sign_unadjustedBias_of_same_sign`, `sign_unadjustedBias_exposed`,
  `sign_biasFactor_sub_one`, `smr_lt_crudeRR_iff`: the signed DAG rules of Table 5.10 on both
  scales, under sign agreement of the confounder to disease effects;
  `signed_rule_fails_with_interaction`: without sign agreement no pair of signs determines the
  bias for every standard.
* `Examples`: all cells of Tables 5.5 and 5.6, Tables 5.8 and 12.5, Equations 5.1 and 5.8, the
  polytomous and difference-scale examples, the Winkelstein example, the E-value `3.41` and
  the G-values `4.56` and `6.70`, each checked by `norm_num` with rounding intervals. Table 5.8,
  row 1, recomputes to `1.10` (printed `1.11`).

## References

* M. P. Fox, R. F. MacLehose, T. L. Lash, *Applying Quantitative Bias Analysis to
  Epidemiologic Data*, second edition, Springer (2021), Chapter 5 and Chapter 12 (Table 12.5).
* J. J. Schlesselman, *Assessing effects of confounding variables*, American Journal of
  Epidemiology (1978).
* W. D. Flanders and M. J. Khoury, *Indirect assessment of confounding: graphic description
  and limits on effect of adjusting for covariates*, Epidemiology (1990).
* P. Ding and T. J. VanderWeele, *Sensitivity analysis without assumptions*, Epidemiology
  (2016).
* T. J. VanderWeele and P. Ding, *Sensitivity analysis in observational research: introducing
  the E-value*, Annals of Internal Medicine (2017).
-/

@[expose] public section

namespace CausalInference

namespace BiasAnalysis

namespace ExternalAdjustment

open BiasFormulas

/-! ### The exact ratio factor -/

/-- The mixing factor `rr * p + (1 - p)`: the risk of a population with confounder prevalence
`p`, relative to the risk at `C = 0`, when the confounder multiplies the risk by `rr`. -/
def mixFactor (rr p : ℝ) : ℝ := rr * p + (1 - p)

/-- The exact bias factor of a binary confounder (the "relative risk due to confounding" of
Fox, MacLehose and Lash 2021, Equation 5.9, in the closed form of Equation 5.1):
`(rr * p₁ + 1 - p₁) / (rr * p₀ + 1 - p₀)`, with `rr` the confounder to disease risk ratio and
`p₁`, `p₀` the confounder prevalences among the exposed and the unexposed. -/
noncomputable def biasFactor (rr p₁ p₀ : ℝ) : ℝ := mixFactor rr p₁ / mixFactor rr p₀

/-- The mixing factor is positive for a positive risk ratio and a prevalence in `[0, 1]`. -/
theorem mixFactor_pos {rr p : ℝ} (hrr : 0 < rr) (hp : 0 ≤ p) (hp' : p ≤ 1) :
    0 < mixFactor rr p := by
  unfold mixFactor
  have := convex_comb_pos hp hp' hrr one_pos
  linarith

/-- The crude (observed) risk ratio `P(D = 1 | E = 1) / P(D = 1 | E = 0)` of the stratum risk
model `m e c = P(D = 1 | E = e, C = c)` with confounder prevalences `π e = P(C = 1 | E = e)`. -/
noncomputable def crudeRR (m : Bool → Bool → ℝ) (π : Bool → ℝ) : ℝ :=
  observedMean m π true / observedMean m π false

/-- The standardized morbidity ratio (SMR): the risk ratio standardized to the confounder
distribution of the exposed, `P(D = 1 | E = 1) / ∑ c, P(C = c | E = 1) P(D = 1 | E = 0, C = c)`.
When `C` suffices for confounding control this is the causal risk ratio in the exposed; it is
the bias-adjusted risk ratio `RR_adj` of Fox, MacLehose and Lash (2021), Chapter 5. -/
noncomputable def smr (m : Bool → Bool → ℝ) (π : Bool → ℝ) : ℝ :=
  observedMean m π true / standardizedMean m (π true) false

/-- The numerator of the SMR is the observed risk of the exposed. -/
theorem standardizedMean_exposed (m : Bool → Bool → ℝ) (π : Bool → ℝ) :
    standardizedMean m (π true) true = observedMean m π true := rfl

/-- The reference (unexposed) side of the stratum risk model: with positive unexposed stratum
risks and `m 0 1 = rr * m 0 0`, the ratio `rr` is positive, and the observed and the
standardized risks of the unexposed are `m 0 0` times the mixing factors at `π 0` and `π 1`.
-/
theorem unexposed_facts {m : Bool → Bool → ℝ} {π : Bool → ℝ} {rr : ℝ}
    (hm₀ : ∀ c, 0 < m false c) (hrr : m false true = rr * m false false) :
    0 < rr ∧ observedMean m π false = m false false * mixFactor rr (π false) ∧
      standardizedMean m (π true) false = m false false * mixFactor rr (π true) := by
  refine ⟨?_, ?_, ?_⟩
  · have := hm₀ true
    rw [hrr] at this
    exact pos_of_mul_pos_left this (hm₀ false).le
  · unfold observedMean mixFactor; rw [hrr]; ring
  · unfold standardizedMean mixFactor; rw [hrr]; ring

/-- **External adjustment under effect measure modification** (Fox, MacLehose and Lash 2021,
Equations 5.8 and 5.9). Let the unexposed stratum risks `m 0 c` be positive, `π e ∈ [0, 1]` the
confounder prevalences, and the observed risk of the exposed nonzero (the SMR is then nonzero,
so the quotient below is a real quotient). If the confounder to disease risk ratio among the
unexposed is `rr` (`m 0 1 = rr * m 0 0`), then the relative risk due to confounding, crude
risk ratio divided by SMR, equals `(rr * π 1 + 1 - π 1) / (rr * π 0 + 1 - π 0)`. The exposed
stratum risks, and so the confounder to disease risk ratio among the exposed, do not enter. -/
theorem crudeRR_div_smr {m : Bool → Bool → ℝ} {π : Bool → ℝ} {rr : ℝ}
    (hm₀ : ∀ c, 0 < m false c) (hO : observedMean m π true ≠ 0)
    (hπ₀ : 0 ≤ π false) (hπ₀' : π false ≤ 1) (hπ₁ : 0 ≤ π true) (hπ₁' : π true ≤ 1)
    (hrr : m false true = rr * m false false) :
    crudeRR m π / smr m π = biasFactor rr (π true) (π false) := by
  obtain ⟨hrr0, hO0, hS0⟩ := unexposed_facts (π := π) hm₀ hrr
  have h00 := hm₀ false
  have hg0 := mixFactor_pos hrr0 hπ₀ hπ₀'
  have hg1 := mixFactor_pos hrr0 hπ₁ hπ₁'
  unfold crudeRR smr biasFactor
  rw [hO0, hS0]
  field_simp

/-- **Equation 5.8** of Fox, MacLehose and Lash (2021) solved for the adjusted estimate:
`SMR = RR_crude * (rr * π 0 + 1 - π 0) / (rr * π 1 + 1 - π 1)`, with `rr` the confounder to
disease risk ratio among the unexposed. Only the unexposed stratum risks need to be positive
(the reference risks in both denominators); the exposed risks are arbitrary, so a zero exposed
risk, where both risk ratios are zero, is included. -/
theorem smr_eq {m : Bool → Bool → ℝ} {π : Bool → ℝ} {rr : ℝ} (hm₀ : ∀ c, 0 < m false c)
    (hπ₀ : 0 ≤ π false) (hπ₀' : π false ≤ 1) (hπ₁ : 0 ≤ π true) (hπ₁' : π true ≤ 1)
    (hrr : m false true = rr * m false false) :
    smr m π = crudeRR m π * (mixFactor rr (π false) / mixFactor rr (π true)) := by
  obtain ⟨hrr0, hO0, hS0⟩ := unexposed_facts (π := π) hm₀ hrr
  have h00 := hm₀ false
  have hg0 := mixFactor_pos hrr0 hπ₀ hπ₀'
  have hg1 := mixFactor_pos hrr0 hπ₁ hπ₁'
  unfold crudeRR smr
  rw [hO0, hS0]
  field_simp

/-- No effect measure modification of the confounder to disease risk ratio on the ratio scale:
`m e 1 = rr * m e 0` in both exposure groups. -/
def NoModification (m : Bool → Bool → ℝ) (rr : ℝ) : Prop :=
  ∀ e, m e true = rr * m e false

/-- **External adjustment formula** (Fox, MacLehose and Lash 2021, Equations 5.1 and 5.10;
Schlesselman 1978). With no modification of the confounder to disease risk ratio `rr` across
exposure groups, `RR_adj = RR_obs * (rr * p₀ + 1 - p₀) / (rr * p₁ + 1 - p₁)`, where `RR_adj` is
the SMR. Only the unexposed stratum risks need to be positive. -/
theorem smr_eq_of_noModification {m : Bool → Bool → ℝ} {π : Bool → ℝ} {rr : ℝ}
    (hm₀ : ∀ c, 0 < m false c) (hπ₀ : 0 ≤ π false) (hπ₀' : π false ≤ 1) (hπ₁ : 0 ≤ π true)
    (hπ₁' : π true ≤ 1) (hmod : NoModification m rr) :
    smr m π = crudeRR m π * (mixFactor rr (π false) / mixFactor rr (π true)) :=
  smr_eq hm₀ hπ₀ hπ₀' hπ₁ hπ₁' (hmod false)

/-- **Homogeneous strata.** With no modification of the confounder to disease risk ratio, the
exposure to disease risk ratios in the two confounder strata are equal and equal to the SMR;
standardizing to any confounder distribution gives the same value (Fox, MacLehose and Lash
2021, text after Equation 5.1 and Table 5.5). Only the unexposed stratum risks need to be
positive; the exposed risks may be zero. -/
theorem stratumRR_eq_smr {m : Bool → Bool → ℝ} {π : Bool → ℝ} {rr : ℝ}
    (hm₀ : ∀ c, 0 < m false c) (hπ₁ : 0 ≤ π true) (hπ₁' : π true ≤ 1)
    (hmod : NoModification m rr) :
    m true true / m false true = m true false / m false false ∧
      smr m π = m true false / m false false := by
  have h00 := hm₀ false
  have hrr0 : 0 < rr := (unexposed_facts (π := π) hm₀ (hmod false)).1
  refine ⟨?_, ?_⟩
  · rw [hmod true, hmod false]
    field_simp
  · unfold smr observedMean standardizedMean
    rw [hmod true, hmod false]
    have hg := mixFactor_pos hrr0 hπ₁ hπ₁'
    unfold mixFactor at hg
    rw [div_eq_div_iff (by nlinarith) h00.ne']
    ring

/-- The relative risk due to confounding (Fox, MacLehose and Lash 2021, Equation 5.9):
the crude risk ratio divided by the adjusted one. -/
noncomputable def rrConf (rrCrude rrAdj : ℝ) : ℝ := rrCrude / rrAdj

/-- Equation 5.9 inverted: `RR_adj = RR_crude / RR_conf`, for nonzero crude and adjusted risk
ratios. -/
theorem rrAdj_eq_div_rrConf {rrCrude rrAdj : ℝ} (hc : rrCrude ≠ 0) (ha : rrAdj ≠ 0) :
    rrAdj = rrCrude / rrConf rrCrude rrAdj := by
  unfold rrConf
  field_simp

/-! ### Polytomous confounder -/

/-- **Polytomous confounder** (Fox, MacLehose and Lash 2021, "Polytomous Confounders"). Let the
confounder take values in a finite type `V`, with distributions `π e v = P(C = v | E = e)` and
stratum risks `m e v`, of which the unexposed ones `m 0 v` are positive (the exposed risks are
arbitrary, so a zero exposed risk is included). If the risks of the unexposed are
`m 0 v = θ * rr v` (a baseline risk times category risk ratios `rr v`), then the SMR
standardized to the exposed equals `RR_crude * (∑ v, rr v π 0 v) / (∑ v, rr v π 1 v)`. Only
the risk ratios of the unexposed enter, so the formula allows effect measure modification by
the exposure. With a reference category `v₀` and `rr v₀ = 1` this is the book's display with
three religious categories. -/
theorem smr_eq_polytomous {V : Type*} [Fintype V] {m : Bool → V → ℝ} {π : Bool → V → ℝ}
    {rr : V → ℝ} {θ : ℝ} (hθ : 0 < θ) (hm₀ : ∀ v, 0 < m false v) (hπ : ∀ e v, 0 ≤ π e v)
    (hsum : ∀ e, ∑ v, π e v = 1) (hrr : ∀ v, m false v = θ * rr v) :
    (∑ v, π true v * m true v) / (∑ v, π true v * m false v) =
      ((∑ v, π true v * m true v) / (∑ v, π false v * m false v)) *
        ((∑ v, rr v * π false v) / (∑ v, rr v * π true v)) := by
  have hpos : ∀ e, 0 < ∑ v, π e v * m false v := by
    intro e
    obtain ⟨v, hv⟩ : ∃ v, 0 < π e v := by
      by_contra h
      simp only [not_exists, not_lt] at h
      have : ∑ v, π e v = 0 := Finset.sum_eq_zero fun v _ => le_antisymm (h v) (hπ e v)
      rw [hsum e] at this
      exact one_ne_zero this
    exact lt_of_lt_of_le (mul_pos hv (hm₀ v))
      (Finset.single_le_sum (fun w _ => mul_nonneg (hπ e w) (hm₀ w).le) (Finset.mem_univ v))
  have e1 : ∀ e, ∑ v, π e v * m false v = θ * ∑ v, rr v * π e v := by
    intro e
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by rw [hrr v]; ring
  have h1 := hpos true
  have h0 := hpos false
  rw [e1] at h1 h0
  rw [e1, e1]
  have a1 : 0 < ∑ v, rr v * π true v := pos_of_mul_pos_right h1 hθ.le
  have a0 : 0 < ∑ v, rr v * π false v := pos_of_mul_pos_right h0 hθ.le
  field_simp

/-! ### Difference scale -/

/-- **Difference-scale adjustment** (Fox, MacLehose and Lash 2021, "Difference Measures").
With the confounder to disease risk difference equal to `γ` in both exposure groups, the risk
difference standardized to any confounder distribution `r` is
`RD_adj = RD_obs - γ * (p₁ - p₀)`. A corollary of `unadjustedBias_eq_of_no_interaction`. -/
theorem rdAdj_eq {m : Bool → Bool → ℝ} {γ : ℝ} (h₁ : m true true - m true false = γ)
    (h₀ : m false true - m false false = γ) (π : Bool → ℝ) (r : ℝ) :
    standardizedEffect m r =
      (observedMean m π true - observedMean m π false) - γ * (π true - π false) := by
  have := unadjustedBias_eq_of_no_interaction h₁ h₀ π r
  unfold unadjustedBias at this
  linarith

/-- Difference-scale adjustment under effect measure modification, standardized to the
exposed: only the confounder to disease risk difference `γ₀` among the unexposed enters,
`RD_adj = RD_obs - γ₀ * (p₁ - p₀)`. A corollary of `unadjustedBias_eq`. -/
theorem rdAdj_eq_exposed {m : Bool → Bool → ℝ} {γ₀ : ℝ} (h₀ : m false true - m false false = γ₀)
    (π : Bool → ℝ) :
    standardizedEffect m (π true) =
      (observedMean m π true - observedMean m π false) - γ₀ * (π true - π false) := by
  have := unadjustedBias_eq m π (π true)
  unfold unadjustedBias at this
  rw [h₀] at this
  linarith

/-! ### Projection of the stratified table -/

/-- The projected count of cases in the stratum `C = 1` (Fox, MacLehose and Lash 2021,
Equations 5.2 to 5.5): a column with `x` cases and total `t`, of which `t₁` are in the stratum
`C = 1`, is split so that the stratum specific risks have ratio `rr`:
`x₁ = rr * t₁ * x / (rr * t₁ + t - t₁)`. In the case-control version `t` is the number of
controls and `rr` an odds ratio. -/
noncomputable def splitCases (rr t₁ t x : ℝ) : ℝ := rr * t₁ * x / (rr * t₁ + t - t₁)

/-- **The projection recovers the true table.** If a column with stratum totals `t₁, t₀ > 0`
has stratum case counts `x₁, x₀` whose stratum risks (or odds) have ratio `rr ≥ 0`, that is
`x₁ / t₁ = rr * (x₀ / t₀)` written without division, then Equation 5.5 applied to the collapsed
column returns `x₁`. -/
theorem splitCases_recovers {rr t₁ t₀ x₁ x₀ : ℝ} (hrr : 0 ≤ rr) (ht₁ : 0 < t₁) (ht₀ : 0 < t₀)
    (h : x₁ * t₀ = rr * t₁ * x₀) : splitCases rr t₁ (t₁ + t₀) (x₁ + x₀) = x₁ := by
  unfold splitCases
  have hD : 0 < rr * t₁ + (t₁ + t₀) - t₁ := by nlinarith
  rw [div_eq_iff hD.ne']
  linear_combination (-1 : ℝ) * h

/-- The projected stratum `C = 1` risk: `x₁ / t₁ = rr * x / (t * mixFactor rr p)` when
`t₁ = t * p`. -/
theorem splitCases_div {rr t p x : ℝ} (ht : 0 < t) (hp : 0 < p) (hD : 0 < mixFactor rr p) :
    splitCases rr (t * p) t x / (t * p) = rr * x / (t * mixFactor rr p) := by
  unfold splitCases mixFactor at *
  have e : rr * (t * p) + t - t * p = t * (rr * p + (1 - p)) := by ring
  rw [e]
  field_simp

/-- The projected stratum `C = 0` risk: `(x - x₁) / (t - t₁) = x / (t * mixFactor rr p)` when
`t₁ = t * p` with `p < 1`. -/
theorem sub_splitCases_div {rr t p x : ℝ} (ht : 0 < t) (hp : p < 1) (hD : 0 < mixFactor rr p) :
    (x - splitCases rr (t * p) t x) / (t - t * p) = x / (t * mixFactor rr p) := by
  unfold splitCases mixFactor at *
  have e : rr * (t * p) + t - t * p = t * (rr * p + (1 - p)) := by ring
  have h1 : t - t * p = t * (1 - p) := by ring
  have h1p : 0 < 1 - p := by linarith
  rw [e, h1]
  field_simp
  ring

/-- **Admissibility of the projection.** The projected noncase count of the stratum `C = 1`
is nonnegative (`x₁ ≤ t₁`) exactly when `rr * x ≤ t * mixFactor rr p`, and that of the stratum
`C = 0` (`x - x₁ ≤ t - t₁`) exactly when `x ≤ t * mixFactor rr p`. Outside this region the
projected table has a negative cell and a stratum "risk" above one; see
`splitCases_inadmissible`. -/
theorem splitCases_admissible_iff {rr t p x : ℝ} (ht : 0 < t) (hp : 0 < p) (hp' : p < 1)
    (hD : 0 < mixFactor rr p) :
    (splitCases rr (t * p) t x ≤ t * p ↔ rr * x ≤ t * mixFactor rr p) ∧
      (x - splitCases rr (t * p) t x ≤ t - t * p ↔ x ≤ t * mixFactor rr p) := by
  have htp : 0 < t * p := mul_pos ht hp
  have htq : 0 < t - t * p := by nlinarith
  have htg : 0 < t * mixFactor rr p := mul_pos ht hD
  constructor
  · rw [← div_le_one htp, splitCases_div ht hp hD, div_le_one htg]
  · rw [← div_le_one htq, sub_splitCases_div ht hp' hD, div_le_one htg]

/-- The projection can produce a negative cell: with `9` exposed cases among `10` exposed,
confounder prevalence `1/2` among the exposed and `rr = 3`, the projected stratum `C = 1` has
`6.75` cases among `5` persons, so its noncase count is `-1.75`. -/
theorem splitCases_inadmissible :
    splitCases 3 (10 * (1 / 2)) 10 9 = 27 / 4 ∧
      10 * (1 / 2) - splitCases 3 (10 * (1 / 2)) 10 9 < 0 := by
  unfold splitCases
  norm_num

/-- The four projected cells of one exposure arm (one column of Table 5.1 of Fox, MacLehose and
Lash 2021, split by the confounder), indexed by the confounder `c` and then the disease `d`. The
arm has `t` persons and `x` cases; the stratum `C = 1` has `t * p` persons (Equation 5.4) and
`splitCases rr (t * p) t x` cases (Equation 5.5); the other cells follow by differences, as in
the book. -/
noncomputable def projColumn (rr t p x : ℝ) : Bool → Bool → ℝ
  | true, true => splitCases rr (t * p) t x
  | false, true => x - splitCases rr (t * p) t x
  | true, false => t * p - splitCases rr (t * p) t x
  | false, false => (t - t * p) - (x - splitCases rr (t * p) t x)

/-- The projected stratified table with all eight cells (Tables 5.5 and 5.6 of Fox, MacLehose
and Lash 2021), indexed by the confounder `c`, the disease `d` and the exposure `e`: the exposed
arm has `nE` persons, `a` cases, confounder prevalence `p true` and confounder to disease risk
ratio `rr₁`; the unexposed arm has `nU`, `b`, `p false` and `rr₀`. -/
noncomputable def projTable (a b nE nU rr₁ rr₀ : ℝ) (p : Bool → ℝ) : Bool → Bool → Bool → ℝ :=
  fun c d e => if e then projColumn rr₁ nE (p true) a c d else projColumn rr₀ nU (p false) b c d

/-- Closed form of the four projected cells of an arm, with `M = mixFactor rr p`:
cases `rr p x / M` and `(1 - p) x / M`, noncases `p (t M - rr x) / M` and
`(1 - p) (t M - x) / M` in the strata `C = 1` and `C = 0`. -/
theorem projColumn_eq {rr t p x : ℝ} (ht : t ≠ 0) (hM : mixFactor rr p ≠ 0) :
    projColumn rr t p x true true = rr * p * x / mixFactor rr p ∧
      projColumn rr t p x false true = (1 - p) * x / mixFactor rr p ∧
      projColumn rr t p x true false = p * (t * mixFactor rr p - rr * x) / mixFactor rr p ∧
      projColumn rr t p x false false =
        (1 - p) * (t * mixFactor rr p - x) / mixFactor rr p := by
  have hs : splitCases rr (t * p) t x = rr * p * x / mixFactor rr p := by
    unfold splitCases
    rw [show rr * (t * p) + t - t * p = t * mixFactor rr p by unfold mixFactor; ring]
    field_simp
  simp only [projColumn, hs, true_and]
  refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> unfold mixFactor <;> ring

/-- **Validity of the projected table.** For an arm with `t > 0` persons, `x ≥ 0` cases, a
confounder prevalence `0 < p < 1` and a confounder to disease risk ratio `rr ≥ 0`, all four
projected cells are nonnegative exactly when `max 1 rr * x ≤ t * mixFactor rr p`. The case
cells are always nonnegative; the noncase cells of the strata `C = 1` and `C = 0` are
nonnegative exactly when `rr x ≤ t M` and `x ≤ t M` (`splitCases_admissible_iff`). -/
theorem projColumn_nonneg_iff {rr t p x : ℝ} (ht : 0 < t) (hp : 0 < p) (hp' : p < 1)
    (hrr : 0 ≤ rr) (hx : 0 ≤ x) :
    (∀ c d, 0 ≤ projColumn rr t p x c d) ↔ max 1 rr * x ≤ t * mixFactor rr p := by
  have hM : 0 < mixFactor rr p := by
    unfold mixFactor; nlinarith [mul_nonneg hrr hp.le]
  have hq : 0 < 1 - p := by linarith
  obtain ⟨h11, h01, h10, h00⟩ := projColumn_eq (rr := rr) (x := x) ht.ne' hM.ne'
  rw [max_mul_of_nonneg _ _ hx, one_mul, max_le_iff]
  constructor
  · intro h
    have a := h true false
    have b := h false false
    rw [h10, mul_div_assoc, mul_nonneg_iff_of_pos_left hp, le_div_iff₀ hM, zero_mul] at a
    rw [h00, mul_div_assoc, mul_nonneg_iff_of_pos_left hq, le_div_iff₀ hM, zero_mul] at b
    constructor <;> linarith
  · rintro ⟨h1, h2⟩ c d
    cases c <;> cases d
    · rw [h00]; exact div_nonneg (mul_nonneg hq.le (by linarith)) hM.le
    · rw [h01]; positivity
    · rw [h10]; exact div_nonneg (mul_nonneg hp.le (by linarith)) hM.le
    · rw [h11]; positivity

/-- **Validity of the eight cell table**: with positive arm sizes, prevalences in `(0, 1)`,
nonnegative case counts and nonnegative confounder to disease risk ratios, all eight projected
cells of `projTable` are nonnegative exactly when both arms satisfy the criterion of
`projColumn_nonneg_iff`. -/
theorem projTable_nonneg_iff {a b nE nU rr₁ rr₀ : ℝ} {p : Bool → ℝ} (hnE : 0 < nE)
    (hnU : 0 < nU) (hp : ∀ e, 0 < p e ∧ p e < 1) (hrr₁ : 0 ≤ rr₁) (hrr₀ : 0 ≤ rr₀)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∀ c d e, 0 ≤ projTable a b nE nU rr₁ rr₀ p c d e) ↔
      max 1 rr₁ * a ≤ nE * mixFactor rr₁ (p true) ∧
        max 1 rr₀ * b ≤ nU * mixFactor rr₀ (p false) := by
  rw [← projColumn_nonneg_iff hnE (hp true).1 (hp true).2 hrr₁ ha,
    ← projColumn_nonneg_iff hnU (hp false).1 (hp false).2 hrr₀ hb]
  constructor
  · intro h
    exact ⟨fun c d => by simpa [projTable] using h c d true,
      fun c d => by simpa [projTable] using h c d false⟩
  · rintro ⟨h1, h0⟩ c d e
    cases e
    · simpa [projTable] using h0 c d
    · simpa [projTable] using h1 c d

/-- **The projected table recovers a true table.** If a true arm has strata of `t₁, t₀ > 0`
persons with `x₁, x₀` cases whose stratum risks have ratio `rr ≥ 0` (written
`x₁ * t₀ = rr * t₁ * x₀`), then projecting the collapsed arm (`t₁ + t₀` persons,
`x₁ + x₀` cases, prevalence `t₁ / (t₁ + t₀)`) returns all four true cells. -/
theorem projColumn_recovers {rr t₁ t₀ x₁ x₀ : ℝ} (hrr : 0 ≤ rr) (ht₁ : 0 < t₁) (ht₀ : 0 < t₀)
    (h : x₁ * t₀ = rr * t₁ * x₀) :
    projColumn rr (t₁ + t₀) (t₁ / (t₁ + t₀)) (x₁ + x₀) =
      fun c d => if c then (if d then x₁ else t₁ - x₁) else (if d then x₀ else t₀ - x₀) := by
  have htp : (t₁ + t₀) * (t₁ / (t₁ + t₀)) = t₁ := by
    have : t₁ + t₀ ≠ 0 := by linarith
    field_simp
  have hs := splitCases_recovers hrr ht₁ ht₀ h
  funext c d
  cases c <;> cases d <;> simp only [projColumn, htp, hs, Bool.false_eq_true, ite_true,
    ite_false] <;> ring

/-- The projected stratum risks of Fox, MacLehose and Lash (2021), Table 5.1 and
Equations 5.4 to 5.6. From the observed exposed cases `a` among `nE` exposed and unexposed cases
`b` among `nU` unexposed, the confounder prevalences `p e`, and the confounder to disease risk
ratios `rr₁` (exposed) and `rr₀` (unexposed), the stratum `(e, c)` risk is the projected case
count over the projected total. -/
noncomputable def projRisk (a b nE nU rr₁ rr₀ : ℝ) (p : Bool → ℝ) : Bool → Bool → ℝ
  | true, true => splitCases rr₁ (nE * p true) nE a / (nE * p true)
  | true, false => (a - splitCases rr₁ (nE * p true) nE a) / (nE - nE * p true)
  | false, true => splitCases rr₀ (nU * p false) nU b / (nU * p false)
  | false, false => (b - splitCases rr₀ (nU * p false) nU b) / (nU - nU * p false)

section Projection

variable {a b nE nU rr₁ rr₀ : ℝ} {p : Bool → ℝ}

/-- Closed form of the projected risks. -/
theorem projRisk_eq (hnE : 0 < nE) (hnU : 0 < nU) (hrr₁ : 0 < rr₁) (hrr₀ : 0 < rr₀)
    (hp : ∀ e, 0 < p e ∧ p e < 1) :
    projRisk a b nE nU rr₁ rr₀ p true true = rr₁ * a / (nE * mixFactor rr₁ (p true)) ∧
      projRisk a b nE nU rr₁ rr₀ p true false = a / (nE * mixFactor rr₁ (p true)) ∧
      projRisk a b nE nU rr₁ rr₀ p false true = rr₀ * b / (nU * mixFactor rr₀ (p false)) ∧
      projRisk a b nE nU rr₁ rr₀ p false false = b / (nU * mixFactor rr₀ (p false)) := by
  have g1 := mixFactor_pos hrr₁ (hp true).1.le (hp true).2.le
  have g0 := mixFactor_pos hrr₀ (hp false).1.le (hp false).2.le
  exact ⟨splitCases_div hnE (hp true).1 g1, sub_splitCases_div hnE (hp true).2 g1,
    splitCases_div hnU (hp false).1 g0, sub_splitCases_div hnU (hp false).2 g0⟩

/-- The projected table has the assumed confounder to disease risk ratios: `rr₁` among the
exposed and `rr₀` among the unexposed. -/
theorem projRisk_ratio (hnE : 0 < nE) (hnU : 0 < nU) (hrr₁ : 0 < rr₁) (hrr₀ : 0 < rr₀)
    (hp : ∀ e, 0 < p e ∧ p e < 1) :
    projRisk a b nE nU rr₁ rr₀ p true true = rr₁ * projRisk a b nE nU rr₁ rr₀ p true false ∧
      projRisk a b nE nU rr₁ rr₀ p false true =
        rr₀ * projRisk a b nE nU rr₁ rr₀ p false false := by
  obtain ⟨h1, h2, h3, h4⟩ := projRisk_eq (a := a) (b := b) hnE hnU hrr₁ hrr₀ hp
  rw [h1, h2, h3, h4]
  constructor <;> ring

/-- The projected table reproduces the observed crude risks `a / nE` and `b / nU`. -/
theorem observedMean_projRisk (hnE : 0 < nE) (hnU : 0 < nU) (hrr₁ : 0 < rr₁) (hrr₀ : 0 < rr₀)
    (hp : ∀ e, 0 < p e ∧ p e < 1) :
    observedMean (projRisk a b nE nU rr₁ rr₀ p) p true = a / nE ∧
      observedMean (projRisk a b nE nU rr₁ rr₀ p) p false = b / nU := by
  obtain ⟨h1, h2, h3, h4⟩ := projRisk_eq (a := a) (b := b) hnE hnU hrr₁ hrr₀ hp
  have g1 := mixFactor_pos hrr₁ (hp true).1.le (hp true).2.le
  have g0 := mixFactor_pos hrr₀ (hp false).1.le (hp false).2.le
  unfold observedMean
  rw [h1, h2, h3, h4]
  have key : ∀ r q x n : ℝ, 0 < n → 0 < mixFactor r q →
      q * (r * x / (n * mixFactor r q)) + (1 - q) * (x / (n * mixFactor r q)) = x / n := by
    intro r q x n hn hg
    have e : q * (r * x / (n * mixFactor r q)) + (1 - q) * (x / (n * mixFactor r q)) =
        x * mixFactor r q / (n * mixFactor r q) := by
      unfold mixFactor; ring
    rw [e, mul_div_mul_right _ _ hg.ne']
  exact ⟨key _ _ _ _ hnE g1, key _ _ _ _ hnU g0⟩

/-- The projected risks are positive when the observed cases are. -/
theorem projRisk_pos (ha : 0 < a) (hb : 0 < b) (hnE : 0 < nE) (hnU : 0 < nU) (hrr₁ : 0 < rr₁)
    (hrr₀ : 0 < rr₀) (hp : ∀ e, 0 < p e ∧ p e < 1) :
    ∀ e c, 0 < projRisk a b nE nU rr₁ rr₀ p e c := by
  obtain ⟨h1, h2, h3, h4⟩ := projRisk_eq (a := a) (b := b) hnE hnU hrr₁ hrr₀ hp
  have g1 := mixFactor_pos hrr₁ (hp true).1.le (hp true).2.le
  have g0 := mixFactor_pos hrr₀ (hp false).1.le (hp false).2.le
  intro e c
  cases e <;> cases c
  · rw [h4]; positivity
  · rw [h3]; positivity
  · rw [h2]; positivity
  · rw [h1]; positivity

/-- The projected risks of the unexposed are positive when the unexposed cases are; no sign
condition on the exposed cases is needed. -/
theorem projRisk_pos_unexposed (hb : 0 < b) (hnE : 0 < nE) (hnU : 0 < nU) (hrr₁ : 0 < rr₁)
    (hrr₀ : 0 < rr₀) (hp : ∀ e, 0 < p e ∧ p e < 1) :
    ∀ c, 0 < projRisk a b nE nU rr₁ rr₀ p false c := by
  obtain ⟨-, -, h3, h4⟩ := projRisk_eq (a := a) (b := b) hnE hnU hrr₁ hrr₀ hp
  have g0 := mixFactor_pos hrr₀ (hp false).1.le (hp false).2.le
  intro c
  cases c
  · rw [h4]; positivity
  · rw [h3]; positivity

/-- **The SMR of the projected table equals the closed form** (Fox, MacLehose and Lash 2021,
Table 5.5 and Equation 5.7 against Equations 5.1 and 5.8): the SMR computed from the projected
stratified table is `(a / nE) / (b / nU) * (rr₀ p₀ + 1 - p₀) / (rr₀ p₁ + 1 - p₁)`. Only the
unexposed cases need to be positive: the exposed case count `a` is arbitrary, so `a = 0` (both
risk ratios zero) is included. -/
theorem smr_projRisk (hb : 0 < b) (hnE : 0 < nE) (hnU : 0 < nU) (hrr₁ : 0 < rr₁)
    (hrr₀ : 0 < rr₀) (hp : ∀ e, 0 < p e ∧ p e < 1) :
    smr (projRisk a b nE nU rr₁ rr₀ p) p =
      (a / nE) / (b / nU) * (mixFactor rr₀ (p false) / mixFactor rr₀ (p true)) := by
  rw [smr_eq (projRisk_pos_unexposed hb hnE hnU hrr₁ hrr₀ hp) (hp false).1.le (hp false).2.le
    (hp true).1.le (hp true).2.le (projRisk_ratio hnE hnU hrr₁ hrr₀ hp).2]
  unfold crudeRR
  obtain ⟨o1, o0⟩ := observedMean_projRisk (a := a) (b := b) hnE hnU hrr₁ hrr₀ hp
  rw [o1, o0]

/-- With a common confounder to disease risk ratio (`rr₁ = rr₀ = rr`), the projected strata
have equal exposure to disease risk ratios, both equal to the SMR (Table 5.5). The exposed case
count `a` is arbitrary. -/
theorem projRisk_homogeneous {rr : ℝ} (hb : 0 < b) (hnE : 0 < nE) (hnU : 0 < nU)
    (hrr : 0 < rr) (hp : ∀ e, 0 < p e ∧ p e < 1) :
    projRisk a b nE nU rr rr p true true / projRisk a b nE nU rr rr p false true =
        projRisk a b nE nU rr rr p true false / projRisk a b nE nU rr rr p false false ∧
      smr (projRisk a b nE nU rr rr p) p =
        projRisk a b nE nU rr rr p true false / projRisk a b nE nU rr rr p false false := by
  have hr := projRisk_ratio (a := a) (b := b) hnE hnU hrr hrr hp
  exact stratumRR_eq_smr (projRisk_pos_unexposed hb hnE hnU hrr hrr hp) (hp true).1.le
    (hp true).2.le (fun e => by cases e; exacts [hr.2, hr.1])

/-- **Projected risks are probabilities on the admissible region.** For nonnegative case
counts and positive confounder to disease risk ratios, if each exposure arm satisfies the
admissibility criterion `max 1 rr * x ≤ t * mixFactor rr p` of `projColumn_nonneg_iff`, then
every projected stratum risk lies in `[0, 1]`. For an inadmissible arm see
`splitCases_inadmissible` (`6.75` cases among `5` persons, a projected risk of `1.35`). -/
theorem projRisk_mem_Icc (ha : 0 ≤ a) (hb : 0 ≤ b) (hnE : 0 < nE) (hnU : 0 < nU)
    (hrr₁ : 0 < rr₁) (hrr₀ : 0 < rr₀) (hp : ∀ e, 0 < p e ∧ p e < 1)
    (hvE : max 1 rr₁ * a ≤ nE * mixFactor rr₁ (p true))
    (hvU : max 1 rr₀ * b ≤ nU * mixFactor rr₀ (p false)) :
    ∀ e c, projRisk a b nE nU rr₁ rr₀ p e c ∈ Set.Icc 0 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := projRisk_eq (a := a) (b := b) hnE hnU hrr₁ hrr₀ hp
  have g1 := mul_pos hnE (mixFactor_pos hrr₁ (hp true).1.le (hp true).2.le)
  have g0 := mul_pos hnU (mixFactor_pos hrr₀ (hp false).1.le (hp false).2.le)
  have k1 : rr₁ * a ≤ max 1 rr₁ * a := mul_le_mul_of_nonneg_right (le_max_right _ _) ha
  have k2 : a ≤ max 1 rr₁ * a := le_mul_of_one_le_left ha (le_max_left _ _)
  have k3 : rr₀ * b ≤ max 1 rr₀ * b := mul_le_mul_of_nonneg_right (le_max_right _ _) hb
  have k4 : b ≤ max 1 rr₀ * b := le_mul_of_one_le_left hb (le_max_left _ _)
  intro e c
  cases e <;> cases c
  · rw [h4]; exact ⟨by positivity, (div_le_one g0).2 (k4.trans hvU)⟩
  · rw [h3]; exact ⟨by positivity, (div_le_one g0).2 (k3.trans hvU)⟩
  · rw [h2]; exact ⟨by positivity, (div_le_one g1).2 (k2.trans hvE)⟩
  · rw [h1]; exact ⟨by positivity, (div_le_one g1).2 (k1.trans hvE)⟩

end Projection

/-! ### Case-control data: the odds ratio version -/

/-- **Odds ratio version of the projection** (Fox, MacLehose and Lash 2021, "Ratio Measures",
case-control text). From case counts `a` (exposed), `b` (unexposed) and control counts `c`
(exposed), `d` (unexposed), the controls are split by the confounder prevalences `p₁`, `p₀`
among exposed and unexposed controls, and the cases by Equation 5.5 with the confounder to
disease odds ratio `ψ`. Both projected stratum odds ratios then equal
`OR_obs * (ψ p₀ + 1 - p₀) / (ψ p₁ + 1 - p₁)`, the book's closed form `OR_adj`. In particular
the projected strata are homogeneous (Chapter 12, Table 12.5). By `splitCases_recovers`, the
projected cells are the true ones whenever the true table has the stated control prevalences
and confounder to disease odds ratio `ψ` within each exposure group. -/
theorem stratumOR_projected {a b c d ψ p₁ p₀ : ℝ} (hc : 0 < c) (hd : 0 < d) (ha : 0 < a)
    (hb : 0 < b) (hψ : 0 < ψ) (hp₁ : 0 < p₁) (hp₁' : p₁ < 1) (hp₀ : 0 < p₀) (hp₀' : p₀ < 1) :
    (splitCases ψ (c * p₁) c a / (c * p₁)) / (splitCases ψ (d * p₀) d b / (d * p₀)) =
        (a / c) / (b / d) * (mixFactor ψ p₀ / mixFactor ψ p₁) ∧
      ((a - splitCases ψ (c * p₁) c a) / (c - c * p₁)) /
          ((b - splitCases ψ (d * p₀) d b) / (d - d * p₀)) =
        (a / c) / (b / d) * (mixFactor ψ p₀ / mixFactor ψ p₁) := by
  have g1 := mixFactor_pos hψ hp₁.le hp₁'.le
  have g0 := mixFactor_pos hψ hp₀.le hp₀'.le
  rw [splitCases_div hc hp₁ g1, splitCases_div hd hp₀ g0, sub_splitCases_div hc hp₁' g1,
    sub_splitCases_div hd hp₀' g0]
  constructor <;> field_simp

/-- The Mantel and Haenszel summary odds ratio
`(∑ k, A k D k / T k) / (∑ k, B k C k / T k)` over finitely many strata, with stratum cells
`A` (exposed cases), `B` (unexposed cases), `C` (exposed controls), `D` (unexposed controls) and
stratum totals `T k = A k + B k + C k + D k`. -/
noncomputable def mhOddsRatio {K : Type*} [Fintype K] (A B C D : K → ℝ) : ℝ :=
  (∑ k, A k * D k / (A k + B k + C k + D k)) / (∑ k, B k * C k / (A k + B k + C k + D k))

/-- With a common stratum odds ratio `ψ` (written `A k D k = ψ B k C k`), the Mantel and
Haenszel summary odds ratio equals `ψ`, provided its outer denominator is positive. This is an
identity between totalized expressions: a stratum with total `A k + B k + C k + D k = 0`
contributes `0 / 0 = 0` to both sums. `mhOddsRatio_of_homogeneous_of_pos` is the version in
which every stratum is nonempty. -/
theorem mhOddsRatio_of_homogeneous {K : Type*} [Fintype K] {A B C D : K → ℝ} {ψ : ℝ}
    (h : ∀ k, A k * D k = ψ * (B k * C k))
    (hpos : 0 < ∑ k, B k * C k / (A k + B k + C k + D k)) :
    mhOddsRatio A B C D = ψ := by
  unfold mhOddsRatio
  have e : ∑ k, A k * D k / (A k + B k + C k + D k) =
      ψ * ∑ k, B k * C k / (A k + B k + C k + D k) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [h k]; ring
  rw [e, mul_div_assoc, div_self hpos.ne', mul_one]

/-- **The Mantel and Haenszel summary of homogeneous strata.** Let every stratum be nonempty
(positive total `A k + B k + C k + D k`), the unexposed cases `B` and exposed controls `C`
nonnegative, and some stratum have `B k C k > 0` (so the summary is a real quotient). If all
strata have the common odds ratio `ψ` (written `A k D k = ψ B k C k`), the Mantel and Haenszel
summary odds ratio equals `ψ`. -/
theorem mhOddsRatio_of_homogeneous_of_pos {K : Type*} [Fintype K] {A B C D : K → ℝ} {ψ : ℝ}
    (hB : ∀ k, 0 ≤ B k) (hC : ∀ k, 0 ≤ C k) (hT : ∀ k, 0 < A k + B k + C k + D k)
    (hBC : ∃ k, 0 < B k * C k) (h : ∀ k, A k * D k = ψ * (B k * C k)) :
    mhOddsRatio A B C D = ψ := by
  refine mhOddsRatio_of_homogeneous h (Finset.sum_pos' (fun k _ => ?_) ?_)
  · exact div_nonneg (mul_nonneg (hB k) (hC k)) (hT k).le
  · obtain ⟨k, hk⟩ := hBC
    exact ⟨k, Finset.mem_univ k, div_pos hk (hT k)⟩

/-- **The projected strata are homogeneous, so the Mantel and Haenszel summary equals the
closed form** (Fox, MacLehose and Lash 2021, Table 12.5: equal stratum odds ratios and an equal
summary odds ratio). For the case-control projection of `stratumOR_projected`, the Mantel and
Haenszel odds ratio over the two projected strata is `OR_obs * (ψ p₀ + 1 - p₀) / (ψ p₁ + 1 - p₁)`.
-/
theorem mhOddsRatio_projected {a b c d ψ p₁ p₀ : ℝ} (hc : 0 < c) (hd : 0 < d) (ha : 0 < a)
    (hb : 0 < b) (hψ : 0 < ψ) (hp₁ : 0 < p₁) (hp₁' : p₁ < 1) (hp₀ : 0 < p₀) (hp₀' : p₀ < 1) :
    mhOddsRatio
        (fun k : Bool => if k then splitCases ψ (c * p₁) c a else a - splitCases ψ (c * p₁) c a)
        (fun k : Bool => if k then splitCases ψ (d * p₀) d b else b - splitCases ψ (d * p₀) d b)
        (fun k : Bool => if k then c * p₁ else c - c * p₁)
        (fun k : Bool => if k then d * p₀ else d - d * p₀) =
      (a / c) / (b / d) * (mixFactor ψ p₀ / mixFactor ψ p₁) := by
  have g1 := mixFactor_pos hψ hp₁.le hp₁'.le
  have g0 := mixFactor_pos hψ hp₀.le hp₀'.le
  have hc1 : 0 < c * p₁ := mul_pos hc hp₁
  have hd1 : 0 < d * p₀ := mul_pos hd hp₀
  have hc0 : 0 < c - c * p₁ := by nlinarith
  have hd0 : 0 < d - d * p₀ := by nlinarith
  have hA1 : splitCases ψ (c * p₁) c a = c * p₁ * (ψ * a / (c * mixFactor ψ p₁)) := by
    rw [← splitCases_div hc hp₁ g1]; field_simp
  have hA0 : a - splitCases ψ (c * p₁) c a = (c - c * p₁) * (a / (c * mixFactor ψ p₁)) := by
    rw [← sub_splitCases_div hc hp₁' g1]; field_simp
  have hB1 : splitCases ψ (d * p₀) d b = d * p₀ * (ψ * b / (d * mixFactor ψ p₀)) := by
    rw [← splitCases_div hd hp₀ g0]; field_simp
  have hB0 : b - splitCases ψ (d * p₀) d b = (d - d * p₀) * (b / (d * mixFactor ψ p₀)) := by
    rw [← sub_splitCases_div hd hp₀' g0]; field_simp
  apply mhOddsRatio_of_homogeneous
  · intro k
    cases k
    · simp only [Bool.false_eq_true, ite_false]
      rw [hA0, hB0]
      field_simp
    · simp only [ite_true]
      rw [hA1, hB1]
      field_simp
  · simp only [Fintype.sum_bool, Bool.false_eq_true, ite_true, ite_false]
    rw [hA0, hB0, hA1, hB1]
    positivity

/-! ### Bounds: Flanders and Khoury -/

/-- The relative risk due to confounding of `crudeRR_div_smr` written as a difference:
`mixFactor rr p₁ - mixFactor rr p₀ = (rr - 1) (p₁ - p₀)`. -/
theorem mixFactor_sub (rr p₁ p₀ : ℝ) :
    mixFactor rr p₁ - mixFactor rr p₀ = (rr - 1) * (p₁ - p₀) := by
  unfold mixFactor; ring

/-- The confounder to exposure odds ratio is at least one exactly when the confounder is at
least as prevalent among the exposed, for prevalences in `(0, 1)`. -/
theorem one_le_oddsRatio_iff {p₁ p₀ : ℝ} (hp₁' : p₁ < 1) (hp₀ : 0 < p₀) (hp₀' : p₀ < 1) :
    1 ≤ EffectMeasure.oddsRatio p₁ p₀ ↔ p₀ ≤ p₁ := by
  unfold EffectMeasure.oddsRatio EffectMeasure.odds
  have h1 : 0 < 1 - p₁ := by linarith
  have h0 : 0 < 1 - p₀ := by linarith
  rw [le_div_iff₀ (div_pos hp₀ h0), one_mul, div_le_div_iff₀ h0 h1]
  constructor <;> intro h <;> nlinarith

/-- The fifth Flanders and Khoury factor is the prevalence ratio:
`OR_CE / ((1 - p₀) + p₀ OR_CE) = p₁ / p₀` with `OR_CE` the confounder to exposure odds ratio. -/
theorem oddsRatio_div_mixFactor {p₁ p₀ : ℝ} (hp₁' : p₁ < 1) (hp₀ : 0 < p₀) (hp₀' : p₀ < 1) :
    EffectMeasure.oddsRatio p₁ p₀ / mixFactor (EffectMeasure.oddsRatio p₁ p₀) p₀ = p₁ / p₀ := by
  unfold EffectMeasure.oddsRatio EffectMeasure.odds mixFactor
  have h1 : (1 - p₁) ≠ 0 := by linarith
  have h0 : (1 - p₀) ≠ 0 := by linarith
  have e : p₁ / (1 - p₁) / (p₀ / (1 - p₀)) * p₀ + (1 - p₀) = (1 - p₀) / (1 - p₁) := by
    field_simp; ring
  rw [e]
  field_simp

/-- **Flanders and Khoury bounds** (Fox, MacLehose and Lash 2021, Table 5.9; Flanders and
Khoury 1990). With `rr ≥ 1`, confounder to exposure odds ratio `OR_CE ≥ 1` and prevalences
`0 < p₀`, `p₁ < 1`, the relative risk due to confounding satisfies
`1 ≤ RR_conf ≤ min (OR_CE, rr, 1 / p₀, rr / ((1 - p₀) + p₀ rr),
OR_CE / ((1 - p₀) + p₀ OR_CE))`. -/
theorem flandersKhoury {rr p₁ p₀ : ℝ} (hrr : 1 ≤ rr) (hp₁' : p₁ < 1) (hp₀ : 0 < p₀)
    (hp₀' : p₀ < 1) (hOR : 1 ≤ EffectMeasure.oddsRatio p₁ p₀) :
    1 ≤ biasFactor rr p₁ p₀ ∧
      biasFactor rr p₁ p₀ ≤
        min (min (min (min (EffectMeasure.oddsRatio p₁ p₀) rr) (1 / p₀))
          (rr / mixFactor rr p₀))
          (EffectMeasure.oddsRatio p₁ p₀ / mixFactor (EffectMeasure.oddsRatio p₁ p₀) p₀) := by
  have hle := (one_le_oddsRatio_iff hp₁' hp₀ hp₀').1 hOR
  have hp₁ : 0 < p₁ := lt_of_lt_of_le hp₀ hle
  have g0 := mixFactor_pos (rr := rr) (by linarith) hp₀.le hp₀'.le
  have hs : 0 ≤ rr - 1 := by linarith
  -- the prevalence ratio bound, from which the others follow
  have hprev : biasFactor rr p₁ p₀ ≤ p₁ / p₀ := by
    unfold biasFactor
    rw [div_le_div_iff₀ g0 hp₀]
    unfold mixFactor
    nlinarith [mul_nonneg hs (sub_nonneg.2 hle)]
  rw [oddsRatio_div_mixFactor hp₁' hp₀ hp₀']
  refine ⟨?_, le_min (le_min (le_min (le_min ?_ ?_) ?_) ?_) hprev⟩
  · unfold biasFactor
    rw [one_le_div g0]
    unfold mixFactor
    nlinarith [mul_nonneg hs (sub_nonneg.2 hle)]
  · refine hprev.trans ?_
    unfold EffectMeasure.oddsRatio EffectMeasure.odds
    have h1 : 0 < 1 - p₁ := by linarith
    have h0 : 0 < 1 - p₀ := by linarith
    rw [div_le_div_iff₀ hp₀ (div_pos hp₀ h0), mul_div_assoc', div_mul_eq_mul_div,
      div_le_div_iff₀ h0 h1]
    nlinarith [mul_pos hp₁ hp₀]
  · unfold biasFactor
    rw [div_le_iff₀ g0]
    unfold mixFactor
    nlinarith [mul_nonneg hs hp₀.le, mul_nonneg hs (sub_nonneg.2 hp₁'.le)]
  · exact hprev.trans (div_le_div_of_nonneg_right hp₁'.le hp₀.le)
  · unfold biasFactor
    rw [div_le_div_iff_of_pos_right g0]
    unfold mixFactor
    nlinarith [mul_nonneg hs (sub_nonneg.2 hp₁'.le)]

/-- **The Flanders and Khoury interval for the adjusted risk ratio** (Fox, MacLehose and Lash
2021, text after Table 5.9). In the stratum risk model with confounder to disease risk ratio
`rr ≥ 1` among the unexposed and confounder to exposure odds ratio at least one, the SMR lies
between `RR_crude / Parm_min` and `RR_crude`, where `Parm_min` is any common upper bound of the
relative risk due to confounding, for instance the minimum of Table 5.9. -/
theorem smr_mem_flandersKhoury {m : Bool → Bool → ℝ} {π : Bool → ℝ} {rr parm : ℝ}
    (hm : ∀ e c, 0 < m e c) (hπ₀ : 0 < π false) (hπ₀' : π false < 1) (hπ₁' : π true < 1)
    (hrr : 1 ≤ rr) (hm0 : m false true = rr * m false false)
    (hOR : 1 ≤ EffectMeasure.oddsRatio (π true) (π false))
    (hparm : biasFactor rr (π true) (π false) ≤ parm) :
    crudeRR m π / parm ≤ smr m π ∧ smr m π ≤ crudeRR m π := by
  have hle := (one_le_oddsRatio_iff hπ₁' hπ₀ hπ₀').1 hOR
  have hπ₁ : 0 < π true := lt_of_lt_of_le hπ₀ hle
  have hconf := crudeRR_div_smr (fun c => hm false c)
    (convex_comb_pos hπ₁.le hπ₁'.le (hm _ _) (hm _ _)).ne' hπ₀.le hπ₀'.le hπ₁.le hπ₁'.le hm0
  have h1 := (flandersKhoury hrr hπ₁' hπ₀ hπ₀' hOR).1
  have hS : 0 < smr m π := div_pos (convex_comb_pos hπ₁.le hπ₁'.le (hm _ _) (hm _ _))
    (convex_comb_pos hπ₁.le hπ₁'.le (hm _ _) (hm _ _))
  have hC : 0 < crudeRR m π := div_pos (convex_comb_pos hπ₁.le hπ₁'.le (hm _ _) (hm _ _))
    (convex_comb_pos hπ₀.le hπ₀'.le (hm _ _) (hm _ _))
  rw [← hconf] at h1 hparm
  have hparm0 : 0 < parm := lt_of_lt_of_le one_pos (h1.trans hparm)
  constructor
  · rw [div_le_iff₀ hparm0]
    rw [div_le_iff₀ hS] at hparm
    linarith
  · rwa [one_le_div hS] at h1

/-- **The joint bounding factor is at most each of its arguments**: for `a, b ≥ 1`,
`a b / (a + b - 1) ≤ min a b` (Ding and VanderWeele 2016). -/
theorem boundingFactor_le_min {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    boundingFactor a b ≤ min a b := by
  have hD : 0 < a + b - 1 := by linarith
  unfold boundingFactor
  refine le_min ?_ ?_ <;> rw [div_le_iff₀ hD] <;> nlinarith

/-- **The range of the relative risk due to confounding when only `rr` and `p₀` are fixed.**
For `rr > 1` and `0 ≤ p₀ < 1`, over the prevalences `p₀ ≤ p₁ < 1` the bias factor takes values
in `[1, rr / mixFactor rr p₀)`: the lower end is attained at `p₁ = p₀`, and the upper end is
the value at `p₁ = 1`, which no prevalence below one attains. This is the fourth factor of
Table 5.9 (Fox, MacLehose and Lash 2021). -/
theorem biasFactor_range {rr p₀ : ℝ} (hrr : 1 < rr) (hp₀ : 0 ≤ p₀) (hp₀' : p₀ < 1) :
    (∀ p₁, p₀ ≤ p₁ → p₁ < 1 →
        1 ≤ biasFactor rr p₁ p₀ ∧ biasFactor rr p₁ p₀ < rr / mixFactor rr p₀) ∧
      biasFactor rr p₀ p₀ = 1 ∧ biasFactor rr 1 p₀ = rr / mixFactor rr p₀ := by
  have hg := mixFactor_pos (rr := rr) (by linarith) hp₀ hp₀'.le
  refine ⟨fun p₁ h h' => ⟨?_, ?_⟩, div_self hg.ne', by unfold biasFactor mixFactor; ring_nf⟩
  · unfold biasFactor
    rw [one_le_div hg]
    unfold mixFactor
    nlinarith [mul_nonneg (sub_nonneg.2 hrr.le) (sub_nonneg.2 h)]
  · unfold biasFactor
    rw [div_lt_div_iff_of_pos_right hg]
    unfold mixFactor
    nlinarith [mul_pos (sub_pos.2 hrr) (sub_pos.2 h')]

/-! ### Monotonicity and the conservative case `p₁ = 1` -/

/-- With `rr ≥ 1` the bias factor is nondecreasing in the prevalence `p₁` among the exposed
(Fox, MacLehose and Lash 2021, "The E-Value and G-Value", Figure 5.7). -/
theorem biasFactor_mono_left {rr p₁ q₁ p₀ : ℝ} (hrr : 1 ≤ rr) (h : p₁ ≤ q₁)
    (hg : 0 < mixFactor rr p₀) : biasFactor rr p₁ p₀ ≤ biasFactor rr q₁ p₀ := by
  unfold biasFactor
  refine div_le_div_of_nonneg_right ?_ hg.le
  unfold mixFactor
  nlinarith [mul_nonneg (sub_nonneg.2 hrr) (sub_nonneg.2 h)]

/-- With `rr ≥ 1` the bias factor is nonincreasing in the prevalence `p₀` among the
unexposed, for `0 ≤ p₁` and prevalences in `[0, 1]`. -/
theorem biasFactor_anti_right {rr p₁ p₀ q₀ : ℝ} (hrr : 1 ≤ rr) (h : p₀ ≤ q₀) (hp₀ : 0 ≤ p₀)
    (hq₀ : q₀ ≤ 1) (hp₁ : 0 ≤ p₁) (hp₁' : p₁ ≤ 1) :
    biasFactor rr p₁ q₀ ≤ biasFactor rr p₁ p₀ := by
  have hr : 0 < rr := by linarith
  unfold biasFactor
  exact div_le_div_of_nonneg_left (mixFactor_pos hr hp₁ hp₁').le
    (mixFactor_pos hr hp₀ (h.trans hq₀))
    (by unfold mixFactor; nlinarith [mul_nonneg (sub_nonneg.2 hrr) (sub_nonneg.2 h)])

/-- **Monotonicity along `p₀ = p₁ / RR_EC`** (Fox, MacLehose and Lash 2021, "The E-Value and
G-Value"). With `rr ≥ 1` and confounder to exposure risk ratio `K = RR_EC ≥ 1`, the bias factor
`biasFactor rr p₁ (p₁ / K)` is nondecreasing in `p₁ ≥ 0`; its derivative has the sign of
`(rr - 1) (1 - 1 / K)`. -/
theorem biasFactor_along_mono {rr K p q : ℝ} (hrr : 1 ≤ rr) (hK : 1 ≤ K) (hp : 0 ≤ p)
    (hpq : p ≤ q) : biasFactor rr p (p / K) ≤ biasFactor rr q (q / K) := by
  have hK0 : 0 < K := by linarith
  have hgp : 0 < mixFactor rr (p / K) := by
    unfold mixFactor
    have : 0 ≤ (rr - 1) * (p / K) := mul_nonneg (by linarith) (div_nonneg hp hK0.le)
    nlinarith
  have hgq : 0 < mixFactor rr (q / K) := by
    unfold mixFactor
    have : 0 ≤ (rr - 1) * (q / K) := mul_nonneg (by linarith) (div_nonneg (hp.trans hpq) hK0.le)
    nlinarith
  unfold biasFactor
  rw [div_le_div_iff₀ hgp hgq]
  unfold mixFactor
  have e : ∀ x : ℝ, rr * (x / K) + (1 - x / K) = (K + (rr - 1) * x) / K := fun x => by
    field_simp; ring
  rw [e, e]
  rw [← mul_div_assoc, ← mul_div_assoc, div_le_div_iff_of_pos_right hK0]
  nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hrr) (sub_nonneg.2 hK)) (sub_nonneg.2 hpq)]

/-- **Attainment at `p₁ = 1`** (Fox, MacLehose and Lash 2021, "The E-Value and G-Value"):
`biasFactor rr 1 (1 / K) = boundingFactor rr K = rr K / (rr + K - 1)`, the joint bounding factor
of Ding and VanderWeele. -/
theorem biasFactor_one {rr K : ℝ} (hrr : 1 ≤ rr) (hK : 1 ≤ K) :
    biasFactor rr 1 (1 / K) = boundingFactor rr K := by
  unfold biasFactor mixFactor boundingFactor
  have hK0 : K ≠ 0 := by positivity
  have hD : rr + K - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- **The E-value assumes `p₁ = 1`**: along `p₀ = p₁ / K` with `0 ≤ p₁ ≤ 1`, the bias factor is
at most its value at `p₁ = 1`, the joint bounding factor `boundingFactor rr K`. The deterministic
prevalence `p₁ = 1` attains the bound; by `biasFactor_eq_boundingFactor_iff` it is the only
prevalence that does when `rr > 1` and `K > 1`, while for `rr = 1` or `K = 1` every prevalence
attains it. -/
theorem biasFactor_le_boundingFactor {rr K p : ℝ} (hrr : 1 ≤ rr) (hK : 1 ≤ K) (hp : 0 ≤ p)
    (hp' : p ≤ 1) : biasFactor rr p (p / K) ≤ boundingFactor rr K := by
  rw [← biasFactor_one hrr hK]
  exact biasFactor_along_mono hrr hK hp hp'

/-- **The equality case of `biasFactor_le_boundingFactor`.** For `rr, K ≥ 1` and `p₁ ≥ 0`, the
bias factor along `p₀ = p₁ / K` equals the joint bounding factor exactly when `p₁ = 1`,
`rr = 1` or `K = 1`: cross multiplied, the gap is `(rr - 1) (K - 1) (1 - p₁)`. -/
theorem biasFactor_eq_boundingFactor_iff {rr K p : ℝ} (hrr : 1 ≤ rr) (hK : 1 ≤ K)
    (hp : 0 ≤ p) : biasFactor rr p (p / K) = boundingFactor rr K ↔ p = 1 ∨ rr = 1 ∨ K = 1 := by
  have hK0 : 0 < K := by linarith
  have hg : 0 < mixFactor rr (p / K) := by
    unfold mixFactor
    have : 0 ≤ (rr - 1) * (p / K) := mul_nonneg (by linarith) (div_nonneg hp hK0.le)
    nlinarith
  have hD : 0 < rr + K - 1 := by linarith
  have key : mixFactor rr p * (rr + K - 1) - rr * K * mixFactor rr (p / K) =
      -((rr - 1) * (K - 1) * (1 - p)) := by
    unfold mixFactor; field_simp; ring
  unfold biasFactor boundingFactor
  rw [div_eq_div_iff hg.ne' hD.ne', ← sub_eq_zero, key, neg_eq_zero, mul_eq_zero, mul_eq_zero,
    sub_eq_zero, sub_eq_zero, sub_eq_zero, eq_comm (a := (1 : ℝ)) (b := p)]
  tauto

/-! ### Explaining away: Equations 5.11 to 5.13 and the G-value -/

/-- **Equation 5.11** of Fox, MacLehose and Lash (2021). With `p₀ = p₁ / K` (`K = RR_EC`),
`p₁ > 0` and `RR_obs ≠ K`, the confounder fully explains the observed risk ratio
(`RR_adj = 1`, that is `RR_obs = biasFactor rr p₁ (p₁ / K)`) exactly when
`rr = (K - K p₁ - K RR_obs + RR_obs p₁) / (p₁ (RR_obs - K))`. -/
theorem explainAway_iff {RR rr K p₁ : ℝ} (hp₁ : 0 < p₁) (hK : 0 < K) (hRK : RR ≠ K)
    (hg : mixFactor rr (p₁ / K) ≠ 0) :
    RR = biasFactor rr p₁ (p₁ / K) ↔
      rr = (K - K * p₁ - K * RR + RR * p₁) / (p₁ * (RR - K)) := by
  have hd : p₁ * (RR - K) ≠ 0 := mul_ne_zero hp₁.ne' (sub_ne_zero.2 hRK)
  unfold biasFactor
  rw [eq_div_iff hg, eq_div_iff hd]
  unfold mixFactor
  constructor
  · intro h
    field_simp at h
    linear_combination h
  · intro h
    field_simp
    linear_combination h

/-- **Equation 5.12**: at `p₁ = 1` the isopleth is `rr = RR_obs (1 - K) / (RR_obs - K)`. -/
theorem explainAway_one_iff {RR rr K : ℝ} (hK : 0 < K) (hRK : RR ≠ K)
    (hg : mixFactor rr (1 / K) ≠ 0) :
    RR = biasFactor rr 1 (1 / K) ↔ rr = (RR - K * RR) / (RR - K) := by
  rw [explainAway_iff one_pos hK hRK hg]
  constructor <;> intro h <;> rw [h] <;> ring_nf

/-- **The solution of Equation 5.11 relative to one**: for `p₁ ≠ 0` and `RR ≠ K`,
`rr - 1 = K (RR - 1) / (p₁ (K - RR))`, where `rr` is the right side of Equation 5.11. -/
theorem explainAway_sol_sub_one {RR K p₁ : ℝ} (hp₁ : p₁ ≠ 0) (hRK : RR ≠ K) :
    (K - K * p₁ - K * RR + RR * p₁) / (p₁ * (RR - K)) - 1 = K * (RR - 1) / (p₁ * (K - RR)) := by
  have h1 : RR - K ≠ 0 := sub_ne_zero.2 hRK
  have h2 : K - RR ≠ 0 := sub_ne_zero.2 hRK.symm
  field_simp
  ring

/-- **Admissibility of the solution of Equation 5.11.** For an observed `RR > 1`, `p₁ > 0` and
`K = RR_EC > 0` with `K ≠ RR`, the confounder to disease risk ratio solved from Equation 5.11
exceeds one exactly when `RR < K`. -/
theorem one_lt_explainAway_sol_iff {RR K p₁ : ℝ} (hRR : 1 < RR) (hp₁ : 0 < p₁) (hK : 0 < K)
    (hRK : RR ≠ K) :
    1 < (K - K * p₁ - K * RR + RR * p₁) / (p₁ * (RR - K)) ↔ RR < K := by
  rw [← sub_pos, explainAway_sol_sub_one hp₁.ne' hRK,
    div_pos_iff_of_pos_left (mul_pos hK (by linarith)), mul_pos_iff_of_pos_left hp₁, sub_pos]

/-- **An inadmissible solution.** For `1 ≤ K < RR` and `0 < p₁ ≤ 1`, the solution of
Equation 5.11 is at most zero, so no confounder with confounder to exposure risk ratio
`K ≤ RR_obs` explains the observed risk ratio away. -/
theorem explainAway_sol_nonpos {RR K p₁ : ℝ} (hK : 1 ≤ K) (hKR : K < RR) (hp₁ : 0 < p₁)
    (hp₁' : p₁ ≤ 1) : (K - K * p₁ - K * RR + RR * p₁) / (p₁ * (RR - K)) ≤ 0 := by
  refine div_nonpos_of_nonpos_of_nonneg ?_ (mul_nonneg hp₁.le (by linarith))
  nlinarith [mul_nonneg (sub_nonneg.2 hp₁') (sub_nonneg.2 hKR.le)]

/-- For `rr ≥ 1` and `K > 1` the joint bounding factor is below `K`. -/
theorem boundingFactor_lt_right {rr K : ℝ} (hrr : 1 ≤ rr) (hK : 1 < K) :
    boundingFactor rr K < K := by
  unfold boundingFactor
  rw [div_lt_iff₀ (by linarith)]
  nlinarith

/-- **When a confounder can explain the estimate away** (Equation 5.11 with its admissibility
region). For `K = RR_EC > 1`, a prevalence `0 < p₁ ≤ 1` among the exposed and an observed
`RR > 1`, some confounder to disease risk ratio `rr ≥ 1` gives bias factor exactly `RR` along
`p₀ = p₁ / K` if and only if `RR < K`. At `RR ≥ K` the bias factor stays below `K` for every
`rr ≥ 1` (`biasFactor_le_boundingFactor` and `boundingFactor_lt_right`). -/
theorem exists_explainAway_iff {RR K p₁ : ℝ} (hK : 1 < K) (hp₁ : 0 < p₁) (hp₁' : p₁ ≤ 1)
    (hRR : 1 < RR) : (∃ rr, 1 ≤ rr ∧ RR = biasFactor rr p₁ (p₁ / K)) ↔ RR < K := by
  constructor
  · rintro ⟨rr, hrr, h⟩
    rw [h]
    exact (biasFactor_le_boundingFactor hrr hK.le hp₁.le hp₁').trans_lt
      (boundingFactor_lt_right hrr hK)
  · intro hlt
    have hRK : RR ≠ K := hlt.ne
    set s := (K - K * p₁ - K * RR + RR * p₁) / (p₁ * (RR - K)) with hs
    have h1 : 1 < s := (one_lt_explainAway_sol_iff hRR hp₁ (by linarith) hRK).2 hlt
    have hg : mixFactor s (p₁ / K) ≠ 0 := by
      unfold mixFactor
      have : 0 ≤ (s - 1) * (p₁ / K) := mul_nonneg (by linarith) (by positivity)
      nlinarith
    exact ⟨s, h1.le, (explainAway_iff hp₁ (by linarith) hRK hg).2 rfl⟩

/-- The E-value of Fox, MacLehose and Lash (2021), Equation 5.13 (page 134), printed as
`RR_obs + sqrt (RR_obs² - RR_obs)`, the common value `RR_EC = RR_CD > 1` that explains away an
observed risk ratio above one when `p₁ = 1`; extended to a protective risk ratio
`0 < RR < 1` in the standard way (VanderWeele and Ding 2017) by applying the formula to
`q = max RR (1 / RR)`: `eValue RR = q + sqrt (q (q - 1))`. For `RR ≥ 1` this is the printed
formula (`eValue_of_one_le`), the expression of `evalue_le_max`; the value is meaningful only
for `RR > 0`. -/
noncomputable def eValue (RR : ℝ) : ℝ :=
  max RR RR⁻¹ + Real.sqrt (max RR RR⁻¹ * (max RR RR⁻¹ - 1))

/-- For `RR ≥ 1` the E-value is the printed formula `RR + sqrt (RR (RR - 1))`. -/
theorem eValue_of_one_le {RR : ℝ} (hRR : 1 ≤ RR) :
    eValue RR = RR + Real.sqrt (RR * (RR - 1)) := by
  unfold eValue
  rw [max_eq_left ((inv_le_one_of_one_le₀ hRR).trans hRR)]

/-- The E-value does not depend on the coding of the exposure: `eValue (1 / RR) = eValue RR`.
For `RR > 0` this is the recoding of the exposure; at `RR = 0` it is an identity between
totalized expressions (`0⁻¹ = 0`). -/
theorem eValue_inv (RR : ℝ) : eValue RR⁻¹ = eValue RR := by
  unfold eValue
  rw [inv_inv, max_comm]

/-- For a protective risk ratio `0 < RR ≤ 1` the E-value is the formula applied to `1 / RR`. -/
theorem eValue_of_le_one {RR : ℝ} (h0 : 0 < RR) (h1 : RR ≤ 1) :
    eValue RR = RR⁻¹ + Real.sqrt (RR⁻¹ * (RR⁻¹ - 1)) := by
  rw [← eValue_inv, eValue_of_one_le ((one_le_inv₀ h0).2 h1)]

/-- **The E-value inequality** (`evalue_le_max`) in terms of `eValue`: for an observed
`RR > 1`, if a confounder with parameters `a, b ≥ 1` explains it away
(`RR ≤ boundingFactor a b`), then `eValue RR ≤ max a b`. -/
theorem eValue_le_max {RR a b : ℝ} (hRR : 1 < RR) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : RR ≤ boundingFactor a b) : eValue RR ≤ max a b := by
  rw [eValue_of_one_le hRR.le]
  exact evalue_le_max hRR ha hb h

/-- **The E-value inequality for a protective estimate**: for `0 < RR < 1`, if the confounder
explains away `1 / RR` (`1 / RR ≤ boundingFactor a b`, with the exposure recoded), then
`eValue RR ≤ max a b`. -/
theorem eValue_le_max_of_lt_one {RR a b : ℝ} (h0 : 0 < RR) (h1 : RR < 1) (ha : 1 ≤ a)
    (hb : 1 ≤ b) (h : RR⁻¹ ≤ boundingFactor a b) : eValue RR ≤ max a b := by
  rw [← eValue_inv]
  exact eValue_le_max ((one_lt_inv₀ h0).2 h1) ha hb h

/-- **Sharpness of the E-value** (Equation 5.13): for `RR ≥ 1`,
`boundingFactor E E = RR` with `E = eValue RR`. Together with `evalue_le_max` this shows that
the E-value is the least common value of the two risk ratio parameters that explains away
`RR`. -/
theorem boundingFactor_eValue {RR : ℝ} (hRR : 1 ≤ RR) :
    boundingFactor (eValue RR) (eValue RR) = RR := by
  rw [eValue_of_one_le hRR]
  unfold boundingFactor
  have hs := Real.sq_sqrt (show 0 ≤ RR * (RR - 1) by nlinarith)
  have hs0 := Real.sqrt_nonneg (RR * (RR - 1))
  have hD : RR + Real.sqrt (RR * (RR - 1)) + (RR + Real.sqrt (RR * (RR - 1))) - 1 ≠ 0 := by
    linarith
  rw [div_eq_iff hD]
  linear_combination hs

/-- The E-value explains away the observed risk ratio at `p₁ = 1`: a confounder with
`RR_CD = RR_EC = eValue RR` and prevalence one among the exposed has bias factor `RR`. -/
theorem biasFactor_eValue {RR : ℝ} (hRR : 1 ≤ RR) :
    biasFactor (eValue RR) 1 (1 / eValue RR) = RR := by
  have hE : 1 ≤ eValue RR := by
    rw [eValue_of_one_le hRR]; linarith [Real.sqrt_nonneg (RR * (RR - 1))]
  rw [biasFactor_one hE hE, boundingFactor_eValue hRR]

/-- The linear coefficient `RR + p₁ + RR p₁ - 1` of the G-value quadratic. -/
def gCoeff (RR p₁ : ℝ) : ℝ := RR + p₁ + RR * p₁ - 1

/-- The G-value of Fox, MacLehose and Lash (2021), "The E-Value and G-Value": the larger root
`(B + sqrt (B² - 4 RR p₁²)) / (2 p₁)` of `p₁ G² - B G + RR p₁ = 0` with `B = gCoeff RR p₁`. The
printed radicand `(1 - p₁ - RR - RR p₁)² - 4 RR p₁²` is the same number. -/
noncomputable def gValue (RR p₁ : ℝ) : ℝ :=
  (gCoeff RR p₁ + Real.sqrt (gCoeff RR p₁ ^ 2 - 4 * RR * p₁ ^ 2)) / (2 * p₁)

/-- For `RR ≥ 1` and `p₁ > 0` the discriminant of the G-value quadratic is nonnegative and
`gCoeff RR p₁ ≥ 2 p₁`. -/
theorem gCoeff_facts {RR p₁ : ℝ} (hRR : 1 ≤ RR) (hp₁ : 0 < p₁) :
    2 * p₁ ≤ gCoeff RR p₁ ∧ 0 ≤ gCoeff RR p₁ ^ 2 - 4 * RR * p₁ ^ 2 := by
  set t := Real.sqrt RR with ht
  have ht0 : 0 ≤ t := Real.sqrt_nonneg RR
  have htt : t ^ 2 = RR := Real.sq_sqrt (by linarith)
  have ht1 : 1 ≤ t := by nlinarith
  have hB : gCoeff RR p₁ - 2 * p₁ * t = (t ^ 2 - 1) + p₁ * (t - 1) ^ 2 := by
    unfold gCoeff; rw [← htt]; ring
  have h1 : 0 ≤ gCoeff RR p₁ - 2 * p₁ * t := by
    rw [hB]; nlinarith [mul_nonneg hp₁.le (sq_nonneg (t - 1))]
  refine ⟨by nlinarith, ?_⟩
  have e : gCoeff RR p₁ ^ 2 - 4 * RR * p₁ ^ 2 =
      (gCoeff RR p₁ - 2 * p₁ * t) * (gCoeff RR p₁ + 2 * p₁ * t) := by
    rw [← htt]; ring
  rw [e]
  exact mul_nonneg h1 (by nlinarith)

/-- The G-value solves the quadratic `p₁ G² - (RR + p₁ + RR p₁ - 1) G + RR p₁ = 0` and is at
least one, for `RR ≥ 1` and `p₁ > 0`. -/
theorem gValue_root {RR p₁ : ℝ} (hRR : 1 ≤ RR) (hp₁ : 0 < p₁) :
    p₁ * gValue RR p₁ ^ 2 - gCoeff RR p₁ * gValue RR p₁ + RR * p₁ = 0 ∧ 1 ≤ gValue RR p₁ := by
  obtain ⟨hB, hdisc⟩ := gCoeff_facts hRR hp₁
  have hs := Real.sq_sqrt hdisc
  have hs0 := Real.sqrt_nonneg (gCoeff RR p₁ ^ 2 - 4 * RR * p₁ ^ 2)
  unfold gValue
  set S := Real.sqrt (gCoeff RR p₁ ^ 2 - 4 * RR * p₁ ^ 2)
  set B := gCoeff RR p₁
  constructor
  · field_simp
    linear_combination hs
  · rw [le_div_iff₀ (by positivity)]
    linarith

/-- **The G-value explains away the observed risk ratio**: a confounder with
`RR_CD = RR_EC = gValue RR p₁` and prevalence `p₁ ∈ (0, 1]` among the exposed (so
`p₀ = p₁ / G`) has bias factor exactly `RR`. -/
theorem biasFactor_gValue {RR p₁ : ℝ} (hRR : 1 ≤ RR) (hp₁ : 0 < p₁) :
    biasFactor (gValue RR p₁) p₁ (p₁ / gValue RR p₁) = RR := by
  obtain ⟨hq, hG⟩ := gValue_root hRR hp₁
  set G := gValue RR p₁
  have hG0 : 0 < G := by linarith
  have hg : 0 < mixFactor G (p₁ / G) := by
    unfold mixFactor
    have : 0 ≤ (G - 1) * (p₁ / G) := mul_nonneg (by linarith) (div_nonneg hp₁.le hG0.le)
    nlinarith
  unfold biasFactor
  rw [div_eq_iff hg.ne']
  unfold mixFactor gCoeff at *
  field_simp
  linear_combination hq

/-- **`G(1) = E`**: at `p₁ = 1` the G-value is the E-value, for an observed `RR ≥ 1` (the
domain of both formulas). -/
theorem gValue_one {RR : ℝ} (hRR : 1 ≤ RR) : gValue RR 1 = eValue RR := by
  rw [eValue_of_one_le hRR]
  unfold gValue gCoeff
  have e : (RR + 1 + RR * 1 - 1) ^ 2 - 4 * RR * 1 ^ 2 = 2 ^ 2 * (RR * (RR - 1)) := by ring
  rw [e, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  ring

/-- **The G-value is at least the E-value**: for `RR ≥ 1` and `0 < p₁ ≤ 1`,
`eValue RR ≤ gValue RR p₁`. The strict form printed in the book is `eValue_lt_gValue`. -/
theorem eValue_le_gValue {RR p₁ : ℝ} (hRR : 1 ≤ RR) (hp₁ : 0 < p₁) (hp₁' : p₁ ≤ 1) :
    eValue RR ≤ gValue RR p₁ := by
  have hG := (gValue_root hRR hp₁).2
  rcases hRR.lt_or_eq with h | h
  · have hb : RR ≤ boundingFactor (gValue RR p₁) (gValue RR p₁) := by
      have := biasFactor_le_boundingFactor hG hG hp₁.le hp₁'
      rwa [biasFactor_gValue hRR hp₁] at this
    simpa using eValue_le_max h hG hG hb
  · subst h
    rw [eValue_of_one_le le_rfl]
    simpa using hG

/-- **The G-value exceeds the E-value when `p₁ < 1`** (Fox, MacLehose and Lash 2021, page
135: "When `p₁ < 1`, the result will be greater than the E-value"), for an observed `RR > 1`.
-/
theorem eValue_lt_gValue {RR p₁ : ℝ} (hRR : 1 < RR) (hp₁ : 0 < p₁) (hp₁' : p₁ < 1) :
    eValue RR < gValue RR p₁ := by
  refine lt_of_le_of_ne (eValue_le_gValue hRR.le hp₁ hp₁'.le) fun h => ?_
  have hG := (gValue_root hRR.le hp₁).2
  have hb : biasFactor (gValue RR p₁) p₁ (p₁ / gValue RR p₁) =
      boundingFactor (gValue RR p₁) (gValue RR p₁) := by
    rw [biasFactor_gValue hRR.le hp₁, ← h, boundingFactor_eValue hRR.le]
  rcases (biasFactor_eq_boundingFactor_iff hG hG hp₁.le).1 hb with h1 | h1 | h1
  · linarith
  all_goals
    have := biasFactor_gValue hRR.le hp₁
    rw [h1] at this
    norm_num [biasFactor, mixFactor] at this
    linarith

/-- **The G-value is the only root at least one.** For `RR > 1` and `p₁ > 0`, any root
`G ≥ 1` of `p₁ G² - (RR + p₁ + RR p₁ - 1) G + RR p₁ = 0` is `gValue RR p₁`: the quadratic
equals `1 - RR < 0` at `G = 1`, so its other root is below one. -/
theorem eq_gValue_of_root {RR p₁ G : ℝ} (hRR : 1 < RR) (hp₁ : 0 < p₁) (hG : 1 ≤ G)
    (hq : p₁ * G ^ 2 - gCoeff RR p₁ * G + RR * p₁ = 0) : G = gValue RR p₁ := by
  obtain ⟨hq', hG'⟩ := gValue_root hRR.le hp₁
  set H := gValue RR p₁
  by_contra hne
  have hsub : G - H ≠ 0 := sub_ne_zero.2 hne
  -- the two roots have sum `B / p₁`, hence product `RR`
  have hsum : p₁ * (G + H) = gCoeff RR p₁ := by
    have : (G - H) * (p₁ * (G + H) - gCoeff RR p₁) = 0 := by linear_combination hq - hq'
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hsub
    · linarith
  have hprod : p₁ * (G * H) = p₁ * RR := by
    unfold gCoeff at hsum hq
    linear_combination -hq + G * hsum
  have hGH : G * H = RR := mul_left_cancel₀ hp₁.ne' hprod
  have h1 : 0 ≤ (G - 1) * (H - 1) := mul_nonneg (by linarith) (by linarith)
  -- at `1` the quadratic is `p₁ (1 - G) (1 - H) = 1 - RR < 0`
  have h2 : p₁ * ((G - 1) * (H - 1)) = 1 - RR := by
    unfold gCoeff at hsum
    linear_combination (-1 : ℝ) * hsum + p₁ * hGH
  nlinarith [mul_nonneg hp₁.le h1]

/-! ### Signed rules for the direction of confounding bias -/

/-- **Signed DAG rule, difference scale** (Fox, MacLehose and Lash 2021, Table 5.10;
VanderWeele and colleagues). With no exposure by confounder interaction on the additive scale
(common confounder to disease risk difference `γ`), the sign of the bias of the crude risk
difference is the sign of `γ` times the sign of `p₁ - p₀`, for every standard population. -/
theorem sign_unadjustedBias {m : Bool → Bool → ℝ} {γ : ℝ}
    (h₁ : m true true - m true false = γ) (h₀ : m false true - m false false = γ)
    (π : Bool → ℝ) (r : ℝ) :
    SignType.sign (unadjustedBias m π r) = SignType.sign γ * SignType.sign (π true - π false) := by
  rw [unadjustedBias_eq_of_no_interaction h₁ h₀, sign_mul]

/-- **Signed DAG rule, ratio scale** (Table 5.10): for a positive denominator the relative risk
due to confounding exceeds one exactly when `(rr - 1) (p₁ - p₀) > 0`, and the sign of
`RR_conf - 1` is the sign of `rr - 1` times the sign of `p₁ - p₀`. -/
theorem sign_biasFactor_sub_one {rr p₁ p₀ : ℝ} (hg : 0 < mixFactor rr p₀) :
    SignType.sign (biasFactor rr p₁ p₀ - 1) =
      SignType.sign (rr - 1) * SignType.sign (p₁ - p₀) := by
  have e : biasFactor rr p₁ p₀ - 1 = (rr - 1) * (p₁ - p₀) * (mixFactor rr p₀)⁻¹ := by
    unfold biasFactor
    rw [← mixFactor_sub]
    field_simp
  rw [e, sign_mul, sign_mul, sign_pos (inv_pos.2 hg), mul_one]

/-- The signed rule in the stratum risk model: the crude risk ratio exceeds the SMR exactly
when `(rr - 1) (p₁ - p₀) > 0`, with `rr` the confounder to disease risk ratio among the
unexposed. The unexposed stratum risks and the observed risk of the exposed must be positive
(at a zero exposed risk both ratios are zero). -/
theorem smr_lt_crudeRR_iff {m : Bool → Bool → ℝ} {π : Bool → ℝ} {rr : ℝ}
    (hm₀ : ∀ c, 0 < m false c) (hO : 0 < observedMean m π true)
    (hπ₀ : 0 ≤ π false) (hπ₀' : π false ≤ 1) (hπ₁ : 0 ≤ π true) (hπ₁' : π true ≤ 1)
    (hrr : m false true = rr * m false false) :
    smr m π < crudeRR m π ↔ 0 < (rr - 1) * (π true - π false) := by
  have hconf := crudeRR_div_smr hm₀ hO.ne' hπ₀ hπ₀' hπ₁ hπ₁' hrr
  obtain ⟨hrr0, -, hS0⟩ := unexposed_facts (π := π) hm₀ hrr
  have hg := mixFactor_pos hrr0 hπ₀ hπ₀'
  have hS : 0 < smr m π := by
    unfold smr
    rw [hS0]
    exact div_pos hO (mul_pos (hm₀ false) (mixFactor_pos hrr0 hπ₁ hπ₁'))
  rw [← one_lt_div hS, hconf]
  unfold biasFactor
  rw [one_lt_div hg, ← sub_pos, mixFactor_sub]

/-- The bias of the crude risk difference for a standard population with prevalence
`r = w p₁ + (1 - w) p₀` between the two arms: it is
`((1 - w) γ₁ + w γ₀) (p₁ - p₀)`, with `γ₁`, `γ₀` the confounder to disease risk differences
among the exposed and the unexposed. -/
theorem unadjustedBias_eq_mix (m : Bool → Bool → ℝ) (π : Bool → ℝ) {w r : ℝ}
    (hr : r = w * π true + (1 - w) * π false) :
    unadjustedBias m π r =
      ((1 - w) * (m true true - m true false) + w * (m false true - m false false)) *
        (π true - π false) := by
  rw [unadjustedBias_eq, hr]
  ring

/-- **Signed DAG rule under sign agreement** (Fox, MacLehose and Lash 2021, Table 5.10, stated
there under monotonicity assumptions). If the confounder to disease risk differences in the two
exposure groups are both positive (interaction of any size allowed), then for every standard
population between the arms (`r = w p₁ + (1 - w) p₀`, `0 ≤ w ≤ 1`) the bias of the crude risk
difference has the sign of `p₁ - p₀`; if both are negative, the opposite sign. -/
theorem sign_unadjustedBias_of_same_sign {m : Bool → Bool → ℝ} (π : Bool → ℝ) {w r : ℝ}
    (hw : 0 ≤ w) (hw' : w ≤ 1) (hr : r = w * π true + (1 - w) * π false) :
    (0 < m true true - m true false → 0 < m false true - m false false →
        SignType.sign (unadjustedBias m π r) = SignType.sign (π true - π false)) ∧
      (m true true - m true false < 0 → m false true - m false false < 0 →
        SignType.sign (unadjustedBias m π r) = -SignType.sign (π true - π false)) := by
  rw [unadjustedBias_eq_mix m π hr, sign_mul]
  constructor
  · intro h₁ h₀
    have := convex_comb_pos hw hw' h₀ h₁
    rw [sign_pos (by linarith), one_mul]
  · intro h₁ h₀
    have := convex_comb_pos hw hw' (neg_pos.2 h₀) (neg_pos.2 h₁)
    rw [sign_neg (by linarith), neg_one_mul]

/-- **Signed DAG rule for the standard of the exposed**, the standard of the book's SMR: the
bias of the crude risk difference relative to the effect standardized to the exposed is
`γ₀ (p₁ - p₀)`, so its sign is the sign of the confounder to disease risk difference among the
unexposed times the sign of `p₁ - p₀`, whatever the risk difference among the exposed. -/
theorem sign_unadjustedBias_exposed {m : Bool → Bool → ℝ} {γ₀ : ℝ}
    (h₀ : m false true - m false false = γ₀) (π : Bool → ℝ) :
    SignType.sign (unadjustedBias m π (π true)) =
      SignType.sign γ₀ * SignType.sign (π true - π false) := by
  rw [unadjustedBias_eq, h₀, sub_self, mul_zero, zero_sub, ← sign_mul]
  congr 1
  ring

/-- **The signed rule needs sign agreement across exposure strata.** With confounder to disease
risk differences of opposite signs (`γ₁ = 0.2 > 0` among the exposed, `γ₀ = -0.2 < 0` among the
unexposed) and `p₁ = 0.8 > p₀ = 0.2`, the bias of the crude risk difference is negative
relative to the effect standardized to the exposed and positive relative to the effect
standardized to the unexposed, so no single pair of signs determines it for every standard. The
rule for the standard of the exposed (`sign_unadjustedBias_exposed`, the sign of `γ₀` times the
sign of `p₁ - p₀`) still holds here. -/
theorem signed_rule_fails_with_interaction :
    ∃ (m : Bool → Bool → ℝ) (π : Bool → ℝ),
      0 < m true true - m true false ∧ m false true - m false false < 0 ∧
        π false < π true ∧ unadjustedBias m π (π true) < 0 ∧
          0 < unadjustedBias m π (π false) := by
  refine ⟨fun e c => if e then (if c then 2 / 5 else 1 / 5) else (if c then 1 / 10 else 3 / 10),
    fun e => if e then 4 / 5 else 1 / 5, ?_⟩
  simp only [unadjustedBias, observedMean, standardizedEffect, ite_true, ite_false,
    Bool.false_eq_true]
  norm_num

/-! ### Worked examples -/

namespace Examples

/-- The confounder prevalences of Table 5.2: `p₁ = 0.80` among the circumcised, `p₀ = 0.05`
among the uncircumcised. -/
noncomputable def hivPrev : Bool → ℝ := fun e => if e then 4 / 5 else 1 / 20

/-- Both prevalences of Table 5.2 lie in `(0, 1)`. -/
theorem hivPrev_mem : ∀ e, 0 < hivPrev e ∧ hivPrev e < 1 := by
  intro e; cases e <;> norm_num [hivPrev]

/-- `x` rounds to the printed value `v` at half width `δ` (half a unit of the last printed
digit): `v - δ ≤ x < v + δ`. -/
def RoundsTo (x v δ : ℝ) : Prop := v - δ ≤ x ∧ x < v + δ

/-- The projected stratified table of Table 5.5 (Fox, MacLehose and Lash 2021, page 118):
`RR_CD = 0.63` in both exposure groups, indexed by confounder, disease and exposure. -/
noncomputable def table55 : Bool → Bool → Bool → ℝ :=
  projTable 105 85 632 178 (63 / 100) (63 / 100) hivPrev

/-- **All eight cells of Table 5.5** (page 118) round to the printed values: cases `75.2`,
`2.7` (stratum `C₁`, exposed and unexposed) and `29.8`, `82.3` (stratum `C₀`); noncases
`430.4`, `6.2` and `96.6`, `86.8`. Exact values: `75.1705`, `2.7280`, `29.8295`, `82.2720`,
`430.4295`, `6.1720`, `96.5705`, `86.8280`. -/
theorem table_5_5_cells :
    RoundsTo (table55 true true true) 75.2 0.05 ∧ RoundsTo (table55 true true false) 2.7 0.05 ∧
      RoundsTo (table55 false true true) 29.8 0.05 ∧
      RoundsTo (table55 false true false) 82.3 0.05 ∧
      RoundsTo (table55 true false true) 430.4 0.05 ∧
      RoundsTo (table55 true false false) 6.2 0.05 ∧
      RoundsTo (table55 false false true) 96.6 0.05 ∧
      RoundsTo (table55 false false false) 86.8 0.05 := by
  simp only [table55, projTable, projColumn, hivPrev, RoundsTo, splitCases, ite_true,
    Bool.false_eq_true, ite_false]
  norm_num

/-- **The risk ratio row of Table 5.5** (page 118): the projected stratum risk ratios of both
strata round to the printed `0.49` (exactly, both equal the SMR `0.48506`). -/
theorem table_5_5_stratum_rr :
    RoundsTo (projRisk 105 85 632 178 (63 / 100) (63 / 100) hivPrev true true /
        projRisk 105 85 632 178 (63 / 100) (63 / 100) hivPrev false true) 0.49 0.005 ∧
      RoundsTo (projRisk 105 85 632 178 (63 / 100) (63 / 100) hivPrev true false /
        projRisk 105 85 632 178 (63 / 100) (63 / 100) hivPrev false false) 0.49 0.005 := by
  have h := projRisk_eq (a := 105) (b := 85) (nE := 632) (nU := 178) (rr₁ := 63 / 100)
    (rr₀ := 63 / 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hivPrev_mem
  rw [h.1, h.2.1, h.2.2.1, h.2.2.2]
  simp only [hivPrev, ite_true, Bool.false_eq_true, ite_false, mixFactor, RoundsTo]
  norm_num

/-- Table 5.5: the SMR of the projected table is `0.485` (printed `0.49`), exactly the closed
form of Equation 5.1 evaluated at the unrounded crude risk ratio `(105/632)/(85/178)`. -/
theorem table_5_5_smr :
    smr (projRisk 105 85 632 178 (63 / 100) (63 / 100) hivPrev) hivPrev =
        (105 / 632) / (85 / 178) * (mixFactor (63 / 100) (1 / 20) / mixFactor (63 / 100) (4 / 5)) ∧
      0.485 < smr (projRisk 105 85 632 178 (63 / 100) (63 / 100) hivPrev) hivPrev ∧
      smr (projRisk 105 85 632 178 (63 / 100) (63 / 100) hivPrev) hivPrev < 0.4851 := by
  rw [smr_projRisk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hivPrev_mem]
  simp only [hivPrev, ite_true, Bool.false_eq_true, ite_false, mixFactor]
  norm_num

/-- Equation 5.1 with the rounded crude risk ratio `0.35`: `RR_adj = 0.488`, printed `0.49`. -/
theorem eq_5_1_example :
    RoundsTo (0.35 * (mixFactor 0.63 0.05 / mixFactor 0.63 0.8)) 0.49 0.005 := by
  unfold mixFactor RoundsTo; norm_num

/-- With `RR_CD = 0.8` instead of `0.63` the SMR is `0.410` (printed `0.41`). -/
theorem eq_5_1_example_rr08 :
    0.41 < smr (projRisk 105 85 632 178 (4 / 5) (4 / 5) hivPrev) hivPrev ∧
      smr (projRisk 105 85 632 178 (4 / 5) (4 / 5) hivPrev) hivPrev < 0.4101 := by
  rw [smr_projRisk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hivPrev_mem]
  simp only [hivPrev, ite_true, Bool.false_eq_true, ite_false, mixFactor]
  norm_num

/-- Table 5.6 and Equations 5.6 to 5.8 (page 124; effect measure modification,
`RR_CD|E=1 = 0.4`, `RR_CD|E=0 = 0.7`): the SMR is `0.451` (printed `0.45`); the stratum risk
ratios are `0.377` among Muslims and `0.659` among others (printed `0.38` and `0.66`). -/
theorem table_5_6 :
    RoundsTo (smr (projRisk 105 85 632 178 (2 / 5) (7 / 10) hivPrev) hivPrev) 0.45 0.005 ∧
    RoundsTo (projRisk 105 85 632 178 (2 / 5) (7 / 10) hivPrev true true /
        projRisk 105 85 632 178 (2 / 5) (7 / 10) hivPrev false true) 0.38 0.005 ∧
    RoundsTo (projRisk 105 85 632 178 (2 / 5) (7 / 10) hivPrev true false /
        projRisk 105 85 632 178 (2 / 5) (7 / 10) hivPrev false false) 0.66 0.005 := by
  have h := projRisk_eq (a := 105) (b := 85) (nE := 632) (nU := 178) (rr₁ := 2 / 5)
    (rr₀ := 7 / 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hivPrev_mem
  rw [smr_projRisk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hivPrev_mem, h.1, h.2.1, h.2.2.1, h.2.2.2]
  simp only [hivPrev, ite_true, Bool.false_eq_true, ite_false, mixFactor, RoundsTo]
  norm_num

/-- The projected stratified table of Table 5.6 (page 124): `RR_CD|E=1 = 0.4` and
`RR_CD|E=0 = 0.7`, indexed by confounder, disease and exposure. -/
noncomputable def table56 : Bool → Bool → Bool → ℝ :=
  projTable 105 85 632 178 (2 / 5) (7 / 10) hivPrev

/-- **All eight cells of Table 5.6** (page 124) round to the printed values: cases `64.6`,
`3.0` (stratum `C₁`, exposed and unexposed) and `40.4`, `82.0` (stratum `C₀`); noncases
`441.0`, `5.9` and `86.0`, `87.1`. Exact values: `64.6154`, `3.0203`, `40.3846`, `81.9797`,
`440.9846`, `5.8797`, `86.0154`, `87.1203`. -/
theorem table_5_6_cells :
    RoundsTo (table56 true true true) 64.6 0.05 ∧ RoundsTo (table56 true true false) 3.0 0.05 ∧
      RoundsTo (table56 false true true) 40.4 0.05 ∧
      RoundsTo (table56 false true false) 82.0 0.05 ∧
      RoundsTo (table56 true false true) 441.0 0.05 ∧
      RoundsTo (table56 true false false) 5.9 0.05 ∧
      RoundsTo (table56 false false true) 86.0 0.05 ∧
      RoundsTo (table56 false false false) 87.1 0.05 := by
  simp only [table56, projTable, projColumn, hivPrev, RoundsTo, splitCases, ite_true,
    Bool.false_eq_true, ite_false]
  norm_num

/-- Equation 5.8 with the rounded crude risk ratio: `0.35 (0.7 · 0.05 + 0.95) / (0.7 · 0.8 + 0.2)`
is `0.454`, printed `0.45`. -/
theorem eq_5_8_example :
    RoundsTo (0.35 * (mixFactor 0.7 0.05 / mixFactor 0.7 0.8)) 0.45 0.005 := by
  unfold mixFactor RoundsTo; norm_num

/-- The polytomous example ("Polytomous Confounders"): Muslim, Christian and other with risk
ratios `0.4`, `0.8`, `1` and prevalences `0.6, 0.2, 0.2` (circumcised) and `0.05, 0.2, 0.75`
(uncircumcised) give `RR_adj = 0.35 · 0.93 / 0.6 = 0.5425`, printed `0.54`. -/
theorem polytomous_example :
    0.35 * ((∑ v : Fin 3, ![0.4, 0.8, 1] v * ![0.05, 0.2, 0.75] v) /
      (∑ v : Fin 3, ![0.4, 0.8, 1] v * ![0.6, 0.2, 0.2] v)) = (0.5425 : ℝ) := by
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  norm_num

/-- The difference scale example ("Difference Measures"):
`RD_adj = -0.31 - (-0.37)(0.8 - 0.05) = -0.0325`, printed `-0.03`. -/
theorem difference_example : (-0.31 : ℝ) - (-0.37) * (0.8 - 0.05) = -0.0325 := by norm_num

/-- Table 5.8 (5-fluorouracil, observed hazard ratio `0.66`): the adjusted hazard ratio
`0.66 (HR_CD p₀ + 1 - p₀) / (HR_CD p₁ + 1 - p₁)`, with `p₀` the prevalence without and `p₁`
the prevalence with 5-FU, reproduces the printed values to within `0.005` in rows 2 to 16. -/
theorem table_5_8_rows :
    ∀ row ∈ ([(0.6, 0.1, 2, 0.96), (0.5, 0.1, 2, 0.90), (0.9, 0.5, 2, 0.84),
        (0.9, 0.1, 1.75, 1.03), (0.9, 0.5, 1.75, 0.80), (0.5, 0.1, 1.75, 0.84),
        (0.9, 0.1, 1.5, 0.91), (0.9, 0.5, 1.5, 0.77), (0.5, 0.1, 1.5, 0.79),
        (0.9, 0.1, 1.25, 0.79), (0.9, 0.5, 1.25, 0.72), (0.5, 0.1, 1.25, 0.72),
        (0.9, 0.1, 1.1, 0.71), (0.9, 0.5, 1.1, 0.69), (0.5, 0.1, 1.1, 0.69)] :
        List (ℝ × ℝ × ℝ × ℝ)),
      |0.66 * (mixFactor row.2.2.1 row.1 / mixFactor row.2.2.1 row.2.1) - row.2.2.2| < 0.005 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  norm_num [mixFactor, abs_lt]

/-- Table 5.8, row 1 (`p₀ = 0.5`, `p₁ = 0.1`, `HR_CD = 3`): the formula with the printed
observed hazard ratio `0.66` gives exactly `1.10`; the printed value is `1.11`. -/
theorem table_5_8_row_1 : 0.66 * (mixFactor 3 0.5 / mixFactor 3 0.1) = (1.1 : ℝ) := by
  unfold mixFactor; norm_num

/-- The E-value of `RR_obs = 2` is `2 + sqrt 2 ≈ 3.41` (Equation 5.13). -/
theorem eValue_two : RoundsTo (eValue 2) 3.41 0.005 := by
  unfold RoundsTo
  rw [eValue_of_one_le (by norm_num)]
  have h : (2 : ℝ) * (2 - 1) = 2 := by norm_num
  rw [h]
  constructor
  · have : (1.41 : ℝ) < Real.sqrt 2 := by
      rw [Real.lt_sqrt (by norm_num)]; norm_num
    linarith
  · have : Real.sqrt 2 < 1.415 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num
    linarith

/-- G-values for `RR_obs = 2`: `G(0.5) = 2.5 + sqrt 4.25 ≈ 4.56` (printed `4.6`) and
`G(0.25) = (1.75 + sqrt 2.5625) / 0.5 ≈ 6.70` (printed `6.7`). -/
theorem gValue_examples :
    (4.56 < gValue 2 0.5 ∧ gValue 2 0.5 < 4.57) ∧ (6.7 < gValue 2 0.25 ∧ gValue 2 0.25 < 6.72) := by
  unfold gValue gCoeff
  have e1 : ((2 : ℝ) + 0.5 + 2 * 0.5 - 1) ^ 2 - 4 * 2 * 0.5 ^ 2 = 4.25 := by norm_num
  have e2 : ((2 : ℝ) + 0.25 + 2 * 0.25 - 1) ^ 2 - 4 * 2 * 0.25 ^ 2 = 2.5625 := by norm_num
  rw [e1, e2]
  have s1 : (2.06 : ℝ) < Real.sqrt 4.25 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have s2 : Real.sqrt 4.25 < 2.07 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have s3 : (1.6 : ℝ) < Real.sqrt 2.5625 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have s4 : Real.sqrt 2.5625 < 1.61 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith

/-- The E-value of a protective estimate: `eValue (1 / 2) = 2 + sqrt 2`, the E-value of
`RR = 2` (the protective case of VanderWeele and Ding 2017). -/
theorem eValue_half : eValue (1 / 2) = 2 + Real.sqrt 2 := by
  rw [eValue_of_le_one (by norm_num) (by norm_num)]
  norm_num

/-- The text after Equation 5.12 (page 133): a factor with `RR_EC = 6` and `RR_CD = 4` is not
ruled out by the isopleth `p₁ = 1`, but cannot explain `RR_obs = 2` if `p₁ = 0.25`. Along
`p₀ = p₁ / 6` the bias factor is `8/3` at `p₁ = 1`, so it exceeds the observed `2` and the
adjusted risk ratio would be `2 / (8/3) = 3/4`, beyond the null; at `p₁ = 1/4` it is
`14/9 < 2`. -/
theorem winkelstein_example :
    biasFactor 4 1 (1 / 6) = 8 / 3 ∧ 2 / biasFactor 4 1 (1 / 6) = 3 / 4 ∧
      biasFactor 4 (1 / 4) (1 / 4 / 6) = 14 / 9 := by
  unfold biasFactor mixFactor; norm_num

/-- An exact explain away instance with the strengths of `winkelstein_example` (not printed in
the book; it is where the `p₁ = 0.5` isopleth of Figure 5.7 passes through `RR_EC = 6`): at
`p₁ = 1/2`, `p₀ = 1/12` the bias factor is exactly `2`, so `RR_adj = 1`, and `rr = 4` is the
solution of Equation 5.11. -/
theorem winkelstein_exact :
    biasFactor 4 (1 / 2) (1 / 2 / 6) = 2 ∧
      (6 - 6 * (1 / 2) - 6 * 2 + 2 * (1 / 2)) / (1 / 2 * (2 - 6)) = (4 : ℝ) := by
  unfold biasFactor mixFactor; norm_num

/-- An inadmissible solution of Equation 5.12: for `RR_obs = 2` and `RR_EC = 1.5 < RR_obs`, the
required confounder to disease risk ratio is `(2 - 1.5 · 2) / (2 - 1.5) = -2`
(`explainAway_sol_nonpos`). -/
theorem explainAway_inadmissible : ((2 : ℝ) - 3 / 2 * 2) / (2 - 3 / 2) = -2 := by norm_num

/-- Table 12.5 (Chapter 12): projecting the misclassification and selection adjusted table of
Table 12.4 (cases `262.6`, `928.1`; controls `220.7`, `1128.7`) onto physical activity with
`OR_CD = 0.8` and control prevalences `0.299` (ever users) and `0.436` (never users) gives the
case cells `66.8` and `354.6` and the common stratum odds ratio `1.40` (exactly `1.40486`). -/
theorem table_12_5 :
    (66.8 < splitCases 0.8 (220.7 * 0.299) 220.7 262.6 ∧
      splitCases 0.8 (220.7 * 0.299) 220.7 262.6 < 66.85) ∧
    (354.6 < splitCases 0.8 (1128.7 * 0.436) 1128.7 928.1 ∧
      splitCases 0.8 (1128.7 * 0.436) 1128.7 928.1 < 354.65) ∧
    RoundsTo ((262.6 / 220.7) / (928.1 / 1128.7) * (mixFactor 0.8 0.436 / mixFactor 0.8 0.299))
      1.40 0.005 := by
  unfold splitCases mixFactor RoundsTo; norm_num

end Examples

end ExternalAdjustment

end BiasAnalysis

end CausalInference
