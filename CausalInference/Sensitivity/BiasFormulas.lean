/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Bias formulas for unmeasured confounding

Population-level, finite and algebraic sensitivity analysis for a binary treatment `A` and a
binary unmeasured confounder `U`. The data are summarized by the stratum means
`m a u = E[Y | A = a, U = u]` (or the stratum risks `R u = P(Y = 1 | A = a, U = u)`) and the
prevalences `π a = P(U = 1 | A = a)`. By the law of total expectation the observed mean in arm
`a` is `π a * m a true + (1 - π a) * m a false`. If `U` suffices for confounding control, the
causal contrast is the `U`-standardized difference
`∑ u, P(U = u) * (m true u - m false u)`, written with `r = P(U = 1)`.

## Main results

* `unadjustedBias_eq`: the general bias formula of VanderWeele and Arah for the unadjusted
  difference in means, `γ₁ (π₁ - r) - γ₀ (π₀ - r)` with `γ_a = m a 1 - m a 0`.
* `unadjustedBias_eq_of_no_interaction`: with no `A`-`U` interaction on the additive scale
  (`γ₁ = γ₀ = γ`), the bias is `γ * (π₁ - π₀)`.
* `cornfield_prevalence`: Cornfield's condition. If treatment has no effect within levels of `U`,
  `U` is coded as a risk factor, and the observed risk ratio exceeds one, then the prevalence
  ratio `π₁ / π₀` is at least the observed risk ratio. `cornfield_prevalence_coding_needed` shows
  that the coding hypothesis cannot be dropped, and `cornfield_prevalence_max` gives the
  coding-free form.
* `cornfield_riskRatio`: under the same null, the risk ratio of `U` for the outcome is at least
  the observed risk ratio.
* `jointBoundingFactor_null`: the Ding and VanderWeele joint bounding factor under the null of no
  effect within levels of `U`: the observed risk ratio is at most
  `boundingFactor RR_UD RR_EU = RR_UD * RR_EU / (RR_UD + RR_EU - 1)`;
  `jointBoundingFactor_null_max` is the coding-free form.
* `evalue_le_max`: the E-value inequality `RR + sqrt (RR * (RR - 1)) ≤ max a b` whenever
  `RR ≤ boundingFactor a b`.
* `ratio_le_boundingFactor`, `ratio_le_boundingFactor_max`: away from the null, the observed risk
  ratio divided by the `U`-standardized risk ratio is at most `boundingFactor K L`.

The probability space versions of `observedMean`, `standardizedEffect` and `observedRisk`, and
the causal reading of the standardized effect, are in `CausalInference.Sensitivity.Probability`.

## References

* J. Cornfield, W. Haenszel, E. C. Hammond, A. M. Lilienfeld, M. B. Shimkin, E. L. Wynder,
  *Smoking and lung cancer: recent evidence and a discussion of some questions*, Journal of the
  National Cancer Institute (1959).
* T. J. VanderWeele and O. A. Arah, *Bias formulas for sensitivity analysis of unmeasured
  confounding for general outcomes, treatments, and confounders*, Epidemiology (2011).
* P. Ding and T. J. VanderWeele, *Sensitivity analysis without assumptions*, Epidemiology (2016).
* T. J. VanderWeele and P. Ding, *Sensitivity analysis in observational research: introducing the
  E-value*, Annals of Internal Medicine (2017).
-/

@[expose] public section

namespace CausalInference

namespace BiasFormulas

/-- The observed mean `E[Y | A = a] = π a * m a true + (1 - π a) * m a false`, by the law of total
expectation over the binary confounder `U`, where `m a u = E[Y | A = a, U = u]` and
`π a = P(U = 1 | A = a)`. -/
def observedMean (m : Bool → Bool → ℝ) (π : Bool → ℝ) (a : Bool) : ℝ :=
  π a * m a true + (1 - π a) * m a false

/-- The `U`-standardized treatment effect
`r * (m true true - m false true) + (1 - r) * (m true false - m false false)` with reference
prevalence `r = P(U = 1)`. When `U` suffices for confounding control this is the average causal
effect `E[Y^1] - E[Y^0]`. -/
def standardizedEffect (m : Bool → Bool → ℝ) (r : ℝ) : ℝ :=
  r * (m true true - m false true) + (1 - r) * (m true false - m false false)

/-- The bias of the unadjusted difference in observed means relative to the standardized effect. -/
def unadjustedBias (m : Bool → Bool → ℝ) (π : Bool → ℝ) (r : ℝ) : ℝ :=
  (observedMean m π true - observedMean m π false) - standardizedEffect m r

/-- General bias formula (VanderWeele and Arah 2011, binary `U`): the bias of the unadjusted
difference in means equals
`(m 1 1 - m 1 0) (π 1 - r) - (m 0 1 - m 0 0) (π 0 - r)`. The identity holds for every reference
prevalence `r`. -/
theorem unadjustedBias_eq (m : Bool → Bool → ℝ) (π : Bool → ℝ) (r : ℝ) :
    unadjustedBias m π r =
      (m true true - m true false) * (π true - r) -
        (m false true - m false false) * (π false - r) := by
  unfold unadjustedBias observedMean standardizedEffect
  ring

/-- Simple bias formula (VanderWeele and Arah 2011): if the effect of `U` on the outcome is the same
value `γ` in both treatment arms (no interaction), the bias of the unadjusted difference in means
is `γ * (P(U = 1 | A = 1) - P(U = 1 | A = 0))`, whatever the reference prevalence `r`. -/
theorem unadjustedBias_eq_of_no_interaction {m : Bool → Bool → ℝ} {γ : ℝ}
    (h₁ : m true true - m true false = γ) (h₀ : m false true - m false false = γ)
    (π : Bool → ℝ) (r : ℝ) :
    unadjustedBias m π r = γ * (π true - π false) := by
  rw [unadjustedBias_eq, h₁, h₀]
  ring

/-- The observed risk `P(Y = 1 | A = a) = π a * R true + (1 - π a) * R false` under the null of no
treatment effect within levels of `U`: `R u = P(Y = 1 | A = a, U = u)` does not depend on `a`. -/
def observedRisk (R : Bool → ℝ) (π : Bool → ℝ) (a : Bool) : ℝ :=
  π a * R true + (1 - π a) * R false

/-- Cornfield's condition for the prevalence ratio. Assume no effect of treatment within levels of
`U`, that `U` is coded as a risk factor (`0 ≤ R false ≤ R true`), `P(U = 1 | A = 0) > 0`, and a
positive observed risk in the untreated arm. If the observed risk ratio exceeds one, then
`P(U = 1 | A = 1) / P(U = 1 | A = 0)` is at least the observed risk ratio. -/
theorem cornfield_prevalence {R π : Bool → ℝ} (hR₀ : 0 ≤ R false) (hR : R false ≤ R true)
    (hπ₀ : 0 < π false) (hobs₀ : 0 < observedRisk R π false)
    (hRR : 1 < observedRisk R π true / observedRisk R π false) :
    observedRisk R π true / observedRisk R π false ≤ π true / π false := by
  rw [one_lt_div hobs₀] at hRR
  rw [div_le_div_iff₀ hobs₀ hπ₀]
  unfold observedRisk at *
  have hle : π false ≤ π true := by
    by_contra h
    rw [not_le] at h
    nlinarith [mul_nonneg (sub_nonneg.2 h.le) (sub_nonneg.2 hR)]
  nlinarith [mul_nonneg hR₀ (sub_nonneg.2 hle)]

/-- Cornfield's condition for the confounder-outcome risk ratio. Under the null of no effect within
levels of `U`, with `0 < R false ≤ R true` and prevalences `0 ≤ π false`, `π true ≤ 1`, the risk
ratio `R true / R false` of `U` for the outcome is at least the observed risk ratio. -/
theorem cornfield_riskRatio {R π : Bool → ℝ} (hR₀ : 0 < R false) (hR : R false ≤ R true)
    (hπ₀ : 0 ≤ π false) (hπ₁ : π true ≤ 1) :
    observedRisk R π true / observedRisk R π false ≤ R true / R false := by
  have hobs : R false ≤ observedRisk R π false := by
    unfold observedRisk
    nlinarith
  have hobs₁ : observedRisk R π true ≤ R true := by
    unfold observedRisk
    nlinarith
  rw [div_le_div_iff₀ (by linarith) hR₀]
  nlinarith [mul_le_mul_of_nonneg_right hobs₁ hR₀.le,
    mul_le_mul_of_nonneg_left hobs (by linarith : 0 ≤ R true)]

/-- Recoding the confounder (`U ↦ 1 - U`) leaves the observed risks unchanged. -/
theorem observedRisk_recode (R π : Bool → ℝ) (a : Bool) :
    observedRisk (fun u => R (!u)) (fun a => 1 - π a) a = observedRisk R π a := by
  unfold observedRisk
  simp only [Bool.not_true, Bool.not_false]
  ring

/-- Coding-free Cornfield condition: under the null of no effect within levels of `U`, with
`0 < P(U = 1 | A = 0) < 1` and observed risk ratio above one, the larger of the prevalence ratios
of `U = 1` and of `U = 0` is at least the observed risk ratio. -/
theorem cornfield_prevalence_max {R π : Bool → ℝ} (hR₀ : 0 ≤ R false) (hR₁ : 0 ≤ R true)
    (hπ₀ : 0 < π false) (hπ₀' : π false < 1) (hobs₀ : 0 < observedRisk R π false)
    (hRR : 1 < observedRisk R π true / observedRisk R π false) :
    observedRisk R π true / observedRisk R π false ≤
      max (π true / π false) ((1 - π true) / (1 - π false)) := by
  rcases le_total (R false) (R true) with h | h
  · exact le_max_of_le_left (cornfield_prevalence hR₀ h hπ₀ hobs₀ hRR)
  · refine le_max_of_le_right ?_
    have key := cornfield_prevalence (R := fun u => R (!u)) (π := fun a => 1 - π a) hR₁ h
      (by simpa using hπ₀') (by rwa [observedRisk_recode])
      (by rwa [observedRisk_recode, observedRisk_recode])
    rwa [observedRisk_recode, observedRisk_recode] at key

/-- The coding hypothesis `R false ≤ R true` cannot be dropped from `cornfield_prevalence`: with
`R = (1, 0)` and prevalences `π = (1/2, 1/4)` (untreated, treated) the observed risk ratio is
`3/2 > 1`, yet the prevalence ratio is `1/2`. -/
theorem cornfield_prevalence_coding_needed :
    ∃ R π : Bool → ℝ, 0 ≤ R true ∧ 0 ≤ R false ∧ 0 < π false ∧ π false < 1 ∧ 0 < π true ∧
      π true < 1 ∧ 0 < observedRisk R π false ∧
      1 < observedRisk R π true / observedRisk R π false ∧
      π true / π false < observedRisk R π true / observedRisk R π false := by
  refine ⟨fun u => if u then 0 else 1, fun a => if a then 1 / 4 else 1 / 2, ?_⟩
  simp only [observedRisk]
  norm_num

/-! ### The joint bounding factor -/

/-- The joint bounding factor `a * b / (a + b - 1)` of Ding and VanderWeele (2016) for two
risk ratio parameters `a` and `b`. -/
noncomputable def boundingFactor (a b : ℝ) : ℝ := a * b / (a + b - 1)

/-- The bounding factor is symmetric. -/
theorem boundingFactor_comm (a b : ℝ) : boundingFactor a b = boundingFactor b a := by
  unfold boundingFactor
  ring_nf

/-- For `a, b ≥ 1` the bounding factor is at least one. -/
theorem one_le_boundingFactor {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ boundingFactor a b := by
  unfold boundingFactor
  rw [le_div_iff₀ (by linarith)]
  nlinarith [mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 hb)]

/-- For `b ≥ 1` the bounding factor is nondecreasing in its first argument on `[1, ∞)`. -/
theorem boundingFactor_mono_left {a a' b : ℝ} (ha : 1 ≤ a) (hle : a ≤ a') (hb : 1 ≤ b) :
    boundingFactor a b ≤ boundingFactor a' b := by
  unfold boundingFactor
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hle) (sub_nonneg.2 hb)) (by linarith : 0 ≤ b)]

/-- The bounding factor is nondecreasing in both arguments on `[1, ∞) × [1, ∞)`. -/
theorem boundingFactor_mono {a a' b b' : ℝ} (ha : 1 ≤ a) (hle : a ≤ a') (hb : 1 ≤ b)
    (hle' : b ≤ b') : boundingFactor a b ≤ boundingFactor a' b' := by
  refine (boundingFactor_mono_left ha hle hb).trans ?_
  rw [boundingFactor_comm a', boundingFactor_comm a']
  exact boundingFactor_mono_left hb hle' (ha.trans hle)

/-- The joint bounding factor of Ding and VanderWeele (2016) for a binary confounder, under the
null of no treatment effect within levels of `U` (true risk ratio one). With `U` coded as a risk
factor (`0 < R false ≤ R true`) and more prevalent among the treated
(`0 < π false ≤ π true ≤ 1`), write `RR_UD = R true / R false` and
`RR_EU = π true / π false`. Then the observed risk ratio is at most
`boundingFactor RR_UD RR_EU = RR_UD * RR_EU / (RR_UD + RR_EU - 1)`. -/
theorem jointBoundingFactor_null {R π : Bool → ℝ} (hR₀ : 0 < R false) (hR : R false ≤ R true)
    (hπ₀ : 0 < π false) (hπ : π false ≤ π true) (hπ₁ : π true ≤ 1) :
    observedRisk R π true / observedRisk R π false ≤
      boundingFactor (R true / R false) (π true / π false) := by
  unfold boundingFactor
  have hobs : 0 < observedRisk R π false := by
    unfold observedRisk
    nlinarith
  have hD : 0 < R true * π false + π true * R false - R false * π false := by nlinarith
  have e : (R true / R false) * (π true / π false) / (R true / R false + π true / π false - 1) =
      R true * π true / (R true * π false + π true * R false - R false * π false) := by
    field_simp
  rw [e, div_le_div_iff₀ hobs hD]
  unfold observedRisk
  nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hR₀.le (sub_nonneg.2 hR)) (sub_nonneg.2 hπ))
    (sub_nonneg.2 hπ₁)]

/-- The larger of `x / y` and `y / x` is at least one for `x, y > 0`. -/
theorem one_le_max_div {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : 1 ≤ max (x / y) (y / x) := by
  rcases le_total y x with h | h
  · exact le_max_of_le_left ((one_le_div hy).2 h)
  · exact le_max_of_le_right ((one_le_div hx).2 h)

/-- The larger of the prevalence ratios `p₁ / p₀` and `(1 - p₁) / (1 - p₀)` is at least one for
`0 < p₀ < 1`. -/
theorem one_le_max_prevRatio {p₀ p₁ : ℝ} (h₀ : 0 < p₀) (h₀' : p₀ < 1) :
    1 ≤ max (p₁ / p₀) ((1 - p₁) / (1 - p₀)) := by
  rcases le_total p₀ p₁ with h | h
  · exact le_max_of_le_left ((one_le_div h₀).2 h)
  · exact le_max_of_le_right ((one_le_div (by linarith)).2 (by linarith))

/-- Coding-free joint bounding factor under the null of no effect within levels of `U`: for
positive risks `R u` and prevalences `0 < P(U = 1 | A = 0) < 1`, `0 ≤ P(U = 1 | A = 1) ≤ 1`, the
observed risk ratio is at most `boundingFactor RR_UD RR_EU`, where
`RR_UD = max (R true / R false) (R false / R true)` and
`RR_EU = max (π true / π false) ((1 - π true) / (1 - π false))` are maxima over the two codings
of `U`. -/
theorem jointBoundingFactor_null_max {R π : Bool → ℝ} (hR₀ : 0 < R false) (hR₁ : 0 < R true)
    (hπ₀ : 0 < π false) (hπ₀' : π false < 1) (hπ₁ : 0 ≤ π true) (hπ₁' : π true ≤ 1) :
    observedRisk R π true / observedRisk R π false ≤
      boundingFactor (max (R true / R false) (R false / R true))
        (max (π true / π false) ((1 - π true) / (1 - π false))) := by
  have hU := one_le_max_div hR₁ hR₀
  have hE := one_le_max_prevRatio (p₁ := π true) hπ₀ hπ₀'
  have hobs₀ : 0 < observedRisk R π false := by unfold observedRisk; nlinarith
  rcases le_total (R false) (R true) with hR | hR <;>
    rcases le_total (π false) (π true) with hπ | hπ
  · refine (jointBoundingFactor_null hR₀ hR hπ₀ hπ hπ₁').trans ?_
    exact boundingFactor_mono ((one_le_div hR₀).2 hR) (le_max_left _ _)
      ((one_le_div hπ₀).2 hπ) (le_max_left _ _)
  · refine le_trans ?_ (one_le_boundingFactor hU hE)
    rw [div_le_one hobs₀]
    unfold observedRisk
    nlinarith [mul_nonneg (sub_nonneg.2 hπ) (sub_nonneg.2 hR)]
  · refine le_trans ?_ (one_le_boundingFactor hU hE)
    rw [div_le_one hobs₀]
    unfold observedRisk
    nlinarith [mul_nonneg (sub_nonneg.2 hπ) (sub_nonneg.2 hR)]
  · have key := jointBoundingFactor_null (R := fun u => R (!u)) (π := fun a => 1 - π a) hR₁ hR
      (by show 0 < 1 - π false; linarith) (by show 1 - π false ≤ 1 - π true; linarith)
      (by show 1 - π true ≤ 1; linarith)
    rw [observedRisk_recode, observedRisk_recode] at key
    refine key.trans ?_
    simp only [Bool.not_true, Bool.not_false]
    exact boundingFactor_mono ((one_le_div hR₁).2 hR) (le_max_right _ _)
      ((one_le_div (by linarith)).2 (by linarith)) (le_max_right _ _)

/-- The E-value inequality. If `1 < RR`, `1 ≤ a`, `1 ≤ b`, and `RR ≤ boundingFactor a b`, then
`RR + sqrt (RR * (RR - 1)) ≤ max a b`. Read contrapositively: an unmeasured confounder whose two
risk ratio parameters both stay below the E-value `RR + sqrt (RR * (RR - 1))` cannot explain away
an observed risk ratio `RR` (VanderWeele and Ding 2017). -/
theorem evalue_le_max {RR a b : ℝ} (hRR : 1 < RR) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : RR ≤ boundingFactor a b) : RR + Real.sqrt (RR * (RR - 1)) ≤ max a b := by
  set M := max a b with hM
  have hM1 : 1 ≤ M := ha.trans (le_max_left _ _)
  have hbf : RR ≤ boundingFactor M M :=
    h.trans (boundingFactor_mono ha (le_max_left _ _) hb (le_max_right _ _))
  have hq : RR * (2 * M - 1) ≤ M ^ 2 := by
    unfold boundingFactor at hbf
    rw [le_div_iff₀ (by linarith)] at hbf
    nlinarith
  have hsq : RR * (RR - 1) ≤ (M - RR) ^ 2 := by nlinarith
  have hpos : 0 ≤ RR * (RR - 1) := by nlinarith
  rcases le_total RR M with hle | hle
  · have : Real.sqrt (RR * (RR - 1)) ≤ M - RR := by
      rw [Real.sqrt_le_left (by linarith)]
      exact hsq
    linarith
  · exfalso
    have h1 : Real.sqrt (RR * (RR - 1)) ≤ RR - M := by
      rw [Real.sqrt_le_left (by linarith)]
      nlinarith
    have h2 : RR - 1 < Real.sqrt (RR * (RR - 1)) := by
      rw [Real.lt_sqrt (by linarith)]
      nlinarith
    linarith

/-! ### The bounding factor away from the null -/

/-- The mean in arm `a` standardized to the reference prevalence `r = P(U = 1)`:
`r * m a true + (1 - r) * m a false`. -/
def standardizedMean (m : Bool → Bool → ℝ) (r : ℝ) (a : Bool) : ℝ :=
  r * m a true + (1 - r) * m a false

/-- The standardized effect is the difference of the two standardized means. -/
theorem standardizedEffect_eq_sub (m : Bool → Bool → ℝ) (r : ℝ) :
    standardizedEffect m r = standardizedMean m r true - standardizedMean m r false := by
  unfold standardizedEffect standardizedMean
  ring

/-- A convex combination of two positive numbers is positive. -/
theorem convex_comb_pos {t x y : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) (hx : 0 < x) (hy : 0 < y) :
    0 < t * x + (1 - t) * y := by
  rcases le_or_gt t (1 / 2) with h | h
  · nlinarith [mul_nonneg ht hx.le]
  · nlinarith [mul_nonneg (sub_nonneg.2 ht') hy.le]

/-- The aligned case of `ratio_le_boundingFactor`, where `P(U = 1 | A = 0) ≤ P(U = 1 | A = 1)`. -/
theorem ratio_le_boundingFactor_of_le {m : Bool → Bool → ℝ} {π : Bool → ℝ} {w r K L : ℝ}
    (hm : ∀ a u, 0 < m a u) (hπ₀ : 0 < π false) (hπ₁' : π true ≤ 1)
    (hπ : π false ≤ π true) (hw : 0 ≤ w) (hw' : w ≤ 1) (hr : r = w * π true + (1 - w) * π false)
    (hK : π true ≤ K * π false)
    (hL : ∀ a, m a true ≤ L * m a false ∧ m a false ≤ L * m a true) :
    (observedMean m π true / observedMean m π false) /
      (standardizedMean m r true / standardizedMean m r false) ≤ boundingFactor K L := by
  have h11 := hm true true
  have h10 := hm true false
  have h01 := hm false true
  have h00 := hm false false
  obtain ⟨hL₁, hL₁'⟩ := hL true
  obtain ⟨hL₀, hL₀'⟩ := hL false
  have hL1 : 1 ≤ L := by
    by_contra hlt
    rw [not_le] at hlt
    have hLpos : 0 < L := by
      by_contra hneg
      rw [not_lt] at hneg
      nlinarith
    nlinarith [mul_pos hLpos h10]
  have hrlo : π false ≤ r := by rw [hr]; nlinarith
  have hrhi : r ≤ π true := by rw [hr]; nlinarith
  have hπ₁ : 0 ≤ π true := by linarith
  have hr0 : 0 ≤ r := by linarith
  have hr1 : r ≤ 1 := by linarith
  -- positivity of the observed and standardized means
  have hO1 : 0 < observedMean m π true := convex_comb_pos hπ₁ hπ₁' h11 h10
  have hO0 : 0 < observedMean m π false := convex_comb_pos hπ₀.le (by linarith) h01 h00
  have hS1 : 0 < standardizedMean m r true := convex_comb_pos hr0 hr1 h11 h10
  have hS0 : 0 < standardizedMean m r false := convex_comb_pos hr0 hr1 h01 h00
  -- the reference risks `h f = f L + (1 - f)` of a confounder with risk ratio `L`
  have hh : ∀ f : ℝ, 0 ≤ f → f ≤ 1 → 0 < f * L + (1 - f) * 1 :=
    fun f hf hf' => convex_comb_pos hf hf' (by linarith) one_pos
  have hq := hh r hr0 hr1
  have hp1 := hh (π true) hπ₁ hπ₁'
  have hp0 := hh (π false) hπ₀.le (by linarith)
  -- treated arm: `O₁ / S₁ ≤ h (π true) / h r`
  have step1 : observedMean m π true * (r * L + (1 - r) * 1) ≤
      (π true * L + (1 - π true) * 1) * standardizedMean m r true := by
    unfold observedMean standardizedMean
    nlinarith [mul_nonneg (sub_nonneg.2 hrhi) (sub_nonneg.2 hL₁)]
  -- untreated arm: `S₀ / O₀ ≤ h r / h (π false)`
  have step0 : standardizedMean m r false * (π false * L + (1 - π false) * 1) ≤
      (r * L + (1 - r) * 1) * observedMean m π false := by
    unfold observedMean standardizedMean
    nlinarith [mul_nonneg (sub_nonneg.2 hrlo) (sub_nonneg.2 hL₀)]
  -- combine the two arms
  have hcomb : (observedMean m π true / observedMean m π false) /
      (standardizedMean m r true / standardizedMean m r false) ≤
      (π true * L + (1 - π true) * 1) / (π false * L + (1 - π false) * 1) := by
    rw [div_div_div_eq, div_le_div_iff₀ (mul_pos hO0 hS1) hp0]
    have := mul_le_mul step1 step0 (by positivity) (by positivity)
    have e : observedMean m π true * standardizedMean m r false *
        (π false * L + (1 - π false) * 1) * (r * L + (1 - r) * 1) ≤
        (π true * L + (1 - π true) * 1) * (observedMean m π false *
          standardizedMean m r true) * (r * L + (1 - r) * 1) := by nlinarith
    exact le_of_mul_le_mul_right e hq
  -- the reference ratio is a null case with confounder risks `1` and `L`
  have hnull := jointBoundingFactor_null (R := fun u => if u then L else 1) (π := π)
    one_pos (by simpa using hL1) hπ₀ hπ hπ₁'
  simp only [observedRisk, ite_true, Bool.false_eq_true, ite_false, div_one] at hnull
  refine hcomb.trans (hnull.trans ?_)
  rw [boundingFactor_comm K]
  exact boundingFactor_mono hL1 le_rfl ((one_le_div hπ₀).2 hπ) ((div_le_iff₀ hπ₀).2 hK)

/-- The bounding factor of Ding and VanderWeele (2016) away from the null, for a binary
confounder `U`. Let `m a u = P(Y = 1 | A = a, U = u) > 0` be arm specific risks (no null
hypothesis is assumed), `π a = P(U = 1 | A = a)` with `0 < π false < 1` and
`0 ≤ π true ≤ 1`, and let the reference prevalence be the mixture
`r = w * π true + (1 - w) * π false` with `0 ≤ w ≤ 1` (for instance `r = P(U = 1)` with
`w = P(A = 1)`). If `K` bounds the prevalence ratios of both levels of `U`
(`π true ≤ K * π false`, `1 - π true ≤ K * (1 - π false)`) and `L` bounds the risk ratios of
`U` for the outcome within each arm, in both directions, then the observed risk ratio divided by
the `U`-standardized risk ratio is at most `boundingFactor K L = K L / (K + L - 1)`. -/
theorem ratio_le_boundingFactor {m : Bool → Bool → ℝ} {π : Bool → ℝ} {w r K L : ℝ}
    (hm : ∀ a u, 0 < m a u) (hπ₀ : 0 < π false) (hπ₀' : π false < 1) (hπ₁ : 0 ≤ π true)
    (hπ₁' : π true ≤ 1) (hw : 0 ≤ w) (hw' : w ≤ 1) (hr : r = w * π true + (1 - w) * π false)
    (hK₁ : π true ≤ K * π false) (hK₀ : 1 - π true ≤ K * (1 - π false))
    (hL : ∀ a, m a true ≤ L * m a false ∧ m a false ≤ L * m a true) :
    (observedMean m π true / observedMean m π false) /
      (standardizedMean m r true / standardizedMean m r false) ≤ boundingFactor K L := by
  rcases le_total (π false) (π true) with hπ | hπ
  · exact ratio_le_boundingFactor_of_le hm hπ₀ hπ₁' hπ hw hw' hr hK₁ hL
  · -- recode `U ↦ 1 - U`
    have key := ratio_le_boundingFactor_of_le (m := fun a u => m a (!u)) (π := fun a => 1 - π a)
      (r := 1 - r) (w := w) (K := K) (L := L) (fun a u => hm a _) (by linarith)
      (by linarith) (by linarith) hw hw' (by rw [hr]; ring) hK₀
      (fun a => ⟨(hL a).2, (hL a).1⟩)
    have eO : ∀ a, observedMean (fun a u => m a (!u)) (fun a => 1 - π a) a =
        observedMean m π a := fun a => by
      simp only [observedMean, Bool.not_true, Bool.not_false]; ring
    have eS : ∀ a, standardizedMean (fun a u => m a (!u)) (1 - r) a =
        standardizedMean m r a := fun a => by
      simp only [standardizedMean, Bool.not_true, Bool.not_false]; ring
    simpa only [eO, eS] using key

/-- `ratio_le_boundingFactor` with the parameters of Ding and VanderWeele (2016) written as
maxima: `K = max (π true / π false) ((1 - π true) / (1 - π false))` and `L` the largest within
arm risk ratio of `U` for the outcome, over both arms and both codings of `U`. -/
theorem ratio_le_boundingFactor_max {m : Bool → Bool → ℝ} {π : Bool → ℝ} {w r : ℝ}
    (hm : ∀ a u, 0 < m a u) (hπ₀ : 0 < π false) (hπ₀' : π false < 1) (hπ₁ : 0 ≤ π true)
    (hπ₁' : π true ≤ 1) (hw : 0 ≤ w) (hw' : w ≤ 1) (hr : r = w * π true + (1 - w) * π false) :
    (observedMean m π true / observedMean m π false) /
      (standardizedMean m r true / standardizedMean m r false) ≤
      boundingFactor (max (π true / π false) ((1 - π true) / (1 - π false)))
        (max (max (m true true / m true false) (m true false / m true true))
          (max (m false true / m false false) (m false false / m false true))) := by
  refine ratio_le_boundingFactor hm hπ₀ hπ₀' hπ₁ hπ₁' hw hw' hr ?_ ?_ ?_
  · rw [← div_le_iff₀ hπ₀]; exact le_max_left _ _
  · rw [← div_le_iff₀ (by linarith)]; exact le_max_right _ _
  · intro a
    have hle : max (m a true / m a false) (m a false / m a true) ≤
        max (max (m true true / m true false) (m true false / m true true))
          (max (m false true / m false false) (m false false / m false true)) := by
      cases a
      · exact le_max_right _ _
      · exact le_max_left _ _
    constructor
    · rw [← div_le_iff₀ (hm a false)]; exact (le_max_left _ _).trans hle
    · rw [← div_le_iff₀ (hm a true)]; exact (le_max_right _ _).trans hle

end BiasFormulas

end CausalInference
