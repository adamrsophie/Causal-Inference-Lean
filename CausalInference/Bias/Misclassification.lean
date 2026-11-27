/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Bias.Selection
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic.Positivity

/-!
# Measurement error and misclassification

Finite results on measurement bias for a treatment `A` and an outcome `Y` measured as `A*` and
`Y*`.

## Setting

The true variables have a joint table `p a y`. The measurement process is a kernel
`K a y a' y' = P(A* = a', Y* = y' | A = a, Y = y)`, and the observed table is
`observedTable p K a' y' = ∑ a, ∑ y, p a y * K a y a' y'`. The errors are independent and
nondifferential when the kernel is a product `kA a a' * kY y y'`: this is the finite form of
`A* = f(A, U_A)` and `Y* = g(Y, U_Y)` with `U_A`, `U_Y` and `(A, Y)` mutually independent. A
binary variable is classified with sensitivity `se = P(B* = 1 | B = 1)` and specificity
`sp = P(B* = 0 | B = 0)` (`binaryKernel`). Conditional risks are ratios of table entries
(`risk`), with the needed positivity hypotheses.

## Main results

* `observed_indep_of_indep`: the null is preserved under independent nondifferential error. If
  `A ⫫ Y` then `A* ⫫ Y*` (What If, Fine Point 9.1).
* `differentialExample_not_indep`: differential error of the treatment (recall bias) creates an
  association under the null.
* `dependentExample_not_indep`: dependent but nondifferential errors create an association under
  the null.
* `outcome_risk_eq`, `outcome_riskDiff_eq`: under outcome misclassification that is
  nondifferential with respect to treatment, `P(Y* = 1 | A = a) = (1 - sp) + (se + sp - 1) P(Y = 1
  | A = a)`, so the observed risk difference is the true one times `se + sp - 1`.
  `outcome_riskDiff_toward_null` gives, for `se + sp > 1` and `se, sp ≤ 1`, the same sign and no
  larger magnitude; `outcome_riskDiff_reversed` gives the reversal when `se + sp < 1`.
* `trendExample_reversal`: a three-level treatment with independent nondifferential error whose
  conditional mean `E[A* | A]` is not monotone in `A`: the true risks increase in `A` and the
  covariance of treatment and outcome is positive, while the observed covariance of `A*` and `Y`
  is negative (Fine Point 9.1).
* `prevalence_correction`, `misclassMatrix_det`, `misclassMatrix_correction`: with known `se` and
  `sp` and `se + sp ≠ 1`, the true prevalence is recovered from the observed one, by the scalar
  formula and by inverting the misclassification matrix, whose determinant is `se + sp - 1`.
  `prevalence_not_identified` shows that for `se + sp = 1` the observed prevalence does not
  depend on the true one.

## References

* M. A. Hernán and J. M. Robins, *Causal Inference: What If*, Chapman and Hall/CRC (2020),
  sections 9.1 and 9.2, Technical Point 9.1 and Fine Point 9.1.
* M. Dosemeci, S. Wacholder and J. H. Lubin (1990), cited in What If, Fine Point 9.1, for the
  trend reversal.
The scaling by `se + sp - 1` and the matrix correction are standard results of the
misclassification literature; they are not stated in What If.
-/

@[expose] public section

namespace CausalInference

namespace Bias

open Finset

section General

variable {α β α' β' : Type*}

/-- The observed table of `(A*, Y*)`: the true table `p a y` pushed through the measurement
kernel `K a y a' y' = P(A* = a', Y* = y' | A = a, Y = y)`. -/
def observedTable [Fintype α] [Fintype β] (p : α → β → ℝ) (K : α → β → α' → β' → ℝ)
    (a' : α') (y' : β') : ℝ :=
  ∑ a, ∑ y, p a y * K a y a' y'

/-- Independent nondifferential error preserves the null (What If, Fine Point 9.1). If the true
table is independent (`A ⫫ Y`) with nonzero total mass and the measurement kernel is a product
`kA a a' * kY y y'` (the error of `A*` depends only on `A`, that of `Y*` only on `Y`, and the two
are independent), then the observed table is independent (`A* ⫫ Y*`). -/
theorem observed_indep_of_indep [Fintype α] [Fintype β] [Fintype α'] [Fintype β']
    (p : α → β → ℝ) (hp : TableIndep p) (hT : ∑ a, ∑ y, p a y ≠ 0)
    (kA : α → α' → ℝ) (kY : β → β' → ℝ) :
    TableIndep (observedTable p fun a y a' y' ↦ kA a a' * kY y y') := by
  set T := ∑ a, ∑ y, p a y with hTdef
  have hprod : ∀ a y, p a y = ((∑ y', p a y') / T) * ∑ a', p a' y := by
    intro a y
    rw [div_mul_eq_mul_div, eq_div_iff hT]
    exact hp a y
  have hq : observedTable p (fun a y a' y' ↦ kA a a' * kY y y') =
      fun a' y' ↦ (∑ a, (∑ y₀, p a y₀) / T * kA a a') * ∑ y, (∑ a₀, p a₀ y) * kY y y' := by
    funext a' y'
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun y _ ↦ ?_
    rw [hprod a y]
    ring
  rw [hq]
  exact tableIndep_mul _ _

/-- The kernel of a variable measured without error: `P(B* = b' | B = b) = [b = b']`. -/
def exactKernel [DecidableEq α] (b b' : α) : ℝ := if b = b' then 1 else 0

/-- The risk `P(Y = 1 | A = a) = q a 1 / (q a 1 + q a 0)` of a table `q` of `(A, Y)` with binary
`Y`. Every use carries the hypothesis that the row mass is nonzero. -/
noncomputable def risk (q : α → Bool → ℝ) (a : α) : ℝ := q a true / (q a true + q a false)

end General

section Binary

/-- The classification kernel of a binary variable with sensitivity `se` and specificity `sp`:
`P(B* = 1 | B = 1) = se`, `P(B* = 0 | B = 1) = 1 - se`, `P(B* = 1 | B = 0) = 1 - sp`,
`P(B* = 0 | B = 0) = sp`. -/
def binaryKernel (se sp : ℝ) (b b' : Bool) : ℝ :=
  if b then (if b' then se else 1 - se) else (if b' then 1 - sp else sp)

/-- Each row of the binary classification kernel sums to one. -/
theorem binaryKernel_sum (se sp : ℝ) (b : Bool) : ∑ b', binaryKernel se sp b b' = 1 := by
  cases b <;> simp [binaryKernel]

/-- The risk difference `P(Y = 1 | A = 1) - P(Y = 1 | A = 0)` of a table of `(A, Y)`. -/
noncomputable def riskDiff (q : Bool → Bool → ℝ) : ℝ := risk q true - risk q false

/-- The observed table of `(A, Y*)` when treatment is measured exactly and the outcome is
misclassified with sensitivity `se` and specificity `sp` that do not depend on treatment
(nondifferential outcome misclassification). -/
def outcomeMisclassified (p : Bool → Bool → ℝ) (se sp : ℝ) : Bool → Bool → ℝ :=
  observedTable p fun a y a' y' ↦ exactKernel a a' * binaryKernel se sp y y'

theorem outcomeMisclassified_apply (p : Bool → Bool → ℝ) (se sp : ℝ) (a y' : Bool) :
    outcomeMisclassified p se sp a y' = ∑ y, p a y * binaryKernel se sp y y' := by
  cases a <;> simp [outcomeMisclassified, observedTable, exactKernel]

/-- Under nondifferential outcome misclassification, the observed risk in each treatment arm is
`P(Y* = 1 | A = a) = (1 - sp) + (se + sp - 1) P(Y = 1 | A = a)`. -/
theorem outcome_risk_eq (p : Bool → Bool → ℝ) (se sp : ℝ) (a : Bool)
    (hrow : p a true + p a false ≠ 0) :
    risk (outcomeMisclassified p se sp) a = (1 - sp) + (se + sp - 1) * risk p a := by
  simp only [risk, outcomeMisclassified_apply, Fintype.sum_bool, binaryKernel, ↓reduceIte,
    Bool.false_eq_true]
  have hden : p a true * se + p a false * (1 - sp) + (p a true * (1 - se) + p a false * sp) =
      p a true + p a false := by ring
  rw [hden]
  field_simp
  ring

/-- Under nondifferential outcome misclassification, the observed risk difference is the true
risk difference times `se + sp - 1`. -/
theorem outcome_riskDiff_eq (p : Bool → Bool → ℝ) (se sp : ℝ)
    (h1 : p true true + p true false ≠ 0) (h0 : p false true + p false false ≠ 0) :
    riskDiff (outcomeMisclassified p se sp) = (se + sp - 1) * riskDiff p := by
  simp only [riskDiff, outcome_risk_eq p se sp true h1, outcome_risk_eq p se sp false h0]
  ring

/-- Bias toward the null without reversal. Under nondifferential outcome misclassification with
`se ≤ 1`, `sp ≤ 1` and `se + sp > 1`, the observed risk difference has the same sign as the true
one and no larger absolute value. -/
theorem outcome_riskDiff_toward_null (p : Bool → Bool → ℝ) (se sp : ℝ) (hse : se ≤ 1)
    (hsp : sp ≤ 1) (h : 1 < se + sp)
    (h1 : p true true + p true false ≠ 0) (h0 : p false true + p false false ≠ 0) :
    (0 < riskDiff (outcomeMisclassified p se sp) ↔ 0 < riskDiff p) ∧
      (riskDiff (outcomeMisclassified p se sp) = 0 ↔ riskDiff p = 0) ∧
      |riskDiff (outcomeMisclassified p se sp)| ≤ |riskDiff p| := by
  rw [outcome_riskDiff_eq p se sp h1 h0]
  have hc : 0 < se + sp - 1 := by linarith
  refine ⟨mul_pos_iff_of_pos_left hc, ?_, ?_⟩
  · simp [hc.ne']
  · rw [abs_mul, abs_of_pos hc]
    exact mul_le_of_le_one_left (abs_nonneg _) (by linarith)

/-- When `se + sp < 1` the classification is worse than chance and the observed risk difference
has the opposite sign of the true one: the hypothesis `se + sp > 1` cannot be dropped. -/
theorem outcome_riskDiff_reversed (p : Bool → Bool → ℝ) (se sp : ℝ) (h : se + sp < 1)
    (h1 : p true true + p true false ≠ 0) (h0 : p false true + p false false ≠ 0)
    (hrd : 0 < riskDiff p) :
    riskDiff (outcomeMisclassified p se sp) < 0 := by
  rw [outcome_riskDiff_eq p se sp h1 h0]
  exact mul_neg_of_neg_of_pos (by linarith) hrd

/-- The observed table of `(A*, Y)` when the outcome is measured exactly and treatment is
misclassified with sensitivity `se` and specificity `sp` that do not depend on the outcome
(nondifferential treatment misclassification). -/
def exposureMisclassified (p : Bool → Bool → ℝ) (se sp : ℝ) : Bool → Bool → ℝ :=
  observedTable p fun a y a' y' ↦ binaryKernel se sp a a' * exactKernel y y'

theorem exposureMisclassified_apply (p : Bool → Bool → ℝ) (se sp : ℝ) (a' y : Bool) :
    exposureMisclassified p se sp a' y = ∑ a, p a y * binaryKernel se sp a a' := by
  cases y <;> simp [exposureMisclassified, observedTable, exactKernel]

/-- The positive predictive weight `P(A = 1 | A* = a')` under treatment misclassification, where
`n a = p a 1 + p a 0` is the mass of `A = a`. -/
noncomputable def exposureWeight (p : Bool → Bool → ℝ) (se sp : ℝ) (a' : Bool) : ℝ :=
  (p true true + p true false) * binaryKernel se sp true a' /
    ∑ a, (p a true + p a false) * binaryKernel se sp a a'

/-- Under nondifferential treatment misclassification the observed risk in the stratum
`A* = a'` is the mixture `w P(Y = 1 | A = 1) + (1 - w) P(Y = 1 | A = 0)` with
`w = P(A = 1 | A* = a')`. -/
theorem exposure_risk_eq (p : Bool → Bool → ℝ) (se sp : ℝ) (a' : Bool)
    (h1 : p true true + p true false ≠ 0) (h0 : p false true + p false false ≠ 0)
    (hobs : ∑ a, (p a true + p a false) * binaryKernel se sp a a' ≠ 0) :
    risk (exposureMisclassified p se sp) a' =
      exposureWeight p se sp a' * risk p true +
        (1 - exposureWeight p se sp a') * risk p false := by
  simp only [Fintype.sum_bool] at hobs
  simp only [risk, exposureWeight, exposureMisclassified_apply, Fintype.sum_bool]
  have hden : p true true * binaryKernel se sp true a' + p false true * binaryKernel se sp false a'
      + (p true false * binaryKernel se sp true a' + p false false * binaryKernel se sp false a') =
      (p true true + p true false) * binaryKernel se sp true a' +
        (p false true + p false false) * binaryKernel se sp false a' := by ring
  rw [hden]
  generalize binaryKernel se sp true a' = k1 at *
  generalize binaryKernel se sp false a' = k0 at *
  have hw : 1 - (p true true + p true false) * k1 /
      ((p true true + p true false) * k1 + (p false true + p false false) * k0) =
      (p false true + p false false) * k0 /
        ((p true true + p true false) * k1 + (p false true + p false false) * k0) := by
    rw [eq_div_iff hobs, sub_mul, div_mul_cancel₀ _ hobs]
    ring
  rw [hw, div_mul_div_comm, div_mul_div_comm,
    div_add_div _ _ (mul_ne_zero hobs h1) (mul_ne_zero hobs h0),
    div_eq_div_iff hobs (mul_ne_zero (mul_ne_zero hobs h1) (mul_ne_zero hobs h0))]
  ring

/-- The difference of the predictive weights between the observed strata:
`P(A = 1 | A* = 1) - P(A = 1 | A* = 0) = n1 n0 (se + sp - 1) / (D1 D0)`, where `n a` is the mass
of `A = a` and `D a'` the mass of `A* = a'`. -/
theorem exposureWeight_sub (p : Bool → Bool → ℝ) (se sp : ℝ)
    (hobs1 : ∑ a, (p a true + p a false) * binaryKernel se sp a true ≠ 0)
    (hobs0 : ∑ a, (p a true + p a false) * binaryKernel se sp a false ≠ 0) :
    exposureWeight p se sp true - exposureWeight p se sp false =
      (p true true + p true false) * (p false true + p false false) * (se + sp - 1) /
        ((∑ a, (p a true + p a false) * binaryKernel se sp a true) *
          ∑ a, (p a true + p a false) * binaryKernel se sp a false) := by
  simp only [Fintype.sum_bool] at hobs1 hobs0 ⊢
  simp only [exposureWeight, Fintype.sum_bool]
  rw [div_sub_div _ _ hobs1 hobs0]
  congr 1
  simp only [binaryKernel, ↓reduceIte, Bool.false_eq_true]
  ring

/-- Nondifferential treatment misclassification of a binary treatment biases the risk difference
toward the null without reversing it. If both treatment levels and both observed levels have
positive mass, `se ≤ 1`, `sp ≤ 1` and `se + sp > 1`, then the observed risk difference
`P(Y = 1 | A* = 1) - P(Y = 1 | A* = 0)` equals `c` times the true one for some `0 < c ≤ 1`. -/
theorem exposure_riskDiff_toward_null (p : Bool → Bool → ℝ) (se sp : ℝ)
    (hp : ∀ a y, 0 ≤ p a y) (hse : se ≤ 1) (hsp : sp ≤ 1)
    (h : 1 < se + sp) (h1 : 0 < p true true + p true false)
    (h0 : 0 < p false true + p false false)
    (hobs1 : 0 < ∑ a, (p a true + p a false) * binaryKernel se sp a true)
    (hobs0 : 0 < ∑ a, (p a true + p a false) * binaryKernel se sp a false) :
    ∃ c, 0 < c ∧ c ≤ 1 ∧
      riskDiff (exposureMisclassified p se sp) = c * riskDiff p := by
  refine ⟨exposureWeight p se sp true - exposureWeight p se sp false, ?_, ?_, ?_⟩
  · rw [exposureWeight_sub p se sp hobs1.ne' hobs0.ne']
    have : 0 < se + sp - 1 := by linarith
    positivity
  · have hw0 : 0 ≤ exposureWeight p se sp false := by
      unfold exposureWeight
      have : 0 ≤ binaryKernel se sp true false := by simp [binaryKernel]; linarith
      positivity
    have hw1 : exposureWeight p se sp true ≤ 1 := by
      unfold exposureWeight
      rw [div_le_one hobs1]
      simp only [Fintype.sum_bool]
      have : 0 ≤ binaryKernel se sp false true := by simp [binaryKernel]; linarith
      have := hp false true
      have := hp false false
      nlinarith
    linarith
  · simp only [riskDiff, exposure_risk_eq p se sp true h1.ne' h0.ne' hobs1.ne',
      exposure_risk_eq p se sp false h1.ne' h0.ne' hobs0.ne']
    ring

end Binary

section Counterexamples

/-- The joint table of independent fair binary `A` and `Y`: every cell has mass `1/4`. -/
noncomputable def uniformTable (_ _ : Bool) : ℝ := 1 / 4

/-- The fair table satisfies the null `A ⫫ Y`. -/
theorem uniformTable_indep : TableIndep uniformTable := by
  rw [tableIndep_bool_iff]
  simp [uniformTable]

/-- A kernel `K a y a' y'` is a measurement kernel: nonnegative with every row summing to one. -/
def IsMeasurementKernel (K : Bool → Bool → Bool → Bool → ℝ) : Prop :=
  (∀ a y a' y', 0 ≤ K a y a' y') ∧ ∀ a y, ∑ a', ∑ y', K a y a' y' = 1

/-- Differential treatment error (recall bias, What If section 9.2, Figure 9.4): the outcome is
measured exactly, individuals with `Y = 1` always report `A* = 1`, and individuals with `Y = 0`
report their true treatment. The error of `A*` depends on the true outcome. The errors are
independent, since `Y` has no error. -/
def differentialKernel (a y a' y' : Bool) : ℝ :=
  (if y then (if a' then 1 else 0) else exactKernel a a') * exactKernel y y'

theorem differentialKernel_isMeasurementKernel : IsMeasurementKernel differentialKernel := by
  refine ⟨fun a y a' y' ↦ ?_, fun a y ↦ ?_⟩ <;>
    cases a <;> cases y <;> (try cases a') <;> (try cases y') <;>
    simp [differentialKernel, exactKernel]

/-- Differential error creates an association under the null: with `A ⫫ Y`, the observed
`A*` and `Y` are dependent (`P(A* = 1, Y = 1) = 1/2` while `P(A* = 1) P(Y = 1) = 3/8`). -/
theorem differentialExample_not_indep :
    ¬ TableIndep (observedTable uniformTable differentialKernel) := by
  rw [tableIndep_bool_iff]
  simp [observedTable, uniformTable, differentialKernel, exactKernel]

/-- The numbers of the differential example (the observed table has total mass one):
`P(A* = 1, Y = 1) = 1/2` while `P(A* = 1) P(Y = 1) = 3/4 * 1/2 = 3/8`. -/
theorem differentialExample_values :
    observedTable uniformTable differentialKernel true true = 1 / 2 ∧
      (observedTable uniformTable differentialKernel true true +
          observedTable uniformTable differentialKernel true false) *
        (observedTable uniformTable differentialKernel true true +
          observedTable uniformTable differentialKernel false true) = 3 / 8 := by
  constructor <;> norm_num [observedTable, uniformTable, differentialKernel, exactKernel]

/-- Dependent nondifferential errors (What If section 9.2, Figure 9.3): with probability `1/2`
both variables are recorded correctly, and with probability `1/2` a common error (for example
poor recall) records both as `1`. The error source is independent of `(A, Y)`, so the errors are
nondifferential, but the errors of `A*` and `Y*` are dependent. -/
noncomputable def dependentKernel (a y a' y' : Bool) : ℝ :=
  1 / 2 * (exactKernel a a' * exactKernel y y') + 1 / 2 * (if a' && y' then 1 else 0)

theorem dependentKernel_isMeasurementKernel : IsMeasurementKernel dependentKernel := by
  refine ⟨fun a y a' y' ↦ ?_, fun a y ↦ ?_⟩ <;>
    cases a <;> cases y <;> (try cases a') <;> (try cases y') <;>
    norm_num [dependentKernel, exactKernel]

/-- The dependent kernel is nondifferential: the law of `A*` given `(A, Y)` does not depend on
`Y`, and the law of `Y*` given `(A, Y)` does not depend on `A`. -/
theorem dependentKernel_nondifferential :
    (∀ a y₁ y₂ a', ∑ y', dependentKernel a y₁ a' y' = ∑ y', dependentKernel a y₂ a' y') ∧
      ∀ a₁ a₂ y y', ∑ a', dependentKernel a₁ y a' y' = ∑ a', dependentKernel a₂ y a' y' := by
  refine ⟨fun a y₁ y₂ a' ↦ ?_, fun a₁ a₂ y y' ↦ ?_⟩
  · cases a <;> cases y₁ <;> cases y₂ <;> cases a' <;> norm_num [dependentKernel, exactKernel]
  · cases a₁ <;> cases a₂ <;> cases y <;> cases y' <;> norm_num [dependentKernel, exactKernel]

/-- Dependent errors create an association under the null: with `A ⫫ Y`, the observed `A*` and
`Y*` are dependent (`P(A* = 1, Y* = 1) = 5/8` while `P(A* = 1) P(Y* = 1) = 9/16`). -/
theorem dependentExample_not_indep :
    ¬ TableIndep (observedTable uniformTable dependentKernel) := by
  rw [tableIndep_bool_iff]
  simp [observedTable, uniformTable, dependentKernel, exactKernel]
  norm_num

/-- The numbers of the dependent example (the observed table has total mass one):
`P(A* = 1, Y* = 1) = 5/8` while `P(A* = 1) P(Y* = 1) = 3/4 * 3/4 = 9/16`. -/
theorem dependentExample_values :
    observedTable uniformTable dependentKernel true true = 5 / 8 ∧
      (observedTable uniformTable dependentKernel true true +
          observedTable uniformTable dependentKernel true false) *
        (observedTable uniformTable dependentKernel true true +
          observedTable uniformTable dependentKernel false true) = 9 / 16 := by
  constructor <;> norm_num [observedTable, uniformTable, dependentKernel, exactKernel]

end Counterexamples

section Trend

/-- True risk `P(Y = 1 | A = a) = (a + 1) / 10` for a three-level treatment `A ∈ {0, 1, 2}`. -/
noncomputable def trendRisk (a : Fin 3) : ℝ := ((a : ℕ) + 1) / 10

/-- The true joint table of `(A, Y)`: `A` uniform on three levels and `P(Y = 1 | A) = trendRisk`.
-/
noncomputable def trendTable (a : Fin 3) (y : Bool) : ℝ := 1 / 3 * bern (trendRisk a) y

/-- A nondifferential classification of the three-level treatment, with rows
`P(A* = · | A = 0) = (1/4, 3/4, 0)`, `P(A* = · | A = 1) = (0, 1/4, 3/4)` and
`P(A* = · | A = 2) = (3/4, 0, 1/4)`. -/
noncomputable def trendKernel : Fin 3 → Fin 3 → ℝ :=
  ![![1 / 4, 3 / 4, 0], ![0, 1 / 4, 3 / 4], ![3 / 4, 0, 1 / 4]]

/-- The observed table of `(A*, Y)`: the outcome is measured exactly and the treatment error does
not depend on the outcome (independent nondifferential error). -/
noncomputable def trendObserved : Fin 3 → Bool → ℝ :=
  observedTable trendTable fun a y a' y' ↦ trendKernel a a' * exactKernel y y'

theorem trendKernel_stochastic :
    (∀ a a', 0 ≤ trendKernel a a') ∧ ∀ a, ∑ a', trendKernel a a' = 1 := by
  refine ⟨fun a a' ↦ ?_, fun a ↦ ?_⟩
  · fin_cases a <;> fin_cases a' <;> norm_num [trendKernel]
  · fin_cases a <;> norm_num [trendKernel, Fin.sum_univ_three]

/-- The conditional mean `E[A* | A = a]` is `3/4, 7/4, 1/2` for `a = 0, 1, 2`: it is not
monotone in `a`. -/
theorem trendKernel_mean :
    ∑ a' : Fin 3, ((a' : ℕ) : ℝ) * trendKernel 0 a' = 3 / 4 ∧
      ∑ a' : Fin 3, ((a' : ℕ) : ℝ) * trendKernel 1 a' = 7 / 4 ∧
      ∑ a' : Fin 3, ((a' : ℕ) : ℝ) * trendKernel 2 a' = 1 / 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [trendKernel, Fin.sum_univ_three]

/-- The covariance `E[X Y] - E[X] E[Y]` of the treatment level `X ∈ {0, 1, 2}` and the binary
outcome `Y` under a table `q` of total mass one. -/
def tableCov (q : Fin 3 → Bool → ℝ) : ℝ :=
  ∑ a : Fin 3, ((a : ℕ) : ℝ) * q a true -
    (∑ a : Fin 3, ∑ y, ((a : ℕ) : ℝ) * q a y) * ∑ a, q a true

/-- Both the true and the observed tables have total mass one. -/
theorem trend_total :
    ∑ a, ∑ y, trendTable a y = 1 ∧ ∑ a, ∑ y, trendObserved a y = 1 := by
  constructor <;>
    norm_num [trendObserved, observedTable, trendTable, trendRisk, trendKernel, bern,
      exactKernel, Fin.sum_univ_three, Fintype.sum_bool]

/-- Trend reversal under independent nondifferential error (What If, Fine Point 9.1). The true
risks increase in the treatment level (`1/10 < 1/5 < 3/10`) and the true covariance of
treatment level and outcome is `1/15 > 0`. The observed covariance of `A*` and `Y` is
`-1/120 < 0`: the observed trend has the opposite direction. The observed category risks
`P(Y = 1 | A* = a')` are `1/4, 1/8, 9/40`. -/
theorem trendExample_reversal :
    risk trendTable 0 < risk trendTable 1 ∧ risk trendTable 1 < risk trendTable 2 ∧
      tableCov trendTable = 1 / 15 ∧ tableCov trendObserved = -1 / 120 ∧
      risk trendObserved 0 = 1 / 4 ∧ risk trendObserved 1 = 1 / 8 ∧
      risk trendObserved 2 = 9 / 40 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [risk, tableCov, trendObserved, observedTable, trendTable, trendRisk, trendKernel,
      bern, exactKernel, Fin.sum_univ_three, Fintype.sum_bool]

end Trend

section Correction

open Matrix

/-- The observed prevalence `P(B* = 1)` of a binary variable with true prevalence `π`,
sensitivity `se` and specificity `sp`, by the law of total probability. -/
def observedPrevalence (se sp π : ℝ) : ℝ := ∑ b, bern π b * binaryKernel se sp b true

theorem observedPrevalence_eq (se sp π : ℝ) :
    observedPrevalence se sp π = (1 - sp) + (se + sp - 1) * π := by
  simp only [observedPrevalence, bern, binaryKernel, Fintype.sum_bool, ↓reduceIte,
    Bool.false_eq_true]
  ring

/-- Correction for misclassification: with known `se` and `sp` and `se + sp ≠ 1`, the true
prevalence is recovered from the observed one as
`π = (P(B* = 1) - (1 - sp)) / (se + sp - 1)`. -/
theorem prevalence_correction (se sp π : ℝ) (h : se + sp ≠ 1) :
    π = (observedPrevalence se sp π - (1 - sp)) / (se + sp - 1) := by
  have h' : se + sp - 1 ≠ 0 := sub_ne_zero.mpr h
  rw [observedPrevalence_eq, eq_div_iff h']
  ring

/-- When `se + sp = 1` the observed prevalence is `1 - sp` whatever the true prevalence, so the
true prevalence is not identified and the condition `se + sp ≠ 1` cannot be dropped. -/
theorem prevalence_not_identified (se sp π π' : ℝ) (h : se + sp = 1) :
    observedPrevalence se sp π = observedPrevalence se sp π' := by
  simp only [observedPrevalence_eq, h, sub_self, zero_mul]

/-- The misclassification matrix: rows are the true value (index `0` negative, `1` positive),
columns the observed value, entries `P(B* = j | B = i)`. -/
def misclassMatrix (se sp : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![sp, 1 - sp; 1 - se, se]

/-- The observed distribution is the true distribution times the misclassification matrix; its
positive entry is the observed prevalence. -/
theorem vecMul_misclassMatrix (se sp π : ℝ) :
    (![1 - π, π] ᵥ* misclassMatrix se sp) 1 = observedPrevalence se sp π := by
  simp [misclassMatrix, Matrix.vecMul, dotProduct, Fin.sum_univ_two, observedPrevalence_eq]
  ring

/-- The determinant of the misclassification matrix is `se + sp - 1`. -/
theorem misclassMatrix_det (se sp : ℝ) : (misclassMatrix se sp).det = se + sp - 1 := by
  rw [misclassMatrix, Matrix.det_fin_two_of]
  ring

/-- Matrix correction: when `se + sp ≠ 1` the misclassification matrix is invertible and every
true distribution `v` is recovered from the observed one, `v = (v M) M⁻¹`. -/
theorem misclassMatrix_correction (se sp : ℝ) (h : se + sp ≠ 1) (v : Fin 2 → ℝ) :
    (v ᵥ* misclassMatrix se sp) ᵥ* (misclassMatrix se sp)⁻¹ = v := by
  have hdet : IsUnit (misclassMatrix se sp).det := by
    rw [misclassMatrix_det, isUnit_iff_ne_zero]
    exact sub_ne_zero.mpr h
  rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hdet, Matrix.vecMul_one]

end Correction

end Bias

end CausalInference
