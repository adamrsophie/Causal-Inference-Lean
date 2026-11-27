/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.BiasAnalysis.EcologicalBias
public import CausalInference.BiasAnalysis.BiasedEstimates

/-!
# Within-trial and across-trial treatment by covariate interactions

Individual patient data allow a treatment by covariate interaction to be estimated from two
sources. TSD 3, Section 4.5.1, states that "treatment by covariate interactions can be estimated
exclusively using between-study information when only summary data are available
(meta-regression) and exclusively using within-study (variability) information if IPD are
available", that "both between- and within-study coefficients can be estimated", and that this
"can be achieved by including two covariates: the mean covariate value in that study" and "a
second covariate which is the individual patient response minus the mean value in that study"
(the printed text says "response"; the covariate value is meant). The document gives no model
("Specific modelling details are available elsewhere", its reference 54, Riley and Steyerberg,
2010). The model below is the one formalized here.

## The model

Patient `j` belongs to trial `tr j`, has binary treatment `A j ∈ {0, 1}`, covariate `x j` and
outcome `y j`. The objective `interactionRSS` fits
`α_{tr j} + δ A_j + γ (x_j - x̄_{tr j}) + β_W A_j (x_j - x̄_{tr j}) + β_B A_j x̄_{tr j}`:
* trial intercepts `α_i`, which also absorb any covariate main effect through `x̄_i`;
* a common treatment effect `δ`: trial-specific treatment effects would absorb the column
  `A_j x̄_{tr j}`, and the across coefficient would not be identified;
* a common within-trial prognostic slope `γ`, so that the within coefficient is the difference
  of the pooled within-trial slopes of the two arms; trial-specific prognostic slopes would make
  it a weighted mean of trial-specific differences instead;
* the two interaction columns of the document, with coefficients `β_W` (within) and `β_B`
  (across).

## Identifiable design

`IdentifiableDesign`: binary treatment; covariate balance in every populated cell
(`Balanced`: the mean covariate of each arm of a trial is the trial mean, as randomization gives
in expectation and a design stratified on the covariate gives exactly); within-cell variation of
the covariate in each arm; positive weighted variation of the trial mean covariates, with trial
weights `n_{i0} n_{i1} / (n_{i0} + n_{i1})` (so only trials with both arms count).

## Main results

* `interactionRSS_eq`, `interactionRSS_min`: the objective splits into two within-arm parts, an
  intercept part and a weighted least squares objective of the trial treatment effects on the
  trial mean covariates; the unique least squares coefficients are `β_W = withinInteraction`
  and `β_B = acrossInteraction`.
* (a) `withinInteraction` is the difference of the arm-specific pooled within-trial slopes
  `armWithinSlope`, and `withinInteraction_add_trial`: it is unchanged by trial-level terms
  `g (trial) + h (trial) A`.
* (b) `acrossInteraction` is the weighted regression of the trial treatment effects
  `ȳ_{i1} - ȳ_{i0}` on `x̄_i`; `acrossInteraction_eq_sizeWeighted`: with equal allocation in
  every trial the weights are proportional to trial size.
* (c) `ecological_interaction_example`: in a balanced two-trial design, outcome `A x̄_{trial}`
  gives within interaction `0` and across interaction `1`, and outcome `A x` gives `1` and `1`.
* (d) `interaction_effectModifier`: with a common interaction `β` and a trial-level effect
  modifier `m`, the within coefficient is `β` and the across coefficient is `β` plus the
  weighted least squares slope of `m` on the trial mean covariate.

## Without balance

* `colRSS_isMin_iff`: for any columns `Z`, after the trial intercepts are profiled out, a
  parameter vector minimizes the objective if and only if it solves the normal equations
  `∑_q G_{pq} θ_q = b_p` (`NormalEquations`), with `G_{pq} = ∑_j dZ_p dZ_q` (`gram`) and
  `b_p = ∑_j dZ_p dy` (`gramRhs`), where `d` is the deviation from the trial mean, and every
  populated intercept is the trial mean of the residual.
* `normalEquations_unique`, `profiledInjective_iff_posDef`: the solution is unique when the
  profiled design map is injective, equivalently when the Gram matrix is positive definite.
* `interactionRSS_isMin_iff`: the model above is the case of the four columns
  `interactionColumns`. `gram_interaction_decouple`: under binary treatment and balance the
  Gram matrix decouples, which is the balanced case; the balanced results keep their separate
  proof because it gives the closed forms `withinInteraction` and `acrossInteraction`.
* `unbalanced_interaction_example`: in a design that is identifiable except for balance, the
  least squares within coefficient is `-3/89`, while the cell-centered `withinInteraction` is
  `0`.
* `trialEffectFit_not_identified`: with trial-specific treatment effects, `A x̄_{trial}` lies in
  the span of the trial by treatment columns, so `β_B` is not identified.

## References

* S. Dias, A. J. Sutton, N. J. Welton, A. E. Ades, *NICE DSU Technical Support Document 3:
  Heterogeneity: Subgroups, Meta-Regression, Bias and Bias-Adjustment* (2011, updated 2012),
  Section 4.5.1.
-/

@[expose] public section

open Finset

namespace CausalInference.BiasAnalysis.EcologicalBias

open BiasedEstimates

variable {ι : Type*} [Fintype ι] {k : ℕ}

/-! ### Linear algebra of trial means -/

section DevLemmas

variable {J I : Type*} [Fintype J] [DecidableEq I] {t : J → I}

/-- Trial means are additive. -/
theorem trialMean_add (y z : J → ℝ) (i : I) :
    trialMean t (fun j => y j + z j) i = trialMean t y i + trialMean t z i := by
  unfold trialMean; rw [Finset.sum_add_distrib, add_div]

/-- Trial means are homogeneous. -/
theorem trialMean_mul (c : ℝ) (z : J → ℝ) (i : I) :
    trialMean t (fun j => c * z j) i = c * trialMean t z i := by
  unfold trialMean; rw [← Finset.mul_sum, mul_div_assoc]

/-- The deviations from the trial means have trial mean `0` in every populated trial. -/
theorem trialMean_dev (x : J → ℝ) (j : J) : trialMean t (dev t x) (t j) = 0 := by
  have e : dev t x = fun k => x k + (fun i => -trialMean t x i) (t k) := by
    funext k; simp [dev, sub_eq_add_neg]
  rw [e, trialMean_add, trialMean_trial (fun i => -trialMean t x i) j]
  ring

/-- Deviations are homogeneous. -/
theorem dev_mul (c : ℝ) (z : J → ℝ) : dev t (fun k => c * z k) = fun j => c * dev t z j := by
  funext j; simp only [dev, trialMean_mul]; ring

/-- Deviations of deviations are the deviations. -/
theorem dev_dev (x : J → ℝ) : dev t (dev t x) = dev t x := by
  have e : dev t x = fun k => x k + (fun i => -trialMean t x i) (t k) := by
    funext k; simp [dev, sub_eq_add_neg]
  calc dev t (dev t x) = dev t (fun k => x k + (fun i => -trialMean t x i) (t k)) := by
        rw [← e]
    _ = dev t x := dev_add_trial (tr := t) x (fun i => -trialMean t x i)

/-- The pooled within-trial slope of a trial-level term plus `κ` times the covariate deviations
is `κ`, when the covariate varies within some trial. -/
theorem withinSlope_affine (x : J → ℝ) (hS : ∑ j, dev t x j ^ 2 ≠ 0) (c : I → ℝ) (κ : ℝ) :
    withinSlope t x (fun j => c (t j) + κ * dev t x j) = κ := by
  have e : (fun j => c (t j) + κ * dev t x j) = fun j => κ * dev t x j + c (t j) := by
    funext j; ring
  rw [e, withinSlope_add_trial, withinSlope, dev_mul, dev_dev]
  have : ∑ j, dev t x j * (κ * dev t x j) = κ * ∑ j, dev t x j ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [this]; field_simp

end DevLemmas

/-! ### Arms -/

/-- The trial of a patient of arm `a` (treatment value `A j = a`). -/
def armTr (tr : ι → Fin k) (A : ι → ℝ) (a : ℝ) : {j // A j = a} → Fin k := fun j => tr j

/-- The mean `z̄_{i a}` of a patient-level variable `z` over the patients of arm `a` in trial `i`
(`0` for an empty cell). -/
noncomputable def armMean (tr : ι → Fin k) (A : ι → ℝ) (a : ℝ) (z : ι → ℝ) (i : Fin k) : ℝ :=
  trialMean (armTr tr A a) (fun j => z j) i

/-- The number `n_{i a}` of patients of arm `a` in trial `i`. -/
noncomputable def armSize (tr : ι → Fin k) (A : ι → ℝ) (a : ℝ) (i : Fin k) : ℕ :=
  trialSize (armTr tr A a) i

/-- The weight `n_{i0} n_{i1} / (n_{i0} + n_{i1})` of trial `i` in the across-trial regression:
`0` unless both arms of the trial are populated. -/
noncomputable def cellWeight (tr : ι → Fin k) (A : ι → ℝ) (i : Fin k) : ℝ :=
  (armSize tr A 0 i : ℝ) * armSize tr A 1 i / (armSize tr A 0 i + armSize tr A 1 i)

/-- The observed treatment effect `ȳ_{i1} - ȳ_{i0}` of trial `i`. -/
noncomputable def armEffect (tr : ι → Fin k) (A : ι → ℝ) (y : ι → ℝ) (i : Fin k) : ℝ :=
  armMean tr A 1 y i - armMean tr A 0 y i

/-- The within-trial interaction: the difference of the pooled within-trial covariate slopes of
the treated and the control arm. -/
noncomputable def withinInteraction (tr : ι → Fin k) (A : ι → ℝ) (x y : ι → ℝ) : ℝ :=
  armWithinSlope tr A 1 x y - armWithinSlope tr A 0 x y

/-- The across-trial interaction: the weighted least squares slope of the trial treatment
effects on the trial mean covariates, with weights `cellWeight`. -/
noncomputable def acrossInteraction (tr : ι → Fin k) (A : ι → ℝ) (x y : ι → ℝ) : ℝ :=
  wlsSlope (cellWeight tr A) (trialMean tr x) (armEffect tr A y)

/-- A sum over patients is the sum over the control arm plus the sum over the treated arm, when
the treatment is binary. -/
theorem sum_arms (A : ι → ℝ) (hA : ∀ j, A j = 0 ∨ A j = 1) (f : ι → ℝ) :
    ∑ j, f j = ∑ j : {j // A j = 0}, f j + ∑ j : {j // A j = 1}, f j := by
  rw [← Finset.sum_subtype (univ.filter fun j => A j = 0) (by simp) f,
    ← Finset.sum_subtype (univ.filter fun j => A j = 1) (by simp) f,
    ← Finset.sum_filter_add_sum_filter_not univ (fun j => A j = 0) f]
  congr 1
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext j
  rcases hA j with h | h <;> simp [h]

/-- A sum over the patients of arm `a` in trial `i`, as a sum over all patients. -/
theorem sum_arm_filter (tr : ι → Fin k) (A : ι → ℝ) (a : ℝ) (f : ι → ℝ) (i : Fin k) :
    ∑ j : {j // A j = a} with armTr tr A a j = i, f j =
      ∑ j, if A j = a ∧ tr j = i then f j else 0 := by
  rw [Finset.sum_filter]
  change (∑ j : {j // A j = a}, (fun j => if tr j = i then f j else 0) j.1) = _
  rw [← Finset.sum_subtype (univ.filter fun j => A j = a) (by simp)
    (fun j => if tr j = i then f j else 0), Finset.sum_filter]
  exact Finset.sum_congr rfl fun j _ => by split_ifs <;> simp_all

/-- The size of a cell, as a sum over all patients. -/
theorem armSize_eq (tr : ι → Fin k) (A : ι → ℝ) (a : ℝ) (i : Fin k) :
    (armSize tr A a i : ℝ) = ∑ j, if A j = a ∧ tr j = i then 1 else 0 := by
  rw [armSize, trialSize, Finset.natCast_card_filter, ← sum_arm_filter tr A a (fun _ => 1) i,
    Finset.sum_filter]

/-- `armWithinSlope` is the pooled within-trial slope over the patients of the arm. -/
theorem armWithinSlope_eq (tr : ι → Fin k) (A : ι → ℝ) (a : ℝ) (x y : ι → ℝ) :
    armWithinSlope tr A a x y = withinSlope (armTr tr A a) (fun j => x j) (fun j => y j) := rfl

/-- **Covariate balance.** In every populated cell (trial and arm) the mean covariate equals the
trial mean covariate: `x̄_{i a} = x̄_i`. Randomization gives this in expectation; here it is a
property of the data, as in a design stratified on the covariate. -/
def Balanced (tr : ι → Fin k) (A x : ι → ℝ) : Prop :=
  ∀ j, armMean tr A (A j) x (tr j) = trialMean tr x (tr j)

/-- Under balance, the deviation of a patient from the trial mean is its deviation from the mean
of its cell. -/
theorem dev_arm {tr : ι → Fin k} {A x : ι → ℝ} (hbal : Balanced tr A x) (a : ℝ)
    (j : {j // A j = a}) : dev tr x j = dev (armTr tr A a) (fun j => x j) j := by
  have h := hbal j.1
  rw [j.2] at h
  unfold dev
  rw [← h]
  rfl

/-- In an arm where the outcome is a trial-level term plus `κ` times the covariate deviation, the
arm-specific within-trial slope is `κ`. -/
theorem armWithinSlope_eq_of_affine {tr : ι → Fin k} {A x : ι → ℝ} (hbal : Balanced tr A x)
    (a : ℝ) (hS : ∑ j, dev (armTr tr A a) (fun j => x j) j ^ 2 ≠ 0) {y : ι → ℝ}
    (c : Fin k → ℝ) (κ : ℝ) (hy : ∀ j : {j // A j = a}, y j = c (tr j) + κ * dev tr x j) :
    armWithinSlope tr A a x y = κ := by
  rw [armWithinSlope_eq]
  have e : (fun j : {j // A j = a} => y j) =
      fun j => c (armTr tr A a j) + κ * dev (armTr tr A a) (fun j => x j) j :=
    funext fun j => by rw [hy, dev_arm hbal a j]; rfl
  rw [e]
  exact withinSlope_affine _ hS c κ

/-- In an arm where the outcome is a trial-level term `c` plus `κ` times the covariate deviation,
the cell mean of the outcome in a populated cell is `c i`. -/
theorem armMean_eq_of_affine {tr : ι → Fin k} {A x : ι → ℝ} (hbal : Balanced tr A x)
    (a : ℝ) {y : ι → ℝ} (c : Fin k → ℝ) (κ : ℝ)
    (hy : ∀ j : {j // A j = a}, y j = c (tr j) + κ * dev tr x j) (j : {j // A j = a}) :
    armMean tr A a y (tr j) = c (tr j) := by
  unfold armMean
  have e : (fun j : {j // A j = a} => y j) =
      fun j => c (armTr tr A a j) + κ * dev (armTr tr A a) (fun j => x j) j :=
    funext fun j => by rw [hy, dev_arm hbal a j]; rfl
  rw [e, trialMean_add, trialMean_mul]
  change trialMean (armTr tr A a) (fun j => c (armTr tr A a j)) (armTr tr A a j) +
    κ * trialMean (armTr tr A a) (dev (armTr tr A a) fun j => x j) (armTr tr A a j) = _
  rw [trialMean_trial, trialMean_dev]
  simp [armTr]

/-- **One arm of the objective.** Under balance, the residual sum of squares over arm `a` of a
fit `c (trial) + κ (x - x̄)` is the minimal within-cell part, the within penalty
`(κ - s_a)² S_a`, where `s_a` is the arm-specific within-trial slope and `S_a` the within-cell
variation of the covariate, and the cell part `∑_i n_{i a} (ȳ_{i a} - c_i)²`. -/
theorem arm_rss {tr : ι → Fin k} {A x : ι → ℝ} (hbal : Balanced tr A x) (a : ℝ)
    (hS : ∑ j, dev (armTr tr A a) (fun j => x j) j ^ 2 ≠ 0) (y : ι → ℝ) (c : Fin k → ℝ)
    (κ : ℝ) :
    ∑ j : {j // A j = a}, (y j - c (tr j) - κ * dev tr x j) ^ 2 =
      ∑ j, (dev (armTr tr A a) (fun j => y j) j -
          armWithinSlope tr A a x y * dev (armTr tr A a) (fun j => x j) j) ^ 2 +
        (κ - armWithinSlope tr A a x y) ^ 2 * ∑ j, dev (armTr tr A a) (fun j => x j) j ^ 2 +
        ∑ i, (armSize tr A a i : ℝ) * (armMean tr A a y i - c i) ^ 2 := by
  have e1 : ∑ j : {j // A j = a}, (y j - c (tr j) - κ * dev tr x j) ^ 2 =
      ∑ j : {j // A j = a}, ((fun j => y j) j - κ * dev (armTr tr A a) (fun j => x j) j -
        c (armTr tr A a j)) ^ 2 :=
    Finset.sum_congr rfl fun j _ => by rw [dev_arm hbal a j]; unfold armTr; ring
  rw [e1, sum_sq_split, sum_sq_dev_sub _ _ κ hS,
    sum_comp_trial (tr := armTr tr A a)
      (fun i => (trialMean (armTr tr A a) (fun j => y j) i - c i) ^ 2)]
  rfl

/-- The algebra of one trial: profiling the trial intercept out of the two cell terms. -/
theorem cell_identity {n0 n1 : ℝ} (h0 : 0 ≤ n0) (h1 : 0 ≤ n1) (u v α e : ℝ) :
    n0 * (u - α) ^ 2 + n1 * (v - (α + e)) ^ 2 =
      (n0 + n1) * (α - (n0 * u + n1 * (v - e)) / (n0 + n1)) ^ 2 +
        n0 * n1 / (n0 + n1) * (v - u - e) ^ 2 := by
  by_cases hn : n0 + n1 = 0
  · have e0 : n0 = 0 := by linarith
    have e1 : n1 = 0 := by linarith
    simp [e0, e1]
  · field_simp
    ring

/-! ### The patient-level interaction model -/

/-- **The residual sum of squares of the interaction model.** Patient `j` of trial `tr j` with
treatment `A j ∈ {0, 1}`, covariate `x j` and outcome `y j` is fitted by
`α_{tr j} + δ A_j + γ (x_j - x̄_{tr j}) + β_W A_j (x_j - x̄_{tr j}) + β_B A_j x̄_{tr j}`: trial
intercepts `α`, a common treatment effect `δ`, a common within-trial prognostic slope `γ` of the
covariate (its main effect across trials, the term in `x̄_i`, is absorbed by the intercepts), and
the two interaction columns of TSD 3, Section 4.5.1: treatment times the within-trial centered
covariate, with the within coefficient `β_W`, and treatment times the trial mean, with the
across coefficient `β_B`. -/
noncomputable def interactionRSS (tr : ι → Fin k) (A x y : ι → ℝ) (α : Fin k → ℝ)
    (δ γ βW βB : ℝ) : ℝ :=
  ∑ j, (y j - α (tr j) - δ * A j - γ * dev tr x j - βW * (A j * dev tr x j) -
    βB * (A j * trialMean tr x (tr j))) ^ 2

/-- **An identifiable design** for the two interaction coefficients: a binary treatment,
covariate balance in every populated cell (`Balanced`), within-cell variation of the covariate
in each arm (identifying the two arm-specific prognostic slopes, so the within coefficient), and
positive weighted variation of the trial mean covariates over the trials with both arms
populated (identifying the across coefficient). -/
structure IdentifiableDesign (tr : ι → Fin k) (A x : ι → ℝ) : Prop where
  binary : ∀ j, A j = 0 ∨ A j = 1
  balanced : Balanced tr A x
  within0 : 0 < ∑ j, dev (armTr tr A 0) (fun j => x j) j ^ 2
  within1 : 0 < ∑ j, dev (armTr tr A 1) (fun j => x j) j ^ 2
  across : 0 < wSxx (cellWeight tr A) (trialMean tr x)

/-- The trial weights are nonnegative. -/
theorem cellWeight_nonneg (tr : ι → Fin k) (A : ι → ℝ) (i : Fin k) : 0 ≤ cellWeight tr A i := by
  unfold cellWeight; positivity

/-- Positive weighted variation of the trial mean covariates forces positive total weight. -/
theorem IdentifiableDesign.sum_cellWeight_pos {tr : ι → Fin k} {A x : ι → ℝ}
    (hd : IdentifiableDesign tr A x) : 0 < ∑ i, cellWeight tr A i := by
  rcases (Finset.sum_nonneg fun i _ => cellWeight_nonneg tr A i).lt_or_eq with h | h
  · exact h
  · have h0 : ∀ i, cellWeight tr A i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ => cellWeight_nonneg tr A i).1 h.symm i
        (Finset.mem_univ i)
    have := hd.across
    simp [wSxx, h0] at this

/-- The profiled trial intercept `α*_i`: the least squares intercept of trial `i` given `δ` and
`β_B`. -/
noncomputable def profiledIntercept (tr : ι → Fin k) (A x y : ι → ℝ) (δ βB : ℝ) (i : Fin k) : ℝ :=
  ((armSize tr A 0 i : ℝ) * armMean tr A 0 y i + (armSize tr A 1 i : ℝ) *
    (armMean tr A 1 y i - (δ + βB * trialMean tr x i))) / (armSize tr A 0 i + armSize tr A 1 i)

/-- **Decomposition of the interaction objective.** Under a binary treatment, balance and
within-cell variation in both arms, the objective is the sum of
* the control-arm within part, minimal at `γ = s₀` (the control-arm within-trial slope),
* the treated-arm within part, minimal at `γ + β_W = s₁`,
* the intercept part `∑_i n_i (α_i - α*_i)²`, zero at the profiled intercepts,
* the weighted least squares objective of the trial treatment effects `ȳ_{i1} - ȳ_{i0}` on the
  trial mean covariates with weights `n_{i0} n_{i1} / n_i`, at `(δ, β_B)`. -/
theorem interactionRSS_eq {tr : ι → Fin k} {A x : ι → ℝ} (hA : ∀ j, A j = 0 ∨ A j = 1)
    (hbal : Balanced tr A x) (hS0 : ∑ j, dev (armTr tr A 0) (fun j => x j) j ^ 2 ≠ 0)
    (hS1 : ∑ j, dev (armTr tr A 1) (fun j => x j) j ^ 2 ≠ 0) (y : ι → ℝ) (α : Fin k → ℝ)
    (δ γ βW βB : ℝ) :
    interactionRSS tr A x y α δ γ βW βB =
      (∑ j, (dev (armTr tr A 0) (fun j => y j) j -
          armWithinSlope tr A 0 x y * dev (armTr tr A 0) (fun j => x j) j) ^ 2 +
        (γ - armWithinSlope tr A 0 x y) ^ 2 * ∑ j, dev (armTr tr A 0) (fun j => x j) j ^ 2) +
      (∑ j, (dev (armTr tr A 1) (fun j => y j) j -
          armWithinSlope tr A 1 x y * dev (armTr tr A 1) (fun j => x j) j) ^ 2 +
        (γ + βW - armWithinSlope tr A 1 x y) ^ 2 *
          ∑ j, dev (armTr tr A 1) (fun j => x j) j ^ 2) +
      ∑ i, ((armSize tr A 0 i : ℝ) + armSize tr A 1 i) *
        (α i - profiledIntercept tr A x y δ βB i) ^ 2 +
      wlsRSS (cellWeight tr A) (trialMean tr x) (armEffect tr A y) δ βB := by
  rw [interactionRSS, sum_arms A hA]
  have e0 : ∑ j : {j // A j = 0}, (y j - α (tr j) - δ * A j - γ * dev tr x j -
      βW * (A j * dev tr x j) - βB * (A j * trialMean tr x (tr j))) ^ 2 =
      ∑ j : {j // A j = 0}, (y j - α (tr j) - γ * dev tr x j) ^ 2 :=
    Finset.sum_congr rfl fun j _ => by rw [j.2]; ring
  have e1 : ∑ j : {j // A j = 1}, (y j - α (tr j) - δ * A j - γ * dev tr x j -
      βW * (A j * dev tr x j) - βB * (A j * trialMean tr x (tr j))) ^ 2 =
      ∑ j : {j // A j = 1}, (y j - (fun i => α i + δ + βB * trialMean tr x i) (tr j) -
        (γ + βW) * dev tr x j) ^ 2 :=
    Finset.sum_congr rfl fun j _ => by rw [j.2]; ring
  rw [e0, e1, arm_rss hbal 0 hS0 y α γ,
    arm_rss hbal 1 hS1 y (fun i => α i + δ + βB * trialMean tr x i) (γ + βW)]
  have hcell : ∑ i, (armSize tr A 0 i : ℝ) * (armMean tr A 0 y i - α i) ^ 2 +
      ∑ i, (armSize tr A 1 i : ℝ) *
        (armMean tr A 1 y i - (α i + δ + βB * trialMean tr x i)) ^ 2 =
      ∑ i, ((armSize tr A 0 i : ℝ) + armSize tr A 1 i) *
        (α i - profiledIntercept tr A x y δ βB i) ^ 2 +
      wlsRSS (cellWeight tr A) (trialMean tr x) (armEffect tr A y) δ βB := by
    rw [wlsRSS, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h := cell_identity (Nat.cast_nonneg (armSize tr A 0 i))
      (Nat.cast_nonneg (armSize tr A 1 i)) (armMean tr A 0 y i) (armMean tr A 1 y i) (α i)
      (δ + βB * trialMean tr x i)
    rw [show α i + δ + βB * trialMean tr x i = α i + (δ + βB * trialMean tr x i) by ring, h,
      profiledIntercept, cellWeight, armEffect]
    ring
  linear_combination hcell

/-- **Least squares in the interaction model.** Under an identifiable design, the objective
`interactionRSS` is minimized by the profiled trial intercepts, the across-trial line
`(δ̂, β̂_B) = (wlsIntercept, acrossInteraction)` of the trial treatment effects on the trial mean
covariates, the control-arm within-trial slope `γ̂`, and the within coefficient
`β̂_W = withinInteraction`, the difference of the arm-specific within-trial slopes. The minimizer
is unique in `(δ, γ, β_W, β_B)`. -/
theorem interactionRSS_min {tr : ι → Fin k} {A x : ι → ℝ} (hd : IdentifiableDesign tr A x)
    (y : ι → ℝ) (α : Fin k → ℝ) (δ γ βW βB : ℝ) :
    interactionRSS tr A x y
        (profiledIntercept tr A x y
          (wlsIntercept (cellWeight tr A) (trialMean tr x) (armEffect tr A y))
          (acrossInteraction tr A x y))
        (wlsIntercept (cellWeight tr A) (trialMean tr x) (armEffect tr A y))
        (armWithinSlope tr A 0 x y) (withinInteraction tr A x y) (acrossInteraction tr A x y) ≤
      interactionRSS tr A x y α δ γ βW βB ∧
    (interactionRSS tr A x y α δ γ βW βB = interactionRSS tr A x y
        (profiledIntercept tr A x y
          (wlsIntercept (cellWeight tr A) (trialMean tr x) (armEffect tr A y))
          (acrossInteraction tr A x y))
        (wlsIntercept (cellWeight tr A) (trialMean tr x) (armEffect tr A y))
        (armWithinSlope tr A 0 x y) (withinInteraction tr A x y) (acrossInteraction tr A x y) →
      δ = wlsIntercept (cellWeight tr A) (trialMean tr x) (armEffect tr A y) ∧
        γ = armWithinSlope tr A 0 x y ∧ βW = withinInteraction tr A x y ∧
        βB = acrossInteraction tr A x y) := by
  obtain ⟨hle, huniq⟩ := wlsRSS_le (armEffect tr A y) hd.sum_cellWeight_pos hd.across δ βB
  have hE := interactionRSS_eq hd.binary hd.balanced hd.within0.ne' hd.within1.ne' y
  rw [hE, hE]
  set s0 := armWithinSlope tr A 0 x y
  set s1 := armWithinSlope tr A 1 x y
  set S0 := ∑ j, dev (armTr tr A 0) (fun j => x j) j ^ 2
  set S1 := ∑ j, dev (armTr tr A 1) (fun j => x j) j ^ 2
  have hz : s0 + withinInteraction tr A x y - s1 = 0 := by
    simp only [withinInteraction, s0, s1]; ring
  have hα0 : ∑ i, ((armSize tr A 0 i : ℝ) + armSize tr A 1 i) *
      (profiledIntercept tr A x y
          (wlsIntercept (cellWeight tr A) (trialMean tr x) (armEffect tr A y))
          (acrossInteraction tr A x y) i -
        profiledIntercept tr A x y
          (wlsIntercept (cellWeight tr A) (trialMean tr x) (armEffect tr A y))
          (acrossInteraction tr A x y) i) ^ 2 = 0 := by simp
  have hα : 0 ≤ ∑ i, ((armSize tr A 0 i : ℝ) + armSize tr A 1 i) *
      (α i - profiledIntercept tr A x y δ βB i) ^ 2 :=
    Finset.sum_nonneg fun i _ => by positivity
  have h0 : 0 ≤ (γ - s0) ^ 2 * S0 := mul_nonneg (sq_nonneg _) hd.within0.le
  have h1 : 0 ≤ (γ + βW - s1) ^ 2 * S1 := mul_nonneg (sq_nonneg _) hd.within1.le
  rw [hα0, hz, sub_self]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, add_zero]
  change wlsRSS (cellWeight tr A) (trialMean tr x) (armEffect tr A y)
      (wlsIntercept (cellWeight tr A) (trialMean tr x) (armEffect tr A y))
      (wlsSlope (cellWeight tr A) (trialMean tr x) (armEffect tr A y)) ≤ _ at hle
  refine ⟨by unfold acrossInteraction; linarith, fun h => ?_⟩
  unfold acrossInteraction at h ⊢
  have e0 : (γ - s0) ^ 2 * S0 = 0 := by linarith
  have e1 : (γ + βW - s1) ^ 2 * S1 = 0 := by linarith
  obtain ⟨hδ, hβ⟩ := huniq (by linarith)
  rw [mul_eq_zero, or_iff_left hd.within0.ne', sq_eq_zero_iff, sub_eq_zero] at e0
  rw [mul_eq_zero, or_iff_left hd.within1.ne', sq_eq_zero_iff, sub_eq_zero] at e1
  refine ⟨hδ, e0, ?_, hβ⟩
  simp only [withinInteraction, s0, s1] at e0 e1 ⊢
  linarith

/-- **(a) The within-trial interaction ignores trial-level terms.** Adding trial-specific
intercepts and trial-specific treatment effects `g (trial) + h (trial) * A` to the outcome does
not change `withinInteraction`, the least squares within coefficient of `interactionRSS_min`. -/
theorem withinInteraction_add_trial (tr : ι → Fin k) (A x y : ι → ℝ) (g h : Fin k → ℝ) :
    withinInteraction tr A x (fun j => y j + g (tr j) + h (tr j) * A j) =
      withinInteraction tr A x y :=
  armWithinSlope_sub_add_trial A x y g h

/-! ### Properties of weighted least squares slopes -/

/-- Rescaling the weights by a nonzero constant does not change the weighted slope. -/
theorem wlsSlope_const_mul {m : ℕ} (w x y : Fin m → ℝ) {c : ℝ} (hc : c ≠ 0) :
    wlsSlope (fun i => c * w i) x y = wlsSlope w x y := by
  have hM : ∀ z : Fin m → ℝ, wMean (fun i => c * w i) z = wMean w z := by
    intro z
    unfold wMean
    rw [show ∑ i, c * w i * z i = c * ∑ i, w i * z i by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring,
      ← Finset.mul_sum, mul_div_mul_left _ _ hc]
  unfold wlsSlope wSxx
  rw [hM, hM,
    show ∑ i, c * w i * (x i - wMean w x) * (y i - wMean w y) =
      c * ∑ i, w i * (x i - wMean w x) * (y i - wMean w y) by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring,
    show ∑ i, c * w i * (x i - wMean w x) ^ 2 = c * ∑ i, w i * (x i - wMean w x) ^ 2 by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring,
    mul_div_mul_left _ _ hc]

/-- The weighted slope depends on the outcomes only where the weight is not zero. -/
theorem wlsSlope_congr_support {m : ℕ} (w x : Fin m → ℝ) {y y' : Fin m → ℝ}
    (h : ∀ i, w i ≠ 0 → y i = y' i) : wlsSlope w x y = wlsSlope w x y' := by
  have hy : ∀ i, w i * y i = w i * y' i := fun i => by
    by_cases hw : w i = 0
    · simp [hw]
    · rw [h i hw]
  have hM : wMean w y = wMean w y' := by
    unfold wMean; rw [Finset.sum_congr rfl fun i _ => hy i]
  unfold wlsSlope
  rw [hM]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have := hy i
  linear_combination (x i - wMean w x) * this

/-- The weighted slope of `d + γ x + z` on `x` is `γ` plus the slope of `z`. -/
theorem wlsSlope_affine_add {m : ℕ} {w x : Fin m → ℝ} (hw : ∑ i, w i ≠ 0)
    (hS : wSxx w x ≠ 0) (d γ : ℝ) (z : Fin m → ℝ) :
    wlsSlope w x (fun i => d + γ * x i + z i) = γ + wlsSlope w x z := by
  have hM : wMean w (fun i => d + γ * x i + z i) = d + γ * wMean w x + wMean w z := by
    unfold wMean
    rw [show ∑ i, w i * (d + γ * x i + z i) =
        d * ∑ i, w i + γ * ∑ i, w i * x i + ∑ i, w i * z i by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring]
    field_simp
  unfold wlsSlope
  rw [hM, show ∑ i, w i * (x i - wMean w x) * (d + γ * x i + z i - (d + γ * wMean w x +
      wMean w z)) = γ * wSxx w x + ∑ i, w i * (x i - wMean w x) * (z i - wMean w z) by
    rw [wSxx, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring]
  field_simp

/-! ### The across-trial coefficient -/

/-- A trial with positive weight has patients in both arms. -/
theorem exists_of_cellWeight_ne_zero {tr : ι → Fin k} {A : ι → ℝ} {i : Fin k}
    (h : cellWeight tr A i ≠ 0) (a : ℝ) (ha : a = 0 ∨ a = 1) :
    ∃ j : {j // A j = a}, tr j = i := by
  have hn : armSize tr A a i ≠ 0 := by
    intro h0
    apply h
    rcases ha with rfl | rfl <;> simp [cellWeight, h0]
  obtain ⟨j, hj⟩ := Finset.card_ne_zero.1 hn
  exact ⟨j, (Finset.mem_filter.1 hj).2⟩

/-- The size of a trial is the sum of the sizes of its two arms. -/
theorem trialSize_eq_armSize {tr : ι → Fin k} {A : ι → ℝ} (hA : ∀ j, A j = 0 ∨ A j = 1)
    (i : Fin k) : (trialSize tr i : ℝ) = armSize tr A 0 i + armSize tr A 1 i := by
  rw [trialSize, Finset.natCast_card_filter, armSize_eq, armSize_eq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rcases hA j with h | h <;> by_cases ht : tr j = i <;> simp [h, ht]

/-- **(b) The across coefficient is a weighted regression of trial treatment effects.** It is the
weighted least squares slope of the trial treatment effects `ȳ_{i1} - ȳ_{i0}` on the trial mean
covariates `x̄_i` with weights `n_{i0} n_{i1} / n_i` (by definition, and by
`interactionRSS_min` the least squares across coefficient). With equal allocation in every
trial (`n_{i0} = n_{i1}`) these weights are `n_i / 4`, and the across coefficient is the
regression of the trial treatment effects weighted by trial size. -/
theorem acrossInteraction_eq_sizeWeighted {tr : ι → Fin k} {A : ι → ℝ}
    (hA : ∀ j, A j = 0 ∨ A j = 1) (heq : ∀ i, armSize tr A 0 i = armSize tr A 1 i)
    (x y : ι → ℝ) :
    acrossInteraction tr A x y =
      wlsSlope (fun i => (trialSize tr i : ℝ)) (trialMean tr x) (armEffect tr A y) := by
  have hw : cellWeight tr A = fun i => (1 / 4 : ℝ) * trialSize tr i := by
    funext i
    rw [trialSize_eq_armSize hA, cellWeight, heq i]
    by_cases h0 : (armSize tr A 1 i : ℝ) = 0
    · simp [h0]
    · field_simp; ring
  rw [acrossInteraction, hw, wlsSlope_const_mul _ _ _ (by norm_num)]

/-- **(d) Ecological bias for effect modification.** Let the outcome follow a model with a
common interaction `β` (the same within and across trials) and a trial-level effect modifier
`m`: `y_j = α₀(trial) + δ₀ A_j + γ₀ (x_j - x̄_{tr j}) + β A_j x_j + A_j m(trial)`. Under an
identifiable design the within coefficient is `β`, while the across coefficient is
`β + wlsSlope (weights) x̄ m`: it is biased by the weighted least squares slope of the effect
modifier on the trial mean covariate, `∑ w_i (x̄_i - x̄_w)(m_i - m̄_w) / ∑ w_i (x̄_i - x̄_w)²`,
which is not zero when `m` is correlated with `x̄` across the trials. -/
theorem interaction_effectModifier {tr : ι → Fin k} {A x : ι → ℝ}
    (hd : IdentifiableDesign tr A x) (α₀ : Fin k → ℝ) (δ₀ γ₀ β : ℝ) (m : Fin k → ℝ) :
    let y : ι → ℝ := fun j => α₀ (tr j) + δ₀ * A j + γ₀ * dev tr x j + β * (A j * x j) +
      A j * m (tr j)
    withinInteraction tr A x y = β ∧
      acrossInteraction tr A x y = β + wlsSlope (cellWeight tr A) (trialMean tr x) m := by
  intro y
  have hx : ∀ j, x j = dev tr x j + trialMean tr x (tr j) := fun j => by unfold dev; ring
  set c1 : Fin k → ℝ := fun i => α₀ i + δ₀ + β * trialMean tr x i + m i
  have hy1 : ∀ j : {j // A j = 1}, y j = c1 (tr j) + (γ₀ + β) * dev tr x j := fun j => by
    simp only [y, c1, j.2]; rw [hx j]; ring
  have hy0 : ∀ j : {j // A j = 0}, y j = α₀ (tr j) + γ₀ * dev tr x j := fun j => by
    simp only [y, j.2]; ring
  refine ⟨?_, ?_⟩
  · rw [withinInteraction, armWithinSlope_eq_of_affine hd.balanced 1 hd.within1.ne' c1 _ hy1,
      armWithinSlope_eq_of_affine hd.balanced 0 hd.within0.ne' α₀ _ hy0]
    ring
  · have hE : ∀ i, cellWeight tr A i ≠ 0 →
        armEffect tr A y i = δ₀ + β * trialMean tr x i + m i := by
      intro i hi
      obtain ⟨j1, rfl⟩ := exists_of_cellWeight_ne_zero hi 1 (Or.inr rfl)
      obtain ⟨j0, hj0⟩ := exists_of_cellWeight_ne_zero hi 0 (Or.inl rfl)
      rw [armEffect, armMean_eq_of_affine hd.balanced 1 c1 _ hy1 j1, ← hj0,
        armMean_eq_of_affine hd.balanced 0 α₀ _ hy0 j0, hj0]
      simp only [c1]; ring
    rw [acrossInteraction, wlsSlope_congr_support _ _ hE,
      wlsSlope_affine_add hd.sum_cellWeight_pos.ne' hd.across.ne']

/-! ### A balanced two-trial design -/

/-- A trial mean as a ratio of sums over all patients. -/
theorem trialMean_eq_sum {J I : Type*} [Fintype J] [DecidableEq I] (t : J → I) (z : J → ℝ)
    (i : I) : trialMean t z i =
      (∑ j, if t j = i then z j else 0) / ∑ j, if t j = i then (1 : ℝ) else 0 := by
  rw [trialMean, trialSize, Finset.sum_filter, Finset.natCast_card_filter]

/-- A cell mean as a ratio of sums over all patients. -/
theorem armMean_eq_sum (tr : ι → Fin k) (A : ι → ℝ) (a : ℝ) (z : ι → ℝ) (i : Fin k) :
    armMean tr A a z i = (∑ j, if A j = a ∧ tr j = i then z j else 0) /
      ∑ j, if A j = a ∧ tr j = i then (1 : ℝ) else 0 := by
  rw [armMean, trialMean, sum_arm_filter, ← armSize_eq]
  rfl

/-- The patients of the example: `(trial, treated, high covariate)`, two trials of four
patients, two per arm. -/
abbrev ExPatient := Fin 2 × Bool × Bool

/-- The trial of a patient of the example. -/
def exTr : ExPatient → Fin 2 := fun j => j.1

/-- The treatment of a patient of the example. -/
noncomputable def exA : ExPatient → ℝ := fun j => if j.2.1 then 1 else 0

/-- The covariate of the example: `0, 2` in each arm of trial `0`, `2, 4` in each arm of
trial `1`. -/
noncomputable def exX : ExPatient → ℝ := fun j =>
  (if j.1 = 1 then 2 else 0) + if j.2.2 then 2 else 0

/-- The treatment of the example is binary. -/
theorem exA_binary (j : ExPatient) : exA j = 0 ∨ exA j = 1 := by
  unfold exA; split_ifs <;> simp

/-- The trial mean covariates of the example are `1` and `3`. -/
theorem exX_trialMean (i : Fin 2) : trialMean exTr exX i = if i = 1 then 3 else 1 := by
  rw [trialMean_eq_sum]
  fin_cases i <;> simp [exTr, exX, Fintype.sum_prod_type, Fin.sum_univ_two] <;> norm_num

/-- Every cell of the example has two patients. -/
theorem exCard (b : Bool) (i : Fin 2) :
    (Finset.univ.filter fun x : ExPatient => x.2.1 = b ∧ x.1 = i).card = 2 := by
  revert b i; decide

/-- In both arms the cell mean covariates of the example are `1` and `3`. -/
theorem exX_armMean {a : ℝ} (ha : a = 0 ∨ a = 1) (i : Fin 2) :
    armMean exTr exA a exX i = if i = 1 then 3 else 1 := by
  rw [armMean_eq_sum]
  rcases ha with rfl | rfl <;> fin_cases i <;>
    simp [exTr, exA, exX, Fintype.sum_prod_type, exCard] <;> norm_num

/-- Every cell of the example has two patients (as a real number). -/
theorem exArmSize {a : ℝ} (ha : a = 0 ∨ a = 1) (i : Fin 2) :
    (armSize exTr exA a i : ℝ) = 2 := by
  rw [armSize_eq]
  rcases ha with rfl | rfl <;> fin_cases i <;>
    simp [exTr, exA, exCard]

/-- Both trials of the example have weight `2 · 2 / 4 = 1`. -/
theorem exCellWeight (i : Fin 2) : cellWeight exTr exA i = 1 := by
  rw [cellWeight, exArmSize (Or.inl rfl), exArmSize (Or.inr rfl)]; norm_num

/-- Each arm of the example has within-cell covariate variation: every deviation is `±1`. -/
theorem ex_within {a : ℝ} (ha : a = 0 ∨ a = 1) (j₀ : {j // exA j = a}) :
    0 < ∑ j, dev (armTr exTr exA a) (fun j => exX j) j ^ 2 := by
  have hdev : ∀ j : {j // exA j = a}, dev (armTr exTr exA a) (fun j => exX j) j ^ 2 = 1 := by
    intro j
    change (exX j - armMean exTr exA a exX (exTr j)) ^ 2 = 1
    rw [exX_armMean ha]
    obtain ⟨⟨i, b, c⟩, _⟩ := j
    fin_cases i <;> cases c <;> simp [exX, exTr] <;> norm_num
  exact Finset.sum_pos (fun j _ => by rw [hdev j]; exact one_pos) ⟨j₀, Finset.mem_univ _⟩

/-- **The example design is identifiable**: binary treatment, exact covariate balance, within-cell
variation in both arms, and trial mean covariates `1` and `3` with equal trial weights. -/
theorem exDesign : IdentifiableDesign exTr exA exX where
  binary := exA_binary
  balanced := fun j => by rw [exX_armMean (exA_binary j), exX_trialMean]
  within0 := ex_within (Or.inl rfl) ⟨(0, false, false), by simp [exA]⟩
  within1 := ex_within (Or.inr rfl) ⟨(0, true, false), by simp [exA]⟩
  across := by
    simp only [wSxx, wMean, exCellWeight, exX_trialMean, Fin.sum_univ_two]
    norm_num

/-- **(c) Within and across interactions can differ, or agree.** In the balanced design
`exDesign` (two trials with mean covariates `1` and `3`):
* with outcome `y = A x̄_{trial}` (the treatment effect varies across trials with the trial mean
  covariate, but within each trial not at all with the patient's covariate), the within-trial
  interaction is `0` and the across-trial interaction is `1`: ecological bias for effect
  modification;
* with outcome `y = A x` (the effect varies with the patient's covariate), both are `1`. -/
theorem ecological_interaction_example :
    withinInteraction exTr exA exX (fun j => exA j * trialMean exTr exX (exTr j)) = 0 ∧
      acrossInteraction exTr exA exX (fun j => exA j * trialMean exTr exX (exTr j)) = 1 ∧
      withinInteraction exTr exA exX (fun j => exA j * exX j) = 1 ∧
      acrossInteraction exTr exA exX (fun j => exA j * exX j) = 1 := by
  have hw := exDesign.sum_cellWeight_pos
  have hS := exDesign.across
  obtain ⟨h1w, h1a⟩ := interaction_effectModifier exDesign (fun _ => 0) 0 0 0
    (trialMean exTr exX)
  obtain ⟨h2w, h2a⟩ := interaction_effectModifier exDesign (fun _ => 0) 0 0 1 (fun _ => 0)
  have e1 : (fun j => (fun _ => (0 : ℝ)) (exTr j) + 0 * exA j + 0 * dev exTr exX j +
      0 * (exA j * exX j) + exA j * trialMean exTr exX (exTr j)) =
      fun j => exA j * trialMean exTr exX (exTr j) := by funext j; ring
  have e2 : (fun j => (fun _ => (0 : ℝ)) (exTr j) + 0 * exA j + 0 * dev exTr exX j +
      1 * (exA j * exX j) + exA j * (fun _ => (0 : ℝ)) (exTr j)) =
      fun j => exA j * exX j := by funext j; ring
  have hself : wlsSlope (cellWeight exTr exA) (trialMean exTr exX) (trialMean exTr exX) = 1 := by
    simpa using (wlsIntercept_line hw hS.ne' 0 1).1
  have hzero : wlsSlope (cellWeight exTr exA) (trialMean exTr exX) (fun _ => 0) = 0 := by
    simp [wlsSlope, wMean]
  rw [e1] at h1w h1a
  rw [e2] at h2w h2a
  refine ⟨h1w, ?_, h2w, ?_⟩
  · rw [h1a, hself]; ring
  · rw [h2a, hzero]; ring

/-! ### The interaction model without balance -/

section Unbalanced

variable {m : ℕ}

/-- The residual sum of squares `∑ⱼ (yⱼ - α_{tr j} - ∑ₚ θₚ Zₚⱼ)²` of a linear model with trial
intercepts `α` and columns `Z₀, …, Z_{m-1}` with coefficients `θ`. -/
noncomputable def colRSS (tr : ι → Fin k) (Z : Fin m → ι → ℝ) (y : ι → ℝ) (α : Fin k → ℝ)
    (θ : Fin m → ℝ) : ℝ :=
  ∑ j, (y j - α (tr j) - ∑ p, θ p * Z p j) ^ 2

/-- The outcome minus the column part of the fit, `yⱼ - ∑ₚ θₚ Zₚⱼ`. -/
noncomputable def colResid (Z : Fin m → ι → ℝ) (y : ι → ℝ) (θ : Fin m → ℝ) : ι → ℝ :=
  fun j => y j - ∑ p, θ p * Z p j

/-- The profiled objective: the residual sum of squares of the trial-demeaned outcome on the
trial-demeaned columns, `∑ⱼ (ỹⱼ - ∑ₚ θₚ Z̃ₚⱼ)²`, the minimum over the trial intercepts. -/
noncomputable def profiledRSS (tr : ι → Fin k) (Z : Fin m → ι → ℝ) (y : ι → ℝ)
    (θ : Fin m → ℝ) : ℝ :=
  ∑ j, (dev tr y j - ∑ p, θ p * dev tr (Z p) j) ^ 2

/-- The profiled design Gram matrix `G_{pq} = ∑ⱼ Z̃ₚⱼ Z̃_qⱼ` (columns demeaned within trials). -/
noncomputable def gram (tr : ι → Fin k) (Z : Fin m → ι → ℝ) (p q : Fin m) : ℝ :=
  ∑ j, dev tr (Z p) j * dev tr (Z q) j

/-- The right side `bₚ = ∑ⱼ Z̃ₚⱼ ỹⱼ` of the normal equations. -/
noncomputable def gramRhs (tr : ι → Fin k) (Z : Fin m → ι → ℝ) (y : ι → ℝ) (p : Fin m) : ℝ :=
  ∑ j, dev tr (Z p) j * dev tr y j

/-- The normal equations `G θ = b` of the profiled least squares problem. -/
def NormalEquations (tr : ι → Fin k) (Z : Fin m → ι → ℝ) (y : ι → ℝ) (θ : Fin m → ℝ) : Prop :=
  ∀ p, ∑ q, gram tr Z p q * θ q = gramRhs tr Z y p

/-- Injectivity of the profiled design map `h ↦ (∑ₚ hₚ Z̃ₚⱼ)ⱼ`; equivalent to positive
definiteness of the Gram matrix (`profiledInjective_iff_posDef`). -/
def ProfiledInjective (tr : ι → Fin k) (Z : Fin m → ι → ℝ) : Prop :=
  ∀ h : Fin m → ℝ, (∀ j, ∑ p, h p * dev tr (Z p) j = 0) → h = 0

/-- Trial means of `y - ∑ θₚ Zₚ` are the corresponding combinations of trial means. -/
theorem trialMean_colResid (tr : ι → Fin k) (Z : Fin m → ι → ℝ) (y : ι → ℝ) (θ : Fin m → ℝ)
    (i : Fin k) :
    trialMean tr (colResid Z y θ) i = trialMean tr y i - ∑ p, θ p * trialMean tr (Z p) i := by
  unfold colResid trialMean
  have e : ∑ j with tr j = i, ∑ p, θ p * Z p j = ∑ p, θ p * ∑ j with tr j = i, Z p j := by
    rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun p _ => (Finset.mul_sum _ _ _).symm
  rw [Finset.sum_sub_distrib, e, sub_div]
  congr 1
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun p _ => by rw [mul_div_assoc]

/-- Deviations of `y - ∑ θₚ Zₚ` are the corresponding combinations of deviations. -/
theorem dev_colResid (tr : ι → Fin k) (Z : Fin m → ι → ℝ) (y : ι → ℝ) (θ : Fin m → ℝ)
    (j : ι) : dev tr (colResid Z y θ) j = dev tr y j - ∑ p, θ p * dev tr (Z p) j := by
  have e : dev tr (colResid Z y θ) j =
      colResid Z y θ j - trialMean tr (colResid Z y θ) (tr j) := rfl
  rw [e, trialMean_colResid]
  simp only [colResid, dev, mul_sub, Finset.sum_sub_distrib]
  ring

/-- Products of deviations: `∑ ũ ṽ = ∑ ũ v`. -/
theorem sum_dev_mul_dev (tr : ι → Fin k) (u v : ι → ℝ) :
    ∑ j, dev tr u j * dev tr v j = ∑ j, dev tr u j * v j := by
  have h := sum_dev_mul_trial (tr := tr) u (trialMean tr v)
  rw [show ∑ j, dev tr u j * dev tr v j =
      ∑ j, dev tr u j * v j - ∑ j, dev tr u j * trialMean tr v (tr j) by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by
      rw [show dev tr v j = v j - trialMean tr v (tr j) from rfl]; ring, h, sub_zero]

/-- The defect of the normal equations, `bₚ - (G θ)ₚ = ∑ⱼ Z̃ₚⱼ (ỹⱼ - ∑_q θ_q Z̃_qⱼ)`. -/
theorem gramRhs_sub_gram' (tr : ι → Fin k) (Z : Fin m → ι → ℝ) (y : ι → ℝ) (θ : Fin m → ℝ)
    (p : Fin m) :
    gramRhs tr Z y p - ∑ q, gram tr Z p q * θ q =
      ∑ j, dev tr (Z p) j * (dev tr y j - ∑ q, θ q * dev tr (Z q) j) := by
  simp only [gramRhs, gram, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun q _ => by ring

/-- **The normal equations in residual form.** `bₚ - (G θ)ₚ = ∑ⱼ Zₚⱼ r̃ⱼ`, where `r̃` is the
trial-demeaned residual `dev (y - ∑ θ_q Z_q)` of the fit with coefficients `θ`. -/
theorem gramRhs_sub_gram (tr : ι → Fin k) (Z : Fin m → ι → ℝ) (y : ι → ℝ) (θ : Fin m → ℝ)
    (p : Fin m) :
    gramRhs tr Z y p - ∑ q, gram tr Z p q * θ q =
      ∑ j, Z p j * dev tr (colResid Z y θ) j := by
  rw [gramRhs_sub_gram']
  simp_rw [← dev_colResid]
  rw [show ∑ j, dev tr (Z p) j * dev tr (colResid Z y θ) j =
      ∑ j, dev tr (colResid Z y θ) j * dev tr (Z p) j from
    Finset.sum_congr rfl fun j _ => mul_comm _ _, sum_dev_mul_dev]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- **Expansion of the profiled objective** around `θ`: with `hₚ = θ'ₚ - θₚ`,
`P(θ') = P(θ) - 2 ∑ₚ hₚ (b - G θ)ₚ + ∑ⱼ (∑ₚ hₚ Z̃ₚⱼ)²`. -/
theorem profiledRSS_eq_add (tr : ι → Fin k) (Z : Fin m → ι → ℝ) (y : ι → ℝ)
    (θ θ' : Fin m → ℝ) :
    profiledRSS tr Z y θ' = profiledRSS tr Z y θ -
      2 * ∑ p, (θ' p - θ p) * (gramRhs tr Z y p - ∑ q, gram tr Z p q * θ q) +
      ∑ j, (∑ p, (θ' p - θ p) * dev tr (Z p) j) ^ 2 := by
  have hr : ∀ j, dev tr y j - ∑ p, θ' p * dev tr (Z p) j =
      (dev tr y j - ∑ p, θ p * dev tr (Z p) j) - ∑ p, (θ' p - θ p) * dev tr (Z p) j := by
    intro j
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  have hcross : ∑ j, (dev tr y j - ∑ p, θ p * dev tr (Z p) j) *
      ∑ p, (θ' p - θ p) * dev tr (Z p) j =
      ∑ p, (θ' p - θ p) * (gramRhs tr Z y p - ∑ q, gram tr Z p q * θ q) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [gramRhs_sub_gram', Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  unfold profiledRSS
  rw [Finset.sum_congr rfl fun j _ => by rw [hr j], ← hcross, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The quadratic form of the Gram matrix is the squared norm of the profiled design map. -/
theorem gram_quadratic (tr : ι → Fin k) (Z : Fin m → ι → ℝ) (h : Fin m → ℝ) :
    ∑ p, ∑ q, h p * gram tr Z p q * h q = ∑ j, (∑ p, h p * dev tr (Z p) j) ^ 2 := by
  have e : ∀ j, (∑ p, h p * dev tr (Z p) j) ^ 2 =
      ∑ p, ∑ q, h p * dev tr (Z p) j * (h q * dev tr (Z q) j) := fun j => by
    rw [sq, Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl fun j _ => e j]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [gram, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- Injectivity of the profiled design map is positive definiteness of the Gram matrix. -/
theorem profiledInjective_iff_posDef (tr : ι → Fin k) (Z : Fin m → ι → ℝ) :
    ProfiledInjective tr Z ↔ ∀ h : Fin m → ℝ, h ≠ 0 → 0 < ∑ p, ∑ q, h p * gram tr Z p q * h q := by
  simp only [gram_quadratic]
  constructor
  · intro hinj h hh
    rcases (Finset.sum_nonneg fun j _ => sq_nonneg (∑ p, h p * dev tr (Z p) j)).lt_or_eq with
      hlt | heq
    · exact hlt
    · exact absurd (hinj h fun j => by
        have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg
          (∑ p, h p * dev tr (Z p) j)).1 heq.symm j (Finset.mem_univ j)
        exact pow_eq_zero_iff two_ne_zero |>.1 this) hh
  · intro hpd h hz
    by_contra hh
    have := hpd h hh
    simp [hz] at this

/-- **Solutions of the normal equations minimize the profiled objective.** -/
theorem profiledRSS_le_of_normal {tr : ι → Fin k} {Z : Fin m → ι → ℝ} {y : ι → ℝ}
    {θ : Fin m → ℝ} (hθ : NormalEquations tr Z y θ) (θ' : Fin m → ℝ) :
    profiledRSS tr Z y θ ≤ profiledRSS tr Z y θ' := by
  rw [profiledRSS_eq_add tr Z y θ θ']
  have h0 : ∑ p, (θ' p - θ p) * (gramRhs tr Z y p - ∑ q, gram tr Z p q * θ q) = 0 :=
    Finset.sum_eq_zero fun p _ => by rw [hθ p, sub_self, mul_zero]
  rw [h0]
  linarith [Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) =>
    sq_nonneg (∑ p, (θ' p - θ p) * dev tr (Z p) j)]

/-- **Minimizers of the profiled objective solve the normal equations.** -/
theorem normal_of_profiledRSS_le {tr : ι → Fin k} {Z : Fin m → ι → ℝ} {y : ι → ℝ}
    {θ : Fin m → ℝ} (hmin : ∀ θ', profiledRSS tr Z y θ ≤ profiledRSS tr Z y θ') :
    NormalEquations tr Z y θ := by
  intro p
  set c := gramRhs tr Z y p - ∑ q, gram tr Z p q * θ q with hc
  set g := gram tr Z p p
  have hg : 0 ≤ g := Finset.sum_nonneg fun j _ => mul_self_nonneg _
  have key : ∀ t : ℝ, 0 ≤ -2 * t * c + t ^ 2 * g := by
    intro t
    have := hmin (fun q => θ q + if q = p then t else 0)
    rw [profiledRSS_eq_add tr Z y θ (fun q => θ q + if q = p then t else 0)] at this
    have hs : ∀ f : Fin m → ℝ, ∑ q, (θ q + (if q = p then t else 0) - θ q) * f q = t * f p :=
      fun f => by
        rw [Finset.sum_eq_single p (fun b _ hb => by simp [hb]) (by simp)]
        simp
    simp only [hs] at this
    have e : ∑ j, (t * dev tr (Z p) j) ^ 2 = t ^ 2 * g := by
      simp only [g, gram, Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [e] at this
    linarith
  have h := key (c / (g + 1))
  have hg1 : 0 < g + 1 := by linarith
  have e : (-2 * (c / (g + 1)) * c + (c / (g + 1)) ^ 2 * g) * (g + 1) ^ 2 = -c ^ 2 * (g + 2) := by
    field_simp; ring
  have h2 : 0 ≤ -c ^ 2 * (g + 2) := by rw [← e]; positivity
  have hc0 : c ^ 2 = 0 := by nlinarith [sq_nonneg c]
  have : c = 0 := pow_eq_zero_iff two_ne_zero |>.1 hc0
  linarith

/-- **Uniqueness.** If the profiled design map is injective, a solution of the normal equations
is the unique minimizer of the profiled objective. -/
theorem eq_of_profiledRSS_eq {tr : ι → Fin k} {Z : Fin m → ι → ℝ} {y : ι → ℝ}
    {θ θ' : Fin m → ℝ} (hθ : NormalEquations tr Z y θ) (hinj : ProfiledInjective tr Z)
    (h : profiledRSS tr Z y θ' = profiledRSS tr Z y θ) : θ' = θ := by
  rw [profiledRSS_eq_add tr Z y θ θ'] at h
  have h0 : ∑ p, (θ' p - θ p) * (gramRhs tr Z y p - ∑ q, gram tr Z p q * θ q) = 0 :=
    Finset.sum_eq_zero fun p _ => by rw [hθ p, sub_self, mul_zero]
  rw [h0] at h
  have hs : ∑ j, (∑ p, (θ' p - θ p) * dev tr (Z p) j) ^ 2 = 0 := by linarith
  have hd := hinj (fun p => θ' p - θ p) fun j => pow_eq_zero_iff two_ne_zero |>.1
    ((Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg _).1 hs j (Finset.mem_univ j))
  funext p
  have := congrFun hd p
  simp only [Pi.zero_apply, sub_eq_zero] at this
  exact this

/-- **Profiling out the trial intercepts.** The objective is the profiled objective plus
`∑ⱼ (m_{tr j}(θ) - α_{tr j})²`, where `m_i(θ)` is the trial mean of `y - ∑ θₚ Zₚ`. -/
theorem colRSS_eq (tr : ι → Fin k) (Z : Fin m → ι → ℝ) (y : ι → ℝ) (α : Fin k → ℝ)
    (θ : Fin m → ℝ) :
    colRSS tr Z y α θ = profiledRSS tr Z y θ +
      ∑ j, (trialMean tr (colResid Z y θ) (tr j) - α (tr j)) ^ 2 := by
  have h := sum_sq_split (tr := tr) (colResid Z y θ) (colResid Z y θ) 0 α
  simp only [zero_mul, sub_zero] at h
  unfold colRSS profiledRSS
  rw [show ∑ j, (y j - α (tr j) - ∑ p, θ p * Z p j) ^ 2 =
      ∑ j, (colResid Z y θ j - α (tr j)) ^ 2 from
    Finset.sum_congr rfl fun j _ => by simp only [colResid]; ring, h]
  simp only [dev_colResid]

/-- **Least squares without balance: minimizers are the solutions of the normal equations.** A
pair `(α, θ)` minimizes `colRSS` if and only if `θ` solves the normal equations `G θ = b` and
every populated trial intercept is the trial mean of `y - ∑ θₚ Zₚ`. -/
theorem colRSS_isMin_iff (tr : ι → Fin k) (Z : Fin m → ι → ℝ) (y : ι → ℝ) (α : Fin k → ℝ)
    (θ : Fin m → ℝ) :
    (∀ α' θ', colRSS tr Z y α θ ≤ colRSS tr Z y α' θ') ↔
      NormalEquations tr Z y θ ∧ ∀ j, α (tr j) = trialMean tr (colResid Z y θ) (tr j) := by
  have hQ : ∀ (α' : Fin k → ℝ) (θ' : Fin m → ℝ),
      0 ≤ ∑ j, (trialMean tr (colResid Z y θ') (tr j) - α' (tr j)) ^ 2 :=
    fun _ _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hstar : ∀ θ', colRSS tr Z y (fun i => trialMean tr (colResid Z y θ') i) θ' =
      profiledRSS tr Z y θ' := fun θ' => by rw [colRSS_eq]; simp
  constructor
  · intro hmin
    have hP : ∀ θ', profiledRSS tr Z y θ ≤ profiledRSS tr Z y θ' := by
      intro θ'
      have := hmin (fun i => trialMean tr (colResid Z y θ') i) θ'
      rw [hstar, colRSS_eq] at this
      linarith [hQ α θ]
    refine ⟨normal_of_profiledRSS_le hP, fun j => ?_⟩
    have := hmin (fun i => trialMean tr (colResid Z y θ) i) θ
    rw [hstar, colRSS_eq] at this
    have h0 : ∑ j, (trialMean tr (colResid Z y θ) (tr j) - α (tr j)) ^ 2 = 0 := by
      linarith [hQ α θ]
    have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg _).1 h0 j (Finset.mem_univ j)
    linarith [pow_eq_zero_iff two_ne_zero |>.1 this]
  · rintro ⟨hθ, hα⟩ α' θ'
    rw [colRSS_eq, colRSS_eq]
    have h0 : ∑ j, (trialMean tr (colResid Z y θ) (tr j) - α (tr j)) ^ 2 = 0 :=
      Finset.sum_eq_zero fun j _ => by rw [hα j, sub_self]; ring
    rw [h0]
    linarith [profiledRSS_le_of_normal hθ θ', hQ α' θ']

/-- Two solutions of the normal equations coincide when the profiled design map is injective. -/
theorem normalEquations_unique {tr : ι → Fin k} {Z : Fin m → ι → ℝ} {y : ι → ℝ}
    {θ θ' : Fin m → ℝ} (hθ : NormalEquations tr Z y θ) (hθ' : NormalEquations tr Z y θ')
    (hinj : ProfiledInjective tr Z) : θ' = θ :=
  eq_of_profiledRSS_eq hθ hinj (le_antisymm (profiledRSS_le_of_normal hθ' θ)
    (profiledRSS_le_of_normal hθ θ'))

/-- The normal equations in residual form: `θ` solves them if and only if every column is
orthogonal to the trial-demeaned residual. -/
theorem normalEquations_iff_resid (tr : ι → Fin k) (Z : Fin m → ι → ℝ) (y : ι → ℝ)
    (θ : Fin m → ℝ) :
    NormalEquations tr Z y θ ↔ ∀ p, ∑ j, Z p j * dev tr (colResid Z y θ) j = 0 := by
  refine forall_congr' fun p => ?_
  rw [← gramRhs_sub_gram, sub_eq_zero, eq_comm]

/-! #### The four columns of the interaction model -/

/-- The four columns of the interaction model, in the order of the coefficients
`(δ, γ, β_W, β_B)`: treatment `A`, the within-trial centered covariate `x - x̄_{trial}`,
treatment times it, and treatment times the trial mean `A x̄_{trial}`. The normal equations of
`interactionRSS` after profiling out the trial intercepts are `NormalEquations tr
(interactionColumns tr A x) y θ`, the four-by-four system `∑_q G_{pq} θ_q = b_p` with
`G_{pq} = ∑ⱼ Z̃ₚⱼ Z̃_qⱼ` and `bₚ = ∑ⱼ Z̃ₚⱼ ỹⱼ`, sums over patients of the trial-demeaned
columns. -/
noncomputable def interactionColumns (tr : ι → Fin k) (A x : ι → ℝ) : Fin 4 → ι → ℝ :=
  ![A, dev tr x, fun j => A j * dev tr x j, fun j => A j * trialMean tr x (tr j)]

/-- The interaction objective is the column model with the four interaction columns. -/
theorem interactionRSS_eq_colRSS (tr : ι → Fin k) (A x y : ι → ℝ) (α : Fin k → ℝ)
    (δ γ βW βB : ℝ) :
    interactionRSS tr A x y α δ γ βW βB =
      colRSS tr (interactionColumns tr A x) y α ![δ, γ, βW, βB] := by
  unfold interactionRSS colRSS
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Fin.sum_univ_four, interactionColumns, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- **Least squares in the interaction model without balance.** A parameter vector
`(α, δ, γ, β_W, β_B)` minimizes `interactionRSS` if and only if `(δ, γ, β_W, β_B)` solves the
four-by-four normal equations of the profiled problem and every populated trial intercept is the
trial mean of the outcome minus the column part of the fit. When the profiled design map is
injective (equivalently, the profiled Gram matrix is positive definite,
`profiledInjective_iff_posDef`), the coefficients `(δ, γ, β_W, β_B)` of a minimizer are unique
(`normalEquations_unique`). -/
theorem interactionRSS_isMin_iff (tr : ι → Fin k) (A x y : ι → ℝ) (α : Fin k → ℝ)
    (δ γ βW βB : ℝ) :
    (∀ (α' : Fin k → ℝ) (δ' γ' βW' βB' : ℝ),
        interactionRSS tr A x y α δ γ βW βB ≤ interactionRSS tr A x y α' δ' γ' βW' βB') ↔
      NormalEquations tr (interactionColumns tr A x) y ![δ, γ, βW, βB] ∧
        ∀ j, α (tr j) =
          trialMean tr (colResid (interactionColumns tr A x) y ![δ, γ, βW, βB]) (tr j) := by
  rw [← colRSS_isMin_iff]
  simp only [interactionRSS_eq_colRSS]
  constructor
  · intro h α' θ'
    have := h α' (θ' 0) (θ' 1) (θ' 2) (θ' 3)
    rwa [show (![θ' 0, θ' 1, θ' 2, θ' 3] : Fin 4 → ℝ) = θ' by
      funext i; fin_cases i <;> rfl] at this
  · intro h α' δ' γ' βW' βB'
    exact h α' _

/-- Under balance, a covariate deviation is orthogonal to every treated trial-level term. -/
theorem sum_dev_mul_treated {tr : ι → Fin k} {A x : ι → ℝ} (hA : ∀ j, A j = 0 ∨ A j = 1)
    (hbal : Balanced tr A x) (g : Fin k → ℝ) : ∑ j, dev tr x j * (A j * g (tr j)) = 0 := by
  rw [sum_arms A hA]
  have h0 : ∑ j : {j // A j = 0}, dev tr x j * (A j * g (tr j)) = 0 :=
    Finset.sum_eq_zero fun j _ => by rw [j.2]; ring
  have h1 : ∑ j : {j // A j = 1}, dev tr x j * (A j * g (tr j)) =
      ∑ j : {j // A j = 1}, dev (armTr tr A 1) (fun j => x j) j * g (armTr tr A 1 j) :=
    Finset.sum_congr rfl fun j _ => by rw [j.2, dev_arm hbal 1 j]; unfold armTr; ring
  rw [h0, h1, sum_dev_mul_trial (tr := armTr tr A 1), zero_add]

/-- **Decoupling under balance.** With a binary treatment and covariate balance, the profiled
Gram matrix of the interaction columns has zero entries between the within block
`(γ, β_W)` (columns `1, 2`) and the across block `(δ, β_B)` (columns `0, 3`), so the normal
equations split into two two-by-two systems. The balanced theorem `interactionRSS_min` keeps its
own proof because it gives the solutions in closed form (arm slopes and a weighted regression of
trial treatment effects), which the general system does not display. -/
theorem gram_interaction_decouple {tr : ι → Fin k} {A x : ι → ℝ}
    (hA : ∀ j, A j = 0 ∨ A j = 1) (hbal : Balanced tr A x) :
    gram tr (interactionColumns tr A x) 1 0 = 0 ∧ gram tr (interactionColumns tr A x) 1 3 = 0 ∧
      gram tr (interactionColumns tr A x) 2 0 = 0 ∧
      gram tr (interactionColumns tr A x) 2 3 = 0 := by
  have hAA : ∀ j, A j * A j = A j := fun j => by rcases hA j with h | h <;> simp [h]
  refine ⟨?_, ?_, ?_, ?_⟩
  · change ∑ j, dev tr (dev tr x) j * dev tr A j = 0
    rw [dev_dev, sum_dev_mul_dev]
    simpa using sum_dev_mul_treated hA hbal (fun _ => 1)
  · change ∑ j, dev tr (dev tr x) j * dev tr (fun j => A j * trialMean tr x (tr j)) j = 0
    rw [dev_dev, sum_dev_mul_dev]
    exact sum_dev_mul_treated hA hbal (trialMean tr x)
  · change ∑ j, dev tr (fun j => A j * dev tr x j) j * dev tr A j = 0
    rw [show ∑ j, dev tr (fun j => A j * dev tr x j) j * dev tr A j =
        ∑ j, dev tr A j * dev tr (fun j => A j * dev tr x j) j from
      Finset.sum_congr rfl fun j _ => mul_comm _ _, sum_dev_mul_dev]
    rw [← sum_dev_mul_treated hA hbal (fun i => 1 - trialMean tr A i)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show dev tr A j = A j - trialMean tr A (tr j) from rfl]
    linear_combination (dev tr x j) * hAA j
  · change ∑ j, dev tr (fun j => A j * dev tr x j) j *
      dev tr (fun j => A j * trialMean tr x (tr j)) j = 0
    rw [show ∑ j, dev tr (fun j => A j * dev tr x j) j *
          dev tr (fun j => A j * trialMean tr x (tr j)) j =
        ∑ j, dev tr (fun j => A j * trialMean tr x (tr j)) j *
          dev tr (fun j => A j * dev tr x j) j from
      Finset.sum_congr rfl fun j _ => mul_comm _ _, sum_dev_mul_dev]
    rw [← sum_dev_mul_treated hA hbal
      (fun i => trialMean tr x i - trialMean tr (fun j => A j * trialMean tr x (tr j)) i)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show dev tr (fun j => A j * trialMean tr x (tr j)) j = A j * trialMean tr x (tr j) -
      trialMean tr (fun j => A j * trialMean tr x (tr j)) (tr j) from rfl]
    linear_combination (dev tr x j * trialMean tr x (tr j)) * hAA j

/-! #### Trial-specific treatment effects -/

/-- The fitted value of the interaction model with trial-specific treatment effects `δ_i` in
place of the common `δ`. -/
noncomputable def trialEffectFit (tr : ι → Fin k) (A x : ι → ℝ) (α δ : Fin k → ℝ)
    (γ βW βB : ℝ) (j : ι) : ℝ :=
  α (tr j) + δ (tr j) * A j + γ * dev tr x j + βW * (A j * dev tr x j) +
    βB * (A j * trialMean tr x (tr j))

/-- The column `A x̄_{trial}` is a combination of the trial by treatment columns
`A · 1{trial = i}`, with coefficients the trial mean covariates. -/
theorem treatedMean_mem_span (tr : ι → Fin k) (A x : ι → ℝ) :
    (fun j => A j * trialMean tr x (tr j)) =
      fun j => ∑ i, trialMean tr x i * (A j * if tr j = i then 1 else 0) := by
  funext j
  rw [Finset.sum_eq_single (tr j) (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp only [ite_true]
  ring

/-- **With trial-specific treatment effects the across coefficient is not identified.** For
every parameter vector, moving `β_B x̄_i` into the trial treatment effects gives the same fitted
values with across coefficient `0`; so two parameter vectors with different `β_B` (when
`β_B ≠ 0`) fit every outcome equally well. -/
theorem trialEffectFit_not_identified (tr : ι → Fin k) (A x : ι → ℝ) (α δ : Fin k → ℝ)
    (γ βW βB : ℝ) :
    trialEffectFit tr A x α δ γ βW βB =
        trialEffectFit tr A x α (fun i => δ i + βB * trialMean tr x i) γ βW 0 ∧
      ∀ y : ι → ℝ, ∑ j, (y j - trialEffectFit tr A x α δ γ βW βB j) ^ 2 =
        ∑ j, (y j -
          trialEffectFit tr A x α (fun i => δ i + βB * trialMean tr x i) γ βW 0 j) ^ 2 := by
  have h : trialEffectFit tr A x α δ γ βW βB =
      trialEffectFit tr A x α (fun i => δ i + βB * trialMean tr x i) γ βW 0 := by
    funext j; unfold trialEffectFit; ring
  exact ⟨h, fun y => by rw [h]⟩

end Unbalanced

/-! ### Balance matters: an unbalanced design -/

/-- The patients of the unbalanced example: `(trial, treated, high covariate)`, three trials of
four patients, two per arm. -/
abbrev UbPatient := Fin 3 × Bool × Bool

/-- The trial of a patient of the unbalanced example. -/
def ubTr : UbPatient → Fin 3 := fun j => j.1

/-- The treatment of a patient of the unbalanced example. -/
noncomputable def ubA : UbPatient → ℝ := fun j => if j.2.1 then 1 else 0

/-- The covariate of the unbalanced example: in trial `i` the control arm has `o_i, o_i + 2` and
the treated arm `o_i + s_i, o_i + s_i + 4`, with `o = (0, 2, 4)` and `s = (2, 0, 0)`. -/
noncomputable def ubX : UbPatient → ℝ := fun j =>
  ![0, 2, 4] j.1 + (if j.2.1 then ![2, 0, 0] j.1 else 0) +
    if j.2.2 then (if j.2.1 then 4 else 2) else 0

/-- The outcome of the unbalanced example: a treatment effect `1` in trial `0` only,
`y = A · 1{trial = 0}`. -/
noncomputable def ubY : UbPatient → ℝ := fun j => ubA j * ![1, 0, 0] j.1

/-- The least squares coefficients `(δ, γ, β_W, β_B)` of the unbalanced example. -/
noncomputable def ubTheta : Fin 4 → ℝ := ![235 / 178, 4 / 89, -3 / 89, -24 / 89]

/-- Every cell of the unbalanced example has two patients. -/
theorem ubCard (b : Bool) (i : Fin 3) :
    (Finset.univ.filter fun x : UbPatient => x.2.1 = b ∧ x.1 = i).card = 2 := by
  revert b i; decide

/-- The treatment of the unbalanced example is binary. -/
theorem ubA_binary (j : UbPatient) : ubA j = 0 ∨ ubA j = 1 := by
  unfold ubA; split_ifs <;> simp

/-- The trial mean covariates of the unbalanced example are `5/2, 7/2, 11/2`. -/
theorem ubX_trialMean (i : Fin 3) : trialMean ubTr ubX i = ![5 / 2, 7 / 2, 11 / 2] i := by
  rw [trialMean_eq_sum]
  fin_cases i <;> simp [ubTr, ubX, Fintype.sum_prod_type, Fin.sum_univ_three] <;> norm_num

/-- The cell mean covariates of the unbalanced example: `1, 3, 5` in the control arm and
`4, 4, 6` in the treated arm. -/
theorem ubX_armMean (i : Fin 3) :
    armMean ubTr ubA 0 ubX i = ![1, 3, 5] i ∧ armMean ubTr ubA 1 ubX i = ![4, 4, 6] i := by
  rw [armMean_eq_sum, armMean_eq_sum]
  fin_cases i <;> simp [ubTr, ubA, ubX, Fintype.sum_prod_type, ubCard] <;> norm_num

/-- The deviations of the covariate from the trial means in the unbalanced example. -/
theorem ub_devX (j : UbPatient) : dev ubTr ubX j = ubX j - ![5 / 2, 7 / 2, 11 / 2] j.1 := by
  unfold dev; rw [ubX_trialMean]; rfl

/-- **Balance matters: the two within-trial interactions separate.** In the unbalanced example
(three trials, two patients per cell; the treated arm has a larger covariate spread than the
control arm, and in trial `0` the treated arm is shifted), the treatment is binary, the
covariate varies within the cells of both arms, and the trials have positive weights and
distinct mean covariates, but covariate balance fails. For the outcome `y = A · 1{trial = 0}`
* the pooled difference of the arm slopes computed with cell-centered covariates,
  `withinInteraction`, is `0` (the outcome is constant within every cell);
* the least squares fit of the model with the document's columns `A (x - x̄_{trial})` and
  `A x̄_{trial}` has the unique coefficients `(δ, γ, β_W, β_B) = (235/178, 4/89, -3/89, -24/89)`:
  they solve the normal equations, the profiled design map is injective, and every minimizer of
  `interactionRSS` has these coefficients. So its within coefficient is `-3/89 ≠ 0`. -/
theorem unbalanced_interaction_example :
    (∀ j, ubA j = 0 ∨ ubA j = 1) ∧ ¬ Balanced ubTr ubA ubX ∧
      0 < ∑ j, dev (armTr ubTr ubA 0) (fun j => ubX j) j ^ 2 ∧
      0 < ∑ j, dev (armTr ubTr ubA 1) (fun j => ubX j) j ^ 2 ∧
      0 < wSxx (cellWeight ubTr ubA) (trialMean ubTr ubX) ∧
      withinInteraction ubTr ubA ubX ubY = 0 ∧
      NormalEquations ubTr (interactionColumns ubTr ubA ubX) ubY ubTheta ∧
      ProfiledInjective ubTr (interactionColumns ubTr ubA ubX) ∧
      (∀ (α : Fin 3 → ℝ) (δ γ βW βB : ℝ),
        (∀ (α' : Fin 3 → ℝ) (δ' γ' βW' βB' : ℝ),
          interactionRSS ubTr ubA ubX ubY α δ γ βW βB ≤
            interactionRSS ubTr ubA ubX ubY α' δ' γ' βW' βB') →
        δ = 235 / 178 ∧ γ = 4 / 89 ∧ βW = -3 / 89 ∧ βB = -24 / 89) := by
  have hsize : ∀ a i, (a = 0 ∨ a = 1) → (armSize ubTr ubA a i : ℝ) = 2 := by
    intro a i ha
    rw [armSize_eq]
    rcases ha with rfl | rfl <;> fin_cases i <;> simp [ubTr, ubA, ubCard]
  have hcw : ∀ i, cellWeight ubTr ubA i = 1 := fun i => by
    rw [cellWeight, hsize 0 i (Or.inl rfl), hsize 1 i (Or.inr rfl)]; norm_num
  -- normal equations
  have hnorm : NormalEquations ubTr (interactionColumns ubTr ubA ubX) ubY ubTheta := by
    rw [normalEquations_iff_resid]
    have hm : ∀ i, trialMean ubTr (colResid (interactionColumns ubTr ubA ubX) ubY ubTheta) i =
        ![18 / 89, -16 / 89, 8 / 89] i := by
      intro i
      rw [trialMean_eq_sum]
      fin_cases i <;>
        simp [colResid, Fin.sum_univ_four, interactionColumns, ub_devX, ubX_trialMean, ubTheta,
          ubTr, ubA, ubX, ubY, Fintype.sum_prod_type, Fin.sum_univ_three] <;> norm_num
    intro p
    have hd : ∀ j, dev ubTr (colResid (interactionColumns ubTr ubA ubX) ubY ubTheta) j =
        colResid (interactionColumns ubTr ubA ubX) ubY ubTheta j -
          ![18 / 89, -16 / 89, 8 / 89] j.1 :=
      fun j => by unfold dev; rw [hm]; rfl
    simp only [hd]
    fin_cases p <;>
      simp [colResid, Fin.sum_univ_four, interactionColumns, ub_devX, ubX_trialMean, ubTheta,
        ubTr, ubA, ubX, ubY, Fintype.sum_prod_type, Fin.sum_univ_three] <;> norm_num
  -- injectivity
  have hinj : ProfiledInjective ubTr (interactionColumns ubTr ubA ubX) := by
    have hmA : ∀ i, trialMean ubTr ubA i = 1 / 2 := by
      intro i; rw [trialMean_eq_sum]
      fin_cases i <;> simp [ubTr, ubA, Fintype.sum_prod_type, Fin.sum_univ_three] <;> norm_num
    have hmAd : ∀ i, trialMean ubTr (fun j => ubA j * dev ubTr ubX j) i =
        ![3 / 4, 1 / 4, 1 / 4] i := by
      intro i; rw [trialMean_eq_sum]
      fin_cases i <;>
        simp [ubTr, ubA, ub_devX, ubX, Fintype.sum_prod_type, Fin.sum_univ_three] <;> norm_num
    have hmAm : ∀ i, trialMean ubTr (fun j => ubA j * trialMean ubTr ubX (ubTr j)) i =
        ![5 / 4, 7 / 4, 11 / 4] i := by
      intro i; rw [trialMean_eq_sum]
      fin_cases i <;>
        simp [ubTr, ubA, ubX_trialMean, Fintype.sum_prod_type, Fin.sum_univ_three] <;> norm_num
    intro h hz
    have e : ∀ j, ∑ p, h p * dev ubTr (interactionColumns ubTr ubA ubX p) j =
        h 0 * (ubA j - 1 / 2) + h 1 * dev ubTr ubX j +
        h 2 * (ubA j * dev ubTr ubX j - ![3 / 4, 1 / 4, 1 / 4] j.1) +
        h 3 * (ubA j * ![5 / 2, 7 / 2, 11 / 2] j.1 - ![5 / 4, 7 / 4, 11 / 4] j.1) := by
      intro j
      rw [Fin.sum_univ_four]
      simp only [interactionColumns, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, dev_dev]
      rw [show dev ubTr ubA j = ubA j - trialMean ubTr ubA (ubTr j) from rfl, hmA,
        show dev ubTr (fun j => ubA j * dev ubTr ubX j) j = ubA j * dev ubTr ubX j -
          trialMean ubTr (fun j => ubA j * dev ubTr ubX j) (ubTr j) from rfl, hmAd,
        show dev ubTr (fun j => ubA j * trialMean ubTr ubX (ubTr j)) j =
          ubA j * trialMean ubTr ubX (ubTr j) -
          trialMean ubTr (fun j => ubA j * trialMean ubTr ubX (ubTr j)) (ubTr j) from rfl,
        hmAm, ubX_trialMean]
      rfl
    have q1 := hz (0, false, false)
    have q2 := hz (0, false, true)
    have q3 := hz (0, true, false)
    have q4 := hz (0, true, true)
    have q5 := hz (1, false, false)
    rw [e] at q1 q2 q3 q4 q5
    simp [ub_devX, ubA, ubX] at q1 q2 q3 q4 q5
    norm_num at q1 q2 q3 q4 q5
    funext p
    fin_cases p <;> simp <;> linarith
  refine ⟨ubA_binary, ?_, ?_, ?_, ?_, ?_, hnorm, hinj, ?_⟩
  · intro hb
    have := hb (0, true, false)
    rw [show ubA (0, true, false) = 1 by simp [ubA], show ubTr (0, true, false) = 0 from rfl,
      (ubX_armMean 0).2, ubX_trialMean] at this
    norm_num at this
  · refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun j => dev (armTr ubTr ubA 0)
      (fun j => ubX j) j ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ ⟨(0, false, false), by simp [ubA]⟩))
    change 0 < (ubX (0, false, false) - armMean ubTr ubA 0 ubX 0) ^ 2
    rw [(ubX_armMean 0).1]; norm_num [ubX]
  · refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun j => dev (armTr ubTr ubA 1)
      (fun j => ubX j) j ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ ⟨(0, true, false), by simp [ubA]⟩))
    change 0 < (ubX (0, true, false) - armMean ubTr ubA 1 ubX 0) ^ 2
    rw [(ubX_armMean 0).2]; norm_num [ubX]
  · simp only [wSxx, wMean, hcw, ubX_trialMean, Fin.sum_univ_three]
    norm_num
  · calc withinInteraction ubTr ubA ubX ubY = withinInteraction ubTr ubA ubX (fun _ => 0) := by
          rw [← withinInteraction_add_trial ubTr ubA ubX (fun _ => 0) (fun _ => 0) ![1, 0, 0]]
          congr 1; funext j; simp only [ubY, ubTr]; ring
      _ = 0 := by simp [withinInteraction, armWithinSlope, withinSlope, dev, trialMean]
  · intro α δ γ βW βB hmin
    have h := ((interactionRSS_isMin_iff ubTr ubA ubX ubY α δ γ βW βB).1 hmin).1
    have := normalEquations_unique hnorm h hinj
    have h0 := congrFun this 0
    have h1 := congrFun this 1
    have h2 := congrFun this 2
    have h3 := congrFun this 3
    exact ⟨by simpa [ubTheta] using h0, by simpa [ubTheta] using h1, by simpa [ubTheta] using h2,
      by simpa [ubTheta] using h3⟩

end CausalInference.BiasAnalysis.EcologicalBias
