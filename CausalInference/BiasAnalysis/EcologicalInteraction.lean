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

end CausalInference.BiasAnalysis.EcologicalBias
