/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.StructuralNested.TwoStage
public import CausalInference.Estimation.InstrumentalVariables

/-!
# Two-stage estimation: the stage-one estimator in finite samples

The stage-one equation is affine in `exp ψ` (`TwoStageTrial.stageOne_eq`): intercept plus
`exp ψ` times slope. This file defines its closed-form root, applies it to the empirical law of a
finite sample, and proves consistency under i.i.d. sampling.

## Main results

* `TwoStageTrial.closedForm`, `TwoStageTrial.stageOne_eq_zero_iff_closedForm`: the closed form
  `log (-intercept / slope)` is the unique root when the slope is positive and the intercept is
  negative. A positive slope alone is not enough: with a nonnegative intercept there is no root
  (`TwoStageTrial.stageOne_ne_zero`). At a root with positive slope the intercept is negative
  and the closed form is that root (`TwoStageTrial.closedForm_eq_of_root`).
* `empiricalDist`, `sum_empiricalDist`: the empirical law of the first `n` observations, under
  which expectations are sample means.
* `TwoStageTrial.sampleRoot`, `TwoStageTrial.stageOne_empiricalDist_eq_zero_iff`: the stage-one
  estimator, built from sample conditional means, is the unique root of stage one under the
  empirical law (a single stratum) whenever the sample slope is positive and the sample
  intercept negative.
* `TwoStageTrial.sampleRoot_isConsistent`: for an i.i.d. sample in the finite observation space
  of the trial, with law `q`, the estimator is consistent (`IsConsistent`) for the population
  closed form, by the law of large numbers for sample conditional means
  (`sampleCondMean_isConsistent`) and continuous mapping; and
  `TwoStageTrial.sampleRoot_isConsistent_true`: under the structural model, no unmeasured
  confounding, positivity and relevance for `q`, it is consistent for the true parameter.

The estimator here uses a single stratum; `TwoStageSampleStrata` treats several strata, with
fixed weights or with the stratum frequencies as weights.
-/

@[expose] public section

open Finset MeasureTheory ProbabilityTheory CausalInference.Longitudinal

namespace CausalInference

namespace StructuralNested

namespace TwoStageTrial

/-! ### The closed form of the stage-one root -/

/-- **The closed-form stage-one estimator**: the root of the affine equation
`a + exp ψ * b = 0` on the log scale, `log (-a / b)`. -/
noncomputable def closedForm (a b : ℝ) : ℝ := Real.log (-a / b)

/-- With a positive slope and a negative intercept, the closed form is the unique root of the
affine equation. -/
theorem affine_eq_zero_iff_closedForm {a b : ℝ} (hb : 0 < b) (ha : a < 0) (ψ : ℝ) :
    a + Real.exp ψ * b = 0 ↔ ψ = closedForm a b := by
  have hq : 0 < -a / b := div_pos (by linarith) hb
  rw [closedForm]
  constructor
  · intro h
    rw [show -a / b = Real.exp ψ by rw [div_eq_iff hb.ne']; linarith, Real.log_exp]
  · rintro rfl
    rw [Real.exp_log hq]
    field_simp
    ring

/-- With a positive slope and a nonnegative intercept the affine equation has no root. -/
theorem affine_ne_zero {a b : ℝ} (hb : 0 < b) (ha : 0 ≤ a) (ψ : ℝ) : a + Real.exp ψ * b ≠ 0 :=
  (add_pos_of_nonneg_of_pos ha (mul_pos (Real.exp_pos ψ) hb)).ne'

variable {Ω : Type*} (M : TwoStageTrial Ω) [Fintype Ω] [DecidableEq Ω] {𝓛 : Type*} [Fintype 𝓛]
  [DecidableEq 𝓛]

/-- **The closed form is the unique stage-one root** when the slope is positive and the
intercept negative; with a positive slope and a nonnegative intercept there is no root
(`stageOne_ne_zero`). -/
theorem stageOne_eq_zero_iff_closedForm {p : FiniteDist Ω} {P : Finset Ω} {L : Ω → 𝓛}
    {w : 𝓛 → ℝ} {B : Ω → ℝ} (hb : 0 < M.stageOneSlope p P L w B)
    (ha : M.stageOneIntercept p P L w B < 0) (ψ : ℝ) :
    M.stageOne p P L w B ψ = 0 ↔
      ψ = closedForm (M.stageOneIntercept p P L w B) (M.stageOneSlope p P L w B) := by
  rw [M.stageOne_eq]; exact affine_eq_zero_iff_closedForm hb ha ψ

/-- With a positive slope and a nonnegative intercept, stage one has no root. -/
theorem stageOne_ne_zero {p : FiniteDist Ω} {P : Finset Ω} {L : Ω → 𝓛} {w : 𝓛 → ℝ}
    {B : Ω → ℝ} (hb : 0 < M.stageOneSlope p P L w B) (ha : 0 ≤ M.stageOneIntercept p P L w B)
    (ψ : ℝ) : M.stageOne p P L w B ψ ≠ 0 := by
  rw [M.stageOne_eq]; exact affine_ne_zero hb ha ψ

/-- **At the truth the closed form is the truth.** If `ψ` is a root and the slope is positive,
the intercept is negative and the closed form is `ψ`. -/
theorem closedForm_eq_of_root {p : FiniteDist Ω} {P : Finset Ω} {L : Ω → 𝓛} {w : 𝓛 → ℝ}
    {B : Ω → ℝ} {ψ : ℝ} (h : M.stageOne p P L w B ψ = 0) (hb : 0 < M.stageOneSlope p P L w B) :
    M.stageOneIntercept p P L w B < 0 ∧
      closedForm (M.stageOneIntercept p P L w B) (M.stageOneSlope p P L w B) = ψ := by
  rw [M.stageOne_eq] at h
  have ha : M.stageOneIntercept p P L w B < 0 := by
    nlinarith [mul_pos (Real.exp_pos ψ) hb]
  exact ⟨ha, ((affine_eq_zero_iff_closedForm hb ha ψ).1 h).symm⟩

end TwoStageTrial

/-! ### The empirical law of a sample -/

section Empirical

variable {Ω 𝒪 : Type*} [Fintype 𝒪] [DecidableEq 𝒪]

/-- **The empirical law** of the first `n > 0` observations `O 0 ω, …, O (n - 1) ω`: the mass of
`o` is the proportion of observations equal to `o`. -/
noncomputable def empiricalDist (O : ℕ → Ω → 𝒪) {n : ℕ} (hn : 0 < n) (ω : Ω) : FiniteDist 𝒪 where
  mass o := (#{i ∈ range n | O i ω = o} : ℝ) / n
  nonneg o := by positivity
  sum_eq_one := by
    rw [← sum_div, div_eq_one_iff_eq (by exact_mod_cast hn.ne')]
    have := Finset.sum_fiberwise (range n) (fun i => O i ω) (fun _ => (1 : ℝ))
    simp only [sum_const, nsmul_eq_mul, mul_one, card_range] at this
    exact_mod_cast this

/-- An expectation under the empirical law is a sample mean. -/
theorem sum_empiricalDist (O : ℕ → Ω → 𝒪) {n : ℕ} (hn : 0 < n) (ω : Ω) (g : 𝒪 → ℝ) :
    ∑ o, empiricalDist O hn ω o * g o = sampleMean g O n ω := by
  rw [sampleMean, ← Finset.sum_fiberwise (range n) (fun i => O i ω) (fun i => g (O i ω)),
    mul_sum]
  refine sum_congr rfl fun o _ => ?_
  rw [sum_congr rfl (g := fun _ => g o) fun i hi => by rw [(mem_filter.1 hi).2], sum_const,
    nsmul_eq_mul]
  change (#{i ∈ range n | O i ω = o} : ℝ) / n * g o = _
  ring

end Empirical

namespace TwoStageTrial

variable {Ω 𝒪 : Type*} [Fintype 𝒪] [DecidableEq 𝒪] (M : TwoStageTrial 𝒪)

/-- A stage-one conditional mean under the empirical law, with a single stratum, is a sample
conditional mean. -/
theorem condMean_empiricalDist (O : ℕ → Ω → 𝒪) {n : ℕ} (hn : 0 < n) (ω : Ω) (x : Bool)
    (f : 𝒪 → ℝ) :
    condMean (empiricalDist O hn ω) (M.cell univ (fun _ => ()) x ()) f =
      sampleCondMean M.X x f O n ω := by
  rw [condMean, sampleCondMean, M.wsum_cell_univ, M.wmass_cell_univ,
    ← sum_empiricalDist O hn ω, ← sum_empiricalDist O hn ω]
  congr 1 <;> exact sum_congr rfl fun o _ => by split_ifs <;> simp_all

/-- The sample slope of stage one: the sample mean of the treated time among switchers. -/
noncomputable def sampleSlope (B : 𝒪 → ℝ) (O : ℕ → Ω → 𝒪) (n : ℕ) (ω : Ω) : ℝ :=
  sampleCondMean M.X true (M.treated B) O n ω

/-- The sample intercept of stage one: the difference of the sample means of the part of the
transformed residual that does not depend on `ψ`. -/
noncomputable def sampleIntercept (B : 𝒪 → ℝ) (O : ℕ → Ω → 𝒪) (n : ℕ) (ω : Ω) : ℝ :=
  sampleCondMean M.X true (M.baseResid B) O n ω - sampleCondMean M.X false (M.baseResid B) O n ω

/-- **The stage-one estimator**: the closed form of the sample intercept and slope. -/
noncomputable def sampleRoot (B : 𝒪 → ℝ) (O : ℕ → Ω → 𝒪) (n : ℕ) (ω : Ω) : ℝ :=
  closedForm (M.sampleIntercept B O n ω) (M.sampleSlope B O n ω)

/-- The slope of stage one under the empirical law is the sample slope. -/
theorem stageOneSlope_empiricalDist (B : 𝒪 → ℝ) (O : ℕ → Ω → 𝒪) {n : ℕ} (hn : 0 < n)
    (ω : Ω) : M.stageOneSlope (empiricalDist O hn ω) univ (fun _ => ()) (fun _ => 1) B =
      M.sampleSlope B O n ω := by
  rw [stageOneSlope, Fintype.sum_unique, one_mul, show (default : Unit) = () from rfl,
    condMean_empiricalDist, sampleSlope]

/-- The intercept of stage one under the empirical law is the sample intercept. -/
theorem stageOneIntercept_empiricalDist (B : 𝒪 → ℝ) (O : ℕ → Ω → 𝒪) {n : ℕ} (hn : 0 < n)
    (ω : Ω) : M.stageOneIntercept (empiricalDist O hn ω) univ (fun _ => ()) (fun _ => 1) B =
      M.sampleIntercept B O n ω := by
  rw [stageOneIntercept, Fintype.sum_unique, one_mul, show (default : Unit) = () from rfl,
    condMean_empiricalDist, condMean_empiricalDist, sampleIntercept]

/-- **The estimator is the unique root of stage one under the empirical law** (a single
stratum), whenever the sample slope is positive and the sample intercept negative. -/
theorem stageOne_empiricalDist_eq_zero_iff (B : 𝒪 → ℝ) (O : ℕ → Ω → 𝒪) {n : ℕ} (hn : 0 < n)
    (ω : Ω) (hb : 0 < M.sampleSlope B O n ω) (ha : M.sampleIntercept B O n ω < 0) (ψ : ℝ) :
    M.stageOne (empiricalDist O hn ω) univ (fun _ => ()) (fun _ => 1) B ψ = 0 ↔
      ψ = M.sampleRoot B O n ω := by
  rw [M.stageOne_eq, stageOneSlope_empiricalDist, stageOneIntercept_empiricalDist, sampleRoot]
  exact affine_eq_zero_iff_closedForm hb ha ψ

/-! ### Consistency -/

variable {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒪] [MeasurableSingletonClass 𝒪]

omit [DecidableEq 𝒪] in
/-- A conditional mean of a function of the first observation, given an event about it, is the
conditional mean under the law `q` of the first observation. -/
theorem integral_cond_eq_condMean {μ : Measure Ω} {O0 : Ω → 𝒪} (hO0 : AEMeasurable O0 μ)
    {q : FiniteDist 𝒪} (hlaw : μ.map O0 = q.toMeasure) (A : Finset 𝒪) (f : 𝒪 → ℝ) :
    ∫ ω, f (O0 ω) ∂μ[|O0 ⁻¹' (A : Set 𝒪)] = condMean q A f := by
  have hA : MeasurableSet (A : Set 𝒪) := A.finite_toSet.measurableSet
  have hf : AEStronglyMeasurable f (μ.map O0) := (Measurable.of_discrete).aestronglyMeasurable
  have hmass : μ (O0 ⁻¹' (A : Set 𝒪)) = q.toMeasure A := by
    rw [← hlaw, Measure.map_apply_of_aemeasurable hO0 hA]
  have hreal : (q.toMeasure A).toReal = wmass q A := q.toMeasure_real_finset A
  rw [ProbabilityTheory.cond, integral_smul_measure, ← setIntegral_map hA hf hO0, hlaw,
    hmass, ENNReal.toReal_inv, hreal, integral_indicator hA |>.symm, FiniteDist.integral_toMeasure,
    condMean, smul_eq_mul, wsum, FiniteDist.expect, inv_mul_eq_div]
  congr 1
  classical
  simp only [Set.indicator_apply, Finset.mem_coe, mul_ite, mul_zero]
  rw [← sum_filter]
  congr 1
  ext; simp

omit [MeasurableSpace 𝒪] [MeasurableSingletonClass 𝒪] in
/-- The switch group `x` as a set of observations. -/
theorem cell_univ_eq (x : Bool) :
    M.cell univ (fun _ => ()) x () = univ.filter fun o => M.X o = x := by
  ext o; simp [cell, ev]

/-- **Consistency of the stage-one estimator.** Let `O` be an i.i.d. sample under a probability
measure `μ`, with values in the finite observation space of the trial and law `q` (as a measure,
`μ.map (O 0) = q.toMeasure`). If stage one under `q`, with a single stratum, has a positive slope
and a negative intercept, the estimator `sampleRoot` is consistent for the closed form of the
population intercept and slope, the unique population root. -/
theorem sampleRoot_isConsistent {μ : Measure Ω} [IsProbabilityMeasure μ] {O : ℕ → Ω → 𝒪}
    (hO : IsIIDSample O μ) {q : FiniteDist 𝒪} (hlaw : μ.map (O 0) = q.toMeasure) (B : 𝒪 → ℝ)
    (hb : 0 < M.stageOneSlope q univ (fun _ => ()) (fun _ => 1) B)
    (ha : M.stageOneIntercept q univ (fun _ => ()) (fun _ => 1) B < 0)
    (hm0 : 0 < wmass q (M.cell univ (fun _ => ()) false ())) :
    IsConsistent (M.sampleRoot B O)
      (closedForm (M.stageOneIntercept q univ (fun _ => ()) (fun _ => 1) B)
        (M.stageOneSlope q univ (fun _ => ()) (fun _ => 1) B)) μ := by
  have hO0 : AEMeasurable (O 0) μ := hO.aemeasurable 0
  have hint : ∀ f : 𝒪 → ℝ, Integrable (fun ω => f (O 0 ω)) μ := fun f =>
    (integrable_map_measure (Measurable.of_discrete).aestronglyMeasurable hO0).1
      (by rw [hlaw]; exact Integrable.of_finite)
  have hpre : ∀ x : Bool, (fun ω => M.X (O 0 ω)) ⁻¹' {x} =
      O 0 ⁻¹' ((univ.filter fun o => M.X o = x : Finset 𝒪) : Set 𝒪) := fun x => by
    ext ω; simp
  have htarget : ∀ x f, ∫ ω, f (O 0 ω) ∂μ[|(fun ω => M.X (O 0 ω)) ⁻¹' {x}] =
      condMean q (M.cell univ (fun _ => ()) x ()) f := fun x f => by
    rw [hpre, integral_cond_eq_condMean hO0 hlaw, cell_univ_eq]
  have hpos : ∀ x, 0 < wmass q (M.cell univ (fun _ => ()) x ()) →
      μ ((fun ω => M.X (O 0 ω)) ⁻¹' {x}) ≠ 0 := fun x hm h0 => by
    rw [hpre, ← Measure.map_apply_of_aemeasurable hO0 (Finset.finite_toSet _).measurableSet,
      hlaw, ← cell_univ_eq] at h0
    have := q.toMeasure_real_finset (M.cell univ (fun _ => ()) x ())
    rw [h0, ENNReal.toReal_zero] at this
    have hw : wmass q (M.cell univ (fun _ => ()) x ()) = q.prob _ := rfl
    linarith
  have hslope : M.stageOneSlope q univ (fun _ => ()) (fun _ => 1) B =
      condMean q (M.cell univ (fun _ => ()) true ()) (M.treated B) := by
    rw [stageOneSlope, Fintype.sum_unique, one_mul]
  have hm1 : 0 < wmass q (M.cell univ (fun _ => ()) true ()) := by
    by_contra h
    have h0 : wmass q (M.cell univ (fun _ => ()) true ()) = 0 :=
      le_antisymm (not_lt.1 h) (sum_nonneg fun ω _ => q.nonneg ω)
    rw [hslope, condMean, h0, div_zero] at hb
    exact lt_irrefl _ hb
  have hinter : M.stageOneIntercept q univ (fun _ => ()) (fun _ => 1) B =
      condMean q (M.cell univ (fun _ => ()) true ()) (M.baseResid B) -
        condMean q (M.cell univ (fun _ => ()) false ()) (M.baseResid B) := by
    rw [stageOneIntercept, Fintype.sum_unique, one_mul]
  have cm : ∀ x f, 0 < wmass q (M.cell univ (fun _ => ()) x ()) →
      IsConsistent (sampleCondMean M.X x f O)
        (condMean q (M.cell univ (fun _ => ()) x ()) f) μ := fun x f hm => by
    rw [← htarget]
    exact sampleCondMean_isConsistent hO Measurable.of_discrete x Measurable.of_discrete
      (hint f) (hpos x hm)
  have hS : IsConsistent (M.sampleSlope B O)
      (M.stageOneSlope q univ (fun _ => ()) (fun _ => 1) B) μ := by
    rw [hslope]; exact cm true _ hm1
  have hI : IsConsistent (M.sampleIntercept B O)
      (M.stageOneIntercept q univ (fun _ => ()) (fun _ => 1) B) μ := by
    rw [hinter]; exact (cm true _ hm1).sub (cm false _ hm0)
  have hne : -(M.stageOneIntercept q univ (fun _ => ()) (fun _ => 1) B /
      M.stageOneSlope q univ (fun _ => ()) (fun _ => 1) B) ≠ 0 :=
    neg_ne_zero.2 (div_neg_of_neg_of_pos ha hb).ne
  have key := (hI.div hS hb.ne').comp (g := fun t => Real.log (-t))
    ((Real.continuousAt_log hne).comp continuousAt_neg)
  simp only [← neg_div] at key
  exact key

/-- **Consistency for the true parameter.** If the population law `q` follows the structural
model, no unmeasured confounding and positivity hold at the secondary baseline with a single
stratum, and relevance holds (`0 < stageOneSlope`), the stage-one estimator is consistent for
the true parameter `ψ`. -/
theorem sampleRoot_isConsistent_true {μ : Measure Ω} [IsProbabilityMeasure μ]
    {O : ℕ → Ω → 𝒪} (hO : IsIIDSample O μ) {q : FiniteDist 𝒪} (hlaw : μ.map (O 0) = q.toMeasure)
    {B : 𝒪 → ℝ} {ψ : ℝ} (hmodel : M.ModelOn univ B ψ) (hnuc : M.BaselineNUC q univ fun _ => ())
    (hpos : M.BaselinePositive q univ (fun _ => ()) fun _ => 1)
    (hb : 0 < M.stageOneSlope q univ (fun _ => ()) (fun _ => 1) B) :
    IsConsistent (M.sampleRoot B O) ψ μ := by
  obtain ⟨ha, hc⟩ := M.closedForm_eq_of_root (M.stageOne_eq_zero hmodel hnuc hpos) hb
  rw [← hc]
  exact M.sampleRoot_isConsistent hO hlaw B hb ha (hpos () one_ne_zero).2

end TwoStageTrial

end StructuralNested

end CausalInference
