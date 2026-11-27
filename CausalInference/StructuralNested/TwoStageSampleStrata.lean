/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.StructuralNested.TwoStageSample

/-!
# Two-stage estimation: the stage-one estimator with several strata

The sample estimator of `TwoStageSample` uses a single stratum. Here the strata are the values
of a finite covariate `S : 𝒪 → 𝓛` measured at the secondary baseline, with fixed weights or
with the stratum frequencies as estimated weights.

## Main results

* `TwoStageTrial.sampleCellMean`: the sample mean in a cell (switch group and stratum);
  `TwoStageTrial.condMean_empiricalDist_cell`: it is the cell conditional mean under the
  empirical law.
* `TwoStageTrial.sampleRootStrata` (fixed weights `w`) and `TwoStageTrial.sampleRootFreq`
  (stratum frequencies `sampleFreq`): the closed forms of the sample intercept and slope.
  `TwoStageTrial.stageOne_empiricalDist_strata_iff` and
  `TwoStageTrial.stageOne_empiricalDist_freq_iff`: each is the unique root of stage one under
  the empirical law, with the weights `w`, respectively with the empirical stratum masses.
* `TwoStageTrial.sampleRootStrata_isConsistent`, `TwoStageTrial.sampleRootStrata_isConsistent_true`:
  consistency for the population closed form, and for the true parameter under the structural
  model, no unmeasured confounding within strata, positivity and relevance.
* `TwoStageTrial.sampleRootFreq_isConsistent`, `TwoStageTrial.sampleRootFreq_isConsistent_true`:
  the same with estimated weights, whose population values are the stratum masses
  `freqWeight q S`; the continuous mapping step goes through (`IsConsistent.mul`). Positivity
  is assumed in every stratum.
* `isConsistent_const`, `isConsistent_sum`: constants and finite sums of consistent estimators.
-/

@[expose] public section

open Finset MeasureTheory ProbabilityTheory CausalInference.Longitudinal

namespace CausalInference

namespace StructuralNested

section Consistency

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- A constant estimator is consistent for its value. -/
theorem isConsistent_const (c : ℝ) : IsConsistent (fun _ _ => c) c μ := by
  rw [IsConsistent, tendstoInMeasure_iff_dist]
  intro ε hε
  simp [not_le.2 hε]

/-- **Consistency of a finite sum** of consistent estimators. -/
theorem isConsistent_sum {ι : Type*} (s : Finset ι) {a : ι → ℕ → Ω → ℝ} {α : ι → ℝ}
    (h : ∀ i ∈ s, IsConsistent (a i) (α i) μ) :
    IsConsistent (fun n ω => ∑ i ∈ s, a i n ω) (∑ i ∈ s, α i) μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isConsistent_const (μ := μ) 0
  | insert j s hj ih =>
    simp only [sum_insert hj]
    exact IsConsistent.comp₂ (g := (· + ·)) continuous_add.continuousAt
      (h j (mem_insert_self j s)) (ih fun i hi => h i (mem_insert_of_mem hi))

end Consistency

namespace TwoStageTrial

variable {Ω 𝒪 𝓛 : Type*} [Fintype 𝒪] [DecidableEq 𝒪] [Fintype 𝓛] [DecidableEq 𝓛]
  (M : TwoStageTrial 𝒪)

/-- The sample mean of `f` in the cell of switch group `x` and stratum `l`. -/
noncomputable def sampleCellMean (S : 𝒪 → 𝓛) (x : Bool) (l : 𝓛) (f : 𝒪 → ℝ)
    (O : ℕ → Ω → 𝒪) (n : ℕ) (ω : Ω) : ℝ :=
  sampleCondMean (fun o => decide (S o = l ∧ M.X o = x)) true f O n ω

/-- The sample slope of stage one with the strata `S` and the weights `w`. -/
noncomputable def sampleSlopeStrata (S : 𝒪 → 𝓛) (w : 𝓛 → ℝ) (B : 𝒪 → ℝ) (O : ℕ → Ω → 𝒪)
    (n : ℕ) (ω : Ω) : ℝ :=
  ∑ l, w l * M.sampleCellMean S true l (M.treated B) O n ω

/-- The sample intercept of stage one with the strata `S` and the weights `w`. -/
noncomputable def sampleInterceptStrata (S : 𝒪 → 𝓛) (w : 𝓛 → ℝ) (B : 𝒪 → ℝ)
    (O : ℕ → Ω → 𝒪) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ l, w l * (M.sampleCellMean S true l (M.baseResid B) O n ω -
    M.sampleCellMean S false l (M.baseResid B) O n ω)

/-- **The stratified stage-one estimator with fixed weights**: the closed form of the sample
intercept and slope. -/
noncomputable def sampleRootStrata (S : 𝒪 → 𝓛) (w : 𝓛 → ℝ) (B : 𝒪 → ℝ) (O : ℕ → Ω → 𝒪)
    (n : ℕ) (ω : Ω) : ℝ :=
  closedForm (M.sampleInterceptStrata S w B O n ω) (M.sampleSlopeStrata S w B O n ω)

/-- The sample frequency of the stratum `l`. -/
noncomputable def sampleFreq (S : 𝒪 → 𝓛) (l : 𝓛) (O : ℕ → Ω → 𝒪) (n : ℕ) (ω : Ω) : ℝ :=
  sampleMean (fun o => if S o = l then 1 else 0) O n ω

/-- The sample slope with the stratum frequencies as weights. -/
noncomputable def sampleSlopeFreq (S : 𝒪 → 𝓛) (B : 𝒪 → ℝ) (O : ℕ → Ω → 𝒪) (n : ℕ)
    (ω : Ω) : ℝ :=
  ∑ l, sampleFreq S l O n ω * M.sampleCellMean S true l (M.treated B) O n ω

/-- The sample intercept with the stratum frequencies as weights. -/
noncomputable def sampleInterceptFreq (S : 𝒪 → 𝓛) (B : 𝒪 → ℝ) (O : ℕ → Ω → 𝒪) (n : ℕ)
    (ω : Ω) : ℝ :=
  ∑ l, sampleFreq S l O n ω * (M.sampleCellMean S true l (M.baseResid B) O n ω -
    M.sampleCellMean S false l (M.baseResid B) O n ω)

/-- **The stratified stage-one estimator with estimated weights**, the stratum frequencies. -/
noncomputable def sampleRootFreq (S : 𝒪 → 𝓛) (B : 𝒪 → ℝ) (O : ℕ → Ω → 𝒪) (n : ℕ)
    (ω : Ω) : ℝ :=
  closedForm (M.sampleInterceptFreq S B O n ω) (M.sampleSlopeFreq S B O n ω)

/-! ### The estimators are stage one under the empirical law -/

omit [Fintype 𝓛] in
/-- A cell conditional mean under the empirical law is a sample cell mean. -/
theorem condMean_empiricalDist_cell (S : 𝒪 → 𝓛) (O : ℕ → Ω → 𝒪) {n : ℕ} (hn : 0 < n)
    (ω : Ω) (x : Bool) (l : 𝓛) (f : 𝒪 → ℝ) :
    condMean (empiricalDist O hn ω) (M.cell univ S x l) f =
      M.sampleCellMean S x l f O n ω := by
  rw [condMean, sampleCellMean, sampleCondMean, M.wsum_cell_univ, M.wmass_cell_univ,
    ← sum_empiricalDist O hn ω, ← sum_empiricalDist O hn ω]
  congr 1 <;> exact sum_congr rfl fun o _ => by split_ifs <;> simp_all

omit [Fintype 𝓛] in
/-- The mass of a stratum under the empirical law is its sample frequency. -/
theorem wmass_empiricalDist_stratum (S : 𝒪 → 𝓛) (O : ℕ → Ω → 𝒪) {n : ℕ} (hn : 0 < n)
    (ω : Ω) (l : 𝓛) :
    wmass (empiricalDist O hn ω) (univ ∩ ev S l) = sampleFreq S l O n ω := by
  rw [wmass_stratum_univ, sampleFreq, ← sum_empiricalDist O hn ω]
  exact sum_congr rfl fun o _ => by split_ifs <;> simp

/-- **With fixed weights, the estimator is the unique root of stage one under the empirical
law** with the strata `S`, whenever the sample slope is positive and the sample intercept
negative. -/
theorem stageOne_empiricalDist_strata_iff (S : 𝒪 → 𝓛) (w : 𝓛 → ℝ) (B : 𝒪 → ℝ)
    (O : ℕ → Ω → 𝒪) {n : ℕ} (hn : 0 < n) (ω : Ω) (hb : 0 < M.sampleSlopeStrata S w B O n ω)
    (ha : M.sampleInterceptStrata S w B O n ω < 0) (ψ : ℝ) :
    M.stageOne (empiricalDist O hn ω) univ S w B ψ = 0 ↔
      ψ = M.sampleRootStrata S w B O n ω := by
  have hs : M.stageOneSlope (empiricalDist O hn ω) univ S w B =
      M.sampleSlopeStrata S w B O n ω := by
    simp only [stageOneSlope, sampleSlopeStrata, condMean_empiricalDist_cell]
  have hi : M.stageOneIntercept (empiricalDist O hn ω) univ S w B =
      M.sampleInterceptStrata S w B O n ω := by
    simp only [stageOneIntercept, sampleInterceptStrata, condMean_empiricalDist_cell]
  rw [M.stageOne_eq, hs, hi, sampleRootStrata]
  exact affine_eq_zero_iff_closedForm hb ha ψ

/-- **With the stratum frequencies as weights, the estimator is the unique root of stage one
under the empirical law with its own stratum masses as weights.** -/
theorem stageOne_empiricalDist_freq_iff (S : 𝒪 → 𝓛) (B : 𝒪 → ℝ) (O : ℕ → Ω → 𝒪) {n : ℕ}
    (hn : 0 < n) (ω : Ω) (hb : 0 < M.sampleSlopeFreq S B O n ω)
    (ha : M.sampleInterceptFreq S B O n ω < 0) (ψ : ℝ) :
    M.stageOne (empiricalDist O hn ω) univ S
        (fun l => wmass (empiricalDist O hn ω) (univ ∩ ev S l)) B ψ = 0 ↔
      ψ = M.sampleRootFreq S B O n ω := by
  have hs : M.stageOneSlope (empiricalDist O hn ω) univ S
      (fun l => wmass (empiricalDist O hn ω) (univ ∩ ev S l)) B = M.sampleSlopeFreq S B O n ω := by
    simp only [stageOneSlope, sampleSlopeFreq, condMean_empiricalDist_cell,
      wmass_empiricalDist_stratum]
  have hi : M.stageOneIntercept (empiricalDist O hn ω) univ S
      (fun l => wmass (empiricalDist O hn ω) (univ ∩ ev S l)) B =
      M.sampleInterceptFreq S B O n ω := by
    simp only [stageOneIntercept, sampleInterceptFreq, condMean_empiricalDist_cell,
      wmass_empiricalDist_stratum]
  rw [M.stageOne_eq, hs, hi, sampleRootFreq]
  exact affine_eq_zero_iff_closedForm hb ha ψ

/-! ### Consistency -/

variable {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒪] [MeasurableSingletonClass 𝒪]

omit [Fintype 𝓛] in
/-- **Consistency of a sample cell mean** for the cell conditional mean under the law `q` of
an observation, when the cell has positive mass. -/
theorem sampleCellMean_isConsistent {μ : Measure Ω} [IsProbabilityMeasure μ]
    {O : ℕ → Ω → 𝒪} (hO : IsIIDSample O μ) {q : FiniteDist 𝒪} (hlaw : μ.map (O 0) = q.toMeasure)
    (S : 𝒪 → 𝓛) (x : Bool) (l : 𝓛) (f : 𝒪 → ℝ) (hm : 0 < wmass q (M.cell univ S x l)) :
    IsConsistent (M.sampleCellMean S x l f O) (condMean q (M.cell univ S x l) f) μ := by
  have hO0 : AEMeasurable (O 0) μ := hO.aemeasurable 0
  have hint : Integrable (fun ω => f (O 0 ω)) μ :=
    (integrable_map_measure (Measurable.of_discrete).aestronglyMeasurable hO0).1
      (by rw [hlaw]; exact Integrable.of_finite)
  have hcell : M.cell univ S x l = univ.filter fun o => decide (S o = l ∧ M.X o = x) = true := by
    ext o; simp [cell, ev]
  have hpre : (fun ω => decide (S (O 0 ω) = l ∧ M.X (O 0 ω) = x)) ⁻¹' {true} =
      O 0 ⁻¹' ((M.cell univ S x l : Finset 𝒪) : Set 𝒪) := by
    rw [hcell]; ext ω; simp
  have hpos : μ ((fun ω => decide (S (O 0 ω) = l ∧ M.X (O 0 ω) = x)) ⁻¹' {true}) ≠ 0 := by
    intro h0
    rw [hpre, ← Measure.map_apply_of_aemeasurable hO0 (Finset.finite_toSet _).measurableSet,
      hlaw] at h0
    have := q.toMeasure_real_finset (M.cell univ S x l)
    rw [h0, ENNReal.toReal_zero] at this
    have hw : wmass q (M.cell univ S x l) = q.prob _ := rfl
    linarith
  have key := sampleCondMean_isConsistent hO
    (zb := fun o => decide (S o = l ∧ M.X o = x)) Measurable.of_discrete true
    Measurable.of_discrete hint hpos
  rw [hpre, integral_cond_eq_condMean hO0 hlaw] at key
  exact key

omit [Fintype 𝓛] in
/-- **Consistency of a sample stratum frequency** for the stratum mass under `q`. -/
theorem sampleFreq_isConsistent {μ : Measure Ω} [IsProbabilityMeasure μ]
    {O : ℕ → Ω → 𝒪} (hO : IsIIDSample O μ) {q : FiniteDist 𝒪} (hlaw : μ.map (O 0) = q.toMeasure)
    (S : 𝒪 → 𝓛) (l : 𝓛) :
    IsConsistent (sampleFreq S l O) (wmass q (univ ∩ ev S l)) μ := by
  have hO0 : AEMeasurable (O 0) μ := hO.aemeasurable 0
  have hint : Integrable (fun ω => (fun o => if S o = l then (1 : ℝ) else 0) (O 0 ω)) μ :=
    show Integrable ((fun o => if S o = l then (1 : ℝ) else 0) ∘ O 0) μ from
    (integrable_map_measure (Measurable.of_discrete).aestronglyMeasurable hO0).1
      (by rw [hlaw]; exact Integrable.of_finite)
  have key := sampleMean_isConsistent hO (f := fun o => if S o = l then (1 : ℝ) else 0)
    Measurable.of_discrete hint
  have hval : μ[fun ω => (fun o => if S o = l then (1 : ℝ) else 0) (O 0 ω)] =
      wmass q (univ ∩ ev S l) := by
    rw [← integral_map hO0 (Measurable.of_discrete).aestronglyMeasurable, hlaw,
      FiniteDist.integral_toMeasure, wmass_stratum_univ, FiniteDist.expect]
    exact sum_congr rfl fun o _ => by split_ifs <;> simp
  rw [hval] at key
  exact key

omit [Fintype 𝓛] in
/-- The weighted cell terms of stage one are consistent: a stratum of weight zero contributes
`0`, any other has both cells of positive mass by positivity. -/
theorem weightedCell_isConsistent {μ : Measure Ω} [IsProbabilityMeasure μ]
    {O : ℕ → Ω → 𝒪} (hO : IsIIDSample O μ) {q : FiniteDist 𝒪} (hlaw : μ.map (O 0) = q.toMeasure)
    {S : 𝒪 → 𝓛} {w : 𝓛 → ℝ} (hpos : M.BaselinePositive q univ S w) (B : 𝒪 → ℝ) (l : 𝓛) :
    IsConsistent (fun n ω => w l * M.sampleCellMean S true l (M.treated B) O n ω)
        (w l * condMean q (M.cell univ S true l) (M.treated B)) μ ∧
      IsConsistent (fun n ω => w l * (M.sampleCellMean S true l (M.baseResid B) O n ω -
          M.sampleCellMean S false l (M.baseResid B) O n ω))
        (w l * (condMean q (M.cell univ S true l) (M.baseResid B) -
          condMean q (M.cell univ S false l) (M.baseResid B))) μ := by
  by_cases hw : w l = 0
  · simp only [hw, zero_mul]
    exact ⟨isConsistent_const 0, isConsistent_const 0⟩
  obtain ⟨h1, h0⟩ := hpos l hw
  exact ⟨(isConsistent_const (w l)).mul (M.sampleCellMean_isConsistent hO hlaw S true l _ h1),
    (isConsistent_const (w l)).mul
      ((M.sampleCellMean_isConsistent hO hlaw S true l _ h1).sub
        (M.sampleCellMean_isConsistent hO hlaw S false l _ h0))⟩

omit [MeasurableSpace 𝒪] [MeasurableSingletonClass 𝒪] in
/-- Continuous mapping from the intercept and the slope to the closed form. -/
theorem closedForm_isConsistent {μ : Measure Ω} {a b : ℕ → Ω → ℝ} {α β : ℝ}
    (ha : IsConsistent a α μ) (hb : IsConsistent b β μ) (hβ : 0 < β) (hα : α < 0) :
    IsConsistent (fun n ω => closedForm (a n ω) (b n ω)) (closedForm α β) μ := by
  have hne : -(α / β) ≠ 0 := neg_ne_zero.2 (div_neg_of_neg_of_pos hα hβ).ne
  have key := (ha.div hb hβ.ne').comp (g := fun t => Real.log (-t))
    ((Real.continuousAt_log hne).comp continuousAt_neg)
  simp only [← neg_div] at key
  exact key

/-- **Consistency of the stratified estimator with fixed weights.** For an i.i.d. sample with
law `q` in the finite observation space, strata `S` and fixed weights `w` with positivity for
`q`, if stage one under `q` has a positive slope and a negative intercept, the estimator is
consistent for the closed form of the population intercept and slope, the unique population
root. -/
theorem sampleRootStrata_isConsistent {μ : Measure Ω} [IsProbabilityMeasure μ]
    {O : ℕ → Ω → 𝒪} (hO : IsIIDSample O μ) {q : FiniteDist 𝒪} (hlaw : μ.map (O 0) = q.toMeasure)
    {S : 𝒪 → 𝓛} {w : 𝓛 → ℝ} (hpos : M.BaselinePositive q univ S w) (B : 𝒪 → ℝ)
    (hb : 0 < M.stageOneSlope q univ S w B) (ha : M.stageOneIntercept q univ S w B < 0) :
    IsConsistent (M.sampleRootStrata S w B O)
      (closedForm (M.stageOneIntercept q univ S w B) (M.stageOneSlope q univ S w B)) μ :=
  closedForm_isConsistent
    (isConsistent_sum univ fun l _ => (M.weightedCell_isConsistent hO hlaw hpos B l).2)
    (isConsistent_sum univ fun l _ => (M.weightedCell_isConsistent hO hlaw hpos B l).1) hb ha

/-- **Consistency for the true parameter with fixed weights.** Under the structural model, no
unmeasured confounding within the strata `S`, positivity and relevance for `q`, the stratified
estimator is consistent for the true parameter. -/
theorem sampleRootStrata_isConsistent_true {μ : Measure Ω} [IsProbabilityMeasure μ]
    {O : ℕ → Ω → 𝒪} (hO : IsIIDSample O μ) {q : FiniteDist 𝒪} (hlaw : μ.map (O 0) = q.toMeasure)
    {S : 𝒪 → 𝓛} {w : 𝓛 → ℝ} {B : 𝒪 → ℝ} {ψ : ℝ} (hmodel : M.ModelOn univ B ψ)
    (hnuc : M.BaselineNUC q univ S) (hpos : M.BaselinePositive q univ S w)
    (hb : 0 < M.stageOneSlope q univ S w B) :
    IsConsistent (M.sampleRootStrata S w B O) ψ μ := by
  obtain ⟨ha, hc⟩ := M.closedForm_eq_of_root (M.stageOne_eq_zero hmodel hnuc hpos) hb
  rw [← hc]
  exact M.sampleRootStrata_isConsistent hO hlaw hpos B hb ha

/-- The stratum masses under `q`, the population weights of the frequency estimator. -/
noncomputable def freqWeight (q : FiniteDist 𝒪) (S : 𝒪 → 𝓛) (l : 𝓛) : ℝ :=
  wmass q (univ ∩ ev S l)

/-- **Consistency of the stratified estimator with estimated weights.** With the stratum
frequencies as weights, and positivity in every stratum (each stratum contains switchers and
non-switchers with positive probability under `q`), the estimator is consistent for the closed
form of stage one under `q` weighted by the stratum masses. -/
theorem sampleRootFreq_isConsistent {μ : Measure Ω} [IsProbabilityMeasure μ]
    {O : ℕ → Ω → 𝒪} (hO : IsIIDSample O μ) {q : FiniteDist 𝒪} (hlaw : μ.map (O 0) = q.toMeasure)
    {S : 𝒪 → 𝓛} (hpos : M.BaselinePositive q univ S fun _ => 1) (B : 𝒪 → ℝ)
    (hb : 0 < M.stageOneSlope q univ S (freqWeight q S) B)
    (ha : M.stageOneIntercept q univ S (freqWeight q S) B < 0) :
    IsConsistent (M.sampleRootFreq S B O)
      (closedForm (M.stageOneIntercept q univ S (freqWeight q S) B)
        (M.stageOneSlope q univ S (freqWeight q S) B)) μ := by
  have h1 := fun l => M.weightedCell_isConsistent hO hlaw hpos B l
  simp only [one_mul] at h1
  refine closedForm_isConsistent (isConsistent_sum univ fun l _ => ?_)
    (isConsistent_sum univ fun l _ => ?_) hb ha
  · exact (sampleFreq_isConsistent hO hlaw S l).mul (h1 l).2
  · exact (sampleFreq_isConsistent hO hlaw S l).mul (h1 l).1

/-- **Consistency for the true parameter with estimated weights.** Under the structural model,
no unmeasured confounding within the strata, positivity in every stratum and relevance, the
estimator with the stratum frequencies as weights is consistent for the true parameter. -/
theorem sampleRootFreq_isConsistent_true {μ : Measure Ω} [IsProbabilityMeasure μ]
    {O : ℕ → Ω → 𝒪} (hO : IsIIDSample O μ) {q : FiniteDist 𝒪} (hlaw : μ.map (O 0) = q.toMeasure)
    {S : 𝒪 → 𝓛} {B : 𝒪 → ℝ} {ψ : ℝ} (hmodel : M.ModelOn univ B ψ)
    (hnuc : M.BaselineNUC q univ S) (hpos : M.BaselinePositive q univ S fun _ => 1)
    (hb : 0 < M.stageOneSlope q univ S (freqWeight q S) B) :
    IsConsistent (M.sampleRootFreq S B O) ψ μ := by
  have hpos' : M.BaselinePositive q univ S (freqWeight q S) := fun l _ => hpos l one_ne_zero
  obtain ⟨ha, hc⟩ := M.closedForm_eq_of_root (M.stageOne_eq_zero hmodel hnuc hpos') hb
  rw [← hc]
  exact M.sampleRootFreq_isConsistent hO hlaw hpos B hb ha

end TwoStageTrial

end StructuralNested

end CausalInference
